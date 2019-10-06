// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// An optimized 3-CNF for 3SAT problems. All unit clauses should be removed
/// before the creation of this CNF resulting in only [doubleClauses] and
/// [tripleClauses].
class CNF3 {
  /// All variables.
  final Set<int> variables;

  /// For any literal, store which literal is implied. This stores all double
  /// clauses. For any clause {p q}, the map contains ~p => q, ~q => p.
  final Map<int, List<int>> doubleClauses;

  /// For any pair of literals, find which third literal is implied (if any).
  /// For any clause {p q r} with p < q < r, the map contains: (~p ~q) => r,
  /// (~p ~r) => q, (~q ~r) => p. With ordered pairs we get a 2x compression.
  final Map<OrderedLiteralPair, List<int>> tripleClauses;

  /// Variable labels
  final Map<int, String> labels;

  CNF3(this.variables, this.doubleClauses, this.tripleClauses, this.labels)
      : assert(!mmContainsEmpty(doubleClauses)),
        assert(!mmContainsEmpty(tripleClauses));

  /// Compute number of clauses this CNF represents.
  int get length => mmLength(doubleClauses) ~/ 2 + mmLength(tripleClauses) ~/ 3;
}

/// A pair of literals stored as signed integers where the sign means negation.
/// (we could use bitwise operations to store negation as even/odd, but I doubt
/// this will be faster in the Dart VM).
///
/// Since any pair that contains both p and -p refers to a clause that is
/// trivially true, no pair will have |p| = |q|. Therefore |p| < |q|.
class OrderedLiteralPair {
  final int p, q;

  factory OrderedLiteralPair(int p, int q) => p.abs() < q.abs()
      ? OrderedLiteralPair._(p, q)
      : OrderedLiteralPair._(q, p);

  OrderedLiteralPair._(this.p, this.q);

  /// Inspired by http://szudzik.com/ElegantPairing.pdf. This variant is not
  /// completely collision free (note that both may be negative).
  ///
  /// Collisions:
  /// - (p, q) collides with (p, -q) for all p, q
  ///   + Since (-q)^2 + p = q^2 + p
  ///
  /// Note that:
  /// - (p, q) collides with (p + 2q - 1, q - 1)
  ///   + Since (q - 1)^2 + (p + 2q - 1) = q^2 + p
  ///   + However |p + 2q - 1| < |q - 1| does not exist since |p| < |q|.
  /// - (p, q) collides with (p - 2q - 1, q + 1)
  ///   + Since (q + 1)^2 + (p - 2q - 1) = q^2 + p
  ///   + However |p - 2q - 1| < |q + 1| does not exist since |p| < |q|.
  @override
  int get hashCode => q * q + p;

  @override
  bool operator ==(x) => x is OrderedLiteralPair && x.p == p && x.q == q;

  @override
  String toString() => '{$p $q}';
}

/// Convert list of [clauses] to a 3-CNF instance and convert all unit clauses
/// to CDCL rules.
CDCLInput convertClausesToCDCLInput(List<Expr> clauses) {
  final variables = <int>{};
  final doubleClauses = <int, List<int>>{};
  final tripleClauses = <OrderedLiteralPair, List<int>>{};
  final labelMap = <String, int>{};
  final indexMap = <int, int>{};
  var vSeq = 0; // Variable identifier sequence

  // Convert literal expression to integer. Note that 0 cannot be used as
  // variable identifier because 0 == -0.
  int convertLiteral(Expr x) {
    assert(isLiteral(x));
    final n = x.isNot;
    final v = n ? x.arguments[0] : x;
    final i = v.index >= 0
        ? indexMap.putIfAbsent(v.index, () => ++vSeq)
        : labelMap.putIfAbsent(v.label, () => ++vSeq);
    variables.add(i);
    return n ? -i : i;
  }

  // Process all clauses.
  final rules = <CDCLRule>[];
  for (final c in clauses) {
    final l = toUniqueList(flattenExpr(ExprType.or, c).map(convertLiteral));
    switch (l.length) {
      case 1:
        // Add CDCL rule.
        rules.add(CDCLRule.unitPropagate(l[0], -1, -1));
        break;

      case 2:
        // Add to double clause map unless clause is trivial.
        if (!(l[0] == -l[1])) {
          mmAdd(doubleClauses, -l[0], l[1]);
          mmAdd(doubleClauses, -l[1], l[0]);
        }
        break;

      case 3:
        // Add to triple clause map unless clause is trivial.
        if (!(l[0] == -l[1] || l[0] == -l[2] || l[1] == -l[2])) {
          mmAdd(tripleClauses, OrderedLiteralPair(-l[0], -l[1]), l[2]);
          mmAdd(tripleClauses, OrderedLiteralPair(-l[0], -l[2]), l[1]);
          mmAdd(tripleClauses, OrderedLiteralPair(-l[1], -l[2]), l[0]);
        }
        break;

      default:
        throw new ArgumentError('input is not a 3-CNF');
    }
  }

  // We could apply unit resolution now to find more unit clauses and make some
  // clauses smaller, however:
  // + Doing this before creating the hash tables requires expensive loops.
  // + Doing this after creating hash tables only (slightly) reduces the size of
  //   the hash tables. It is not clear this is an overall improvement.
  //
  // Note that we still have to do the same lookups in the CDCL algorithm
  // because we do not know which implications are present. The only performance
  // improvement would be caused by the hash tables using less space, but I
  // don't think this is significant.
  assert(mmLength(doubleClauses) % 2 == 0);
  assert(mmLength(tripleClauses) % 3 == 0);
  assert(labelMap.keys.every((lbl) => lbl.isNotEmpty));
  final labels = invertMap(labelMap);
  final cnf = CNF3(variables, doubleClauses, tripleClauses, labels);
  return CDCLInput(cnf, rules);
}

/// Convert CNF3 + CDCL rules to CNF for debugging.
CNF convertCDCLInputToCNF(CDCLInput input) {
  final clauses = <Clause>[];
  void addClause(List<int> literals) {
    assert(!literals.any((l) => l == 0));
    final pos = literals.where((l) => l > 0).toSet();
    final neg = literals.where((l) => l < 0).map((l) => l.abs()).toSet();
    clauses.add(Clause(pos, neg));
  }

  // Process unit clauses.
  for (final r in input.rules) {
    addClause([r.literal]);
  }

  // Process double clauses.
  final clauses2 = mmCopy(input.cnf.doubleClauses);
  while (clauses2.isNotEmpty) {
    final entry = clauses2.entries.first;
    final p = -entry.key, q = entry.value.first;
    mmRemove(clauses2, -p, q);
    mmRemove(clauses2, -q, p);
    addClause([p, q]);
  }

  // Process triple clauses.
  final clauses3 = mmCopy(input.cnf.tripleClauses);
  while (clauses3.isNotEmpty) {
    final entry = clauses3.entries.first;
    final p = -entry.key.p, q = -entry.key.q, r = entry.value.first;
    mmRemove(clauses3, OrderedLiteralPair(-p, -q), r);
    mmRemove(clauses3, OrderedLiteralPair(-p, -r), q);
    mmRemove(clauses3, OrderedLiteralPair(-q, -r), p);
    addClause([p, q, r]);
  }

  assert(clauses.length == input.rules.length + input.cnf.length);
  return CNF(clauses, input.cnf.labels, input.cnf.variables.toList());
}

/// CNF3 and CDCL initialization rules representing a CDCL input.
class CDCLInput {
  final CNF3 cnf;
  final List<CDCLRule> rules;
  CDCLInput(this.cnf, this.rules);
}
