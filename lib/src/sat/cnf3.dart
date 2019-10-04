// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// An optimized 3-CNF for 3SAT problems. All unit clauses should be removed
/// before the creation of this CNF resulting in only [doubleClauses] and
/// [tripleClauses].
class CNF3 {
  /// For any literal, store which literal is implied. This stores all double
  /// clauses. For any clause {p q}, the map contains ~p => q, ~q => p.
  final Map<int, int> doubleClauses;

  /// For any pair of literals, find which third literal is implied (if any).
  /// For any clause {p q r} with p < q < r, the map contains: (~p ~q) => r,
  /// (~p ~r) => q, (~q ~r) => p. With ordered pairs we get a 2x compression.
  final Map<OrderedLiteralPair, int> tripleClauses;

  /// Variable labels
  final Map<int, String> labels;

  CNF3(this.doubleClauses, this.tripleClauses, this.labels);
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
}

/// Convert list of [clauses] to a 3-CNF instance and convert all unit clauses
/// to CDCL rules.
Pair<CNF3, List<CDCLRule>> convertClausesToCNF3(List<Expr> clauses) {
  final doubleClauses = <int, int>{};
  final tripleClauses = <OrderedLiteralPair, int>{};
  final labelMap = <String, int>{};
  final indexMap = <int, int>{};
  var vSeq = 0; // Variable identifier sequence

  // Convert literal expression to integer.
  int convertLiteral(Expr x) {
    final n = x.isNot;
    final v = n ? x.arguments[0] : x;
    final i = v.index >= 0
        ? indexMap.putIfAbsent(v.index, () => ++vSeq)
        : labelMap.putIfAbsent(x.label, () => ++vSeq);
    return n ? -i : i;
  }

  // Process all clauses.
  final rules = <CDCLRule>[];
  for (final c in clauses) {
    final l = toUniqueList(flattenExpr(ExprType.or, c).map(convertLiteral));
    switch (l.length) {
      case 1:
        // Add CDCL rule.
        rules.add(CDCLRule.unitPropagate(l[0]));
        break;

      case 2:
        // Add to double clause map unless clause is trivial.
        if (l[0] != -l[1]) {
          doubleClauses[-l[0]] = l[1];
          doubleClauses[-l[1]] = l[0];
        }
        break;

      case 3:
        // Add to triple clause map unless clause is trivial.
        if (l[0] != -l[1] && l[0] != -l[2] && l[1] != -l[2]) {
          tripleClauses[OrderedLiteralPair(-l[0], -l[1])] = l[2];
          tripleClauses[OrderedLiteralPair(-l[0], -l[2])] = l[1];
          tripleClauses[OrderedLiteralPair(-l[1], -l[2])] = l[0];
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
  return Pair(CNF3(doubleClauses, tripleClauses, invertMap(labelMap)), rules);
}
