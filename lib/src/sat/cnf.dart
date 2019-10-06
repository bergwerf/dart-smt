// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// A formula in Conjunctive Normal Form
///
/// A clause is a set of literals (integer sign represents negation).
class CNF {
  final List<Set<int>> clauses;
  final List<int> variables;
  final Map<int, String> labels;

  CNF(this.clauses, [this.labels, List<int> variables])
      : variables = variables ?? getVariablesInClauses(clauses);

  /// Compute size (summed size of all clauses).
  int get size => clauses.fold(0, (n, c) => n + c.length);

  /// Check if this CNF is empty.
  bool get isEmpty => clauses.isEmpty;

  /// Check if there is an empty clause.
  bool get hasEmptyClause => clauses.any((c) => c.isEmpty);

  @override
  String toString() {
    // Convert literal to string.
    String toStr(int p) => '${p.isNegative ? '~' : ''}' // Literal sign
        '${labels[p.abs()] ?? '#${p.abs()}'}'; // Literal label
    // Join clauses with newlines.
    return clauses.map((c) => '{${c.map(toStr).join(' ')}}').join('\n');
  }
}

/// Create full copy of [cnf].
CNF copyCNF(CNF cnf) => CNF(
    cnf.clauses.map((c) => c.toSet()).toList(),
    cnf.labels, // Not modified so no copy needed.
    cnf.variables.toList());

/// Compute list of unique variables in [clauses].
List<int> getVariablesInClauses(List<Set<int>> clauses) =>
    clauses.expand((c) => c).toSet().toList();

/// Evaluate [cnf] for the given [assignment] (for testing purposes).
bool evaluateCNF(CNF cnf, Map<int, bool> assignment) {
  // Check if every clause is true, else return false.
  CLAUSES:
  for (final c in cnf.clauses) {
    for (final p in c) {
      // Check if this literal evaluates to true.
      if ((p > 0) == assignment[p.abs()]) {
        continue CLAUSES;
      }
    }
    // This clause is not true.
    return false;
  }
  // All clauses are true.
  return true;
}

/// Convert list of [clauses] to CNF instance.
CNF convertClausesToCNF(List<Expr> clauses) {
  final variables = <int>{};
  final labelMap = <String, int>{};
  final indexMap = <int, int>{};
  var vSeq = 0; // Variable identifier sequence

  // Convert all clauses.
  final convertedClauses = clauses.map((c) {
    final literals = flattenExpr(ExprType.or, c);
    assert(literals.every(isLiteral));
    return literals.map((x) {
      final n = x.isNot;
      final v = n ? x.arguments[0] : x;
      final i = v.index >= 0
          ? indexMap.putIfAbsent(v.index, () => ++vSeq)
          : labelMap.putIfAbsent(v.label, () => ++vSeq);
      variables.add(i);
      return n ? -i : i;
    }).toSet();
  }).toList();

  return CNF(convertedClauses, invertMap(labelMap), variables.toList());
}
