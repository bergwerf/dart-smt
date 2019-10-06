// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// A clause is a disjunction of literals where each literal is either a
/// variable or a negation of a variable. Here we represent these more
/// efficiently using hash tables.
///
/// TODO: Use only one set with positive and negative integers.
class Clause {
  final Set<int> pos, neg;

  Clause(this.pos, this.neg);

  /// Get clause size.
  int get size => pos.length + neg.length;

  /// Check if this clause is empty.
  bool get isEmpty => pos.isEmpty && neg.isEmpty;

  /// Check if this clause contains [v].
  bool containsVariable(int v) => pos.contains(v) || neg.contains(v);

  /// Check if this clause contains the literal [positive] [variable].
  bool containsLiteral(bool positive, int variable) =>
      positive ? pos.contains(variable) : neg.contains(variable);

  /// Remove literal [positive] [variable].
  void removeLiteral(bool positive, int variable) =>
      positive ? pos.remove(variable) : neg.remove(variable);

  /// Check if this clause is a subset or equal to [other].
  bool containsClause(Clause other) =>
      other.pos.containsAll(pos) && other.neg.containsAll(neg);
}

/// A formula in Conjunctive Normal Form
class CNF {
  final List<Clause> clauses;
  final List<int> variables;
  final Map<int, String> labels;

  CNF(this.clauses, [this.labels, List<int> variables])
      : variables = variables ?? getVariablesInClauses(clauses);

  /// Compute size (summed size of all clauses).
  int get size => clauses.fold(0, (n, c) => n + c.size);

  /// Check if this CNF is empty.
  bool get isEmpty => clauses.isEmpty;

  /// Check if there is an empty clause.
  bool get hasEmptyClause => clauses.any((c) => c.isEmpty);

  @override
  String toString() {
    String lbl(int i) => labels[i] ?? '?$i';
    return clauses.map((c) {
      final literals = [
        c.pos.map(lbl), //
        c.neg.map(lbl).map((s) => '~$s')
      ].expand((l) => l);
      return '{${literals.join(' ')}}';
    }).join('\n');
  }
}

/// Create full copy of [cnf].
CNF copyCNF(CNF cnf) => CNF(
    cnf.clauses.map((c) => Clause(c.pos.toSet(), c.neg.toSet())).toList(),
    cnf.labels, // Not modified so no copy needed.
    cnf.variables.toList());

/// Compute list of unique variables in [clauses].
List<int> getVariablesInClauses(List<Clause> clauses) =>
    clauses.expand((c) => c.pos.union(c.neg)).toSet().toList();

/// Evaluate [cnf] for the given [assignment] (for testing purposes).
bool evaluateCNF(CNF cnf, Map<int, bool> assignment) {
  // Check if every clause is true, else return false.
  CLAUSES:
  for (final c in cnf.clauses) {
    for (final v in c.pos) {
      if (assignment[v]) {
        continue CLAUSES;
      }
    }
    for (final v in c.neg) {
      if (!assignment[v]) {
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
  final labelMap = <String, int>{};
  final indexMap = <int, int>{};
  var vSeq = 0; // Variable identifier sequence

  // Convert all clauses.
  final convertedClauses = clauses.map((c) {
    final literals = flattenExpr(ExprType.or, c);
    assert(literals.every(isLiteral));
    final pos = literals.where((l) => l.isVariable);
    final neg = literals.where((l) => l.isNot).map((l) => l.arguments[0]);

    Set<int> toSet(Iterable<Expr> xs) {
      return xs.map((x) {
        assert(x.isVariable);
        return x.index >= 0
            ? indexMap.putIfAbsent(x.index, () => ++vSeq)
            : labelMap.putIfAbsent(x.label, () => ++vSeq);
      }).toSet();
    }

    return Clause(toSet(pos), toSet(neg));
  }).toList();

  return CNF(convertedClauses, invertMap(labelMap));
}
