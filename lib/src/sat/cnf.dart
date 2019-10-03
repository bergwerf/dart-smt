// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

enum SatResult { sat, unsat }

/// A clause is a disjunction of literals where each literal is either a
/// variable or a negation of a variable. Here we represent these more
/// efficiently using hash tables.
class Clause {
  final Set<int> tVars, fVars;
  Clause(this.tVars, this.fVars);

  /// Check if this clause is empty.
  bool get isEmpty => tVars.isEmpty && fVars.isEmpty;

  /// Check if this clause contains [v].
  bool containsVariable(int v) => tVars.contains(v) || fVars.contains(v);

  /// Check if this clause contains the literal [negation] of [variable].
  bool containsLiteral(bool negation, int variable) =>
      (negation ? fVars : tVars).contains(variable);

  /// Check if this clause is a subset or equal to [other].
  bool containsClause(Clause other) =>
      other.tVars.containsAll(tVars) && other.fVars.containsAll(fVars);

  /// Remove literal [negation] of [variable].
  void removeLiteral(bool negation, int variable) =>
      (negation ? fVars : tVars).remove(variable);
}

/// A formula in Conjunctive Normal Form
class CNF {
  final List<Clause> clauses;
  final List<int> variables;

  /// This is metadata. It is ok to supply null to save memory in recursion.
  final Map<int, String> labels;

  CNF(this.clauses, this.labels) : variables = getVariablesInCNF(clauses);

  /// Check if there is an empty clause.
  bool get hasEmptyClause => clauses.any((c) => c.isEmpty);

  @override
  String toString() {
    String lbl(int i) => labels[i] ?? '?$i';
    return clauses.map((c) {
      final literals = [
        c.tVars.map(lbl), //
        c.fVars.map(lbl).map((s) => '~$s')
      ].expand((l) => l);
      return '{${literals.join(' ')}}';
    }).join('\n');
  }
}

/// Compute list of unique variables in [clauses].
List<int> getVariablesInCNF(List<Clause> clauses) {
  return clauses.expand((c) => c.tVars.union(c.fVars)).toSet().toList();
}

/// Evaluate [cnf] for the given [assignment] (for testing purposes).
bool evaluateCNF(CNF cnf, Map<int, bool> assignment) {
  // Check if every clause is true, else return false.
  CLAUSES:
  for (final c in cnf.clauses) {
    for (final v in c.tVars) {
      if (assignment[v]) {
        continue CLAUSES;
      }
    }
    for (final v in c.fVars) {
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

/// Compile CPL in [input] and build CNF.
CNF compileCplToCNF(String input, [Map<String, bool> assignments]) {
  final expr = compileCpl(input, assignments);
  final clauseExprs = convertExprToCNF(rewriteToNNF(unfoldImply(expr)));
  final lm = <String, int>{};
  final clauses = clauseExprs.map((c) => convertExprToClause(lm, c)).toList();
  final labels = lm.map((k, v) => MapEntry(v, k));
  return CNF(clauses, labels);
}

/// Convert disjunction in [expr] to clause.
Clause convertExprToClause(Map<String, int> labelMap, Expr expr) {
  final literals = flattenExpr(ExprType.or, expr);
  final tVars = literals.where((l) => l.type == ExprType.variable);
  final fVars = literals.where((l) => l.type == ExprType.not);

  Set<int> toSet(Iterable<Expr> xs) {
    return xs.map((x) {
      final label = x.type == ExprType.not ? x.arguments[0].label : x.label;
      return labelMap.putIfAbsent(label, () => labelMap.length);
    }).toSet();
  }

  return Clause(toSet(tVars), toSet(fVars));
}
