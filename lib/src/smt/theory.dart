// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt;

/// SMT theory
///
/// There are two term types: [Term], which is used to represent terms of this
/// theory in expressions, and [NormTerm], which should be a normalized and more
/// efficient type for terms that uses integers to identify variables.
///
/// The theory can freely specify the type of a term, a normalized term, and a
/// solution (booleans, numbers, strings). A theory must have an (efficient)
/// iterative algorithm for checking feasibility.
abstract class SmtTheory<NormTerm, Value, Term extends SmtTerm<NormTerm>,
    Problem extends SmtProblem<NormTerm, Value>> {
  /// Convert [CplTerm] to term in this theory or return null.
  Term read(CplTerm term);

  /// Check if [term] belongs to this theory.
  bool contains(term) => term is Term;

  /// Create an empty problem.
  Problem createEmptyProblem();
}

/// A term in an SMT theory.
abstract class SmtTerm<NormTerm> {
  /// Get list of variable labels that are used in this term.
  List<String> get labels;

  /// Normalize this term given integer variable [identifiers].
  NormTerm normalize(Map<String, int> identifiers);
}

/// A problem instance in an SMT theory.
abstract class SmtProblem<Constraint, Value> {
  /// Create copy of this problem with a new [constraint].
  SmtProblem<Constraint, Value> add(Constraint constraint);

  /// Check feasibility of the current constraints.
  bool check();

  /// If this problem is feasible, get the value assignment for its variables.
  Map<int, Value> get assignment;
}
