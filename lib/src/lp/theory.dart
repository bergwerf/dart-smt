// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.lp;

/// SMT theory for linear optimization on floating point numbers
class LinearOptimizationTheory extends SmtTheory<LinearConstraint, double,
    LinearInequality, LinearProblem> {
  // TODO
  @override
  LinearInequality read(CplTerm term) {
    return null;
  }

  @override
  LinearProblem createEmptyProblem() => new LinearProblem();
}

/// Linear inequality
class LinearInequality implements SmtTerm<LinearConstraint> {
  // TODO
  @override
  List<String> get labels => null;

  // TODO
  @override
  LinearConstraint normalize(Map<String, int> variables) {
    return null;
  }
}

/// Normalized linear inequality
class LinearConstraint {
  //
}

/// Linear programming problem
class LinearProblem implements SmtProblem<LinearConstraint, double> {
  // TODO
  @override
  void add(LinearConstraint constraint) {}

  // TODO
  @override
  bool check() {
    return false;
  }

  // TODO
  @override
  Map<int, double> get assignment => null;
}
