// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.lp;

/// SMT theory for linear optimization on floating point numbers
class LinearOptimizationTheory extends SmtTheory<LinearConstraint, double,
    LinearInequality, LinearProblem> {
  @override
  LinearInequality read(CplTerm term) {
    if (!term.isTuple ||
        term.subTerms.length != 3 ||
        !term.subTerms[0].isName) {
      return null;
    }

    // Check operator.
    final op = term.subTerms[0].expectName();
    final leq = op == '<=';
    if (!leq && op != '>=') {
      return null;
    }

    // Get linear combination of both sides.
    final l = getLinearFunction(term.subTerms[1]);
    final r = getLinearFunction(term.subTerms[2]);
    if (l == null || r == null) {
      return null;
    }

    // We now have l <= r or l >= r. Normalize to 0 <= f.
    return LinearInequality(subtractLinearFns(leq ? r : l, leq ? l : r));
  }

  @override
  LinearProblem createEmptyProblem() => LinearProblem.empty();
}

/// Linear inequality of the form x <= c where x is a linear combination and
/// c is a constant. We store this as 0 <= c - x where c - x is a linear
/// function and is stored in [f].
class LinearInequality implements SmtTerm<LinearConstraint> {
  final LinearFn f;

  LinearInequality(this.f);

  @override
  List<String> get labels => f.x.map((x) => x.snd).toList();

  @override
  LinearConstraint normalize(Map<String, int> identifiers) {
    final ax = f.x.map((x) => Pair(x.fst, identifiers[x.snd])).toList();
    assert(!ax.any((x) => x.snd == null));
    ax.sort((ax1, ax2) => ax1.snd - ax2.snd);
    final a = ax.map((ax) => ax.fst).toList();
    final x = ax.map((ax) => ax.snd).toList();
    return LinearConstraint(f.c, a, x);
  }
}

/// Normalized linear inequality of the form y = b + a_0*x_0 + a_1*x_1 + ...
/// where the x variables are ordered by their integer identifier such that this
/// represents a unique constraint. Here y is a pseudo variable which is not
/// stored.
class LinearConstraint {
  final double b;
  final List<double> as;
  final List<int> xs;

  LinearConstraint(this.b, this.as, this.xs) : assert(b >= 0);

  @override
  int get hashCode => hash3(b, hashObjects(as), hashObjects(xs));

  @override
  bool operator ==(other) =>
      other is LinearConstraint &&
      other.b == b &&
      listsEqual(other.as, as) &&
      listsEqual(other.xs, xs);
}

/// Linear programming problem (see [solveSimplex] for details)
class LinearProblem implements SmtProblem<LinearConstraint, double> {
  final List<int> xs;
  final List<int> ys;
  final Vec c;
  final Mat2 a;

  LinearProblem(this.xs, this.ys, this.c, this.a)
      : assert(c.length == xs.length + 1),
        assert(a.width == c.length && a.height == ys.length);

  factory LinearProblem.empty() =>
      LinearProblem([], [], Vec.zeros(1), Mat2.zeros(1, 0));

  /// Replace optimization function [coefficients]. If some x and y are already
  /// swapped, or the input does not contain a value for some coefficients, then
  /// those coefficients are kept unchanged.
  void replaceZ(double v, Map<int, double> coefficients) {
    c[0] = v;
    assert(coefficients.keys.every((k) => k > 0));
    for (var i = 0; i < xs.length; i++) {
      c[i + 1] = coefficients[xs[i]];
    }
  }

  @override
  LinearProblem add(LinearConstraint constraint) =>
      addConstraintToLinearProblem(this, constraint);

  @override
  bool check() => solveSimplex(c, a, xs, ys) == SimplexResult.optimized;

  @override
  Map<int, double> get assignment {
    // Retrieve values that the current optimization state assigns to the
    // original x variables of the input constraints (the y variables are
    // discarded). Note that y variables are referenced as negative numbers.
    final k = a.height;
    final x = <int, double>{};
    for (var i = 0; i < k; i++) {
      if (ys[i] > 0) {
        x[ys[i]] = a.at(i, 0);
      }
    }
    // Add 0 for all other x values.
    for (final j in xs) {
      if (j > 0) {
        x[j] = 0;
      }
    }
    return x;
  }
}

/// Add constraint [lc] to linear inequality problem [p].
LinearProblem addConstraintToLinearProblem(
    LinearProblem p, LinearConstraint lc) {
  // Compute xs and ys. Note that we add all xs that were not yet in the system.
  // Also note swaps from earlier optimizations may have placed some variables
  // in [p.ys], we have to apply these swaps to the new constraint.
  final xy = p.xs.toSet()..addAll(p.ys);
  final xs = p.xs.toList()..addAll(lc.xs.where((x) => !xy.contains(x)));
  final ys = p.ys.toList();
  ys.add(-(ys.length + 1));

  // Copy optimization coefficients in [p] and add a 1 for each new x_i.
  final c = Vec.zeros(xs.length + 1);
  c.copy(p.c);
  for (var i = p.c.length; i < c.length; i++) {
    c[i] = 1;
  }

  // Copy constraint coefficients of [p] and [lc].
  final a = Mat2.zeros(xs.length + 1, ys.length);
  final alc = a.row(ys.length - 1);
  a.copy(p.a);
  alc[0] = lc.b;
  for (var j = 0; j < xs.length; j++) {
    // Copy coefficient for this x_j from [lc] if it is present.
    if (xs[j] > 0) {
      final lcj = lc.xs.indexOf(xs[j]);
      if (lcj != -1) {
        alc[j + 1] = lc.as[lcj];
      }
    }
  }

  // Substitute all swapped x_i's in [p] that are also in [lc] in the new
  // constraint entry with the corresponding coefficient for x_i in [lc].
  for (var i = 0; i < p.ys.length; i++) {
    if (ys[i] > 0) {
      // This is an x, check if it is in [lc].
      final lcj = lc.xs.indexOf(ys[i]);
      if (lcj != -1) {
        final ai = a.row(i).clone(); // Clone x for substitution.
        ai.multiplyAll(lc.as[lcj]); // Add multiplier of this x in [lc].
        // Substitute. Note that this x is already zero in [alc].
        alc.addVec(ai);
      }
    }
  }

  return LinearProblem(xs, ys, c, a);
}
