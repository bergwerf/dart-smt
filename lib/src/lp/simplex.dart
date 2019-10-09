// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.lp;

/// Termination state of the simplex algorithm
enum SimplexResult { unbounded, optimized }

/// Simplex algorithm
///
/// The input should be normalized to slack form. Let n be the size of the x
/// vector and k be the number of constraints. The input consists of two parts:
/// + Maximization function:     z = v   +  c_1*x_1 +  c_2*x_2 + ... +  c_n*x_n
/// + Constraints for i=1..k:  y_i = b_i + a_i1*x_1 + a_i2*x_2 + ... + a_in*x_n
///
/// Arguments:
/// + [c]: vector of length n containing all maximization coefficients (0 <= v)
/// + [a]: matrix of size (n + 1)*k containing all constraints (0 <= b_i)
/// + [xs]: variable belonging to each x_j
/// + [ys]: variable belonging to each y_i
///
/// The goal is to maximize z. The input equation system defines an n-polytope
/// that encompasses the feasible region of the vector x. The simplex algorithm
/// starts at x_i = 0 (the zero vector is always contained because of the
/// constraints on b_i, x_i, y_i) and moves along the edges of the polytope
/// until no move yields a higher value for z or an infinite upper bound is
/// discovered.
SimplexResult solveSimplex(Vec c, Mat2 a, List<int> xs, List<int> ys) {
  // Get n, k and check input constraints.
  assert(a.width >= 1);
  final n = a.width - 1;
  final k = a.height;
  assert(c.length == n + 1);
  assert(0 <= c[0]);
  assert(a.col(0).every((b) => 0 <= b));

  // Note that the following does not crash if n = 0 || k = 0.
  for (;;) {
    // Find j such that c_j > 0 (we can increase z by increasing x_j). Note that
    // we start at j = 1 (we are not interested in the constant v).
    final j = c.indexWhere((c) => c > 0, 1);
    if (j == -1) {
      return SimplexResult.optimized;
    }

    // Find increase upper bound for x_j.
    //
    // Note that by starting at the zero vector and swapping variables, the
    // coefficients all stay zero except for b_i. Therefore for every i we have
    // y_i = b_i + a_j*x_j and we can increase x_j as long as b_i + a_j*x_j >= 0
    // (we want to keep y_i >= 0, remember that y_i is introduced to translate
    // `a_1*x_1 +...+ a_n*x_n <= b_i` to `y_i = b_i - a_1*x_1 +...+ a_n*x_n`).
    // Thus we have x_j <= -b_i/a_j if a_j < 0 and x_j >= -b_i/a_j if a_j > 0.
    var upperBound = 0.0, pivot = -1;
    for (var i = 0; i < k; i++) {
      final aij = a.at(i, j);
      if (aij < 0) {
        // The i-th constraint produces a bound.
        final bi = a.at(i, 0);
        final bound = -bi / aij;
        if (pivot == -1 || bound < upperBound) {
          upperBound = bound;
          pivot = i;
        }
      }
    }

    // If we did not find a pivot, then z is unbounded.
    if (pivot == -1) {
      return SimplexResult.unbounded;
    }

    // For i = pivot, swap x_j and y_i. We find x_j = (... - y_i)/-a_j and
    // substitute this into all constraints and the optimization function.
    final _xj = xs[j - 1];
    xs[j - 1] = ys[pivot];
    ys[pivot] = _xj;

    // Compute new coefficients in i-th row.
    final ai = a.row(pivot);
    final aij = ai[j];
    ai[j] = -1; // "subtract y_i"
    ai.multiplyAll(1 / -aij);

    // For each other coefficient row, substitute x_j.
    _simplexSubstitute(ai, c, j);
    for (var i = 0; i < k; i++) {
      if (i != pivot) {
        _simplexSubstitute(ai, a.row(i), j);
      }
    }
  }
}

/// Substitute x_j = b + a_1*x_1 + ... + a_j*y + ... (coefficients in [ai])
/// in y' = b' + a'_1*x'_1 + ... + a'_j*x_j + ... (coefficients in [aai]).
/// + Compute d = a'_j * x_j = ai .* aai[j]
/// + Set a'_j = aai[j] = 0
/// + Set y' += d
void _simplexSubstitute(Vec ai, Vec aai, int j) {
  assert(ai.length == aai.length && j < ai.length);
  final d = ai.clone();
  d.multiplyAll(aai[j]);
  aai[j] = 0;
  aai.addVec(d);
}
