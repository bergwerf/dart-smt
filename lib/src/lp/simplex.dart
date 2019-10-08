// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.lp;

/// Output of the simplex algorithm (n = length of [x], k = length of [y])
/// [unbounded] is true if the input is unbounded above. In this case [x] and
/// [y] will contain the assignment when discovering the missing upper bound.
class SimplexResult {
  final bool unbounded;
  final Vec x, y;

  SimplexResult(this.unbounded, this.x, this.y);
}

/// Simplex algorithm
///
/// The input should be normalized to slack form. Let n be the size of the x
/// vector and k be the number of constraints. The input consists of two parts:
/// + Maximization function:     z = v   +  c_1*x_1 +  c_2*x_2 + ... +  c_n*x_n
/// + Constraints for i=1..k:  y_i = b_i + a_i1*x_1 + a_i2*x_2 + ... + a_in*x_n
///
/// Input range:
/// + 0 <= b_i
/// + 0 <= x_i
/// + 0 <= y_i
///
/// Arguments:
/// + [c]: vector of length n containing all maximization coefficients.
/// + [a]: matrix of size (n + 1)*k containing all constraints.
///
/// The goal is to maximize z. The input equation system defines an n-polytope
/// that encompasses the feasible region of the vector x. The simplex algorithm
/// starts at x_i = 0 (the zero vector is always contained because of the
/// constraints on b_i, x_i, y_i) and moves along the edges of the polytope
/// until no move yields a higher value for z or an infinite upper bound is
/// discovered.
SimplexResult optimizeBySimplex(Vec c, Mat2 a) {
  // Get n, k and check input constraints.
  final n = c.length;
  final k = a.height;
  assert(a.width == n + 1);
  assert(a.col(0).every((y) => 0 <= y));
  assert(a.col(1).every((b) => 0 <= b));

  // Pivots swap the role of variables but when generating the output we have to
  // restore the original order. These lists store which variable is assigned to
  // which position in the equation system.
  final xs = List.generate(n, (j) => j + 1); // Positive numbers represent xs
  final ys = List.generate(k, (j) => -j - 1); // Negative numbers represent ys

  // Assign current values of b_i to the corresponding x and y variables.
  SimplexResult getResult({bool unbounded: false}) {
    final x = Vec.zeros(n);
    final y = Vec.zeros(n);
    for (var i = 0; i < k; i++) {
      if (ys[i] > 0) {
        x[ys[i] - 1] = a.at(i, 0);
      } else {
        y[-ys[i] - 1] = a.at(i, 0);
      }
    }
    return SimplexResult(false, x, y);
  }

  // Note that the following does not crash if n = 0 || k = 0.
  for (;;) {
    // Find j such that c_j > 0 (we can increase z by increasing x_j).
    final j = c.indexWhere((c) => c > 0);
    if (j == -1) {
      // We cannot increase z further.
      return getResult(unbounded: false);
    }

    // Find maximum increase for x_j.
    //
    // Note that by starting at the zero vector and swapping variables, the
    // coefficients all stay zero except for b_i. Therefore for every i we have
    // y_i = b_i + a_j*x_j and we can increase x_j as long as b_i + a_j*x_j >= 0
    // (we want to keep y_i >= 0, remember that y_i is introduced to translate
    // `a_1*x_1 +...+ a_n*x_n <= b_i` to `y_i = b_i - a_1*x_1 +...+ a_n*x_n`).
    // Thus we have x_j <= -b_i/a_j if a_j < 0 and x_j >= -b_i/a_j if a_j > 0.
    var best = -1.0, pivot = -1;
    for (var i = 0; i < k; i++) {
      final aij = a.at(i, j + 1);
      if (aij < 0) {
        final bi = a.at(i, 0);
        final increase = -bi / aij;
        if (increase > best) {
          best = increase;
          pivot = i;
        }
      }
    }

    // If we did not find a pivot, then z is unbounded.
    if (pivot == -1) {
      return getResult(unbounded: true);
    }

    // For i = pivot, swap x_j and y_i. We find x_j = (... - y_i)/-a_j and
    // substitute this into all constraints and the optimization function..
    final xj = xs[j], yi = ys[pivot];
    ys[pivot] = xj;
    xs[j] = yi;

    // Compute new coefficients in i-th row.
    final ai = a.row(pivot);
    final aij = ai[j + 1];
    ai[j + 1] = -1; // "subtract y_i"
    ai.multiplyAll(1 / -aij);

    // For each other coefficient row aa (the optimization function is similar),
    // substitute x_j = ... + ai_j*y_i:
    // + Compute d = ai .* aa_j
    // + Set aa_j = 0
    // + Set aa = aa + d
    for (var i = 0; i < k; i++) {
      if (i != pivot) {
        final aa = a.row(i);
        final d = aa.copy();
        d.multiplyAll(aa[j + 1]);
        aa[j + 1] = 0;
        aa.addVec(d);
      }
    }
    final d = c.copy();
    d.multiplyAll(c[j]);
    d[j] = 0;
    c.addVec(d);
  }
}
