// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

/// Process [term] into a linear function or return null if it is not a linear
/// function. There is support for the following operators:
/// + `+` n-ary
/// + `-` 1-ary or 2-ary
/// + `*` n-ary
LinearFn getLinearFunction(CplTerm term) {
  switch (term.type) {
    case CplTermType.name:
      return LinearFn(0, [Pair(1, term.name)]);

    case CplTermType.number:
      return LinearFn(term.number.toDouble(), []);

    default: // tuple
      final fs = term.subTerms.sublist(1).map(getLinearFunction).toList();
      if (fs.any((f) => f == null)) {
        return null;
      }

      switch (term.subTerms[0].expectName()) {
        case '+':
          // n-ary addition
          return addLinearFns(fs);

        case '-':
          // negation or subtraction
          cplAssert(() => fs.length < 3 && fs.isNotEmpty);
          return fs.length == 1
              ? multiplyLinearFn(-1, fs[0])
              : subtractLinearFns(fs[0], fs[1]);

        case '*':
          // n-ary multiplication, find non-constant term.
          final c = fs.fold(1, (n, f) => f.x.isEmpty ? n * f.c : n);
          final nc = fs.where((f) => f.x.isNotEmpty).toList();
          return nc.length == 1
              ? multiplyLinearFn(c, nc[0])
              : nc.isEmpty ? c : null;

        default:
          return null;
      }
  }
}

/// Linear function of the form `c + (x[0].a)*(x[0].b) + ...`.
class LinearFn {
  final double c;
  final List<Pair<double, String>> x;

  LinearFn(this.c, this.x);
}

/// Add linear functions.
LinearFn addLinearFns(List<LinearFn> fs) {
  var c = 0.0;
  final x = <String, double>{};
  for (final f in fs) {
    c += f.c;
    for (final xp in f.x) {
      x[xp.snd] = (x[xp.snd] ?? 0) + xp.fst;
    }
  }
  return LinearFn(c, convertMapToInvPairs(x));
}

/// Multiply linear function [f] by a constant [c].
LinearFn multiplyLinearFn(double c, LinearFn f) =>
    LinearFn(c * f.c, f.x.map((x) => Pair(c * x.fst, x.snd)).toList());

/// Subtract linear functions [a] and [b].
LinearFn subtractLinearFns(LinearFn a, LinearFn b) =>
    addLinearFns([a, multiplyLinearFn(-1, b)]);
