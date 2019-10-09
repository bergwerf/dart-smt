// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

import 'package:smt/lp.dart';
import 'package:smt/cpl.dart';
import 'package:test/test.dart';

final theory = LinearOptimizationTheory();

/// Parse linear inequalities in [input].
List<LinearInequality> parseInequalities(String input) =>
    parseCpl(tokenizeCpl(input)).map(theory.read).toList();

void main() {
  test('optimizeBySimplex', () {
    const inequalities = '''
      (<= (+ (- x_1) x_2 (- x_3)) 2)
      (<= (+ x_1 x_3) 3)
      (<= (- (* 2 x_1) x_2) 4)
    ''';
    final ies = parseInequalities(inequalities);
    final lbl = ies.expand((li) => li.labels).toSet();
    final ids = Map.fromIterables(lbl, List.generate(lbl.length, (i) => i + 1));
    final con = ies.map((li) => li.normalize(ids)).toList();
    final emp = theory.createEmptyProblem();
    final pro = con.fold<LinearProblem>(emp, (p, c) => p.add(c));

    // The function z = 3 + x_1 + x_3 is optimized for x = (3, 2, 0).
    const solution = {'x_1': 3, 'x_2': 2, 'x_3': 0};
    pro.replaceZ(3, mapKeys({'x_1': 1, 'x_2': 0, 'x_3': 1}, ids));
    expect(pro.check(), isTrue);
    expect(mapKeys(pro.assignment, invertMap(ids)), equals(solution));
  });
}
