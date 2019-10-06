// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

import 'package:smt/sat.dart';
import '../test/utils.dart';

void main() {
  final t = Stopwatch();
  t.start();
  for (var n = 8; n < 20; n++) {
    print('Solving $n-queens problem');

    // Compiling
    t.reset();
    final cnf = compileCNF('(n-queens $n)', libs: ['cpl/n_queens.txt']);
    print('Compiled DPLL CNF in ${t.elapsedMilliseconds}ms');
    t.reset();
    final ci = compileCDCLInput('(n-queens $n)', libs: ['cpl/n_queens.txt']);
    print('Compiled CDCL 3-CNF in ${t.elapsedMilliseconds}ms');

    // Checking
    t.reset();
    final r1 = checkSatByDPLL(cnf, assign: {});
    print('Solved in ${t.elapsedMilliseconds}ms by DPLL (${r1.summary})');
    t.reset();
    final r2 = checkSatByCDCL(ci);
    print('Solved in ${t.elapsedMilliseconds}ms by CDCL (${r2.summary})');
  }
}
