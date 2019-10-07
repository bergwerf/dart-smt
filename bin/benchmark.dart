// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

import 'package:smt/cpl.dart';
import 'package:smt/sat.dart';
import '../test/utils.dart';

/// [args]: Use `boards` to see visual solutions.
void main(List<String> args) {
  final showBoards = args.contains('boards');
  void info(String message) => showBoards ? print(message) : null;
  void table(List<String> cols) =>
      showBoards ? null : print(cols.map((s) => s.padRight(15)).join(''));

  final t = Stopwatch()..start();
  table(['n', 'DPLL (ms)', 'CDCL (ms)']);

  for (var n = 1; n < 20; n++) {
    info('Solving $n-queens problem');

    // Compiling
    t.reset();
    final cnf = compileCNF('(n-queens $n)', libs: ['cpl/n_queens.txt']);
    info('Compiled DPLL CNF in ${t.elapsedMilliseconds}ms');
    t.reset();
    final ci = compileCDCLInput('(n-queens $n)', libs: ['cpl/n_queens.txt']);
    info('Compiled CDCL 3-CNF in ${t.elapsedMilliseconds}ms');

    // Checking
    t.reset();
    final r1 = checkSatByDPLL(cnf, assign: {});
    final dpllMs = t.elapsedMilliseconds;
    info('Solved in ${dpllMs}ms by DPLL (${r1.summary})');
    info(nQueensSolutionBoard(n, mapKeys(r1.assignment ?? {}, cnf.labels)));
    t.reset();
    final r2 = checkSatByCDCL(ci);
    final cdclMs = t.elapsedMilliseconds;
    info('Solved in ${cdclMs}ms by CDCL (${r2.summary})');
    info(nQueensSolutionBoard(n, mapKeys(r2.assignment ?? {}, ci.cnf.labels)));

    // Stats
    table(['$n', '$dpllMs', '$cdclMs']);
  }
}

/// Generate string representation of a [solution] for the [n]-queens problem.
String nQueensSolutionBoard(int n, Map<String, bool> solution) {
  if (solution.isEmpty) {
    return '(no solution)';
  }
  const queen = '♛';
  final board = StringBuffer();
  board.writeln('┌${'───┬' * (n - 1)}───┐');
  for (var i = 1; i <= n; i++) {
    for (var j = 1; j <= n; j++) {
      assert(solution.containsKey('p_${i}_$j'));
      board.write('| ${solution['p_${i}_$j'] ? queen : ' '} ');
    }
    board.writeln('|');
    if (i != n) {
      board.writeln('├${'───┼' * (n - 1)}───┤');
    }
  }
  board.write('└${'───┴' * (n - 1)}───┘');
  return board.toString();
}
