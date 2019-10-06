// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

import 'package:smt/cpl.dart';
import 'package:smt/sat.dart';
import 'package:test/test.dart';
import 'utils.dart';

void main() {
  // Negation of smoking student advisors: UNSAT
  final testAdvisors = compileCNF('(~ #non-smoking-student-advisors)',
      libs: ['cpl/student_advisors.txt'], tseytin: false);

  // Binary addition: SAT
  final testBinAdd = compileCNF('(add 8 a b)',
      libs: ['cpl/binary_add.txt'],
      assign: intToBits(8, {'a': 42, 'b': 24}),
      tseytin: false);

  // Negation of binary addition: UNSAT
  final testBinAddNeg = compileCNF('(~ (add 8 a b))',
      libs: ['cpl/binary_add.txt'], assign: intToBits(8, {'a': 42, 'b': 24}));

  // 8-queens problem: SAT
  final test8queens = compileCNF('(8-queens)', libs: ['cpl/n_queens.txt']);

  // Check DP algorithm on some cases.
  test('checkSatByDP', () {
    expect(checkSatByDP(copyCNF(testAdvisors)).satisfiable, isFalse);
    expect(checkSatByDP(copyCNF(testBinAdd)).satisfiable, isTrue);
    //expect(checkSatByDP(copyCNF(testBinAddNeg)).satisfiable, isFalse);
    //expect(checkSatByDP(copyCNF(test8queens)).satisfiable, isTrue);
  });

  // Check DPLL algorithm on some cases.
  test('checkSatByDPLL', () {
    expect(checkSatByDPLL(copyCNF(testAdvisors)).satisfiable, isFalse);
    expect(checkSatByDPLL(copyCNF(testBinAddNeg)).satisfiable, isFalse);
    //expect(checkSatByDPLL(copyCNF(test8queens)).satisfiable, isTrue);

    // Solve binary addition and check resulting assignment.
    final result = checkSatByDPLL(copyCNF(testBinAdd), assign: {});
    final assign = mapKeys(result.assignment, testBinAdd.labels);
    expect(result.satisfiable, isTrue);
    expect(evaluateCNF(testBinAdd, result.assignment), isTrue);
    expect(bitsToInt(assign, 8, 'd'), equals(42 + 24));
  });

  // Check CNF3 generation and CNF3 to CNF conversion.
  test('convertClausesToCDCLInput', () {
    final input = compileCDCLInput('(add 8 a b)',
        libs: ['cpl/binary_add.txt'], assign: intToBits(8, {'a': 42, 'b': 24}));
    final cnf = convertCDCLInputToCNF(input);
    expect(checkSatByDPLL(cnf).satisfiable, isTrue);
  });

  // Check CDCL algorithm on some cases.
  test('checkSatByCDCL', () {
    // Enable heavy runtime checks.
    enableCDCLChecks = true;

    final testAdvisors = compileCDCLInput('(~ #non-smoking-student-advisors)',
        libs: ['cpl/student_advisors.txt']);
    final testBinAdd = compileCDCLInput('(add 8 a b)', //
        assign: intToBits(8, {'a': 42, 'b': 24}),
        libs: ['cpl/binary_add.txt']);
    final test8queens = compileCDCLInput('(8-queens)', //
        libs: ['cpl/n_queens.txt']);

    expect(checkSatByCDCL(testAdvisors).satisfiable, isFalse);
    expect(checkSatByCDCL(test8queens).satisfiable, isTrue);

    // Solve binary addition and check resulting assignment.
    final result = checkSatByCDCL(testBinAdd);
    final assign = mapKeys(result.assignment, testBinAdd.cnf.labels);

    expect(result.satisfiable, isTrue);
    expect(bitsToInt(assign, 8, 'd'), equals(42 + 24));

    enableCDCLChecks = false;
  });
}
