// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

import 'dart:io';
import 'package:smt/cpl.dart';
import 'package:smt/sat.dart';
import 'package:test/test.dart';

/// Read libraries and append with line endings.
String readLibs(List<String> libraries) =>
    libraries.map((path) => File('test/$path').readAsStringSync()).join('\n');

/// Compile [input] to [CNF].
CNF compileCNF(String input,
    {List<String> libs: const [],
    Map<String, bool> assign,
    bool tseytin: false}) {
  final str = '${readLibs(libs)}\n$input';
  final clauses = compileCplToCnf(str, assignments: assign, tseytin: tseytin);
  return convertClausesToCNF(clauses);
}

/// Compile [input] to [CDCLInput].
CDCLInput compileCDCLInput(String input,
    {List<String> libs: const [], Map<String, bool> assign}) {
  final str = '${readLibs(libs)}\n$input';
  final clauses = compileCplToCnf(str, assignments: assign, tseytin: true);
  return convertClausesToCDCLInput(clauses);
}

/// Generate assignment for an [n]-bit binary addition of [a] and [b].
Map<String, bool> computeAddAssignment(int n, int a, int b,
    {bool negate: false, bool tseytin: false}) {
  final assignment = <String, bool>{};
  for (var i = 0; i < n; i++) {
    assignment['a_${n - i}'] = ((a >> i) & 1) == 1;
    assignment['b_${n - i}'] = ((b >> i) & 1) == 1;
  }
  return assignment;
}

/// Construct numeric answer (d) of binary addition [solution].
int computeAddSolution(Map<String, bool> solution) {
  var d = 0;
  for (var i = 0; i < 8; i++) {
    d ^= (solution['d_${8 - i}'] ? 1 : 0) << i;
  }
  return d;
}

void main() {
  // Compile a few CNFs for testing.
  final testCNF1 = compileCNF('(~ #non-smoking-student-advisors)',
      libs: ['cpl/student_advisors.txt']);
  final testCNF2 = compileCNF('(add 8 a b)',
      libs: ['cpl/binary_add.txt'], assign: computeAddAssignment(8, 42, 24));

  // Check DP algorithm on some cases.
  test('checkSatByDP', () {
    expect(checkSatByDP(copyCNF(testCNF1)).satisfiable, isFalse);
    expect(checkSatByDP(copyCNF(testCNF2)).satisfiable, isTrue);
  });

  // Check DPLL algorithm on some cases.
  test('checkSatByDPLL', () {
    expect(checkSatByDPLL(copyCNF(testCNF1)).satisfiable, isFalse);

    // Solve binary addition and check resulting assignment.
    final result = checkSatByDPLL(copyCNF(testCNF2), assign: {});
    final assign = mapKeys(result.assignment, testCNF2.labels);
    expect(result.satisfiable, isTrue);
    expect(evaluateCNF(testCNF2, result.assignment), isTrue);
    expect(computeAddSolution(assign), equals(42 + 24));

    // Solve negation of binary addition with Tseytin transformation.
    final cnf3 = compileCNF('(~ (add 8 a b))',
        assign: computeAddAssignment(8, 42, 24),
        libs: ['cpl/binary_add.txt'],
        tseytin: true);

    expect(checkSatByDPLL(copyCNF(cnf3)).satisfiable, isFalse);
  });

  // Check CNF3 generation and CNF3 to CNF conversion.
  test('convertClausesToCDCLInput', () {
    final input = compileCDCLInput('(add 8 a b)',
        libs: ['cpl/binary_add.txt'], assign: computeAddAssignment(8, 42, 24));
    final cnf = converCDCLInputToCNF(input);
    expect(checkSatByDPLL(cnf).satisfiable, isTrue);
  });

  // Check CDCL algorithm on some cases.
  test('checkSatByCDCL', () {
    // Enable heavy runtime checks.
    enableCDCLChecking = true;

    final input1 = compileCDCLInput('(~ #non-smoking-student-advisors)',
        libs: ['cpl/student_advisors.txt']);
    final input2 = compileCDCLInput('(add 8 a b)', //
        assign: computeAddAssignment(8, 42, 24),
        libs: ['cpl/binary_add.txt']);

    final result1 = checkSatByCDCL(input1.cnf, input1.rules);
    final result2 = checkSatByCDCL(input2.cnf, input2.rules);
    final assign2 = mapKeys(result2.assignment, input2.cnf.labels);

    expect(result1.satisfiable, isFalse);
    expect(result2.satisfiable, isTrue);
    expect(computeAddSolution(assign2), equals(42 + 24));

    enableCDCLChecking = false;
  });
}
