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

/// Compile [input] to a CNF instance.
CNF compileCNF(String input,
    {List<String> libs: const [],
    Map<String, bool> assign,
    bool tseytin: false}) {
  final str = '${readLibs(libs)}\n$input';
  final clauses = compileCplToCnf(str, assignments: assign, tseytin: tseytin);
  return convertClausesToCNF(clauses);
}

/// Compile [input] to a 3-CNF instance.
Pair<CNF3, List<CDCLRule>> compileCNF3(String input,
    {List<String> libs: const [], Map<String, bool> assign}) {
  final str = '${readLibs(libs)}\n$input';
  final clauses = compileCplToCnf(str, assignments: assign, tseytin: true);
  return convertClausesToCNF3(clauses);
}

/// Generate assignment for an [n]-bit binary addition of [a] and [b].
Map<String, bool> generateAddAssignment(int n, int a, int b,
    {bool negate: false, bool tseytin: false}) {
  final assignment = <String, bool>{};
  for (var i = 0; i < n; i++) {
    assignment['a_${n - i}'] = ((a >> i) & 1) == 1;
    assignment['b_${n - i}'] = ((b >> i) & 1) == 1;
  }
  return assignment;
}

void main() {
  test('checkSatByDP(LL)', () {
    // Solve the problem of the non-smoking student advisors.
    final cnf1 = compileCNF('(~ #non-smoking-student-advisors)',
        libs: ['cpl/student_advisors.txt']);

    expect(checkSatByDP(copyCNF(cnf1)).satisfiable, isFalse);
    expect(checkSatByDPLL(copyCNF(cnf1)).satisfiable, isFalse);

    // Solve binary addition with DP.
    final cnf2 = compileCNF('(add 8 a b)', //
        assign: generateAddAssignment(8, 42, 24),
        libs: ['cpl/binary_add.txt']);

    expect(checkSatByDP(copyCNF(cnf2)).satisfiable, isTrue);

    // Solve binary addition with DPLL and check resulting assignment.
    final result = checkSatByDPLL(copyCNF(cnf2), assign: {});
    expect(result.satisfiable, isTrue);
    expect(evaluateCNF(cnf2, result.assignment), isTrue);

    // Convert the result back into an integer value for d.
    final assign = mapKeys(result.assignment, cnf2.labels);
    var d = 0;
    for (var i = 0; i < 8; i++) {
      d ^= (assign['d_${8 - i}'] ? 1 : 0) << i;
    }
    expect(d, equals(42 + 24));

    // Solve negation of binary addition with Tseytin transformation and DPLL.
    final cnf3 = compileCNF('(~ (add 8 a b))',
        assign: generateAddAssignment(8, 42, 24),
        libs: ['cpl/binary_add.txt'],
        tseytin: true);

    expect(checkSatByDPLL(copyCNF(cnf3)).satisfiable, isFalse);
  });

  test('convertClausesToCNF3', () {
    final init = compileCNF3('(add 8 a b)', //
        assign: generateAddAssignment(8, 42, 24),
        libs: ['cpl/binary_add.txt']);
    final cnf = convertCNF3AndRulesToCNF(init.a, init.b);
    expect(checkSatByDPLL(cnf).satisfiable, isTrue);
  });

  test('checkSatByCDCL', () {
    final init1 = compileCNF3('(~ #non-smoking-student-advisors)',
        libs: ['cpl/student_advisors.txt']);
    final init2 = compileCNF3('(add 8 a b)', //
        assign: generateAddAssignment(8, 42, 24),
        libs: ['cpl/binary_add.txt']);

    expect(checkSatByCDCL(init1.a, init1.b).satisfiable, isFalse);
    expect(checkSatByCDCL(init2.a, init2.b).satisfiable, isTrue);
  }, skip: true);
}
