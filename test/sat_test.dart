// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

import 'package:smt/cpl.dart';
import 'package:smt/sat.dart';
import 'package:test/test.dart';

/// Problem of the non-smoking student advisors.
const nonSmokingStudentAdvisors = r'''
% Translation to propositions
(macro good-natured A)
(macro grumpy (~ A))
(macro tenured B)
(macro professor C)
(macro dynamic D)
(macro phlegmatic (~ D))
(macro wearing-cap E)
(macro smoke F)
(macro comical G)
(macro relaxed H)
(macro nervous (~ H))
(macro play-stock-market I)
(macro scholar J)
(macro creative K)
(macro plays-slot-machine L)
(macro student-advisor M)

% We want to test if this is a tautology
(macro non-smoking-student-advisors (-> (and
  (-> (/\ #good-natured #tenured #professor) #dynamic)
  (-> (/\ #grumpy #student-advisor) #plays-slot-machine)
  (-> (/\ #smoke #wearing-cap) #phlegmatic)
  (-> (/\ #comical #student-advisor) #professor)
  (-> (/\ #smoke (~ #tenured)) #nervous)
  (-> (/\ #phlegmatic #tenured #wearing-cap) #comical)
  (-> (/\ #student-advisor (~ #play-stock-market)) #scholar)
  (-> (/\ #relaxed #student-advisor) #creative)
  (-> (/\ #creative #scholar (~ #plays-slot-machine)) #wearing-cap)
  (-> (/\ #nervous #smoke) #plays-slot-machine)
  (-> (/\ #student-advisor #plays-slot-machine) (~ #smoke))
  (-> (/\ #creative #good-natured #play-stock-market) #wearing-cap)
  ) (~ (/\ #student-advisor #smoke))))

% The CNF of the original question is huge (size > 20 million)
(~ #non-smoking-student-advisors)
''';

/// Macros to formulate arithmetic as SAT problem
const arithmeticMacros = r'''
% Helper macros
(macro add-bit   (a b c d)  (iff a b c d))
(macro carry-bit (a b c c') (iff c' (or (/\ a b) (/\ a c) (/\ b c))))
(macro add-fits  (c0 cn)    (/\ (~ c0) (~ cn)))

% Binary addition constraints
(macro add-phi (n) (/\* i 1 n (and
  (add-bit a_i b_i c_i d_i)
  (carry-bit a_i b_i c_i (_ c (sub i 1)))
  (add-fits c_0 c_n)
)))

% Add two given numbers (result is stored in d_i)
% Note that the bits are numbered from left to right starting with 1.
(macro add (n a b) (and
  (add-phi n)
  (/\* i 1 n (? a_i))
  (/\* i 1 n (? b_i))
))
''';

/// Shorthand to compile [input] to a CNF instance.
CNF compileCNF(String input, {Map<String, bool> assign, bool tseytin: false}) {
  final clauses = compileCplToCnf(input, assignments: assign, tseytin: tseytin);
  return convertClausesToCNF(clauses);
}

/// Build CNF that represents an [n]-bit binary addition of [a] and [b].
CNF buildBinaryAddCNF(int a, int b, int n,
    {bool negate: false, bool tseytin: false}) {
  // Generate assignment for bits in a and b.
  final assignment = <String, bool>{};
  for (var i = 0; i < n; i++) {
    assignment['a_${n - i}'] = ((a >> i) & 1) == 1;
    assignment['b_${n - i}'] = ((b >> i) & 1) == 1;
  }
  final adder = negate ? '(~ (add $n a b))' : '(add $n a b)';
  return compileCNF('$arithmeticMacros $adder',
      assign: assignment, tseytin: tseytin);
}

void main() {
  test('checkSatByDP(LL)', () {
    // Solve the problem of the non-smoking student advisors.
    final cnf1 = compileCNF(nonSmokingStudentAdvisors);
    expect(checkSatByDP(copyCNF(cnf1)).satisfiable, isFalse);
    expect(checkSatByDPLL(copyCNF(cnf1)).satisfiable, isFalse);

    // Solve binary addition with DP.
    final cnf2 = buildBinaryAddCNF(42, 24, 8);
    expect(checkSatByDP(copyCNF(cnf2)).satisfiable, isTrue);

    // Solve binary addition with DPLL and check resulting assignment.
    final result = checkSatByDPLL(copyCNF(cnf2), assign: {});
    expect(result.satisfiable, isTrue);
    expect(evaluateCNF(cnf2, result.assignment), isTrue);

    // Convert the result back into an integer value for d.
    var d = 0;
    final assign = result.assignment.map((k, v) => MapEntry(cnf2.labels[k], v));
    for (var i = 0; i < 8; i++) {
      d ^= (assign['d_${8 - i}'] ? 1 : 0) << i;
    }
    expect(d, equals(42 + 24));

    // Solve negation of binary addition with Tseytin transformation and DPLL.
    final cnf3 = buildBinaryAddCNF(42, 24, 8, negate: true, tseytin: true);
    expect(checkSatByDPLL(copyCNF(cnf3)).satisfiable, isFalse);
  });
}
