// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

import 'package:smt/sat.dart';
import 'package:test/test.dart';

/// Problem of the non-smoking student advisors.
const nonSmokingStudentAdvisors = '''
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
(macro tautology (-> (and
  (-> (and #good-natured #tenured #professor) #dynamic)
  (-> (and #grumpy #student-advisor) #plays-slot-machine)
  (-> (and #smoke #wearing-cap) #phlegmatic)
  (-> (and #comical #student-advisor) #professor)
  (-> (and #smoke (~ #tenured)) #nervous)
  (-> (and #phlegmatic #tenured #wearing-cap) #comical)
  (-> (and #student-advisor (~ #play-stock-market)) #scholar)
  (-> (and #relaxed #student-advisor) #creative)
  (-> (and #creative #scholar (~ #plays-slot-machine)) #wearing-cap)
  (-> (and #nervous #smoke) #plays-slot-machine)
  (-> (and #student-advisor #plays-slot-machine) (~ #smoke))
  (-> (and #creative #good-natured #play-stock-market) #wearing-cap)
  ) (~ (and #student-advisor #smoke))))

% We do so by checking if its negation is satisfiable.
(~ #tautology)
''';

/// Macros to formulate arithmetic as SAT problem
const arithmeticMacros = '''
% Helper macros
(macro add-bit   (a b c d)  (<-> a b c d))
(macro carry-bit (a b c c') (<-> c' (or (and a b) (and a c) (and b c))))
(macro add-fits  (c0 cn)    (/\ (~ c0) (~ cn)))

% Binary addition constraints
(macro add-phi (n) (/\* i 1 n (and
  (add-bits a_i b_i c_i d_i)
  (carry-bits a_i b_i c_i (_ c (sub i 1)))
  (add-fits c_0 c_n)
)))

% Add two given numbers (result is stored in d_i)
(macro add (n a b) (and
  (add-phi n)
  (/\* i 1 n (? a_i))
  (/\* i 1 n (? b_i))
)))
''';

void main() {
  test('checkSatByDP(LL)', () {
    /// Solve the problem of the non-smoking student advisors.
    final cnf = compileCplToCNF(nonSmokingStudentAdvisors);
    expect(checkSatByDP(copyCNF(cnf)), equals(SatResult.unsat));
    expect(checkSatByDPLL(copyCNF(cnf)), equals(SatResult.unsat));
  });
}
