// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// Control if expensive asserts are enabled.
var enableCDCLChecks = false;

/// Check if a 3-CNF is satisfiable using a Conflict-Driven-Clause-Learning
/// (CDCL) algorithm. It is possible to specify a list of rules to start with.
SatResult checkSatByCDCL(CDCLInput input) {
  final rand = Random();
  final cnf = input.cnf;
  final free = cnf.variables.toSet(); // All free (undecided) variables.
  final fixed = <int, int>{}; // literal => rule index that sets this literal.
  final rules = input.rules?.toList() ?? [];

  // Add initialized literals to fixed set and check for contradictions.
  for (var i = 0; i < rules.length; i++) {
    final p = rules[i].literal;
    if (fixed.containsKey(-p)) {
      return SatResult.unsat();
    }
    fixed[p] = i;
    free.remove(p.abs());
  }

  /// Add unit propagate rule. This checks if [p] was already derived or if it
  /// creates a contradiction (in which case we do a backjump). Arguments:
  /// + [p]: Literal that is derived.
  /// + [decideA], [decideB]: Index of the last decisions this literal was
  ///   derived with such that [decideA] > [decideB].
  ///
  /// Return value:
  /// + -2: Fail (found UNSAT).
  /// + -1: Continue normally.
  /// + >=0: Stop and continue at this rule index (Backjump).
  int addUnitPropagate(int p, int decideA, [int decideB = -1]) {
    assert(decideA == -1 || rules[decideA].decide);
    assert(decideB == -1 || rules[decideB].decide);
    assert(decideA == -1 || decideA != decideB);

    // Check if this literal was already derived.
    if (fixed.containsKey(p)) {
      return -1;
    }

    // Check if this literal does not contradict the current assignment.
    final notP = fixed[-p];
    if (notP == null) {
      rules.add(CDCLRule.unitPropagate(p, decideA, decideB));
      fixed[p] = rules.length - 1;
      free.remove(p.abs());
      return -1;
    }

    // [p] and [notP] form a contradiction.
    //
    // Try a backjump; [p] was derived using the last decision [lD] (so for this
    // decision q we can proceed to trying ~q for this branch). However some
    // decisions before that may have nothing to do with the derivation of [p].
    // We insert ~q as early as possible. This prevents p from being encountered
    // again under the same unrelated earlier decisions.
    final lD = decideA;
    assert(!enableCDCLChecks || rules.lastIndexWhere((r) => r.decide) == lD);
    if (lD == -1) {
      // Fail
      return -2;
    }

    // Compute second last decision (slD) this contradiction was based on (we
    // always have slD != lD). If slD == -1, then p.decideB = -1 and
    // (notP.decideA = lD = p.decideA, notP.decideB = -1), or notP.decideA = -1.
    //
    // There are three scenarios:
    // + slD == -1. In this case the decision q at [lD] derived both p and ~p
    //   and we continue with ~q before the first decision.
    // + slD != -1. In this case we find the next decision (this is either [lD]
    //   or a decision that was not involved in deriving the contradiction) and
    //   continue with ~q.
    final npR = rules[notP];
    final slD = max(decideB, npR.decideA == lD ? npR.decideB : npR.decideA);
    var newStart = slD;
    do {
      newStart++;
    } while (!rules[newStart].decide);
    assert(newStart <= lD);

    // Create backjump rule.
    final q = rules[lD].literal;
    final bR = CDCLRule.unitPropagate(-q, slD, -1);

    // If slD == -1, check if the backjump retains satisfiability (in other
    // cases we keep prior decisions and this branch might not be satisfiable).
    assert(!(enableCDCLChecks && slD == -1) ||
        _satEquivalent(cnf, input.rules, rules.sublist(0, newStart)..add(bR)));

    // Pop all rules until [newStart].
    for (var i = rules.length; i > newStart; i--) {
      final r = rules.removeLast().literal;
      fixed.remove(r);
      free.add(r.abs());
    }

    // Insert backjump rule.
    assert(rules.length == newStart);
    rules.add(bR);
    fixed[-q] = newStart;
    free.remove(q.abs());
    return rules.length - 2; // Will ++ to process ~q rule.
  }

  // Move pointer forward through rules.
  RULES:
  for (var i = 0; i < rules.length; i++) {
    // Check if [free] and [fixed] are correct.
    assert(!enableCDCLChecks || _validState(cnf.variables, free, fixed, rules));

    // Derive all possible unit propagate rules given the i-th rule. Note that
    // [addUnitPropagate] takes care of duplicates and backjumps.
    final ri = rules[i];

    // Add all unit propagate rules implied by double clauses.
    final implied1 = cnf.doubleClauses[ri.literal];
    if (implied1 != null) {
      for (final literal in implied1) {
        final goto = addUnitPropagate(literal, ri.decideA, ri.decideB);
        if (goto >= 0) {
          i = goto;
          continue RULES;
        } else if (goto == -2) {
          return SatResult.unsat();
        }
      }
    }

    // Combine this rule with each previous rule and add all unit propagate
    // rules implied by triple clauses.
    for (var j = 0; j < i; j++) {
      final rj = rules[j];
      final pair = OrderedLiteralPair(ri.literal, rj.literal);
      final implied2 = cnf.tripleClauses[pair];
      if (implied2 != null) {
        // Determine secondary decision index for all implications. Note that
        // since ri was derived after rj, ri.decideA >= rj.decideA.
        assert(ri.decideA >= rj.decideA);
        final decideB = max(
            ri.decideB, // We do not want decideB = ri.decideA
            ri.decideA == rj.decideA ? rj.decideB : rj.decideA);

        // Add unit propagate for all implications.
        for (final literal in implied2) {
          final goto = addUnitPropagate(literal, ri.decideA, decideB);
          if (goto >= 0) {
            i = goto;
            continue RULES;
          } else if (goto == -2) {
            return SatResult.unsat();
          }
        }
      }
    }

    // If no more unit propagate rules can be derived, we have to decide. If
    // there are no free variables left, we have found a satisfying assignment.
    if (i + 1 == rules.length) {
      if (free.isNotEmpty) {
        // Randomly choosing a decision turns out to be beneficial.
        final p = free.elementAt(rand.nextInt(free.length));
        // Note that we set this rule to depend on itself.
        rules.add(CDCLRule.decide(p, i + 1));
        fixed[p] = i + 1;
        free.remove(p);
      } else {
        final assignment = Map.fromEntries(rules.map((r) => r.entry));
        return SatResult.sat(assignment);
      }
    }
  }
  throw StateError('algorithm has escaped');
}

/// Check if state ([all], [free], [fixed], [rules]) is valid (for debugging).
bool _validState(
    Set<int> all, Set<int> free, Map<int, int> fixed, List<CDCLRule> rules) {
  if (!(fixed.length == rules.length)) {
    return false;
  } else if (!(all.length == free.length + fixed.length)) {
    return false;
  }
  for (var i = 0; i < rules.length; i++) {
    final r = rules[i];
    final p = r.literal;
    if (fixed[p] != i || free.contains(p.abs())) {
      return false;
    } else if (r.decideA != -1 && !rules[r.decideA].decide) {
      return false;
    } else if (r.decideB != -1 && !rules[r.decideB].decide) {
      return false;
    }
  }
  return true;
}

/// Check if [cnf] has the same satisfiability with [rules1] as with [rules2]
/// using DPLL (for debugging).
bool _satEquivalent(CNF3 cnf, List<CDCLRule> rules1, List<CDCLRule> rules2) {
  final r1 = checkSatByDPLL(convertCDCLInputToCNF(CDCLInput(cnf, rules1)));
  final r2 = checkSatByDPLL(convertCDCLInputToCNF(CDCLInput(cnf, rules2)));
  return r1.satisfiable == r2.satisfiable;
}

class CDCLRule {
  final int literal;
  final bool decide;

  /// To quickly compute backjumps, we store the index of the last two decisions
  /// this rule is based on. [decideB] should be less than [decideA].
  final int decideA, decideB;

  CDCLRule.unitPropagate(this.literal, this.decideA, this.decideB)
      : decide = false,
        assert(decideA == -1 || decideA > decideB);

  CDCLRule.decide(this.literal, this.decideA)
      : decide = true,
        decideB = -1;

  // Get entry for an assignment map.
  MapEntry<int, bool> get entry => MapEntry(literal.abs(), !literal.isNegative);

  @override
  String toString() => decide ? '$literal^' : '$literal';
}
