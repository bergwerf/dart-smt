// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// Check if 3-CNF [cnf] is satisfiable using a Conflict-Driven-Clause-Learning
/// (CDCL) algorithm. It is possible to specify a list of rules to start with in
/// [initialize] (unit resolution is not yet applied on these).
SatResult checkSatByCDCL(CNF3 cnf, [List<CDCLRule> initialize]) {
  final rules = initialize ?? [];
  final fixed = <int>{}; // All determined literals.
  final free = cnf.variables.toSet(); // All free (undecided) variables.

  // Add unit propagate rule. This checks if [literal] was already derived or if
  // it creates a contradiction (in which case we do a backjump). Arguments:
  // + [literal]: the literal that is derived.
  // + [currentRule]: index of the rule that is being inspected.
  // + [secondRule]: index of secondary rule that was used.
  //
  // Return value:
  // + -2: Fail (found UNSAT).
  // + -1: Continue normally.
  // + >=0: Stop and continue at this rule index (Backjump).
  int addUnitPropagate(int literal, int currentRule, [int secondRule = -1]) {
    assert(secondRule < currentRule);
    // Check if this literal was already derived.
    if (fixed.contains(literal)) {
      return -1;
    }
    // Check if this literal does not cause a contradiction.
    if (!fixed.contains(-literal)) {
      rules.add(CDCLRule.unitPropagate(literal, currentRule, secondRule));
      free.remove(literal.abs());
      fixed.add(literal);
      return -1;
    }
    // Try a backjump. This contradiction was caused by the current rule, which
    // is a result of the last decision (which was clearly wrong). However some
    // decisions before that may have nothing to do with the derivation of this
    // contradiction. Therefore we insert the negation of the wrong decision as
    // early as possible. This prevents the contradiction from being encountered
    // again under the same unrelated earlier decisions.
    //
    // Thus, we have to find the last decision p (which is the cause of this
    // contradiction), clear all consecutive unrelated decisions before that,
    // and insert a unit propagate rule ~p.
    // TODO
  }

  // Move pointer forward through rules.
  for (var i = 0; i < rules.length; i++) {
    // Derive all possible unit propagate rules given the i-th rule. Note that
    // [addUnitPropagate] takes care of duplicates and backjumps.
    final r = rules[i];
    final result1 = cnf.doubleClauses[-r.literal];
    if (result1 != null) {
      final goto = addUnitPropagate(result1, i);
      if (goto >= 0) {
        i = goto;
        continue;
      } else if (goto == -2) {
        return SatResult.unsat();
      }
    }
    for (var j = 0; j < i; j++) {
      final pair = OrderedLiteralPair(-r.literal, -rules[j].literal);
      final result2 = cnf.tripleClauses[pair];
      if (result2 != null) {
        final goto = addUnitPropagate(result2, i, j);
        if (goto >= 0) {
          i = goto;
          continue;
        } else if (goto == -2) {
          return SatResult.unsat();
        }
      }
    }

    // If no more unit propagate rules can be derived, we have to decide. If
    // there are no free variables left, we have found a satisfying assignment.
    if (i + 1 == rules.length) {
      if (free.isNotEmpty) {
        final p = free.first;
        free.remove(p);
        fixed.add(p);
        rules.add(CDCLRule.decide(p));
      } else {
        final assignment = Map.fromEntries(rules.map((r) => r.entry));
        return SatResult.sat(assignment);
      }
    }
  }
  throw StateError('algorithm has escaped');
}

class CDCLRule {
  final int literal;
  final bool decide;

  /// Indices of CDCL rules that were used to derive this literal. This is used
  /// to determine an optimal backjump.
  final int by1, by2;

  CDCLRule.unitPropagate(this.literal, this.by1, this.by2) : decide = false;

  CDCLRule.decide(this.literal)
      : decide = true,
        by1 = -1,
        by2 = -1;

  // Get entry for an assignment map.
  MapEntry<int, bool> get entry => MapEntry(literal.abs(), !literal.isNegative);
}
