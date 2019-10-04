// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

/// Note that this file contains two older algorithms for SAT problems: DP and
/// DPLL. A faster and more space efficient algorithm is CDCL.
part of smt.sat;

class SatResult {
  final bool satisfiable;
  final Map<int, bool> assignment;

  SatResult(this.satisfiable, [this.assignment]);
  SatResult.sat([this.assignment]) : satisfiable = true;
  SatResult.unsat()
      : satisfiable = false,
        assignment = null;
}

/// Check if [cnf] is satisfiable using the Davis-Putnam-Logemann-Loveland
/// method (1962). To get a variable assignment in the case of SAT, pass an
/// empty map to [assign].
///
/// DPLL method:
/// + Apply unit resolution.
/// + Check for empty clause (UNSAT) or no clauses (SAT).
/// + Choose a variable p.
/// + Try DPLL with extra clause {p} and return SAT if it returns SAT.
/// + Return the result of DPLL with extra clause {~p}.
SatResult checkSatByDPLL(CNF cnf, {Map<int, bool> assign}) {
  applyUnitResolution(cnf, assign);
  if (cnf.isEmpty) {
    return SatResult.sat(assign);
  } else if (cnf.hasEmptyClause) {
    return SatResult.unsat();
  } else {
    // Choose a variable p.
    final p = cnf.variables.first;
    // Copy CNF and assingment for first search branch.
    final cnf1 = copyCNF(cnf)..clauses.add(Clause({p}, {}));
    final assign1 = assign == null ? null : Map.of(assign);
    final result = checkSatByDPLL(cnf1, assign: assign1);
    if (result.satisfiable) {
      return result;
    } else {
      // Re-use CNF and assignment for second search branch.
      final cnf2 = copyCNF(cnf)..clauses.add(Clause({}, {p}));
      return checkSatByDPLL(cnf2, assign: assign);
    }
  }
}

/// Check if [cnf] is satisfiable using the Davis-Putnam procedure (1960).
///
/// DP procedure:
/// + Choose a variable p.
/// + Apply resolution on all pairs V, W such that p in V and ~p in W.
/// + Remove all clauses containing q and ~q for some q.
/// + Remove all clauses that contain p or ~p.
///
/// A truth assignment could be constructed by keeping intermediary CNFs and
/// applying unit resolution backwards (before eliminating all clauses we have
/// some singleton clauses).
SatResult checkSatByDP(CNF cnf) {
  // Note that neither unit resolution nor intelligent resolution produce new
  // trivial clauses. Therefore we only have to do this once. We also apply
  // subsumption once to remove duplicate clauses in the input.
  removeTrivialClauses(cnf);
  applySubsumption(cnf);

  // Follow procedure.
  for (var i = 0; i < cnf.variables.length; i++) {
    final p = cnf.variables[i];

    // Generate all resolutions with p.
    var len = cnf.clauses.length; // We do not check new clauses.
    for (var a = 0; a < len; a++) {
      // Check if the a-th clause contains p or ~p.
      final clauseA = cnf.clauses[a];
      if (!(clauseA.pos.contains(p) || clauseA.neg.contains(p))) {
        continue;
      }

      // Try resolution with all next clauses.
      for (var b = a + 1; b < len; b++) {
        final clause = tryResolution(cnf.clauses[a], cnf.clauses[b], p);
        if (clause != null) {
          // If we derive an empty clause the CNF is unsatisfiable.
          if (clause.isEmpty) {
            return SatResult.unsat();
          } else {
            // It is possible we derived a singleton clause {q}, and in this
            // case we could apply unit resolution here. It is not clear if this
            // would generate a significant advantage.
            cnf.clauses.add(clause);
          }
        }
      }

      // Remove this clause since it contains p or ~p.
      cnf.clauses.removeAt(a);
      len--;
      a--;
    }
  }

  // We eliminated all variables.
  assert(cnf.isEmpty);
  return SatResult.sat();
}

/// Try to apply resolution on clauses [p] and [q] with respect to variable [v]
/// and check if the resulting clause is trivially true.
Clause tryResolution(Clause p, Clause q, int v) {
  // Check if one clause contains v and the other ~v.
  if ((p.pos.contains(v) && q.neg.contains(v)) ||
      (p.neg.contains(v) && q.pos.contains(v))) {
    // Check if the disjunction is trivially true.
    final disjunction = Clause(p.pos.union(q.pos), p.neg.union(q.neg));
    disjunction.pos.remove(v);
    disjunction.neg.remove(v);
    if (!isTriviallyTrue(disjunction)) {
      return disjunction;
    }
  }
  // If no resolution is possible or the result is trivially true, return null.
  return null;
}

/// If a clause contains only one literal, then it fixes the assignment for that
/// literal. The negation of this literal can be removed from all clauses. Any
/// clause that contains this literal is automatically true and can also be
/// removed (subsumption). If [assignment] is not null, then any singleton
/// clauses will be stored in there.
void applyUnitResolution(CNF cnf, [Map<int, bool> assignment]) {
  for (var i = 0; i < cnf.clauses.length; i++) {
    final c = cnf.clauses[i];
    if (c.pos.length + c.neg.length == 1) {
      // Check if this is a positive literal and remove the i-th clause.
      final positive = c.pos.isNotEmpty;
      final variable = positive ? c.pos.single : c.neg.single;
      cnf.clauses.removeAt(i);

      // If an assignment map is given, store an assignment for this variable.
      if (assignment != null) {
        assignment[variable] = positive;
      }

      // Remove clauses that contain this literal.
      for (var j = 0; j < cnf.clauses.length; j++) {
        final clause = cnf.clauses[j];
        if (clause.containsLiteral(positive, variable)) {
          cnf.clauses.removeAt(j);
          j--;
        }
      }

      // Remove inverted literal from all clauses.
      for (final clause in cnf.clauses) {
        clause.removeLiteral(!positive, variable);
      }

      // Remove variable from CNF variable list.
      assert(!getVariablesInCNF(cnf.clauses).contains(variable));
      cnf.variables.remove(variable);

      // We may have created new singleton clauses.
      i = 0;
    }
  }
}

/// Apply subsumption to [cnf].
void applySubsumption(CNF cnf) {
  cnf.clauses.removeWhere((c1) {
    return cnf.clauses.any((c2) => c1 != c2 && c2.containsClause(c1));
  });
  updateCNFVariables(cnf);
}

/// Check if [clause] is trivially true (if it contains P and ~P for some P).
bool isTriviallyTrue(Clause clause) {
  return clause.pos.intersection(clause.neg).isNotEmpty;
}

/// Clauses that contain both P and ~P for some variable P can be removed.
void removeTrivialClauses(CNF cnf) {
  cnf.clauses.removeWhere(isTriviallyTrue);
  updateCNFVariables(cnf);
}

/// Update the variable list of [cnf].
void updateCNFVariables(CNF cnf) {
  cnf.variables.removeWhere(
      (v) => !cnf.clauses.any((clause) => clause.containsVariable(v)));
}
