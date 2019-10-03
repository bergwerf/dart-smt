// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// Davis-Putnam procedure (1960) for deciding SAT
SatResult checkSatByDP(CNF cnf) {
  // Note that neither unit resolution nor intelligent resolution produce new
  // trivial clauses. Therefore we only have to do this once.
  removeTrivialClauses(cnf);

  // Subsumption is expensive, so we only apply it once to remove duplicates.
  applySubsumption(cnf);

  // We start with unit resolution and apply it again after each resolution.
  applyUnitResolution(cnf);
  if (cnf.hasEmptyClause) {
    return SatResult.unsat;
  }

  // DP procedure:
  // + Choose a variable p.
  // + Apply resolution on all pairs V, W such that p in V and ~p in W.
  // + Remove all clauses containing q and ~q for some q.
  // + Remove all clauses that contain p or ~p.
  for (var i = 0; i < cnf.variables.length; i++) {
    final p = cnf.variables[i];

    // Generate all resolutions with p.
    var len = cnf.clauses.length; // We do not check new clauses.
    for (var a = 0; a < len; a++) {
      // Check if the a-th clause contains p or ~p.
      final clauseA = cnf.clauses[a];
      if (!(clauseA.tVars.contains(p) || clauseA.fVars.contains(p))) {
        continue;
      }
      // Try resolution with all next clauses.
      for (var b = a + 1; b < len; b++) {
        final clause = tryResolution(cnf.clauses[a], cnf.clauses[b], p);
        if (clause != null) {
          // If we derive an empty clause the CNF is unsatisfiable.
          if (clause.isEmpty) {
            return SatResult.unsat;
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
  assert(cnf.clauses.isEmpty);
  return SatResult.sat;
}

/// If a clause contains only one literal, then it fixes the assignment for that
/// literal. The negation of this literal can be removed from all clauses. Any
/// clause that contains this literal is automatically true and can also be
/// removed (this is called subsumption).
void applyUnitResolution(CNF cnf) {
  for (var i = 0; i < cnf.clauses.length; i++) {
    final c = cnf.clauses[i];
    if (c.tVars.length + c.fVars.length == 1) {
      // Check if this is a negation and remove the i-th clause.
      final negation = c.fVars.contains(i);
      final variable = c.tVars.union(c.fVars).single;
      cnf.clauses.removeAt(i);
      i--;

      // Remove clauses that contain this literal.
      for (var j = 0; j < cnf.clauses.length; j++) {
        final clause = cnf.clauses[j];
        if (clause.containsLiteral(negation, variable)) {
          cnf.clauses.removeAt(j);
          i -= j <= i ? 1 : 0;
          j--;
        }
      }

      // Remove inverted literal from all clauses.
      for (final clause in cnf.clauses) {
        clause.removeLiteral(!negation, variable);
      }

      // Remove variable from CNF variable list.
      assert(!getVariablesInCNF(cnf.clauses).contains(variable));
      cnf.variables.remove(variable);
    }
  }
}

/// Try to apply resolution on clauses [p] and [q] with respect to variable [v]
/// and check if the resulting clause is trivially true.
Clause tryResolution(Clause p, Clause q, int v) {
  // Check if one clause contains v and the other ~v.
  if ((p.tVars.contains(v) && q.fVars.contains(v)) ||
      (p.fVars.contains(v) && q.tVars.contains(v))) {
    // Check if the disjunction is trivially true.
    final disjunction = Clause(p.tVars.union(q.tVars), p.fVars.union(q.fVars));
    disjunction.tVars.remove(v);
    disjunction.fVars.remove(v);
    if (!isTriviallyTrue(disjunction)) {
      return disjunction;
    }
  }
  // If no resolution is possible or the result is trivially true, return null.
  return null;
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
  return clause.tVars.intersection(clause.fVars).isNotEmpty;
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
