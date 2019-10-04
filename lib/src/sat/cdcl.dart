// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// Check if 3-CNF [cnf] is satisfiable using a Conflict-Driven-Clause-Learning
/// (CDCL) algorithm. It is possible to specify a list of rules to start with in
/// [initialize] (unit resolution is not yet applied on these).
SatResult checkSatByCDCL(CNF3 cnf, [List<CDCLRule> initialize]) {
  final rules = initialize ?? [];
}

class CDCLRule {
  final int literal;
  final bool decide;

  CDCLRule.unitPropagate(this.literal) : decide = false;
  CDCLRule.decide(this.literal) : decide = true;
}
