// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// Check if the 3-CNF [cnf] is satisfiable using a
/// Conflict-Driven-Clause-Learning (CDCL) algorithm.
SatResult checkSatByCDCL(CNF3 cnf, [List<CDCLStep> ray = const []]) {
  //
}

class CDCLStep {
  final int literal;
  final bool decide;
  CDCLStep(this.literal, this.decide);
}
