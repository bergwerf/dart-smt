// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

/// Constraint Problem Language (CPL)
library smt.cpl;

part 'src/cpl/utils.dart';
part 'src/cpl/expr.dart';
part 'src/cpl/parse.dart';
part 'src/cpl/macros.dart';
part 'src/cpl/compile.dart';
part 'src/cpl/transform.dart';
part 'src/cpl/arith.dart';

/// Utility to compile CPL code in [input] given some [assignments], and
/// transform it to a CNF using either products or a Tseytin transformation.
List<Expr> compileCplToCnf(String input,
    {Map<String, bool> assignments, bool tseytin: false}) {
  // Parse CPL and compile it to an expression.
  final terms = parseCpl(tokenizeCpl(input));
  final expr = compileCplTerms(terms, assignments);

  // Transform to CNF clauses.
  if (tseytin) {
    // We could rewrite using De Morgan's laws to get fewer clauses (by
    // eliminating some negation sub-formulas), but this advantage is probably
    // minimal and it isn't clear this creates a CNF that is easier to solve.
    final bonf = rewriteAnyToBonf(removeDoubleNegations(expr));
    return transformBonfTo3CnfWithTseytin(bonf);
  } else {
    final nnf = rewriteCdnnfToNnf(rewriteAnyToCdnnf(expr));
    return transformNnfToCnfWithProducts(nnf);
  }
}
