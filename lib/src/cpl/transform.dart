// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

/// Rewrite any expression [x] to CDN Normal Form (CDNNF). That is, replace all
/// implications and bi-implications with only and, or, not.
Expr rewriteAnyToCdnnf(Expr x) {
  if (x.isImply) {
    // (P -> Q) <-> (~P \/ Q)
    return rewriteAnyToCdnnf(Expr(ExprType.or, [
      Expr(ExprType.not, [x.arguments[0]]),
      x.arguments[1]
    ]));
  } else if (x.isIff) {
    // Convert to implications.
    final a = x.arguments;
    final implyOnly = a.sublist(2).fold(unfoldIff(a[0], a[1]), unfoldIff);
    return rewriteAnyToCdnnf(implyOnly);
  }
  return Expr(x.type, x.arguments.map(rewriteAnyToCdnnf).toList(), x.label);
}

/// Rewrite any expression [x] to Binary Operator Normal Form (BONF). That is,
/// replace all n-ary operators (and, or, iff), with nested binary operators.
Expr rewriteAnyToBonf(Expr x) {
  //
}

/// Rewrite an expression [x] in CDNNF to Negation Normal Form (NNF). That is,
/// use De Morgan's laws to put negation only at the expression leaves.
Expr rewriteCdnnfToNnf(Expr x) {
  assert(x.type.index <= ExprType.not.index);
  if (x.isNot) {
    // If the argument is a conjunction or disjunction, apply a transformation.
    // If the argument is a negation, then cancel the negation.
    final arg = x.arguments[0];
    if (arg.isAnd) {
      final distr = Expr(ExprType.or, arg.arguments.map(negateExpr).toList());
      return rewriteCdnnfToNnf(distr);
    } else if (arg.isOr) {
      final distr = Expr(ExprType.and, arg.arguments.map(negateExpr).toList());
      return rewriteCdnnfToNnf(distr);
    } else if (arg.isNot) {
      return rewriteCdnnfToNnf(arg.arguments[0]);
    }
  }
  // In the default case, convert all arguments.
  return Expr(x.type, x.arguments.map(rewriteCdnnfToNnf).toList(), x.label);
}

/// Transform an expression [x] in NNF to Conjunctive Normal Form (CNF) using
/// the distributive law. The size of the resulting formula may be exponentially
/// larger. The result is represented as a list of clause expressions.
///
/// Note that the disjunction of two conjunctions is essentially the Cartesian
/// product between both sets of literals.
List<Expr> transformNnfToCnfWithProducts(Expr x) {
  switch (x.type) {
    case ExprType.variable:
      return [x];

    case ExprType.not:
      assert(x.arguments.single.isVariable);
      return [x];

    case ExprType.and:
      return x.arguments.expand(transformNnfToCnfWithProducts).toList();

    case ExprType.or:
      // Get CNF for each term.
      final cnfs = x.arguments.map(transformNnfToCnfWithProducts).toList();
      if (cnfs.isNotEmpty) {
        // Compute cartesian product between clauses of each term.
        // + (A1&A2) | (B1&B2) <-> (A1|B1) & (A1|B2) & (A2|B1) & (A2|B2)
        return cnfs.reduce((cnfA, cnfB) {
          return cnfA.expand((clauseA) {
            return cnfB.map((clauseB) {
              return Expr(ExprType.or, [clauseA, clauseB]);
            }).toList();
          }).toList();
        });
      }
      return [];

    default:
      throw new ArgumentError('invalid input form');
  }
}

/// Transform an expression [x] in BONF to 3-CNF (CNF where each clause contains
/// at most 3 literals) using a Tseytin transformation. The size of the
/// resulting formula is linearly bounded and introduces a linearly bounded
/// number of new variables.
List<Expr> transformBonfTo3CnfWithTseytin(Expr x) {
  //
}
