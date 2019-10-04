// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

enum ExprType { variable, and, or, not, imply, iff }

class Expr {
  final ExprType type;
  final String label;
  final List<Expr> arguments;

  Expr(this.type, [this.arguments = const [], this.label = ''])
      : assert((type == ExprType.variable) == label.isNotEmpty),
        assert(type == ExprType.variable ? arguments.isEmpty : true),
        assert(type == ExprType.not ? arguments.length == 1 : true),
        assert(type == ExprType.imply ? arguments.length == 2 : true),
        assert(type == ExprType.iff ? arguments.length >= 2 : true);

  @override
  String toString() {
    switch (type) {
      case ExprType.variable:
        return label;
      case ExprType.and:
        return '(${arguments.join(" /\\ ")})';
      case ExprType.or:
        return '(${arguments.join(" \\/ ")})';
      case ExprType.not:
        return '(~ ${arguments[0]})';
      case ExprType.imply:
        return '(${arguments.join(" -> ")})';
      case ExprType.iff:
        return '(${arguments.join(" <-> ")})';
    }
    return '';
  }
}

/// Convert [term] to expression given it contains only tuples of the form:
/// + `(and .*)` or `(/\ .*)`
/// + `(or .*)` or `(\/ .*)`
/// + `(not .)` or `(~ .)`
/// + `(imply . .)` or `(-> . .)`
/// + `(iff .*)` or `(<-> .*)`
/// + `(_ .*)`
/// + `(? .)`
Expr convertCplTermToExpr(CplTerm term, Map<String, bool> assignment) {
  switch (term.type) {
    case CplTermType.name:
      // Check for macro references.
      if (term.name.startsWith('#')) {
        throw CplException('unknown macro reference ${term.name}');
      }
      return Expr(ExprType.variable, [], term.name);

    case CplTermType.number:
      // Convert number to string (some variables are composed of numbers, for
      // example `(_ a 1)` is converted to `a_1`).
      return Expr(ExprType.variable, [], '${term.number}');

    case CplTermType.tuple:
      // Generate all sub-terms.
      final subTerms = term.terms
          .sublist(1)
          .map((t) => convertCplTermToExpr(t, assignment))
          .toList();

      switch (extractName(term.terms[0])) {
        case 'and':
        case '/\\':
          return Expr(ExprType.and, subTerms);

        case 'or':
        case '\\/':
          return Expr(ExprType.or, subTerms);

        case 'not':
        case '~':
          cplAssert(() => subTerms.length == 1);
          return Expr(ExprType.not, subTerms);

        case 'imply':
        case '->':
          cplAssert(() => subTerms.length == 2);
          return Expr(ExprType.imply, subTerms);

        case 'iff':
        case '<->':
          cplAssert(() => subTerms.length >= 2);
          return Expr(ExprType.iff, subTerms);

        case '_':
          cplAssert(() => subTerms.isNotEmpty);
          cplAssert(() => subTerms.every((t) => t.type == ExprType.variable));
          final label = subTerms.map((t) => t.label).join('_');
          return Expr(ExprType.variable, [], label);

        case '?':
          cplAssert(() => subTerms.length == 1);
          cplAssert(() => subTerms[0].type == ExprType.variable);
          if (assignment != null && assignment.containsKey(subTerms[0].label)) {
            final isTrue = assignment[subTerms[0].label];
            return isTrue ? subTerms[0] : Expr(ExprType.not, subTerms);
          } else {
            throw CplException('no assignment for ${subTerms[0].label}');
          }
      }
      throw const CplException('unknown format');

    default: // null
      throw const CplException('null term');
  }
}

/// Convert bi-implication to two implications.
Expr unfoldIff(Expr left, Expr right) {
  return Expr(ExprType.and, [
    Expr(ExprType.imply, [left, right]),
    Expr(ExprType.imply, [right, left])
  ]);
}

/// Remove all implications from expression [x].
Expr unfoldImply(Expr x) {
  if (x.type == ExprType.imply) {
    // (P -> Q) <-> (~P \/ Q)
    return unfoldImply(Expr(ExprType.or, [
      Expr(ExprType.not, [x.arguments[0]]),
      x.arguments[1]
    ]));
  } else if (x.type == ExprType.iff) {
    // Convert to implications.
    final a = x.arguments;
    final implyOnly = a.sublist(2).fold(unfoldIff(a[0], a[1]), unfoldIff);
    return unfoldImply(implyOnly);
  }
  return Expr(x.type, x.arguments.map(unfoldImply).toList(), x.label);
}

/// Negate [expr].
Expr negateExpr(Expr expr) => Expr(ExprType.not, [expr]);

/// Rewrite [x] to negation normal form assuming there are only variables,
/// conjunctions, disjunctions, and negations.
Expr rewriteToNNF(Expr x) {
  assert(x.type.index <= ExprType.not.index);
  if (x.type == ExprType.not) {
    // If the argument is a conjunction or disjunction, apply a transformation.
    // If the argument is a negation, then cancel the negation.
    final arg = x.arguments[0];
    if (arg.type == ExprType.and) {
      final distr = Expr(ExprType.or, arg.arguments.map(negateExpr).toList());
      return rewriteToNNF(distr);
    } else if (arg.type == ExprType.or) {
      final distr = Expr(ExprType.and, arg.arguments.map(negateExpr).toList());
      return rewriteToNNF(distr);
    } else if (arg.type == ExprType.not) {
      return rewriteToNNF(arg.arguments[0]);
    }
  }
  // In the default case, convert all arguments.
  return Expr(x.type, x.arguments.map(rewriteToNNF).toList(), x.label);
}

/// Convert [expr] to a list of disjunctive clauses using the distributive law
/// assuming it is already in negation normal form (the disjunction of two
/// conjunctions is essentially the cartesian product between both sets of
/// literals). Note that the size of the resulting formula may be exponentially
/// larger.
List<Expr> convertExprToCNFByProducts(Expr expr) {
  switch (expr.type) {
    case ExprType.variable:
    case ExprType.not:
      return [expr];

    case ExprType.and:
      return expr.arguments.expand(convertExprToCNFByProducts).toList();

    case ExprType.or:
      final cnfs = expr.arguments.map(convertExprToCNFByProducts).toList();
      if (cnfs.isNotEmpty) {
        // (A1&A2)|(B1&B2) <-> (A1|B1)&(A1|B2)&(A2|B1)&(A2|B2)
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

/// Convert nested expressions of [type] to a flat list of arguments.
List<Expr> flattenExpr(ExprType type, Expr expr) => expr.type == type
    ? expr.arguments.expand((a) => flattenExpr(type, a)).toList()
    : [expr];
