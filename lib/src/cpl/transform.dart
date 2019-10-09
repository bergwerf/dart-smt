// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

/// Rewrite any expression [x] to CDN Normal Form (CDNNF). That is, replace all
/// implications and bi-implications with only and, or, not.
Expr rewriteAnyToCdnnf(Expr x) {
  if (x.isImply) {
    // (P -> Q) <-> (~P \/ Q)
    return rewriteAnyToCdnnf(Expr.or([_neg(x.arguments[0]), x.arguments[1]]));
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
  final a = x.arguments.map(rewriteAnyToBonf).toList();
  // Nest n-ary operators.
  if (a.length > 2) {
    return a.sublist(2).fold(Expr(x.type, [a[0], a[1]]),
        (x, argument) => Expr(x.type, [x, argument]));
  }
  // Unwrap unary and/or/iff.
  if (a.length == 1 && (x.isAnd || x.isOr || x.isIff)) {
    return a[0];
  }
  // Else retain expression structure.
  return Expr(x.type, a, x.label, x.index);
}

/// Rewrite an expression [x] in CDNNF to Negation Normal Form (NNF). That is,
/// use De Morgan's laws to put negation only at the expression leaves. You can
/// also input an expression that is not in CDNNF to get a partial NNF (and
/// eliminate double negations).
Expr rewriteCdnnfToNnf(Expr x) {
  if (x.isNot) {
    // If the argument is a conjunction or disjunction, apply a transformation.
    // If the argument is a negation, then cancel the negation.
    final p = x.arguments[0];
    if (p.isAnd) {
      final distr = Expr.or(p.arguments.map(_neg).toList());
      return rewriteCdnnfToNnf(distr);
    } else if (p.isOr) {
      final distr = Expr.and(p.arguments.map(_neg).toList());
      return rewriteCdnnfToNnf(distr);
    } else if (p.isNot) {
      return rewriteCdnnfToNnf(p.arguments[0]);
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
              return Expr.or([clauseA, clauseB]);
            }).toList();
          }).toList();
        });
      }
      return [];

    default:
      throw ArgumentError('invalid input form');
  }
}

/// Transform an expression [x] in BONF to 3-CNF (CNF where each clause contains
/// at most 3 literals) using a Tseytin transformation. The size of the
/// resulting formula is linearly bounded and introduces a linearly bounded
/// number of new variables.
List<Expr> transformBonfTo3CnfWithTseytin(Expr x) {
  // Get transformation for the whole formula and add a unit clause for the
  // literal that describes the whole formula.
  final t = _tseytinTransform(x, _Seq());
  t.clauses.add(t.name);
  return t.clauses;
}

/// Compute Tseytin transformation for a sub-formula [x].
_Tseytin _tseytinTransform(Expr x, _Seq seq) {
  // If this sub-formula is a literal, then the name of this sub-formula is
  // equal to the literal and there are no extra clauses.
  if (isLiteral(x)) {
    return _Tseytin(x, []);
  }

  // Create variable to name this sub-formula and generate extra clauses.
  final nD = Expr.indexVar(++seq.i);
  final a = x.arguments.map((arg) => _tseytinTransform(arg, seq)).toList();
  final clauses = a.expand((t) => t.clauses).toList();
  switch (x.type) {
    case ExprType.not:
      // nD <-> ~q
      assert(a.length == 1);
      final q = a[0].name;
      // {nD q}, {~nD ~q}
      clauses.addAll([
        Expr.or([nD, q]),
        Expr.or([_neg(nD), _neg(q)])
      ]);
      break;

    case ExprType.and:
      // nD <-> (q /\ r)
      assert(a.length == 2);
      final q = a[0].name;
      final r = a[1].name;
      // {nD ~q ~r}, {~nD q}, {~nD r}
      clauses.addAll([
        Expr.or([nD, _neg(q), _neg(r)]),
        Expr.or([_neg(nD), q]),
        Expr.or([_neg(nD), r])
      ]);
      break;

    case ExprType.or:
      // nD <-> (q \/ r)
      assert(a.length == 2);
      final q = a[0].name;
      final r = a[1].name;
      // {~nD q r}, {nD ~q}, {nD ~r}
      clauses.addAll([
        Expr.or([_neg(nD), q, r]),
        Expr.or([nD, _neg(q)]),
        Expr.or([nD, _neg(r)])
      ]);
      break;

    case ExprType.imply:
      // nD <-> (q -> r)
      assert(a.length == 2);
      final q = a[0].name;
      final r = a[1].name;
      // {~nD ~q r}, {nD ~r}, {nD q}
      clauses.addAll([
        Expr.or([_neg(nD), _neg(q), r]),
        Expr.or([nD, _neg(r)]),
        Expr.or([nD, q])
      ]);
      break;

    case ExprType.iff:
      // nD <-> (q <-> r)
      assert(a.length == 2);
      final q = a[0].name;
      final r = a[1].name;
      // {nD q r}, {nD ~q ~r}, {~nD q ~r}, {~nD ~q r}
      clauses.addAll([
        Expr.or([nD, q, r]),
        Expr.or([nD, _neg(q), _neg(r)]),
        Expr.or([_neg(nD), q, _neg(r)]),
        Expr.or([_neg(nD), _neg(q), r])
      ]);
      break;

    default: // ExprType.variable
      throw StateError('this is a literal');
  }
  return _Tseytin(nD, clauses);
}

/// Shortcut to negate [x]. If [x] is a negation this will return its argument.
Expr _neg(Expr x) => x.isNot ? x.arguments[0] : Expr.not(x);

/// A sequence number reference that is used to get unique variable indices in
/// [_tseytinTransform].
class _Seq {
  var i = 0;
}

/// Result of a Tseytin transformation.
class _Tseytin {
  final Expr name;
  final List<Expr> clauses;
  _Tseytin(this.name, this.clauses);
}
