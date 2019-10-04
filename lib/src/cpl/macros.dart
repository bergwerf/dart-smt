// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

/// Macro format
typedef CplTerm CplMacro(List<CplTerm> arguments);

/// Standard macros include:
/// + `(/\* index from to body)` or `(and* . . . .)`
/// + `(sub . .)`
const standardMacros = <MapEntry<String, CplMacro>>[
  // Note that to terminate, any arithmetic should be put at the very start.
  const MapEntry('sub', computeSubtraction),
  const MapEntry('and*', applyIndexedAnd),
  const MapEntry(r'/\*', applyIndexedAnd)
];

/// Apply conjunction over a range of indices.
CplTerm applyIndexedAnd(List<CplTerm> arguments) {
  cplAssert(() => arguments.length == 4);
  cplAssert(() => arguments.sublist(1, 3).every((a) => a.isNumber));
  final indexName = extractName(arguments[0]);
  final from = arguments[1].number;
  final to = arguments[2].number;
  final body = arguments[3];

  // Generate all items by substituting the index with a number.
  final subTerms = <CplTerm>[CplTerm(CplTermType.name, name: 'and')];
  for (var i = from; i <= to; i++) {
    final iTerm = CplTerm(CplTermType.number, number: i);
    subTerms.add(substituteName(indexName, iTerm, body));
  }
  return CplTerm(CplTermType.tuple, terms: subTerms);
}

/// Subtract two numbers.
CplTerm computeSubtraction(List<CplTerm> arguments) {
  cplAssert(() => arguments.length == 2 && arguments.every((a) => a.isNumber));
  final result = arguments[0].number - arguments[1].number;
  return CplTerm(CplTermType.number, number: result);
}
