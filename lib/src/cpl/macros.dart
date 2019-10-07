// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

/// Macro format
typedef CplTerm CplMacro(List<CplTerm> arguments);

/// Standard macros
final standardMacros = <MapEntry<String, CplMacro>>[
  // Note that the order matters for the application.
  const MapEntry('if', insertBodyIfNonZero),
  const MapEntry('calc', computePostfixCalculation),
  MapEntry(r'/\*', (a) => repeatSingleIndex(r'/\', a)),
  MapEntry(r'\/*', (a) => repeatSingleIndex(r'\/', a)),
  MapEntry(r'/\**', (a) => repeatDoubleIndex(r'/\', a)),
  MapEntry(r'\/**', (a) => repeatDoubleIndex(r'\/', a)),
];

/// Insert argument body if the number in the first argument is non-zero.
CplTerm insertBodyIfNonZero(List<CplTerm> arguments) {
  cplAssert(() => arguments.length == 2 && arguments[0].isNumber);
  if (arguments[0].number == 0) {
    return CplTerm.tuple([CplTerm.name('empty')]);
  } else {
    return arguments[1];
  }
}

/// Compute the result of the given postfix computation.
CplTerm computePostfixCalculation(List<CplTerm> arguments) {
  cplAssert(() => arguments.every((a) => a.isNumber || a.isName));
  final stack = <int>[];
  for (final a in arguments) {
    if (a.isNumber) {
      stack.add(a.number);
    } else {
      // All operations are binary.
      if (stack.length < 2) {
        throw const CplException('calc stack too small');
      }
      final r = stack.removeLast();
      final l = stack.removeLast();
      switch (a.name) {
        case '+':
          stack.add(l + r);
          break;
        case '-':
          stack.add(l - r);
          break;
        case '*':
          stack.add(l * r);
          break;
        case '=':
          stack.add(l == r ? 1 : 0);
          break;
        case 'and':
          stack.add(l != 0 && r != 0 ? 1 : 0);
          break;
        case 'or':
          stack.add(l != 0 || r != 0 ? 1 : 0);
          break;
        default:
          throw new CplException('unrecognized operation ${a.name} in calc');
      }
    }
  }
  if (stack.length != 1) {
    throw const CplException('calc stack incorrect');
  }
  return CplTerm.number(stack[0]);
}

/// Repeat body for one index over a given range.
/// + [wrapperName] should contain the tuple name for the result.
/// + [arguments] should contain (indexName, from, to, body)
CplTerm repeatSingleIndex(String wrapperName, List<CplTerm> arguments) {
  cplAssert(() => arguments.length == 4);
  cplAssert(() => arguments[1].isNumber && arguments[2].isNumber);
  final indexName = extractName(arguments[0]);
  final from = arguments[1].number;
  final to = arguments[2].number;
  final body = arguments[3];

  // Generate all sub-terms by substituting the index.
  final subTerms = <CplTerm>[CplTerm.name(wrapperName)];
  for (var i = from; i <= to; i++) {
    subTerms.add(substituteName(indexName, CplTerm.number(i), body));
  }
  return CplTerm.tuple(subTerms);
}

/// Repeat body for two distinct indices over a given range where the first
/// index is always smaller than the second index.
/// + [wrapperName] should contain the tuple name for the result.
/// + [arguments] should contain (from, index1Name, index2Name, to, body)
CplTerm repeatDoubleIndex(String wrapperName, List<CplTerm> arguments) {
  cplAssert(() => arguments.length == 5);
  cplAssert(() => arguments[0].isNumber && arguments[3].isNumber);
  final from = arguments[0].number;
  final index1Name = extractName(arguments[1]);
  final index2Name = extractName(arguments[2]);
  final to = arguments[3].number;
  final body = arguments[4];

  // Generate all sub-terms by substituting both indices.
  final subTerms = <CplTerm>[CplTerm.name(wrapperName)];
  for (var i = from; i < to; i++) {
    for (var j = i + 1; j <= to; j++) {
      final body1 = substituteName(index1Name, CplTerm.number(i), body);
      final body2 = substituteName(index2Name, CplTerm.number(j), body1);
      subTerms.add(body2);
    }
  }
  return CplTerm.tuple(subTerms);
}
