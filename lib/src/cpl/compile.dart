// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

typedef CplTerm CplMacro(List<CplTerm> arguments);

Expr compileCpl(String input, [Map<String, bool> assignment]) =>
    compileCplTerms(parseCpl(tokenizeCpl(input)), assignment);

Expr compileCplTerms(List<CplTerm> terms, Map<String, bool> assignment) {
  // We need at least one term.
  if (terms.isEmpty) {
    throw const CplException('should have at least one term');
  }

  // Process macros.
  final macros = terms.sublist(0, terms.length - 1).map(compileMacro).toList();
  final dup = macros.where((a) => macros.any((b) => a != b && a.key == b.key));

  // Check for duplicate macro definitions.
  if (dup.isNotEmpty) {
    throw CplException('macro ${dup.first.key} is already defined');
  }

  // Apply defined macros and then the standard macros.
  macros.insertAll(0, standardMacros);
  return convertCplTermToExpr(applyMacros(terms.last, macros), assignment);
}

/// Compile macro definition in [term] and return it.
MapEntry<String, CplMacro> compileMacro(CplTerm term) {
  cplAssert(() => [3, 4].contains(term.terms.length));
  cplAssert(() => extractName(term.terms[0]) == 'macro');
  cplAssert(() => term.terms.length == 3 || term.terms[2].isTuple);

  final macroName = extractName(term.terms[1]);
  final hasArgs = term.terms.length == 4;
  final argNames = hasArgs ? term.terms[2].terms.map(extractName).toList() : [];
  final body = term.terms[hasArgs ? 3 : 2];

  CplTerm macro(List<CplTerm> arguments) {
    if (arguments.length != argNames.length) {
      throw CplException('expected ${argNames.length} arguments');
    } else {
      final z = zip(argNames, arguments);
      return z.fold(body, (term, p) => substituteName(p.a, p.b, term));
    }
  }

  return MapEntry(macroName, macro);
}

/// Apply all [macros] to [term] such that no recursion is possible.
CplTerm applyMacros(CplTerm term, List<MapEntry<String, CplMacro>> macros) {
  // We apply macros in LIFO order.
  return macros.reversed
      .fold(term, (t, macro) => applyMacro(macro.key, macro.value, t));
}

/// Apply [macro] with [name] to [term] using recursion. If a term is found to
/// be an instance of this macro, then apply the macro function.
CplTerm applyMacro(String name, CplMacro macro, CplTerm term) {
  // Check for a nullary macro instance (prefixed by a hash).
  if (term.isName &&
      term.name.startsWith('#') &&
      term.name.substring(1) == name) {
    return macro([]);
  }
  // Check for a macro instance with arguments. The parser should throw on empty
  // tuples. Note that in general all tuples are expected to start with a name.
  if (term.isTuple) {
    if (extractName(term.terms[0]) == name) {
      return macro(term.terms.sublist(1));
    } else {
      // Apply macro to all sub-terms.
      return CplTerm(CplTermType.tuple,
          terms: term.terms.map((t) => applyMacro(name, macro, t)).toList());
    }
  }
  // The term remains unaltered.
  return term;
}

/// Replace all variables with [name] with [replace] in [term].
CplTerm substituteName(String name, CplTerm replace, CplTerm term) {
  switch (term.type) {
    case CplTermType.name:
      if (term.name == name) {
        return replace;
      }
      // Process compound names.
      final parts = term.name.split('_');
      if (parts.contains(name)) {
        if (replace.type != CplTermType.tuple) {
          final r = replace.isName ? replace.name : '${replace.number}';
          return CplTerm(CplTermType.name,
              name: parts.map((str) => str == name ? r : str).join('_'));
        }
        // In case the replacement term is a tuple..
        throw const CplException('can not substitute tuples in compound names');
      }
      // The name is not changed.
      return term;

    case CplTermType.tuple:
      // Process sub-terms.
      return CplTerm(CplTermType.tuple,
          terms: term.terms
              .map((term) => substituteName(name, replace, term))
              .toList());

    default: // CplTermType.number
      return term;
  }
}

/// Extract name of [term] or throw if it is not a name.
String extractName(CplTerm term) => term.type != CplTermType.name
    ? throw const CplException('expected a name')
    : term.name;

/// Assert a certain condition or throw.
void cplAssert(bool condition()) {
  if (!condition()) {
    throw const CplException('unexpected structure');
  }
}
