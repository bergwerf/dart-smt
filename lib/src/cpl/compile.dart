// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

/// Compile a list of [terms] where all terms are macros except for the last one
/// which must be a formula (which is returned).
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

  // Add standard macros.
  macros.insertAll(0, standardMacros);

  // Apply macros in LIFO order (such that any macro can only use macros that
  // were defined before it). Note that this makes recursion impossible (thus
  // CPL is not Turing complete).
  final result = macros.reversed.fold(
      terms.last, (term, macro) => applyMacro(macro.key, macro.value, term));

  // Convert final term to expression.
  return convertCplTermToExpr(result, assignment);
}

/// Compile macro definition in [term] and return it.
MapEntry<String, CplMacro> compileMacro(CplTerm term) {
  final t = term.subTerms;
  cplAssert(() => term.isTuple);
  cplAssert(() => t[0].expectName() == 'macro');
  cplAssert(() => t.length == 3 || (t.length == 4 && t[2].isTuple));

  final body = t.last;
  final macroName = t[1].expectName();
  final hasArguments = t.length == 4;
  final argumentNames = hasArguments //
      ? t[2].subTerms.map((t) => t.expectName()).toList()
      : <String>[];

  CplTerm macro(List<CplTerm> arguments) {
    if (arguments.length != argumentNames.length) {
      throw CplException('expected ${argumentNames.length} arguments');
    } else {
      final z = zip(argumentNames, arguments);
      return z.fold(body, (term, p) => substituteName(p.fst, p.snd, term));
    }
  }

  return MapEntry(macroName, macro);
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
    // Apply macro to all sub-terms.
    final st = term.subTerms.map((t) => applyMacro(name, macro, t)).toList();

    // Compute macro for this tuple if it starts with the macro name.
    if (st[0].expectName() == name) {
      return macro(st.sublist(1));
    } else {
      return CplTerm.tuple(st);
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
          final str = parts.map((str) => str == name ? r : str).join('_');
          return CplTerm.name(str);
        }
        // In case the replacement term is a tuple..
        throw const CplException('can not substitute tuples in compound names');
      }
      // The name is not changed.
      return term;

    case CplTermType.tuple:
      // Process sub-terms.
      return CplTerm.tuple(term.subTerms
          .map((term) => substituteName(name, replace, term))
          .toList());

    default: // CplTermType.number
      return term;
  }
}

/// Assert a certain condition or throw.
void cplAssert(bool condition()) {
  if (!condition()) {
    throw const CplException('unexpected structure');
  }
}
