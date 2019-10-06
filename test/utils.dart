// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

library smt.test.utils;

import 'dart:io';
import 'package:smt/cpl.dart';
import 'package:smt/sat.dart';

/// Read libraries and append with line endings.
String readLibs(List<String> libraries) =>
    libraries.map((path) => File('test/$path').readAsStringSync()).join('\n');

/// Compile [input] to [CNF].
CNF compileCNF(String input,
    {List<String> libs: const [],
    Map<String, bool> assign,
    bool tseytin: true}) {
  final str = '${readLibs(libs)}\n$input';
  final clauses = compileCplToCnf(str, assignments: assign, tseytin: tseytin);
  return convertClausesToCNF(clauses);
}

/// Compile [input] to [CDCLInput].
CDCLInput compileCDCLInput(String input,
    {List<String> libs: const [], Map<String, bool> assign}) {
  final str = '${readLibs(libs)}\n$input';
  final clauses = compileCplToCnf(str, assignments: assign, tseytin: true);
  return convertClausesToCDCLInput(clauses);
}

/// Construct assignment for [n]-bit binary [numbers].
Map<String, bool> intToBits(int n, Map<String, int> numbers,
    {bool negate: false, bool tseytin: false}) {
  final assignment = <String, bool>{};
  for (final entry in numbers.entries) {
    final variable = entry.key;
    final value = entry.value;
    for (var i = 0; i < n; i++) {
      assignment['${variable}_${n - i}'] = ((value >> i) & 1) == 1;
    }
  }
  return assignment;
}

/// Construct number from [n] bits in [solution] for [variable].
int bitsToInt(Map<String, bool> solution, int n, String variable) {
  var value = 0;
  for (var i = 0; i < n; i++) {
    value ^= (solution['${variable}_${n - i}'] ? 1 : 0) << i;
  }
  return value;
}
