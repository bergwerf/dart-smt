// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

enum CplTokenType {
  /// `(`
  open,

  /// `)`
  close,

  /// A name
  name,

  /// `[0-9]+`
  number
}

enum CplTermType { name, number, tuple }

class CplToken {
  final CplTokenType type;
  final String name;
  final int number;
  final int ln, col;

  CplToken(this.type, this.ln, this.col, {this.name: '', this.number: 0});
}

class CplTerm {
  final CplTermType type;
  final String name;
  final int number;
  final List<CplTerm> subTerms;

  CplTerm.name(this.name)
      : type = CplTermType.name,
        number = 0,
        subTerms = [];

  CplTerm.number(this.number)
      : type = CplTermType.number,
        name = '',
        subTerms = [];

  CplTerm.tuple(this.subTerms)
      : type = CplTermType.tuple,
        name = '',
        number = 0;

  bool get isName => type == CplTermType.name;
  bool get isNumber => type == CplTermType.number;
  bool get isTuple => type == CplTermType.tuple;

  /// Get name of this or throw exception if it is not a name.
  String expectName() => type != CplTermType.name
      ? throw const CplException('expected a name')
      : name;

  @override
  String toString() =>
      isName ? name : isNumber ? '$number' : '(${subTerms.join(" ")})';
}

/// Process [tokens] into a list of AST terms.
List<CplTerm> parseCpl(List<CplToken> tokens) {
  final topLevel = <CplTerm>[];
  final queue = <CplTerm>[];

  CplTerm top() {
    if (queue.isEmpty) {
      throw const CplException('queue is empty');
    } else {
      return queue.last;
    }
  }

  for (final t in tokens) {
    switch (t.type) {
      case CplTokenType.name:
        top().subTerms.add(CplTerm.name(t.name));
        break;

      case CplTokenType.number:
        top().subTerms.add(CplTerm.number(t.number));
        break;

      case CplTokenType.open:
        queue.add(CplTerm.tuple([]));
        break;

      case CplTokenType.close:
        top();
        final tuple = queue.removeLast();
        if (tuple.subTerms.isEmpty) {
          throw const CplException('tuples may not be empty');
        }
        if (queue.isNotEmpty) {
          queue.last.subTerms.add(tuple);
        } else {
          topLevel.add(tuple);
        }
        break;
    }
  }

  return topLevel;
}

/// Turn [input] into a list of tokens. Already checks that all names are
/// non-empty.
List<CplToken> tokenizeCpl(String input) {
  final whitespaceRe = RegExp(r'[\t ]*');
  final commentRe = RegExp(r'%[^\n]*');
  final numberRe = RegExp(r'([0-9]+)[\s%()]');
  final nameRe = RegExp(r'[^()\s]+');
  final tokens = <CplToken>[];

  for (var i = 0, ln = 1, lnOffset = 0; i < input.length; i++) {
    // Skip any whitespace (not newlines since we count these).
    i = whitespaceRe.matchAsPrefix(input, i)?.end ?? i;
    if (i == input.length) {
      break;
    }
    // Inspect current character.
    final col = i - lnOffset;
    final c = input[i];
    switch (c) {
      case '\n':
        ln++;
        lnOffset = i;
        break;
      case '%':
        // This is a comment, skip to the end of the line.
        i = commentRe.matchAsPrefix(input, i).end - 1;
        break;
      case '(':
        // This is the start of a tuple.
        tokens.add(CplToken(CplTokenType.open, ln, col));
        break;
      case ')':
        // This is the end of a tuple.
        tokens.add(CplToken(CplTokenType.close, ln, col));
        break;
      default:
        // This could be a number.
        final m1 = numberRe.matchAsPrefix(input, i);
        if (m1 != null) {
          final number = int.parse(m1.group(1));
          tokens.add(CplToken(CplTokenType.number, ln, col, number: number));
          i = m1.end - 2; // Also subtract terminating character.
          break;
        }
        // There must be a name here.
        final m2 = nameRe.matchAsPrefix(input, i);
        final name = m2?.group(0) ?? '';
        if (name.isEmpty) {
          throw const CplException('found an empty name');
        }
        tokens.add(CplToken(CplTokenType.name, ln, col, name: name));
        i = m2.end - 1;
    }
  }
  return tokens;
}
