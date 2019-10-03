// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

/// Zip two lists into a list of pairs.
List<Pair<A, B>> zip<A, B>(List<A> as, List<B> bs) {
  final zipped = <Pair<A, B>>[];
  for (var i = 0; i < as.length && i < bs.length; i++) {
    zipped.add(Pair(as[i], bs[i]));
  }
  return zipped;
}

/// Exception for CPL processing
class CplException implements Exception {
  final String message;
  const CplException(this.message);
}

/// Pair of two elements
class Pair<A, B> {
  final A a;
  final B b;
  Pair(this.a, this.b);
}
