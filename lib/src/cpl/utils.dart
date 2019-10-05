// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

/// Invert [map].
Map<V, K> invertMap<K, V>(Map<K, V> map) => map.map((k, v) => MapEntry(v, k));

/// Zip two lists into a list of pairs.
List<Pair<A, B>> zip<A, B>(List<A> as, List<B> bs) {
  final zipped = <Pair<A, B>>[];
  for (var i = 0; i < as.length && i < bs.length; i++) {
    zipped.add(Pair(as[i], bs[i]));
  }
  return zipped;
}

/// Convert iterable to list of unique elements (more efficient than using a
/// hash-table for really small lists such as when generating a 3-CNF).
List<T> toUniqueList<T>(Iterable<T> iterable) {
  final output = <T>[];
  for (final element in iterable) {
    if (!output.contains(element)) {
      output.add(element);
    }
  }
  return output;
}

/// Compose a list of [transformers].
T Function(T) compose<T>(List<T Function(T)> transformers) =>
    (x) => transformers.fold(x, (x, t) => t(x));

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
