// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.cpl;

/// Invert [map].
Map<V, K> invertMap<K, V>(Map<K, V> map) => map.map((k, v) => MapEntry(v, k));

/// Compute number of entries in [multimap].
int mmLength<K, V>(Map<K, List<V>> multimap) =>
    multimap.entries.fold(0, (n, entry) => n + entry.value.length);

/// Check if [multimap] contains empty values.
bool mmContainsEmpty<K, V>(Map<K, List<V>> multimap) =>
    multimap.entries.any((entry) => entry.value.isEmpty);

/// Copy [multimap].
Map<K, List<V>> mmCopy<K, V>(Map<K, List<V>> multimap) =>
    multimap.map((k, v) => MapEntry(k, v.toList()));

/// Add ([key], [value]) to [multimap].
void mmAdd<K, V>(Map<K, List<V>> multimap, K key, V value) =>
    multimap.putIfAbsent(key, () => []).add(value);

/// Remove ([key], [value]) from [multimap]. Removes [key] if the list is empty.
void mmRemove<K, V>(Map<K, List<V>> multimap, K key, V value) {
  final l = multimap[key];
  if (l != null) {
    l.remove(value);
    if (l.isEmpty) {
      multimap.remove(key);
    }
  }
}

/// Map all keys in [map] using [keyMap].
Map<K2, V> mapKeys<K1, K2, V>(Map<K1, V> map, Map<K1, K2> keyMap) {
  final newMap = map.map((k, v) => MapEntry(keyMap[k], v));
  newMap.remove(null);
  return newMap;
}

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
