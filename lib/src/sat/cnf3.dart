// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.sat;

/// An optimized 3-CNF for 3SAT problems.
class CNF3 {
  /// For any pair of literals, store which third literal is implied (if any).
  /// For any literal {p q r} with p < q < r, the map contains: (~p ~q) => r,
  /// (~p ~r) => q, (~q ~r) => p. With ordered pairs we get a 2x compression.
  final Map<OrderedLiteralPair, int> literals;

  CNF3(this.literals);
}

/// A pair of literals stored as signed integers where the sign means negation.
/// (we could use bitwise operations to store negation as even/odd, but I doubt
/// this will be faster in the Dart VM).
///
/// Since any pair that contains both p and -p refers to a clause that is
/// trivially true, no pair will have |p| = |q|. Therefore |p| < |q|.
class OrderedLiteralPair {
  final int p, q;

  factory OrderedLiteralPair(int p, int q) => p.abs() < q.abs()
      ? OrderedLiteralPair._(p, q)
      : OrderedLiteralPair._(q, p);

  OrderedLiteralPair._(this.p, this.q);

  /// Inspired by http://szudzik.com/ElegantPairing.pdf. This variant is not
  /// completely collision free (note that both may be negative).
  ///
  /// Collisions:
  /// - (p, q) collides with (p, -q) for all p, q
  ///   + Since (-q)^2 + p = q^2 + p
  ///
  /// Note that:
  /// - (p, q) collides with (p + 2q - 1, q - 1)
  ///   + Since (q - 1)^2 + (p + 2q - 1) = q^2 + p
  ///   + However |p + 2q - 1| < |q - 1| does not exist since |p| < |q|.
  /// - (p, q) collides with (p - 2q - 1, q + 1)
  ///   + Since (q + 1)^2 + (p - 2q - 1) = q^2 + p
  ///   + However |p - 2q - 1| < |q + 1| does not exist since |p| < |q|.
  @override
  int get hashCode => q * q + p;

  @override
  bool operator ==(x) => x is OrderedLiteralPair && x.p == p && x.q == q;
}
