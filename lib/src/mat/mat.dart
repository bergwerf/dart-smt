// Copyright (c) 2019, Herman Bergwerf. All rights reserved.
// Use of this source code is governed by a MIT-style license
// that can be found in the LICENSE file.

part of smt.mat;

/// Vector of 64bit floating point values
class Vec with ListMixin<double> implements List<double> {
  final Float64List _v;
  final int _length;
  final int _stride;

  Vec._view(this._v, this._stride, this._length);

  /// Create vector of [length] containing zeros.
  factory Vec.zeros(int length) => Vec._view(Float64List(length), 1, length);

  @override
  int get length => _length;

  @override
  set length(int l) => throw UnsupportedError('Vec has a fixed length');

  @override
  double operator [](int i) => _v[i * _stride];

  @override
  void operator []=(int i, double v) => _v[i * _stride] = v;

  /// Copy [v].
  void copy(Vec v) {
    setAll(0, v);
  }

  /// Clone this vector.
  Vec clone() {
    final v = Vec.zeros(length);
    for (var i = 0; i < length; i++) {
      v[i] = this[i];
    }
    return v;
  }

  /// Add elements of [vec] to the elements of this vector.
  void addVec(Vec vec) {
    assert(vec.length == length);
    for (var i = 0; i < length; i++) {
      this[i] += vec[i];
    }
  }

  /// Multiply all elements by [n].
  void multiplyAll(double n) {
    for (var i = 0; i < length; i++) {
      this[i] *= n;
    }
  }
}

/// 2-dimensional matrix of 64bit floating point values in row-major order
class Mat2 {
  final Float64List _v;
  final int width;
  final int height;

  Mat2.zeros(this.width, this.height) : _v = Float64List(width * height);

  /// Get element at ([i], [j]).
  double at(int i, int j) => _v[i * width + j];

  /// Set element at ([i], [j]) to [v].
  void set(int i, int j, double v) => _v[i * width + j] = v;

  /// Get view of [i]-th row.
  Vec row(int i) {
    final offset = i * width * Float64List.bytesPerElement;
    return Vec._view(Float64List.view(_v.buffer, offset, width), 1, width);
  }

  /// Get view of [j]-th column.
  Vec col(int j) {
    if (height == 0) {
      return Vec.zeros(0);
    } else {
      final o = j * Float64List.bytesPerElement;
      final l = width * (height - 1) + 1;
      return Vec._view(Float64List.view(_v.buffer, o, l), width, height);
    }
  }

  /// Copy [mat].
  void copy(Mat2 mat) {
    assert(mat.height <= height);
    for (var i = 0; i < mat.height; i++) {
      row(i).copy(mat.row(i));
    }
  }

  @override
  String toString() {
    final buffer = StringBuffer();
    for (var i = 0; i < height; i++) {
      buffer.writeln(row(i).join('\t'));
    }
    return buffer.toString();
  }
}
