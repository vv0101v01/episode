///|
/// Module S6 — 形變函子與模塔；衍生纖維積。
///
/// 係數域 𝔽_p，p = 32003（奇質數，故 ½ 存在；兩個餘數之積 < 2³¹）。
pub const P : Int32 = 32003

///|
pub fn md(x : Int32) -> Int32 {
  let r = x % P
  if r < 0 {
    r + P
  } else {
    r
  }
}

///|
pub fn mul(a : Int32, b : Int32) -> Int32 {
  md(a) * md(b) % P
}

///|
pub fn inv(a : Int32) -> Int32 {
  // 費馬小定理：a^(p−2)
  let mut result = 1
  let mut base = md(a)
  let mut e = P - 2
  while e > 0 {
    if e % 2 == 1 {
      result = result * base % P
    }
    base = base * base % P
    e = e / 2
  }
  result
}

///|
/// 矩陣以列為主：`m[i][j]`，i < rows，j < cols。
pub(all) struct Matrix {
  rows : Int32
  cols : Int32
  data : Array[Array[Int32]]
}

///|
pub fn Matrix::zero(rows : Int32, cols : Int32) -> Matrix {
  let data : Array[Array[Int32]] = []
  for _ in 0..<rows {
    data.push(Array::make(cols, 0))
  }
  { rows, cols, data, }
}

///|
/// 由各基底向量的像（行向量）組成矩陣。
pub fn Matrix::from_columns(
  rows : Int32,
  columns : Array[Array[Int32]],
) -> Matrix {
  let m = Matrix::zero(rows, columns.length())
  for j in 0..<columns.length() {
    for i in 0..<rows {
      m.data[i][j] = md(columns[j][i])
    }
  }
  m
}

///|
pub fn Matrix::apply(self : Matrix, v : Array[Int32]) -> Array[Int32] {
  let out = Array::make(self.rows, 0)
  for i in 0..<self.rows {
    let mut acc = 0
    for j in 0..<self.cols {
      acc = (acc + mul(self.data[i][j], v[j])) % P
    }
    out[i] = acc
  }
  out
}

///|
pub fn Matrix::compose(self : Matrix, other : Matrix) -> Matrix {
  // self ∘ other
  let m = Matrix::zero(self.rows, other.cols)
  for i in 0..<self.rows {
    for k in 0..<self.cols {
      let a = self.data[i][k]
      if a != 0 {
        for j in 0..<other.cols {
          m.data[i][j] = (m.data[i][j] + mul(a, other.data[k][j])) % P
        }
      }
    }
  }
  m
}

///|
pub fn Matrix::is_zero(self : Matrix) -> Bool {
  for row in self.data {
    for x in row {
      if md(x) != 0 {
        return false
      }
    }
  }
  true
}

///|
/// 化為簡化列梯形；回傳（主元所在行的清單, 梯形矩陣）。
fn rref(m : Matrix) -> (Array[Int32], Array[Array[Int32]]) {
  let a : Array[Array[Int32]] = []
  for row in m.data {
    let r : Array[Int32] = []
    for x in row {
      r.push(md(x))
    }
    a.push(r)
  }
  let pivots : Array[Int32] = []
  let mut r = 0
  for c in 0..<m.cols {
    if r >= m.rows {
      break
    }
    let mut piv = -1
    for i in r..<m.rows {
      if a[i][c] != 0 {
        piv = i
        break
      }
    }
    if piv < 0 {
      continue
    }
    let tmp = a[r]
    a[r] = a[piv]
    a[piv] = tmp
    let s = inv(a[r][c])
    for j in 0..<m.cols {
      a[r][j] = mul(a[r][j], s)
    }
    for i in 0..<m.rows {
      if i != r && a[i][c] != 0 {
        let f = a[i][c]
        for j in 0..<m.cols {
          a[i][j] = md(a[i][j] - mul(f, a[r][j]))
        }
      }
    }
    pivots.push(c)
    r += 1
  }
  (pivots, a)
}

///|
pub fn Matrix::rank(self : Matrix) -> Int32 {
  let (pivots, _) = rref(self)
  pivots.length()
}

///|
/// 核的一組基底。
pub fn Matrix::kernel(self : Matrix) -> Array[Array[Int32]] {
  let (pivots, a) = rref(self)
  let is_pivot = Array::make(self.cols, -1)
  for k in 0..<pivots.length() {
    is_pivot[pivots[k]] = k
  }
  let basis : Array[Array[Int32]] = []
  for c in 0..<self.cols {
    if is_pivot[c] >= 0 {
      continue
    }
    let v = Array::make(self.cols, 0)
    v[c] = 1
    for k in 0..<pivots.length() {
      v[pivots[k]] = md(-a[k][c])
    }
    basis.push(v)
  }
  basis
}

///|
/// 解 M·x = b；無解回傳 None。
pub fn Matrix::solve(self : Matrix, b : Array[Int32]) -> Array[Int32]? {
  let aug = Matrix::zero(self.rows, self.cols + 1)
  for i in 0..<self.rows {
    for j in 0..<self.cols {
      aug.data[i][j] = self.data[i][j]
    }
    aug.data[i][self.cols] = b[i]
  }
  let (pivots, a) = rref(aug)
  let x = Array::make(self.cols, 0)
  for k in 0..<pivots.length() {
    if pivots[k] == self.cols {
      return None
    }
    x[pivots[k]] = a[k][self.cols]
  }
  Some(x)
}

///|
/// 一組向量張成的子空間維數。
pub fn span_rank(dim : Int32, vectors : Array[Array[Int32]]) -> Int32 {
  Matrix::from_columns(dim, vectors).rank()
}
