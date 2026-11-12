///|
/// 組合範例 11 — Morita 等價。有限維結合代數以結構常數給出：
/// `mul[i][j]` = 基元 eᵢ·eⱼ 的座標向量（𝔽_p，p = S6 的 `P`）。
pub(all) struct Algebra {
  dim : Int32
  mul : Array[Array[Array[Int32]]]
}

///|
pub fn Algebra::product(
  self : Algebra,
  a : Array[Int32],
  b : Array[Int32],
) -> Array[Int32] {
  let mut out = Array::make(self.dim, 0)
  for i in 0..<self.dim {
    if a[i] == 0 {
      continue
    }
    for j in 0..<self.dim {
      if b[j] == 0 {
        continue
      }
      out = @s6.vec_add(out, @s6.vec_scale(@s6.mul(a[i], b[j]), self.mul[i][j]))
    }
  }
  out
}

///|
fn basis_vec(dim : Int32, i : Int32) -> Array[Int32] {
  let v = Array::make(dim, 0)
  v[i] = 1
  v
}

///|
/// 結合律於全部基元三元組上的檢驗。
pub fn Algebra::is_associative(self : Algebra) -> Bool {
  for i in 0..<self.dim {
    for j in 0..<self.dim {
      for k in 0..<self.dim {
        let l = self.product(self.mul[i][j], basis_vec(self.dim, k))
        let r = self.product(basis_vec(self.dim, i), self.mul[j][k])
        if !@s6.vec_is_zero(@s6.vec_add(l, @s6.vec_scale(@s6.P - 1, r))) {
          return false
        }
      }
    }
  }
  true
}

///|
/// 基元的交換子 [eᵢ, eⱼ]。
fn Algebra::commutator(self : Algebra, i : Int32, j : Int32) -> Array[Int32] {
  @s6.vec_add(self.mul[i][j], @s6.vec_scale(@s6.P - 1, self.mul[j][i]))
}

///|
/// 中心的維數：線性映射 z ↦ (z eⱼ − eⱼ z)ⱼ 的核。
pub fn Algebra::center_dim(self : Algebra) -> Int32 {
  let images : Array[Array[Int32]] = []
  for i in 0..<self.dim {
    let img : Array[Int32] = []
    for j in 0..<self.dim {
      for t in self.commutator(i, j) {
        img.push(t)
      }
    }
    images.push(img)
  }
  self.dim - @s6.span_rank(self.dim * self.dim, images)
}

///|
/// 交換子商 A/[A, A] 的維數（= HH₀，同為 Morita 不變量）。
pub fn Algebra::cocenter_dim(self : Algebra) -> Int32 {
  let comms : Array[Array[Int32]] = []
  for i in 0..<self.dim {
    for j in 0..<self.dim {
      comms.push(self.commutator(i, j))
    }
  }
  self.dim - @s6.span_rank(self.dim, comms)
}

///|
/// 矩陣代數 Mₙ(A) = A ⊗ Mₙ(k)：基元 e_a ⊗ E_{rs} 編號為 (a·n + r)·n + s。
pub fn Algebra::matrices(self : Algebra, n : Int32) -> Algebra {
  let dim = self.dim * n * n
  let mul : Array[Array[Array[Int32]]] = []
  for x in 0..<dim {
    let row : Array[Array[Int32]] = []
    let a = x / (n * n)
    let r = x / n % n
    let s = x % n
    for y in 0..<dim {
      let b = y / (n * n)
      let t = y / n % n
      let u = y % n
      let v = Array::make(dim, 0)
      if s == t {
        for c in 0..<self.dim {
          v[(c * n + r) * n + u] = self.mul[a][b][c]
        }
      }
      row.push(v)
    }
    mul.push(row)
  }
  { dim, mul, }
}

///|
/// 群代數 k[G]（乘法表來自 S4 的重寫系統）。
pub fn group_algebra(table : Array[Array[Int32]]) -> Algebra {
  let n = table.length()
  let mul : Array[Array[Array[Int32]]] = []
  for a in 0..<n {
    let row : Array[Array[Int32]] = []
    for b in 0..<n {
      row.push(basis_vec(n, table[a][b]))
    }
    mul.push(row)
  }
  { dim: n, mul, }
}

///|
/// 上三角 2×2 矩陣代數（基：E₁₁, E₁₂, E₂₂）。
pub fn upper_triangular() -> Algebra {
  let z = [0, 0, 0]
  {
    dim: 3,
    mul: [[[1, 0, 0], [0, 1, 0], z], [z, z, [0, 1, 0]], [z, z, [0, 0, 1]]],
  }
}

///|
/// 定理（Morita 不變性）：Z(Mₙ(A)) ≅ Z(A) 且 HH₀(Mₙ(A)) ≅ HH₀(A)。
/// 回傳（dim Z(A), dim Z(Mₙ(A)), dim HH₀(A), dim HH₀(Mₙ(A)), Mₙ(A) 結合, 兩不變量皆相等）。
pub fn verify_morita(
  a : Algebra,
  n : Int32,
) -> (Int32, Int32, Int32, Int32, Bool, Bool) {
  let m = a.matrices(n)
  let za = a.center_dim()
  let zm = m.center_dim()
  let ha = a.cocenter_dim()
  let hm = m.cocenter_dim()
  (za, zm, ha, hm, m.is_associative(), za == zm && ha == hm)
}
