///|
/// 上鏈複形 C⁰ → C¹ → … ；`d[k] : Cᵏ → Cᵏ⁺¹`。
pub(all) struct Cochain {
  dims : Array[Int32]
  d : Array[Matrix]
}

///|
pub fn Cochain::is_complex(self : Cochain) -> Bool {
  for k in 0..<(self.d.length() - 1) {
    if !self.d[k + 1].compose(self.d[k]).is_zero() {
      return false
    }
  }
  true
}

///|
/// 上同調維數 hᵏ = dim ker dᵏ − rank dᵏ⁻¹。
pub fn Cochain::betti(self : Cochain) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<self.dims.length() {
    let ker = if k < self.d.length() {
      self.dims[k] - self.d[k].rank()
    } else {
      self.dims[k]
    }
    let img = if k > 0 { self.d[k - 1].rank() } else { 0 }
    out.push(ker - img)
  }
  out
}

///|
pub fn Cochain::euler(self : Cochain) -> Int32 {
  let mut chi = 0
  for k in 0..<self.dims.length() {
    chi += if k % 2 == 0 { self.dims[k] } else { -self.dims[k] }
  }
  chi
}

///|
/// 上鏈映射是否與微分交換。
pub fn is_chain_map(a : Cochain, c : Cochain, f : Array[Matrix]) -> Bool {
  for k in 0..<a.d.length() {
    let lhs = f[k + 1].compose(a.d[k])
    let rhs = c.d[k].compose(f[k])
    for i in 0..<lhs.rows {
      for j in 0..<lhs.cols {
        if md(lhs.data[i][j] - rhs.data[i][j]) != 0 {
          return false
        }
      }
    }
  }
  true
}

///|
/// 衍生（同倫）纖維積 A ×ʰ_C B：Pⁿ = Aⁿ ⊕ Bⁿ ⊕ Cⁿ⁻¹，
/// d(a, b, c) = (da, db, f a − g b − dc)。三個複形須同長。
pub fn derived_fiber_product(
  a : Cochain,
  b : Cochain,
  c : Cochain,
  f : Array[Matrix],
  g : Array[Matrix],
) -> Cochain {
  let n = a.dims.length()
  let dims : Array[Int32] = []
  for k in 0..<n {
    dims.push(a.dims[k] + b.dims[k] + (if k > 0 { c.dims[k - 1] } else { 0 }))
  }
  let d : Array[Matrix] = []
  for k in 0..<(n - 1) {
    let m = Matrix::zero(dims[k + 1], dims[k])
    let ao = 0
    let bo = a.dims[k]
    let co = a.dims[k] + b.dims[k]
    let ao2 = 0
    let bo2 = a.dims[k + 1]
    let co2 = a.dims[k + 1] + b.dims[k + 1]
    // da
    for i in 0..<a.dims[k + 1] {
      for j in 0..<a.dims[k] {
        m.data[ao2 + i][ao + j] = a.d[k].data[i][j]
      }
    }
    // db
    for i in 0..<b.dims[k + 1] {
      for j in 0..<b.dims[k] {
        m.data[bo2 + i][bo + j] = b.d[k].data[i][j]
      }
    }
    // f a − g b（落在 Cᵏ）
    for i in 0..<c.dims[k] {
      for j in 0..<a.dims[k] {
        m.data[co2 + i][ao + j] = f[k].data[i][j]
      }
      for j in 0..<b.dims[k] {
        m.data[co2 + i][bo + j] = md(-g[k].data[i][j])
      }
    }
    // −dc : Cᵏ⁻¹ → Cᵏ
    if k > 0 {
      for i in 0..<c.dims[k] {
        for j in 0..<c.dims[k - 1] {
          m.data[co2 + i][co + j] = md(-c.d[k - 1].data[i][j])
        }
      }
    }
    d.push(m)
  }
  { dims, d, }
}

///|
/// 嚴格纖維積：逐次取 ker(f − g : Aⁿ ⊕ Bⁿ → Cⁿ) 的維數，以及其上同調維數。
pub fn strict_fiber_product_betti(
  a : Cochain,
  b : Cochain,
  c : Cochain,
  f : Array[Matrix],
  g : Array[Matrix],
) -> Array[Int32] {
  let n = a.dims.length()
  // 每次的核基底（在 A ⊕ B 座標下）
  let bases : Array[Array[Array[Int32]]] = []
  for k in 0..<n {
    let m = Matrix::zero(c.dims[k], a.dims[k] + b.dims[k])
    for i in 0..<c.dims[k] {
      for j in 0..<a.dims[k] {
        m.data[i][j] = f[k].data[i][j]
      }
      for j in 0..<b.dims[k] {
        m.data[i][a.dims[k] + j] = md(-g[k].data[i][j])
      }
    }
    bases.push(m.kernel())
  }
  // 限制後的微分之秩：把基底向量經 (dA ⊕ dB) 送出後所張空間的維數
  let ranks : Array[Int32] = []
  for k in 0..<(n - 1) {
    let images : Array[Array[Int32]] = []
    for v in bases[k] {
      let va : Array[Int32] = []
      let vb : Array[Int32] = []
      for j in 0..<a.dims[k] {
        va.push(v[j])
      }
      for j in 0..<b.dims[k] {
        vb.push(v[a.dims[k] + j])
      }
      let ia = a.d[k].apply(va)
      let ib = b.d[k].apply(vb)
      let img : Array[Int32] = []
      for x in ia {
        img.push(x)
      }
      for x in ib {
        img.push(x)
      }
      images.push(img)
    }
    ranks.push(span_rank(a.dims[k + 1] + b.dims[k + 1], images))
  }
  let out : Array[Int32] = []
  for k in 0..<n {
    let ker = bases[k].length() - (if k < n - 1 { ranks[k] } else { 0 })
    let img = if k > 0 { ranks[k - 1] } else { 0 }
    out.push(ker - img)
  }
  out
}

///|
/// 上同調上誘導映射 φⁿ = f_* − g_* : Hⁿ(A) ⊕ Hⁿ(B) → Hⁿ(C) 的秩。
fn induced_rank(
  a : Cochain,
  b : Cochain,
  c : Cochain,
  f : Array[Matrix],
  g : Array[Matrix],
  k : Int32,
) -> Int32 {
  let za = if k < a.d.length() {
    a.d[k].kernel()
  } else {
    Matrix::zero(0, a.dims[k]).kernel()
  }
  let zb = if k < b.d.length() {
    b.d[k].kernel()
  } else {
    Matrix::zero(0, b.dims[k]).kernel()
  }
  let vectors : Array[Array[Int32]] = []
  let mut boundary = 0
  if k > 0 {
    for j in 0..<c.dims[k - 1] {
      let e = Array::make(c.dims[k - 1], 0)
      e[j] = 1
      vectors.push(c.d[k - 1].apply(e))
    }
    boundary = c.d[k - 1].rank()
  }
  for z in za {
    vectors.push(f[k].apply(z))
  }
  for z in zb {
    let img = g[k].apply(z)
    let neg : Array[Int32] = []
    for x in img {
      neg.push(md(-x))
    }
    vectors.push(neg)
  }
  span_rank(c.dims[k], vectors) - boundary
}

///|
/// Mayer–Vietoris 長正合序列（組合範例 13）的維數等式：
/// hⁿ(P) = dim coker φⁿ⁻¹ + dim ker φⁿ。回傳（P 的上同調維數, 由序列預測的維數, 一致）。
pub fn verify_mayer_vietoris(
  a : Cochain,
  b : Cochain,
  c : Cochain,
  f : Array[Matrix],
  g : Array[Matrix],
) -> (Array[Int32], Array[Int32], Bool) {
  let p = derived_fiber_product(a, b, c, f, g)
  let hp = p.betti()
  let ha = a.betti()
  let hb = b.betti()
  let hc = c.betti()
  let predicted : Array[Int32] = []
  let mut ok = p.is_complex()
  for k in 0..<a.dims.length() {
    let ker = ha[k] + hb[k] - induced_rank(a, b, c, f, g, k)
    let coker = if k > 0 {
      hc[k - 1] - induced_rank(a, b, c, f, g, k - 1)
    } else {
      0
    }
    predicted.push(ker + coker)
    if predicted[k] != hp[k] {
      ok = false
    }
  }
  (hp, predicted, ok)
}
