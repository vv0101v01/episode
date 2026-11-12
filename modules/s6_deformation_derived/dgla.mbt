///|
/// 微分分次李代數 L = 𝔤 ⊗ Ω：𝔤 為有限維李代數（置於 0 次），
/// Ω 為 m 個 1 次生成元上的外代數並帶二次微分（如環面、冪零流形的 Chevalley–Eilenberg 代數）。
/// 基底 e_a ⊗ z_S 的座標為 a·2ᵐ + S（S 為生成元位元集，次數 = |S|）。
/// [a⊗α, b⊗β] = [a,b] ⊗ αβ，d(a⊗α) = a ⊗ dα。
pub(all) struct Dgla {
  name : String
  /// dim 𝔤
  g : Int32
  /// 結構常數：`lie[a][b]` 為 [e_a, e_b] 的座標向量
  lie : Array[Array[Array[Int32]]]
  /// Ω 的生成元數
  m : Int32
  /// 生成元的微分：`dgen[i]` 為 (二元位元集, 係數) 的清單
  dgen : Array[Array[(Int32, Int32)]]
}

///|
pub fn Dgla::dim(self : Dgla) -> Int32 {
  self.g * (1 << self.m)
}

///|
/// 外積 z_S ∧ z_T：回傳（位元集, 符號）；有重複生成元時符號為 0。
fn wedge(s : Int32, t : Int32) -> (Int32, Int32) {
  if (s & t) != 0 {
    return (0, 0)
  }
  // 逆序數：i ∈ S、j ∈ T 且 i > j 的對數
  let mut inversions = 0
  let mut tt = t
  while tt != 0 {
    let j = tt.ctz()
    tt = tt & (tt - 1)
    inversions += (s >> (j + 1)).popcnt()
  }
  (s | t, if inversions % 2 == 0 { 1 } else { -1 })
}

///|
/// Ω 中的乘法（係數向量長 2ᵐ）。
fn Dgla::omega_mul(
  self : Dgla,
  x : Array[Int32],
  y : Array[Int32],
) -> Array[Int32] {
  let n = 1 << self.m
  let out = Array::make(n, 0)
  for s in 0..<n {
    if x[s] == 0 {
      continue
    }
    for t in 0..<n {
      if y[t] == 0 {
        continue
      }
      let (u, sign) = wedge(s, t)
      if sign != 0 {
        out[u] = md(out[u] + sign * mul(x[s], y[t]))
      }
    }
  }
  out
}

///|
/// Ω 的微分作用於基底 z_S（Leibniz：d(z_{i₁}…z_{i_k}) = Σ_j (−1)ʲ z_{i₁}…dz_{i_j}…z_{i_k}）。
fn Dgla::omega_d_basis(self : Dgla, s : Int32) -> Array[Int32] {
  let n = 1 << self.m
  let out = Array::make(n, 0)
  let mut rest = s
  let mut position = 0
  while rest != 0 {
    let i = rest.ctz()
    rest = rest & (rest - 1)
    let prefix = s & ((1 << i) - 1)
    let suffix = s & ((1 << (i + 1)) - 1).lnot()
    for term in self.dgen[i] {
      let (mask, coef) = term
      let (u1, s1) = wedge(prefix, mask)
      if s1 == 0 {
        continue
      }
      let (u2, s2) = wedge(u1, suffix)
      if s2 == 0 {
        continue
      }
      let sign = (if position % 2 == 0 { 1 } else { -1 }) * s1 * s2
      out[u2] = md(out[u2] + sign * md(coef))
    }
    position += 1
  }
  out
}

///|
/// 微分 d : L → L（次數 +1）。
pub fn Dgla::d(self : Dgla, x : Array[Int32]) -> Array[Int32] {
  let n = 1 << self.m
  let out = Array::make(self.dim(), 0)
  for s in 0..<n {
    let ds = self.omega_d_basis(s)
    for a in 0..<self.g {
      let c = x[a * n + s]
      if c == 0 {
        continue
      }
      for u in 0..<n {
        if ds[u] != 0 {
          out[a * n + u] = md(out[a * n + u] + mul(c, ds[u]))
        }
      }
    }
  }
  out
}

///|
/// 分次李括號。
pub fn Dgla::bracket(
  self : Dgla,
  x : Array[Int32],
  y : Array[Int32],
) -> Array[Int32] {
  let n = 1 << self.m
  let out = Array::make(self.dim(), 0)
  for a in 0..<self.g {
    let xa : Array[Int32] = []
    for s in 0..<n {
      xa.push(x[a * n + s])
    }
    let mut xa_zero = true
    for v in xa {
      if v != 0 {
        xa_zero = false
      }
    }
    if xa_zero {
      continue
    }
    for b in 0..<self.g {
      let yb : Array[Int32] = []
      let mut yb_zero = true
      for s in 0..<n {
        yb.push(y[b * n + s])
        if y[b * n + s] != 0 {
          yb_zero = false
        }
      }
      if yb_zero {
        continue
      }
      let prod = self.omega_mul(xa, yb)
      for c in 0..<self.g {
        let k = self.lie[a][b][c]
        if k == 0 {
          continue
        }
        for u in 0..<n {
          if prod[u] != 0 {
            out[c * n + u] = md(out[c * n + u] + mul(k, prod[u]))
          }
        }
      }
    }
  }
  out
}

///|
pub fn vec_add(x : Array[Int32], y : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<x.length() {
    out.push(md(x[i] + y[i]))
  }
  out
}

///|
pub fn vec_scale(k : Int32, x : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for v in x {
    out.push(mul(k, v))
  }
  out
}

///|
pub fn vec_is_zero(x : Array[Int32]) -> Bool {
  for v in x {
    if md(v) != 0 {
      return false
    }
  }
  true
}

///|
/// k 次部分的座標清單。
pub fn Dgla::degree_indices(self : Dgla, k : Int32) -> Array[Int32] {
  let n = 1 << self.m
  let out : Array[Int32] = []
  for a in 0..<self.g {
    for s in 0..<n {
      if s.popcnt() == k {
        out.push(a * n + s)
      }
    }
  }
  out
}

///|
fn Dgla::basis_vector(self : Dgla, idx : Int32) -> Array[Int32] {
  let v = Array::make(self.dim(), 0)
  v[idx] = 1
  v
}

///|
/// 把 L 看作上鏈複形（次數 0..m）。`twist` 給定時用扭轉微分 d_x = d + [x, ·]。
pub fn Dgla::cochain(self : Dgla, twist : Array[Int32]?) -> Cochain {
  let dims : Array[Int32] = []
  let idx : Array[Array[Int32]] = []
  for k in 0..<(self.m + 1) {
    let ids = self.degree_indices(k)
    dims.push(ids.length())
    idx.push(ids)
  }
  let d : Array[Matrix] = []
  for k in 0..<self.m {
    let columns : Array[Array[Int32]] = []
    for i in idx[k] {
      let e = self.basis_vector(i)
      let mut img = self.d(e)
      match twist {
        Some(x) => img = vec_add(img, self.bracket(x, e))
        None => ()
      }
      let col : Array[Int32] = []
      for j in idx[k + 1] {
        col.push(img[j])
      }
      columns.push(col)
    }
    d.push(Matrix::from_columns(dims[k + 1], columns))
  }
  { dims, d, }
}

///|
/// 曲率 F(x) = dx + ½[x, x]（x ∈ L¹）。Maurer–Cartan 方程即 F(x) = 0（平坦）。
pub fn Dgla::curvature(self : Dgla, x : Array[Int32]) -> Array[Int32] {
  vec_add(self.d(x), vec_scale(inv(2), self.bracket(x, x)))
}

///|
pub fn Dgla::is_maurer_cartan(self : Dgla, x : Array[Int32]) -> Bool {
  vec_is_zero(self.curvature(x))
}

///|
/// 偽隨機的 k 次元素。
pub fn Dgla::random_element(
  self : Dgla,
  k : Int32,
  seed : Int32,
) -> Array[Int32] {
  let v = Array::make(self.dim(), 0)
  let mut state = seed
  for i in self.degree_indices(k) {
    state = lcg_step(state)
    v[i] = (state >> 8) % 7
  }
  v
}

///|
/// 公理與恆等式的檢驗報告。
pub(all) struct DglaAxioms {
  /// d² = 0
  d_squared_zero : Bool
  /// 分次反對稱 [x,y] = −(−1)^{|x||y|}[y,x]
  antisymmetry : Bool
  /// 分次 Jacobi
  jacobi : Bool
  /// d 為括號的導子（Leibniz）
  leibniz : Bool
  /// Bianchi 恆等式：dF + [x, F] = 0 對任意 x ∈ L¹
  bianchi : Bool
  /// 協變導數的平方即曲率：d_x² u = [F(x), u]
  twisted_square_is_curvature : Bool
  /// 無窮小規範變換 δx = dλ + [x, λ] 下 δF = [F, λ]
  gauge_covariance : Bool
  checks : Int32
}

///|
pub fn DglaAxioms::all(self : DglaAxioms) -> Bool {
  self.d_squared_zero &&
  self.antisymmetry &&
  self.jacobi &&
  self.leibniz &&
  self.bianchi &&
  self.twisted_square_is_curvature &&
  self.gauge_covariance
}

///|
pub fn Dgla::verify_axioms(self : Dgla) -> DglaAxioms {
  let n = self.dim()
  let size = 1 << self.m
  let deg = fn(i : Int32) -> Int32 { (i % size).popcnt() }
  let mut checks = 0
  let mut d2 = true
  let mut anti = true
  let mut jac = true
  let mut leib = true
  for i in 0..<n {
    let ei = self.basis_vector(i)
    checks += 1
    if !vec_is_zero(self.d(self.d(ei))) {
      d2 = false
    }
    for j in 0..<n {
      let ej = self.basis_vector(j)
      let bij = self.bracket(ei, ej)
      let bji = self.bracket(ej, ei)
      let sign = if deg(i) * deg(j) % 2 == 0 { 1 } else { -1 }
      checks += 2
      // [x,y] + (−1)^{|x||y|}[y,x] = 0
      if !vec_is_zero(vec_add(bij, vec_scale(sign, bji))) {
        anti = false
      }
      // d[x,y] = [dx,y] + (−1)^{|x|}[x,dy]
      let s2 = if deg(i) % 2 == 0 { 1 } else { -1 }
      let rhs = vec_add(
        self.bracket(self.d(ei), ej),
        vec_scale(s2, self.bracket(ei, self.d(ej))),
      )
      if !vec_is_zero(vec_add(self.d(bij), vec_scale(-1, rhs))) {
        leib = false
      }
    }
  }
  // Jacobi：[x,[y,z]] = [[x,y],z] + (−1)^{|x||y|}[y,[x,z]]，於偽隨機齊次元素上
  for trial in 0..<12 {
    let dx = trial % (self.m + 1)
    let dy = trial / 2 % (self.m + 1)
    let dz = trial / 3 % (self.m + 1)
    let x = self.random_element(dx, 100 + trial)
    let y = self.random_element(dy, 200 + trial)
    let z = self.random_element(dz, 300 + trial)
    let sign = if dx * dy % 2 == 0 { 1 } else { -1 }
    let lhs = self.bracket(x, self.bracket(y, z))
    let rhs = vec_add(
      self.bracket(self.bracket(x, y), z),
      vec_scale(sign, self.bracket(y, self.bracket(x, z))),
    )
    checks += 1
    if !vec_is_zero(vec_add(lhs, vec_scale(-1, rhs))) {
      jac = false
    }
  }
  let mut bianchi = true
  let mut twisted = true
  let mut gauge = true
  for trial in 0..<10 {
    let x = self.random_element(1, 17 + trial)
    let f = self.curvature(x)
    checks += 3
    if !vec_is_zero(vec_add(self.d(f), self.bracket(x, f))) {
      bianchi = false
    }
    let u = self.random_element(trial % 2, 91 + trial)
    let dxu = vec_add(self.d(u), self.bracket(x, u))
    let dxdxu = vec_add(self.d(dxu), self.bracket(x, dxu))
    if !vec_is_zero(vec_add(dxdxu, vec_scale(-1, self.bracket(f, u)))) {
      twisted = false
    }
    // δF = d(δx) + [x, δx]，應等於 [F, λ]
    let lambda = self.random_element(0, 55 + trial)
    let delta = vec_add(self.d(lambda), self.bracket(x, lambda))
    let delta_f = vec_add(self.d(delta), self.bracket(x, delta))
    if !vec_is_zero(vec_add(delta_f, vec_scale(-1, self.bracket(f, lambda)))) {
      gauge = false
    }
  }
  {
    d_squared_zero: d2,
    antisymmetry: anti,
    jacobi: jac,
    leibniz: leib,
    bianchi,
    twisted_square_is_curvature: twisted,
    gauge_covariance: gauge,
    checks,
  }
}

///|
/// sl₂ 的結構常數（基底 e, f, h）：[h,e] = 2e，[h,f] = −2f，[e,f] = h。
pub fn sl2() -> Array[Array[Array[Int32]]] {
  let z = fn() -> Array[Int32] { [0, 0, 0] }
  let lie : Array[Array[Array[Int32]]] = [
    [z(), z(), z()],
    [z(), z(), z()],
    [z(), z(), z()],
  ]
  lie[0][1] = [0, 0, 1]
  lie[1][0] = [0, 0, md(-1)]
  lie[2][0] = [2, 0, 0]
  lie[0][2] = [md(-2), 0, 0]
  lie[2][1] = [0, md(-2), 0]
  lie[1][2] = [0, 2, 0]
  lie
}

///|
pub fn abelian(n : Int32) -> Array[Array[Array[Int32]]] {
  let lie : Array[Array[Array[Int32]]] = []
  for _ in 0..<n {
    let row : Array[Array[Int32]] = []
    for _ in 0..<n {
      row.push(Array::make(n, 0))
    }
    lie.push(row)
  }
  lie
}

///|
/// 環面 T² 上以 𝔤 為係數的平坦聯絡問題：Ω = Λ[x, y]，d = 0。
/// Maurer–Cartan 元素 A = a·x + b·y 即交換對 [a, b] = 0。
pub fn torus_dgla(lie : Array[Array[Array[Int32]]]) -> Dgla {
  { name: "g ⊗ H*(T²)", g: lie.length(), lie, m: 2, dgen: [[], []], }
}

///|
/// Heisenberg 冪零流形：Ω = Λ[x, y, z]，dz = x∧y。
pub fn heisenberg_dgla(lie : Array[Array[Array[Int32]]]) -> Dgla {
  {
    name: "g ⊗ CE(heis₃)",
    g: lie.length(),
    lie,
    m: 3,
    dgen: [[], [], [(3, 1)]],
  }
}

///|
/// 線性同餘偽隨機步（本模組所有取樣共用）。
fn lcg_step(state : Int32) -> Int32 {
  (state * 1103515245 + 12345) & 0x7fffffff
}
