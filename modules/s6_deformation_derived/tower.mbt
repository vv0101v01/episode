///|
/// 模塔的一層：在 k[t]/(tⁿ⁺¹) 上的提升結果。
pub(all) struct Level {
  order : Int32
  /// 阻礙上閉鏈 Oₙ = ½ Σ_{i+j=n} [xᵢ, xⱼ] 是否閉（定理：恆閉）
  obstruction_closed : Bool
  /// 阻礙類 [Oₙ] ∈ H² 是否為零（⇔ 可提升）
  obstruction_exact : Bool
  /// 精細阻礙：允許把上一層的提升改動一個上閉鏈後是否可提升
  refined_liftable : Bool
  /// 提升的自由度（dim Z¹，提升構成其上的仿射空間）
  torsor_dim : Int32
}

///|
pub(all) struct Tower {
  /// 已構造的係數 x₁ … xₙ（x(t) = Σ xₖ tᵏ）
  coeffs : Array[Array[Int32]]
  levels : Array[Level]
  /// 首個受阻的階（0 表示在指定深度內無阻礙）
  obstructed_at : Int32
  /// 每一階截斷是否滿足 Maurer–Cartan 方程（模 tⁿ⁺¹）
  truncations_mc : Bool
}

///|
/// 截斷冪級數 x(t) = Σ_{k=1..n} xₖ tᵏ 的 Maurer–Cartan 方程在 tᵏ 項的係數（k ≤ n）。
fn mc_coefficient(
  l : Dgla,
  xs : Array[Array[Int32]],
  k : Int32,
) -> Array[Int32] {
  // d x_k + ½ Σ_{i+j=k} [x_i, x_j]
  let mut acc = if k <= xs.length() {
    l.d(xs[k - 1])
  } else {
    Array::make(l.dim(), 0)
  }
  let half = inv(2)
  for i in 1..<k {
    let j = k - i
    if i <= xs.length() && j <= xs.length() {
      acc = vec_add(acc, vec_scale(half, l.bracket(xs[i - 1], xs[j - 1])))
    }
  }
  acc
}

///|
fn restrict(v : Array[Int32], idx : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in idx {
    out.push(v[i])
  }
  out
}

///|
fn embed_coords(
  l : Dgla,
  coords : Array[Int32],
  idx : Array[Int32],
) -> Array[Int32] {
  let v = Array::make(l.dim(), 0)
  for k in 0..<idx.length() {
    v[idx[k]] = coords[k]
  }
  v
}

///|
/// 形變函子的模塔：自一階形變 x₁（須為上閉鏈）起，逐階於
/// Def(k[t]/t²) ← Def(k[t]/t³) ← … 提升，至 `depth` 階或受阻。
pub fn Dgla::moduli_tower(
  self : Dgla,
  x1 : Array[Int32],
  depth : Int32,
) -> Tower {
  let c = self.cochain(None)
  let idx1 = self.degree_indices(1)
  let idx2 = self.degree_indices(2)
  let d1 = c.d[1]
  let z1 = d1.kernel()
  let xs : Array[Array[Int32]] = [x1]
  let levels : Array[Level] = []
  let mut obstructed_at = 0
  let mut mc = vec_is_zero(self.d(x1))
  for n in 2..<(depth + 1) {
    // Oₙ = ½ Σ_{i+j=n} [xᵢ, xⱼ]（僅涉及已知的 x₁…xₙ₋₁）
    let o = mc_coefficient(self, xs, n)
    let closed = vec_is_zero(self.d(o))
    let neg : Array[Int32] = []
    for v in restrict(o, idx2) {
      neg.push(md(-v))
    }
    let sol = d1.solve(neg)
    // 精細阻礙：Oₙ ∈ im d + [x₁, Z¹]（改動 xₙ₋₁ ↦ xₙ₋₁ + z）
    let columns : Array[Array[Int32]] = []
    for j in 0..<d1.cols {
      let col : Array[Int32] = []
      for i in 0..<d1.rows {
        col.push(d1.data[i][j])
      }
      columns.push(col)
    }
    for z in z1 {
      columns.push(
        restrict(self.bracket(x1, embed_coords(self, z, idx1)), idx2),
      )
    }
    // n = 2 時尚無可改動的上一層提升，精細阻礙即阻礙本身
    let refined = if n == 2 {
      sol is Some(_)
    } else {
      Matrix::from_columns(idx2.length(), columns).solve(neg) is Some(_)
    }
    levels.push({
      order: n,
      obstruction_closed: closed,
      obstruction_exact: sol is Some(_),
      refined_liftable: refined,
      torsor_dim: z1.length(),
    })
    match sol {
      Some(coords) => {
        xs.push(embed_coords(self, coords, idx1))
        // 檢驗截斷的 Maurer–Cartan 方程
        for k in 1..<(n + 1) {
          if !vec_is_zero(mc_coefficient(self, xs, k)) {
            mc = false
          }
        }
      }
      None => {
        obstructed_at = n
        break
      }
    }
  }
  { coeffs: xs, levels, obstructed_at, truncations_mc: mc, }
}

///|
/// 形變問題的整體報告。
pub(all) struct DeformationReport {
  /// 切空間 H¹、阻礙空間 H²、無窮小自同構 H⁰
  h0 : Int32
  h1 : Int32
  h2 : Int32
  /// Kuranishi 二次映射 x ↦ ½[x,x] : H¹ → H² 在偽隨機切向量上非零的比例（分子, 分母）
  kuranishi_nonzero : Int32
  kuranishi_trials : Int32
  axioms : Bool
}

///|
pub fn Dgla::deformation_report(
  self : Dgla,
  trials : Int32,
) -> DeformationReport {
  let c = self.cochain(None)
  let h = c.betti()
  let idx1 = self.degree_indices(1)
  let idx2 = self.degree_indices(2)
  let z1 = c.d[1].kernel()
  let mut nonzero = 0
  let mut state = 12345
  for _ in 0..<trials {
    // 偽隨機上閉鏈
    let coords = Array::make(idx1.length(), 0)
    for z in z1 {
      state = lcg_step(state)
      let k = (state >> 8) % 5
      for i in 0..<coords.length() {
        coords[i] = md(coords[i] + k * z[i])
      }
    }
    let x = embed_coords(self, coords, idx1)
    let q = vec_scale(inv(2), self.bracket(x, x))
    // 類是否非零：q ∉ im d
    let neg = restrict(q, idx2)
    if c.d[1].solve(neg) is None {
      nonzero += 1
    }
  }
  {
    h0: h[0],
    h1: h[1],
    h2: h[2],
    kuranishi_nonzero: nonzero,
    kuranishi_trials: trials,
    axioms: self.verify_axioms().all(),
  }
}

///|
/// 定理（切複形 = 衍生纖維積）：交換簇 {(a,b) : [a,b] = 0} = 𝔤² ×_𝔤 {0} 在點 (a,b) 的
/// 衍生切複形 T = (𝔤² → 𝔤)，與環面 DGLA 在 Maurer–Cartan 元素 x = a·x + b·y 處的扭轉複形
/// (L, d_x) 在 ≥1 次的截斷一致：h¹(T) = dim Z¹(L, d_x)（未除以規範作用），h²(T) = H²(L, d_x)。
/// 回傳（扭轉複形的 (dim Z¹, h²), 衍生纖維積的 (h¹, h²), 一致）。
pub fn verify_tangent_fiber_product(
  lie : Array[Array[Array[Int32]]],
  a : Array[Int32],
  b : Array[Int32],
) -> ((Int32, Int32), (Int32, Int32), Bool) {
  let l = torus_dgla(lie)
  let g = lie.length()
  // x = a ⊗ z₀ + b ⊗ z₁
  let x = Array::make(l.dim(), 0)
  for i in 0..<g {
    x[i * 4 + 1] = md(a[i])
    x[i * 4 + 2] = md(b[i])
  }
  let tc = l.cochain(Some(x))
  let h = tc.betti()
  let twisted = [0, tc.dims[1] - tc.d[1].rank(), h[2]]
  // 衍生纖維積：A = 𝔤²（置於 1 次）、B = 0、C = 𝔤（置於 1 次），f = dμ_(a,b)(u, v) = [u, b] + [a, v]
  let ad = fn(u : Array[Int32], v : Array[Int32]) -> Array[Int32] {
    let out = Array::make(g, 0)
    for i in 0..<g {
      for j in 0..<g {
        for k in 0..<g {
          out[k] = md(out[k] + mul(mul(u[i], v[j]), lie[i][j][k]))
        }
      }
    }
    out
  }
  let columns : Array[Array[Int32]] = []
  for i in 0..<g {
    let e = Array::make(g, 0)
    e[i] = 1
    columns.push(ad(e, b))
  }
  for i in 0..<g {
    let e = Array::make(g, 0)
    e[i] = 1
    columns.push(ad(a, e))
  }
  let f1 = Matrix::from_columns(g, columns)
  let ca : Cochain = {
    dims: [0, 2 * g, 0],
    d: [Matrix::zero(2 * g, 0), Matrix::zero(0, 2 * g)],
  }
  let cb : Cochain = {
    dims: [0, 0, 0],
    d: [Matrix::zero(0, 0), Matrix::zero(0, 0)],
  }
  let cc : Cochain = {
    dims: [0, g, 0],
    d: [Matrix::zero(g, 0), Matrix::zero(0, g)],
  }
  let f = [Matrix::zero(0, 0), f1, Matrix::zero(0, 0)]
  let gm = [Matrix::zero(0, 0), Matrix::zero(g, 0), Matrix::zero(0, 0)]
  let p = derived_fiber_product(ca, cb, cc, f, gm)
  let hp = p.betti()
  let mc = l.is_maurer_cartan(x)
  (
    (twisted[1], twisted[2]),
    (hp[1], hp[2]),
    mc && twisted[1] == hp[1] && twisted[2] == hp[2],
  )
}
