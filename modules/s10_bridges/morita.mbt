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

///|
/// 組合範例 4 — 單子分配律的複合。
/// T = 自由么半群單子（串列，「乘法」），S = 自由交換么半群單子（多重集，「加法」）。
/// 分配律 λ : T S ⇒ S T 把「和的積」展開成「積的和」；複合單子 S T 的代數即半環，
/// S T X = ℕ⟨X⟩（非交換多項式）。
///
/// 多重集以（元素, 重數）的正規列表表示：依元素字典序排序、重數為正、元素互異。
/// 元素一律編碼為整數陣列（X 的元素 x 編為 `[x]`）。
pub(all) struct Multiset {
  terms : Array[(Array[Int32], Int32)]
}

///|
fn compare_words(a : Array[Int32], b : Array[Int32]) -> Int32 {
  if a.length() != b.length() {
    return a.length() - b.length()
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return a[i] - b[i]
    }
  }
  0
}

///|
/// 正規化：排序並合併相同元素。
pub fn Multiset::of(raw : Array[(Array[Int32], Int32)]) -> Multiset {
  let sorted = raw.copy()
  sorted.sort_by(fn(x, y) { compare_words(x.0, y.0) })
  let terms : Array[(Array[Int32], Int32)] = []
  for t in sorted {
    let (w, c) = t
    if c == 0 {
      continue
    }
    if terms.length() > 0 && compare_words(terms[terms.length() - 1].0, w) == 0 {
      let (w0, c0) = terms[terms.length() - 1]
      terms[terms.length() - 1] = (w0, c0 + c)
    } else {
      terms.push((w, c))
    }
  }
  { terms, }
}

///|
pub fn Multiset::same(self : Multiset, o : Multiset) -> Bool {
  if self.terms.length() != o.terms.length() {
    return false
  }
  for i in 0..<self.terms.length() {
    if self.terms[i].1 != o.terms[i].1 ||
      compare_words(self.terms[i].0, o.terms[i].0) != 0 {
      return false
    }
  }
  true
}

///|
/// 多重集作為元素時的整數陣列編碼：[長度, 元素…, 重數] 逐項相接。
pub fn Multiset::encode(self : Multiset) -> Array[Int32] {
  let out : Array[Int32] = []
  for t in self.terms {
    let (w, c) = t
    out.push(w.length())
    for x in w {
      out.push(x)
    }
    out.push(c)
  }
  out
}

///|
pub fn Multiset::decode(code : Array[Int32]) -> Multiset {
  let terms : Array[(Array[Int32], Int32)] = []
  let mut i = 0
  while i < code.length() {
    let len = code[i]
    let w : Array[Int32] = []
    for k in 0..<len {
      w.push(code[i + 1 + k])
    }
    terms.push((w, code[i + 1 + len]))
    i += len + 2
  }
  { terms, }
}

///|
/// 串列（元素為整數陣列）作為元素時的編碼：[長度, 元素…] 逐項相接。
fn encode_list(items : Array[Array[Int32]]) -> Array[Int32] {
  let out : Array[Int32] = []
  for w in items {
    out.push(w.length())
    for x in w {
      out.push(x)
    }
  }
  out
}

///|
fn decode_list(code : Array[Int32]) -> Array[Array[Int32]] {
  let items : Array[Array[Int32]] = []
  let mut i = 0
  while i < code.length() {
    let len = code[i]
    let w : Array[Int32] = []
    for k in 0..<len {
      w.push(code[i + 1 + k])
    }
    items.push(w)
    i += len + 1
  }
  items
}

///|
/// 分配律 λ_X : T(S X) → S(T X)。輸入為多重集的串列，輸出為「串列」的多重集，
/// 其中每個串列以 `encode_list` 編碼：Π_i (Σ_j c_ij·x_ij) = Σ (Π c)·[x_1j₁, …, x_njₙ]。
pub fn distribute(factors : Array[Multiset]) -> Multiset {
  let mut acc : Array[(Array[Array[Int32]], Int32)] = [([], 1)]
  for f in factors {
    let next : Array[(Array[Array[Int32]], Int32)] = []
    for partial in acc {
      let (items, c) = partial
      for t in f.terms {
        let (x, d) = t
        let extended = items.copy()
        extended.push(x)
        next.push((extended, c * d))
      }
    }
    acc = next
  }
  Multiset::of(acc.map(fn(t) { (encode_list(t.0), t.1) }))
}

///|
/// μ_S：多重集的多重集（內層以 `encode` 編碼）攤平。
pub fn flatten_sum(m : Multiset) -> Multiset {
  let raw : Array[(Array[Int32], Int32)] = []
  for t in m.terms {
    let (code, c) = t
    for u in Multiset::decode(code).terms {
      raw.push((u.0, u.1 * c))
    }
  }
  Multiset::of(raw)
}

///|
/// S(μ_T)：把多重集中每個「串列的串列」（兩層 `encode_list`）相接成一個串列。
fn concat_inside(m : Multiset) -> Multiset {
  let raw : Array[(Array[Int32], Int32)] = []
  for t in m.terms {
    let (code, c) = t
    let joined : Array[Array[Int32]] = []
    for inner in decode_list(code) {
      for w in decode_list(inner) {
        joined.push(w)
      }
    }
    raw.push((encode_list(joined), c))
  }
  Multiset::of(raw)
}

///|
/// 確定性偽隨機多重集：`size` 項，元素取自 `[0, alphabet)`，重數 1–2。
fn sample_multiset(seed : Int32, size : Int32, alphabet : Int32) -> Multiset {
  let mut state = seed
  let raw : Array[(Array[Int32], Int32)] = []
  for _ in 0..<size {
    state = (state * 1103515245 + 12345) & 0x7fffffff
    let x = (state >> 8) % alphabet
    state = (state * 1103515245 + 12345) & 0x7fffffff
    raw.push(([x], 1 + (state >> 8) % 2))
  }
  Multiset::of(raw)
}

///|
/// Beck 分配律四公理的檢驗結果。
pub(all) struct DistributiveLaw {
  /// λ ∘ T(η_S) = η_S T
  unit_sum : Bool
  /// λ ∘ η_T S = S(η_T)
  unit_product : Bool
  /// λ ∘ T(μ_S) = μ_S ∘ S(λ) ∘ λ_S
  mult_sum : Bool
  /// λ ∘ μ_T S = S(μ_T) ∘ λ_T ∘ T(λ)
  mult_product : Bool
  /// 複合單子 S T 的 Kleisli 結合律與單位律（多項式代換）
  composite_monad : Bool
  /// 求值 ℕ⟨X⟩ → 𝔽_p 為 S T-代數（半環同態）
  evaluation_is_algebra : Bool
  instances : Int32
}

///|
pub fn DistributiveLaw::all(self : DistributiveLaw) -> Bool {
  self.unit_sum &&
  self.unit_product &&
  self.mult_sum &&
  self.mult_product &&
  self.composite_monad &&
  self.evaluation_is_algebra
}

///|
/// 多項式（串列的多重集）的 Kleisli 代換：p >>= f，f 把每個變數送到一個多項式。
/// 由分配律導出：先對每個單項式的各變數代入，再以 λ 展開、μ_S 與 μ_T 攤平。
pub fn substitute(p : Multiset, f : (Int32) -> Multiset) -> Multiset {
  let outer : Array[(Array[Int32], Int32)] = []
  for t in p.terms {
    let (code, c) = t
    // 單項式 = 變數的串列；各變數代入後得多項式的串列
    let factors : Array[Multiset] = []
    for x in decode_list(code) {
      factors.push(f(x[0]))
    }
    // λ_T：元素為「串列」；再 S(μ_T) 相接
    outer.push((concat_inside(distribute(factors)).encode(), c))
  }
  flatten_sum(Multiset::of(outer))
}

///|
/// 變數 x 作為多項式（η_S η_T）。
pub fn variable(x : Int32) -> Multiset {
  { terms: [(encode_list([[x]]), 1)], }
}

///|
/// 多項式於 𝔽_p 的求值（變數 x ↦ rho(x)）。
pub fn evaluate(p : Multiset, rho : (Int32) -> Int32) -> Int32 {
  let mut total = 0
  for t in p.terms {
    let (code, c) = t
    let mut prod = @s6.md(c)
    for x in decode_list(code) {
      prod = @s6.mul(prod, rho(x[0]))
    }
    total = @s6.md(total + prod)
  }
  total
}

///|
/// 定理（Beck）：λ 為分配律，故 S T 為單子，其代數為半環。以偽隨機樣本檢驗。
pub fn verify_distributive_law(trials : Int32) -> DistributiveLaw {
  let mut unit_sum = true
  let mut unit_product = true
  let mut mult_sum = true
  let mut mult_product = true
  let mut composite = true
  let mut algebra = true
  let mut instances = 0
  let singleton = fn(x : Array[Int32]) -> Multiset { { terms: [(x, 1)], } }
  for t in 0..<trials {
    instances += 1
    let m1 = sample_multiset(3 + 7 * t, 2, 3)
    let m2 = sample_multiset(5 + 11 * t, 2 + t % 2, 3)
    let m3 = sample_multiset(9 + 13 * t, 1 + t % 2, 3)
    // (1) 單元素多重集的串列 ↦ 該串列的單元素多重集
    let xs : Array[Array[Int32]] = [[t % 3], [(t + 1) % 3], [t % 2]]
    if !distribute(xs.map(singleton)).same(singleton(encode_list(xs))) {
      unit_sum = false
    }
    // (2) 單元素串列 [m] ↦ m 中每個 x 換成 [x]
    let lifted = Multiset::of(m2.terms.map(fn(u) { (encode_list([u.0]), u.1) }))
    if !distribute([m2]).same(lifted) {
      unit_product = false
    }
    // (3) 輸入：多重集的多重集的串列
    let mm1 = Multiset::of([(m1.encode(), 1), (m2.encode(), 2)])
    let mm2 = Multiset::of([(m3.encode(), 1), (m1.encode(), 1)])
    let lhs3 = distribute([flatten_sum(mm1), flatten_sum(mm2)])
    // λ_S：把內層多重集當作元素；S(λ)：對每個串列施 λ；μ_S：攤平
    let stage : Array[(Array[Int32], Int32)] = []
    for u in distribute([mm1, mm2]).terms {
      let (code, c) = u
      let inner = decode_list(code).map(Multiset::decode)
      stage.push((distribute(inner).encode(), c))
    }
    if !lhs3.same(flatten_sum(Multiset::of(stage))) {
      mult_sum = false
    }
    // (4) 輸入：多重集的串列的串列
    let ll = [[m1, m2], [m3], [m2, m1]]
    let flat : Array[Multiset] = []
    for l in ll {
      for m in l {
        flat.push(m)
      }
    }
    // T(λ)：對每個內層串列施 λ；λ_T：元素為串列；S(μ_T)：相接
    let rhs4 = concat_inside(distribute(ll.map(distribute)))
    if !distribute(flat).same(rhs4) {
      mult_product = false
    }
    // 複合單子：多項式 p = λ[m1, m2]，代換 f、g
    let p = distribute([m1, m2])
    let f = fn(x : Int32) -> Multiset {
      distribute([sample_multiset(17 * x + t, 2, 3), singleton([x])])
    }
    let g = fn(x : Int32) -> Multiset {
      distribute([singleton([(x + 1) % 3]), sample_multiset(29 * x + t, 2, 3)])
    }
    let assoc_l = substitute(substitute(p, f), g)
    let assoc_r = substitute(p, fn(x) { substitute(f(x), g) })
    if !assoc_l.same(assoc_r) ||
      !substitute(p, variable).same(p) ||
      !substitute(variable(t % 3), f).same(f(t % 3)) {
      composite = false
    }
    // 求值為代數：eval(p >>= f) = eval(p; x ↦ eval(f x))
    let rho = fn(x : Int32) -> Int32 { 2 + 3 * x + t }
    if evaluate(substitute(p, f), rho) !=
      evaluate(p, fn(x) { evaluate(f(x), rho) }) {
      algebra = false
    }
  }
  {
    unit_sum,
    unit_product,
    mult_sum,
    mult_product,
    composite_monad: composite,
    evaluation_is_algebra: algebra,
    instances,
  }
}
