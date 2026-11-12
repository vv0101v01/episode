///|
/// Module S9 — 小立方體算子 Eₙ（Boardman–Vogt／May）。
///
/// Eₙ(k) 的一個運算是單位 n-方體內 k 個帶標號、內部兩兩不交、與座標軸平行的小方體。
/// 座標用精確有理數（分子／分母，Int64）。
pub(all) struct Q {
  n : Int64
  d : Int64
}

///|
fn gcd64(a : Int64, b : Int64) -> Int64 {
  let mut x = if a < 0L { -a } else { a }
  let mut y = if b < 0L { -b } else { b }
  while y != 0L {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
pub fn Q::new(n : Int64, d : Int64) -> Q {
  let g = gcd64(n, d)
  let g2 = if g == 0L { 1L } else { g }
  if d < 0L {
    { n: -n / g2, d: -d / g2, }
  } else {
    { n: n / g2, d: d / g2, }
  }
}

///|
pub fn Q::of_int(k : Int32) -> Q {
  { n: k.to_int64(), d: 1L, }
}

///|
pub fn Q::frac(n : Int32, d : Int32) -> Q {
  Q::new(n.to_int64(), d.to_int64())
}

///|
pub fn Q::add(self : Q, o : Q) -> Q {
  Q::new(self.n * o.d + o.n * self.d, self.d * o.d)
}

///|
pub fn Q::sub(self : Q, o : Q) -> Q {
  Q::new(self.n * o.d - o.n * self.d, self.d * o.d)
}

///|
pub fn Q::mul(self : Q, o : Q) -> Q {
  Q::new(self.n * o.n, self.d * o.d)
}

///|
pub fn Q::cmp(self : Q, o : Q) -> Int32 {
  let l = self.n * o.d
  let r = o.n * self.d
  if l < r {
    -1
  } else if l > r {
    1
  } else {
    0
  }
}

///|
pub fn Q::same(self : Q, o : Q) -> Bool {
  self.n == o.n && self.d == o.d
}

///|
pub fn Q::show(self : Q) -> String {
  if self.d == 1L {
    "\{self.n}"
  } else {
    "\{self.n}/\{self.d}"
  }
}

///|
/// 一個小方體：每個座標軸上的區間 [lo, hi]。
pub(all) struct Box {
  lo : Array[Q]
  hi : Array[Q]
}

///|
/// Eₙ(k) 的運算：`boxes[j]` 為第 j 個輸入槽的小方體。
pub(all) struct Cubes {
  dim : Int32
  boxes : Array[Box]
}

///|
pub fn Cubes::arity(self : Cubes) -> Int32 {
  self.boxes.length()
}

///|
/// 單位元：充滿整個方體的單一小方體。
pub fn Cubes::unit(dim : Int32) -> Cubes {
  let lo : Array[Q] = []
  let hi : Array[Q] = []
  for _ in 0..<dim {
    lo.push(Q::of_int(0))
    hi.push(Q::of_int(1))
  }
  { dim, boxes: [{ lo, hi, }], }
}

///|
fn interiors_disjoint(a : Box, b : Box) -> Bool {
  // 存在某軸使兩區間內部不交
  for k in 0..<a.lo.length() {
    if a.hi[k].cmp(b.lo[k]) <= 0 || b.hi[k].cmp(a.lo[k]) <= 0 {
      return true
    }
  }
  false
}

///|
/// 合法性：每個小方體非退化、落在單位方體內，且內部兩兩不交。
pub fn Cubes::is_valid(self : Cubes) -> Bool {
  let zero = Q::of_int(0)
  let one = Q::of_int(1)
  for b in self.boxes {
    if b.lo.length() != self.dim || b.hi.length() != self.dim {
      return false
    }
    for k in 0..<self.dim {
      if b.lo[k].cmp(zero) < 0 ||
        b.hi[k].cmp(one) > 0 ||
        b.lo[k].cmp(b.hi[k]) >= 0 {
        return false
      }
    }
  }
  for i in 0..<self.boxes.length() {
    for j in (i + 1)..<self.boxes.length() {
      if !interiors_disjoint(self.boxes[i], self.boxes[j]) {
        return false
      }
    }
  }
  true
}

///|
pub fn Cubes::same(self : Cubes, o : Cubes) -> Bool {
  if self.dim != o.dim || self.boxes.length() != o.boxes.length() {
    return false
  }
  for j in 0..<self.boxes.length() {
    for k in 0..<self.dim {
      if !self.boxes[j].lo[k].same(o.boxes[j].lo[k]) ||
        !self.boxes[j].hi[k].same(o.boxes[j].hi[k]) {
        return false
      }
    }
  }
  true
}

///|
/// 把方體 inner 經仿射嵌入放進 outer。
fn embed_box(outer : Box, inner : Box) -> Box {
  let lo : Array[Q] = []
  let hi : Array[Q] = []
  for k in 0..<outer.lo.length() {
    let len = outer.hi[k].sub(outer.lo[k])
    lo.push(outer.lo[k].add(len.mul(inner.lo[k])))
    hi.push(outer.lo[k].add(len.mul(inner.hi[k])))
  }
  { lo, hi, }
}

///|
/// 部分合成 c ∘ᵢ d：把 d 的整個構形縮放後插入 c 的第 i 個小方體（組合範例 9：
/// 「把一個運算的輸出插到另一個運算的某個輸入槽」）。
pub fn Cubes::compose(self : Cubes, i : Int32, d : Cubes) -> Cubes {
  let boxes : Array[Box] = []
  for j in 0..<i {
    boxes.push(self.boxes[j])
  }
  for b in d.boxes {
    boxes.push(embed_box(self.boxes[i], b))
  }
  for j in (i + 1)..<self.boxes.length() {
    boxes.push(self.boxes[j])
  }
  { dim: self.dim, boxes, }
}

///|
/// 對稱群作用：(c·σ) 的第 j 槽為 c 的第 σ(j) 槽。
pub fn Cubes::permute(self : Cubes, sigma : Array[Int32]) -> Cubes {
  let boxes : Array[Box] = []
  for j in 0..<sigma.length() {
    boxes.push(self.boxes[sigma[j]])
  }
  { dim: self.dim, boxes, }
}

///|
/// 穩定化 Eₙ → Eₙ₊₁：每個小方體乘上整個區間 [0, 1]。
pub fn Cubes::suspend(self : Cubes) -> Cubes {
  let boxes : Array[Box] = []
  for b in self.boxes {
    let lo = b.lo.copy()
    let hi = b.hi.copy()
    lo.push(Q::of_int(0))
    hi.push(Q::of_int(1))
    boxes.push({ lo, hi, })
  }
  { dim: self.dim + 1, boxes, }
}

///|
/// 一維情形：小區間自左至右的次序給出排列（第 r 個位置上是哪個槽）。
/// 這是 π₀(E₁(k)) ≅ S_k 的分類映射，也是 E₁ → Ass 的算子態射。
pub fn Cubes::order(self : Cubes) -> Array[Int32] {
  let idx : Array[Int32] = []
  for j in 0..<self.boxes.length() {
    idx.push(j)
  }
  idx.sort_by(fn(a, b) { self.boxes[a].lo[0].cmp(self.boxes[b].lo[0]) })
  idx
}

///|
/// 結合算子 Ass 中的部分合成（以「位置 → 槽」的排列表示）：
/// 把 τ 的整段插入 σ 中槽 i 所在的位置，並重新編號。
pub fn ass_compose(
  sigma : Array[Int32],
  i : Int32,
  tau : Array[Int32],
) -> Array[Int32] {
  let m = tau.length()
  let out : Array[Int32] = []
  for s in sigma {
    if s < i {
      out.push(s)
    } else if s == i {
      for t in tau {
        out.push(i + t)
      }
    } else {
      out.push(s + m - 1)
    }
  }
  out
}

///|
/// 確定性偽隨機構形：把單位方體沿各軸切成格子，取其中 k 個互異格子並各自內縮。
pub fn random_cubes(dim : Int32, k : Int32, seed : Int32) -> Cubes {
  let mut state = seed
  let next = fn(bound : Int32) -> Int32 {
    state = (state * 1103515245 + 12345) & 0x7fffffff
    (state >> 8) % bound
  }
  // 每軸的格數：使格子總數 ≥ k
  let mut per = 1
  let mut total = 1
  while total < k {
    per += 1
    total = 1
    for _ in 0..<dim {
      total *= per
    }
  }
  let chosen : Array[Int32] = []
  while chosen.length() < k {
    let c = next(total)
    if !chosen.contains(c) {
      chosen.push(c)
    }
  }
  let boxes : Array[Box] = []
  for c in chosen {
    let lo : Array[Q] = []
    let hi : Array[Q] = []
    let mut code = c
    for _ in 0..<dim {
      let cell = code % per
      code = code / per
      // 內縮：在格子 [cell/per, (cell+1)/per] 內取 [a, b]，a < b ∈ {0..4}/4
      let a = next(2)
      let b = 3 + next(2)
      lo.push(Q::frac(4 * cell + a, 4 * per))
      hi.push(Q::frac(4 * cell + b, 4 * per))
    }
    boxes.push({ lo, hi, })
  }
  { dim, boxes, }
}

///|
/// 算子公理的檢驗結果。
pub(all) struct OperadAxioms {
  /// 合成保持合法性
  closure : Bool
  /// 單位律：c ∘ᵢ 1 = c，1 ∘₀ c = c
  unit : Bool
  /// 序列結合律：(a ∘ᵢ b) ∘ᵢ₊ⱼ c = a ∘ᵢ (b ∘ⱼ c)
  sequential : Bool
  /// 平行結合律：(a ∘ᵢ b) ∘ₖ₊ₘ₋₁ c = (a ∘ₖ c) ∘ᵢ b（i < k，m = b 的元數）
  parallel : Bool
  /// 等變性：(a·σ) ∘ᵢ b 與 a ∘_{σ(i)} b 相差一個區塊排列
  equivariance : Bool
  /// 穩定化為算子態射
  suspension : Bool
  /// 一維：order 為到 Ass 的算子態射
  to_associative : Bool
  instances : Int32
}

///|
pub fn OperadAxioms::all(self : OperadAxioms) -> Bool {
  self.closure &&
  self.unit &&
  self.sequential &&
  self.parallel &&
  self.equivariance &&
  self.suspension &&
  self.to_associative
}

///|
pub fn verify_operad_axioms(dim : Int32, trials : Int32) -> OperadAxioms {
  let mut closure = true
  let mut unit = true
  let mut sequential = true
  let mut parallel = true
  let mut equivariance = true
  let mut suspension = true
  let mut to_ass = true
  let mut instances = 0
  for t in 0..<trials {
    let a = random_cubes(dim, 2 + t % 3, 11 + 7 * t)
    let b = random_cubes(dim, 1 + t % 3, 101 + 13 * t)
    let c = random_cubes(dim, 1 + (t + 1) % 3, 211 + 17 * t)
    let ka = a.arity()
    let kb = b.arity()
    if !(a.is_valid() && b.is_valid() && c.is_valid()) {
      closure = false
    }
    for i in 0..<ka {
      instances += 1
      let ab = a.compose(i, b)
      if !ab.is_valid() || ab.arity() != ka + kb - 1 {
        closure = false
      }
      if !a.compose(i, Cubes::unit(dim)).same(a) {
        unit = false
      }
      for j in 0..<kb {
        if !ab.compose(i + j, c).same(a.compose(i, b.compose(j, c))) {
          sequential = false
        }
      }
      for k in (i + 1)..<ka {
        if !ab.compose(k + kb - 1, c).same(a.compose(k, c).compose(i, b)) {
          parallel = false
        }
      }
      // 穩定化
      if !ab.suspend().same(a.suspend().compose(i, b.suspend())) {
        suspension = false
      }
      if dim == 1 && ab.order() != ass_compose(a.order(), i, b.order()) {
        to_ass = false
      }
    }
    if !Cubes::unit(dim).compose(0, a).same(a) {
      unit = false
    }
    // 等變性：σ 為循環移位。 (a·σ) ∘ᵢ b 的槽重排後等於 a ∘_{σ(i)} b
    let sigma : Array[Int32] = []
    for j in 0..<ka {
      sigma.push((j + 1) % ka)
    }
    let lhs = a.permute(sigma).compose(0, b)
    let rhs = a.compose(sigma[0], b)
    // lhs 的槽：先是 b 的 kb 個（位於 a 的槽 σ(0)），再是 a 的槽 σ(1), σ(2), …
    // rhs 的槽：a 的槽 0..σ(0)-1，b 的 kb 個，a 的槽 σ(0)+1..
    let block : Array[Int32] = []
    for j in 0..<kb {
      block.push(sigma[0] + j)
    }
    for j in 1..<ka {
      let s = sigma[j]
      block.push(if s < sigma[0] { s } else { s + kb - 1 })
    }
    if !lhs.same(rhs.permute(block)) {
      equivariance = false
    }
  }
  {
    closure,
    unit,
    sequential,
    parallel,
    equivariance,
    suspension,
    to_associative: to_ass,
    instances,
  }
}

///|
/// E₁ 在迴路上的作用（於同倫類層次）：θ(c; w₁, …, w_k) 為各迴路的字依小區間
/// 自左至右的次序相接。回傳接合後的字。
pub fn act_on_loops(c : Cubes, loops : Array[Array[Int32]]) -> Array[Int32] {
  let out : Array[Int32] = []
  for slot in c.order() {
    for x in loops[slot] {
      out.push(x)
    }
  }
  out
}

///|
/// 代數公理：θ(c ∘ᵢ d; ws) = θ(c; …, θ(d; ws_i…), …)。回傳（受檢實例數, 成立）。
pub fn verify_loop_action(trials : Int32) -> (Int32, Bool) {
  let mut ok = true
  let mut n = 0
  for t in 0..<trials {
    let c = random_cubes(1, 2 + t % 3, 31 + 5 * t)
    let d = random_cubes(1, 1 + t % 3, 77 + 9 * t)
    for i in 0..<c.arity() {
      n += 1
      let total = c.arity() + d.arity() - 1
      let ws : Array[Array[Int32]] = []
      for j in 0..<total {
        ws.push([2 * j, 2 * j + 1 + 2 * (t % 2), 2 * j])
      }
      let lhs = act_on_loops(c.compose(i, d), ws)
      let inner : Array[Array[Int32]] = []
      for j in 0..<d.arity() {
        inner.push(ws[i + j])
      }
      let outer : Array[Array[Int32]] = []
      for j in 0..<i {
        outer.push(ws[j])
      }
      outer.push(act_on_loops(d, inner))
      for j in (i + d.arity())..<total {
        outer.push(ws[j])
      }
      if lhs != act_on_loops(c, outer) {
        ok = false
      }
    }
  }
  (n, ok)
}
