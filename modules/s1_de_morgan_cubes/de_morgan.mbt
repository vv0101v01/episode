///|
/// Module S1 — 德摩根立方體代數。
///
/// 區間 𝕀 的項由名字 i、端點 0/1、∧、∨、對合 ¬（即 1−r）生成。
/// n 個名字上的自由德摩根代數同構於 2n 個生成元（i 與 ¬i）上的自由有界分配格，
/// 故每個元素有唯一的「反鏈析取範式」：單項式（文字集合）的反鏈。
/// 單項式以位元集表示：第 i 位 = 文字 i，第 i+MAX_NAMES 位 = 文字 ¬i。
pub const MAX_NAMES : Int32 = 15

///|
/// 區間元素的正規形：依數值排序、互不包含的單項式陣列。
/// `[]` 為 0；`[0]`（空合取）為 1。
pub(all) struct Dm {
  ms : Array[Int32]
}

///|
fn minimize(raw : Array[Int32]) -> Array[Int32] {
  let sorted = raw.copy()
  sorted.sort_by(fn(a, b) {
    let pa = a.popcnt()
    let pb = b.popcnt()
    if pa != pb {
      pa - pb
    } else {
      a.compare(b)
    }
  })
  let kept : Array[Int32] = []
  for m in sorted {
    let mut absorbed = false
    for k in kept {
      if (k & m) == k {
        absorbed = true
        break
      }
    }
    if !absorbed {
      kept.push(m)
    }
  }
  kept.sort()
  kept
}

///|
pub fn Dm::zero() -> Dm {
  { ms: [], }
}

///|
pub fn Dm::one() -> Dm {
  { ms: [0], }
}

///|
/// 名字 i。
pub fn Dm::name(i : Int32) -> Dm {
  { ms: [1 << i], }
}

///|
/// 文字 ¬i（即 1−i）。
pub fn Dm::co_name(i : Int32) -> Dm {
  { ms: [1 << (i + MAX_NAMES)], }
}

///|
pub fn Dm::join(self : Dm, other : Dm) -> Dm {
  let raw = self.ms.copy()
  for m in other.ms {
    raw.push(m)
  }
  { ms: minimize(raw), }
}

///|
pub fn Dm::meet(self : Dm, other : Dm) -> Dm {
  let raw : Array[Int32] = []
  for a in self.ms {
    for b in other.ms {
      raw.push(a | b)
    }
  }
  { ms: minimize(raw), }
}

///|
fn flip_literal_bit(bit : Int32) -> Int32 {
  if bit < MAX_NAMES {
    bit + MAX_NAMES
  } else {
    bit - MAX_NAMES
  }
}

///|
/// 對合 ¬r：以德摩根律推入——¬(⋁ₖ mₖ) = ⋀ₖ ¬mₖ，¬(⋀ l) = ⋁ ¬l。
pub fn Dm::neg(self : Dm) -> Dm {
  let mut acc = Dm::one()
  for m in self.ms {
    let clause : Array[Int32] = []
    for bit in 0..<(2 * MAX_NAMES) {
      if ((m >> bit) & 1) == 1 {
        clause.push(1 << flip_literal_bit(bit))
      }
    }
    acc = acc.meet({ ms: minimize(clause), })
  }
  acc
}

///|
/// 正規形相等即代數相等（自由代數的字問題）。
pub fn Dm::same(self : Dm, other : Dm) -> Bool {
  self.ms == other.ms
}

///|
/// 格序：a ≤ b ⇔ a 的每個單項式都被 b 的某個單項式吸收。
pub fn Dm::leq(self : Dm, other : Dm) -> Bool {
  for m in self.ms {
    let mut covered = false
    for k in other.ms {
      if (k & m) == k {
        covered = true
        break
      }
    }
    if !covered {
      return false
    }
  }
  true
}

///|
pub fn Dm::is_zero(self : Dm) -> Bool {
  self.ms.length() == 0
}

///|
pub fn Dm::is_one(self : Dm) -> Bool {
  self.ms.length() == 1 && self.ms[0] == 0
}

///|
/// 出現的名字集合（位元集）。
pub fn Dm::support(self : Dm) -> Int32 {
  let mut s = 0
  for m in self.ms {
    s = s | (m & ((1 << MAX_NAMES) - 1)) | (m >> MAX_NAMES)
  }
  s
}

///|
/// 同時代換：名字 i ↦ `image(i)`。代換是德摩根代數同態。
pub fn Dm::subst(self : Dm, image : (Int32) -> Dm) -> Dm {
  let mut acc = Dm::zero()
  for m in self.ms {
    let mut term = Dm::one()
    for i in 0..<MAX_NAMES {
      if ((m >> i) & 1) == 1 {
        term = term.meet(image(i))
      }
      if ((m >> (i + MAX_NAMES)) & 1) == 1 {
        term = term.meet(image(i).neg())
      }
    }
    acc = acc.join(term)
  }
  acc
}

///|
/// 面映射：把名字 i 固定於端點（`one=true` 為 1，否則 0）。
pub fn Dm::face(self : Dm, i : Int32, one~ : Bool) -> Dm {
  self.subst(fn(j) {
    if j == i {
      if one {
        Dm::one()
      } else {
        Dm::zero()
      }
    } else {
      Dm::name(j)
    }
  })
}

///|
pub fn Dm::show(self : Dm) -> String {
  if self.is_zero() {
    return "0"
  }
  if self.is_one() {
    return "1"
  }
  let sb = StringBuilder()
  let mut first_m = true
  for m in self.ms {
    if !first_m {
      sb.write_string(" ∨ ")
    }
    first_m = false
    let mut first_l = true
    for i in 0..<MAX_NAMES {
      if ((m >> i) & 1) == 1 {
        if !first_l {
          sb.write_string("∧")
        }
        first_l = false
        sb.write_string("i\{i}")
      }
      if ((m >> (i + MAX_NAMES)) & 1) == 1 {
        if !first_l {
          sb.write_string("∧")
        }
        first_l = false
        sb.write_string("¬i\{i}")
      }
    }
  }
  sb.to_string()
}

///|
fn Dm::key(self : Dm) -> String {
  let sb = StringBuilder()
  for m in self.ms {
    sb.write_string("\{m},")
  }
  sb.to_string()
}

///|
/// Belnap 四值德摩根代數 𝟜 = 𝟚×𝟚，¬(x, y) = (¬y, ¬x)。值以兩位元 (x | y<<1) 編碼。
/// 在賦值 `v`（名字 i 的值取 `(v >> 2i) & 3`）下求值。
pub fn Dm::eval4(self : Dm, v : Int32) -> Int32 {
  let mut acc = 0
  for m in self.ms {
    let mut term = 3
    for i in 0..<MAX_NAMES {
      let x = (v >> (2 * i)) & 3
      if ((m >> i) & 1) == 1 {
        term = term & x
      }
      if ((m >> (i + MAX_NAMES)) & 1) == 1 {
        // ¬(x0, x1) = (¬x1, ¬x0)
        let nx = (1 - ((x >> 1) & 1)) | ((1 - (x & 1)) << 1)
        term = term & nx
      }
    }
    acc = acc | term
  }
  acc
}

///|
/// Kalman 完備性的可執行形式：a = b 於一切德摩根代數 ⇔ 於 𝟜 的一切賦值下相等。
/// 回傳（語義相等, 受檢賦值數）。`n` 為名字數。
pub fn semantically_equal4(a : Dm, b : Dm, n : Int32) -> (Bool, Int32) {
  let total = 1 << (2 * n)
  for v in 0..<total {
    if a.eval4(v) != b.eval4(v) {
      return (false, v + 1)
    }
  }
  (true, total)
}

///|
/// 由名字 0..n-1 生成的整個自由德摩根代數（以閉包列舉）。
/// |F(1)| = 6，|F(2)| = 168（= 4 個生成元的自由有界分配格，Dedekind 數 M(4)）。
pub fn free_algebra(n : Int32, limit~ : Int32) -> Array[Dm] {
  let seen : Map[String, Bool] = Map([])
  let elems : Array[Dm] = []
  let add = fn(x : Dm) {
    let k = x.key()
    if !seen.contains(k) {
      seen[k] = true
      elems.push(x)
    }
  }
  add(Dm::zero())
  add(Dm::one())
  for i in 0..<n {
    add(Dm::name(i))
    add(Dm::co_name(i))
  }
  let mut frontier = 0
  while frontier < elems.length() && elems.length() < limit {
    let x = elems[frontier]
    frontier += 1
    let upto = elems.length()
    for j in 0..<upto {
      let y = elems[j]
      add(x.meet(y))
      add(x.join(y))
    }
  }
  elems
}

///|
/// 局部可補性：c 在區間 [a, b] 內的相對補元 d（c∧d = a 且 c∨d = b），於 `universe` 中搜尋。
/// 分配格中相對補元若存在則唯一。
pub fn relative_complement(universe : Array[Dm], a : Dm, b : Dm, c : Dm) -> Dm? {
  for d in universe {
    if a.leq(d) && d.leq(b) && c.meet(d).same(a) && c.join(d).same(b) {
      return Some(d)
    }
  }
  None
}

///|
/// 局部可補性的統計報告。
pub(all) struct ComplementReport {
  /// 代數大小
  size : Int32
  /// 全域可補元個數（布林中心）；自由德摩根代數中恰為 {0, 1}
  center : Int32
  /// 受檢的區間 [a, b]（a ≤ b）數
  intervals : Int32
  /// 其中為布林格（每個元素皆有相對補元）的區間數
  boolean_intervals : Int32
  /// 最大布林區間的元素數
  largest_boolean : Int32
  /// ¬ 的不動點個數（如 i∧¬i ∨ … 型的「中間」元素）
  neg_fixed_points : Int32
  /// Kleene 條件 x∧¬x ≤ y∨¬y 的反例數（> 0 表示非 Kleene 代數）
  kleene_violations : Int32
}

///|
pub fn complement_report(universe : Array[Dm]) -> ComplementReport {
  let zero = Dm::zero()
  let one = Dm::one()
  let mut center = 0
  let mut fixed = 0
  for x in universe {
    if relative_complement(universe, zero, one, x) is Some(_) {
      center += 1
    }
    if x.neg().same(x) {
      fixed += 1
    }
  }
  let mut intervals = 0
  let mut boolean_intervals = 0
  let mut largest = 0
  for a in universe {
    for b in universe {
      if !a.leq(b) {
        continue
      }
      intervals += 1
      let inside : Array[Dm] = []
      for c in universe {
        if a.leq(c) && c.leq(b) {
          inside.push(c)
        }
      }
      let mut all = true
      for c in inside {
        if relative_complement(inside, a, b, c) is None {
          all = false
          break
        }
      }
      if all {
        boolean_intervals += 1
        if inside.length() > largest {
          largest = inside.length()
        }
      }
    }
  }
  let mut kleene = 0
  for x in universe {
    let lhs = x.meet(x.neg())
    for y in universe {
      if !lhs.leq(y.join(y.neg())) {
        kleene += 1
      }
    }
  }
  {
    size: universe.length(),
    center,
    intervals,
    boolean_intervals,
    largest_boolean: largest,
    neg_fixed_points: fixed,
    kleene_violations: kleene,
  }
}

///|
/// 德摩根代數公理於 `universe` 上的窮舉檢驗；回傳（受檢等式實例數, 全部成立）。
pub fn verify_de_morgan_laws(universe : Array[Dm]) -> (Int32, Bool) {
  let mut checked = 0
  let mut ok = true
  for x in universe {
    checked += 1
    if !x.neg().neg().same(x) {
      ok = false
    }
    for y in universe {
      checked += 3
      if !x.meet(y).neg().same(x.neg().join(y.neg())) {
        ok = false
      }
      if !x.join(y).neg().same(x.neg().meet(y.neg())) {
        ok = false
      }
      // 吸收律
      if !x.meet(x.join(y)).same(x) {
        ok = false
      }
    }
  }
  (checked, ok)
}
