///|
/// 規則全域：一組引入規則與一組消除規則（各 ≤ 64 條），
/// 以相容關係 r(i, e) ⇔ `locally_sound(i, e)` 構成 Chu 空間／形式脈絡。
/// `rows[i]` 為引入規則 i 可容許的消除規則位元集；`cols[e]` 為其轉置。
pub(all) struct RuleUniverse {
  intros : Array[IntroRule]
  elims : Array[ElimRule]
  rows : Array[UInt64]
  cols : Array[UInt64]
}

///|
pub fn RuleUniverse::new(
  intros : Array[IntroRule],
  elims : Array[ElimRule],
) -> RuleUniverse {
  let rows : Array[UInt64] = Array::make(intros.length(), 0UL)
  let cols : Array[UInt64] = Array::make(elims.length(), 0UL)
  for i in 0..<intros.length() {
    for e in 0..<elims.length() {
      if locally_sound(intros[i], elims[e]) {
        rows[i] = rows[i] | bit(e)
        cols[e] = cols[e] | bit(i)
      }
    }
  }
  { intros, elims, rows, cols, }
}

///|
/// 由外部給定的相容矩陣建立規則全域（供語義側——例如核心的實際求值行為——使用）。
pub fn RuleUniverse::from_matrix(
  intros : Array[IntroRule],
  elims : Array[ElimRule],
  rows : Array[UInt64],
) -> RuleUniverse {
  let cols : Array[UInt64] = Array::make(elims.length(), 0UL)
  for i in 0..<intros.length() {
    for e in 0..<elims.length() {
      if ((rows[i] >> e) & 1UL) != 0UL {
        cols[e] = cols[e] | bit(i)
      }
    }
  }
  { intros, elims, rows, cols, }
}

///|
fn full_mask(n : Int32) -> UInt64 {
  if n >= 64 {
    0xFFFFFFFFFFFFFFFFUL
  } else {
    (1UL << n) - 1UL
  }
}

///|
/// 右極 S▷：被 S 中每條引入規則所證成的全部消除規則（最強的調和消除集）。
pub fn RuleUniverse::right_polar(self : RuleUniverse, s : UInt64) -> UInt64 {
  let mut acc = full_mask(self.elims.length())
  let mut rest = s
  while rest != 0UL {
    let i = rest.ctz()
    rest = rest & (rest - 1UL)
    acc = acc & self.rows[i]
  }
  acc
}

///|
/// 左極 T◁：足以證成 T 中每條消除規則的全部引入規則（最弱的斷言根據）。
pub fn RuleUniverse::left_polar(self : RuleUniverse, t : UInt64) -> UInt64 {
  let mut acc = full_mask(self.intros.length())
  let mut rest = t
  while rest != 0UL {
    let e = rest.ctz()
    rest = rest & (rest - 1UL)
    acc = acc & self.cols[e]
  }
  acc
}

///|
/// 伽羅瓦對應定律 S ⊆ T◁ ⇔ T ⊆ S▷ 的窮舉驗證（對所有子集配對）。
/// 回傳（受檢配對數, 是否全部成立）。
pub fn RuleUniverse::verify_galois_law(self : RuleUniverse) -> (Int32, Bool) {
  let ni = self.intros.length()
  let ne = self.elims.length()
  let mut checked = 0
  let mut ok = true
  let si_max = 1UL << ni
  let te_max = 1UL << ne
  let mut s = 0UL
  while s < si_max {
    let sp = self.right_polar(s)
    let mut t = 0UL
    while t < te_max {
      let lhs = (s & self.left_polar(t).lnot()) == 0UL
      let rhs = (t & sp.lnot()) == 0UL
      if lhs != rhs {
        ok = false
      }
      checked += 1
      t = t + 1UL
    }
    s = s + 1UL
  }
  (checked, ok)
}

///|
/// 全部形式概念（S, T）：S▷ = T 且 T◁ = S。內涵集為 rows 的交集閉包，
/// 以工作表對每個已知內涵與每列取交集直至飽和。
pub fn RuleUniverse::concepts(self : RuleUniverse) -> Array[(UInt64, UInt64)] {
  let seen : Map[UInt64, Unit] = Map([])
  let intents : Array[UInt64] = []
  let top = full_mask(self.elims.length())
  seen[top] = ()
  intents.push(top)
  let mut head = 0
  while head < intents.length() {
    let cur = intents[head]
    head += 1
    for row in self.rows {
      let meet = cur & row
      if !seen.contains(meet) {
        seen[meet] = ()
        intents.push(meet)
      }
    }
  }
  let out : Array[(UInt64, UInt64)] = []
  for t in intents {
    out.push((self.left_polar(t), t))
  }
  out
}

///|
/// 消除規則集 `elims` 是否足以導出目標消除規則（在握有主前提時）。
pub fn elims_generate(
  elims : Array[ElimRule],
  target : ElimRule,
  judgmental : UInt64,
) -> Bool {
  let mut facts = 0UL
  let clauses : Array[(UInt64, Int32)] = []
  let mut atoms = bit(target.concl)
  for p in target.minors {
    match p {
      Plain(a) => {
        facts = facts | bit(a)
        atoms = atoms | bit(a)
      }
      Hypo(m, a) => {
        clauses.push((m, a))
        atoms = atoms | m | bit(a)
      }
    }
  }
  for e in elims {
    atoms = atoms | bit(e.concl)
  }
  let inst = atoms & judgmental.lnot()
  has(elim_closure(elims, facts, clauses, inst), target.concl)
}

///|
/// 穩定性（Dummett）相對於規則全域：連接詞自身的消除規則已與「全域中一切被其引入規則
/// 證成的消除規則」同樣強，即 E 生成 I▷。回傳（I▷ 的大小, 是否穩定）。
pub fn RuleUniverse::stability(
  self : RuleUniverse,
  c : Connective,
) -> (Int32, Bool) {
  let mut justified = full_mask(self.elims.length())
  for i in c.intros {
    let mut row = 0UL
    for e in 0..<self.elims.length() {
      if locally_sound(i, self.elims[e]) {
        row = row | bit(e)
      }
    }
    justified = justified & row
  }
  let mut ok = true
  let mut rest = justified
  while rest != 0UL {
    let e = rest.ctz()
    rest = rest & (rest - 1UL)
    if !elims_generate(c.elims, self.elims[e], c.judgmental) {
      ok = false
    }
  }
  (justified.popcnt(), ok)
}
