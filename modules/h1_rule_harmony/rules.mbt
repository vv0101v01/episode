///|
/// Module H1 — 引入規則、消除規則、計算規則、唯一性規則。
/// 規則以命題原子的 64-bit 位元集描述；「由前提可結構性地推出結論」
/// 化約為 Horn 子句的單位傳播閉包（局部公理：邏輯消元）。
///
/// 原子編號 < 62 為一般命題原子；SELF 表示被定義的類型本身（遞迴前提），
/// PARAM 表示一般消除規則中任意的結論 C。
pub const SELF : Int32 = 62

///|
pub const PARAM : Int32 = 63

///|
/// 規則前提：`Plain(a)` 為 ⊢ a；`Hypo(m, a)` 為假言前提 [m] ⊢ a（m 為被解除假設的位元集）。
pub(all) enum Prem {
  Plain(Int32)
  Hypo(UInt64, Int32)
}

///|
/// 引入規則：前提 ⟹ 該類型（結論恆為被定義的類型）。
pub(all) struct IntroRule {
  name : String
  premises : Array[Prem]
}

///|
/// 消除規則：主前提為該類型，另有次前提，結論為原子 `concl`（PARAM 表示一般消除）。
pub(all) struct ElimRule {
  name : String
  minors : Array[Prem]
  concl : Int32
}

///|
/// 類型形成子／邏輯連接詞的規則簽名。
/// `judgmental`：屬於判斷層（不可作為一般消除之結論 C 的實例）的原子位元集。
pub(all) struct Connective {
  name : String
  intros : Array[IntroRule]
  elims : Array[ElimRule]
  judgmental : UInt64
}

///|
#derive(Eq)
pub(all) enum Polarity {
  /// 負類型：由消除（觀察）刻畫；唯一性規則為定義性 η
  Negative
  /// 正類型：由引入（建構）刻畫；唯一性規則僅命題性成立（由一般消除／歸納證得）
  Positive
  /// 局部完備性失敗：無唯一性規則
  NoUniqueness
}

///|
pub extend Polarity with Eq::{equal, not_equal}

///|
pub fn bit(a : Int32) -> UInt64 {
  1UL << a
}

///|
fn has(m : UInt64, a : Int32) -> Bool {
  ((m >> a) & 1UL) != 0UL
}

///|
/// Horn 閉包：自事實集 `facts` 出發，反覆觸發前件已滿足的子句（前件位元集 ⟹ 原子）。
/// 每輪以位元運算 O(1) 檢查一個子句；至多 |clauses| 輪。
pub fn horn_closure(facts : UInt64, clauses : Array[(UInt64, Int32)]) -> UInt64 {
  let mut f = facts
  let mut changed = true
  while changed {
    changed = false
    for cl in clauses {
      let (body, head) = cl
      if (body & f.lnot()) == 0UL && !has(f, head) {
        f = f | bit(head)
        changed = true
      }
    }
  }
  f
}

///|
/// 反演原理（Prawitz）／局部健全性：消除規則 e 作用於引入規則 i 的結論時，
/// e 的結論已可由 i 的前提與 e 的次前提結構性推出 ⇔ 存在計算規則（迂迴可消去）。
pub fn locally_sound(i : IntroRule, e : ElimRule) -> Bool {
  let mut facts = 0UL
  let clauses : Array[(UInt64, Int32)] = []
  for p in i.premises {
    match p {
      Plain(a) => facts = facts | bit(a)
      Hypo(m, a) => clauses.push((m, a))
    }
  }
  for p in e.minors {
    match p {
      Plain(a) => facts = facts | bit(a)
      Hypo(m, a) => clauses.push((m, a))
    }
  }
  has(horn_closure(facts, clauses), e.concl)
}

///|
fn subst_param(m : UInt64, g : Int32) -> UInt64 {
  if has(m, PARAM) {
    (m & bit(PARAM).lnot()) | bit(g)
  } else {
    m
  }
}

///|
fn minors_hold(
  e : ElimRule,
  facts : UInt64,
  clauses : Array[(UInt64, Int32)],
  g : Int32,
) -> Bool {
  for p in e.minors {
    match p {
      Plain(a) => {
        let a2 = if a == PARAM { g } else { a }
        if !has(facts, a2) {
          return false
        }
      }
      Hypo(m, a) => {
        let a2 = if a == PARAM { g } else { a }
        if !has(horn_closure(facts | subst_param(m, g), clauses), a2) {
          return false
        }
      }
    }
  }
  true
}

///|
/// 擁有該類型的一個證明時，以消除規則集可推出的全部原子。
/// 一般消除規則的結論 C 可實例化為 `inst` 中的任一原子。
pub fn elim_closure(
  elims : Array[ElimRule],
  facts0 : UInt64,
  clauses : Array[(UInt64, Int32)],
  inst : UInt64,
) -> UInt64 {
  let mut facts = horn_closure(facts0, clauses)
  let mut changed = true
  while changed {
    changed = false
    for e in elims {
      if e.concl != PARAM {
        if !has(facts, e.concl) && minors_hold(e, facts, clauses, PARAM) {
          facts = horn_closure(facts | bit(e.concl), clauses)
          changed = true
        }
      } else {
        let mut rest = inst & facts.lnot()
        while rest != 0UL {
          let g = rest.ctz()
          rest = rest & (rest - 1UL)
          if minors_hold(e, facts, clauses, g) {
            facts = horn_closure(facts | bit(g), clauses)
            changed = true
          }
        }
      }
    }
  }
  facts
}

///|
/// 連接詞規則中出現的全部原子。
pub fn Connective::atoms(self : Connective) -> UInt64 {
  let mut m = 0UL
  for i in self.intros {
    for p in i.premises {
      match p {
        Plain(a) => m = m | bit(a)
        Hypo(h, a) => m = m | h | bit(a)
      }
    }
  }
  for e in self.elims {
    m = m | bit(e.concl)
    for p in e.minors {
      match p {
        Plain(a) => m = m | bit(a)
        Hypo(h, a) => m = m | h | bit(a)
      }
    }
  }
  m
}

///|
/// 由事實集 `facts` 能否以某條引入規則重新引入該類型。
fn Connective::introducible(self : Connective, facts : UInt64) -> Bool {
  for i in self.intros {
    let mut ok = true
    for p in i.premises {
      match p {
        Plain(a) => if !has(facts, a) { ok = false }
        Hypo(m, a) => if !has(horn_closure(facts | m, []), a) { ok = false }
      }
    }
    if ok {
      return true
    }
  }
  false
}

///|
/// 負式局部展開：恰有一條引入規則，且其每個前提皆可由消除規則自該類型的證明取回
/// （t ≡ intro(elim₁ t, …, elimₙ t)：定義性唯一性規則）。
pub fn Connective::negative_expansion(self : Connective) -> Bool {
  if self.intros.length() != 1 {
    return false
  }
  let inst = self.atoms() & (self.judgmental | bit(PARAM) | bit(SELF)).lnot()
  for p in self.intros[0].premises {
    match p {
      Plain(a) =>
        if !has(elim_closure(self.elims, 0UL, [], inst), a) {
          return false
        }
      Hypo(m, a) =>
        if !has(elim_closure(self.elims, m, [], inst), a) {
          return false
        }
    }
  }
  true
}

///|
/// 正式局部展開：存在一般消除規則，取 C 為該類型本身時每個次前提皆可重新引入
/// （t ≡ elim(t; 各分支重新引入)：命題性唯一性規則，即歸納原理）。
pub fn Connective::positive_expansion(self : Connective) -> Bool {
  for e in self.elims {
    if e.concl != PARAM {
      continue
    }
    let mut ok = true
    for p in e.minors {
      match p {
        Plain(a) => if a != PARAM || !self.introducible(0UL) { ok = false }
        Hypo(m, a) =>
          if a == PARAM {
            if !self.introducible(subst_param(m, SELF)) {
              ok = false
            }
          } else if !has(horn_closure(m, []), a) {
            ok = false
          }
      }
    }
    if ok {
      return true
    }
  }
  false
}

///|
/// 調和性分析結果。
pub(all) struct Harmony {
  /// 局部健全：每個（引入, 消除）配對皆有計算規則
  sound : Bool
  /// 局部完備：存在局部展開（唯一性規則）
  complete : Bool
  polarity : Polarity
  /// 計算規則數 = |引入| × |消除|
  computation_rules : Int32
}

///|
pub fn Connective::harmony(self : Connective) -> Harmony {
  let mut sound = true
  for i in self.intros {
    for e in self.elims {
      if !locally_sound(i, e) {
        sound = false
      }
    }
  }
  let polarity = if self.negative_expansion() {
    Negative
  } else if self.positive_expansion() {
    Positive
  } else {
    NoUniqueness
  }
  {
    sound,
    complete: polarity != NoUniqueness,
    polarity,
    computation_rules: self.intros.length() * self.elims.length(),
  }
}

///|
/// 由引入規則「讀出」一般消除規則（Gentzen 之語；von Plato／Francez–Dyckhoff 的扁平化 GE 形式）：
/// 每條引入規則 i 對應一個次前提 [i 的簡單前提 ∪ 假言前提之結論] ⊢ C，
/// 而假言前提 [m] ⊢ b 的前件 m 轉為額外的簡單次前提。
pub fn Connective::derive_general_elim(self : Connective) -> ElimRule {
  let minors : Array[Prem] = []
  for i in self.intros {
    let mut discharged = 0UL
    for p in i.premises {
      match p {
        Plain(a) => discharged = discharged | bit(a)
        Hypo(m, b) => {
          discharged = discharged | bit(b)
          let mut rest = m
          while rest != 0UL {
            let a = rest.ctz()
            rest = rest & (rest - 1UL)
            minors.push(Plain(a))
          }
        }
      }
    }
    if has(discharged, SELF) {
      // 遞迴前提附帶歸納假設
      discharged = discharged | bit(PARAM)
    }
    minors.push(
      if discharged == 0UL {
        Plain(PARAM)
      } else {
        Hypo(discharged, PARAM)
      },
    )
  }
  { name: self.name + "-GE", minors, concl: PARAM, }
}

///|
/// 以推導出的一般消除規則取代原有消除規則。
pub fn Connective::with_general_elim(self : Connective) -> Connective {
  {
    name: self.name + "ᴳᴱ",
    intros: self.intros,
    elims: [self.derive_general_elim()],
    judgmental: self.judgmental,
  }
}

///|
/// 計算規則一覽：每個局部健全的（引入, 消除）配對各一條。
pub fn Connective::computation_rule_names(self : Connective) -> Array[String] {
  let out : Array[String] = []
  for e in self.elims {
    for i in self.intros {
      if locally_sound(i, e) {
        out.push("\{e.name}(\{i.name}) ▷")
      }
    }
  }
  out
}
