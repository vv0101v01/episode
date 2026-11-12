///|
/// 命題原子：A = 0，B = 1；EQ = 2 為判斷層原子（Id 的兩個指標定義性相等）。
pub const A : Int32 = 0

///|
pub const B : Int32 = 1

///|
pub const EQ : Int32 = 2

///|
fn intro(name : String, premises : Array[Prem]) -> IntroRule {
  { name, premises, }
}

///|
fn elim(name : String, minors : Array[Prem], concl : Int32) -> ElimRule {
  { name, minors, concl, }
}

///|
/// 依賴類型論核心的七個類型形成子（規則的命題骨架）。
pub fn type_formers() -> Array[Connective] {
  [
    {
      name: "Π",
      intros: [intro("λ", [Hypo(bit(A), B)])],
      elims: [elim("app", [Plain(A)], B)],
      judgmental: 0UL,
    },
    {
      name: "Σ",
      intros: [intro("pair", [Plain(A), Plain(B)])],
      elims: [elim("fst", [], A), elim("snd", [], B)],
      judgmental: 0UL,
    },
    { name: "Unit", intros: [intro("star", [])], elims: [], judgmental: 0UL, },
    {
      name: "Empty",
      intros: [],
      elims: [elim("absurd", [], PARAM)],
      judgmental: 0UL,
    },
    {
      name: "Bool",
      intros: [intro("tt", []), intro("ff", [])],
      elims: [elim("if", [Plain(PARAM), Plain(PARAM)], PARAM)],
      judgmental: 0UL,
    },
    {
      name: "Nat",
      intros: [intro("zero", []), intro("succ", [Plain(SELF)])],
      elims: [
        elim("rec", [Plain(PARAM), Hypo(bit(SELF) | bit(PARAM), PARAM)], PARAM),
      ],
      judgmental: 0UL,
    },
    {
      name: "Id",
      intros: [intro("refl", [Plain(EQ)])],
      elims: [elim("J", [Hypo(bit(EQ), PARAM)], PARAM)],
      judgmental: bit(EQ),
    },
  ]
}

///|
/// 經典命題連接詞，以及兩個不調和的反例：
/// tonk（Prior：∨ 的引入配 ∧ 的消除）與 weak-∧（僅有第一投影）。
pub fn logical_connectives() -> Array[Connective] {
  [
    {
      name: "→",
      intros: [intro("→I", [Hypo(bit(A), B)])],
      elims: [elim("→E", [Plain(A)], B)],
      judgmental: 0UL,
    },
    {
      name: "∧",
      intros: [intro("∧I", [Plain(A), Plain(B)])],
      elims: [elim("∧E1", [], A), elim("∧E2", [], B)],
      judgmental: 0UL,
    },
    {
      name: "∨",
      intros: [intro("∨I1", [Plain(A)]), intro("∨I2", [Plain(B)])],
      elims: [elim("∨E", [Hypo(bit(A), PARAM), Hypo(bit(B), PARAM)], PARAM)],
      judgmental: 0UL,
    },
    { name: "⊤", intros: [intro("⊤I", [])], elims: [], judgmental: 0UL, },
    {
      name: "⊥",
      intros: [],
      elims: [elim("⊥E", [], PARAM)],
      judgmental: 0UL,
    },
    {
      name: "tonk",
      intros: [intro("tonk-I", [Plain(A)])],
      elims: [elim("tonk-E", [], B)],
      judgmental: 0UL,
    },
    {
      name: "weak-∧",
      intros: [intro("w∧I", [Plain(A), Plain(B)])],
      elims: [elim("w∧E1", [], A)],
      judgmental: 0UL,
    },
  ]
}

///|
/// 由一組連接詞收集全部引入與消除規則，建立規則全域。
pub fn universe_of(cs : Array[Connective]) -> RuleUniverse {
  let intros : Array[IntroRule] = []
  let elims : Array[ElimRule] = []
  for c in cs {
    for i in c.intros {
      intros.push(i)
    }
    for e in c.elims {
      elims.push(e)
    }
  }
  RuleUniverse::new(intros, elims)
}
