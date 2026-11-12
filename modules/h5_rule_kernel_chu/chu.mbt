///|
/// Module H5 — H1（規則綱要）× H3（核心）的橋接。
/// 每個類型形成子的具體見證：計算規則的實例（可約式, 收縮結果）、
/// 唯一性規則的陳述，及其定義性證明（refl）與命題性證明（以消除子證得）。
pub(all) struct RuleCase {
  former : String
  computation : Array[(String, String)]
  /// 唯一性規則陳述（一個類型）
  eta_statement : String
  /// 以 refl 作成的證明（僅當 η 為定義性時核心才接受）
  eta_by_refl : String
  /// 以消除子作成的命題性證明
  eta_by_elim : String
}

///|
/// 核心七個類型形成子的規則見證。
pub fn rule_cases() -> Array[RuleCase] {
  [
    {
      former: "Π",
      computation: [("((lam (x Nat) (S x)) 2)", "3")],
      eta_statement: "(Pi (f (-> Nat Nat)) (Id (-> Nat Nat) f (lam (x Nat) (f x))))",
      eta_by_refl: "(lam f refl)",
      eta_by_elim: "(lam f (refl f))",
    },
    {
      former: "Σ",
      computation: [
        ("(fst (the (* Nat Bool) (pair 1 tt)))", "1"),
        ("(snd (the (* Nat Bool) (pair 1 tt)))", "tt"),
      ],
      eta_statement: "(Pi (p (* Nat Bool)) (Id (* Nat Bool) p (pair (fst p) (snd p))))",
      eta_by_refl: "(lam p refl)",
      eta_by_elim: "(lam p (refl p))",
    },
    {
      former: "Unit",
      computation: [],
      eta_statement: "(Pi (u Unit) (Id Unit u star))",
      eta_by_refl: "(lam u refl)",
      eta_by_elim: "(lam u (refl u))",
    },
    {
      former: "Empty",
      computation: [],
      eta_statement: "(Pi (e Empty) (x Empty) (Id Empty e x))",
      eta_by_refl: "(lam e x refl)",
      eta_by_elim: "(lam e x (absurd e))",
    },
    {
      former: "Bool",
      computation: [("(if tt 1 2)", "1"), ("(if ff 1 2)", "2")],
      eta_statement: "(Pi (b Bool) (Id Bool b (if b tt ff)))",
      eta_by_refl: "(lam b refl)",
      eta_by_elim: "(lam b (if-as (x (Id Bool x (if x tt ff))) b refl refl))",
    },
    {
      former: "Nat",
      computation: [
        ("(rec (x Nat) 5 (k ih (S ih)) 0)", "5"),
        ("(rec (x Nat) 5 (k ih (S ih)) 2)", "7"),
      ],
      eta_statement: "(Pi (n Nat) (Id Nat n (rec (x Nat) 0 (k ih (S ih)) n)))",
      eta_by_refl: "(lam n refl)",
      eta_by_elim: "(lam n (rec (x (Id Nat x (rec (y Nat) 0 (k ih (S ih)) x))) refl (k ih (J (a b q (Id Nat (S a) (S b))) (w (refl (S w))) ih)) n))",
    },
    {
      former: "Id",
      computation: [("(J (x y q Nat) (w (S w)) (refl 8))", "9")],
      eta_statement: "(Pi (a Nat) (b Nat) (p (Id Nat a b)) (Id (Id Nat a b) p (J (x y q (Id Nat x y)) (w (refl w)) p)))",
      eta_by_refl: "(lam a b p refl)",
      eta_by_elim: "(lam a b p (J (x y q (Id (Id Nat x y) q (J (x1 y1 q1 (Id Nat x1 y1)) (w (refl w)) q))) (w refl) p))",
    },
  ]
}

///|
/// 單一類型形成子的對偶檢驗結果。
pub(all) struct FormerReport {
  former : String
  polarity : @h1.Polarity
  /// H1 預測的計算規則數／核心驗證為定義性相等的計算規則實例數
  predicted_rules : Int32
  verified_rules : Int32
  /// 核心是否接受唯一性規則的 refl 證明（定義性 η）
  definitional_eta : Bool
  /// 核心是否接受以消除子作成的證明（命題性 η）
  propositional_eta : Bool
  /// 綱要與核心行為一致：規則數吻合，且「負極性 ⇔ 定義性 η」，且唯一性規則至少命題性成立
  consistent : Bool
}

///|
fn accepts(k : @h3.Kernel, src : String) -> Bool {
  try k.elaborate(src) catch {
    _ => false
  } noraise {
    _ => true
  }
}

///|
/// refl 證明被拒絕，且拒絕原因確為「兩側非定義性相等」（排除其他錯誤來源）。
fn rejected_as_not_definitional(k : @h3.Kernel, src : String) -> Bool {
  try k.elaborate(src) catch {
    Expected(what, _) => what == "definitionally equal sides for refl"
    _ => false
  } noraise {
    _ => false
  }
}

///|
pub fn verify_former(
  k : @h3.Kernel,
  c : @h1.Connective,
  case : RuleCase,
) -> FormerReport {
  let h = c.harmony()
  let mut verified = 0
  for rc in case.computation {
    let (redex, contractum) = rc
    let ok = try {
      let r = k.elaborate(redex)
      let e = k.elaborate(contractum)
      // 可約式本身不是正規形，且與收縮結果定義性相等
      !@h3.is_normal(r.term) && k.convertible(@h3.Ctx::empty(), r.term, e.term)
    } catch {
      _ => false
    }
    if ok {
      verified += 1
    }
  }
  let statement_ok = accepts(k, case.eta_statement)
  let by_refl = "(the " + case.eta_statement + " " + case.eta_by_refl + ")"
  let by_elim = "(the " + case.eta_statement + " " + case.eta_by_elim + ")"
  let definitional = statement_ok && accepts(k, by_refl)
  let refused = statement_ok && rejected_as_not_definitional(k, by_refl)
  let propositional = statement_ok && accepts(k, by_elim)
  let polarity_matches = if h.polarity == Negative {
    definitional
  } else {
    refused
  }
  {
    former: case.former,
    polarity: h.polarity,
    predicted_rules: h.computation_rules,
    verified_rules: verified,
    definitional_eta: definitional,
    propositional_eta: propositional,
    consistent: h.sound &&
    h.complete &&
    verified == h.computation_rules &&
    polarity_matches &&
    propositional,
  }
}

///|
/// 對全部類型形成子執行對偶檢驗。
pub fn verify_all(k : @h3.Kernel) -> Array[FormerReport] {
  let formers = @h1.type_formers()
  let cases = rule_cases()
  let out : Array[FormerReport] = []
  for i in 0..<formers.length() {
    out.push(verify_former(k, formers[i], cases[i]))
  }
  out
}

///|
fn intro_term(name : String) -> @h3.Tm? {
  match name {
    "λ" => Some(Lam(NatTy, Var(0)))
    "pair" => Some(Pair(Zero, Zero, NatTy))
    "star" => Some(Star)
    "tt" => Some(Tt)
    "ff" => Some(Ff)
    "zero" => Some(Zero)
    "succ" => Some(Succ(Zero))
    "refl" => Some(Refl(Zero))
    _ => None
  }
}

///|
fn elim_term(name : String, x : @h3.Tm) -> @h3.Tm? {
  match name {
    "app" => Some(App(x, Zero))
    "fst" => Some(Fst(x))
    "snd" => Some(Snd(x))
    "absurd" => Some(Absurd(NatTy, x))
    "if" => Some(If(NatTy, x, Zero, Zero))
    "rec" => Some(NatRec(NatTy, Zero, Var(0), x))
    "J" => Some(J(NatTy, Zero, x))
    _ => None
  }
}

///|
/// 語法—語義 Chu 對偶的檢驗結果。
pub(all) struct ChuReport {
  intros : Int32
  elims : Int32
  /// 綱要矩陣（同一形成子且局部健全）與操作矩陣（核心求值確實觸發計算規則）逐格相等
  matrices_agree : Bool
  /// 操作矩陣中 1 的個數 = 計算規則總數
  fired_cells : Int32
  /// 操作矩陣的形式概念數，以及「每個形成子的（引入集, 消除集）皆為形式概念」
  concepts : Int32
  formers_are_concepts : Bool
  /// 伽羅瓦定律於操作矩陣上的窮舉驗證（受檢配對數, 成立）
  galois_pairs : Int32
  galois_holds : Bool
}

///|
/// 建立操作矩陣：對每個（引入子 i, 消除子 e）讓核心對 e(i) 求值——
/// 觸發計算規則則記 1；卡住（`Stuck`）則記 0。再與 H1 的綱要矩陣比較。
pub fn verify_chu_duality(k : @h3.Kernel) -> ChuReport {
  let formers = @h1.type_formers()
  let intros : Array[@h1.IntroRule] = []
  let elims : Array[@h1.ElimRule] = []
  let intro_owner : Array[Int32] = []
  let elim_owner : Array[Int32] = []
  for f in 0..<formers.length() {
    for i in formers[f].intros {
      intros.push(i)
      intro_owner.push(f)
    }
    for e in formers[f].elims {
      elims.push(e)
      elim_owner.push(f)
    }
  }
  let operational : Array[UInt64] = Array::make(intros.length(), 0UL)
  let schematic : Array[UInt64] = Array::make(intros.length(), 0UL)
  let mut fired = 0
  let env = @h3.Ctx::empty().env
  for i in 0..<intros.length() {
    for e in 0..<elims.length() {
      if intro_owner[i] == elim_owner[e] &&
        @h1.locally_sound(intros[i], elims[e]) {
        schematic[i] = schematic[i] | @h1.bit(e)
      }
      let fires = match intro_term(intros[i].name) {
        Some(it) =>
          match elim_term(elims[e].name, it) {
            Some(t) =>
              try k.eval(env, t) catch {
                _ => false
              } noraise {
                _ => true
              }
            None => false
          }
        None => false
      }
      if fires {
        operational[i] = operational[i] | @h1.bit(e)
        fired += 1
      }
    }
  }
  let mut agree = true
  for i in 0..<intros.length() {
    if operational[i] != schematic[i] {
      agree = false
    }
  }
  let u = @h1.RuleUniverse::from_matrix(intros, elims, operational)
  let cs = u.concepts()
  let mut all_concepts = true
  for f in 0..<formers.length() {
    let mut s = 0UL
    let mut t = 0UL
    for i in 0..<intros.length() {
      if intro_owner[i] == f {
        s = s | @h1.bit(i)
      }
    }
    for e in 0..<elims.length() {
      if elim_owner[e] == f {
        t = t | @h1.bit(e)
      }
    }
    // 無引入子（Empty）或無消除子（Unit）的形成子對應格的頂／底，不要求閉合
    if s != 0UL && t != 0UL {
      if u.right_polar(s) != t || u.left_polar(t) != s {
        all_concepts = false
      }
    }
  }
  let (pairs, holds) = u.verify_galois_law()
  {
    intros: intros.length(),
    elims: elims.length(),
    matrices_agree: agree,
    fired_cells: fired,
    concepts: cs.length(),
    formers_are_concepts: all_concepts,
    galois_pairs: pairs,
    galois_holds: holds,
  }
}
