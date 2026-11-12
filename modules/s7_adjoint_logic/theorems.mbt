///|
/// 線性／非線性（LNL）模式：U（非限制，W+C）> L（線性）。
pub fn lnl_modes() -> Modes {
  Modes::new(["U", "L"], [true, false], [true, false], [(0, 1)])
}

///|
/// 四模式格：U（W,C）> A（仿射，W）> L；U > S（嚴格，C）> L。
pub fn substructural_modes() -> Modes {
  Modes::new(
    ["U", "A", "S", "L"],
    [true, true, false, false],
    [true, false, true, false],
    [(0, 1), (0, 2), (1, 3), (2, 3)],
  )
}

///|
/// 判斷性 S4：V（有效性）> T（真），兩者皆 W+C。
pub fn s4_modes() -> Modes {
  Modes::new(["V", "T"], [true, true], [true, true], [(0, 1)])
}

///|
/// 指數 !A = ↓ᵁ_L ↑ᵁ_L A。
pub fn bang(a : Prop) -> Prop {
  Down(1, Up(0, a))
}

///|
/// 一項可導性斷言：名稱、證明項、目標、預期（接受或拒絕）。
pub(all) struct Claim {
  name : String
  term : Tm
  goal : Prop
  expected : Bool
}

///|
/// LNL 下指數模態的定理與反例。
pub fn lnl_claims() -> Array[Claim] {
  let a = Prop::Atom("A", 1)
  let b = Prop::Atom("B", 1)
  let ba = bang(a)
  let bb = bang(b)
  let up_a = Prop::Up(0, a)
  [
    // 失職（dereliction）= 伴隨的餘單位
    {
      name: "dereliction !A ⊸ A",
      term: Lam(ba, LetDown(Var(0), Force(Var(0)))),
      goal: Lolli(ba, a),
      expected: true,
    },
    // 挖掘（digging）= 餘單子的餘乘
    {
      name: "digging !A ⊸ !!A",
      term: Lam(ba, LetDown(Var(0), Down(1, Susp(0, Down(1, Var(0)))))),
      goal: Lolli(ba, bang(ba)),
      expected: true,
    },
    {
      name: "contraction !A ⊸ !A ⊗ !A",
      term: Lam(ba, LetDown(Var(0), Pair(Down(1, Var(0)), Down(1, Var(0))))),
      goal: Lolli(ba, Tensor(ba, ba)),
      expected: true,
    },
    {
      name: "weakening !A ⊸ 1",
      term: Lam(ba, LetDown(Var(0), Unit(1))),
      goal: Lolli(ba, One(1)),
      expected: true,
    },
    // 函子性 K：!(A ⊸ B) ⊸ !A ⊸ !B
    {
      name: "functoriality !(A ⊸ B) ⊸ !A ⊸ !B",
      term: Lam(
        bang(Lolli(a, b)),
        Lam(
          ba,
          LetDown(
            Var(1),
            LetDown(Var(1), Down(1, Susp(0, App(Force(Var(1)), Force(Var(0)))))),
          ),
        ),
      ),
      goal: Lolli(bang(Lolli(a, b)), Lolli(ba, bb)),
      expected: true,
    },
    // Seely：!(A & B) ⊸ !A ⊗ !B
    {
      name: "seely !(A & B) ⊸ !A ⊗ !B",
      term: Lam(
        bang(With(a, b)),
        LetDown(
          Var(0),
          Pair(
            Down(1, Susp(0, Fst(Force(Var(0))))),
            Down(1, Susp(0, Snd(Force(Var(0))))),
          ),
        ),
      ),
      goal: Lolli(bang(With(a, b)), Tensor(ba, bb)),
      expected: true,
    },
    // 單子的單位：A_U ⊸ ↑↓A_U（於 U）
    {
      name: "unit X ⊸ ↑↓X (mode U)",
      term: Lam(Atom("X", 0), Susp(0, Down(1, Var(0)))),
      goal: Lolli(Atom("X", 0), Up(0, Down(1, Atom("X", 0)))),
      expected: true,
    },
    // 反例：A ⊸ !A 違反獨立性原理
    {
      name: "promotion without ! : A ⊸ !A",
      term: Lam(a, Down(1, Susp(0, Var(0)))),
      goal: Lolli(a, ba),
      expected: false,
    },
    // 反例：線性假設不可複製、不可丟棄
    {
      name: "linear contraction A ⊸ A ⊗ A",
      term: Lam(a, Pair(Var(0), Var(0))),
      goal: Lolli(a, Tensor(a, a)),
      expected: false,
    },
    {
      name: "linear weakening A ⊸ 1",
      term: Lam(a, Unit(1)),
      goal: Lolli(a, One(1)),
      expected: false,
    },
    // 加性：A ⊸ A & A 合法（兩支共用資源）；A ⊗ B ⊸ A 非法
    {
      name: "additive sharing A ⊸ A & A",
      term: Lam(a, WithPair(Var(0), Var(0))),
      goal: Lolli(a, With(a, a)),
      expected: true,
    },
    {
      name: "projection from tensor A ⊗ B ⊸ A",
      term: Lam(Tensor(a, b), LetPair(Var(0), Var(1))),
      goal: Lolli(Tensor(a, b), a),
      expected: false,
    },
    // 反例：↑A 不可在線性層直接被當作 A 的來源而不經 ↓
    {
      name: "mode mixing: ↑A hypothesis in a linear function",
      term: Lam(up_a, Force(Var(0))),
      goal: Lolli(up_a, a),
      expected: false,
    },
  ]
}

///|
/// 子結構模式下的弱化／收縮定理與反例。
pub fn substructural_claims() -> Array[Claim] {
  let claims : Array[Claim] = []
  let names = ["U", "A", "S", "L"]
  let weaken = [true, true, false, false]
  let contract = [true, false, true, false]
  for m in 0..<4 {
    let a = Prop::Atom("A", m)
    claims.push({
      name: "weakening at " + names[m],
      term: Lam(a, Unit(m)),
      goal: Lolli(a, One(m)),
      expected: weaken[m],
    })
    claims.push({
      name: "contraction at " + names[m],
      term: Lam(a, Pair(Var(0), Var(0))),
      goal: Lolli(a, Tensor(a, a)),
      expected: contract[m],
    })
  }
  claims
}

///|
/// S4 的 □A = ↓ⱽ_T ↑ⱽ_T A：T、4、K 可導；A → □A 不可導。
pub fn s4_claims() -> Array[Claim] {
  let a = Prop::Atom("A", 1)
  let b = Prop::Atom("B", 1)
  let bx = fn(p : Prop) -> Prop { Down(1, Up(0, p)) }
  [
    {
      name: "T: □A → A",
      term: Lam(bx(a), LetDown(Var(0), Force(Var(0)))),
      goal: Lolli(bx(a), a),
      expected: true,
    },
    {
      name: "4: □A → □□A",
      term: Lam(bx(a), LetDown(Var(0), Down(1, Susp(0, Down(1, Var(0)))))),
      goal: Lolli(bx(a), bx(bx(a))),
      expected: true,
    },
    {
      name: "K: □(A → B) → □A → □B",
      term: Lam(
        bx(Lolli(a, b)),
        Lam(
          bx(a),
          LetDown(
            Var(1),
            LetDown(Var(1), Down(1, Susp(0, App(Force(Var(1)), Force(Var(0)))))),
          ),
        ),
      ),
      goal: Lolli(bx(Lolli(a, b)), Lolli(bx(a), bx(b))),
      expected: true,
    },
    {
      name: "necessitation of a hypothesis: A → □A",
      term: Lam(a, Down(1, Susp(0, Var(0)))),
      goal: Lolli(a, bx(a)),
      expected: false,
    },
  ]
}

///|
/// 檢驗一組斷言；回傳（符合預期數, 總數）。
pub fn verify_claims(modes : Modes, claims : Array[Claim]) -> (Int32, Int32) {
  let ck = Checker::new(modes)
  let mut ok = 0
  for c in claims {
    let (accepted, _) = ck.proves(c.term, c.goal)
    if accepted == c.expected {
      ok += 1
    }
  }
  (ok, claims.length())
}

///|
/// 伴隨 ↓ ⊣ ↑ 作為可導性上的伽羅瓦對應：
/// 由 f : ↓A ⊸ B 得轉置 f♯ = λa. susp (f (down a)) : A ⊸ ↑B，
/// 由 g : A ⊸ ↑B 得轉置 g♭ = λd. let down a = d in force (g a) : ↓A ⊸ B。
/// 兩個轉置皆保持可導性，且 (f♯)♭ 約簡回 f 的 η-展開。
/// 回傳（受檢實例數, 兩方向轉置皆通過檢查, 往返後仍通過檢查且正規化終止）。
pub fn verify_adjunction() -> (Int32, Bool, Bool) {
  let modes = lnl_modes()
  let ck = Checker::new(modes)
  let a = Prop::Atom("X", 0)
  let a2 = Prop::Atom("Y", 0)
  let b = Prop::Atom("B", 1)
  // 實例：(A, B, f : ↓A ⊸ B)
  let instances : Array[(Prop, Prop, Tm)] = [
    // B := ↓A，f = id
    (a, Down(1, a), Lam(Down(1, a), Var(0))),
    // A := ↑B，f = 餘單位
    (Up(0, b), b, Lam(Down(1, Up(0, b)), LetDown(Var(0), Force(Var(0))))),
    // A := X，B := ↓X ⊗ ↓X（收縮後打包）
    (
      a,
      Tensor(Down(1, a), Down(1, a)),
      Lam(Down(1, a), LetDown(Var(0), Pair(Down(1, Var(0)), Down(1, Var(0))))),
    ),
    // A := Y，B := 1（弱化）
    (a2, One(1), Lam(Down(1, a2), LetDown(Var(0), Unit(1)))),
  ]
  let mut both = true
  let mut round = true
  for inst in instances {
    let (pa, pb, f) = inst
    let (ok0, _) = ck.proves(f, Lolli(Down(1, pa), pb))
    // f♯
    let sharp = Lam(pa, Susp(0, App(f, Down(1, Var(0)))))
    let (ok1, _) = ck.proves(sharp, Lolli(pa, Up(0, pb)))
    // (f♯)♭
    let flat = Lam(Down(1, pa), LetDown(Var(0), Force(App(sharp, Var(0)))))
    let (ok2, _) = ck.proves(flat, Lolli(Down(1, pa), pb))
    if !(ok0 && ok1 && ok2) {
      both = false
    }
    let (nf, _, done) = normalize(flat, fuel=1000)
    let (ok3, _) = ck.proves(nf, Lolli(Down(1, pa), pb))
    if !(done && ok3) {
      round = false
    }
  }
  (instances.length(), both, round)
}

///|
/// 含切（cut）的證明項：把指數模態的各定理相互合成，供約簡檢驗。
pub fn lnl_cut_examples() -> Array[Claim] {
  let a = Prop::Atom("A", 1)
  let ba = bang(a)
  let der = fn(p : Prop) -> Tm { Lam(bang(p), LetDown(Var(0), Force(Var(0)))) }
  let dig = fn(p : Prop) -> Tm {
    Lam(bang(p), LetDown(Var(0), Down(1, Susp(0, Down(1, Var(0))))))
  }
  let contr = fn(p : Prop) -> Tm {
    Lam(bang(p), LetDown(Var(0), Pair(Down(1, Var(0)), Down(1, Var(0)))))
  }
  let weak = fn(p : Prop) -> Tm { Lam(bang(p), LetDown(Var(0), Unit(1))) }
  let kfun = fn(p : Prop, q : Prop) -> Tm {
    Lam(
      bang(Lolli(p, q)),
      Lam(
        bang(p),
        LetDown(
          Var(1),
          LetDown(Var(1), Down(1, Susp(0, App(Force(Var(1)), Force(Var(0)))))),
        ),
      ),
    )
  }
  [
    // 餘單子律：ε_{!A} ∘ δ_A = id
    {
      name: "counit after comultiplication",
      term: Lam(ba, App(der(ba), App(dig(a), Var(0)))),
      goal: Lolli(ba, ba),
      expected: true,
    },
    // !ε_A ∘ δ_A = id（經函子性 K）
    {
      name: "mapped counit after comultiplication",
      term: Lam(
        ba,
        App(App(kfun(ba, a), Down(1, Susp(0, der(a)))), App(dig(a), Var(0))),
      ),
      goal: Lolli(ba, ba),
      expected: true,
    },
    // 收縮後一份失職：!A ⊸ A ⊗ !A
    {
      name: "contract then derelict one copy",
      term: Lam(
        ba,
        LetPair(App(contr(a), Var(0)), Pair(App(der(a), Var(1)), Var(0))),
      ),
      goal: Lolli(ba, Tensor(a, ba)),
      expected: true,
    },
    // 餘么半群的單位律：收縮後丟棄一份 = id
    {
      name: "contract then discard one copy",
      term: Lam(
        ba,
        LetPair(App(contr(a), Var(0)), LetUnit(App(weak(a), Var(1)), Var(0))),
      ),
      goal: Lolli(ba, ba),
      expected: true,
    },
    // 函子保恆等：!(id) 作用於 !A
    {
      name: "functorial action of the identity",
      term: Lam(
        ba,
        App(App(kfun(a, a), Down(1, Susp(0, Lam(a, Var(0))))), Var(0)),
      ),
      goal: Lolli(ba, ba),
      expected: true,
    },
    // 加性：自 A & A 取兩次投影其一
    {
      name: "projection of an additive pair",
      term: Lam(a, Fst(WithPair(Var(0), Var(0)))),
      goal: Lolli(a, a),
      expected: true,
    },
    {
      name: "case of an injection",
      term: Lam(a, Case(Inl(a, Var(0)), Var(0), Var(0))),
      goal: Lolli(a, a),
      expected: true,
    },
  ]
}

///|
/// 主詞約簡與正規化：每個證明項沿最左最外約簡，逐步重新檢查類型與用量；
/// 回傳（受檢約簡步數, 每步皆仍證明同一命題, 全部於燃料內到達正規形, 正規形總大小）。
pub fn verify_subject_reduction(
  modes : Modes,
  claims : Array[Claim],
) -> (Int32, Bool, Bool, Int32) {
  let ck = Checker::new(modes)
  let mut steps = 0
  let mut preserved = true
  let mut terminated = true
  let mut size = 0
  for c in claims {
    let (ok, _) = ck.proves(c.term, c.goal)
    if !ok {
      preserved = false
      continue
    }
    let mut cur = c.term
    let mut fuel = 500
    while fuel > 0 {
      match step(cur) {
        Some(next) => {
          steps += 1
          let (still, _) = ck.proves(next, c.goal)
          if !still {
            preserved = false
          }
          cur = next
        }
        None => break
      }
      fuel -= 1
    }
    if fuel == 0 {
      terminated = false
    }
    size += tm_size(cur)
  }
  (steps, preserved, terminated, size)
}

///|
/// 組合範例 5 — 張量積與加法結構的對偶。線性層（模式 1）中：
///   ⊗ 對 ⊕ 分配（兩個方向）；⊗ ⊣ ⊸（柯里化兩個方向）；
///   ⊕ 為餘積：(A ⊸ C) & (B ⊸ C) ≅ (A ⊕ B ⊸ C)；& 為積：(C ⊸ A) & (C ⊸ B) ⊸ (C ⊸ A & B)。
/// 反例：加法的 & 不能充當乘法的 ⊗。
pub fn tensor_additive_claims() -> Array[Claim] {
  let a = Prop::Atom("A", 1)
  let b = Prop::Atom("B", 1)
  let c = Prop::Atom("C", 1)
  [
    {
      name: "distribution A ⊗ (B ⊕ C) ⊸ (A ⊗ B) ⊕ (A ⊗ C)",
      term: distribute_term(a, b, c),
      goal: Lolli(Tensor(a, Plus(b, c)), Plus(Tensor(a, b), Tensor(a, c))),
      expected: true,
    },
    {
      name: "factoring (A ⊗ B) ⊕ (A ⊗ C) ⊸ A ⊗ (B ⊕ C)",
      term: factor_term(a, b, c),
      goal: Lolli(Plus(Tensor(a, b), Tensor(a, c)), Tensor(a, Plus(b, c))),
      expected: true,
    },
    {
      name: "currying (A ⊗ B ⊸ C) ⊸ A ⊸ B ⊸ C",
      term: Lam(
        Lolli(Tensor(a, b), c),
        Lam(a, Lam(b, App(Var(2), Pair(Var(1), Var(0))))),
      ),
      goal: Lolli(Lolli(Tensor(a, b), c), Lolli(a, Lolli(b, c))),
      expected: true,
    },
    {
      name: "uncurrying (A ⊸ B ⊸ C) ⊸ A ⊗ B ⊸ C",
      term: Lam(
        Lolli(a, Lolli(b, c)),
        Lam(Tensor(a, b), LetPair(Var(0), App(App(Var(3), Var(1)), Var(0)))),
      ),
      goal: Lolli(Lolli(a, Lolli(b, c)), Lolli(Tensor(a, b), c)),
      expected: true,
    },
    {
      name: "copairing (A ⊸ C) & (B ⊸ C) ⊸ A ⊕ B ⊸ C",
      term: Lam(
        With(Lolli(a, c), Lolli(b, c)),
        Lam(
          Plus(a, b),
          Case(Var(0), App(Fst(Var(2)), Var(0)), App(Snd(Var(2)), Var(0))),
        ),
      ),
      goal: Lolli(With(Lolli(a, c), Lolli(b, c)), Lolli(Plus(a, b), c)),
      expected: true,
    },
    {
      name: "restriction (A ⊕ B ⊸ C) ⊸ (A ⊸ C) & (B ⊸ C)",
      term: Lam(
        Lolli(Plus(a, b), c),
        WithPair(
          Lam(a, App(Var(1), Inl(b, Var(0)))),
          Lam(b, App(Var(1), Inr(a, Var(0)))),
        ),
      ),
      goal: Lolli(Lolli(Plus(a, b), c), With(Lolli(a, c), Lolli(b, c))),
      expected: true,
    },
    {
      name: "pairing (C ⊸ A) & (C ⊸ B) ⊸ C ⊸ A & B",
      term: Lam(
        With(Lolli(c, a), Lolli(c, b)),
        Lam(c, WithPair(App(Fst(Var(1)), Var(0)), App(Snd(Var(1)), Var(0)))),
      ),
      goal: Lolli(With(Lolli(c, a), Lolli(c, b)), Lolli(c, With(a, b))),
      expected: true,
    },
    {
      name: "A ⊗ (B & C) ⊸ (A ⊗ B) & (A ⊗ C)",
      term: Lam(
        Tensor(a, With(b, c)),
        LetPair(
          Var(0),
          WithPair(Pair(Var(1), Fst(Var(0))), Pair(Var(1), Snd(Var(0)))),
        ),
      ),
      goal: Lolli(Tensor(a, With(b, c)), With(Tensor(a, b), Tensor(a, c))),
      expected: true,
    },
    // 反例：& 的兩個分量共用同一份資源，不能同時取出
    {
      name: "A & B ⊸ A ⊗ B",
      term: Lam(With(a, b), Pair(Fst(Var(0)), Snd(Var(0)))),
      goal: Lolli(With(a, b), Tensor(a, b)),
      expected: false,
    },
    // 反例：⊕ 的注入不能憑空製造另一側
    {
      name: "A ⊕ B ⊸ A",
      term: Lam(Plus(a, b), Case(Var(0), Var(0), Var(0))),
      goal: Lolli(Plus(a, b), a),
      expected: false,
    },
  ]
}

///|
fn distribute_term(a : Prop, b : Prop, c : Prop) -> Tm {
  Lam(
    Tensor(a, Plus(b, c)),
    LetPair(
      Var(0),
      Case(
        Var(0),
        Inl(Tensor(a, c), Pair(Var(2), Var(0))),
        Inr(Tensor(a, b), Pair(Var(2), Var(0))),
      ),
    ),
  )
}

///|
fn factor_term(a : Prop, b : Prop, c : Prop) -> Tm {
  Lam(
    Plus(Tensor(a, b), Tensor(a, c)),
    Case(
      Var(0),
      LetPair(Var(0), Pair(Var(1), Inl(c, Var(0)))),
      LetPair(Var(0), Pair(Var(1), Inr(b, Var(0)))),
    ),
  )
}

///|
/// 含切的往返：分配後再提取公因子（及反向）作用於具體的注入，
/// 供 `verify_subject_reduction` 逐步約簡。
pub fn tensor_additive_cuts() -> Array[Claim] {
  let a = Prop::Atom("A", 1)
  let b = Prop::Atom("B", 1)
  let c = Prop::Atom("C", 1)
  let left = Plus(Tensor(a, b), Tensor(a, c))
  [
    {
      name: "factor ∘ distribute on a ⊗ inl b",
      term: Lam(
        a,
        Lam(
          b,
          App(
            factor_term(a, b, c),
            App(distribute_term(a, b, c), Pair(Var(1), Inl(c, Var(0)))),
          ),
        ),
      ),
      goal: Lolli(a, Lolli(b, Tensor(a, Plus(b, c)))),
      expected: true,
    },
    {
      name: "distribute ∘ factor on inr (a ⊗ c)",
      term: Lam(
        a,
        Lam(
          c,
          App(
            distribute_term(a, b, c),
            App(factor_term(a, b, c), Inr(Tensor(a, b), Pair(Var(1), Var(0)))),
          ),
        ),
      ),
      goal: Lolli(a, Lolli(c, left)),
      expected: true,
    },
  ]
}
