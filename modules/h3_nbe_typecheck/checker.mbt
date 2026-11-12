///|
/// 推導規則名稱（判斷 Γ ⊢ t : A 的最後一步）。
#derive(Eq)
pub(all) enum Rule {
  Hyp
  UnivF
  PiF
  PiI
  PiE
  SigmaF
  SigmaI
  SigmaE1
  SigmaE2
  UnitF
  UnitI
  EmptyF
  EmptyE
  BoolF
  BoolI
  BoolE
  NatF
  NatI
  NatE
  IdF
  IdI
  IdE
  /// 轉換／包攝規則：Γ ⊢ t : A，A ≤ B ⟹ Γ ⊢ t : B
  Conv
  /// 定義規則：Γ ⊢ A type，Γ ⊢ e : A，Γ, x := e : A ⊢ b : B ⟹ Γ ⊢ let x := e in b : B[e/x]
  LetDef
}

///|
pub extend Rule with Eq::{equal, not_equal}

///|
/// 規則分類：形成／引入／消除／結構。
#derive(Eq)
pub(all) enum RuleClass {
  Formation
  Introduction
  Elimination
  Structural
}

///|
pub extend RuleClass with Eq::{equal, not_equal}

///|
pub fn Rule::class(self : Rule) -> RuleClass {
  match self {
    UnivF | PiF | SigmaF | UnitF | EmptyF | BoolF | NatF | IdF => Formation
    PiI | SigmaI | UnitI | BoolI | NatI | IdI => Introduction
    PiE | SigmaE1 | SigmaE2 | EmptyE | BoolE | NatE | IdE => Elimination
    Hyp | Conv | LetDef => Structural
  }
}

///|
pub fn Rule::name(self : Rule) -> String {
  match self {
    Hyp => "Hyp"
    UnivF => "U-F"
    PiF => "Π-F"
    PiI => "Π-I"
    PiE => "Π-E"
    SigmaF => "Σ-F"
    SigmaI => "Σ-I"
    SigmaE1 => "Σ-E1"
    SigmaE2 => "Σ-E2"
    UnitF => "1-F"
    UnitI => "1-I"
    EmptyF => "0-F"
    EmptyE => "0-E"
    BoolF => "2-F"
    BoolI => "2-I"
    BoolE => "2-E"
    NatF => "N-F"
    NatI => "N-I"
    NatE => "N-E"
    IdF => "Id-F"
    IdI => "Id-I"
    IdE => "Id-E"
    Conv => "Conv"
    LetDef => "Let"
  }
}

///|
/// 推導樹：證明物件本身。`tm` 為主詞，`ty` 為其類型（語義值），`premises` 為前提推導。
/// 前提次序：Π-F/Σ-F [A, B]；Π-I [A, b]；Π-E [f, a]；Σ-I [a, 族, b]；Σ-E [p]；
/// 0-E [C, e]；2-E [C, s, t, e]；N-I(S) [n]；N-E [C, z, s, n]；Id-F [A, x, y]；Id-I [a]；Id-E [C, d, p]；Conv [原推導]。
pub(all) struct Deriv {
  rule : Rule
  tm : Tm
  ty : Val
  premises : Array[Deriv]
}

///|
/// 推導樹的規則總數。
pub fn Deriv::size(self : Deriv) -> Int32 {
  let mut n = 1
  for p in self.premises {
    n += p.size()
  }
  n
}

///|
/// 規則使用統計：（形成, 引入, 消除, 結構）。
pub fn Deriv::class_counts(self : Deriv) -> (Int32, Int32, Int32, Int32) {
  let counts : Array[Int32] = [0, 0, 0, 0]
  self.count_into(counts)
  (counts[0], counts[1], counts[2], counts[3])
}

///|
fn Deriv::count_into(self : Deriv, counts : Array[Int32]) -> Unit {
  let k = match self.rule.class() {
    Formation => 0
    Introduction => 1
    Elimination => 2
    Structural => 3
  }
  counts[k] += 1
  for p in self.premises {
    p.count_into(counts)
  }
}

///|
fn Kernel::show_val(self : Kernel, ctx : Ctx, v : Val) -> String {
  try self.quote_ty(ctx, v) catch {
    _ => "<unprintable>"
  } noraise {
    t => show_tm_at(t, ctx.lvl)
  }
}

///|
/// 判斷 Γ ⊢ A type：回傳推導與其宇宙層級。
pub fn Kernel::infer_type(
  self : Kernel,
  ctx : Ctx,
  t : Tm,
) -> (Deriv, Int32) raise KernelError {
  let d = self.infer(ctx, t)
  match d.ty {
    VUniv(l) => (d, l)
    other => raise Expected("a universe", self.show_val(ctx, other))
  }
}

///|
/// 判斷 Γ ⊢ t : A（檢查模式）：合成類型後以累積子類型包攝。
pub fn Kernel::check(
  self : Kernel,
  ctx : Ctx,
  t : Tm,
  expected : Val,
) -> Deriv raise KernelError {
  let d = self.infer(ctx, t)
  if self.conv(ctx.lvl, d.ty, expected) {
    self.conv_fast += 1
    return d
  }
  if self.sub_ty(ctx, d.ty, expected) {
    return { rule: Conv, tm: t, ty: expected, premises: [d], }
  }
  raise Mismatch(
    self.show_val(ctx, expected),
    self.show_val(ctx, d.ty),
    show_tm_at(t, ctx.lvl),
  )
}

///|
fn max_int(a : Int32, b : Int32) -> Int32 {
  if a > b {
    a
  } else {
    b
  }
}

///|
/// 判斷 Γ ⊢ t ⇒ A（合成模式）：核心項全標註，故每個項皆可合成其主類型。
/// 回傳完整推導樹（證明物件）。
pub fn Kernel::infer(
  self : Kernel,
  ctx : Ctx,
  t : Tm,
) -> Deriv raise KernelError {
  match t {
    Var(i) => { rule: Hyp, tm: t, ty: ctx.type_of_index(i), premises: [], }
    Univ(l) => { rule: UnivF, tm: t, ty: VUniv(l + 1), premises: [], }
    Pi(a, b) => {
      let (da, la) = self.infer_type(ctx, a)
      let (db, lb) = self.infer_type(ctx.bind(self.eval(ctx.env, a)), b)
      { rule: PiF, tm: t, ty: VUniv(max_int(la, lb)), premises: [da, db], }
    }
    Sigma(a, b) => {
      let (da, la) = self.infer_type(ctx, a)
      let (db, lb) = self.infer_type(ctx.bind(self.eval(ctx.env, a)), b)
      { rule: SigmaF, tm: t, ty: VUniv(max_int(la, lb)), premises: [da, db], }
    }
    Lam(a, b) => {
      let (da, _) = self.infer_type(ctx, a)
      let av = self.eval(ctx.env, a)
      let inner = ctx.bind(av)
      let db = self.infer(inner, b)
      let cod = self.quote_ty(inner, db.ty)
      {
        rule: PiI,
        tm: t,
        ty: VPi(done(av), { env: ctx.env, body: cod, }),
        premises: [da, db],
      }
    }
    App(f, a) => {
      let df = self.infer(ctx, f)
      match df.ty {
        VPi(dom, cod) => {
          let da = self.check(ctx, a, self.force(dom))
          {
            rule: PiE,
            tm: t,
            ty: self.inst(cod, self.delay(ctx.env, a)),
            premises: [df, da],
          }
        }
        other => raise Expected("a Pi type", self.show_val(ctx, other))
      }
    }
    Pair(a, b, fam) => {
      let da = self.infer(ctx, a)
      let (dfam, _) = self.infer_type(ctx.bind(da.ty), fam)
      let bty = self.eval(Cons(self.delay(ctx.env, a), ctx.env), fam)
      let db = self.check(ctx, b, bty)
      {
        rule: SigmaI,
        tm: t,
        ty: VSigma(done(da.ty), { env: ctx.env, body: fam, }),
        premises: [da, dfam, db],
      }
    }
    Fst(p) => {
      let dp = self.infer(ctx, p)
      match dp.ty {
        VSigma(a, _) =>
          { rule: SigmaE1, tm: t, ty: self.force(a), premises: [dp], }
        other => raise Expected("a Sigma type", self.show_val(ctx, other))
      }
    }
    Snd(p) => {
      let dp = self.infer(ctx, p)
      match dp.ty {
        VSigma(_, b) =>
          {
            rule: SigmaE2,
            tm: t,
            ty: self.inst(b, self.delay(ctx.env, Fst(p))),
            premises: [dp],
          }
        other => raise Expected("a Sigma type", self.show_val(ctx, other))
      }
    }
    UnitTy => { rule: UnitF, tm: t, ty: VUniv(0), premises: [], }
    Star => { rule: UnitI, tm: t, ty: VUnitTy, premises: [], }
    EmptyTy => { rule: EmptyF, tm: t, ty: VUniv(0), premises: [], }
    Absurd(c, e) => {
      let (dc, _) = self.infer_type(ctx, c)
      let de = self.check(ctx, e, VEmptyTy)
      { rule: EmptyE, tm: t, ty: self.eval(ctx.env, c), premises: [dc, de], }
    }
    BoolTy => { rule: BoolF, tm: t, ty: VUniv(0), premises: [], }
    Tt | Ff => { rule: BoolI, tm: t, ty: VBoolTy, premises: [], }
    If(c, s, x, y) => {
      let (dc, _) = self.infer_type(ctx.bind(VBoolTy), c)
      let ds = self.check(ctx, s, VBoolTy)
      let dx = self.check(ctx, x, self.eval(Cons(done(VTt), ctx.env), c))
      let dy = self.check(ctx, y, self.eval(Cons(done(VFf), ctx.env), c))
      {
        rule: BoolE,
        tm: t,
        ty: self.eval(Cons(self.delay(ctx.env, s), ctx.env), c),
        premises: [dc, ds, dx, dy],
      }
    }
    NatTy => { rule: NatF, tm: t, ty: VUniv(0), premises: [], }
    Zero => { rule: NatI, tm: t, ty: VNatTy, premises: [], }
    Succ(n) => {
      let dn = self.check(ctx, n, VNatTy)
      { rule: NatI, tm: t, ty: VNatTy, premises: [dn], }
    }
    NatRec(c, z, s, n) => {
      let (dc, _) = self.infer_type(ctx.bind(VNatTy), c)
      let dz = self.check(ctx, z, self.eval(Cons(done(VZero), ctx.env), c))
      let pred = ctx.fresh()
      let ctx1 = ctx.bind(VNatTy)
      let ctx2 = ctx1.bind(self.eval(Cons(pred, ctx.env), c))
      let ds = self.check(
        ctx2,
        s,
        self.eval(Cons(done(VSucc(pred)), ctx.env), c),
      )
      let dn = self.check(ctx, n, VNatTy)
      {
        rule: NatE,
        tm: t,
        ty: self.eval(Cons(self.delay(ctx.env, n), ctx.env), c),
        premises: [dc, dz, ds, dn],
      }
    }
    IdTy(a, x, y) => {
      let (da, l) = self.infer_type(ctx, a)
      let av = self.eval(ctx.env, a)
      let dx = self.check(ctx, x, av)
      let dy = self.check(ctx, y, av)
      { rule: IdF, tm: t, ty: VUniv(l), premises: [da, dx, dy], }
    }
    Refl(a) => {
      let da = self.infer(ctx, a)
      let th = self.delay(ctx.env, a)
      { rule: IdI, tm: t, ty: VIdTy(done(da.ty), th, th), premises: [da], }
    }
    Let(a, e, b) => {
      let (da, _) = self.infer_type(ctx, a)
      let av = self.eval(ctx.env, a)
      let de = self.check(ctx, e, av)
      // 定義以懸置綁入語境：b 的類型中出現的 x 直接展開為 e
      let db = self.infer(ctx.bind_def(av, self.delay(ctx.env, e)), b)
      { rule: LetDef, tm: t, ty: db.ty, premises: [da, de, db], }
    }
    J(c, d, p) => {
      let dp = self.infer(ctx, p)
      match dp.ty {
        VIdTy(dom, a, b) => {
          let av = self.force(dom)
          let x = ctx.fresh()
          let ctx1 = ctx.bind(av)
          let y = ctx1.fresh()
          let ctx2 = ctx1.bind(av)
          let ctx3 = ctx2.bind(VIdTy(dom, x, y))
          let (dc, _) = self.infer_type(ctx3, c)
          let dd = self.check(
            ctx1,
            d,
            self.eval(Cons(done(VRefl(x)), Cons(x, Cons(x, ctx.env))), c),
          )
          {
            rule: IdE,
            tm: t,
            ty: self.eval(
              Cons(self.delay(ctx.env, p), Cons(b, Cons(a, ctx.env))),
              c,
            ),
            premises: [dc, dd, dp],
          }
        }
        other => raise Expected("an identity type", self.show_val(ctx, other))
      }
    }
  }
}

///|
/// 正規化：類型檢查後以 NbE 求 β-正規、η-長的正規形；回傳（正規形，類型的正規形）。
pub fn Kernel::normalize(
  self : Kernel,
  ctx : Ctx,
  t : Tm,
) -> (Tm, Tm) raise KernelError {
  let d = self.infer(ctx, t)
  let v = self.eval(ctx.env, t)
  (self.quote_nf(ctx, d.ty, v), self.quote_ty(ctx, d.ty))
}

///|
/// 判斷 Γ ⊢ a ≡ b : A（定義性相等，含 Π/Σ/Unit 的 η）。兩項須可檢查於同一類型。
pub fn Kernel::convertible(
  self : Kernel,
  ctx : Ctx,
  a : Tm,
  b : Tm,
) -> Bool raise KernelError {
  let da = self.infer(ctx, a)
  let _ = self.check(ctx, b, da.ty)
  self.conv_typed(ctx, da.ty, self.eval(ctx.env, a), self.eval(ctx.env, b))
}

///|
/// 僅以無類型（項導向）演算法判斷轉換。
pub fn Kernel::convertible_untyped(
  self : Kernel,
  ctx : Ctx,
  a : Tm,
  b : Tm,
) -> Bool raise KernelError {
  self.conv(ctx.lvl, self.eval(ctx.env, a), self.eval(ctx.env, b))
}
