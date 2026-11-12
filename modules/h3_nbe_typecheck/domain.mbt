///|
/// 語義域：弱頭正規值。所有「引數位置」皆為記憶化懸置（call-by-need），
/// 相同的懸置物件在轉換檢查中以物理相等 O(1) 判同而不需求值。
pub(all) enum Val {
  VNe(Neu)
  VUniv(Int32)
  VPi(Thunk, Clos)
  VLam(Thunk, Clos)
  VSigma(Thunk, Clos)
  VPair(Thunk, Thunk, Clos)
  VUnitTy
  VStar
  VEmptyTy
  VBoolTy
  VTt
  VFf
  VNatTy
  VZero
  VSucc(Thunk)
  VIdTy(Thunk, Thunk, Thunk)
  VRefl(Thunk)
}

///|
/// 中性值：變數（de Bruijn 層級）上堆疊的消除子脊。
pub(all) enum Neu {
  NVar(Int32)
  NApp(Neu, Thunk)
  NFst(Neu)
  NSnd(Neu)
  NAbsurd(Thunk, Neu)
  NIf(Clos, Neu, Thunk, Thunk)
  NNatRec(Clos, Thunk, Clos, Neu)
  NJ(Clos, Clos, Neu)
}

///|
pub(all) enum Susp {
  Done(Val)
  Delay(Env, Tm)
  /// 自然數遞迴的歸納假設：rec(C, z, s, pred) 於需要時才計算
  RecIH(Clos, Thunk, Clos, Thunk)
}

///|
pub(all) struct Thunk {
  mut s : Susp
}

///|
pub(all) enum Env {
  Nil
  Cons(Thunk, Env)
}

///|
pub(all) struct Clos {
  env : Env
  body : Tm
}

///|
/// 類型語境中各變數的類型（最新者在前）。
pub(all) enum Types {
  TNil
  TCons(Val, Types)
}

///|
pub(all) struct Ctx {
  lvl : Int32
  env : Env
  types : Types
}

///|
pub fn Ctx::empty() -> Ctx {
  { lvl: 0, env: Nil, types: TNil, }
}

///|
pub fn done(v : Val) -> Thunk {
  { s: Done(v), }
}

///|
/// 語境下一個新鮮變數（層級 = 目前深度）。
pub fn Ctx::fresh(self : Ctx) -> Thunk {
  done(VNe(NVar(self.lvl)))
}

///|
pub fn Ctx::bind(self : Ctx, ty : Val) -> Ctx {
  {
    lvl: self.lvl + 1,
    env: Cons(self.fresh(), self.env),
    types: TCons(ty, self.types),
  }
}

///|
/// 以定義擴充語境（let）：變數直接綁定其值。
pub fn Ctx::bind_def(self : Ctx, ty : Val, value : Thunk) -> Ctx {
  {
    lvl: self.lvl + 1,
    env: Cons(value, self.env),
    types: TCons(ty, self.types),
  }
}

///|
pub fn Ctx::type_of_index(self : Ctx, i : Int32) -> Val raise KernelError {
  let mut cur = self.types
  let mut k = i
  while true {
    match cur {
      TNil => raise Unbound(i)
      TCons(v, rest) => {
        if k == 0 {
          return v
        }
        k -= 1
        cur = rest
      }
    }
  }
  raise Unbound(i)
}

///|
/// 核心引擎與遙測計數器。
pub(all) struct Kernel {
  /// β 收縮（函數應用）次數
  mut beta : Int32
  /// ι 收縮（投影、if、rec、J）次數
  mut iota : Int32
  /// ζ 收縮（核心層定義的展開；惰性，定義體至多求值一次）次數
  mut zeta : Int32
  /// 回讀時於中性項上施行的 η 展開次數
  mut eta : Int32
  /// 其中屬於 Unit 類型的 η（中性項回讀為 star；無類型演算法無法施行者）
  mut eta_unit : Int32
  /// 建立的懸置數／實際被強制求值的懸置數／因變數引數而直接共享的次數
  mut thunks : Int32
  mut forced : Int32
  mut shared : Int32
  /// 轉換檢查：無類型快速路徑成功數／退回類型導向 η-長正規形比較數／物理相等捷徑數
  mut conv_fast : Int32
  mut conv_typed : Int32
  mut conv_physical : Int32
}

///|
pub fn Kernel::new() -> Kernel {
  {
    beta: 0,
    iota: 0,
    eta: 0,
    eta_unit: 0,
    thunks: 0,
    forced: 0,
    shared: 0,
    conv_fast: 0,
    conv_typed: 0,
    conv_physical: 0,
    zeta: 0,
  }
}

///|
fn lookup(env : Env, i : Int32) -> Thunk raise KernelError {
  let mut cur = env
  let mut k = i
  while true {
    match cur {
      Nil => raise Unbound(i)
      Cons(th, rest) => {
        if k == 0 {
          return th
        }
        k -= 1
        cur = rest
      }
    }
  }
  raise Unbound(i)
}

///|
/// 懸置：變數直接共享既有懸置，常數直接成值，其餘延後求值。
pub fn Kernel::delay(
  self : Kernel,
  env : Env,
  t : Tm,
) -> Thunk raise KernelError {
  match t {
    Var(i) => {
      self.shared += 1
      lookup(env, i)
    }
    Univ(l) => done(VUniv(l))
    UnitTy => done(VUnitTy)
    Star => done(VStar)
    EmptyTy => done(VEmptyTy)
    BoolTy => done(VBoolTy)
    Tt => done(VTt)
    Ff => done(VFf)
    NatTy => done(VNatTy)
    Zero => done(VZero)
    _ => {
      self.thunks += 1
      { s: Delay(env, t), }
    }
  }
}

///|
/// 強制求值並記憶化（每個懸置至多計算一次）。
pub fn Kernel::force(self : Kernel, th : Thunk) -> Val raise KernelError {
  match th.s {
    Done(v) => v
    Delay(env, t) => {
      let v = self.eval(env, t)
      th.s = Done(v)
      self.forced += 1
      v
    }
    RecIH(c, z, s, pred) => {
      let v = self.natrec(c, z, s, self.force(pred))
      th.s = Done(v)
      self.forced += 1
      v
    }
  }
}

///|
/// 求值至弱頭正規值（執行全部計算規則）。
pub fn Kernel::eval(self : Kernel, env : Env, t : Tm) -> Val raise KernelError {
  match t {
    Var(i) => self.force(lookup(env, i))
    Univ(l) => VUniv(l)
    Pi(a, b) => VPi(self.delay(env, a), { env, body: b, })
    Lam(a, b) => VLam(self.delay(env, a), { env, body: b, })
    App(f, a) => {
      let fv = self.eval(env, f)
      self.apply(fv, self.delay(env, a))
    }
    Sigma(a, b) => VSigma(self.delay(env, a), { env, body: b, })
    Pair(a, b, fam) =>
      VPair(self.delay(env, a), self.delay(env, b), { env, body: fam, })
    Fst(p) => self.vfst(self.eval(env, p))
    Snd(p) => self.vsnd(self.eval(env, p))
    UnitTy => VUnitTy
    Star => VStar
    EmptyTy => VEmptyTy
    Absurd(c, e) =>
      match self.eval(env, e) {
        VNe(n) => VNe(NAbsurd(self.delay(env, c), n))
        _ => raise Stuck("absurd applied to a canonical value")
      }
    BoolTy => VBoolTy
    Tt => VTt
    Ff => VFf
    If(c, s, x, y) =>
      match self.eval(env, s) {
        VTt => {
          self.iota += 1
          self.eval(env, x)
        }
        VFf => {
          self.iota += 1
          self.eval(env, y)
        }
        VNe(n) =>
          VNe(NIf({ env, body: c, }, n, self.delay(env, x), self.delay(env, y)))
        _ => raise Stuck("if on a non-boolean")
      }
    NatTy => VNatTy
    Zero => VZero
    Succ(n) => VSucc(self.delay(env, n))
    NatRec(c, z, s, n) => {
      let nv = self.eval(env, n)
      self.natrec({ env, body: c, }, self.delay(env, z), { env, body: s, }, nv)
    }
    IdTy(a, x, y) =>
      VIdTy(self.delay(env, a), self.delay(env, x), self.delay(env, y))
    Refl(a) => VRefl(self.delay(env, a))
    Let(_, e, b) => {
      self.zeta += 1
      self.eval(Cons(self.delay(env, e), env), b)
    }
    J(c, d, p) =>
      match self.eval(env, p) {
        VRefl(a) => {
          self.iota += 1
          self.eval(Cons(a, env), d)
        }
        VNe(n) => VNe(NJ({ env, body: c, }, { env, body: d, }, n))
        _ => raise Stuck("J on a non-identity proof")
      }
  }
}

///|
/// Π-消除的計算規則（β）。
pub fn Kernel::apply(
  self : Kernel,
  f : Val,
  arg : Thunk,
) -> Val raise KernelError {
  match f {
    VLam(_, c) => {
      self.beta += 1
      self.eval(Cons(arg, c.env), c.body)
    }
    VNe(n) => VNe(NApp(n, arg))
    _ => raise Stuck("application of a non-function")
  }
}

///|
/// 閉包實例化（1 個綁定）。
pub fn Kernel::inst(
  self : Kernel,
  c : Clos,
  arg : Thunk,
) -> Val raise KernelError {
  self.eval(Cons(arg, c.env), c.body)
}

///|
pub fn Kernel::vfst(self : Kernel, p : Val) -> Val raise KernelError {
  match p {
    VPair(a, _, _) => {
      self.iota += 1
      self.force(a)
    }
    VNe(n) => VNe(NFst(n))
    _ => raise Stuck("fst of a non-pair")
  }
}

///|
pub fn Kernel::vsnd(self : Kernel, p : Val) -> Val raise KernelError {
  match p {
    VPair(_, b, _) => {
      self.iota += 1
      self.force(b)
    }
    VNe(n) => VNe(NSnd(n))
    _ => raise Stuck("snd of a non-pair")
  }
}

///|
/// Nat-消除的計算規則；歸納假設為惰性懸置（未被使用則永不計算）。
pub fn Kernel::natrec(
  self : Kernel,
  c : Clos,
  z : Thunk,
  s : Clos,
  n : Val,
) -> Val raise KernelError {
  match n {
    VZero => {
      self.iota += 1
      self.force(z)
    }
    VSucc(pred) => {
      self.iota += 1
      self.thunks += 1
      let ih : Thunk = { s: RecIH(c, z, s, pred), }
      self.eval(Cons(ih, Cons(pred, s.env)), s.body)
    }
    VNe(ne) => VNe(NNatRec(c, z, s, ne))
    _ => raise Stuck("rec on a non-numeral")
  }
}

///|
/// 將族閉包在新鮮變數下回讀為類型。
fn Kernel::quote_fam(
  self : Kernel,
  ctx : Ctx,
  dom : Val,
  c : Clos,
) -> Tm raise KernelError {
  self.quote_ty(ctx.bind(dom), self.inst(c, ctx.fresh()))
}

///|
/// 類型的正規形回讀。
pub fn Kernel::quote_ty(
  self : Kernel,
  ctx : Ctx,
  v : Val,
) -> Tm raise KernelError {
  match v {
    VUniv(l) => Univ(l)
    VPi(a, b) => {
      let av = self.force(a)
      Pi(self.quote_ty(ctx, av), self.quote_fam(ctx, av, b))
    }
    VSigma(a, b) => {
      let av = self.force(a)
      Sigma(self.quote_ty(ctx, av), self.quote_fam(ctx, av, b))
    }
    VUnitTy => UnitTy
    VEmptyTy => EmptyTy
    VBoolTy => BoolTy
    VNatTy => NatTy
    VIdTy(a, x, y) => {
      let av = self.force(a)
      IdTy(
        self.quote_ty(ctx, av),
        self.quote_nf(ctx, av, self.force(x)),
        self.quote_nf(ctx, av, self.force(y)),
      )
    }
    VNe(n) => self.quote_ne(ctx, n).0
    _ => raise Expected("a type", "a non-type canonical value")
  }
}

///|
/// 類型導向回讀：產生 β-正規且 η-長的正規形（唯一性規則在此施行）。
/// Π：一律展開為 λ；Σ：一律展開為 pair；Unit：一律回讀為 star。
pub fn Kernel::quote_nf(
  self : Kernel,
  ctx : Ctx,
  ty : Val,
  v : Val,
) -> Tm raise KernelError {
  match ty {
    VPi(a, b) => {
      let av = self.force(a)
      let x = ctx.fresh()
      if v is VNe(_) {
        self.eta += 1
      }
      let body = self.quote_nf(ctx.bind(av), self.inst(b, x), self.apply(v, x))
      Lam(self.quote_ty(ctx, av), body)
    }
    VSigma(a, b) => {
      let av = self.force(a)
      if v is VNe(_) {
        self.eta += 1
      }
      let first = self.vfst(v)
      let second = self.vsnd(v)
      Pair(
        self.quote_nf(ctx, av, first),
        self.quote_nf(ctx, self.inst(b, done(first)), second),
        self.quote_fam(ctx, av, b),
      )
    }
    VUnitTy => {
      if v is VNe(_) {
        self.eta += 1
        self.eta_unit += 1
      }
      Star
    }
    VUniv(_) => self.quote_ty(ctx, v)
    _ =>
      match v {
        VNe(n) => self.quote_ne(ctx, n).0
        VZero => Zero
        VSucc(n) => Succ(self.quote_nf(ctx, ty, self.force(n)))
        VTt => Tt
        VFf => Ff
        VRefl(a) =>
          match ty {
            VIdTy(dom, _, _) =>
              Refl(self.quote_nf(ctx, self.force(dom), self.force(a)))
            _ => raise Expected("an identity type", "another type for refl")
          }
        _ =>
          raise Expected(
            "a canonical value of a base type", "a mismatched value",
          )
      }
  }
}

///|
/// 中性項回讀，同時合成其類型（供引數的類型導向回讀使用）。
pub fn Kernel::quote_ne(
  self : Kernel,
  ctx : Ctx,
  n : Neu,
) -> (Tm, Val) raise KernelError {
  match n {
    NVar(l) => {
      let i = ctx.lvl - 1 - l
      (Var(i), ctx.type_of_index(i))
    }
    NApp(f, arg) => {
      let (ftm, fty) = self.quote_ne(ctx, f)
      match fty {
        VPi(a, b) =>
          (
            App(ftm, self.quote_nf(ctx, self.force(a), self.force(arg))),
            self.inst(b, arg),
          )
        _ => raise Expected("a Pi type", "another type for a neutral function")
      }
    }
    NFst(p) => {
      let (ptm, pty) = self.quote_ne(ctx, p)
      match pty {
        VSigma(a, _) => (Fst(ptm), self.force(a))
        _ => raise Expected("a Sigma type", "another type for a neutral pair")
      }
    }
    NSnd(p) => {
      let (ptm, pty) = self.quote_ne(ctx, p)
      match pty {
        VSigma(_, b) => (Snd(ptm), self.inst(b, done(VNe(NFst(p)))))
        _ => raise Expected("a Sigma type", "another type for a neutral pair")
      }
    }
    NAbsurd(c, e) => {
      let cv = self.force(c)
      let (etm, _) = self.quote_ne(ctx, e)
      (Absurd(self.quote_ty(ctx, cv), etm), cv)
    }
    NIf(c, s, x, y) => {
      let (stm, _) = self.quote_ne(ctx, s)
      let ctm = self.quote_fam(ctx, VBoolTy, c)
      let xtm = self.quote_nf(ctx, self.inst(c, done(VTt)), self.force(x))
      let ytm = self.quote_nf(ctx, self.inst(c, done(VFf)), self.force(y))
      (If(ctm, stm, xtm, ytm), self.inst(c, done(VNe(s))))
    }
    NNatRec(c, z, s, m) => {
      let (mtm, _) = self.quote_ne(ctx, m)
      let ctm = self.quote_fam(ctx, VNatTy, c)
      let ztm = self.quote_nf(ctx, self.inst(c, done(VZero)), self.force(z))
      let pred = ctx.fresh()
      let ctx1 = ctx.bind(VNatTy)
      let ih = ctx1.fresh()
      let ctx2 = ctx1.bind(self.inst(c, pred))
      let sval = self.eval(Cons(ih, Cons(pred, s.env)), s.body)
      let stm = self.quote_nf(ctx2, self.inst(c, done(VSucc(pred))), sval)
      (NatRec(ctm, ztm, stm, mtm), self.inst(c, done(VNe(m))))
    }
    NJ(c, d, p) => {
      let (ptm, pty) = self.quote_ne(ctx, p)
      match pty {
        VIdTy(dom, a, b) => {
          let av = self.force(dom)
          let x = ctx.fresh()
          let ctx1 = ctx.bind(av)
          let y = ctx1.fresh()
          let ctx2 = ctx1.bind(av)
          let q = ctx2.fresh()
          let ctx3 = ctx2.bind(VIdTy(dom, x, y))
          let ctm = self.quote_ty(
            ctx3,
            self.eval(Cons(q, Cons(y, Cons(x, c.env))), c.body),
          )
          let dval = self.eval(Cons(x, d.env), d.body)
          let dty = self.eval(
            Cons(done(VRefl(x)), Cons(x, Cons(x, c.env))),
            c.body,
          )
          let dtm = self.quote_nf(ctx1, dty, dval)
          let ty = self.eval(
            Cons(done(VNe(p)), Cons(b, Cons(a, c.env))),
            c.body,
          )
          (J(ctm, dtm, ptm), ty)
        }
        _ =>
          raise Expected("an identity type", "another type for a neutral proof")
      }
    }
  }
}

///|
fn fresh_at(lvl : Int32) -> Thunk {
  done(VNe(NVar(lvl)))
}

///|
/// 懸置的轉換：物理相等 ⇒ 不經求值即判同。
fn Kernel::conv_thunk(
  self : Kernel,
  lvl : Int32,
  a : Thunk,
  b : Thunk,
) -> Bool raise KernelError {
  if physical_equal(a, b) {
    self.conv_physical += 1
    return true
  }
  self.conv(lvl, self.force(a), self.force(b))
}

///|
/// 無類型（項導向）轉換檢查：對 Π 與 Σ 以「一側為引入子」觸發 η；
/// 無法處理 Unit 的 η（需類型資訊）——該情形由 `conv_typed` 補足。
pub fn Kernel::conv(
  self : Kernel,
  lvl : Int32,
  a : Val,
  b : Val,
) -> Bool raise KernelError {
  match (a, b) {
    (VNe(n1), VNe(n2)) => self.conv_ne(lvl, n1, n2)
    (VUniv(i), VUniv(j)) => i == j
    (VPi(a1, b1), VPi(a2, b2)) =>
      self.conv_thunk(lvl, a1, a2) && self.conv_clos(lvl, b1, b2)
    (VSigma(a1, b1), VSigma(a2, b2)) =>
      self.conv_thunk(lvl, a1, a2) && self.conv_clos(lvl, b1, b2)
    (VLam(_, c1), VLam(_, c2)) => self.conv_clos(lvl, c1, c2)
    (VLam(_, c1), VNe(n)) => {
      let x = fresh_at(lvl)
      self.conv(lvl + 1, self.inst(c1, x), VNe(NApp(n, x)))
    }
    (VNe(n), VLam(_, c2)) => {
      let x = fresh_at(lvl)
      self.conv(lvl + 1, VNe(NApp(n, x)), self.inst(c2, x))
    }
    (VPair(a1, b1, _), VPair(a2, b2, _)) =>
      self.conv_thunk(lvl, a1, a2) && self.conv_thunk(lvl, b1, b2)
    (VPair(a1, b1, _), VNe(n)) =>
      self.conv(lvl, self.force(a1), VNe(NFst(n))) &&
      self.conv(lvl, self.force(b1), VNe(NSnd(n)))
    (VNe(n), VPair(a2, b2, _)) =>
      self.conv(lvl, VNe(NFst(n)), self.force(a2)) &&
      self.conv(lvl, VNe(NSnd(n)), self.force(b2))
    (VUnitTy, VUnitTy)
    | (VStar, VStar)
    | (VEmptyTy, VEmptyTy)
    | (VBoolTy, VBoolTy)
    | (VTt, VTt)
    | (VFf, VFf)
    | (VNatTy, VNatTy)
    | (VZero, VZero) => true
    (VSucc(x), VSucc(y)) => self.conv_thunk(lvl, x, y)
    (VIdTy(a1, x1, y1), VIdTy(a2, x2, y2)) =>
      self.conv_thunk(lvl, a1, a2) &&
      self.conv_thunk(lvl, x1, x2) &&
      self.conv_thunk(lvl, y1, y2)
    (VRefl(x), VRefl(y)) => self.conv_thunk(lvl, x, y)
    _ => false
  }
}

///|
fn Kernel::conv_clos(
  self : Kernel,
  lvl : Int32,
  c1 : Clos,
  c2 : Clos,
) -> Bool raise KernelError {
  let x = fresh_at(lvl)
  self.conv(lvl + 1, self.inst(c1, x), self.inst(c2, x))
}

///|
fn Kernel::conv_ne(
  self : Kernel,
  lvl : Int32,
  a : Neu,
  b : Neu,
) -> Bool raise KernelError {
  match (a, b) {
    (NVar(i), NVar(j)) => i == j
    (NApp(f1, x1), NApp(f2, x2)) =>
      self.conv_ne(lvl, f1, f2) && self.conv_thunk(lvl, x1, x2)
    (NFst(p1), NFst(p2)) | (NSnd(p1), NSnd(p2)) => self.conv_ne(lvl, p1, p2)
    (NAbsurd(_, e1), NAbsurd(_, e2)) => self.conv_ne(lvl, e1, e2)
    (NIf(c1, s1, x1, y1), NIf(c2, s2, x2, y2)) =>
      self.conv_ne(lvl, s1, s2) &&
      self.conv_clos(lvl, c1, c2) &&
      self.conv_thunk(lvl, x1, x2) &&
      self.conv_thunk(lvl, y1, y2)
    (NNatRec(c1, z1, s1, m1), NNatRec(c2, z2, s2, m2)) => {
      if !(self.conv_ne(lvl, m1, m2) &&
        self.conv_clos(lvl, c1, c2) &&
        self.conv_thunk(lvl, z1, z2)) {
        return false
      }
      let pred = fresh_at(lvl)
      let ih = fresh_at(lvl + 1)
      self.conv(
        lvl + 2,
        self.eval(Cons(ih, Cons(pred, s1.env)), s1.body),
        self.eval(Cons(ih, Cons(pred, s2.env)), s2.body),
      )
    }
    (NJ(c1, d1, p1), NJ(c2, d2, p2)) => {
      if !(self.conv_ne(lvl, p1, p2) && self.conv_clos(lvl, d1, d2)) {
        return false
      }
      let x = fresh_at(lvl)
      let y = fresh_at(lvl + 1)
      let q = fresh_at(lvl + 2)
      self.conv(
        lvl + 3,
        self.eval(Cons(q, Cons(y, Cons(x, c1.env))), c1.body),
        self.eval(Cons(q, Cons(y, Cons(x, c2.env))), c2.body),
      )
    }
    _ => false
  }
}

///|
/// 類型導向轉換：先試無類型快速路徑（健全），失敗才比較 η-長正規形（完備，含 Unit-η）。
pub fn Kernel::conv_typed(
  self : Kernel,
  ctx : Ctx,
  ty : Val,
  a : Val,
  b : Val,
) -> Bool raise KernelError {
  if self.conv(ctx.lvl, a, b) {
    self.conv_fast += 1
    return true
  }
  self.conv_typed += 1
  self.quote_nf(ctx, ty, a) == self.quote_nf(ctx, ty, b)
}

///|
/// 類型的轉換。
pub fn Kernel::conv_ty(
  self : Kernel,
  ctx : Ctx,
  a : Val,
  b : Val,
) -> Bool raise KernelError {
  if self.conv(ctx.lvl, a, b) {
    self.conv_fast += 1
    return true
  }
  self.conv_typed += 1
  self.quote_ty(ctx, a) == self.quote_ty(ctx, b)
}

///|
/// 累積子類型：U_i ≤ U_j（i ≤ j）；Π 於陪域協變、Σ 於兩分量協變。
pub fn Kernel::sub_ty(
  self : Kernel,
  ctx : Ctx,
  a : Val,
  b : Val,
) -> Bool raise KernelError {
  match (a, b) {
    (VUniv(i), VUniv(j)) => i <= j
    (VPi(a1, b1), VPi(a2, b2)) => {
      let av = self.force(a1)
      if !self.conv_ty(ctx, av, self.force(a2)) {
        return false
      }
      let x = ctx.fresh()
      self.sub_ty(ctx.bind(av), self.inst(b1, x), self.inst(b2, x))
    }
    (VSigma(a1, b1), VSigma(a2, b2)) => {
      let av = self.force(a1)
      if !self.sub_ty(ctx, av, self.force(a2)) {
        return false
      }
      let x = ctx.fresh()
      self.sub_ty(ctx.bind(av), self.inst(b1, x), self.inst(b2, x))
    }
    _ => self.conv_ty(ctx, a, b)
  }
}
