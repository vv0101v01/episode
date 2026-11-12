///|
pub(all) struct Ctx {
  lvl : Int32
  dlvl : Int32
  env : Env
  /// 依層級索引的項變數類型
  types : Array[VTy]
}

///|
pub fn Ctx::empty() -> Ctx {
  { lvl: 0, dlvl: 0, env: Env::empty(), types: [], }
}

///|
pub fn Ctx::bind(self : Ctx, ty : VTy) -> Ctx {
  let types = self.types.copy()
  types.push(ty)
  {
    lvl: self.lvl + 1,
    dlvl: self.dlvl,
    env: self.env.push(VNe(NVar(self.lvl, ty))),
    types,
  }
}

///|
/// 綁定語法維度名 `name` 為新鮮維度層級。
pub fn Ctx::bind_dim(self : Ctx, name : Int32) -> Ctx raise CubicalError {
  if self.dlvl >= @s1.MAX_NAMES || name >= @s1.MAX_NAMES || name < 0 {
    raise Ill("dimension name out of range")
  }
  {
    lvl: self.lvl,
    dlvl: self.dlvl + 1,
    env: self.env.bind_dim(name, @s1.Dm::name(self.dlvl)),
    types: self.types,
  }
}

///|
fn Theory::check_dim_scope(
  _self : Theory,
  ctx : Ctx,
  r : @s1.Dm,
) -> Unit raise CubicalError {
  let s = r.support()
  for n in 0..<@s1.MAX_NAMES {
    if ((s >> n) & 1) == 1 && ctx.env.lookup_dim(n) is None {
      raise Ill("unbound dimension i\{n}")
    }
  }
}

///|
/// 類型形成規則。
pub fn Theory::check_ty(
  self : Theory,
  ctx : Ctx,
  t : Ty,
) -> Unit raise CubicalError {
  match t {
    TBase(s) =>
      if !self.bases.contains(s) {
        raise Ill("unknown base type " + s)
      }
    TPi(a, b) => {
      self.check_ty(ctx, a)
      self.check_ty(ctx.bind(self.eval_ty(ctx.env, a)), b)
    }
    TPathP(n, a, l, r) => {
      self.check_ty(ctx.bind_dim(n), a)
      let a0 = self.eval_ty(ctx.env.bind_dim(n, @s1.Dm::zero()), a)
      let a1 = self.eval_ty(ctx.env.bind_dim(n, @s1.Dm::one()), a)
      self.check(ctx, l, a0)
      self.check(ctx, r, a1)
    }
  }
}

///|
/// 合成類型（消除規則）。
pub fn Theory::infer(
  self : Theory,
  ctx : Ctx,
  t : Tm,
) -> VTy raise CubicalError {
  match t {
    Var(i) =>
      if i < 0 || i >= ctx.lvl {
        raise Ill("unbound variable #\{i}")
      } else {
        ctx.types[ctx.lvl - i - 1]
      }
    Const(c) =>
      match self.consts.get(c) {
        Some(ty) => ty
        None => raise Ill("undeclared constant " + c)
      }
    App(f, a) =>
      match self.infer(ctx, f) {
        VPi(dom, env, cod) => {
          self.check(ctx, a, dom)
          self.eval_ty(env.push(self.eval(ctx.env, a)), cod)
        }
        _ => raise Ill("application of a non-function: " + show_tm(f))
      }
    PApp(p, r) =>
      match self.infer(ctx, p) {
        VPathP(env, n, a, _, _) => {
          self.check_dim_scope(ctx, r)
          self.eval_ty(env.bind_dim(n, self.eval_dim(ctx.env, r)), a)
        }
        _ => raise Ill("path application of a non-path: " + show_tm(p))
      }
    Ann(x, ty) => {
      self.check_ty(ctx, ty)
      let v = self.eval_ty(ctx.env, ty)
      self.check(ctx, x, v)
      v
    }
    Lam(_) | PLam(_, _) =>
      raise Ill("cannot infer an abstraction: " + show_tm(t))
  }
}

///|
/// 檢查類型（引入規則）。路徑抽象除檢查主體外，還要驗證兩端邊界與類型記載者判定性相等。
pub fn Theory::check(
  self : Theory,
  ctx : Ctx,
  t : Tm,
  ty : VTy,
) -> Unit raise CubicalError {
  match (t, ty) {
    (Lam(b), VPi(a, env, cod)) => {
      let inner = ctx.bind(a)
      let x = VNe(NVar(ctx.lvl, a))
      self.check(inner, b, self.eval_ty(env.push(x), cod))
    }
    (PLam(n, b), VPathP(env, m, a, l, r)) => {
      let inner = ctx.bind_dim(n)
      let fresh = @s1.Dm::name(ctx.dlvl)
      self.check(inner, b, self.eval_ty(env.bind_dim(m, fresh), a))
      let zero = @s1.Dm::zero()
      let one = @s1.Dm::one()
      let v0 = self.eval(ctx.env.bind_dim(n, zero), b)
      let v1 = self.eval(ctx.env.bind_dim(n, one), b)
      let a0 = self.eval_ty(env.bind_dim(m, zero), a)
      let a1 = self.eval_ty(env.bind_dim(m, one), a)
      if !self.conv(ctx.lvl, ctx.dlvl, a0, v0, l) {
        raise Ill(
          "left endpoint mismatch: " +
          show_tm(self.readback(ctx.lvl, ctx.dlvl, a0, v0)) +
          " vs " +
          show_tm(self.readback(ctx.lvl, ctx.dlvl, a0, l)),
        )
      }
      if !self.conv(ctx.lvl, ctx.dlvl, a1, v1, r) {
        raise Ill(
          "right endpoint mismatch: " +
          show_tm(self.readback(ctx.lvl, ctx.dlvl, a1, v1)) +
          " vs " +
          show_tm(self.readback(ctx.lvl, ctx.dlvl, a1, r)),
        )
      }
    }
    _ => {
      let got = self.infer(ctx, t)
      if !self.conv_ty(ctx.lvl, ctx.dlvl, got, ty) {
        raise Ill(
          "type mismatch: " +
          show_tm(t) +
          " has type " +
          show_ty(self.readback_ty(ctx.lvl, ctx.dlvl, got)) +
          ", expected " +
          show_ty(self.readback_ty(ctx.lvl, ctx.dlvl, ty)),
        )
      }
    }
  }
}

///|
pub fn Theory::declare_base(self : Theory, name : String) -> Unit {
  self.bases[name] = true
}

///|
/// 宣告常數（點、路徑或高維生成元）；類型須為閉且良構。
pub fn Theory::add_const(
  self : Theory,
  name : String,
  ty : Ty,
) -> Unit raise CubicalError {
  self.check_ty(Ctx::empty(), ty)
  self.consts[name] = self.eval_ty(Env::empty(), ty)
}

///|
/// 閉項於閉類型下的 η-長正規形。
pub fn Theory::normalize(
  self : Theory,
  t : Tm,
  ty : Ty,
) -> Tm raise CubicalError {
  let ctx = Ctx::empty()
  self.check_ty(ctx, ty)
  let v = self.eval_ty(ctx.env, ty)
  self.check(ctx, t, v)
  self.readback(0, 0, v, self.eval(ctx.env, t))
}

///|
/// 判定：閉項 a ≡ b : ty（兩者皆先通過類型檢查）。
pub fn Theory::definitionally_equal(
  self : Theory,
  a : Tm,
  b : Tm,
  ty : Ty,
) -> Bool raise CubicalError {
  tm_equal(self.normalize(a, ty), self.normalize(b, ty))
}

///|
/// 是否通過類型檢查（把錯誤轉為 false 與訊息）。
pub fn Theory::accepts(self : Theory, t : Tm, ty : Ty) -> (Bool, String) {
  try self.normalize(t, ty) catch {
    err => (false, err.message())
  } noraise {
    nf => (true, show_tm(nf))
  }
}
