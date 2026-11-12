///|
pub(all) enum TEnv {
  TNil
  TCons(Val, TEnv)
}

///|
pub(all) enum DEnv {
  DNil
  DCons(Int32, @s1.Dm, DEnv)
}

///|
pub(all) struct Env {
  tms : TEnv
  dims : DEnv
}

///|
pub(all) enum Val {
  VLam(Env, Tm)
  VPLam(Env, Int32, Tm)
  VNe(Neu)
}

///|
/// 中性項；頭部攜帶類型，使路徑應用於端點處可由類型算出邊界。
pub(all) enum Neu {
  NVar(Int32, VTy)
  NConst(String, VTy)
  NApp(Neu, Val)
  NPApp(Neu, @s1.Dm)
}

///|
pub(all) enum VTy {
  VBase(String)
  VPi(VTy, Env, Ty)
  VPathP(Env, Int32, Ty, Val, Val)
}

///|
pub fn Env::empty() -> Env {
  { tms: TNil, dims: DNil, }
}

///|
pub fn Env::push(self : Env, v : Val) -> Env {
  { tms: TCons(v, self.tms), dims: self.dims, }
}

///|
pub fn Env::bind_dim(self : Env, name : Int32, r : @s1.Dm) -> Env {
  { tms: self.tms, dims: DCons(name, r, self.dims), }
}

///|
fn Env::lookup_dim(self : Env, name : Int32) -> @s1.Dm? {
  let mut d = self.dims
  while true {
    match d {
      DNil => return None
      DCons(n, r, rest) => {
        if n == name {
          return Some(r)
        }
        d = rest
      }
    }
  }
  None
}

///|
/// 理論：基礎類型與常數（含高維生成元，如圓的 loop、球面的 surf）的簽名，
/// 並統計 NbE 的計算步數。
pub(all) struct Theory {
  bases : Map[String, Bool]
  consts : Map[String, VTy]
  mut beta : Int32
  mut path_beta : Int32
  mut boundary : Int32
  mut eta : Int32
  mut path_eta : Int32
}

///|
pub fn Theory::new() -> Theory {
  {
    bases: Map([]),
    consts: Map([]),
    beta: 0,
    path_beta: 0,
    boundary: 0,
    eta: 0,
    path_eta: 0,
  }
}

///|
/// 區間項於維度環境下求值（代換為德摩根同態，結果仍為正規形）。
pub fn Theory::eval_dim(_self : Theory, env : Env, r : @s1.Dm) -> @s1.Dm {
  r.subst(fn(n) {
    match env.lookup_dim(n) {
      Some(x) => x
      None => @s1.Dm::name(n)
    }
  })
}

///|
pub fn Theory::eval(self : Theory, env : Env, t : Tm) -> Val raise CubicalError {
  match t {
    Var(i) => {
      let mut e = env.tms
      let mut k = i
      while true {
        match e {
          TNil => raise Ill("unbound variable #\{i}")
          TCons(v, rest) => {
            if k == 0 {
              return v
            }
            k -= 1
            e = rest
          }
        }
      }
      raise Ill("unbound variable #\{i}")
    }
    Const(c) =>
      match self.consts.get(c) {
        Some(ty) => VNe(NConst(c, ty))
        None => raise Ill("undeclared constant " + c)
      }
    Lam(_) => VLam(env, t)
    App(f, a) => self.apply(self.eval(env, f), self.eval(env, a))
    PLam(n, b) => VPLam(env, n, b)
    PApp(p, r) => self.papp(self.eval(env, p), self.eval_dim(env, r))
    Ann(x, _) => self.eval(env, x)
  }
}

///|
/// 函數的計算規則（β）。
pub fn Theory::apply(self : Theory, f : Val, a : Val) -> Val raise CubicalError {
  match f {
    VLam(env, Lam(b)) => {
      self.beta += 1
      self.eval(env.push(a), b)
    }
    VNe(n) => VNe(NApp(n, a))
    _ => raise Ill("application of a non-function")
  }
}

///|
/// 路徑的計算規則：(⟨i⟩ t) @ r ▷ t[r/i]；中性路徑於端點 0/1 化為其類型記載的邊界。
pub fn Theory::papp(
  self : Theory,
  p : Val,
  r : @s1.Dm,
) -> Val raise CubicalError {
  match p {
    VPLam(env, n, b) => {
      self.path_beta += 1
      self.eval(env.bind_dim(n, r), b)
    }
    VNe(n) =>
      if r.is_zero() || r.is_one() {
        match self.type_of_neu(n) {
          VPathP(_, _, _, l, rt) => {
            self.boundary += 1
            if r.is_zero() {
              l
            } else {
              rt
            }
          }
          _ => raise Ill("path application of a non-path")
        }
      } else {
        VNe(NPApp(n, r))
      }
    _ => raise Ill("path application of a non-path")
  }
}

///|
pub fn Theory::eval_ty(
  self : Theory,
  env : Env,
  t : Ty,
) -> VTy raise CubicalError {
  match t {
    TBase(s) => VBase(s)
    TPi(a, b) => VPi(self.eval_ty(env, a), env, b)
    TPathP(n, a, l, r) =>
      VPathP(env, n, a, self.eval(env, l), self.eval(env, r))
  }
}

///|
pub fn Theory::type_of_neu(self : Theory, n : Neu) -> VTy raise CubicalError {
  match n {
    NVar(_, t) | NConst(_, t) => t
    NApp(f, a) =>
      match self.type_of_neu(f) {
        VPi(_, env, cod) => self.eval_ty(env.push(a), cod)
        _ => raise Ill("neutral application of a non-function")
      }
    NPApp(p, r) =>
      match self.type_of_neu(p) {
        VPathP(env, name, a, _, _) => self.eval_ty(env.bind_dim(name, r), a)
        _ => raise Ill("neutral path application of a non-path")
      }
  }
}

///|
/// 類型導向回讀：於 Π 與 PathP 處作 η 展開（唯一性規則），輸出 η-長正規形。
/// `lvl`／`dlvl` 為項／維度的新鮮層級；回讀的維度名即層級，故正規形與綁定名無關。
pub fn Theory::readback(
  self : Theory,
  lvl : Int32,
  dlvl : Int32,
  ty : VTy,
  v : Val,
) -> Tm raise CubicalError {
  match ty {
    VPi(a, env, cod) => {
      let x = VNe(NVar(lvl, a))
      self.eta += 1
      Lam(
        self.readback(
          lvl + 1,
          dlvl,
          self.eval_ty(env.push(x), cod),
          self.apply(v, x),
        ),
      )
    }
    VPathP(env, n, a, _, _) => {
      if dlvl >= @s1.MAX_NAMES {
        raise Ill("dimension depth exceeds the interval name capacity")
      }
      let r = @s1.Dm::name(dlvl)
      self.path_eta += 1
      PLam(
        dlvl,
        self.readback(
          lvl,
          dlvl + 1,
          self.eval_ty(env.bind_dim(n, r), a),
          self.papp(v, r),
        ),
      )
    }
    VBase(_) =>
      match v {
        VNe(n) => self.readback_neu(lvl, dlvl, n)
        _ => raise Ill("non-neutral value at a base type")
      }
  }
}

///|
pub fn Theory::readback_neu(
  self : Theory,
  lvl : Int32,
  dlvl : Int32,
  n : Neu,
) -> Tm raise CubicalError {
  match n {
    NVar(l, _) => Var(lvl - l - 1)
    NConst(c, _) => Const(c)
    NApp(f, a) =>
      match self.type_of_neu(f) {
        VPi(dom, _, _) =>
          App(self.readback_neu(lvl, dlvl, f), self.readback(lvl, dlvl, dom, a))
        _ => raise Ill("neutral application of a non-function")
      }
    NPApp(p, r) => PApp(self.readback_neu(lvl, dlvl, p), r)
  }
}

///|
pub fn Theory::readback_ty(
  self : Theory,
  lvl : Int32,
  dlvl : Int32,
  ty : VTy,
) -> Ty raise CubicalError {
  match ty {
    VBase(s) => TBase(s)
    VPi(a, env, cod) => {
      let x = VNe(NVar(lvl, a))
      TPi(
        self.readback_ty(lvl, dlvl, a),
        self.readback_ty(lvl + 1, dlvl, self.eval_ty(env.push(x), cod)),
      )
    }
    VPathP(env, n, a, l, r) => {
      let fresh = @s1.Dm::name(dlvl)
      let a0 = self.eval_ty(env.bind_dim(n, @s1.Dm::zero()), a)
      let a1 = self.eval_ty(env.bind_dim(n, @s1.Dm::one()), a)
      TPathP(
        dlvl,
        self.readback_ty(lvl, dlvl + 1, self.eval_ty(env.bind_dim(n, fresh), a)),
        self.readback(lvl, dlvl, a0, l),
        self.readback(lvl, dlvl, a1, r),
      )
    }
  }
}

///|
/// 判定性相等（可判定）：比較 η-長正規形。
pub fn Theory::conv(
  self : Theory,
  lvl : Int32,
  dlvl : Int32,
  ty : VTy,
  a : Val,
  b : Val,
) -> Bool raise CubicalError {
  tm_equal(self.readback(lvl, dlvl, ty, a), self.readback(lvl, dlvl, ty, b))
}

///|
pub fn Theory::conv_ty(
  self : Theory,
  lvl : Int32,
  dlvl : Int32,
  a : VTy,
  b : VTy,
) -> Bool raise CubicalError {
  ty_equal(self.readback_ty(lvl, dlvl, a), self.readback_ty(lvl, dlvl, b))
}
