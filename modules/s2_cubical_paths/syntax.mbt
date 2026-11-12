///|
/// Module S2 — 路徑類型（建立於 S1 的德摩根區間之上）。
///
/// 項變數用 de Bruijn 指標；維度（區間）變數用語法名字（0..14），
/// 區間項即 S1 的 `Dm` 正規形。
pub(all) enum Ty {
  /// 基礎類型
  TBase(String)
  /// Π(x : A). B —— B 綁定一個項變數
  TPi(Ty, Ty)
  /// PathP (i. A) a b —— A 綁定維度名 i；a : A[0/i]，b : A[1/i]
  TPathP(Int32, Ty, Tm, Tm)
}

///|
pub(all) enum Tm {
  Var(Int32)
  Const(String)
  Lam(Tm)
  App(Tm, Tm)
  /// 路徑抽象 ⟨i⟩ t
  PLam(Int32, Tm)
  /// 路徑應用 p @ r
  PApp(Tm, @s1.Dm)
  Ann(Tm, Ty)
}

///|
pub suberror CubicalError {
  Ill(String)
}

///|
pub fn CubicalError::message(self : CubicalError) -> String {
  match self {
    Ill(s) => s
  }
}

///|
pub fn tm_equal(a : Tm, b : Tm) -> Bool {
  match (a, b) {
    (Var(i), Var(j)) => i == j
    (Const(x), Const(y)) => x == y
    (Lam(x), Lam(y)) => tm_equal(x, y)
    (App(f, x), App(g, y)) => tm_equal(f, g) && tm_equal(x, y)
    (PLam(i, x), PLam(j, y)) => i == j && tm_equal(x, y)
    (PApp(p, r), PApp(q, s)) => tm_equal(p, q) && r.same(s)
    (Ann(x, s), Ann(y, t)) => tm_equal(x, y) && ty_equal(s, t)
    _ => false
  }
}

///|
pub fn ty_equal(a : Ty, b : Ty) -> Bool {
  match (a, b) {
    (TBase(x), TBase(y)) => x == y
    (TPi(a1, b1), TPi(a2, b2)) => ty_equal(a1, a2) && ty_equal(b1, b2)
    (TPathP(i, a1, l1, r1), TPathP(j, a2, l2, r2)) =>
      i == j && ty_equal(a1, a2) && tm_equal(l1, l2) && tm_equal(r1, r2)
    _ => false
  }
}

///|
pub fn show_tm(t : Tm) -> String {
  match t {
    Var(i) => "#\{i}"
    Const(c) => c
    Lam(b) => "(λ " + show_tm(b) + ")"
    App(f, a) => "(" + show_tm(f) + " " + show_tm(a) + ")"
    PLam(i, b) => "⟨i\{i}⟩ " + show_tm(b)
    PApp(p, r) => "(" + show_tm(p) + " @ " + r.show() + ")"
    Ann(x, _) => show_tm(x)
  }
}

///|
pub fn show_ty(t : Ty) -> String {
  match t {
    TBase(s) => s
    TPi(a, b) => "(Π " + show_ty(a) + ". " + show_ty(b) + ")"
    TPathP(i, a, l, r) =>
      "(PathP i\{i}." + show_ty(a) + " " + show_tm(l) + " " + show_tm(r) + ")"
  }
}

///|
/// 非相依路徑類型 Path A a b（維度名 `fresh` 不出現於 A）。
pub fn path_ty(fresh : Int32, a : Ty, l : Tm, r : Tm) -> Ty {
  TPathP(fresh, a, l, r)
}

///|
pub fn dim(i : Int32) -> @s1.Dm {
  @s1.Dm::name(i)
}

///|
/// refl a = ⟨i⟩ a
pub fn refl(i : Int32, a : Tm) -> Tm {
  PLam(i, a)
}

///|
/// sym p = ⟨i⟩ p @ ¬i
pub fn sym(i : Int32, p : Tm) -> Tm {
  PLam(i, PApp(p, @s1.Dm::co_name(i)))
}

///|
/// ap f p = ⟨i⟩ f (p @ i)
pub fn ap(i : Int32, f : Tm, p : Tm) -> Tm {
  PLam(i, App(f, PApp(p, dim(i))))
}

///|
/// funext h = ⟨i⟩ λx. h x @ i（`h` 須為閉項或常數，免位移）
pub fn funext(i : Int32, h : Tm) -> Tm {
  PLam(i, Lam(PApp(App(h, Var(0)), dim(i))))
}

///|
/// happly q = λx. ⟨i⟩ q @ i x
pub fn happly(i : Int32, q : Tm) -> Tm {
  Lam(PLam(i, App(PApp(q, dim(i)), Var(0))))
}

///|
/// 連接方塊 ⟨i⟩⟨j⟩ p @ (i ∧ j) 或 p @ (i ∨ j)
pub fn connection_square(i : Int32, j : Int32, p : Tm, meet~ : Bool) -> Tm {
  let r = if meet { dim(i).meet(dim(j)) } else { dim(i).join(dim(j)) }
  PLam(i, PLam(j, PApp(p, r)))
}
