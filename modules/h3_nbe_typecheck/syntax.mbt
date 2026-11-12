///|
/// Module H3 — 正規化、類型檢查、證明即程式。
/// 核心語法（Church 式全標註、de Bruijn 指標）。綁定慣例與 H2 相同：
/// Pi/Lam/Sigma 第二欄綁 1；Pair 第三欄（纖維族）綁 1；If 的 C 綁 1；
/// NatRec 的 C 綁 1、s 綁 2（指標 1 = 前驅，0 = 歸納假設）；J 的 C 綁 3、d 綁 1。
#derive(Eq)
pub(all) enum Tm {
  Var(Int32)
  Univ(Int32)
  Pi(Tm, Tm)
  Lam(Tm, Tm)
  App(Tm, Tm)
  Sigma(Tm, Tm)
  Pair(Tm, Tm, Tm)
  Fst(Tm)
  Snd(Tm)
  UnitTy
  Star
  EmptyTy
  Absurd(Tm, Tm)
  BoolTy
  Tt
  Ff
  If(Tm, Tm, Tm, Tm)
  NatTy
  Zero
  Succ(Tm)
  NatRec(Tm, Tm, Tm, Tm)
  IdTy(Tm, Tm, Tm)
  Refl(Tm)
  J(Tm, Tm, Tm)
}

///|
pub extend Tm with Eq::{equal, not_equal}

///|
pub suberror KernelError {
  /// 求值卡住（僅於不良類型項出現）
  Stuck(String)
  Unbound(Int32)
  /// Expected(期望的形式, 實際)
  Expected(String, String)
  /// Mismatch(期望類型, 實際類型, 項)
  Mismatch(String, String, String)
  CannotInfer(String)
  Parse(String)
  Scope(String)
  Fuel(Int32)
}

///|
pub fn KernelError::message(self : KernelError) -> String {
  match self {
    Stuck(s) => "stuck: \{s}"
    Unbound(i) => "unbound index \{i}"
    Expected(w, g) => "expected \{w}, got \{g}"
    Mismatch(e, a, t) => "type mismatch: \{t} has type \{a}, expected \{e}"
    CannotInfer(s) => "cannot infer: \{s}"
    Parse(s) => "parse error: \{s}"
    Scope(s) => "unbound name: \{s}"
    Fuel(n) => "fuel exhausted after \{n} steps"
  }
}

///|
/// 逐子項映射；回呼參數為（子項，該位置綁定的變數個數）。
pub fn map_tm(t : Tm, f : (Tm, Int32) -> Tm) -> Tm {
  match t {
    Var(_)
    | Univ(_)
    | UnitTy
    | Star
    | EmptyTy
    | BoolTy
    | Tt
    | Ff
    | NatTy
    | Zero => t
    Pi(a, b) => Pi(f(a, 0), f(b, 1))
    Lam(a, b) => Lam(f(a, 0), f(b, 1))
    App(g, a) => App(f(g, 0), f(a, 0))
    Sigma(a, b) => Sigma(f(a, 0), f(b, 1))
    Pair(a, b, fam) => Pair(f(a, 0), f(b, 0), f(fam, 1))
    Fst(p) => Fst(f(p, 0))
    Snd(p) => Snd(f(p, 0))
    Absurd(c, e) => Absurd(f(c, 0), f(e, 0))
    If(c, s, x, y) => If(f(c, 1), f(s, 0), f(x, 0), f(y, 0))
    Succ(n) => Succ(f(n, 0))
    NatRec(c, z, s, n) => NatRec(f(c, 1), f(z, 0), f(s, 2), f(n, 0))
    IdTy(a, x, y) => IdTy(f(a, 0), f(x, 0), f(y, 0))
    Refl(a) => Refl(f(a, 0))
    J(c, d, p) => J(f(c, 3), f(d, 1), f(p, 0))
  }
}

///|
/// 位移：≥ c 的自由指標加 d。
pub fn shift_tm(t : Tm, d : Int32, c : Int32) -> Tm {
  match t {
    Var(i) => if i >= c { Var(i + d) } else { t }
    _ => map_tm(t, fn(x, b) { shift_tm(x, d, c + b) })
  }
}

///|
/// 代換 t[s/k]。
pub fn subst_tm(t : Tm, k : Int32, s : Tm) -> Tm {
  match t {
    Var(i) =>
      if i == k {
        shift_tm(s, k, 0)
      } else if i > k {
        Var(i - 1)
      } else {
        t
      }
    _ => map_tm(t, fn(x, b) { subst_tm(x, k + b, s) })
  }
}

///|
pub fn numeral(n : Int32) -> Tm {
  let mut r = Zero
  for _ in 0..<n {
    r = Succ(r)
  }
  r
}

///|
pub fn as_numeral(t : Tm) -> Int32? {
  let mut cur = t
  let mut n = 0
  while true {
    match cur {
      Zero => return Some(n)
      Succ(m) => {
        n += 1
        cur = m
      }
      _ => return None
    }
  }
  None
}

///|
pub fn tm_size(t : Tm) -> Int32 {
  let mut n = 1
  let _ = map_tm(t, fn(x, _b) {
    n += tm_size(x)
    x
  })
  n
}

///|
/// 中性項文法 Ne ::= x | Ne Nf | fst Ne | snd Ne | absurd Ne | if Ne … | rec … Ne | J … Ne
pub fn is_neutral(t : Tm) -> Bool {
  match t {
    Var(_) => true
    App(f, a) => is_neutral(f) && is_normal(a)
    Fst(p) | Snd(p) => is_neutral(p)
    Absurd(c, e) => is_normal(c) && is_neutral(e)
    If(c, s, x, y) =>
      is_normal(c) && is_neutral(s) && is_normal(x) && is_normal(y)
    NatRec(c, z, s, n) =>
      is_normal(c) && is_normal(z) && is_normal(s) && is_neutral(n)
    J(c, d, p) => is_normal(c) && is_normal(d) && is_neutral(p)
    _ => false
  }
}

///|
/// β/ι-正規形文法 Nf ::= Ne | 引入子(Nf…) | 類型形成子(Nf…)：無任何「消除子作用於引入子」。
pub fn is_normal(t : Tm) -> Bool {
  match t {
    Var(_)
    | Univ(_)
    | UnitTy
    | Star
    | EmptyTy
    | BoolTy
    | Tt
    | Ff
    | NatTy
    | Zero => true
    Pi(a, b) | Lam(a, b) | Sigma(a, b) => is_normal(a) && is_normal(b)
    Pair(a, b, fam) => is_normal(a) && is_normal(b) && is_normal(fam)
    Succ(n) | Refl(n) => is_normal(n)
    IdTy(a, x, y) => is_normal(a) && is_normal(x) && is_normal(y)
    _ => is_neutral(t)
  }
}

///|
/// 以具名 S-表達式輸出（綁定變數依深度命名為 x0, x1, …）。
pub fn show_tm(t : Tm) -> String {
  let sb = StringBuilder()
  write_tm(sb, t, 0)
  sb.to_string()
}

///|
/// 在已有 `depth` 個外層綁定的語境下輸出。
pub fn show_tm_at(t : Tm, depth : Int32) -> String {
  let sb = StringBuilder()
  write_tm(sb, t, depth)
  sb.to_string()
}

///|
fn write_tm(sb : StringBuilder, t : Tm, d : Int32) -> Unit {
  match t {
    Var(i) =>
      if i < d {
        sb.write_string("x\{d - 1 - i}")
      } else {
        sb.write_string("?\{i - d}")
      }
    Univ(l) => sb.write_string("U\{l}")
    Pi(a, b) => {
      sb.write_string("(Pi (x\{d} ")
      write_tm(sb, a, d)
      sb.write_string(") ")
      write_tm(sb, b, d + 1)
      sb.write_string(")")
    }
    Lam(a, b) => {
      sb.write_string("(lam (x\{d} ")
      write_tm(sb, a, d)
      sb.write_string(") ")
      write_tm(sb, b, d + 1)
      sb.write_string(")")
    }
    App(_, _) => {
      let args : Array[Tm] = []
      let mut head = t
      while head is App(f, a) {
        args.push(a)
        head = f
      }
      sb.write_string("(")
      write_tm(sb, head, d)
      for i in 0..<args.length() {
        sb.write_string(" ")
        write_tm(sb, args[args.length() - 1 - i], d)
      }
      sb.write_string(")")
    }
    Sigma(a, b) => {
      sb.write_string("(Sigma (x\{d} ")
      write_tm(sb, a, d)
      sb.write_string(") ")
      write_tm(sb, b, d + 1)
      sb.write_string(")")
    }
    Pair(a, b, _) => write_form(sb, "pair", [a, b], d)
    Fst(p) => write_form(sb, "fst", [p], d)
    Snd(p) => write_form(sb, "snd", [p], d)
    UnitTy => sb.write_string("Unit")
    Star => sb.write_string("star")
    EmptyTy => sb.write_string("Empty")
    Absurd(_, e) => write_form(sb, "absurd", [e], d)
    BoolTy => sb.write_string("Bool")
    Tt => sb.write_string("tt")
    Ff => sb.write_string("ff")
    If(c, s, x, y) => {
      sb.write_string("(if-as (x\{d} ")
      write_tm(sb, c, d + 1)
      sb.write_string(")")
      for e in [s, x, y] {
        sb.write_string(" ")
        write_tm(sb, e, d)
      }
      sb.write_string(")")
    }
    NatTy => sb.write_string("Nat")
    Zero => sb.write_string("0")
    Succ(n) =>
      match as_numeral(t) {
        Some(k) => sb.write_string("\{k}")
        None => write_form(sb, "S", [n], d)
      }
    NatRec(c, z, s, n) => {
      sb.write_string("(rec (x\{d} ")
      write_tm(sb, c, d + 1)
      sb.write_string(") ")
      write_tm(sb, z, d)
      sb.write_string(" (x\{d} x\{d + 1} ")
      write_tm(sb, s, d + 2)
      sb.write_string(") ")
      write_tm(sb, n, d)
      sb.write_string(")")
    }
    IdTy(a, x, y) => write_form(sb, "Id", [a, x, y], d)
    Refl(a) => write_form(sb, "refl", [a], d)
    J(c, e, p) => {
      sb.write_string("(J (x\{d} x\{d + 1} x\{d + 2} ")
      write_tm(sb, c, d + 3)
      sb.write_string(") (x\{d} ")
      write_tm(sb, e, d + 1)
      sb.write_string(") ")
      write_tm(sb, p, d)
      sb.write_string(")")
    }
  }
}

///|
fn write_form(
  sb : StringBuilder,
  head : String,
  args : Array[Tm],
  d : Int32,
) -> Unit {
  sb.write_string("(")
  sb.write_string(head)
  for a in args {
    sb.write_string(" ")
    write_tm(sb, a, d)
  }
  sb.write_string(")")
}
