///|
/// 表層語法（具名變數、可省略標註）——由雙向精化轉為全標註核心項。
pub(all) enum Raw {
  SVar(String)
  SUniv(Int32)
  SPi(String, Raw, Raw)
  SLam(String, Raw?, Raw)
  SApp(Raw, Raw)
  SSigma(String, Raw, Raw)
  SPair(Raw, Raw)
  SFst(Raw)
  SSnd(Raw)
  SUnit
  SStar
  SEmpty
  SAbsurd(Raw)
  SBool
  STt
  SFf
  SIf(Raw, Raw, Raw)
  /// SIfAs(x, C, s, t, e)：帶動機的依賴 if
  SIfAs(String, Raw, Raw, Raw, Raw)
  SNat
  SLit(Int32)
  SSucc(Raw)
  /// SRec(x, C, z, m, ih, s, n)
  SRec(String, Raw, Raw, String, String, Raw, Raw)
  SId(Raw, Raw, Raw)
  SRefl
  SReflOf(Raw)
  /// SJ(x, y, q, C, w, d, p)
  SJ(String, String, String, Raw, String, Raw, Raw)
  SThe(Raw, Raw)
  /// SLet(x, T, e, body)
  SLet(String, Raw, Raw, Raw)
}

///|
priv enum Sexp {
  Atom(String)
  List(Array[Sexp])
}

///|
fn tokenize(src : String) -> Array[String] {
  let out : Array[String] = []
  let sb = StringBuilder()
  let mut in_comment = false
  let mut has = false
  for c in src {
    if in_comment {
      if c == '\n' {
        in_comment = false
      }
      continue
    }
    if c == ';' ||
      c == '(' ||
      c == ')' ||
      c == ' ' ||
      c == '\n' ||
      c == '\t' ||
      c == '\r' {
      if has {
        out.push(sb.to_string())
        sb.reset()
        has = false
      }
      if c == ';' {
        in_comment = true
      } else if c == '(' {
        out.push("(")
      } else if c == ')' {
        out.push(")")
      }
    } else {
      sb.write_char(c)
      has = true
    }
  }
  if has {
    out.push(sb.to_string())
  }
  out
}

///|
fn parse_sexps(tokens : Array[String]) -> Array[Sexp] raise KernelError {
  let stack : Array[Array[Sexp]] = [[]]
  for tok in tokens {
    if tok == "(" {
      stack.push([])
    } else if tok == ")" {
      if stack.length() < 2 {
        raise Parse("unbalanced ')'")
      }
      match stack.pop() {
        Some(items) => stack[stack.length() - 1].push(List(items))
        None => raise Parse("unbalanced ')'")
      }
    } else {
      stack[stack.length() - 1].push(Atom(tok))
    }
  }
  if stack.length() != 1 {
    raise Parse("unbalanced '('")
  }
  stack[0]
}

///|
/// 解析自第 `start` 個字元起的十進位自然數（其後不得有其他字元）。
fn parse_nat(s : String, start : Int32) -> Int32? {
  let mut n = 0
  let mut any = false
  let mut pos = 0
  for c in s {
    if pos >= start {
      if c >= '0' && c <= '9' {
        n = n * 10 + (c.to_int() - 48)
        any = true
      } else {
        return None
      }
    }
    pos += 1
  }
  if any {
    Some(n)
  } else {
    None
  }
}

///|
fn atom_to_raw(a : String) -> Raw {
  match a {
    "Unit" => SUnit
    "star" => SStar
    "Empty" => SEmpty
    "Bool" => SBool
    "tt" => STt
    "ff" => SFf
    "Nat" => SNat
    "refl" => SRefl
    _ =>
      match parse_nat(a, 0) {
        Some(n) => SLit(n)
        None =>
          if a.has_prefix("U") {
            match parse_nat(a, 1) {
              Some(l) => SUniv(l)
              None => SVar(a)
            }
          } else {
            SVar(a)
          }
      }
  }
}

///|
/// 解析綁定子 (x A) 為（名稱, 類型）。
fn binder(s : Sexp) -> (String, Raw) raise KernelError {
  match s {
    List([Atom(x), ty]) => (x, to_raw(ty))
    _ => raise Parse("expected a binder of the form (x A)")
  }
}

///|
fn to_raw(s : Sexp) -> Raw raise KernelError {
  match s {
    Atom(a) => atom_to_raw(a)
    List(items) => {
      if items.length() == 0 {
        raise Parse("empty form")
      }
      let n = items.length()
      match items[0] {
        Atom("Pi") => {
          if n < 3 {
            raise Parse("Pi needs binders and a body")
          }
          let mut body = to_raw(items[n - 1])
          for k in 0..<(n - 2) {
            let (x, ty) = binder(items[n - 2 - k])
            body = SPi(x, ty, body)
          }
          body
        }
        Atom("->") => {
          if n < 3 {
            raise Parse("-> needs at least two types")
          }
          let mut body = to_raw(items[n - 1])
          for k in 0..<(n - 2) {
            body = SPi("_", to_raw(items[n - 2 - k]), body)
          }
          body
        }
        Atom("lam") => {
          if n < 3 {
            raise Parse("lam needs binders and a body")
          }
          let mut body = to_raw(items[n - 1])
          for k in 0..<(n - 2) {
            match items[n - 2 - k] {
              Atom(x) => body = SLam(x, None, body)
              b => {
                let (x, ty) = binder(b)
                body = SLam(x, Some(ty), body)
              }
            }
          }
          body
        }
        Atom("Sigma") => {
          if n != 3 {
            raise Parse("Sigma needs one binder and a body")
          }
          let (x, ty) = binder(items[1])
          SSigma(x, ty, to_raw(items[2]))
        }
        Atom("*") if n == 3 => SSigma("_", to_raw(items[1]), to_raw(items[2]))
        Atom("pair") if n == 3 => SPair(to_raw(items[1]), to_raw(items[2]))
        Atom("fst") if n == 2 => SFst(to_raw(items[1]))
        Atom("snd") if n == 2 => SSnd(to_raw(items[1]))
        Atom("absurd") if n == 2 => SAbsurd(to_raw(items[1]))
        Atom("S") if n == 2 => SSucc(to_raw(items[1]))
        Atom("refl") if n == 2 => SReflOf(to_raw(items[1]))
        Atom("the") if n == 3 => SThe(to_raw(items[1]), to_raw(items[2]))
        Atom("if") if n == 4 =>
          SIf(to_raw(items[1]), to_raw(items[2]), to_raw(items[3]))
        Atom("if-as") if n == 5 => {
          let (x, c) = binder(items[1])
          SIfAs(x, c, to_raw(items[2]), to_raw(items[3]), to_raw(items[4]))
        }
        Atom("rec") if n == 5 => {
          let (x, c) = binder(items[1])
          match items[3] {
            List([Atom(m), Atom(ih), step]) =>
              SRec(
                x,
                c,
                to_raw(items[2]),
                m,
                ih,
                to_raw(step),
                to_raw(items[4]),
              )
            _ => raise Parse("rec step must be (m ih body)")
          }
        }
        Atom("Id") if n == 4 =>
          SId(to_raw(items[1]), to_raw(items[2]), to_raw(items[3]))
        Atom("J") if n == 4 =>
          match (items[1], items[2]) {
            (List([Atom(x), Atom(y), Atom(q), c]), List([Atom(w), d])) =>
              SJ(x, y, q, to_raw(c), w, to_raw(d), to_raw(items[3]))
            _ => raise Parse("J must be (J (x y q C) (w d) p)")
          }
        Atom("let") if n == 3 =>
          match items[1] {
            List([Atom(x), ty, e]) =>
              SLet(x, to_raw(ty), to_raw(e), to_raw(items[2]))
            _ => raise Parse("let must be (let (x T e) body)")
          }
        _ => {
          let mut f = to_raw(items[0])
          for k in 1..<n {
            f = SApp(f, to_raw(items[k]))
          }
          f
        }
      }
    }
  }
}

///|
/// 解析程式：零或多個 `(def x T e)` 後接一個最終表達式（定義轉為巢狀 let）。
pub fn parse(src : String) -> Raw raise KernelError {
  let forms = parse_sexps(tokenize(src))
  if forms.length() == 0 {
    raise Parse("empty input")
  }
  let n = forms.length()
  let mut body = to_raw(forms[n - 1])
  for k in 0..<(n - 1) {
    match forms[n - 2 - k] {
      List([Atom("def"), Atom(x), ty, e]) =>
        body = SLet(x, to_raw(ty), to_raw(e), body)
      _ =>
        raise Parse("only (def x T e) forms may precede the final expression")
    }
  }
  body
}

///|
priv enum Names {
  Top
  Name(String, Names)
}

///|
priv struct Scope {
  ctx : Ctx
  names : Names
}

///|
fn Scope::bind(self : Scope, x : String, ty : Val) -> Scope {
  { ctx: self.ctx.bind(ty), names: Name(x, self.names), }
}

///|
fn Scope::find(self : Scope, x : String) -> Int32 raise KernelError {
  let mut cur = self.names
  let mut i = 0
  while true {
    match cur {
      Top => raise Scope(x)
      Name(y, rest) => {
        if y == x {
          return i
        }
        i += 1
        cur = rest
      }
    }
  }
  raise Scope(x)
}

///|
/// 精化結果：全標註核心項、其類型的正規形、以及核心重新檢查所得的推導樹。
pub(all) struct Elaborated {
  term : Tm
  ty : Tm
  deriv : Deriv
}

///|
/// 完整前端管線：解析 → 雙向精化 → 核心獨立重檢（de Bruijn 準則）。
pub fn Kernel::elaborate(
  self : Kernel,
  src : String,
) -> Elaborated raise KernelError {
  let raw = parse(src)
  let sc : Scope = { ctx: Ctx::empty(), names: Top, }
  let (term, _) = self.elab_synth(sc, raw)
  let deriv = self.infer(Ctx::empty(), term)
  { term, ty: self.quote_ty(Ctx::empty(), deriv.ty), deriv, }
}

///|
fn Kernel::elab_type(
  self : Kernel,
  sc : Scope,
  r : Raw,
) -> (Tm, Int32) raise KernelError {
  let (t, ty) = self.elab_synth(sc, r)
  match ty {
    VUniv(l) => (t, l)
    other => raise Expected("a type", self.show_val(sc.ctx, other))
  }
}

///|
/// 檢查模式 Γ ⊢ r ⇐ A：引入形式由期望類型導引（λ、pair、refl 可省略標註）。
fn Kernel::elab_check(
  self : Kernel,
  sc : Scope,
  r : Raw,
  expected : Val,
) -> Tm raise KernelError {
  let ctx = sc.ctx
  match (r, expected) {
    (SLam(x, ann, body), VPi(dom, cod)) => {
      let av = self.force(dom)
      match ann {
        Some(a) => {
          let (atm, _) = self.elab_type(sc, a)
          if !self.conv_ty(ctx, self.eval(ctx.env, atm), av) {
            raise Mismatch(
              self.show_val(ctx, av),
              show_tm_at(atm, ctx.lvl),
              "binder " + x,
            )
          }
        }
        None => ()
      }
      let b = self.elab_check(sc.bind(x, av), body, self.inst(cod, ctx.fresh()))
      Lam(self.quote_ty(ctx, av), b)
    }
    (SPair(a, b), VSigma(dom, fam)) => {
      let av = self.force(dom)
      let atm = self.elab_check(sc, a, av)
      let btm = self.elab_check(sc, b, self.inst(fam, self.delay(ctx.env, atm)))
      Pair(atm, btm, self.quote_fam(ctx, av, fam))
    }
    (SRefl, VIdTy(dom, x, y)) => {
      let av = self.force(dom)
      let xv = self.force(x)
      if !self.conv_typed(ctx, av, xv, self.force(y)) {
        raise Expected(
          "definitionally equal sides for refl",
          self.show_val(ctx, expected),
        )
      }
      Refl(self.quote_nf(ctx, av, xv))
    }
    (SAbsurd(e), _) => {
      let etm = self.elab_check(sc, e, VEmptyTy)
      Absurd(self.quote_ty(ctx, expected), etm)
    }
    (SIf(s, x, y), _) => {
      let stm = self.elab_check(sc, s, VBoolTy)
      let xtm = self.elab_check(sc, x, expected)
      let ytm = self.elab_check(sc, y, expected)
      If(shift_tm(self.quote_ty(ctx, expected), 1, 0), stm, xtm, ytm)
    }
    (SLet(x, ty, e, body), _) => {
      let (ttm, _) = self.elab_type(sc, ty)
      let tv = self.eval(ctx.env, ttm)
      let etm = self.elab_check(sc, e, tv)
      let inner : Scope = {
        ctx: ctx.bind_def(tv, self.delay(ctx.env, etm)),
        names: Name(x, sc.names),
      }
      subst_tm(self.elab_check(inner, body, expected), 0, etm)
    }
    _ => {
      let (t, ty) = self.elab_synth(sc, r)
      if !self.sub_ty(ctx, ty, expected) {
        raise Mismatch(
          self.show_val(ctx, expected),
          self.show_val(ctx, ty),
          show_tm_at(t, ctx.lvl),
        )
      }
      t
    }
  }
}

///|
/// 合成模式 Γ ⊢ r ⇒ A：變數、消除形式與帶標註者可合成類型。
fn Kernel::elab_synth(
  self : Kernel,
  sc : Scope,
  r : Raw,
) -> (Tm, Val) raise KernelError {
  let ctx = sc.ctx
  let env = ctx.env
  match r {
    SVar(x) => {
      let i = sc.find(x)
      (Var(i), ctx.type_of_index(i))
    }
    SUniv(l) => (Univ(l), VUniv(l + 1))
    SPi(x, a, b) => {
      let (atm, la) = self.elab_type(sc, a)
      let (btm, lb) = self.elab_type(sc.bind(x, self.eval(env, atm)), b)
      (Pi(atm, btm), VUniv(max_int(la, lb)))
    }
    SSigma(x, a, b) => {
      let (atm, la) = self.elab_type(sc, a)
      let (btm, lb) = self.elab_type(sc.bind(x, self.eval(env, atm)), b)
      (Sigma(atm, btm), VUniv(max_int(la, lb)))
    }
    SLam(x, Some(a), body) => {
      let (atm, _) = self.elab_type(sc, a)
      let av = self.eval(env, atm)
      let inner = sc.bind(x, av)
      let (btm, bty) = self.elab_synth(inner, body)
      let cod = self.quote_ty(inner.ctx, bty)
      (Lam(atm, btm), VPi(done(av), { env, body: cod, }))
    }
    SLam(x, None, _) => raise CannotInfer("unannotated lambda binding " + x)
    SApp(f, a) => {
      let (ftm, fty) = self.elab_synth(sc, f)
      match fty {
        VPi(dom, cod) => {
          let atm = self.elab_check(sc, a, self.force(dom))
          (App(ftm, atm), self.inst(cod, self.delay(env, atm)))
        }
        other => raise Expected("a function", self.show_val(ctx, other))
      }
    }
    SPair(a, b) => {
      let (atm, aty) = self.elab_synth(sc, a)
      let (btm, bty) = self.elab_synth(sc, b)
      let fam = shift_tm(self.quote_ty(ctx, bty), 1, 0)
      (Pair(atm, btm, fam), VSigma(done(aty), { env, body: fam, }))
    }
    SFst(p) => {
      let (ptm, pty) = self.elab_synth(sc, p)
      match pty {
        VSigma(a, _) => (Fst(ptm), self.force(a))
        other => raise Expected("a pair", self.show_val(ctx, other))
      }
    }
    SSnd(p) => {
      let (ptm, pty) = self.elab_synth(sc, p)
      match pty {
        VSigma(_, b) => (Snd(ptm), self.inst(b, self.delay(env, Fst(ptm))))
        other => raise Expected("a pair", self.show_val(ctx, other))
      }
    }
    SUnit => (UnitTy, VUniv(0))
    SStar => (Star, VUnitTy)
    SEmpty => (EmptyTy, VUniv(0))
    SAbsurd(_) => raise CannotInfer("absurd without an expected type")
    SBool => (BoolTy, VUniv(0))
    STt => (Tt, VBoolTy)
    SFf => (Ff, VBoolTy)
    SIf(s, x, y) => {
      let stm = self.elab_check(sc, s, VBoolTy)
      let (xtm, ty) = self.elab_synth(sc, x)
      let ytm = self.elab_check(sc, y, ty)
      (If(shift_tm(self.quote_ty(ctx, ty), 1, 0), stm, xtm, ytm), ty)
    }
    SIfAs(x, c, s, t, e) => {
      let (ctm, _) = self.elab_type(sc.bind(x, VBoolTy), c)
      let stm = self.elab_check(sc, s, VBoolTy)
      let ttm = self.elab_check(sc, t, self.eval(Cons(done(VTt), env), ctm))
      let etm = self.elab_check(sc, e, self.eval(Cons(done(VFf), env), ctm))
      (If(ctm, stm, ttm, etm), self.eval(Cons(self.delay(env, stm), env), ctm))
    }
    SNat => (NatTy, VUniv(0))
    SLit(n) => (numeral(n), VNatTy)
    SSucc(n) => (Succ(self.elab_check(sc, n, VNatTy)), VNatTy)
    SRec(x, c, z, m, ih, s, n) => {
      let (ctm, _) = self.elab_type(sc.bind(x, VNatTy), c)
      let ztm = self.elab_check(sc, z, self.eval(Cons(done(VZero), env), ctm))
      let pred = ctx.fresh()
      let sc1 = sc.bind(m, VNatTy)
      let sc2 = sc1.bind(ih, self.eval(Cons(pred, env), ctm))
      let stm = self.elab_check(
        sc2,
        s,
        self.eval(Cons(done(VSucc(pred)), env), ctm),
      )
      let ntm = self.elab_check(sc, n, VNatTy)
      (
        NatRec(ctm, ztm, stm, ntm),
        self.eval(Cons(self.delay(env, ntm), env), ctm),
      )
    }
    SId(a, x, y) => {
      let (atm, l) = self.elab_type(sc, a)
      let av = self.eval(env, atm)
      let xtm = self.elab_check(sc, x, av)
      let ytm = self.elab_check(sc, y, av)
      (IdTy(atm, xtm, ytm), VUniv(l))
    }
    SRefl => raise CannotInfer("refl without an expected identity type")
    SReflOf(a) => {
      let (atm, aty) = self.elab_synth(sc, a)
      let th = self.delay(env, atm)
      (Refl(atm), VIdTy(done(aty), th, th))
    }
    SJ(xn, yn, qn, c, wn, d, p) => {
      let (ptm, pty) = self.elab_synth(sc, p)
      match pty {
        VIdTy(dom, a, b) => {
          let av = self.force(dom)
          let x = ctx.fresh()
          let sc1 = sc.bind(xn, av)
          let y = sc1.ctx.fresh()
          let sc2 = sc1.bind(yn, av)
          let sc3 = sc2.bind(qn, VIdTy(dom, x, y))
          let (ctm, _) = self.elab_type(sc3, c)
          let dtm = self.elab_check(
            sc.bind(wn, av),
            d,
            self.eval(Cons(done(VRefl(x)), Cons(x, Cons(x, env))), ctm),
          )
          (
            J(ctm, dtm, ptm),
            self.eval(Cons(self.delay(env, ptm), Cons(b, Cons(a, env))), ctm),
          )
        }
        other => raise Expected("an identity proof", self.show_val(ctx, other))
      }
    }
    SThe(ty, e) => {
      let (ttm, _) = self.elab_type(sc, ty)
      let tv = self.eval(env, ttm)
      (self.elab_check(sc, e, tv), tv)
    }
    SLet(x, ty, e, body) => {
      let (ttm, _) = self.elab_type(sc, ty)
      let tv = self.eval(env, ttm)
      let etm = self.elab_check(sc, e, tv)
      let inner : Scope = {
        ctx: ctx.bind_def(tv, self.delay(env, etm)),
        names: Name(x, sc.names),
      }
      let (btm, bty) = self.elab_synth(inner, body)
      (subst_tm(btm, 0, etm), bty)
    }
  }
}
