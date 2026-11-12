///|
/// Module S7 — 伴隨邏輯（Benton LNL／Reed／Pruiksma–Pfenning／Jang 等的自然演繹）。
///
/// 每個命題有固有的模式 m；模式帶結構性質 σ(m) ⊆ {W（弱化）, C（收縮）}，
/// 並由預序 m ≥ k 規定依賴方向：模式 k 的結論只可依賴模式 ≥ k 的假設（獨立性原理）。
/// 移位 ↑ₖᵐ（k 升至 m）與 ↓ᵐₖ（m 降至 k）構成伴隨 ↓ ⊣ ↑。
pub(all) struct Modes {
  names : Array[String]
  weaken : Array[Bool]
  contract : Array[Bool]
  /// `geq[m][k]` ⇔ m ≥ k（自反傳遞）
  geq : Array[Array[Bool]]
}

///|
/// 由覆蓋關係 `above`（(m, k) 表 m ≥ k）建立模式結構並取自反傳遞閉包。
pub fn Modes::new(
  names : Array[String],
  weaken : Array[Bool],
  contract : Array[Bool],
  above : Array[(Int32, Int32)],
) -> Modes {
  let n = names.length()
  let geq : Array[Array[Bool]] = []
  for i in 0..<n {
    let row = Array::make(n, false)
    row[i] = true
    geq.push(row)
  }
  for pair in above {
    let (m, k) = pair
    geq[m][k] = true
  }
  for mid in 0..<n {
    for a in 0..<n {
      for b in 0..<n {
        if geq[a][mid] && geq[mid][b] {
          geq[a][b] = true
        }
      }
    }
  }
  { names, weaken, contract, geq, }
}

///|
/// 單調性條件：m ≥ k ⇒ σ(m) ⊇ σ(k)（切消除成立的前提）。
pub fn Modes::is_monotone(self : Modes) -> Bool {
  let n = self.names.length()
  for m in 0..<n {
    for k in 0..<n {
      if self.geq[m][k] {
        if self.weaken[k] && !self.weaken[m] {
          return false
        }
        if self.contract[k] && !self.contract[m] {
          return false
        }
      }
    }
  }
  true
}

///|
pub(all) enum Prop {
  Atom(String, Int32)
  /// A ⊸ B（同模式）
  Lolli(Prop, Prop)
  Tensor(Prop, Prop)
  One(Int32)
  With(Prop, Prop)
  Plus(Prop, Prop)
  /// ↑ₖᵐ A：`Up(m, A)`，A 的模式 k ≤ m，結果模式 m
  Up(Int32, Prop)
  /// ↓ᵐₖ A：`Down(k, A)`，A 的模式 m ≥ k，結果模式 k
  Down(Int32, Prop)
}

///|
pub fn prop_equal(a : Prop, b : Prop) -> Bool {
  match (a, b) {
    (Atom(x, m), Atom(y, k)) => x == y && m == k
    (Lolli(a1, b1), Lolli(a2, b2))
    | (Tensor(a1, b1), Tensor(a2, b2))
    | (With(a1, b1), With(a2, b2))
    | (Plus(a1, b1), Plus(a2, b2)) => prop_equal(a1, a2) && prop_equal(b1, b2)
    (One(m), One(k)) => m == k
    (Up(m, x), Up(k, y)) | (Down(m, x), Down(k, y)) =>
      m == k && prop_equal(x, y)
    _ => false
  }
}

///|
pub fn Prop::mode(self : Prop) -> Int32 {
  match self {
    Atom(_, m) | One(m) | Up(m, _) | Down(m, _) => m
    Lolli(a, _) | Tensor(a, _) | With(a, _) | Plus(a, _) => a.mode()
  }
}

///|
pub fn Modes::show_prop(self : Modes, p : Prop) -> String {
  match p {
    Atom(x, m) => x + "_" + self.names[m]
    Lolli(a, b) => "(" + self.show_prop(a) + " ⊸ " + self.show_prop(b) + ")"
    Tensor(a, b) => "(" + self.show_prop(a) + " ⊗ " + self.show_prop(b) + ")"
    One(m) => "1_" + self.names[m]
    With(a, b) => "(" + self.show_prop(a) + " & " + self.show_prop(b) + ")"
    Plus(a, b) => "(" + self.show_prop(a) + " ⊕ " + self.show_prop(b) + ")"
    Up(m, a) => "↑" + self.names[m] + " " + self.show_prop(a)
    Down(k, a) => "↓" + self.names[k] + " " + self.show_prop(a)
  }
}

///|
pub suberror AdjointError {
  Refuse(String)
}

///|
pub fn AdjointError::message(self : AdjointError) -> String {
  match self {
    Refuse(s) => s
  }
}

///|
/// 命題良構：二元連接詞兩側同模式；移位方向符合預序。
pub fn Modes::check_prop(self : Modes, p : Prop) -> Unit raise AdjointError {
  match p {
    Atom(_, _) | One(_) => ()
    Lolli(a, b) | Tensor(a, b) | With(a, b) | Plus(a, b) => {
      self.check_prop(a)
      self.check_prop(b)
      if a.mode() != b.mode() {
        raise Refuse("connective joins different modes: " + self.show_prop(p))
      }
    }
    Up(m, a) => {
      self.check_prop(a)
      if !self.geq[m][a.mode()] {
        raise Refuse("up-shift against the preorder: " + self.show_prop(p))
      }
    }
    Down(k, a) => {
      self.check_prop(a)
      if !self.geq[a.mode()][k] {
        raise Refuse("down-shift against the preorder: " + self.show_prop(p))
      }
    }
  }
}

///|
/// 證明項（de Bruijn 指標）。每個連接詞各有引入與消除形式。
pub(all) enum Tm {
  Var(Int32)
  Lam(Prop, Tm)
  App(Tm, Tm)
  Pair(Tm, Tm)
  /// let (x, y) = e in e'（綁定 2）
  LetPair(Tm, Tm)
  Unit(Int32)
  LetUnit(Tm, Tm)
  WithPair(Tm, Tm)
  Fst(Tm)
  Snd(Tm)
  /// inl（附另一側的命題）
  Inl(Prop, Tm)
  Inr(Prop, Tm)
  /// case e of inl x ⇒ e₁ | inr y ⇒ e₂
  Case(Tm, Tm, Tm)
  /// susp e : ↑ₖᵐ A
  Susp(Int32, Tm)
  Force(Tm)
  /// down e : ↓ᵐₖ A
  Down(Int32, Tm)
  /// let down x = e in e'（綁定 1）
  LetDown(Tm, Tm)
}

///|
/// 檢查器狀態（遙測）。
pub(all) struct Checker {
  modes : Modes
  mut nodes : Int32
  mut independence_checks : Int32
}

///|
pub fn Checker::new(modes : Modes) -> Checker {
  { modes, nodes: 0, independence_checks: 0, }
}

///|
fn add_usage(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<a.length() {
    out.push(a[i] + b[i])
  }
  out
}

///|
/// 加性分支的用量合併：無弱化的變數在兩支中必須同為用或同為不用。
fn Checker::merge_usage(
  self : Checker,
  ctx : Array[Prop],
  a : Array[Int32],
  b : Array[Int32],
) -> Array[Int32] raise AdjointError {
  let out : Array[Int32] = []
  for i in 0..<a.length() {
    let m = ctx[i].mode()
    if !self.modes.weaken[m] && (a[i] > 0) != (b[i] > 0) {
      raise Refuse(
        "additive branches disagree on a variable of mode " +
        self.modes.names[m] +
        " without weakening",
      )
    }
    out.push(if a[i] > b[i] { a[i] } else { b[i] })
  }
  out
}

///|
/// 綁定變數離開作用域：依其模式的結構性質檢查用量，並移除其計數。
fn Checker::close_binder(
  self : Checker,
  p : Prop,
  usage : Array[Int32],
) -> Array[Int32] raise AdjointError {
  let count = usage[usage.length() - 1]
  let m = p.mode()
  if count == 0 && !self.modes.weaken[m] {
    raise Refuse(
      "unused variable of mode " + self.modes.names[m] + " (no weakening)",
    )
  }
  if count > 1 && !self.modes.contract[m] {
    raise Refuse(
      "variable of mode " +
      self.modes.names[m] +
      " used \{count} times (no contraction)",
    )
  }
  let out : Array[Int32] = []
  for i in 0..<(usage.length() - 1) {
    out.push(usage[i])
  }
  out
}

///|
/// 獨立性原理：模式 r 的結論所用的每個假設，模式須 ≥ r。
fn Checker::independence(
  self : Checker,
  ctx : Array[Prop],
  usage : Array[Int32],
  r : Int32,
) -> Unit raise AdjointError {
  self.independence_checks += 1
  for i in 0..<ctx.length() {
    if usage[i] > 0 && !self.modes.geq[ctx[i].mode()][r] {
      raise Refuse(
        "independence violated: a conclusion of mode " +
        self.modes.names[r] +
        " depends on a hypothesis of mode " +
        self.modes.names[ctx[i].mode()],
      )
    }
  }
}

///|
/// 合成類型並回傳各假設的用量（依層級索引）。
pub fn Checker::infer(
  self : Checker,
  ctx : Array[Prop],
  t : Tm,
) -> (Prop, Array[Int32]) raise AdjointError {
  self.nodes += 1
  let n = ctx.length()
  let zero = fn() -> Array[Int32] { Array::make(n, 0) }
  let (p, usage) : (Prop, Array[Int32]) = match t {
    Var(i) => {
      if i < 0 || i >= n {
        raise Refuse("unbound variable #\{i}")
      }
      let u = zero()
      u[n - 1 - i] = 1
      (ctx[n - 1 - i], u)
    }
    Lam(a, body) => {
      self.modes.check_prop(a)
      let inner = ctx.copy()
      inner.push(a)
      let (b, u) = self.infer(inner, body)
      if b.mode() != a.mode() {
        raise Refuse("function body changes mode")
      }
      (Lolli(a, b), self.close_binder(a, u))
    }
    App(f, x) => {
      let (fp, uf) = self.infer(ctx, f)
      match fp {
        Lolli(a, b) => {
          let (xp, ux) = self.infer(ctx, x)
          if !prop_equal(a, xp) {
            raise Refuse(
              "argument mismatch: expected " +
              self.modes.show_prop(a) +
              ", got " +
              self.modes.show_prop(xp),
            )
          }
          (b, add_usage(uf, ux))
        }
        _ => raise Refuse("application of a non-function")
      }
    }
    Pair(a, b) => {
      let (pa, ua) = self.infer(ctx, a)
      let (pb, ub) = self.infer(ctx, b)
      if pa.mode() != pb.mode() {
        raise Refuse("tensor joins different modes")
      }
      (Tensor(pa, pb), add_usage(ua, ub))
    }
    LetPair(e, body) => {
      let (pe, ue) = self.infer(ctx, e)
      match pe {
        Tensor(a, b) => {
          let inner = ctx.copy()
          inner.push(a)
          inner.push(b)
          let (c, u) = self.infer(inner, body)
          let u1 = self.close_binder(b, u)
          let u2 = self.close_binder(a, u1)
          self.elim_mode(pe, c)
          (c, add_usage(ue, u2))
        }
        _ => raise Refuse("let-pair of a non-tensor")
      }
    }
    Unit(m) => (One(m), zero())
    LetUnit(e, body) => {
      let (pe, ue) = self.infer(ctx, e)
      match pe {
        One(_) => {
          let (c, u) = self.infer(ctx, body)
          self.elim_mode(pe, c)
          (c, add_usage(ue, u))
        }
        _ => raise Refuse("let-unit of a non-unit")
      }
    }
    WithPair(a, b) => {
      let (pa, ua) = self.infer(ctx, a)
      let (pb, ub) = self.infer(ctx, b)
      if pa.mode() != pb.mode() {
        raise Refuse("with joins different modes")
      }
      (With(pa, pb), self.merge_usage(ctx, ua, ub))
    }
    Fst(e) => {
      let (pe, ue) = self.infer(ctx, e)
      match pe {
        With(a, _) => (a, ue)
        _ => raise Refuse("fst of a non-with")
      }
    }
    Snd(e) => {
      let (pe, ue) = self.infer(ctx, e)
      match pe {
        With(_, b) => (b, ue)
        _ => raise Refuse("snd of a non-with")
      }
    }
    Inl(other, e) => {
      let (pe, ue) = self.infer(ctx, e)
      self.modes.check_prop(other)
      if other.mode() != pe.mode() {
        raise Refuse("plus joins different modes")
      }
      (Plus(pe, other), ue)
    }
    Inr(other, e) => {
      let (pe, ue) = self.infer(ctx, e)
      self.modes.check_prop(other)
      if other.mode() != pe.mode() {
        raise Refuse("plus joins different modes")
      }
      (Plus(other, pe), ue)
    }
    Case(e, l, r) => {
      let (pe, ue) = self.infer(ctx, e)
      match pe {
        Plus(a, b) => {
          let cl = ctx.copy()
          cl.push(a)
          let (c1, u1) = self.infer(cl, l)
          let cr = ctx.copy()
          cr.push(b)
          let (c2, u2) = self.infer(cr, r)
          if !prop_equal(c1, c2) {
            raise Refuse("case branches have different types")
          }
          let m = self.merge_usage(
            ctx,
            self.close_binder(a, u1),
            self.close_binder(b, u2),
          )
          self.elim_mode(pe, c1)
          (c1, add_usage(ue, m))
        }
        _ => raise Refuse("case of a non-plus")
      }
    }
    Susp(m, e) => {
      let (pe, ue) = self.infer(ctx, e)
      let p = Up(m, pe)
      self.modes.check_prop(p)
      (p, ue)
    }
    Force(e) => {
      let (pe, ue) = self.infer(ctx, e)
      match pe {
        Up(_, a) => (a, ue)
        _ => raise Refuse("force of a non-up-shift")
      }
    }
    Down(k, e) => {
      let (pe, ue) = self.infer(ctx, e)
      let p = Prop::Down(k, pe)
      self.modes.check_prop(p)
      (p, ue)
    }
    LetDown(e, body) => {
      let (pe, ue) = self.infer(ctx, e)
      match pe {
        Down(_, a) => {
          let inner = ctx.copy()
          inner.push(a)
          let (c, u) = self.infer(inner, body)
          self.elim_mode(pe, c)
          (c, add_usage(ue, self.close_binder(a, u)))
        }
        _ => raise Refuse("let-down of a non-down-shift")
      }
    }
  }
  self.independence(ctx, usage, p.mode())
  (p, usage)
}

///|
/// 正式消除規則的模式條件：被消除者的模式 ≥ 結論的模式。
fn Checker::elim_mode(
  self : Checker,
  scrutinee : Prop,
  conclusion : Prop,
) -> Unit raise AdjointError {
  if !self.modes.geq[scrutinee.mode()][conclusion.mode()] {
    raise Refuse("elimination into a mode not below the eliminated proposition")
  }
}

///|
/// 閉證明項是否證明命題 `goal`。回傳（是否接受, 類型或拒絕原因）。
pub fn Checker::proves(self : Checker, t : Tm, goal : Prop) -> (Bool, String) {
  try self.infer([], t) catch {
    err => (false, err.message())
  } noraise {
    (p, _) =>
      if prop_equal(p, goal) {
        (true, self.modes.show_prop(p))
      } else {
        (false, "proves " + self.modes.show_prop(p) + " instead")
      }
  }
}
