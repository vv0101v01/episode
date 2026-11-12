///|
/// Module S8 — 符號動態執行與 NbE 的整合。
///
/// NbE 於開項上求值時，卡在符號變數上的消除子（中性項）恰好標示出「下一個要分歧的輸入」：
///   if 卡在 Bool 變數 ⇒ 路徑條件分為 x = tt / x = ff；
///   rec 卡在 Nat 變數 ⇒ 分為 x = 0 / x = S k（附歸納假設）。
/// 執行樹的每個葉子再由 NbE 判定等式；整棵樹編譯為消除子證明項，交回 H3 核心重檢。
/// 於是正類型（Bool、Nat）缺少的定義性 η，由符號執行自動補成命題性證明。
pub(all) enum SymTree {
  /// 葉：此路徑上的 η-長正規形
  Leaf(@h3.Tm)
  /// 於變數（de Bruijn 指標）上的布林分歧：(tt 支, ff 支)
  BoolSplit(Int32, SymTree, SymTree)
  /// 於自然數變數上的分歧：(零支, 後繼支——後繼支中該變數代表前驅)
  NatSplit(Int32, SymTree, SymTree)
  /// 展開深度用盡
  Cutoff(@h3.Tm)
}

///|
/// 把自由變數 i 取代為 s（不移除該變數；s 活在同一上下文）。
pub fn replace_var(t : @h3.Tm, i : Int32, s : @h3.Tm) -> @h3.Tm {
  match t {
    Var(j) => if j == i { s } else { t }
    _ =>
      @h3.map_tm(t, fn(x, b) { replace_var(x, i + b, @h3.shift_tm(s, b, 0)) })
  }
}

///|
/// 自由變數集合（相對於深度 0；回傳布林陣列，長 n）。
fn free_vars(t : @h3.Tm, n : Int32) -> Array[Bool] {
  let out = Array::make(n, false)
  fn go(x : @h3.Tm, depth : Int32) -> Unit {
    match x {
      Var(j) => if j >= depth && j - depth < n { out[j - depth] = true }
      _ =>
        ignore(
          @h3.map_tm(x, fn(y, b) {
            go(y, depth + b)
            y
          }),
        )
    }
  }

  go(t, 0)
  out
}

///|
/// 在正規形中尋找卡在符號變數上的消除子：`nat = false` 找 `if`（布林變數），
/// `nat = true` 找 `rec`（自然數變數）。回傳該變數的 de Bruijn 指標。
fn find_stuck(t : @h3.Tm, tys : Array[@h3.Tm], nat~ : Bool) -> Int32? {
  let n = tys.length()
  let mut found : Int32? = None
  fn go(x : @h3.Tm, depth : Int32) -> Unit {
    if !(found is None) {
      return
    }
    match x {
      If(_, Var(j), _, _) if !nat =>
        if j >= depth && j - depth < n && tys[n - 1 - (j - depth)] is BoolTy {
          found = Some(j - depth)
          return
        }
      NatRec(_, _, _, Var(j)) if nat =>
        if j >= depth && j - depth < n && tys[n - 1 - (j - depth)] is NatTy {
          found = Some(j - depth)
          return
        }
      _ => ()
    }
    ignore(
      @h3.map_tm(x, fn(y, b) {
        go(y, depth + b)
        y
      }),
    )
  }

  go(t, 0)
  found
}

///|
/// 一組正規形中卡住的消除子：布林先於自然數。
fn stuck_split(nfs : Array[@h3.Tm], tys : Array[@h3.Tm]) -> (Int32, Bool)? {
  for nat in [false, true] {
    for nf in nfs {
      if find_stuck(nf, tys, nat~) is Some(i) {
        return Some((i, nat))
      }
    }
  }
  None
}

///|
/// 分歧變數的選擇次序（回傳（指標, 是否為自然數））：
///   1. 卡住 `if` 的布林變數——分歧完備且不引入歸納假設，故最先；
///   2. 卡住 `rec` 的自然數變數——作歸納；
///   3. 兩側正規形中任一自由布林變數、再任一自由自然數變數——此時兩側已無卡住的
///      消除子卻仍相異，分歧只為把反例具體化。
fn choose_split(
  nl : @h3.Tm,
  nr : @h3.Tm,
  tys : Array[@h3.Tm],
) -> (Int32, Bool)? {
  if stuck_split([nl, nr], tys) is Some(c) {
    return Some(c)
  }
  let n = tys.length()
  let fl = free_vars(nl, n)
  let fr = free_vars(nr, n)
  for nat in [false, true] {
    for i in 0..<n {
      let ty = tys[n - 1 - i]
      if (fl[i] || fr[i]) && (if nat { ty is NatTy } else { ty is BoolTy }) {
        return Some((i, nat))
      }
    }
  }
  None
}

///|
/// 由類型清單建立核心上下文（第 k 個類型活在前 k 個變數的上下文中）。
pub fn build_ctx(
  k : @h3.Kernel,
  tys : Array[@h3.Tm],
) -> @h3.Ctx raise @h3.KernelError {
  let mut ctx = @h3.Ctx::empty()
  for t in tys {
    ctx = ctx.bind(k.eval(ctx.env, t))
  }
  ctx
}

///|
/// 符號執行：把含符號輸入的程式展開成以路徑條件為分支的執行樹。
/// `depth` 限制自然數的展開層數。
pub fn execute(
  k : @h3.Kernel,
  tys : Array[@h3.Tm],
  t : @h3.Tm,
  depth : Int32,
) -> SymTree raise @h3.KernelError {
  let ctx = build_ctx(k, tys)
  let (nf, _) = k.normalize(ctx, t)
  match stuck_split([nf], tys) {
    None => Leaf(nf)
    Some((i, false)) =>
      BoolSplit(
        i,
        execute(k, tys, replace_var(t, i, Tt), depth),
        execute(k, tys, replace_var(t, i, Ff), depth),
      )
    Some((i, true)) =>
      if depth == 0 {
        Cutoff(nf)
      } else {
        NatSplit(
          i,
          execute(k, tys, replace_var(t, i, Zero), depth),
          execute(k, tys, replace_var(t, i, Succ(Var(i))), depth - 1),
        )
      }
  }
}

///|
pub fn SymTree::leaves(self : SymTree) -> Int32 {
  match self {
    Leaf(_) | Cutoff(_) => 1
    BoolSplit(_, a, b) | NatSplit(_, a, b) => a.leaves() + b.leaves()
  }
}

///|
pub fn SymTree::cutoffs(self : SymTree) -> Int32 {
  match self {
    Leaf(_) => 0
    Cutoff(_) => 1
    BoolSplit(_, a, b) | NatSplit(_, a, b) => a.cutoffs() + b.cutoffs()
  }
}

///|
/// 以路徑條件列出每個葉子。
pub fn SymTree::render(self : SymTree) -> String {
  let sb = StringBuilder()
  fn go(t : SymTree, path : String) -> Unit {
    match t {
      Leaf(nf) => sb.write_string(path + " ⊢ " + @h3.show_tm(nf) + "\n")
      Cutoff(nf) => sb.write_string(path + " ⊢ … " + @h3.show_tm(nf) + "\n")
      BoolSplit(i, a, b) => {
        go(a, path + " #\{i}=tt")
        go(b, path + " #\{i}=ff")
      }
      NatSplit(i, a, b) => {
        go(a, path + " #\{i}=0")
        go(b, path + " #\{i}=S·")
      }
    }
  }

  go(self, "·")
  sb.to_string()
}

///|
/// 證明搜尋的結果。
pub(all) enum Outcome {
  /// 證明項（活在目標的上下文中）
  Proved(@h3.Tm)
  /// 反例：使兩側化為不同閉正規形的路徑條件
  Refuted(Array[String])
  /// 無法繼續（需要輔助引理）
  Stuck(String)
}

///|
pub(all) struct Stats {
  mut normalizations : Int32
  mut leaves : Int32
  mut bool_splits : Int32
  mut inductions : Int32
  mut ih_rewrites : Int32
}

///|
/// 把 t 中 target 的每個出現抽象為新變數 0（結果活在多一個變數的上下文）；回傳（抽象後的項, 出現次數）。
fn abstract_term(t : @h3.Tm, target : @h3.Tm) -> (@h3.Tm, Int32) {
  let mut count = 0
  fn go(x : @h3.Tm, tg : @h3.Tm, depth : Int32) -> @h3.Tm {
    if x == tg {
      count += 1
      return Var(depth)
    }
    match x {
      Var(_) => x
      _ => @h3.map_tm(x, fn(y, b) { go(y, @h3.shift_tm(tg, b, 0), depth + b) })
    }
  }

  let shifted = @h3.shift_tm(t, 1, 0)
  let r = go(shifted, @h3.shift_tm(target, 1, 0), 0)
  (r, count)
}

///|
/// 以假設 h : Id T u v 改寫：若 lhs ≡ L[u] 且 L[v] ≡ rhs，則 J 給出證明（即 cong L h）。
fn try_rewrite(
  k : @h3.Kernel,
  ctx : @h3.Ctx,
  ty : @h3.Tm,
  nl : @h3.Tm,
  nr : @h3.Tm,
  hyp : Int32,
  u : @h3.Tm,
  v : @h3.Tm,
) -> @h3.Tm? raise @h3.KernelError {
  let (nu, _) = k.normalize(ctx, u)
  let (nv, _) = k.normalize(ctx, v)
  // 兩個方向：抽象左側中的 u，或抽象右側中的 v
  let candidates : Array[@h3.Tm] = []
  let (l_abs, c1) = abstract_term(nl, nu)
  if c1 > 0 {
    let (back, _) = k.normalize(ctx, @h3.subst_tm(l_abs, 0, nv))
    if back == nr {
      candidates.push(l_abs)
    }
  }
  let (r_abs, c2) = abstract_term(nr, nv)
  if c2 > 0 {
    let (back, _) = k.normalize(ctx, @h3.subst_tm(r_abs, 0, nu))
    if back == nl {
      candidates.push(r_abs)
    }
  }
  if candidates.length() == 0 {
    return None
  }
  let l = candidates[0]
  // 動機 C(x, y, q) = Id ty L[x] L[y]（x = #2，y = #1，q = #0）
  let at = fn(idx : Int32) -> @h3.Tm {
    @h3.subst_tm(@h3.shift_tm(l, 3, 1), 0, Var(idx))
  }
  let motive : @h3.Tm = IdTy(@h3.shift_tm(ty, 3, 0), at(2), at(1))
  Some(J(motive, Refl(l), Var(hyp)))
}

///|
fn has_free(t : @h3.Tm, n : Int32) -> Bool {
  for b in free_vars(t, n) {
    if b {
      return true
    }
  }
  false
}

///|
/// 兩個正規形在建構子層面必然相異（0 對 S、tt 對 ff，或 S 之下遞迴相異）。
fn constructors_clash(a : @h3.Tm, b : @h3.Tm) -> Bool {
  match (a, b) {
    (Zero, Succ(_)) | (Succ(_), Zero) | (Tt, Ff) | (Ff, Tt) => true
    (Succ(x), Succ(y)) => constructors_clash(x, y)
    _ => false
  }
}

///|
/// 核心搜尋：於上下文 `tys` 中證明 Id ty lhs rhs。
/// `hyps` 為可用的等式假設（變數指標, u, v）；`split` 表示是否仍可分歧。
fn search(
  k : @h3.Kernel,
  tys : Array[@h3.Tm],
  ty : @h3.Tm,
  lhs : @h3.Tm,
  rhs : @h3.Tm,
  hyps : Array[(Int32, @h3.Tm, @h3.Tm)],
  split : Bool,
  path : Array[String],
  st : Stats,
) -> Outcome raise @h3.KernelError {
  let n = tys.length()
  let ctx = build_ctx(k, tys)
  let (nl, _) = k.normalize(ctx, lhs)
  let (nr, _) = k.normalize(ctx, rhs)
  st.normalizations += 2
  if nl == nr {
    st.leaves += 1
    return Proved(Refl(nl))
  }
  for h in hyps {
    let (idx, u, v) = h
    match try_rewrite(k, ctx, ty, nl, nr, idx, u, v) {
      Some(p) => {
        st.leaves += 1
        st.ih_rewrites += 1
        return Proved(p)
      }
      None => ()
    }
  }
  if constructors_clash(nl, nr) {
    // 建構子相異：對其餘變數的任何取值皆不等
    st.leaves += 1
    let cond = path.copy()
    cond.push(@h3.show_tm(nl) + " ≠ " + @h3.show_tm(nr))
    return Refuted(cond)
  }
  if !split {
    return Stuck(
      "induction step needs a lemma: " +
      @h3.show_tm(nl) +
      " vs " +
      @h3.show_tm(nr),
    )
  }
  match choose_split(nl, nr, tys) {
    None =>
      if !has_free(nl, n) && !has_free(nr, n) {
        st.leaves += 1
        let cond = path.copy()
        cond.push(@h3.show_tm(nl) + " ≠ " + @h3.show_tm(nr))
        Refuted(cond)
      } else {
        Stuck(
          "no eliminator is stuck on a variable: " +
          @h3.show_tm(nl) +
          " vs " +
          @h3.show_tm(nr),
        )
      }
    Some((i, false)) => {
      st.bool_splits += 1
      let pt = path.copy()
      pt.push("#\{i} = tt")
      let rt = search(
        k,
        tys,
        replace_var(ty, i, Tt),
        replace_var(lhs, i, Tt),
        replace_var(rhs, i, Tt),
        hyps,
        split,
        pt,
        st,
      )
      let proof_t = match rt {
        Proved(p) => p
        other => return other
      }
      let pf = path.copy()
      pf.push("#\{i} = ff")
      let rf = search(
        k,
        tys,
        replace_var(ty, i, Ff),
        replace_var(lhs, i, Ff),
        replace_var(rhs, i, Ff),
        hyps,
        split,
        pf,
        st,
      )
      let proof_f = match rf {
        Proved(p) => p
        other => return other
      }
      // 動機 λz. Id ty lhs rhs [x_i := z]
      let gen = fn(x : @h3.Tm) -> @h3.Tm {
        replace_var(@h3.shift_tm(x, 1, 0), i + 1, Var(0))
      }
      let motive : @h3.Tm = IdTy(gen(ty), gen(lhs), gen(rhs))
      Proved(If(motive, Var(i), proof_t, proof_f))
    }
    Some((i, true)) => {
      st.inductions += 1
      let p0 = path.copy()
      p0.push("#\{i} = 0")
      let r0 = search(
        k,
        tys,
        replace_var(ty, i, Zero),
        replace_var(lhs, i, Zero),
        replace_var(rhs, i, Zero),
        hyps,
        split,
        p0,
        st,
      )
      let proof_0 = match r0 {
        Proved(p) => p
        other => return other
      }
      // 歸納步：上下文加入 k : Nat 與 ih : G[x_i := k]
      let gen = fn(x : @h3.Tm) -> @h3.Tm {
        replace_var(@h3.shift_tm(x, 1, 0), i + 1, Var(0))
      }
      let motive : @h3.Tm = IdTy(gen(ty), gen(lhs), gen(rhs))
      let step_tys = tys.copy()
      step_tys.push(NatTy)
      step_tys.push(motive)
      let up = fn(x : @h3.Tm) -> @h3.Tm {
        replace_var(@h3.shift_tm(x, 2, 0), i + 2, Succ(Var(1)))
      }
      // 歸納假設的兩側（活在加入 k、ih 之後的上下文）
      let ih_u = @h3.shift_tm(gen(lhs), 1, 0)
      let ih_v = @h3.shift_tm(gen(rhs), 1, 0)
      let step_hyps : Array[(Int32, @h3.Tm, @h3.Tm)] = [(0, ih_u, ih_v)]
      for h in hyps {
        let (idx, u, v) = h
        step_hyps.push((idx + 2, up(u), up(v)))
      }
      let ps = path.copy()
      ps.push("#\{i} = S k")
      let rs = search(
        k,
        step_tys,
        up(ty),
        up(lhs),
        up(rhs),
        step_hyps,
        false,
        ps,
        st,
      )
      let proof_s = match rs {
        Proved(p) => p
        other => return other
      }
      Proved(NatRec(motive, proof_0, proof_s, Var(i)))
    }
  }
}

///|
/// 一則定理的完整報告。
pub(all) struct ProofReport {
  /// "proved" / "refuted" / "stuck" / "unsupported"
  status : String
  /// 反例的路徑條件或卡住原因
  detail : String
  /// H3 核心是否接受合成的證明項
  kernel_accepted : Bool
  proof_size : Int32
  derivation_size : Int32
  leaves : Int32
  bool_splits : Int32
  inductions : Int32
  ih_rewrites : Int32
  normalizations : Int32
}

///|
/// 證明閉命題 Π(x₁:T₁)…(xₙ:Tₙ). Id A l r（Tᵢ 為 Bool 或 Nat）。
/// 成功時把證明項以 λ 封閉並交由核心對原命題重新檢查。
pub fn prove(
  k : @h3.Kernel,
  statement : @h3.Tm,
) -> ProofReport raise @h3.KernelError {
  let st : Stats = {
    normalizations: 0,
    leaves: 0,
    bool_splits: 0,
    inductions: 0,
    ih_rewrites: 0,
  }
  let mk = fn(
    status : String,
    detail : String,
    accepted : Bool,
    psize : Int32,
    dsize : Int32,
  ) -> ProofReport {
    {
      status,
      detail,
      kernel_accepted: accepted,
      proof_size: psize,
      derivation_size: dsize,
      leaves: st.leaves,
      bool_splits: st.bool_splits,
      inductions: st.inductions,
      ih_rewrites: st.ih_rewrites,
      normalizations: st.normalizations,
    }
  }
  let tys : Array[@h3.Tm] = []
  let mut body = statement
  while true {
    match body {
      Pi(dom, cod) => {
        if !(dom is (BoolTy | NatTy)) {
          return mk(
            "unsupported",
            "parameter type " + @h3.show_tm(dom) + " is neither Bool nor Nat",
            false,
            0,
            0,
          )
        }
        tys.push(dom)
        body = cod
      }
      _ => break
    }
  }
  let (ty, lhs, rhs) = match body {
    IdTy(a, l, r) => (a, l, r)
    other =>
      return mk(
        "unsupported",
        "conclusion " + @h3.show_tm(other) + " is not an identity type",
        false,
        0,
        0,
      )
  }
  let outcome = search(k, tys, ty, lhs, rhs, [], true, [], st)
  match outcome {
    Proved(p) => {
      let mut closed = p
      let mut i = tys.length() - 1
      while i >= 0 {
        closed = Lam(tys[i], closed)
        i -= 1
      }
      let empty = @h3.Ctx::empty()
      let goal = k.eval(empty.env, statement)
      try k.check(empty, closed, goal) catch {
        err =>
          mk(
            "proved",
            "kernel rejected: " + err.message(),
            false,
            @h3.tm_size(closed),
            0,
          )
      } noraise {
        d => mk("proved", "", true, @h3.tm_size(closed), d.size())
      }
    }
    Refuted(cond) => {
      let sb = StringBuilder()
      for c in cond {
        sb.write_string(c + "; ")
      }
      mk("refuted", sb.to_string(), false, 0, 0)
    }
    Stuck(why) => mk("stuck", why, false, 0, 0)
  }
}

///|
/// 由表層原始碼（定義 + 最終的命題類型）證明。
pub fn prove_source(src : String) -> ProofReport raise @h3.KernelError {
  let k = @h3.Kernel::new()
  let e = k.elaborate(src)
  prove(k, e.term)
}

///|
/// 內建前奏：布林運算與加法。
pub fn prelude() -> String {
  let s =
    #|(def not (-> Bool Bool) (lam b (if b ff tt)))
    #|(def and (-> Bool Bool Bool) (lam a b (if a b ff)))
    #|(def or (-> Bool Bool Bool) (lam a b (if a tt b)))
    #|(def xor (-> Bool Bool Bool) (lam a b (if a (not b) b)))
    #|(def plus (-> Nat Nat Nat) (lam m n (rec (x Nat) n (k ih (S ih)) m)))
    #|(def double (-> Nat Nat) (lam n (rec (x Nat) 0 (k ih (S (S ih))) n)))
    #|
  s
}

///|
/// 內建定理語料：（名稱, 命題, 預期狀態）。
pub fn corpus() -> Array[(String, String, String)] {
  [
    ("double negation", "(Pi (b Bool) (Id Bool (not (not b)) b))", "proved"),
    (
      "de Morgan", "(Pi (a Bool) (b Bool) (Id Bool (not (and a b)) (or (not a) (not b))))",
      "proved",
    ),
    (
      "and commutative", "(Pi (a Bool) (b Bool) (Id Bool (and a b) (and b a)))",
      "proved",
    ),
    (
      "xor associative", "(Pi (a Bool) (b Bool) (c Bool) (Id Bool (xor (xor a b) c) (xor a (xor b c))))",
      "proved",
    ),
    (
      "distributivity", "(Pi (a Bool) (b Bool) (c Bool) (Id Bool (and a (or b c)) (or (and a b) (and a c))))",
      "proved",
    ),
    (
      "and is not or", "(Pi (a Bool) (b Bool) (Id Bool (and a b) (or a b)))", "refuted",
    ),
    ("n + 0 = n", "(Pi (n Nat) (Id Nat (plus n 0) n))", "proved"),
    (
      "n + S m = S (n + m)", "(Pi (n Nat) (m Nat) (Id Nat (plus n (S m)) (S (plus n m))))",
      "proved",
    ),
    (
      "double n = n + n needs a lemma", "(Pi (n Nat) (Id Nat (double n) (plus n n)))",
      "stuck",
    ),
    (
      "mixed Bool and Nat", "(Pi (b Bool) (n Nat) (Id Nat (plus (if b n 0) 0) (if b n 0)))",
      "proved",
    ),
    (
      "Bool split precedes induction", "(Pi (b Bool) (n Nat) (Id Nat (plus n 0) (if b n n)))",
      "proved",
    ),
    (
      "counterexample needs a split on a free Nat", "(Pi (n Nat) (b Bool) (Id Nat (if b n (S n)) n))",
      "refuted",
    ),
    (
      "constructor clash inside an induction step", "(Pi (n Nat) (m Nat) (Id Nat (S n) (S m)))",
      "refuted",
    ),
  ]
}

///|
/// 對整個語料執行；回傳（符合預期數, 總數, 全部被證明者皆獲核心接受）。
pub fn verify_corpus() -> (Int32, Int32, Bool) {
  let mut ok = 0
  let mut accepted = true
  let items = corpus()
  for item in items {
    let (_, stmt, expected) = item
    try prove_source(prelude() + stmt) catch {
      _ => ()
    } noraise {
      r => {
        if r.status == expected {
          ok += 1
        }
        if r.status == "proved" && !r.kernel_accepted {
          accepted = false
        }
      }
    }
  }
  (ok, items.length(), accepted)
}
