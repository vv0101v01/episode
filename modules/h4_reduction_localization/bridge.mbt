///|
/// Module H4 — H2（約簡）× H3（核心）的橋接：
/// 「正規化 = 對約簡箭頭作範疇局部化」：把每個約簡 t → u 強行升格為同構，
/// 所得商範疇的對象即正規形；駐留後定義性相等類別為 O(1) 整數比較。
///
/// 核心項 → 約簡競技場（無損嵌入；相同子項自動共享為 DAG）。
pub fn embed(a : @h2.Arena, t : @h3.Tm) -> Int32 {
  let n : @h2.Node = match t {
    Var(i) => Var(i)
    Univ(l) => Univ(l)
    Pi(x, y) => Pi(embed(a, x), embed(a, y))
    Lam(x, y) => Lam(embed(a, x), embed(a, y))
    App(x, y) => App(embed(a, x), embed(a, y))
    Sigma(x, y) => Sigma(embed(a, x), embed(a, y))
    Pair(x, y, z) => Pair(embed(a, x), embed(a, y), embed(a, z))
    Fst(x) => Fst(embed(a, x))
    Snd(x) => Snd(embed(a, x))
    UnitTy => UnitTy
    Star => Star
    EmptyTy => EmptyTy
    Absurd(c, e) => Absurd(embed(a, c), embed(a, e))
    BoolTy => BoolTy
    Tt => Tt
    Ff => Ff
    If(c, s, x, y) => If(embed(a, c), embed(a, s), embed(a, x), embed(a, y))
    NatTy => NatTy
    Zero => Zero
    Succ(x) => Succ(embed(a, x))
    NatRec(c, z, s, m) =>
      NatRec(embed(a, c), embed(a, z), embed(a, s), embed(a, m))
    IdTy(x, y, z) => IdTy(embed(a, x), embed(a, y), embed(a, z))
    Refl(x) => Refl(embed(a, x))
    J(c, d, p) => J(embed(a, c), embed(a, d), embed(a, p))
  }
  a.mk(n)
}

///|
/// 約簡競技場 → 核心項（`embed` 的逆）。
pub fn reify(a : @h2.Arena, id : Int32) -> @h3.Tm {
  match a.node(id) {
    Var(i) => Var(i)
    Univ(l) => Univ(l)
    Pi(x, y) => Pi(reify(a, x), reify(a, y))
    Lam(x, y) => Lam(reify(a, x), reify(a, y))
    App(x, y) => App(reify(a, x), reify(a, y))
    Sigma(x, y) => Sigma(reify(a, x), reify(a, y))
    Pair(x, y, z) => Pair(reify(a, x), reify(a, y), reify(a, z))
    Fst(x) => Fst(reify(a, x))
    Snd(x) => Snd(reify(a, x))
    UnitTy => UnitTy
    Star => Star
    EmptyTy => EmptyTy
    Absurd(c, e) => Absurd(reify(a, c), reify(a, e))
    BoolTy => BoolTy
    Tt => Tt
    Ff => Ff
    If(c, s, x, y) => If(reify(a, c), reify(a, s), reify(a, x), reify(a, y))
    NatTy => NatTy
    Zero => Zero
    Succ(x) => Succ(reify(a, x))
    NatRec(c, z, s, m) =>
      NatRec(reify(a, c), reify(a, z), reify(a, s), reify(a, m))
    IdTy(x, y, z) => IdTy(reify(a, x), reify(a, y), reify(a, z))
    Refl(x) => Refl(reify(a, x))
    J(c, d, p) => J(reify(a, c), reify(a, d), reify(a, p))
  }
}

///|
/// 局部化函子：把良類型閉項送到其定義性相等類別的代表（η-長 β-正規形的駐留編號）。
/// 普遍性質的可計算面：t ≡ u ⇔ class_of(t) == class_of(u)。
pub(all) struct Localizer {
  arena : @h2.Arena
  kernel : @h3.Kernel
  /// 已知項編號 → 類別代表編號
  classes : Map[Int32, Int32]
  mut lookups : Int32
  mut normalizations : Int32
}

///|
pub fn Localizer::new(arena : @h2.Arena, kernel : @h3.Kernel) -> Localizer {
  { arena, kernel, classes: Map([]), lookups: 0, normalizations: 0, }
}

///|
/// 類別代表。首次查詢執行類型檢查與 NbE；其後為 O(1) 查表。
pub fn Localizer::class_of(
  self : Localizer,
  t : @h3.Tm,
) -> Int32 raise @h3.KernelError {
  let id = embed(self.arena, t)
  self.lookups += 1
  match self.classes.get(id) {
    Some(c) => c
    None => {
      let (nf, _) = self.kernel.normalize(@h3.Ctx::empty(), t)
      let c = embed(self.arena, nf)
      self.normalizations += 1
      self.classes[id] = c
      // 正規形是自身類別的代表（冪等）
      self.classes[c] = c
      c
    }
  }
}

///|
pub fn Localizer::equivalent(
  self : Localizer,
  t : @h3.Tm,
  u : @h3.Tm,
) -> Bool raise @h3.KernelError {
  self.class_of(t) == self.class_of(u)
}

///|
/// 橋接分析報告：同一個良類型閉項在「重寫」與「語義」兩側的全部不變量。
pub(all) struct BridgeReport {
  /// NbE 的 η-長正規形與最左策略所得 β-正規形（駐留編號）
  nbe_nf : @h3.Tm
  beta_nf : Int32
  /// 兩者各自 η-收縮後語法全等
  syntactic_agreement : Bool
  /// 兩者經核心類型導向轉換判定為定義性相等
  definitional_agreement : Bool
  /// 強正規化證書（窮舉約簡圖）
  verdict : @h2.SnVerdict
  graph_nodes : Int32
  graph_edges : Int32
  longest : Int32
  shortest : Int32
  unique_normal_form : Bool
  /// 各策略步數
  leftmost_steps : Int32
  perpetual_steps : Int32
  gross_knuth_rounds : Int32
  /// F∞ 步數恰為最長約簡長度
  perpetual_is_longest : Bool
  /// 主詞約簡：約簡圖中受檢的節點數，以及是否全部保持類型（類型 ≤ 原類型）
  reducts_checked : Int32
  subject_reduction : Bool
  /// 局部化：受檢節點是否全部落入同一定義性相等類別
  reductions_inverted : Bool
}

///|
/// 對良類型閉項 `t` 執行完整橋接分析。`budget` 為約簡圖節點上限。
pub fn analyze(
  k : @h3.Kernel,
  a : @h2.Arena,
  t : @h3.Tm,
  budget~ : Int32,
) -> BridgeReport raise @h3.KernelError {
  let ctx = @h3.Ctx::empty()
  let d = k.infer(ctx, t)
  let ty = d.ty
  let nbe_nf = k.quote_nf(ctx, ty, k.eval(ctx.env, t))
  let root = embed(a, t)
  let lo = a.run_leftmost(root, fuel=budget * 16)
  let pe = a.run_perpetual(root, fuel=budget * 16)
  let gk = a.run_gross_knuth(root, fuel=budget)
  let cert = a.sn_certificate(root, eta=false, budget~)
  let (e1, _) = a.eta_normalize(embed(a, nbe_nf))
  let (e2, _) = a.eta_normalize(lo.result)
  let definitional = try {
    let back = reify(a, lo.result)
    let _ = k.check(ctx, back, ty)
    k.conv_typed(ctx, ty, k.eval(ctx.env, back), k.eval(ctx.env, nbe_nf))
  } catch {
    _ => false
  }
  // 走訪約簡圖：每個可達約簡項皆須保持類型並落入同一類別
  let loc = Localizer::new(a, k)
  let target = loc.class_of(t)
  let seen : Map[Int32, Unit] = Map([])
  let queue = [root]
  seen[root] = ()
  let mut head = 0
  let mut sr = true
  let mut inverted = true
  while head < queue.length() && queue.length() <= budget {
    let cur = queue[head]
    head += 1
    let back = reify(a, cur)
    let ok = try {
      let dr = k.infer(ctx, back)
      k.sub_ty(ctx, dr.ty, ty)
    } catch {
      _ => false
    }
    if !ok {
      sr = false
    } else {
      let same = try loc.class_of(back) == target catch {
        _ => false
      }
      if !same {
        inverted = false
      }
    }
    for r in a.reducts(cur, eta=false) {
      if !seen.contains(r) {
        seen[r] = ()
        queue.push(r)
      }
    }
  }
  {
    nbe_nf,
    beta_nf: lo.result,
    syntactic_agreement: lo.normal && e1 == e2,
    definitional_agreement: definitional,
    verdict: cert.verdict,
    graph_nodes: cert.nodes,
    graph_edges: cert.edges,
    longest: cert.longest,
    shortest: cert.shortest,
    unique_normal_form: cert.normal_forms.length() == 1 &&
    cert.normal_forms[0] == lo.result,
    leftmost_steps: lo.steps,
    perpetual_steps: pe.steps,
    gross_knuth_rounds: gk.steps,
    perpetual_is_longest: pe.normal && pe.steps == cert.longest,
    reducts_checked: head,
    subject_reduction: sr,
    reductions_inverted: inverted,
  }
}

///|
/// 纖維積視角的合流：對同源項的任兩個一步約簡結果求共同約簡項，並驗證其落在 NbE 正規形的類別上。
/// 回傳（受檢的約簡結果配對數, 是否全部合流於同一類別）。
pub fn verify_confluence_squares(
  k : @h3.Kernel,
  a : @h2.Arena,
  t : @h3.Tm,
  fuel~ : Int32,
) -> (Int32, Bool) raise @h3.KernelError {
  let loc = Localizer::new(a, k)
  let target = loc.class_of(t)
  let rs = a.reducts(embed(a, t), eta=false)
  let mut pairs = 0
  let mut ok = true
  for i in 0..<rs.length() {
    for j in (i + 1)..<rs.length() {
      pairs += 1
      match a.church_rosser_join(rs[i], rs[j], fuel~) {
        Some(join) => {
          let c = loc.class_of(reify(a, join.common)) catch { _ => -1 }
          if c != target {
            ok = false
          }
        }
        None => ok = false
      }
    }
  }
  (pairs, ok)
}
