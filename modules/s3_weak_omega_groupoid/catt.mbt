///|
/// Module S3 — 弱 ω-群胚（Brunerie）與弱 ω-範疇（Finster–Mimram 的 CaTT）。
///
/// 類型：`*` 或 `t →_A u`；項：變數或 `coh_{Δ,A}[σ]`。
/// 理論中沒有計算規則，判定性相等即語法相等，故類型檢查可判定。
pub(all) enum Ty {
  Obj
  Arr(Ty, Tm, Tm)
}

///|
pub(all) enum Tm {
  /// 上下文中的第 k 個變數
  Var(Int32)
  /// 已登錄的第 c 個融貫子，套上代換 σ（對 Δ 的每個變數給一個項）
  Coh(Int32, Array[Tm])
}

///|
pub fn tm_equal(a : Tm, b : Tm) -> Bool {
  match (a, b) {
    (Var(i), Var(j)) => i == j
    (Coh(c, s), Coh(d, t)) => {
      if c != d || s.length() != t.length() {
        return false
      }
      for k in 0..<s.length() {
        if !tm_equal(s[k], t[k]) {
          return false
        }
      }
      true
    }
    _ => false
  }
}

///|
pub fn ty_equal(a : Ty, b : Ty) -> Bool {
  match (a, b) {
    (Obj, Obj) => true
    (Arr(a1, s1, t1), Arr(a2, s2, t2)) =>
      ty_equal(a1, a2) && tm_equal(s1, s2) && tm_equal(t1, t2)
    _ => false
  }
}

///|
pub fn Ty::dim(self : Ty) -> Int32 {
  match self {
    Obj => 0
    Arr(a, _, _) => a.dim() + 1
  }
}

///|
pub fn subst_tm(t : Tm, sigma : Array[Tm]) -> Tm {
  match t {
    Var(k) => sigma[k]
    Coh(c, s) => {
      let out : Array[Tm] = []
      for x in s {
        out.push(subst_tm(x, sigma))
      }
      Coh(c, out)
    }
  }
}

///|
pub fn subst_ty(t : Ty, sigma : Array[Tm]) -> Ty {
  match t {
    Obj => Obj
    Arr(a, s, u) =>
      Arr(subst_ty(a, sigma), subst_tm(s, sigma), subst_tm(u, sigma))
  }
}

///|
/// 自由變數集合（64-bit 位元集；上下文至多 62 個變數）。
pub fn fv_tm(t : Tm) -> Int64 {
  match t {
    Var(k) => 1L << k
    Coh(_, s) => {
      let mut acc = 0L
      for x in s {
        acc = acc | fv_tm(x)
      }
      acc
    }
  }
}

///|
pub fn fv_ty(t : Ty) -> Int64 {
  match t {
    Obj => 0L
    Arr(a, s, u) => fv_ty(a) | fv_tm(s) | fv_tm(u)
  }
}

///|
pub suberror CattError {
  Reject(String)
}

///|
pub fn CattError::message(self : CattError) -> String {
  match self {
    Reject(s) => s
  }
}

///|
/// 融貫子：粘貼圖式 Δ 與其中的類型 A。
pub(all) struct Coherence {
  name : String
  ps : Array[Ty]
  ty : Ty
  /// 由「全變數」條件（等式型）還是「源／靶」條件（運算型）接受；群胚模式下恆為 "contractible"
  kind : String
}

///|
/// 理論狀態：`groupoid=true` 為 Brunerie 的 ω-群胚（粘貼圖式中任何類型皆有居留元），
/// 否則為 CaTT 的 ω-範疇（須滿足變數條件）。
pub(all) struct Theory {
  groupoid : Bool
  cohs : Array[Coherence]
  mut checks : Int32
}

///|
pub fn Theory::new(groupoid~ : Bool) -> Theory {
  { groupoid, cohs: [], checks: 0, }
}

///|
/// Γ ⊢ A
pub fn Theory::check_ty(
  self : Theory,
  ctx : Array[Ty],
  t : Ty,
) -> Unit raise CattError {
  match t {
    Obj => ()
    Arr(a, s, u) => {
      self.check_ty(ctx, a)
      self.check_tm(ctx, s, a)
      self.check_tm(ctx, u, a)
    }
  }
}

///|
/// Γ ⊢ t : A（合成類型）
pub fn Theory::infer(
  self : Theory,
  ctx : Array[Ty],
  t : Tm,
) -> Ty raise CattError {
  self.checks += 1
  match t {
    Var(k) =>
      if k < 0 || k >= ctx.length() {
        raise Reject("unbound variable x\{k}")
      } else {
        ctx[k]
      }
    Coh(c, sigma) => {
      if c < 0 || c >= self.cohs.length() {
        raise Reject("unknown coherence #\{c}")
      }
      let coh = self.cohs[c]
      self.check_sub(ctx, sigma, coh.ps)
      subst_ty(coh.ty, sigma)
    }
  }
}

///|
pub fn Theory::check_tm(
  self : Theory,
  ctx : Array[Ty],
  t : Tm,
  ty : Ty,
) -> Unit raise CattError {
  let got = self.infer(ctx, t)
  if !ty_equal(got, ty) {
    raise Reject(
      "type mismatch: " +
      self.show_tm(t) +
      " : " +
      self.show_ty(got) +
      ", expected " +
      self.show_ty(ty),
    )
  }
}

///|
/// Γ ⊢ σ : Δ
pub fn Theory::check_sub(
  self : Theory,
  ctx : Array[Ty],
  sigma : Array[Tm],
  delta : Array[Ty],
) -> Unit raise CattError {
  if sigma.length() != delta.length() {
    raise Reject("substitution length \{sigma.length()} ≠ \{delta.length()}")
  }
  for k in 0..<delta.length() {
    self.check_tm(ctx, sigma[k], subst_ty(delta[k], sigma))
  }
}

///|
/// Γ ⊢（上下文良構：每個類型在其前綴中良構）
pub fn Theory::check_ctx(
  self : Theory,
  ctx : Array[Ty],
) -> Unit raise CattError {
  if ctx.length() > 62 {
    raise Reject("context too long")
  }
  let prefix : Array[Ty] = []
  for t in ctx {
    self.check_ty(prefix, t)
    prefix.push(t)
  }
}

///|
/// 粘貼圖式判定（Finster–Mimram 的 ⊢ps，確定性演算法，線性時間）：
///   (pss) (x:*) ⊢ps x:*
///   (pse) Γ ⊢ps x:A ⟹ Γ, y:A, f:x→y ⊢ps f:x→y
///   (psd) Γ ⊢ps f:x→y ⟹ Γ ⊢ps y:A
///   (ps)  Γ ⊢ps x:* ⟹ Γ ⊢ps
pub fn is_pasting_scheme(ctx : Array[Ty]) -> Bool {
  let n = ctx.length()
  if n == 0 || n % 2 == 0 {
    return false
  }
  if !(ctx[0] is Obj) {
    return false
  }
  let mut cursor = 0
  let mut k = 1
  while k < n {
    let b = ctx[k]
    let fty = ctx[k + 1]
    // 以 (psd) 下降，直至游標的類型與 y 的類型同維
    while ctx[cursor].dim() > b.dim() {
      match ctx[cursor] {
        Arr(_, _, Var(y)) => cursor = y
        _ => return false
      }
    }
    if !ty_equal(ctx[cursor], b) {
      return false
    }
    if !ty_equal(fty, Arr(b, Var(cursor), Var(k))) {
      return false
    }
    cursor = k + 1
    k += 2
  }
  true
}

///|
/// 粘貼圖式的維數（最高維變數的維數）。
pub fn ctx_dim(ctx : Array[Ty]) -> Int32 {
  let mut d = 0
  for t in ctx {
    if t.dim() > d {
      d = t.dim()
    }
  }
  d
}

///|
/// 邊界 ∂ᵢ⁻Δ 與 ∂ᵢ⁺Δ 的變數集合（i = dim Δ − 1 時即源與靶）。
pub fn boundary_vars(ctx : Array[Ty], i : Int32) -> (Int64, Int64) {
  let mut src = 1L
  let tgt : Array[Int32] = [0]
  let mut k = 1
  while k + 1 < ctx.length() {
    let d = ctx[k].dim()
    if d < i {
      src = src | (1L << k) | (1L << (k + 1))
      tgt.push(k)
      tgt.push(k + 1)
    } else if d == i {
      // 靶：以 y 取代目前最後一個變數（f 的源）
      ignore(tgt.pop())
      tgt.push(k)
    }
    k += 2
  }
  let mut t = 0L
  for v in tgt {
    t = t | (1L << v)
  }
  (src, t)
}

///|
/// 登錄融貫子 coh_{Δ,A}。ω-範疇模式下須滿足：
///   （運算型）A = t → u，Var(t)∪Var(其類型) = Var(∂⁻Δ) 且 Var(u)∪… = Var(∂⁺Δ)；或
///   （等式型）Var(A) = Var(Δ)。
/// ω-群胚模式下 Δ 可縮，任何良構類型皆被接受。回傳融貫子編號。
pub fn Theory::add_coherence(
  self : Theory,
  name : String,
  ps : Array[Ty],
  ty : Ty,
) -> Int32 raise CattError {
  self.check_ctx(ps)
  if !is_pasting_scheme(ps) {
    raise Reject(name + ": context is not a pasting scheme")
  }
  self.check_ty(ps, ty)
  let all = (1L << ps.length()) - 1L
  let kind = if fv_ty(ty) == all {
    "equation"
  } else {
    let op_ok = match ty {
      Arr(b, t, u) => {
        let d = ctx_dim(ps)
        if d == 0 {
          false
        } else {
          let (src, tgt) = boundary_vars(ps, d - 1)
          (fv_tm(t) | fv_ty(b)) == src && (fv_tm(u) | fv_ty(b)) == tgt
        }
      }
      Obj => false
    }
    if op_ok {
      "operation"
    } else if self.groupoid {
      "contractible"
    } else {
      raise Reject(
        name +
        ": type satisfies neither the operation nor the equation variable condition",
      )
    }
  }
  self.cohs.push({ name, ps, ty, kind, })
  self.cohs.length() - 1
}

///|
pub fn Theory::show_tm(self : Theory, t : Tm) -> String {
  match t {
    Var(k) => "x\{k}"
    Coh(c, s) => {
      let sb = StringBuilder()
      sb.write_string(
        if c >= 0 && c < self.cohs.length() {
          self.cohs[c].name
        } else {
          "coh?"
        },
      )
      sb.write_string("[")
      // 只顯示極大維的實參（其餘由類型決定）
      let mut first = true
      for x in s {
        if !first {
          sb.write_string(",")
        }
        first = false
        sb.write_string(self.show_tm(x))
      }
      sb.write_string("]")
      sb.to_string()
    }
  }
}

///|
pub fn Theory::show_ty(self : Theory, t : Ty) -> String {
  match t {
    Obj => "*"
    Arr(_, s, u) => self.show_tm(s) + " → " + self.show_tm(u)
  }
}

///|
/// Theorem 40（Finster–Mimram／Benjamin）的關係 ⊳：由 s(x) ⊳ x ⊳ t(x) 生成的傳遞閉包。
/// 回傳該關係是否為全序（全且反對稱）。只適用於球狀上下文（端點皆為變數）。
pub fn triangle_order_is_linear(ctx : Array[Ty]) -> Bool {
  let n = ctx.length()
  if n == 0 {
    return false
  }
  let rel : Array[Int64] = Array::make(n, 0L)
  for k in 0..<n {
    match ctx[k] {
      Arr(_, Var(s), Var(t)) => {
        rel[s] = rel[s] | (1L << k)
        rel[k] = rel[k] | (1L << t)
      }
      Arr(_, _, _) => return false
      Obj => ()
    }
  }
  // Warshall 傳遞閉包（位元集）
  for m in 0..<n {
    for a in 0..<n {
      if ((rel[a] >> m) & 1L) == 1L {
        rel[a] = rel[a] | rel[m]
      }
    }
  }
  for a in 0..<n {
    if ((rel[a] >> a) & 1L) == 1L {
      return false
    }
    for b in (a + 1)..<n {
      let ab = ((rel[a] >> b) & 1L) == 1L
      let ba = ((rel[b] >> a) & 1L) == 1L
      if ab == ba {
        return false
      }
    }
  }
  true
}
