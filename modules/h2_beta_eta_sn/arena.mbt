///|
/// Module H2 — β約簡、η轉換、強正規化。
/// 項以 de Bruijn 指標表示並駐留（hash-consing）於 `Arena`：
/// 結構相等 ⇔ 節點編號相等（O(1)），每個節點快取 64-bit 自由變數遮罩、
/// 可約式旗標與樹大小，使「是否為正規形」「η 邊條件 x∉FV(f)」「閉項位移」皆為 O(1)。
#derive(Eq, Hash)
pub(all) enum Node {
  Var(Int32)
  Univ(Int32)
  /// Pi(A, B)：B 綁定 1 個變數
  Pi(Int32, Int32)
  /// Lam(A, b)：Church 式標註，b 綁定 1 個變數
  Lam(Int32, Int32)
  App(Int32, Int32)
  Sigma(Int32, Int32)
  /// Pair(a, b, B)：B 為 Σ 的纖維族（綁定 1 個變數）
  Pair(Int32, Int32, Int32)
  Fst(Int32)
  Snd(Int32)
  UnitTy
  Star
  EmptyTy
  /// Absurd(C, e)
  Absurd(Int32, Int32)
  BoolTy
  Tt
  Ff
  /// If(C, s, t, e)：C 綁定 1 個變數
  If(Int32, Int32, Int32, Int32)
  NatTy
  Zero
  Succ(Int32)
  /// NatRec(C, z, s, n)：C 綁定 1 個變數；s 綁定 2 個變數（指標 1 = 前驅，指標 0 = 歸納假設）
  NatRec(Int32, Int32, Int32, Int32)
  IdTy(Int32, Int32, Int32)
  Refl(Int32)
  /// J(C, d, p)：C 綁定 3 個變數（x, y, q）；d 綁定 1 個變數
  J(Int32, Int32, Int32)
}

///|
pub extend Node with Eq::{equal, not_equal}

///|
pub extend Node with Hash::{hash, hash_combine}

///|
/// 遮罩第 63 位為「黏滯位」：表示存在指標 ≥ 63 的自由變數（此時低位為保守上界）。
const TOP : UInt64 = 0x8000000000000000UL

///|
const FLAG_BETA : Int32 = 1

///|
const FLAG_ETA : Int32 = 2

///|
const SIZE_CAP : Int32 = 1000000000

///|
pub(all) struct Arena {
  nodes : Array[Node]
  table : Map[Node, Int32]
  fv : Array[UInt64]
  flags : Array[Int32]
  size : Array[Int32]
  shift_memo : Map[(Int32, Int32, Int32), Int32]
  subst_memo : Map[(Int32, Int32, Int32), Int32]
  reducts_beta : Map[Int32, Array[Int32]]
  reducts_beta_eta : Map[Int32, Array[Int32]]
  cd_memo : Map[Int32, Int32]
  /// 遙測：駐留命中數、遮罩快速路徑命中數、實際收縮次數
  mut hits : Int32
  mut fast_paths : Int32
  mut contractions : Int32
}

///|
pub fn Arena::new() -> Arena {
  {
    nodes: [],
    table: Map([]),
    fv: [],
    flags: [],
    size: [],
    shift_memo: Map([]),
    subst_memo: Map([]),
    reducts_beta: Map([]),
    reducts_beta_eta: Map([]),
    cd_memo: Map([]),
    hits: 0,
    fast_paths: 0,
    contractions: 0,
  }
}

///|
/// 以「主前提優先」次序走訪子項並重建節點；回呼參數為（子項，該位置綁定的變數個數）。
/// 主前提優先使所有計算規則的左式成為 left-normal，令最左最外策略為正規化策略。
pub fn map_children(n : Node, f : (Int32, Int32) -> Int32) -> Node {
  match n {
    Var(_)
    | Univ(_)
    | UnitTy
    | Star
    | EmptyTy
    | BoolTy
    | Tt
    | Ff
    | NatTy
    | Zero => n
    Pi(a, b) => {
      let a2 = f(a, 0)
      Pi(a2, f(b, 1))
    }
    Lam(a, b) => {
      let a2 = f(a, 0)
      Lam(a2, f(b, 1))
    }
    App(g, a) => {
      let g2 = f(g, 0)
      App(g2, f(a, 0))
    }
    Sigma(a, b) => {
      let a2 = f(a, 0)
      Sigma(a2, f(b, 1))
    }
    Pair(a, b, t) => {
      let a2 = f(a, 0)
      let b2 = f(b, 0)
      Pair(a2, b2, f(t, 1))
    }
    Fst(p) => Fst(f(p, 0))
    Snd(p) => Snd(f(p, 0))
    Absurd(c, e) => {
      let e2 = f(e, 0)
      Absurd(f(c, 0), e2)
    }
    If(c, s, t, e) => {
      let s2 = f(s, 0)
      let c2 = f(c, 1)
      let t2 = f(t, 0)
      If(c2, s2, t2, f(e, 0))
    }
    Succ(m) => Succ(f(m, 0))
    NatRec(c, z, s, m) => {
      let m2 = f(m, 0)
      let c2 = f(c, 1)
      let z2 = f(z, 0)
      NatRec(c2, z2, f(s, 2), m2)
    }
    IdTy(a, x, y) => {
      let a2 = f(a, 0)
      let x2 = f(x, 0)
      IdTy(a2, x2, f(y, 0))
    }
    Refl(a) => Refl(f(a, 0))
    J(c, d, p) => {
      let p2 = f(p, 0)
      let c2 = f(c, 3)
      J(c2, f(d, 1), p2)
    }
  }
}

///|
/// 子項清單（主前提優先次序），元素為（子項，綁定數）。
pub fn children(n : Node) -> Array[(Int32, Int32)] {
  let out : Array[(Int32, Int32)] = []
  let _ = map_children(n, fn(c, b) {
    out.push((c, b))
    c
  })
  out
}

///|
/// 將第 `i` 個子項（主前提優先次序）換成 `r`。
pub fn with_child(n : Node, i : Int32, r : Int32) -> Node {
  let idx = Ref(0)
  map_children(n, fn(c, _b) {
    let k = idx.val
    idx.val = k + 1
    if k == i {
      r
    } else {
      c
    }
  })
}

///|
fn lower_mask(m : UInt64, binders : Int32) -> UInt64 {
  let mut r = m
  for _ in 0..<binders {
    r = (r >> 1) | (r & TOP)
  }
  r
}

///|
/// 駐留建構：相同結構恆回傳相同編號。
pub fn Arena::mk(self : Arena, n : Node) -> Int32 {
  match self.table.get(n) {
    Some(i) => {
      self.hits += 1
      i
    }
    None => {
      let id = self.nodes.length()
      let mut mask : UInt64 = 0UL
      let mut flag = 0
      let mut sz = 1
      match n {
        Var(i) => mask = if i < 63 { 1UL << i } else { TOP }
        _ => {
          let _ = map_children(n, fn(c, b) {
            mask = mask | lower_mask(self.fv[c], b)
            flag = flag | self.flags[c]
            sz = if sz + self.size[c] > SIZE_CAP {
              SIZE_CAP
            } else {
              sz + self.size[c]
            }
            c
          })
        }
      }
      self.nodes.push(n)
      self.fv.push(mask)
      self.flags.push(flag)
      self.size.push(sz)
      self.table[n] = id
      if self.is_beta_head(id) {
        self.flags[id] = self.flags[id] | FLAG_BETA
      }
      if self.is_eta_head(id) {
        self.flags[id] = self.flags[id] | FLAG_ETA
      }
      id
    }
  }
}

///|
pub fn Arena::node(self : Arena, t : Int32) -> Node {
  self.nodes[t]
}

///|
/// O(1)：項內是否存在 β/ι 可約式。
pub fn Arena::has_beta(self : Arena, t : Int32) -> Bool {
  (self.flags[t] & FLAG_BETA) != 0
}

///|
/// O(1)：項內是否存在 η 可約式。
pub fn Arena::has_eta(self : Arena, t : Int32) -> Bool {
  (self.flags[t] & FLAG_ETA) != 0
}

///|
/// O(1)：β-正規形判定。
pub fn Arena::is_beta_normal(self : Arena, t : Int32) -> Bool {
  (self.flags[t] & FLAG_BETA) == 0
}

///|
pub fn Arena::tree_size(self : Arena, t : Int32) -> Int32 {
  self.size[t]
}

///|
/// DAG 中自 `t` 可達的相異節點數（共享後的實際記憶體佔用）。
pub fn Arena::dag_size(self : Arena, t : Int32) -> Int32 {
  let seen : Map[Int32, Unit] = Map([])
  let stack = [t]
  while stack.pop() is Some(x) {
    if seen.contains(x) {
      continue
    }
    seen[x] = ()
    let _ = map_children(self.nodes[x], fn(c, _b) {
      stack.push(c)
      c
    })
  }
  seen.length()
}

///|
/// O(1)：是否為閉項（黏滯位為零時精確）。
pub fn Arena::is_closed(self : Arena, t : Int32) -> Bool {
  self.fv[t] == 0UL
}

///|
/// 指標 `k` 是否自由出現於 `t`。遮罩位為 0 ⇒ O(1) 否定；黏滯位為 0 ⇒ O(1) 肯定。
pub fn Arena::occurs(self : Arena, t : Int32, k : Int32) -> Bool {
  let m = self.fv[t]
  if k < 63 {
    if ((m >> k) & 1UL) == 0UL {
      self.fast_paths += 1
      return false
    }
    if (m & TOP) == 0UL {
      self.fast_paths += 1
      return true
    }
  } else if (m & TOP) == 0UL {
    self.fast_paths += 1
    return false
  }
  match self.nodes[t] {
    Var(i) => i == k
    n => {
      let mut found = false
      let _ = map_children(n, fn(c, b) {
        if !found && self.occurs(c, k + b) {
          found = true
        }
        c
      })
      found
    }
  }
}

///|
/// `t` 是否不含任何 ≥ c 的自由指標（保守：回傳 true 時必然成立）。
fn Arena::no_free_at_or_above(self : Arena, t : Int32, c : Int32) -> Bool {
  let m = self.fv[t]
  if c >= 63 {
    (m & TOP) == 0UL
  } else {
    m >> c == 0UL
  }
}

///|
/// 位移：將 ≥ c 的自由指標加上 d（d 可為負）。
pub fn Arena::shift(self : Arena, t : Int32, d : Int32, c : Int32) -> Int32 {
  if d == 0 || self.no_free_at_or_above(t, c) {
    self.fast_paths += 1
    return t
  }
  let key = (t, d, c)
  match self.shift_memo.get(key) {
    Some(r) => r
    None => {
      let r = match self.nodes[t] {
        Var(i) => if i >= c { self.mk(Var(i + d)) } else { t }
        n => self.mk(map_children(n, fn(ch, b) { self.shift(ch, d, c + b) }))
      }
      self.shift_memo[key] = r
      r
    }
  }
}

///|
/// 代換 t[s/k]：以 s 取代指標 k，並將 > k 的自由指標減一。
pub fn Arena::subst(self : Arena, t : Int32, k : Int32, s : Int32) -> Int32 {
  if self.no_free_at_or_above(t, k) {
    self.fast_paths += 1
    return t
  }
  let key = (t, k, s)
  match self.subst_memo.get(key) {
    Some(r) => r
    None => {
      let r = match self.nodes[t] {
        Var(i) =>
          if i == k {
            self.shift(s, k, 0)
          } else if i > k {
            self.mk(Var(i - 1))
          } else {
            t
          }
        n => self.mk(map_children(n, fn(ch, b) { self.subst(ch, k + b, s) }))
      }
      self.subst_memo[key] = r
      r
    }
  }
}

///|
pub fn Arena::lam(self : Arena, a : Int32, b : Int32) -> Int32 {
  self.mk(Lam(a, b))
}

///|
pub fn Arena::app(self : Arena, f : Int32, a : Int32) -> Int32 {
  self.mk(App(f, a))
}

///|
pub fn Arena::numeral(self : Arena, n : Int32) -> Int32 {
  let mut r = self.mk(Zero)
  for _ in 0..<n {
    r = self.mk(Succ(r))
  }
  r
}

///|
/// 若為數字正規形 S^n 0 則回傳 n。
pub fn Arena::as_numeral(self : Arena, t : Int32) -> Int32? {
  let mut cur = t
  let mut n = 0
  while true {
    match self.nodes[cur] {
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
/// Church 數字 λs:A. λz:A. s^n z（標註 A 由呼叫者提供）。
pub fn Arena::church(self : Arena, n : Int32, ann : Int32) -> Int32 {
  let mut body = self.mk(Var(0))
  for _ in 0..<n {
    body = self.mk(App(self.mk(Var(1)), body))
  }
  self.mk(Lam(ann, self.mk(Lam(ann, body))))
}

///|
/// 以 de Bruijn 記號輸出。
pub fn Arena::show(self : Arena, t : Int32) -> String {
  let sb = StringBuilder()
  self.write(sb, t)
  sb.to_string()
}

///|
fn Arena::write(self : Arena, sb : StringBuilder, t : Int32) -> Unit {
  match self.nodes[t] {
    Var(i) => sb.write_string("#\{i}")
    Univ(l) => sb.write_string("U\{l}")
    Pi(a, b) => self.write_form(sb, "Π", [a, b])
    Lam(a, b) => self.write_form(sb, "λ", [a, b])
    App(f, a) => self.write_form(sb, "", [f, a])
    Sigma(a, b) => self.write_form(sb, "Σ", [a, b])
    Pair(a, b, _) => self.write_form(sb, "pair", [a, b])
    Fst(p) => self.write_form(sb, "fst", [p])
    Snd(p) => self.write_form(sb, "snd", [p])
    UnitTy => sb.write_string("Unit")
    Star => sb.write_string("*")
    EmptyTy => sb.write_string("Empty")
    Absurd(_, e) => self.write_form(sb, "absurd", [e])
    BoolTy => sb.write_string("Bool")
    Tt => sb.write_string("tt")
    Ff => sb.write_string("ff")
    If(_, s, x, y) => self.write_form(sb, "if", [s, x, y])
    NatTy => sb.write_string("Nat")
    Zero => sb.write_string("0")
    Succ(_) =>
      match self.as_numeral(t) {
        Some(n) => sb.write_string("\{n}")
        None => if self.nodes[t] is Succ(m) { self.write_form(sb, "S", [m]) }
      }
    NatRec(_, z, s, m) => self.write_form(sb, "rec", [z, s, m])
    IdTy(a, x, y) => self.write_form(sb, "Id", [a, x, y])
    Refl(a) => self.write_form(sb, "refl", [a])
    J(_, d, p) => self.write_form(sb, "J", [d, p])
  }
}

///|
fn Arena::write_form(
  self : Arena,
  sb : StringBuilder,
  head : String,
  args : Array[Int32],
) -> Unit {
  sb.write_string("(")
  sb.write_string(head)
  let mut first = head == ""
  for a in args {
    if !first {
      sb.write_string(" ")
    }
    first = false
    self.write(sb, a)
  }
  sb.write_string(")")
}
