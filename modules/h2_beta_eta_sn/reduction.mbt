///|
/// 頭部 β/ι 可約式判定（計算規則的左式：消除子作用於引入子）。
fn Arena::is_beta_head(self : Arena, t : Int32) -> Bool {
  match self.nodes[t] {
    App(f, _) => self.nodes[f] is Lam(_, _)
    Fst(p) | Snd(p) => self.nodes[p] is Pair(_, _, _)
    If(_, s, _, _) => self.nodes[s] is (Tt | Ff)
    NatRec(_, _, _, m) => self.nodes[m] is (Zero | Succ(_))
    J(_, _, p) => self.nodes[p] is Refl(_)
    _ => false
  }
}

///|
/// 頭部 η 可約式判定（唯一性規則的收縮方向）：
/// λ:A. (f↑ #0) 且 #0∉FV(f)；pair(fst p, snd p)。
fn Arena::is_eta_head(self : Arena, t : Int32) -> Bool {
  match self.nodes[t] {
    Lam(_, b) =>
      match self.nodes[b] {
        App(g, v) => self.nodes[v] is Var(0) && !self.occurs(g, 0)
        _ => false
      }
    Pair(a, b, _) =>
      match (self.nodes[a], self.nodes[b]) {
        (Fst(p), Snd(q)) => p == q
        _ => false
      }
    _ => false
  }
}

///|
/// 頭部 β/ι 收縮（計算規則）。
pub fn Arena::contract_head(self : Arena, t : Int32) -> Int32? {
  if !self.is_beta_head(t) {
    return None
  }
  self.contractions += 1
  match self.nodes[t] {
    App(f, a) =>
      match self.nodes[f] {
        Lam(_, b) => Some(self.subst(b, 0, a))
        _ => None
      }
    Fst(p) =>
      match self.nodes[p] {
        Pair(a, _, _) => Some(a)
        _ => None
      }
    Snd(p) =>
      match self.nodes[p] {
        Pair(_, b, _) => Some(b)
        _ => None
      }
    If(_, s, x, y) =>
      match self.nodes[s] {
        Tt => Some(x)
        Ff => Some(y)
        _ => None
      }
    NatRec(c, z, s, m) =>
      match self.nodes[m] {
        Zero => Some(z)
        Succ(pred) => {
          let ih = self.mk(NatRec(c, z, s, pred))
          let s1 = self.subst(s, 0, self.shift(ih, 1, 0))
          Some(self.subst(s1, 0, pred))
        }
        _ => None
      }
    J(_, d, p) =>
      match self.nodes[p] {
        Refl(a) => Some(self.subst(d, 0, a))
        _ => None
      }
    _ => None
  }
}

///|
/// 頭部 η 收縮（唯一性規則的收縮方向）。
pub fn Arena::eta_head(self : Arena, t : Int32) -> Int32? {
  if !self.is_eta_head(t) {
    return None
  }
  match self.nodes[t] {
    Lam(_, b) =>
      match self.nodes[b] {
        App(g, _) => Some(self.shift(g, -1, 0))
        _ => None
      }
    Pair(a, _, _) =>
      match self.nodes[a] {
        Fst(p) => Some(p)
        _ => None
      }
    _ => None
  }
}

///|
/// 一步約簡的全部約簡結果（去重後的集合）；`eta=true` 時包含 η 收縮。
pub fn Arena::reducts(self : Arena, t : Int32, eta~ : Bool) -> Array[Int32] {
  let relevant = if eta { self.flags[t] != 0 } else { self.has_beta(t) }
  if !relevant {
    return []
  }
  let memo = if eta { self.reducts_beta_eta } else { self.reducts_beta }
  match memo.get(t) {
    Some(r) => return r
    None => ()
  }
  let out : Array[Int32] = []
  let seen : Map[Int32, Unit] = Map([])
  let add = fn(r : Int32) {
    if !seen.contains(r) {
      seen[r] = ()
      out.push(r)
    }
  }
  match self.contract_head(t) {
    Some(r) => add(r)
    None => ()
  }
  if eta {
    match self.eta_head(t) {
      Some(r) => add(r)
      None => ()
    }
  }
  let n = self.nodes[t]
  let kids = children(n)
  for i in 0..<kids.length() {
    let (c, _) = kids[i]
    for r in self.reducts(c, eta~) {
      add(self.mk(with_child(n, i, r)))
    }
  }
  memo[t] = out
  out
}

///|
/// 最左最外（主前提優先）一步 β/ι 約簡 —— 正規化策略。
pub fn Arena::step_leftmost(self : Arena, t : Int32) -> Int32? {
  if !self.has_beta(t) {
    return None
  }
  match self.contract_head(t) {
    Some(r) => return Some(r)
    None => ()
  }
  let n = self.nodes[t]
  let kids = children(n)
  for i in 0..<kids.length() {
    let (c, _) = kids[i]
    if self.has_beta(c) {
      match self.step_leftmost(c) {
        Some(r) => return Some(self.mk(with_child(n, i, r)))
        None => ()
      }
    }
  }
  None
}

///|
/// 永續策略 F∞ 的一步（Barendregt；推廣至含 ι 規則與標註的正交系統）：
/// 取最左最外可約式；若其收縮會抹除某個尚非正規形的子項，則改於該子項內遞迴，
/// 否則收縮之。定理：t 強正規化 ⇔ F∞ 自 t 起終止，且此時 F∞ 路徑為最長約簡。
pub fn Arena::step_perpetual(self : Arena, t : Int32) -> Int32? {
  if !self.has_beta(t) {
    return None
  }
  if self.is_beta_head(t) {
    match self.nodes[t] {
      App(f, a) =>
        if self.nodes[f] is Lam(ann, b) {
          if self.has_beta(ann) {
            if self.step_perpetual(ann) is Some(r) {
              return Some(self.mk(App(self.mk(Lam(r, b)), a)))
            }
          }
          if !self.occurs(b, 0) && self.has_beta(a) {
            if self.step_perpetual(a) is Some(r) {
              return Some(self.mk(App(f, r)))
            }
          }
        }
      Fst(p) =>
        if self.nodes[p] is Pair(a, b, fam) {
          if self.has_beta(b) {
            if self.step_perpetual(b) is Some(r) {
              return Some(self.mk(Fst(self.mk(Pair(a, r, fam)))))
            }
          }
          if self.has_beta(fam) {
            if self.step_perpetual(fam) is Some(r) {
              return Some(self.mk(Fst(self.mk(Pair(a, b, r)))))
            }
          }
        }
      Snd(p) =>
        if self.nodes[p] is Pair(a, b, fam) {
          if self.has_beta(a) {
            if self.step_perpetual(a) is Some(r) {
              return Some(self.mk(Snd(self.mk(Pair(r, b, fam)))))
            }
          }
          if self.has_beta(fam) {
            if self.step_perpetual(fam) is Some(r) {
              return Some(self.mk(Snd(self.mk(Pair(a, b, r)))))
            }
          }
        }
      If(c, s, x, y) => {
        if self.has_beta(c) {
          if self.step_perpetual(c) is Some(r) {
            return Some(self.mk(If(r, s, x, y)))
          }
        }
        let taken_then = self.nodes[s] is Tt
        if taken_then && self.has_beta(y) {
          if self.step_perpetual(y) is Some(r) {
            return Some(self.mk(If(c, s, x, r)))
          }
        }
        if !taken_then && self.has_beta(x) {
          if self.step_perpetual(x) is Some(r) {
            return Some(self.mk(If(c, s, r, y)))
          }
        }
      }
      NatRec(c, z, s, m) => {
        let at_zero = self.nodes[m] is Zero
        let ih_erased = at_zero || !self.occurs(s, 0)
        if ih_erased && self.has_beta(c) {
          if self.step_perpetual(c) is Some(r) {
            return Some(self.mk(NatRec(r, z, s, m)))
          }
        }
        if at_zero && self.has_beta(s) {
          if self.step_perpetual(s) is Some(r) {
            return Some(self.mk(NatRec(c, z, r, m)))
          }
        }
        if !at_zero {
          if ih_erased && self.has_beta(z) {
            if self.step_perpetual(z) is Some(r) {
              return Some(self.mk(NatRec(c, r, s, m)))
            }
          }
          if ih_erased && !self.occurs(s, 1) && self.has_beta(m) {
            if self.step_perpetual(m) is Some(r) {
              return Some(self.mk(NatRec(c, z, s, r)))
            }
          }
        }
      }
      J(c, d, p) => {
        if self.has_beta(c) {
          if self.step_perpetual(c) is Some(r) {
            return Some(self.mk(J(r, d, p)))
          }
        }
        if !self.occurs(d, 0) && self.has_beta(p) {
          if self.step_perpetual(p) is Some(r) {
            return Some(self.mk(J(c, d, r)))
          }
        }
      }
      _ => ()
    }
    return self.contract_head(t)
  }
  let n = self.nodes[t]
  let kids = children(n)
  for i in 0..<kids.length() {
    let (c, _) = kids[i]
    if self.has_beta(c) {
      match self.step_perpetual(c) {
        Some(r) => return Some(self.mk(with_child(n, i, r)))
        None => ()
      }
    }
  }
  None
}

///|
/// 策略執行結果：終項、步數、是否抵達正規形（否則為燃料耗盡）。
pub(all) struct Run {
  result : Int32
  steps : Int32
  normal : Bool
}

///|
pub fn Arena::run_leftmost(self : Arena, t : Int32, fuel~ : Int32) -> Run {
  let mut cur = t
  let mut steps = 0
  while steps < fuel {
    match self.step_leftmost(cur) {
      Some(r) => {
        cur = r
        steps += 1
      }
      None => return { result: cur, steps, normal: true, }
    }
  }
  { result: cur, steps, normal: self.is_beta_normal(cur), }
}

///|
pub fn Arena::run_perpetual(self : Arena, t : Int32, fuel~ : Int32) -> Run {
  let mut cur = t
  let mut steps = 0
  while steps < fuel {
    match self.step_perpetual(cur) {
      Some(r) => {
        cur = r
        steps += 1
      }
      None => return { result: cur, steps, normal: true, }
    }
  }
  { result: cur, steps, normal: self.is_beta_normal(cur), }
}

///|
/// Takahashi 完全展開 t*：同時收縮 t 中現存的全部 β/ι 可約式。
/// 三角性質：t ⇒ u 蘊涵 u ⇒ t*；由此得 Church–Rosser。
pub fn Arena::complete_development(self : Arena, t : Int32) -> Int32 {
  if !self.has_beta(t) {
    return t
  }
  match self.cd_memo.get(t) {
    Some(r) => return r
    None => ()
  }
  let n = self.nodes[t]
  let r = match n {
    App(f, a) =>
      match self.nodes[f] {
        Lam(_, b) =>
          self.subst(
            self.complete_development(b),
            0,
            self.complete_development(a),
          )
        _ => self.cd_congruence(n)
      }
    Fst(p) =>
      match self.nodes[p] {
        Pair(a, _, _) => self.complete_development(a)
        _ => self.cd_congruence(n)
      }
    Snd(p) =>
      match self.nodes[p] {
        Pair(_, b, _) => self.complete_development(b)
        _ => self.cd_congruence(n)
      }
    If(_, s, x, y) =>
      match self.nodes[s] {
        Tt => self.complete_development(x)
        Ff => self.complete_development(y)
        _ => self.cd_congruence(n)
      }
    NatRec(c, z, s, m) =>
      match self.nodes[m] {
        Zero => self.complete_development(z)
        Succ(pred) => {
          let c2 = self.complete_development(c)
          let z2 = self.complete_development(z)
          let s2 = self.complete_development(s)
          let p2 = self.complete_development(pred)
          let ih = self.mk(NatRec(c2, z2, s2, p2))
          let s3 = self.subst(s2, 0, self.shift(ih, 1, 0))
          self.subst(s3, 0, p2)
        }
        _ => self.cd_congruence(n)
      }
    J(_, d, p) =>
      match self.nodes[p] {
        Refl(a) =>
          self.subst(
            self.complete_development(d),
            0,
            self.complete_development(a),
          )
        _ => self.cd_congruence(n)
      }
    _ => self.cd_congruence(n)
  }
  self.cd_memo[t] = r
  r
}

///|
fn Arena::cd_congruence(self : Arena, n : Node) -> Int32 {
  self.mk(map_children(n, fn(c, _b) { self.complete_development(c) }))
}

///|
/// Gross–Knuth 策略：反覆取完全展開直到正規形（共尾且正規化）。
pub fn Arena::run_gross_knuth(self : Arena, t : Int32, fuel~ : Int32) -> Run {
  let mut cur = t
  let mut rounds = 0
  while rounds < fuel && self.has_beta(cur) {
    cur = self.complete_development(cur)
    rounds += 1
  }
  { result: cur, steps: rounds, normal: self.is_beta_normal(cur), }
}

///|
/// Church–Rosser 合流見證：共同約簡項 w 及兩側各自所需的完全展開輪數。
pub(all) struct Join {
  common : Int32
  left_rounds : Int32
  right_rounds : Int32
}

///|
/// 對同源的兩個約簡結果 n1、n2 以 Gross–Knuth 序列尋找共同約簡項。
pub fn Arena::church_rosser_join(
  self : Arena,
  n1 : Int32,
  n2 : Int32,
  fuel~ : Int32,
) -> Join? {
  let left : Map[Int32, Int32] = Map([])
  let right : Map[Int32, Int32] = Map([])
  let mut a = n1
  let mut b = n2
  left[a] = 0
  right[b] = 0
  for round in 0..<(fuel + 1) {
    match right.get(a) {
      Some(j) =>
        return Some({ common: a, left_rounds: round, right_rounds: j, })
      None => ()
    }
    match left.get(b) {
      Some(i) =>
        return Some({ common: b, left_rounds: i, right_rounds: round, })
      None => ()
    }
    let a2 = self.complete_development(a)
    let b2 = self.complete_development(b)
    if a2 == a && b2 == b {
      return None
    }
    a = a2
    b = b2
    if !left.contains(a) {
      left[a] = round + 1
    }
    if !right.contains(b) {
      right[b] = round + 1
    }
  }
  None
}

///|
/// 有界可達性：x ↠ y（β/ι）是否於 `budget` 個相異項內成立。
pub fn Arena::reachable(
  self : Arena,
  x : Int32,
  y : Int32,
  budget~ : Int32,
) -> Bool {
  if x == y {
    return true
  }
  let seen : Map[Int32, Unit] = Map([])
  let queue = [x]
  seen[x] = ()
  let mut head = 0
  while head < queue.length() && seen.length() <= budget {
    let cur = queue[head]
    head += 1
    for r in self.reducts(cur, eta=false) {
      if r == y {
        return true
      }
      if !seen.contains(r) {
        seen[r] = ()
        queue.push(r)
      }
    }
  }
  false
}

///|
/// Z 性質檢驗報告（van Oostrom–Dehornoy）：對每個 a → b 驗證 b ↠ a* 且 a* ↠ b*。
pub(all) struct ZReport {
  pairs : Int32
  holds : Bool
}

///|
pub fn Arena::verify_z_property(
  self : Arena,
  a : Int32,
  budget~ : Int32,
) -> ZReport {
  let star = self.complete_development(a)
  let rs = self.reducts(a, eta=false)
  let mut ok = true
  for b in rs {
    if !self.reachable(b, star, budget~) {
      ok = false
    }
    if !self.reachable(star, self.complete_development(b), budget~) {
      ok = false
    }
  }
  { pairs: rs.length(), holds: ok, }
}

///|
/// η-正規化：反覆收縮最左 η 可約式（每步樹大小嚴格下降，故必終止）。回傳（結果，步數）。
pub fn Arena::eta_normalize(self : Arena, t : Int32) -> (Int32, Int32) {
  let mut cur = t
  let mut steps = 0
  while self.has_eta(cur) {
    match self.step_eta(cur) {
      Some(r) => {
        cur = r
        steps += 1
      }
      None => break
    }
  }
  (cur, steps)
}

///|
fn Arena::step_eta(self : Arena, t : Int32) -> Int32? {
  if !self.has_eta(t) {
    return None
  }
  match self.eta_head(t) {
    Some(r) => return Some(r)
    None => ()
  }
  let n = self.nodes[t]
  let kids = children(n)
  for i in 0..<kids.length() {
    let (c, _) = kids[i]
    if self.has_eta(c) {
      match self.step_eta(c) {
        Some(r) => return Some(self.mk(with_child(n, i, r)))
        None => ()
      }
    }
  }
  None
}
