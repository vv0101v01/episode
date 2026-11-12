///|
fn shift(t : Tm, by : Int32, cutoff : Int32) -> Tm {
  match t {
    Var(i) => if i >= cutoff { Var(i + by) } else { Var(i) }
    Lam(a, b) => Lam(a, shift(b, by, cutoff + 1))
    App(f, x) => App(shift(f, by, cutoff), shift(x, by, cutoff))
    Pair(a, b) => Pair(shift(a, by, cutoff), shift(b, by, cutoff))
    LetPair(e, b) => LetPair(shift(e, by, cutoff), shift(b, by, cutoff + 2))
    Unit(m) => Unit(m)
    LetUnit(e, b) => LetUnit(shift(e, by, cutoff), shift(b, by, cutoff))
    WithPair(a, b) => WithPair(shift(a, by, cutoff), shift(b, by, cutoff))
    Fst(e) => Fst(shift(e, by, cutoff))
    Snd(e) => Snd(shift(e, by, cutoff))
    Inl(p, e) => Inl(p, shift(e, by, cutoff))
    Inr(p, e) => Inr(p, shift(e, by, cutoff))
    Case(e, l, r) =>
      Case(
        shift(e, by, cutoff),
        shift(l, by, cutoff + 1),
        shift(r, by, cutoff + 1),
      )
    Susp(m, e) => Susp(m, shift(e, by, cutoff))
    Force(e) => Force(shift(e, by, cutoff))
    Down(k, e) => Down(k, shift(e, by, cutoff))
    LetDown(e, b) => LetDown(shift(e, by, cutoff), shift(b, by, cutoff + 1))
  }
}

///|
/// t[s/j]，並把高於 j 的指標下移一格。
fn subst(t : Tm, j : Int32, s : Tm) -> Tm {
  match t {
    Var(i) =>
      if i == j {
        shift(s, j, 0)
      } else if i > j {
        Var(i - 1)
      } else {
        Var(i)
      }
    Lam(a, b) => Lam(a, subst(b, j + 1, s))
    App(f, x) => App(subst(f, j, s), subst(x, j, s))
    Pair(a, b) => Pair(subst(a, j, s), subst(b, j, s))
    LetPair(e, b) => LetPair(subst(e, j, s), subst(b, j + 2, s))
    Unit(m) => Unit(m)
    LetUnit(e, b) => LetUnit(subst(e, j, s), subst(b, j, s))
    WithPair(a, b) => WithPair(subst(a, j, s), subst(b, j, s))
    Fst(e) => Fst(subst(e, j, s))
    Snd(e) => Snd(subst(e, j, s))
    Inl(p, e) => Inl(p, subst(e, j, s))
    Inr(p, e) => Inr(p, subst(e, j, s))
    Case(e, l, r) =>
      Case(subst(e, j, s), subst(l, j + 1, s), subst(r, j + 1, s))
    Susp(m, e) => Susp(m, subst(e, j, s))
    Force(e) => Force(subst(e, j, s))
    Down(k, e) => Down(k, subst(e, j, s))
    LetDown(e, b) => LetDown(subst(e, j, s), subst(b, j + 1, s))
  }
}

///|
/// 頂層計算規則（每個連接詞的「引入後消除」）。
fn head_step(t : Tm) -> Tm? {
  match t {
    App(Lam(_, b), x) => Some(subst(b, 0, x))
    LetPair(Pair(a, b), body) =>
      // 綁定次序：a 為外層（指標 1），b 為內層（指標 0）
      Some(subst(subst(body, 0, shift(b, 1, 0)), 0, a))
    LetUnit(Unit(_), body) => Some(body)
    Fst(WithPair(a, _)) => Some(a)
    Snd(WithPair(_, b)) => Some(b)
    Case(Inl(_, e), l, _) => Some(subst(l, 0, e))
    Case(Inr(_, e), _, r) => Some(subst(r, 0, e))
    Force(Susp(_, e)) => Some(e)
    LetDown(Down(_, e), body) => Some(subst(body, 0, e))
    _ => None
  }
}

///|
/// 一步約簡（最左最外，可深入任何位置）。
pub fn step(t : Tm) -> Tm? {
  match head_step(t) {
    Some(r) => return Some(r)
    None => ()
  }
  match t {
    Var(_) | Unit(_) => None
    Lam(a, b) => step(b).map(fn(x) { Lam(a, x) })
    App(f, x) =>
      match step(f) {
        Some(f2) => Some(App(f2, x))
        None => step(x).map(fn(x2) { App(f, x2) })
      }
    Pair(a, b) =>
      match step(a) {
        Some(a2) => Some(Pair(a2, b))
        None => step(b).map(fn(b2) { Pair(a, b2) })
      }
    LetPair(e, b) =>
      match step(e) {
        Some(e2) => Some(LetPair(e2, b))
        None => step(b).map(fn(b2) { LetPair(e, b2) })
      }
    LetUnit(e, b) =>
      match step(e) {
        Some(e2) => Some(LetUnit(e2, b))
        None => step(b).map(fn(b2) { LetUnit(e, b2) })
      }
    WithPair(a, b) =>
      match step(a) {
        Some(a2) => Some(WithPair(a2, b))
        None => step(b).map(fn(b2) { WithPair(a, b2) })
      }
    Fst(e) => step(e).map(fn(x) { Fst(x) })
    Snd(e) => step(e).map(fn(x) { Snd(x) })
    Inl(p, e) => step(e).map(fn(x) { Inl(p, x) })
    Inr(p, e) => step(e).map(fn(x) { Inr(p, x) })
    Case(e, l, r) =>
      match step(e) {
        Some(e2) => Some(Case(e2, l, r))
        None =>
          match step(l) {
            Some(l2) => Some(Case(e, l2, r))
            None => step(r).map(fn(r2) { Case(e, l, r2) })
          }
      }
    Susp(m, e) => step(e).map(fn(x) { Susp(m, x) })
    Force(e) => step(e).map(fn(x) { Force(x) })
    Down(k, e) => step(e).map(fn(x) { Tm::Down(k, x) })
    LetDown(e, b) =>
      match step(e) {
        Some(e2) => Some(LetDown(e2, b))
        None => step(b).map(fn(b2) { LetDown(e, b2) })
      }
  }
}

///|
/// 正規化；回傳（結果, 步數, 是否已達正規形）。
pub fn normalize(t : Tm, fuel~ : Int32) -> (Tm, Int32, Bool) {
  let mut cur = t
  let mut steps = 0
  while steps < fuel {
    match step(cur) {
      Some(next) => {
        cur = next
        steps += 1
      }
      None => return (cur, steps, true)
    }
  }
  (cur, steps, false)
}

///|
pub fn tm_size(t : Tm) -> Int32 {
  match t {
    Var(_) | Unit(_) => 1
    Lam(_, b)
    | Fst(b)
    | Snd(b)
    | Inl(_, b)
    | Inr(_, b)
    | Susp(_, b)
    | Force(b)
    | Down(_, b) => 1 + tm_size(b)
    App(a, b)
    | Pair(a, b)
    | LetPair(a, b)
    | LetUnit(a, b)
    | WithPair(a, b)
    | LetDown(a, b) => 1 + tm_size(a) + tm_size(b)
    Case(e, l, r) => 1 + tm_size(e) + tm_size(l) + tm_size(r)
  }
}
