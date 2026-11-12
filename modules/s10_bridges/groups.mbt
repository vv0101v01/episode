///|
/// 橋接 S4 → S3：把 Knuth–Bendix 完備化得到的有限群（正規形列舉）轉成乘法表，
/// 即 S3 的 `FinGroup`。元素 0 為單位元（空字）。完備化未收斂或列舉超限時回傳 None。
pub fn group_table(
  pres : @s4.Presentation,
  max_rules~ : Int32,
  limit~ : Int32,
) -> Array[Array[Int32]]? {
  let rws = pres.complete(max_rules~)
  if !rws.convergent {
    return None
  }
  let (elems, done) = rws.enumerate(limit~)
  if !done {
    return None
  }
  let index : Map[String, Int32] = Map([])
  for i in 0..<elems.length() {
    index[@s4.show_word(elems[i])] = i
  }
  let table : Array[Array[Int32]] = []
  for a in elems {
    let row : Array[Int32] = []
    for b in elems {
      let nf = rws.normal_form(@s4.concat(a, b))
      row.push(index.get(@s4.show_word(nf)).unwrap_or(-1))
    }
    table.push(row)
  }
  Some(table)
}

///|
/// S₃ = ⟨a, b | a², b³, (ab)²⟩ 與 ℤ/n = ⟨a | aⁿ⟩ 的表現。
pub fn s3_presentation() -> @s4.Presentation {
  { ngens: 2, relators: [[0, 0], [2, 2, 2], [0, 2, 0, 2]], }
}

///|
pub fn cyclic_presentation(n : Int32) -> @s4.Presentation {
  let r : Array[Int32] = []
  for _ in 0..<n {
    r.push(0)
  }
  { ngens: 1, relators: [r], }
}

///|
/// 有限 G-集：`act[g][x]` = g·x（左作用）。
pub(all) struct GSet {
  size : Int32
  act : Array[Array[Int32]]
}

///|
/// 左作用公理：e·x = x，(gh)·x = g·(h·x)。
pub fn GSet::is_action(self : GSet, mul : Array[Array[Int32]]) -> Bool {
  let n = mul.length()
  for x in 0..<self.size {
    if self.act[0][x] != x {
      return false
    }
    for g in 0..<n {
      for h in 0..<n {
        if self.act[mul[g][h]][x] != self.act[g][self.act[h][x]] {
          return false
        }
      }
    }
  }
  true
}

///|
/// 由一組元素生成的子群（元素索引，遞增排序）。
pub fn subgroup(mul : Array[Array[Int32]], gens : Array[Int32]) -> Array[Int32] {
  let inside = Array::make(mul.length(), false)
  inside[0] = true
  let queue : Array[Int32] = [0]
  let mut head = 0
  while head < queue.length() {
    let x = queue[head]
    head += 1
    for g in gens {
      let y = mul[x][g]
      if !inside[y] {
        inside[y] = true
        queue.push(y)
      }
    }
  }
  let out : Array[Int32] = []
  for i in 0..<mul.length() {
    if inside[i] {
      out.push(i)
    }
  }
  out
}

///|
/// 沿 H ≤ G 的限制函子 Res：把 G-集看成 H-集（H 的元素以 `sub` 中的位置重新編號）。
pub fn restrict(y : GSet, sub : Array[Int32]) -> GSet {
  let act : Array[Array[Int32]] = []
  for h in sub {
    act.push(y.act[h])
  }
  { size: y.size, act, }
}

///|
/// 子群的乘法表（以 `sub` 中的位置編號；`sub[0]` 為單位元）。
pub fn subgroup_table(
  mul : Array[Array[Int32]],
  sub : Array[Int32],
) -> Array[Array[Int32]] {
  let pos = Array::make(mul.length(), -1)
  for i in 0..<sub.length() {
    pos[sub[i]] = i
  }
  let t : Array[Array[Int32]] = []
  for a in sub {
    let row : Array[Int32] = []
    for b in sub {
      row.push(pos[mul[a][b]])
    }
    t.push(row)
  }
  t
}

///|
/// 陪集 G/K 上的左乘作用。
pub fn coset_action(mul : Array[Array[Int32]], k : Array[Int32]) -> GSet {
  let n = mul.length()
  let cls = Array::make(n, -1)
  let mut count = 0
  for g in 0..<n {
    if cls[g] < 0 {
      for h in k {
        cls[mul[g][h]] = count
      }
      count += 1
    }
  }
  let rep = Array::make(count, 0)
  for g in 0..<n {
    rep[cls[g]] = g
  }
  let act : Array[Array[Int32]] = []
  for g in 0..<n {
    let row : Array[Int32] = []
    for c in 0..<count {
      row.push(cls[mul[g][rep[c]]])
    }
    act.push(row)
  }
  { size: count, act, }
}

///|
/// 等變映射數 |Hom_G(X, Y)| = ∏_{軌道 O ⊆ X} #{y ∈ Y : Stab(x_O) ⊆ Stab(y)}。
pub fn count_equivariant(x : GSet, y : GSet) -> Int32 {
  let n = x.act.length()
  let seen = Array::make(x.size, false)
  let mut total = 1
  for x0 in 0..<x.size {
    if seen[x0] {
      continue
    }
    for g in 0..<n {
      seen[x.act[g][x0]] = true
    }
    let mut choices = 0
    for y0 in 0..<y.size {
      let mut ok = true
      for g in 0..<n {
        if x.act[g][x0] == x0 && y.act[g][y0] != y0 {
          ok = false
          break
        }
      }
      if ok {
        choices += 1
      }
    }
    total *= choices
  }
  total
}

///|
/// 群的逆元表。
pub fn inverses(mul : Array[Array[Int32]]) -> Array[Int32] {
  @s3.FinGroup::from_table(mul).inv
}

///|
/// X ⊔ {*}：添一個不動點。
pub fn GSet::with_fixed_point(self : GSet) -> GSet {
  let act : Array[Array[Int32]] = []
  for row in self.act {
    let r = row.copy()
    r.push(self.size)
    act.push(r)
  }
  { size: self.size + 1, act, }
}

///|
/// 元素在子群列表中的位置（不在子群內為 -1）。
pub fn positions(order : Int32, sub : Array[Int32]) -> Array[Int32] {
  let pos = Array::make(order, -1)
  for i in 0..<sub.length() {
    pos[sub[i]] = i
  }
  pos
}
