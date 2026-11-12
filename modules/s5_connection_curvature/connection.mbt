///|
/// Module S5 — 聯絡、曲率、水平分佈；群胚模型。
///
/// 底空間為 S4 的 2-複形 X；纖維 F = {0..fiber-1}；結構群 Sym(F)。
/// 聯絡把每條邊 e : u → v 對應到平行移動 τ_e : F_u → F_v（一個排列）。
/// 類型論讀法：聯絡是 X 上的類型族，τ 是 transport；平坦聯絡即基本群胚 Π₁(X) → Set 的函子。
pub(all) struct Connection {
  fiber : Int32
  tau : Array[Array[Int32]]
}

///|
pub fn perm_id(n : Int32) -> Array[Int32] {
  let p : Array[Int32] = []
  for i in 0..<n {
    p.push(i)
  }
  p
}

///|
/// 先 a 後 b。
pub fn perm_then(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let p : Array[Int32] = []
  for x in a {
    p.push(b[x])
  }
  p
}

///|
pub fn perm_inv(a : Array[Int32]) -> Array[Int32] {
  let p = Array::make(a.length(), 0)
  for i in 0..<a.length() {
    p[a[i]] = i
  }
  p
}

///|
pub fn perm_is_id(a : Array[Int32]) -> Bool {
  for i in 0..<a.length() {
    if a[i] != i {
      return false
    }
  }
  true
}

///|
/// 第 k 個排列（階乘進位制解碼；k ∈ [0, n!)）。
pub fn perm_unrank(n : Int32, k : Int32) -> Array[Int32] {
  let pool = perm_id(n)
  let out : Array[Int32] = []
  let mut fact = 1
  for i in 2..<n {
    fact *= i
  }
  let mut r = k
  let mut m = n
  while m > 0 {
    let idx = if m > 1 { r / fact } else { 0 }
    if m > 1 {
      r = r % fact
    }
    out.push(pool.remove(idx))
    m -= 1
    if m > 1 {
      fact = fact / m
    }
  }
  out
}

///|
pub fn factorial(n : Int32) -> Int32 {
  let mut f = 1
  for i in 2..<(n + 1) {
    f *= i
  }
  f
}

///|
/// 沿帶號邊路的和樂（平行移動的合成）。
pub fn Connection::holonomy(
  self : Connection,
  path : Array[Int32],
) -> Array[Int32] {
  let mut acc = perm_id(self.fiber)
  for c in path {
    let t = self.tau[c / 2]
    acc = perm_then(acc, if c % 2 == 0 { t } else { perm_inv(t) })
  }
  acc
}

///|
/// 曲率：每個面的邊界和樂（於該面的起點纖維上）。
pub fn Connection::curvature(
  self : Connection,
  x : @s4.Complex,
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for f in x.faces {
    out.push(self.holonomy(f))
  }
  out
}

///|
pub fn Connection::is_flat(self : Connection, x : @s4.Complex) -> Bool {
  for f in x.faces {
    if !perm_is_id(self.holonomy(f)) {
      return false
    }
  }
  true
}

///|
/// 規範變換 g : V → Sym(F)：τ'_e = g(u)⁻¹ ; τ_e ; g(v)。
pub fn Connection::gauge(
  self : Connection,
  x : @s4.Complex,
  g : Array[Array[Int32]],
) -> Connection {
  let tau : Array[Array[Int32]] = []
  for e in 0..<x.edges.length() {
    let (u, v) = x.edges[e]
    tau.push(perm_then(perm_then(perm_inv(g[u]), self.tau[e]), g[v]))
  }
  { fiber: self.fiber, tau, }
}

///|
/// 水平分佈（Ehresmann 聯絡）：全空間 E = V × F 中的「水平邊」集合。
/// `lifts[e]` 為底邊 e 的提升：一組 (x, y)，表示 (u, x) → (v, y)。
pub(all) struct Horizontal {
  fiber : Int32
  lifts : Array[Array[(Int32, Int32)]]
}

///|
/// 由聯絡得水平分佈。
pub fn Connection::horizontal(self : Connection) -> Horizontal {
  let lifts : Array[Array[(Int32, Int32)]] = []
  for t in self.tau {
    let l : Array[(Int32, Int32)] = []
    for x in 0..<self.fiber {
      l.push((x, t[x]))
    }
    lifts.push(l)
  }
  { fiber: self.fiber, lifts, }
}

///|
/// Ehresmann 條件：每個點對每條底邊恰有一個向前與一個向後的水平提升
/// （水平子空間與垂直子空間互補）。成立時回傳對應的聯絡。
pub fn Horizontal::to_connection(self : Horizontal) -> Connection? {
  let tau : Array[Array[Int32]] = []
  for l in self.lifts {
    let t = Array::make(self.fiber, -1)
    let hit = Array::make(self.fiber, 0)
    for pair in l {
      let (x, y) = pair
      if x < 0 || x >= self.fiber || y < 0 || y >= self.fiber || t[x] >= 0 {
        return None
      }
      t[x] = y
      hit[y] += 1
    }
    for x in 0..<self.fiber {
      if t[x] < 0 || hit[x] != 1 {
        return None
      }
    }
    tau.push(t)
  }
  Some({ fiber: self.fiber, tau, })
}

///|
/// 全空間（Grothendieck 構造 ∫τ，組合範例 6）：頂點 (v, x)；水平邊；
/// 面僅在其水平提升閉合處提升。回傳（全空間複形, 未閉合的面提升數 = 曲率缺陷數）。
pub fn Connection::total_space(
  self : Connection,
  x : @s4.Complex,
) -> (@s4.Complex, Int32) {
  let n = self.fiber
  let edges : Array[(Int32, Int32)] = []
  for e in 0..<x.edges.length() {
    let (u, v) = x.edges[e]
    for a in 0..<n {
      edges.push((u * n + a, v * n + self.tau[e][a]))
    }
  }
  let faces : Array[Array[Int32]] = []
  let mut defects = 0
  for f in x.faces {
    for a in 0..<n {
      let lifted : Array[Int32] = []
      let mut cur = a
      for c in f {
        let e = c / 2
        if c % 2 == 0 {
          lifted.push(2 * (e * n + cur))
          cur = self.tau[e][cur]
        } else {
          let back = perm_inv(self.tau[e])[cur]
          lifted.push(2 * (e * n + back) + 1)
          cur = back
        }
      }
      if cur == a {
        faces.push(lifted)
      } else {
        defects += 1
      }
    }
  }
  ({ nv: x.nv * n, edges, faces, }, defects)
}

///|
/// 連通分支數（只看 1-骨架）。
pub fn components(x : @s4.Complex) -> Int32 {
  let parent : Array[Int32] = []
  for i in 0..<x.nv {
    parent.push(i)
  }
  let find = fn(a : Int32) -> Int32 {
    let mut r = a
    while parent[r] != r {
      r = parent[r]
    }
    r
  }
  for e in x.edges {
    let (u, v) = e
    let ru = find(u)
    let rv = find(v)
    if ru != rv {
      parent[ru] = rv
    }
  }
  let mut c = 0
  for i in 0..<x.nv {
    if parent[i] == i {
      c += 1
    }
  }
  c
}

///|
/// 線性同餘偽隨機數（確定性，供生成聯絡與規範變換）。
pub(all) struct Lcg {
  mut state : Int32
}

///|
pub fn Lcg::next(self : Lcg, bound : Int32) -> Int32 {
  self.state = (self.state * 1103515245 + 12345) & 0x7fffffff
  (self.state >> 8) % bound
}

///|
pub fn random_connection(
  x : @s4.Complex,
  fiber : Int32,
  rng : Lcg,
) -> Connection {
  let tau : Array[Array[Int32]] = []
  let f = factorial(fiber)
  for _ in 0..<x.edges.length() {
    tau.push(perm_unrank(fiber, rng.next(f)))
  }
  { fiber, tau, }
}

///|
/// 純規範聯絡（平坦且和樂平凡）：τ_e = g(u)⁻¹ ; g(v)。
pub fn pure_gauge(
  x : @s4.Complex,
  g : Array[Array[Int32]],
  fiber : Int32,
) -> Connection {
  let trivial : Array[Array[Int32]] = []
  for _ in 0..<x.edges.length() {
    trivial.push(perm_id(fiber))
  }
  let c : Connection = { fiber, tau: trivial, }
  c.gauge(x, g)
}
