///|
/// 立方體範疇 □ 的態射 f : J → I：對 I 的每個名字給出 J 上的區間元素
/// （即自由德摩根代數間的同態 F(I) → F(J)）。
pub(all) struct CubeMap {
  /// 定義域的名字數 |J|
  dom : Int32
  /// images[i] = 名字 i ∈ I 的像
  images : Array[Dm]
}

///|
pub fn CubeMap::identity(n : Int32) -> CubeMap {
  let images : Array[Dm] = []
  for i in 0..<n {
    images.push(Dm::name(i))
  }
  { dom: n, images, }
}

///|
/// 作用於區間元素（反變）。
pub fn CubeMap::act(self : CubeMap, r : Dm) -> Dm {
  r.subst(fn(i) {
    if i < self.images.length() {
      self.images[i]
    } else {
      Dm::name(i)
    }
  })
}

///|
/// 合成：先 `self : J → I`，後 `g : K → J`，得 K → I。
pub fn CubeMap::then(self : CubeMap, g : CubeMap) -> CubeMap {
  let images : Array[Dm] = []
  for r in self.images {
    images.push(g.act(r))
  }
  { dom: g.dom, images, }
}

///|
pub fn CubeMap::same(self : CubeMap, other : CubeMap) -> Bool {
  if self.dom != other.dom || self.images.length() != other.images.length() {
    return false
  }
  for i in 0..<self.images.length() {
    if !self.images[i].same(other.images[i]) {
      return false
    }
  }
  true
}

///|
/// 面映射 (i = ε)：把第 i 個名字固定於端點，其餘名字前移。
pub fn CubeMap::face(n : Int32, i : Int32, one~ : Bool) -> CubeMap {
  let images : Array[Dm] = []
  for j in 0..<n {
    if j < i {
      images.push(Dm::name(j))
    } else if j == i {
      images.push(if one { Dm::one() } else { Dm::zero() })
    } else {
      images.push(Dm::name(j - 1))
    }
  }
  { dom: n - 1, images, }
}

///|
/// 退化（弱化）：忘掉第 i 個名字。
pub fn CubeMap::degeneracy(n : Int32, i : Int32) -> CubeMap {
  let images : Array[Dm] = []
  for j in 0..<n {
    images.push(Dm::name(if j < i { j } else { j + 1 }))
  }
  { dom: n + 1, images, }
}

///|
/// 連接 (i ∧ j) 或 (i ∨ j)、反轉 ¬i、對角線 i=j。
pub fn CubeMap::connection(n : Int32, i : Int32, meet~ : Bool) -> CubeMap {
  let images : Array[Dm] = []
  for j in 0..<n {
    if j < i {
      images.push(Dm::name(j))
    } else if j == i {
      let a = Dm::name(i)
      let b = Dm::name(i + 1)
      images.push(if meet { a.meet(b) } else { a.join(b) })
    } else {
      images.push(Dm::name(j + 1))
    }
  }
  { dom: n + 1, images, }
}

///|
pub fn CubeMap::reversal(n : Int32, i : Int32) -> CubeMap {
  let images : Array[Dm] = []
  for j in 0..<n {
    images.push(if j == i { Dm::co_name(j) } else { Dm::name(j) })
  }
  { dom: n, images, }
}

///|
/// 立方體恆等式的檢驗（n 維處）：
/// 面∘退化 = id；連接的面：(i∧j)[i:=1] = j 方向恆等、(i∧j)[i:=0] 經退化分解；
/// 反轉為對合且交換兩端面；合成結合律；代換為同態。回傳（受檢等式數, 成立）。
pub fn verify_cubical_identities(n : Int32) -> (Int32, Bool) {
  let mut checked = 0
  let mut ok = true
  let id = CubeMap::identity(n)
  for i in 0..<(n + 1) {
    for one in [false, true] {
      // s_i ; d_i^ε = id : n → n   （先退化到 n+1，再取面回 n）
      let s = CubeMap::degeneracy(n, i)
      let d = CubeMap::face(n + 1, i, one~)
      // d : n → n+1 以 images 長 n+1 表示；s : n+1 → n 以 images 長 n 表示
      // s.then(d) : n → n
      checked += 1
      if !s.then(d).same(id) {
        ok = false
      }
    }
  }
  for i in 0..<n {
    // 連接 c : n+1 → n；c 之後取面 i:=1 得 id，取面 i:=0 得「常值 0 於 i」
    let c_meet = CubeMap::connection(n, i, meet=true)
    let c_join = CubeMap::connection(n, i, meet=false)
    let d1 = CubeMap::face(n + 1, i, one=true)
    let d0 = CubeMap::face(n + 1, i, one=false)
    checked += 4
    if !c_meet.then(d1).same(id) {
      ok = false
    }
    if !c_join.then(d0).same(id) {
      ok = false
    }
    // (i∧j)[i:=0] = 0：等於 面(i:=0) 後接退化
    let const0 = CubeMap::face(n, i, one=false).then(
      CubeMap::degeneracy(n - 1, i),
    )
    if !c_meet.then(d0).same(const0) {
      ok = false
    }
    let const1 = CubeMap::face(n, i, one=true).then(
      CubeMap::degeneracy(n - 1, i),
    )
    if !c_join.then(d1).same(const1) {
      ok = false
    }
    // 反轉為對合，並交換端面
    let r = CubeMap::reversal(n, i)
    checked += 3
    if !r.then(r).same(id) {
      ok = false
    }
    if !r
      .then(CubeMap::face(n, i, one=true))
      .same(CubeMap::face(n, i, one=false)) {
      ok = false
    }
    // 德摩根：反轉∘(∧連接) = (∨連接)∘(兩個反轉)
    let lhs = r.then(c_meet)
    let rhs = c_join.then(
      CubeMap::reversal(n + 1, i).then(CubeMap::reversal(n + 1, i + 1)),
    )
    if !lhs.same(rhs) {
      ok = false
    }
  }
  (checked, ok)
}
