///|
/// 有限 2 維胞腔複形：頂點 0..nv-1；有向邊 (源, 靶)；面為閉合的帶號邊路
/// （邊 e 正向記 2e、反向記 2e+1）。
pub(all) struct Complex {
  nv : Int32
  edges : Array[(Int32, Int32)]
  faces : Array[Array[Int32]]
}

///|
pub fn Complex::euler(self : Complex) -> Int32 {
  self.nv - self.edges.length() + self.faces.length()
}

///|
fn Complex::step(self : Complex, v : Int32, signed : Int32) -> Int32? {
  let (s, t) = self.edges[signed / 2]
  if signed % 2 == 0 {
    if s == v {
      Some(t)
    } else {
      None
    }
  } else if t == v {
    Some(s)
  } else {
    None
  }
}

///|
/// 帶號邊的起點。
fn Complex::origin(self : Complex, signed : Int32) -> Int32 {
  let (s, t) = self.edges[signed / 2]
  if signed % 2 == 0 {
    s
  } else {
    t
  }
}

///|
/// 基本群的表現（複形須連通）：取廣度優先生成樹，樹外邊為生成元，
/// 面的邊界（樹邊視為平凡）為關係。回傳（表現, 每條邊的生成元編號（樹邊為 -1））。
pub fn Complex::fundamental_group(
  self : Complex,
) -> (Presentation, Array[Int32]) {
  let label = Array::make(self.edges.length(), -2)
  let visited = Array::make(self.nv, false)
  let queue : Array[Int32] = [0]
  visited[0] = true
  let mut head = 0
  while head < queue.length() {
    let v = queue[head]
    head += 1
    for e in 0..<self.edges.length() {
      let (s, t) = self.edges[e]
      if s == v && !visited[t] {
        visited[t] = true
        label[e] = -1
        queue.push(t)
      } else if t == v && !visited[s] {
        visited[s] = true
        label[e] = -1
        queue.push(s)
      }
    }
  }
  let mut ngens = 0
  for e in 0..<self.edges.length() {
    if label[e] == -2 {
      label[e] = ngens
      ngens += 1
    }
  }
  let relators : Array[Array[Int32]] = []
  for f in self.faces {
    relators.push(path_word(label, f))
  }
  ({ ngens, relators, }, label)
}

///|
/// 帶號邊路在生成元字母下的字。
pub fn path_word(label : Array[Int32], path : Array[Int32]) -> Array[Int32] {
  let w : Array[Int32] = []
  for c in path {
    let g = label[c / 2]
    if g >= 0 {
      w.push(2 * g + c % 2)
    }
  }
  w
}

///|
/// 覆疊空間（泛覆疊或其有限截斷）。
pub(all) struct Cover {
  total : Complex
  /// 投影：覆疊頂點 → 底頂點
  proj : Array[Int32]
  /// 覆疊頂點所在的葉（π₁ 的元素，以正規形表示）
  sheet : Array[Array[Int32]]
  /// 覆疊邊 → 底邊
  edge_proj : Array[Int32]
  /// 是否為整個泛覆疊（π₁ 有限且在上限內列舉完）
  complete : Bool
  /// 提升表：(覆疊頂點, 底邊) → 覆疊邊（由該頂點出發的正向提升），無則 -1
  lift_out : Array[Array[Int32]]
  /// (覆疊頂點, 底邊) → 以該頂點為靶的覆疊邊，無則 -1
  lift_in : Array[Array[Int32]]
}

///|
/// 泛覆疊空間的構造：頂點為 (v, g)，g ∈ π₁ 的正規形；底邊 e : u → v 提升為
/// (u, g) → (v, g·[e])。面在每個葉上提升（關係子在 π₁ 中平凡，故提升閉合）。
pub fn Complex::universal_cover(
  self : Complex,
  rws : Rws,
  label : Array[Int32],
  limit~ : Int32,
) -> Cover {
  let index : Map[String, Int32] = Map([])
  let proj : Array[Int32] = []
  let sheet : Array[Array[Int32]] = []
  let key = fn(v : Int32, g : Array[Int32]) -> String { "\{v}|" + word_key(g) }
  let add = fn(v : Int32, g : Array[Int32]) -> Int32 {
    let k = key(v, g)
    match index.get(k) {
      Some(i) => i
      None => {
        let i = proj.length()
        index[k] = i
        proj.push(v)
        sheet.push(g)
        i
      }
    }
  }
  ignore(add(0, []))
  let mut head = 0
  let mut complete = true
  while head < proj.length() {
    if proj.length() >= limit {
      complete = false
      break
    }
    let v = proj[head]
    let g = sheet[head]
    head += 1
    for e in 0..<self.edges.length() {
      let (s, t) = self.edges[e]
      let letter : Array[Int32] = if label[e] >= 0 {
        [2 * label[e]]
      } else {
        []
      }
      if s == v {
        ignore(add(t, rws.normal_form(concat(g, letter))))
      }
      if t == v {
        ignore(add(s, rws.normal_form(concat(g, inverse_word(letter)))))
      }
    }
  }
  let n = proj.length()
  let edges : Array[(Int32, Int32)] = []
  let edge_proj : Array[Int32] = []
  let lift_out : Array[Array[Int32]] = []
  let lift_in : Array[Array[Int32]] = []
  for _ in 0..<n {
    lift_out.push(Array::make(self.edges.length(), -1))
    lift_in.push(Array::make(self.edges.length(), -1))
  }
  for i in 0..<n {
    for e in 0..<self.edges.length() {
      let (s, t) = self.edges[e]
      if s != proj[i] {
        continue
      }
      let letter : Array[Int32] = if label[e] >= 0 {
        [2 * label[e]]
      } else {
        []
      }
      let k = key(t, rws.normal_form(concat(sheet[i], letter)))
      match index.get(k) {
        Some(j) => {
          lift_out[i][e] = edges.length()
          lift_in[j][e] = edges.length()
          edges.push((i, j))
          edge_proj.push(e)
        }
        None => ()
      }
    }
  }
  let faces : Array[Array[Int32]] = []
  for f in self.faces {
    if f.length() == 0 {
      continue
    }
    let start = self.origin(f[0])
    for i in 0..<n {
      if proj[i] != start {
        continue
      }
      let lifted : Array[Int32] = []
      let mut cur = i
      let mut ok = true
      for c in f {
        let e = c / 2
        if c % 2 == 0 {
          let le = lift_out[cur][e]
          if le < 0 {
            ok = false
            break
          }
          lifted.push(2 * le)
          let (_, j) = edges[le]
          cur = j
        } else {
          let le = lift_in[cur][e]
          if le < 0 {
            ok = false
            break
          }
          lifted.push(2 * le + 1)
          let (j, _) = edges[le]
          cur = j
        }
      }
      if ok && cur == i {
        faces.push(lifted)
      }
    }
  }
  {
    total: { nv: n, edges, faces, },
    proj,
    sheet,
    edge_proj,
    complete,
    lift_out,
    lift_in,
  }
}

///|
/// 唯一路徑提升：自覆疊頂點 `start` 提升底空間的帶號邊路；回傳終點（超出截斷範圍為 None）。
pub fn Cover::lift_path(
  self : Cover,
  start : Int32,
  path : Array[Int32],
) -> Int32? {
  let mut cur = start
  for c in path {
    let e = c / 2
    if c % 2 == 0 {
      let le = self.lift_out[cur][e]
      if le < 0 {
        return None
      }
      let (_, j) = self.total.edges[le]
      cur = j
    } else {
      let le = self.lift_in[cur][e]
      if le < 0 {
        return None
      }
      let (j, _) = self.total.edges[le]
      cur = j
    }
  }
  Some(cur)
}

///|
pub(all) struct CoverReport {
  group_order : Int32
  group_finite : Bool
  rules : Int32
  convergent : Bool
  critical_pairs : Int32
  locally_confluent : Bool
  sheets : Int32
  cover_vertices : Int32
  cover_edges : Int32
  cover_faces : Int32
  /// χ(覆疊) = |π₁|·χ(底)；覆疊未完整建出時為 false
  euler_multiplicative : Bool
  /// 每條纖維恰有 |π₁| 個點（甲板變換自由且可遞）；覆疊未完整建出時為 false
  fibers_uniform : Bool
  /// 覆疊的基本群平凡（泛性）
  simply_connected : Bool
  /// 迴路提升閉合 ⇔ 該迴路在 π₁ 中平凡（對長度 ≤ 4 的一切基點迴路）
  monodromy_faithful : Bool
  loops_checked : Int32
  h1_rank : Int32
  h1_torsion : Array[Int32]
}

///|
/// 對連通 2-複形完成整條動線：π₁ 的表現 → Knuth–Bendix → 泛覆疊 → 性質檢驗。
pub fn analyze_complex(
  x : Complex,
  max_rules~ : Int32,
  limit~ : Int32,
) -> CoverReport {
  let (pres, label) = x.fundamental_group()
  let rws = pres.complete(max_rules~)
  let (pairs, lc) = rws.verify_local_confluence()
  let (elems, finite) = rws.enumerate(limit~)
  let cover = x.universal_cover(rws, label, limit=limit * x.nv + 1)
  let order = elems.length()
  let full = finite && cover.complete
  let fiber = Array::make(x.nv, 0)
  for v in cover.proj {
    fiber[v] += 1
  }
  // 覆疊未完整建出（無限群或超限）時，下列兩項無從成立，記為 false
  let mut uniform = full
  for c in fiber {
    if c != order {
      uniform = false
    }
  }
  let euler_ok = full && cover.total.euler() == order * x.euler()
  let simply = if full {
    let (p2, _) = cover.total.fundamental_group()
    let r2 = p2.complete(max_rules=max_rules * 4)
    let mut trivial = r2.convergent
    for g in 0..<p2.ngens {
      if !r2.is_trivial([2 * g]) {
        trivial = false
      }
    }
    trivial
  } else {
    // 截斷球：每個完全落在球內的面提升都閉合（構造時已檢）；此處檢驗關係子提升
    let mut ok = true
    for f in x.faces {
      if f.length() > 0 && x.origin(f[0]) == 0 {
        match cover.lift_path(0, f) {
          Some(e) => if e != 0 { ok = false }
          None => ()
        }
      }
    }
    ok
  }
  // 單值性：基點處長度 ≤ 4 的閉邊路
  let mut loops = 0
  let mut faithful = true
  let mut paths : Array[(Array[Int32], Int32)] = [([], 0)]
  for _ in 0..<4 {
    let next : Array[(Array[Int32], Int32)] = []
    for item in paths {
      let (path, at) = item
      for c in 0..<(2 * x.edges.length()) {
        match x.step(at, c) {
          Some(to) => {
            let np = path.copy()
            np.push(c)
            next.push((np, to))
            if to == 0 {
              loops += 1
              let trivial = rws.is_trivial(path_word(label, np))
              match cover.lift_path(0, np) {
                Some(end) => if (end == 0) != trivial { faithful = false }
                None => ()
              }
            }
          }
          None => ()
        }
      }
    }
    paths = next
  }
  let (rank, torsion) = pres.abelianization()
  {
    group_order: order,
    group_finite: finite,
    rules: rws.rules.length(),
    convergent: rws.convergent,
    critical_pairs: pairs,
    locally_confluent: lc,
    sheets: if full {
      order
    } else {
      -1
    },
    cover_vertices: cover.total.nv,
    cover_edges: cover.total.edges.length(),
    cover_faces: cover.total.faces.length(),
    euler_multiplicative: euler_ok,
    fibers_uniform: uniform,
    simply_connected: simply,
    monodromy_faithful: faithful,
    loops_checked: loops,
    h1_rank: rank,
    h1_torsion: torsion,
  }
}

///|
/// 標準複形：一個頂點、`loops` 條環邊、給定的面（表現複形）。
pub fn presentation_complex(
  loops : Int32,
  faces : Array[Array[Int32]],
) -> Complex {
  let edges : Array[(Int32, Int32)] = []
  for _ in 0..<loops {
    edges.push((0, 0))
  }
  { nv: 1, edges, faces, }
}

///|
/// 實射影平面 RP²（π₁ = ℤ/2，泛覆疊為球面）。
pub fn rp2() -> Complex {
  presentation_complex(1, [[0, 0]])
}

///|
/// 環面 T²（π₁ = ℤ²，泛覆疊為平面）。
pub fn torus() -> Complex {
  presentation_complex(2, [[0, 2, 1, 3]])
}

///|
/// 克萊因瓶（π₁ = ℤ ⋊ ℤ）。
pub fn klein_bottle() -> Complex {
  presentation_complex(2, [[0, 2, 1, 2]])
}

///|
/// 偽射影平面 / 透鏡型 2-複形（π₁ = ℤ/n）。
pub fn moore_complex(n : Int32) -> Complex {
  let f : Array[Int32] = []
  for _ in 0..<n {
    f.push(0)
  }
  presentation_complex(1, [f])
}

///|
/// 三角形邊界加一個面與一條把手狀環邊：多頂點複形，π₁ = ℤ。
pub fn disk_with_loop() -> Complex {
  { nv: 3, edges: [(0, 1), (1, 2), (2, 0), (1, 1)], faces: [[0, 2, 4]], }
}
