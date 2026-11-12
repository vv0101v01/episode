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
/// 泛覆疊全空間的具體化：π₁ 有限時為整個全空間；π₁ 無限時為全空間中以基點為心的
/// 有限球（列舉上限 `limit` 所及的部分）。泛覆疊本身由 `CodeFamily` 以類型族給出，不受此限。
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

///|
/// 高階歸納類型（HIT）觀點下的泛覆疊。
///
/// 2-複形即一個 HIT 的簽名：頂點為點建構子、邊為路徑建構子、面為 2-路徑建構子。
/// 泛覆疊是以 HIT 的遞迴原理定義的類型族 Code : X → Set：
///   Code(v)       = ‖base = v‖₀ ≅ π₁(X)   —— 迴路空間的集合截斷，以收斂重寫系統的正規形為典範代表；
///   ap Code (e)   = ua(· 右乘 [e])          —— 每條邊給出纖維間的等價；
///   面的義務       ：邊界上各等價的合成為恆等（關係子於 π₁ 平凡）。
/// 纖維以正規形內涵地表示，從不列舉，故 π₁ 有限與否無關；
/// 唯一的前提是重寫系統收斂（否則正規形不是典範代表）。
pub(all) struct CodeFamily {
  base : Complex
  rws : Rws
  /// 每條邊的生成元編號（生成樹邊為 -1）
  label : Array[Int32]
  /// 自基點沿生成樹到各頂點的帶號邊路
  tree_path : Array[Array[Int32]]
  /// 每個生成元對應的樹外邊
  gen_edge : Array[Int32]
}

///|
/// 建立 Code 族；重寫系統於 `max_rules` 內未收斂時回傳 None。
pub fn Complex::code_family(self : Complex, max_rules~ : Int32) -> CodeFamily? {
  let (pres, label) = self.fundamental_group()
  let rws = pres.complete(max_rules~)
  if !rws.convergent {
    return None
  }
  let tree_path : Array[Array[Int32]] = []
  for _ in 0..<self.nv {
    tree_path.push([])
  }
  let visited = Array::make(self.nv, false)
  visited[0] = true
  let queue : Array[Int32] = [0]
  let mut head = 0
  while head < queue.length() {
    let v = queue[head]
    head += 1
    for e in 0..<self.edges.length() {
      if label[e] != -1 {
        continue
      }
      let (s, t) = self.edges[e]
      let (next, signed) = if s == v {
        (t, 2 * e)
      } else if t == v {
        (s, 2 * e + 1)
      } else {
        continue
      }
      if !visited[next] {
        visited[next] = true
        let p = tree_path[v].copy()
        p.push(signed)
        tree_path[next] = p
        queue.push(next)
      }
    }
  }
  let gen_edge = Array::make(pres.ngens, 0)
  for e in 0..<label.length() {
    if label[e] >= 0 {
      gen_edge[label[e]] = e
    }
  }
  Some({ base: self, rws, label, tree_path, gen_edge, })
}

///|
/// 沿一條帶號邊的傳送 transport^Code(e) : Code(u) → Code(v)，即 ua 的計算規則：
/// 沿 ua(f) 傳送就是施用 f。
pub fn CodeFamily::transport(
  self : CodeFamily,
  w : Array[Int32],
  signed : Int32,
) -> Array[Int32] {
  let g = self.label[signed / 2]
  if g < 0 {
    w
  } else {
    let next = w.copy()
    next.push(2 * g + signed % 2)
    self.rws.normal_form(next)
  }
}

///|
/// 全空間 Σ(v : X). Code(v) 中的唯一路徑提升：自 (v, w) 沿底空間的帶號邊路前進。
/// 邊路在底空間不相接時回傳 None。
pub fn CodeFamily::lift(
  self : CodeFamily,
  v : Int32,
  w : Array[Int32],
  path : Array[Int32],
) -> (Int32, Array[Int32])? {
  let mut cur = v
  let mut code = w
  for c in path {
    match self.base.step(cur, c) {
      None => return None
      Some(next) => {
        code = self.transport(code, c)
        cur = next
      }
    }
  }
  Some((cur, code))
}

///|
/// encode : (base = v) → Code(v)，encode(p) = transport^Code(p, ε)。
/// 對 S¹ 即纏繞數；一般地是迴路同倫類的正規形。
pub fn CodeFamily::encode(
  self : CodeFamily,
  path : Array[Int32],
) -> Array[Int32] {
  let mut code : Array[Int32] = []
  for c in path {
    code = self.transport(code, c)
  }
  code
}

///|
fn reverse_path(p : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<p.length() {
    out.push(p[p.length() - 1 - i] ^ 1)
  }
  out
}

///|
/// decode : Code(v) → (base = v)：把正規形的每個字母換成對應的基本迴路
/// （樹路 · 樹外邊 · 樹路⁻¹），最後接上到 v 的樹路。
pub fn CodeFamily::decode(
  self : CodeFamily,
  v : Int32,
  w : Array[Int32],
) -> Array[Int32] {
  let out : Array[Int32] = []
  for letter in w {
    let e = self.gen_edge[letter / 2]
    let (s, t) = self.base.edges[e]
    let (from, to) = if letter % 2 == 0 { (s, t) } else { (t, s) }
    for c in self.tree_path[from] {
      out.push(c)
    }
    out.push(2 * e + letter % 2)
    for c in reverse_path(self.tree_path[to]) {
      out.push(c)
    }
  }
  for c in self.tree_path[v] {
    out.push(c)
  }
  out
}

///|
/// 長度 ≤ `len` 的全部正規形（纖維 Code 的一個有限視窗；纖維本身不必有限）。
pub fn CodeFamily::codes(self : CodeFamily, len : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = [[]]
  let mut frontier : Array[Array[Int32]] = [[]]
  for _ in 0..<len {
    let next : Array[Array[Int32]] = []
    for w in frontier {
      for letter in 0..<(2 * self.rws.ngens) {
        let cand = w.copy()
        cand.push(letter)
        // 正規形的延伸仍為正規形者才保留：每個群元素恰出現一次
        if shortlex(self.rws.normal_form(cand), cand) == 0 {
          next.push(cand)
          out.push(cand)
        }
      }
    }
    frontier = next
  }
  out
}

///|
/// 自基點出發、長度 ≤ `len` 的全部帶號邊路及其終點。
fn Complex::paths_from_base(
  self : Complex,
  len : Int32,
) -> Array[(Array[Int32], Int32)] {
  let out : Array[(Array[Int32], Int32)] = [([], 0)]
  let mut frontier : Array[(Array[Int32], Int32)] = [([], 0)]
  for _ in 0..<len {
    let next : Array[(Array[Int32], Int32)] = []
    for item in frontier {
      let (p, v) = item
      for c in 0..<(2 * self.edges.length()) {
        match self.step(v, c) {
          Some(u) => {
            let q = p.copy()
            q.push(c)
            next.push((q, u))
            out.push((q, u))
          }
          None => ()
        }
      }
    }
    frontier = next
  }
  out
}

///|
/// 整數向量是否落在一組整數向量張成的格內（整數消元）。
fn in_lattice(rows : Array[Array[Int32]], v : Array[Int32]) -> Bool {
  let basis = rows.map(fn(r) { r.copy() })
  let target = v.copy()
  let n = v.length()
  let mut used = 0
  for col in 0..<n {
    // 以輾轉相除把第 col 行在未用列中化為單一非零元
    let mut busy = true
    while busy {
      busy = false
      let mut piv = -1
      for r in used..<basis.length() {
        if basis[r][col] != 0 &&
          (piv < 0 || basis[r][col].abs() < basis[piv][col].abs()) {
          piv = r
        }
      }
      if piv < 0 {
        break
      }
      let tmp = basis[used]
      basis[used] = basis[piv]
      basis[piv] = tmp
      for r in (used + 1)..<basis.length() {
        let q = basis[r][col] / basis[used][col]
        if q != 0 {
          for k in 0..<n {
            basis[r][k] -= q * basis[used][k]
          }
        }
        if basis[r][col] != 0 {
          busy = true
        }
      }
    }
    if used < basis.length() && basis[used][col] != 0 {
      if target[col] % basis[used][col] != 0 {
        return false
      }
      let q = target[col] / basis[used][col]
      for k in 0..<n {
        target[k] -= q * basis[used][k]
      }
      used += 1
    } else if target[col] != 0 {
      return false
    }
  }
  true
}

///|
/// 自由約簡：反覆消去相鄰的 x x⁻¹。
fn free_reduce(w : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in w {
    if out.length() > 0 && out[out.length() - 1] == (x ^ 1) {
      ignore(out.pop())
    } else {
      out.push(x)
    }
  }
  out
}

///|
/// encode–decode 定理的檢驗結果。
pub(all) struct EncodeDecode {
  /// 族良定：每條邊的傳送可逆，每個面的邊界傳送為恆等（2-路徑建構子的義務）
  family_well_defined : Bool
  /// encode(decode(v, w)) = w，且 decode(v, w) 終於 v
  encode_decode : Bool
  /// decode(encode(p)) 與 p 同端點，且差迴路 p · decode(encode p)⁻¹ 於 H₁ 為零
  /// （無面時改以自由約簡為空字檢驗，此時為充要）
  decode_encode : Bool
  /// 提升閉合 ⇔ encode 為 ε：全空間中自 (base, ε) 出發的提升終點只依賴同倫類
  codes_checked : Int32
  paths_checked : Int32
  /// 視窗內纖維元素數（長度 ≤ len 的正規形）
  window : Int32
}

///|
pub fn EncodeDecode::holds(self : EncodeDecode) -> Bool {
  self.family_well_defined && self.encode_decode && self.decode_encode
}

///|
/// 定理（encode–decode；Licata–Shulman 對 S¹，一般情形為覆疊的分類）：
///   Ω(X, base) 的集合截斷 ≃ Code(base)，encode 與 decode 互逆。
/// `code_len`：受檢正規形的長度上限；`path_len`：受檢邊路的長度上限。
pub fn CodeFamily::verify_encode_decode(
  self : CodeFamily,
  code_len : Int32,
  path_len : Int32,
) -> EncodeDecode {
  let x = self.base
  let window = self.codes(code_len)
  let mut family = true
  let mut enc_dec = true
  let mut dec_enc = true
  let mut codes_checked = 0
  for w in window {
    // 邊：來回傳送為恆等
    for c in 0..<(2 * x.edges.length()) {
      let there = self.transport(w, c)
      if shortlex(self.transport(there, c ^ 1), w) != 0 {
        family = false
      }
    }
    // 面：沿邊界傳送一圈回到原處
    for f in x.faces {
      let mut cur = w
      for c in f {
        cur = self.transport(cur, c)
      }
      if shortlex(cur, w) != 0 {
        family = false
      }
    }
    for v in 0..<x.nv {
      codes_checked += 1
      let p = self.decode(v, w)
      match self.lift(0, [], p) {
        Some((end, code)) =>
          if end != v || shortlex(code, w) != 0 {
            enc_dec = false
          }
        None => enc_dec = false
      }
    }
  }
  // H₁ 的關係格：每個面在樹外邊上的帶號計數
  let ngens = self.rws.ngens
  let count = fn(path : Array[Int32]) -> Array[Int32] {
    let v = Array::make(ngens, 0)
    for c in path {
      let g = self.label[c / 2]
      if g >= 0 {
        v[g] += if c % 2 == 0 { 1 } else { -1 }
      }
    }
    v
  }
  let lattice = x.faces.map(count)
  let paths = x.paths_from_base(path_len)
  for item in paths {
    let (p, end) = item
    let q = self.decode(end, self.encode(p))
    let diff = p.copy()
    for c in reverse_path(q) {
      diff.push(c)
    }
    // 同端點
    if !(self.lift(0, [], q) is Some((e2, _)) && e2 == end) {
      dec_enc = false
    }
    let independent = if x.faces.length() == 0 {
      free_reduce(path_word(self.label, diff)).length() == 0
    } else {
      in_lattice(lattice, count(diff))
    }
    if !independent {
      dec_enc = false
    }
  }
  {
    family_well_defined: family,
    encode_decode: enc_dec,
    decode_encode: dec_enc,
    codes_checked,
    paths_checked: paths.length(),
    window: window.length(),
  }
}

///|
/// 宇宙中的路徑（僅含本族用到的形狀）：refl、ua(右乘一個字)、合成、反向。
/// 這是計算性單值性在集合層級的片段：宇宙路徑有典範形，沿之傳送可計算。
pub(all) enum UPath {
  Refl
  /// ua(· 右乘 w)
  Ua(Array[Int32])
  Concat(UPath, UPath)
  Sym(UPath)
}

///|
/// ap Code：把底空間的邊路送到宇宙中的路徑（HIT 遞迴原理在路徑建構子上的值）。
pub fn CodeFamily::ap_code(self : CodeFamily, path : Array[Int32]) -> UPath {
  let mut acc = UPath::Refl
  for c in path {
    let g = self.label[c / 2]
    let step = if g < 0 {
      UPath::Refl
    } else if c % 2 == 0 {
      UPath::Ua([2 * g])
    } else {
      Sym(Ua([2 * g]))
    }
    acc = Concat(acc, step)
  }
  acc
}

///|
/// 沿宇宙路徑的傳送，依路徑結構逐步計算：
///   transport(refl) = id；transport(ua f) = f；transport(p · q) = transport(q) ∘ transport(p)；
///   transport(p⁻¹) = transport(p)⁻¹。
pub fn CodeFamily::transport_along(
  self : CodeFamily,
  p : UPath,
  w : Array[Int32],
) -> Array[Int32] {
  match p {
    Refl => w
    Ua(u) => self.rws.normal_form(concat(w, u))
    Concat(a, b) => self.transport_along(b, self.transport_along(a, w))
    Sym(a) => self.transport_along(self.invert(a), w)
  }
}

///|
/// 宇宙路徑的反向，推到葉上：(p · q)⁻¹ = q⁻¹ · p⁻¹，ua(f)⁻¹ = ua(f⁻¹)。
fn CodeFamily::invert(self : CodeFamily, p : UPath) -> UPath {
  match p {
    Refl => Refl
    Ua(u) => Ua(inverse_word(u))
    Concat(a, b) => Concat(self.invert(b), self.invert(a))
    Sym(a) => a
  }
}

///|
/// 宇宙路徑的典範形：每條路徑等於唯一的 ua(· 右乘 n)，n 為正規形（ua 的 η）。
pub fn CodeFamily::canonical(self : CodeFamily, p : UPath) -> Array[Int32] {
  self.transport_along(p, [])
}

///|
/// 定理（集合層級的計算性單值性）：
///   (1) 典範性：transport(p, w) = w · canonical(p)，對視窗內一切 w；
///   (2) ap Code 的函子性：canonical(ap Code (p · q)) = canonical(ap Code p) · canonical(ap Code q)；
///   (3) canonical(ap Code p) = encode(p)，canonical(p⁻¹) = canonical(p)⁻¹。
/// 回傳（受檢實例數, 成立）。
pub fn CodeFamily::verify_univalence_computation(
  self : CodeFamily,
  code_len : Int32,
  path_len : Int32,
) -> (Int32, Bool) {
  let window = self.codes(code_len)
  let paths = self.base.paths_from_base(path_len)
  let mut ok = true
  let mut n = 0
  for item in paths {
    let (p, _) = item
    let up = self.ap_code(p)
    let canon = self.canonical(up)
    if shortlex(canon, self.encode(p)) != 0 {
      ok = false
    }
    let back = self.canonical(Sym(up))
    if shortlex(back, self.rws.normal_form(inverse_word(canon))) != 0 {
      ok = false
    }
    for w in window {
      n += 1
      let direct = self.transport_along(up, w)
      if shortlex(direct, self.rws.normal_form(concat(w, canon))) != 0 {
        ok = false
      }
      // 往返：沿 p 再沿 p⁻¹ 回到 w
      if shortlex(self.transport_along(Sym(up), direct), w) != 0 {
        ok = false
      }
    }
    // 函子性：把 p 於中點切開
    let mid = p.length() / 2
    let first : Array[Int32] = []
    let second : Array[Int32] = []
    for i in 0..<p.length() {
      if i < mid {
        first.push(p[i])
      } else {
        second.push(p[i])
      }
    }
    let glued = self.rws.normal_form(
      concat(
        self.canonical(self.ap_code(first)),
        self.canonical(self.ap_code(second)),
      ),
    )
    if shortlex(glued, canon) != 0 {
      ok = false
    }
  }
  (n, ok)
}

///|
/// 圓 S¹（一個點、一條環邊，無面）與 n 個圓的楔和（π₁ 為自由群 Fₙ）。
pub fn bouquet(n : Int32) -> Complex {
  presentation_complex(n, [])
}
