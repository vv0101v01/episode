///|
/// n×m 方格圓盤：頂點 (i, j) ↦ i + j(n+1)；水平邊 h(i,j)、垂直邊 v(i,j)；
/// 每格一個面，自左下角起逆時針 R·U·L·D。
pub fn grid_disk(n : Int32, m : Int32) -> @s4.Complex {
  let vid = fn(i : Int32, j : Int32) -> Int32 { i + j * (n + 1) }
  let edges : Array[(Int32, Int32)] = []
  // 水平邊 h(i,j)：編號 i + j·n，j ∈ [0, m]
  for j in 0..<(m + 1) {
    for i in 0..<n {
      edges.push((vid(i, j), vid(i + 1, j)))
    }
  }
  // 垂直邊 v(i,j)：編號 n(m+1) + i + j(n+1)，i ∈ [0, n]
  for j in 0..<m {
    for i in 0..<(n + 1) {
      edges.push((vid(i, j), vid(i, j + 1)))
    }
  }
  let h = fn(i : Int32, j : Int32) -> Int32 { i + j * n }
  let v = fn(i : Int32, j : Int32) -> Int32 { n * (m + 1) + i + j * (n + 1) }
  let faces : Array[Array[Int32]] = []
  for j in 0..<m {
    for i in 0..<n {
      faces.push([
        2 * h(i, j),
        2 * v(i + 1, j),
        2 * h(i, j + 1) + 1,
        2 * v(i, j) + 1,
      ])
    }
  }
  { nv: (n + 1) * (m + 1), edges, faces, }
}

///|
/// 方格圓盤上的套索：由原點沿底邊右行 i 步、上行 j 步，繞格 (i,j) 一圈後原路折返。
pub fn grid_lasso(n : Int32, m : Int32, i : Int32, j : Int32) -> Array[Int32] {
  let h = fn(a : Int32, b : Int32) -> Int32 { a + b * n }
  let v = fn(a : Int32, b : Int32) -> Int32 { n * (m + 1) + a + b * (n + 1) }
  let tail : Array[Int32] = []
  for a in 0..<i {
    tail.push(2 * h(a, 0))
  }
  for b in 0..<j {
    tail.push(2 * v(i, b))
  }
  let path = tail.copy()
  for c in [2 * h(i, j), 2 * v(i + 1, j), 2 * h(i, j + 1) + 1, 2 * v(i, j) + 1] {
    path.push(c)
  }
  for c in @s4.inverse_word(tail) {
    path.push(c)
  }
  path
}

///|
/// 方格圓盤的外邊界（自原點逆時針）。
pub fn grid_boundary(n : Int32, m : Int32) -> Array[Int32] {
  let h = fn(a : Int32, b : Int32) -> Int32 { a + b * n }
  let v = fn(a : Int32, b : Int32) -> Int32 { n * (m + 1) + a + b * (n + 1) }
  let path : Array[Int32] = []
  for a in 0..<n {
    path.push(2 * h(a, 0))
  }
  for b in 0..<m {
    path.push(2 * v(n, b))
  }
  let mut a = n - 1
  while a >= 0 {
    path.push(2 * h(a, m) + 1)
    a -= 1
  }
  let mut b = m - 1
  while b >= 0 {
    path.push(2 * v(0, b) + 1)
    b -= 1
  }
  path
}

///|
/// 非交換 Stokes 定理（離散）：邊界和樂 = 套索曲率的有序乘積
/// （列 i 遞減、列內 j 遞增）。以 `trials` 個偽隨機聯絡檢驗；回傳（受檢數, 成立）。
pub fn verify_nonabelian_stokes(
  n : Int32,
  m : Int32,
  fiber : Int32,
  trials : Int32,
  seed : Int32,
) -> (Int32, Bool) {
  let x = grid_disk(n, m)
  let rng : Lcg = { state: seed, }
  let mut ok = true
  for _ in 0..<trials {
    let conn = random_connection(x, fiber, rng)
    let mut acc = perm_id(fiber)
    let mut i = n - 1
    while i >= 0 {
      for j in 0..<m {
        acc = perm_then(acc, conn.holonomy(grid_lasso(n, m, i, j)))
      }
      i -= 1
    }
    if acc != conn.holonomy(grid_boundary(n, m)) {
      ok = false
    }
  }
  (trials, ok)
}

///|
/// 由一組排列生成的群（閉包）；回傳元素的字串鍵集合大小與元素。
pub fn generated_group(
  gens : Array[Array[Int32]],
  fiber : Int32,
) -> Array[Array[Int32]] {
  let seen : Map[String, Bool] = Map([])
  let key = perm_key
  let elems : Array[Array[Int32]] = [perm_id(fiber)]
  seen[key(elems[0])] = true
  let mut head = 0
  while head < elems.length() {
    let p = elems[head]
    head += 1
    for g in gens {
      for q in [perm_then(p, g), perm_then(p, perm_inv(g))] {
        let k = key(q)
        if !seen.contains(k) {
          seen[k] = true
          elems.push(q)
        }
      }
    }
  }
  elems
}

///|
/// Ambrose–Singer 定理（離散；單連通底空間）：原點處的和樂群 = 套索曲率生成的群。
/// 和樂群由生成樹外各邊的基本迴路生成。回傳（|和樂群|, |曲率生成群|, 相等）。
pub fn verify_ambrose_singer(
  n : Int32,
  m : Int32,
  fiber : Int32,
  seed : Int32,
) -> (Int32, Int32, Bool) {
  let x = grid_disk(n, m)
  let rng : Lcg = { state: seed, }
  let conn = random_connection(x, fiber, rng)
  // 曲率側
  let lassos : Array[Array[Int32]] = []
  for i in 0..<n {
    for j in 0..<m {
      lassos.push(conn.holonomy(grid_lasso(n, m, i, j)))
    }
  }
  let curv_group = generated_group(lassos, fiber)
  // 和樂側：生成樹（BFS）上的樹路 + 樹外邊
  let parent_edge = Array::make(x.nv, -1)
  let visited = Array::make(x.nv, false)
  let in_tree = Array::make(x.edges.length(), false)
  let queue : Array[Int32] = [0]
  visited[0] = true
  let mut head = 0
  while head < queue.length() {
    let v = queue[head]
    head += 1
    for e in 0..<x.edges.length() {
      let (s, t) = x.edges[e]
      if s == v && !visited[t] {
        visited[t] = true
        parent_edge[t] = 2 * e
        in_tree[e] = true
        queue.push(t)
      } else if t == v && !visited[s] {
        visited[s] = true
        parent_edge[s] = 2 * e + 1
        in_tree[e] = true
        queue.push(s)
      }
    }
  }
  let tree_path = fn(v : Int32) -> Array[Int32] {
    // 由 0 到 v 的樹路
    let rev : Array[Int32] = []
    let mut cur = v
    while cur != 0 {
      let c = parent_edge[cur]
      rev.push(c)
      let (s, t) = x.edges[c / 2]
      cur = if c % 2 == 0 { s } else { t }
    }
    let out : Array[Int32] = []
    let mut k = rev.length() - 1
    while k >= 0 {
      out.push(rev[k])
      k -= 1
    }
    out
  }
  let loops : Array[Array[Int32]] = []
  for e in 0..<x.edges.length() {
    if !in_tree[e] {
      let (s, t) = x.edges[e]
      let path = tree_path(s)
      path.push(2 * e)
      for c in @s4.inverse_word(tree_path(t)) {
        path.push(c)
      }
      loops.push(conn.holonomy(path))
    }
  }
  let hol_group = generated_group(loops, fiber)
  let mut same = hol_group.length() == curv_group.length()
  if same {
    let keys : Map[String, Bool] = Map([])
    for p in curv_group {
      keys[perm_key(p)] = true
    }
    for p in hol_group {
      if !keys.contains(perm_key(p)) {
        same = false
      }
    }
  }
  (hol_group.length(), curv_group.length(), same)
}

///|
/// 規範共變性：規範變換 g 下，面 f 的曲率變為 g(v_f)⁻¹ ; F ; g(v_f)，故平坦性規範不變。
/// 回傳（受檢面數, 成立）。
pub fn verify_gauge_covariance(
  x : @s4.Complex,
  fiber : Int32,
  trials : Int32,
  seed : Int32,
) -> (Int32, Bool) {
  let rng : Lcg = { state: seed, }
  let mut checked = 0
  let mut ok = true
  let f = factorial(fiber)
  for _ in 0..<trials {
    let conn = random_connection(x, fiber, rng)
    let g : Array[Array[Int32]] = []
    for _ in 0..<x.nv {
      g.push(perm_unrank(fiber, rng.next(f)))
    }
    let conn2 = conn.gauge(x, g)
    let c1 = conn.curvature(x)
    let c2 = conn2.curvature(x)
    for k in 0..<x.faces.length() {
      if x.faces[k].length() == 0 {
        continue
      }
      let c0 = x.faces[k][0]
      let (s, t) = x.edges[c0 / 2]
      let base = if c0 % 2 == 0 { s } else { t }
      checked += 1
      if c2[k] != perm_then(perm_then(perm_inv(g[base]), c1[k]), g[base]) {
        ok = false
      }
    }
  }
  (checked, ok)
}

///|
/// 平坦聯絡的計數定理：#平坦聯絡 = |Hom(π₁(X), G)| · |G|^(|V|−1)，G = Sym(F)。
/// 兩側各自窮舉：左側枚舉全部聯絡；右側枚舉生成元賦值並檢驗關係子。
/// 回傳（#平坦聯絡, |Hom|, 等式成立）。
pub fn verify_flat_count(
  x : @s4.Complex,
  fiber : Int32,
) -> (Int32, Int32, Bool) {
  let g = factorial(fiber)
  let ne = x.edges.length()
  let mut total = 1
  for _ in 0..<ne {
    total *= g
  }
  let mut flat = 0
  for code in 0..<total {
    let tau : Array[Array[Int32]] = []
    let mut c = code
    for _ in 0..<ne {
      tau.push(perm_unrank(fiber, c % g))
      c = c / g
    }
    let conn : Connection = { fiber, tau, }
    if conn.is_flat(x) {
      flat += 1
    }
  }
  let (pres, _) = x.fundamental_group()
  let mut homs = 0
  let mut assignments = 1
  for _ in 0..<pres.ngens {
    assignments *= g
  }
  for code in 0..<assignments {
    let img : Array[Array[Int32]] = []
    let mut c = code
    for _ in 0..<pres.ngens {
      img.push(perm_unrank(fiber, c % g))
      c = c / g
    }
    let mut ok = true
    for r in pres.relators {
      let mut acc = perm_id(fiber)
      for l in r {
        acc = perm_then(
          acc,
          if l % 2 == 0 {
            img[l / 2]
          } else {
            perm_inv(img[l / 2])
          },
        )
      }
      if !perm_is_id(acc) {
        ok = false
        break
      }
    }
    if ok {
      homs += 1
    }
  }
  let mut scale = 1
  for _ in 0..<(x.nv - 1) {
    scale *= g
  }
  (flat, homs, flat == homs * scale)
}

///|
/// 單值表示定理：平坦聯絡的和樂只依賴迴路的同倫類——
/// 對基點處長度 ≤ `len` 的一切閉邊路，π₁ 中相等（由 S4 的收斂重寫系統判定）⇒ 和樂相等。
/// 回傳（受檢迴路對數, 成立）。
pub fn verify_monodromy_representation(
  x : @s4.Complex,
  conn : Connection,
  len : Int32,
  max_rules~ : Int32,
) -> (Int32, Bool) {
  let (pres, label) = x.fundamental_group()
  let rws = pres.complete(max_rules~)
  let loops : Array[Array[Int32]] = []
  let mut paths : Array[(Array[Int32], Int32)] = [([], 0)]
  for _ in 0..<len {
    let next : Array[(Array[Int32], Int32)] = []
    for item in paths {
      let (path, at) = item
      for c in 0..<(2 * x.edges.length()) {
        let (s, t) = x.edges[c / 2]
        let (from, to) = if c % 2 == 0 { (s, t) } else { (t, s) }
        if from == at {
          let np = path.copy()
          np.push(c)
          next.push((np, to))
          if to == 0 {
            loops.push(np)
          }
        }
      }
    }
    paths = next
  }
  let mut pairs = 0
  let mut ok = true
  // 以正規形分組比較
  let rep : Map[String, Array[Int32]] = Map([])
  for l in loops {
    let nf = rws.normal_form(@s4.path_word(label, l))
    let k = @s4.show_word(nf)
    let h = conn.holonomy(l)
    match rep.get(k) {
      Some(h0) => {
        pairs += 1
        if h0 != h {
          ok = false
        }
      }
      None => rep[k] = h
    }
  }
  (pairs, ok && rws.convergent)
}

///|
/// 表現函子的聯絡（基點路徑族 y ↦ Hom(x₀, y)）：纖維為 π₁ 的元素，邊 e 的平行移動為右乘 [e]。
/// π₁ 須有限。此族的全空間即泛覆疊——J 規則（基點路徑空間可縮）在群胚模型中的內容。
pub fn representable_connection(
  x : @s4.Complex,
  max_rules~ : Int32,
  limit~ : Int32,
) -> Connection? {
  let (pres, label) = x.fundamental_group()
  let rws = pres.complete(max_rules~)
  let (elems, finite) = rws.enumerate(limit~)
  if !finite || !rws.convergent {
    return None
  }
  let index : Map[String, Int32] = Map([])
  for i in 0..<elems.length() {
    index[@s4.show_word(elems[i])] = i
  }
  let tau : Array[Array[Int32]] = []
  for e in 0..<x.edges.length() {
    let letter : Array[Int32] = if label[e] >= 0 { [2 * label[e]] } else { [] }
    let t : Array[Int32] = []
    for w in elems {
      let nf = rws.normal_form(@s4.concat(w, letter))
      t.push(index.get(@s4.show_word(nf)).unwrap_or(0))
    }
    tau.push(t)
  }
  Some({ fiber: elems.length(), tau, })
}

///|
/// 群胚模型報告：把 X 讀作群胚 Π₁(X)、把平坦聯絡讀作其上的類型族。
pub(all) struct GroupoidModelReport {
  /// 頂點群 π₁ 的階（Id(x₀, x₀) 的元素數）；> 1 即 UIP 於此模型失效
  loop_space : Int32
  uip_fails : Bool
  /// 基點路徑族為平坦聯絡，其全空間連通且單連通（泛覆疊；J 的健全性）
  based_paths_flat : Bool
  based_paths_connected : Bool
  based_paths_simply_connected : Bool
  /// 全空間的 (V, E, F) 與 χ 的乘性
  total_vertices : Int32
  total_edges : Int32
  total_faces : Int32
  euler_multiplicative : Bool
  /// transport 的函子性：沿 p·q 的移動 = 先 p 後 q；沿 p⁻¹ 為逆
  transport_functorial : Bool
}

///|
pub fn groupoid_model(
  x : @s4.Complex,
  max_rules~ : Int32,
  limit~ : Int32,
) -> GroupoidModelReport? {
  match representable_connection(x, max_rules~, limit~) {
    None => None
    Some(conn) => {
      let (total, defects) = conn.total_space(x)
      let (p2, _) = total.fundamental_group()
      let r2 = p2.complete(max_rules=max_rules * 4)
      let mut trivial = r2.convergent
      for g in 0..<p2.ngens {
        if !r2.is_trivial([2 * g]) {
          trivial = false
        }
      }
      // 函子性：隨機邊路 p、q
      let rng : Lcg = { state: 2026, }
      let mut functorial = true
      for _ in 0..<50 {
        let p : Array[Int32] = []
        let q : Array[Int32] = []
        for _ in 0..<4 {
          p.push(rng.next(2 * x.edges.length()))
          q.push(rng.next(2 * x.edges.length()))
        }
        let pq = @s4.concat(p, q)
        if conn.holonomy(pq) != perm_then(conn.holonomy(p), conn.holonomy(q)) {
          functorial = false
        }
        if !perm_is_id(
            perm_then(conn.holonomy(p), conn.holonomy(@s4.inverse_word(p))),
          ) {
          functorial = false
        }
      }
      Some({
        loop_space: conn.fiber,
        uip_fails: conn.fiber > 1,
        based_paths_flat: conn.is_flat(x) && defects == 0,
        based_paths_connected: components(total) == 1,
        based_paths_simply_connected: trivial,
        total_vertices: total.nv,
        total_edges: total.edges.length(),
        total_faces: total.faces.length(),
        euler_multiplicative: total.euler() == conn.fiber * x.euler(),
        transport_functorial: functorial,
      })
    }
  }
}

///|
fn perm_key(p : Array[Int32]) -> String {
  let sb = StringBuilder()
  for x in p {
    sb.write_string("\{x},")
  }
  sb.to_string()
}

///|
/// 纖維叢由泛覆疊導出：給定 π₁(X) 在有限集 F 上的作用（每個生成元一個置換），
/// 伴隨叢 X̃ ×_{π₁} F 即以 F 為纖維、邊 e 的平行移動為 [e] 之作用的平坦聯絡。
/// π₁ 本身不必有限。作用不滿足關係子（某個面的和樂非恆等）時回傳 None。
pub fn associated_bundle(
  x : @s4.Complex,
  action : Array[Array[Int32]],
) -> Connection? {
  let (pres, label) = x.fundamental_group()
  if action.length() != pres.ngens {
    return None
  }
  let fiber = if action.length() > 0 { action[0].length() } else { 1 }
  for perm in action {
    if perm.length() != fiber {
      return None
    }
  }
  let tau : Array[Array[Int32]] = []
  for e in 0..<x.edges.length() {
    tau.push(if label[e] < 0 { perm_id(fiber) } else { action[label[e]] })
  }
  let conn : Connection = { fiber, tau, }
  if conn.is_flat(x) {
    Some(conn)
  } else {
    None
  }
}

///|
/// 一個有限葉覆疊的不變量。
pub(all) struct CoveringReport {
  sheets : Int32
  /// 全空間連通（⇔ 作用可遞 ⇔ 對應 π₁ 的一個指數為 `sheets` 的子群）
  connected : Bool
  /// χ(E) = sheets · χ(X)
  euler_multiplicative : Bool
  /// 全空間基本群（即該子群）的表現：生成元數、關係子數、H₁ 的秩與撓（全空間不連通時皆為空）
  subgroup_generators : Int32
  subgroup_relators : Int32
  h1_rank : Int32
  h1_torsion : Array[Int32]
  /// 每個面恰提升為 `sheets` 個面（平坦）
  faces_lift : Bool
}

///|
/// 定理（覆疊的分類）：連通的 n 葉覆疊 ↔ π₁ 在 n 元集上的可遞作用 ↔ 指數 n 的子群（共軛意義下）。
/// 全空間以 Grothendieck 構造建出，其基本群即該子群。
/// 推論（Nielsen–Schreier）：X 為 r 個圓的楔和時，子群為秩 1 + n(r − 1) 的自由群。
pub fn classify_covering(
  x : @s4.Complex,
  action : Array[Array[Int32]],
) -> CoveringReport? {
  match associated_bundle(x, action) {
    None => None
    Some(conn) => {
      let (total, defects) = conn.total_space(x)
      let connected = components(total) == 1
      // 基本群只對連通的全空間有意義；不連通時子群各欄留空
      let (pres, _) = if connected {
        total.fundamental_group()
      } else {
        ({ ngens: 0, relators: [], }, [])
      }
      let (rank, torsion) = pres.abelianization()
      Some({
        sheets: conn.fiber,
        connected,
        euler_multiplicative: total.euler() == conn.fiber * x.euler(),
        subgroup_generators: pres.ngens,
        subgroup_relators: pres.relators.length(),
        h1_rank: rank,
        h1_torsion: torsion,
        faces_lift: defects == 0,
      })
    }
  }
}
