///|
/// Module S4 — 可判定性與合流性；泛覆疊空間。
///
/// 字母：生成元 g 的正字母為 2g、逆字母為 2g+1（故 a⁻¹ = a xor 1）。
/// 字以 shortlex 良序比較；規則恆由大字指向小字，故重寫必終止。
pub(all) struct Rule {
  lhs : Array[Int32]
  rhs : Array[Int32]
}

///|
pub(all) struct Presentation {
  ngens : Int32
  relators : Array[Array[Int32]]
}

///|
/// 字串重寫系統及其遙測。
pub(all) struct Rws {
  ngens : Int32
  rules : Array[Rule]
  /// 完備化是否在預算內收斂（收斂 ⇒ 合流且終止 ⇒ 字問題可判定）
  mut convergent : Bool
  mut rewrites : Int32
  mut pairs_examined : Int32
}

///|
pub fn inverse_word(w : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut k = w.length() - 1
  while k >= 0 {
    out.push(w[k] ^ 1)
    k -= 1
  }
  out
}

///|
pub fn concat(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = a.copy()
  for x in b {
    out.push(x)
  }
  out
}

///|
/// shortlex 比較。
pub fn shortlex(a : Array[Int32], b : Array[Int32]) -> Int32 {
  if a.length() != b.length() {
    return a.length() - b.length()
  }
  for k in 0..<a.length() {
    if a[k] != b[k] {
      return a[k] - b[k]
    }
  }
  0
}

///|
pub fn show_word(w : Array[Int32]) -> String {
  if w.length() == 0 {
    return "ε"
  }
  let sb = StringBuilder()
  let names = "abcdefghijklmnopqrstuvwxyz"
  let upper = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  for x in w {
    let g = x / 2
    if g < 26 {
      let src = if x % 2 == 0 { names } else { upper }
      let mut idx = 0
      for ch in src {
        if idx == g {
          sb.write_char(ch)
        }
        idx += 1
      }
    } else {
      sb.write_string("<\{x}>")
    }
  }
  sb.to_string()
}

///|
fn word_key(w : Array[Int32]) -> String {
  let sb = StringBuilder()
  for x in w {
    sb.write_string("\{x}.")
  }
  sb.to_string()
}

///|
fn suffix_matches(stack : Array[Int32], lhs : Array[Int32]) -> Bool {
  let n = stack.length()
  let m = lhs.length()
  if m > n {
    return false
  }
  for k in 0..<m {
    if stack[n - m + k] != lhs[k] {
      return false
    }
  }
  true
}

///|
/// 正規形：逐字母推入堆疊，一旦堆疊後綴為某規則左式即改寫（最左最內策略）。
pub fn Rws::normal_form(self : Rws, w : Array[Int32]) -> Array[Int32] {
  let stack : Array[Int32] = []
  // 待處理輸入（反向存放以便彈出）
  let input : Array[Int32] = []
  let mut k = w.length() - 1
  while k >= 0 {
    input.push(w[k])
    k -= 1
  }
  while input.pop() is Some(x) {
    stack.push(x)
    for rule in self.rules {
      if suffix_matches(stack, rule.lhs) {
        self.rewrites += 1
        for _ in 0..<rule.lhs.length() {
          ignore(stack.pop())
        }
        let mut j = rule.rhs.length() - 1
        while j >= 0 {
          input.push(rule.rhs[j])
          j -= 1
        }
        break
      }
    }
  }
  stack
}

///|
/// 加入等式 u = v：兩側先化為正規形，相異則定向為規則。回傳是否新增。
fn Rws::add_equation(self : Rws, u : Array[Int32], v : Array[Int32]) -> Bool {
  let nu = self.normal_form(u)
  let nv = self.normal_form(v)
  let c = shortlex(nu, nv)
  if c == 0 {
    return false
  }
  if c > 0 {
    self.rules.push({ lhs: nu, rhs: nv, })
  } else {
    self.rules.push({ lhs: nv, rhs: nu, })
  }
  true
}

///|
/// 規則 i 與 j 的全部臨界對（重疊與包含）。
fn critical_pairs_of(
  r1 : Rule,
  r2 : Rule,
) -> Array[(Array[Int32], Array[Int32])] {
  let out : Array[(Array[Int32], Array[Int32])] = []
  let l1 = r1.lhs
  let l2 = r2.lhs
  let n1 = l1.length()
  let n2 = l2.length()
  // 重疊：l1 = x·s，l2 = s·y（s 非空且為真重疊）
  let mut k = 1
  while k < n1 && k < n2 {
    let mut m = true
    for t in 0..<k {
      if l1[n1 - k + t] != l2[t] {
        m = false
        break
      }
    }
    if m {
      // x·s·y ⇒ r1·y 與 x·r2
      let y : Array[Int32] = []
      for t in k..<n2 {
        y.push(l2[t])
      }
      let x : Array[Int32] = []
      for t in 0..<(n1 - k) {
        x.push(l1[t])
      }
      out.push((concat(r1.rhs, y), concat(x, r2.rhs)))
    }
    k += 1
  }
  // 包含：l1 = x·l2·y
  if n2 <= n1 {
    for start in 0..<(n1 - n2 + 1) {
      let mut m = true
      for t in 0..<n2 {
        if l1[start + t] != l2[t] {
          m = false
          break
        }
      }
      if m && !(n1 == n2) {
        let x : Array[Int32] = []
        for t in 0..<start {
          x.push(l1[t])
        }
        let y : Array[Int32] = []
        for t in (start + n2)..<n1 {
          y.push(l1[t])
        }
        out.push((r1.rhs, concat(concat(x, r2.rhs), y)))
      }
    }
  }
  out
}

///|
/// 刪去冗餘規則並把右式化為正規形（收斂系統的既約化）。
fn Rws::interreduce(self : Rws) -> Unit {
  let old = self.rules.copy()
  // 依左式 shortlex 排序，使較短規則先入
  old.sort_by(fn(a, b) { shortlex(a.lhs, b.lhs) })
  self.rules.clear()
  for r in old {
    // 左式若可被既有規則改寫則冗餘（其資訊由臨界對保留）
    let nl = self.normal_form(r.lhs)
    if shortlex(nl, r.lhs) == 0 {
      let nr = self.normal_form(r.rhs)
      self.rules.push({ lhs: r.lhs, rhs: nr, })
    } else {
      ignore(self.add_equation(nl, r.rhs))
    }
  }
}

///|
/// Knuth–Bendix 完備化。`max_rules` 為規則數預算；超出則 `convergent=false`
/// （一般群的字問題不可判定，故此程序只是半判定）。
pub fn Presentation::complete(self : Presentation, max_rules~ : Int32) -> Rws {
  let rws : Rws = {
    ngens: self.ngens,
    rules: [],
    convergent: false,
    rewrites: 0,
    pairs_examined: 0,
  }
  // 自由約化 a·a⁻¹ → ε
  for a in 0..<(2 * self.ngens) {
    rws.rules.push({ lhs: [a, a ^ 1], rhs: [], })
  }
  for r in self.relators {
    ignore(rws.add_equation(r, []))
  }
  let mut round = 0
  while round < 64 {
    round += 1
    let mut added = false
    let mut restart = false
    let mut i = 0
    while i < rws.rules.length() {
      let mut j = 0
      while j <= i {
        let cps = critical_pairs_of(rws.rules[i], rws.rules[j])
        if i != j {
          for cp in critical_pairs_of(rws.rules[j], rws.rules[i]) {
            cps.push(cp)
          }
        }
        for cp in cps {
          rws.pairs_examined += 1
          let (u, v) = cp
          if rws.add_equation(u, v) {
            added = true
          }
        }
        if rws.rules.length() > max_rules {
          rws.interreduce()
          if rws.rules.length() > max_rules {
            return rws
          }
          // 既約化改變了規則編號：結束本輪，下一輪重新掃描
          restart = true
          break
        }
        j += 1
      }
      if restart {
        break
      }
      i += 1
    }
    rws.interreduce()
    if !added && !restart {
      rws.convergent = true
      return rws
    }
  }
  rws
}

///|
/// 局部合流性：一切臨界對可匯合。配合 shortlex 終止性，由 Newman 引理得合流。
/// 回傳（臨界對數, 全部可匯合）。
pub fn Rws::verify_local_confluence(self : Rws) -> (Int32, Bool) {
  let mut pairs = 0
  let mut ok = true
  for i in 0..<self.rules.length() {
    for j in 0..<self.rules.length() {
      for cp in critical_pairs_of(self.rules[i], self.rules[j]) {
        pairs += 1
        let (u, v) = cp
        if shortlex(self.normal_form(u), self.normal_form(v)) != 0 {
          ok = false
        }
      }
    }
  }
  (pairs, ok)
}

///|
/// 一步改寫的全部結果（任一位置、任一規則）。
pub fn Rws::one_step(self : Rws, w : Array[Int32]) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for rule in self.rules {
    let m = rule.lhs.length()
    if m > w.length() {
      continue
    }
    for start in 0..<(w.length() - m + 1) {
      let mut hit = true
      for t in 0..<m {
        if w[start + t] != rule.lhs[t] {
          hit = false
          break
        }
      }
      if hit {
        let nw : Array[Int32] = []
        for t in 0..<start {
          nw.push(w[t])
        }
        for x in rule.rhs {
          nw.push(x)
        }
        for t in (start + m)..<w.length() {
          nw.push(w[t])
        }
        out.push(nw)
      }
    }
  }
  out
}

///|
/// 合流性的直接窮舉檢驗：長度 ≤ `len` 的每個字，其一切一步改寫結果有相同正規形
/// （即正規形唯一）。回傳（受檢字數, 成立）。
pub fn Rws::verify_unique_normal_forms(
  self : Rws,
  len : Int32,
) -> (Int32, Bool) {
  let mut count = 0
  let mut ok = true
  let letters = 2 * self.ngens
  let mut layer : Array[Array[Int32]] = [[]]
  for _ in 0..<(len + 1) {
    let next : Array[Array[Int32]] = []
    for w in layer {
      count += 1
      let nf = self.normal_form(w)
      for r in self.one_step(w) {
        if shortlex(self.normal_form(r), nf) != 0 {
          ok = false
        }
      }
      for a in 0..<letters {
        let nw = w.copy()
        nw.push(a)
        next.push(nw)
      }
    }
    layer = next
  }
  (count, ok)
}

///|
/// 字問題：u = v 於群中 ⇔ 正規形相同（系統收斂時為判定程序）。
pub fn Rws::equal(self : Rws, u : Array[Int32], v : Array[Int32]) -> Bool {
  shortlex(self.normal_form(u), self.normal_form(v)) == 0
}

///|
pub fn Rws::is_trivial(self : Rws, w : Array[Int32]) -> Bool {
  self.normal_form(w).length() == 0
}

///|
/// 以正規形列舉群元素（廣度優先、右乘生成元）。回傳（元素, 是否列舉完畢）。
/// 列舉完畢時元素數即群的階。
pub fn Rws::enumerate(
  self : Rws,
  limit~ : Int32,
) -> (Array[Array[Int32]], Bool) {
  let seen : Map[String, Bool] = Map([])
  let elems : Array[Array[Int32]] = [[]]
  seen[word_key([])] = true
  let mut head = 0
  while head < elems.length() {
    if elems.length() >= limit {
      return (elems, false)
    }
    let w = elems[head]
    head += 1
    for a in 0..<(2 * self.ngens) {
      let nw = w.copy()
      nw.push(a)
      let nf = self.normal_form(nw)
      let k = word_key(nf)
      if !seen.contains(k) {
        seen[k] = true
        elems.push(nf)
      }
    }
  }
  (elems, true)
}

///|
/// 生長級數：長度恰為 0..len 的正規形個數（收斂的 shortlex 系統下即測地球面大小）。
pub fn Rws::growth(self : Rws, len : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut layer : Array[Array[Int32]] = [[]]
  for _ in 0..<(len + 1) {
    out.push(layer.length())
    let next : Array[Array[Int32]] = []
    for w in layer {
      for a in 0..<(2 * self.ngens) {
        let nw = w.copy()
        nw.push(a)
        // 正規形的延伸仍為正規形 ⇔ 無規則左式為其後綴
        let mut reducible = false
        for rule in self.rules {
          if suffix_matches(nw, rule.lhs) {
            reducible = true
            break
          }
        }
        if !reducible {
          next.push(nw)
        }
      }
    }
    layer = next
  }
  out
}

///|
fn gcd(a : Int32, b : Int32) -> Int32 {
  let mut x = a.abs()
  let mut y = b.abs()
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// 交換化 H₁ = G/[G,G]：關係矩陣的 Smith 正規形。回傳（自由秩, 撓係數（不變因子 > 1，遞增整除鏈））。
pub fn Presentation::abelianization(
  self : Presentation,
) -> (Int32, Array[Int32]) {
  let n = self.ngens
  let rows : Array[Array[Int32]] = []
  for r in self.relators {
    let row = Array::make(n, 0)
    for x in r {
      if x % 2 == 0 {
        row[x / 2] += 1
      } else {
        row[x / 2] -= 1
      }
    }
    rows.push(row)
  }
  let m = rows.length()
  let diag : Array[Int32] = []
  let mut top = 0
  let mut col = 0
  while top < m && col < n {
    // 找主元：剩餘子矩陣中絕對值最小的非零元
    let mut finished = false
    while !finished {
      let mut best = 0
      let mut bi = -1
      let mut bj = -1
      for i in top..<m {
        for j in col..<n {
          let v = rows[i][j].abs()
          if v != 0 && (bi < 0 || v < best) {
            best = v
            bi = i
            bj = j
          }
        }
      }
      if bi < 0 {
        // 剩餘全零
        top = m
        finished = true
        continue
      }
      let tmp = rows[top]
      rows[top] = rows[bi]
      rows[bi] = tmp
      for i in 0..<m {
        let t = rows[i][col]
        rows[i][col] = rows[i][bj]
        rows[i][bj] = t
      }
      let p = rows[top][col]
      let mut clean = true
      for i in (top + 1)..<m {
        let q = rows[i][col] / p
        if q != 0 {
          for j in col..<n {
            rows[i][j] -= q * rows[top][j]
          }
        }
        if rows[i][col] != 0 {
          clean = false
        }
      }
      for j in (col + 1)..<n {
        let q = rows[top][j] / p
        if q != 0 {
          for i in top..<m {
            rows[i][j] -= q * rows[i][col]
          }
        }
        if rows[top][j] != 0 {
          clean = false
        }
      }
      if clean {
        diag.push(p.abs())
        top += 1
        col += 1
        finished = true
      }
    }
  }
  // 化為整除鏈：d_i | d_{i+1}
  let mut changed = true
  while changed {
    changed = false
    for i in 0..<diag.length() {
      for j in (i + 1)..<diag.length() {
        if diag[j] % diag[i] != 0 {
          let g = gcd(diag[i], diag[j])
          let l = diag[i] / g * diag[j]
          diag[i] = g
          diag[j] = l
          changed = true
        }
      }
    }
  }
  diag.sort()
  let torsion : Array[Int32] = []
  for d in diag {
    if d > 1 {
      torsion.push(d)
    }
  }
  (n - diag.length(), torsion)
}

///|
/// 推出（組合範例 7）：G *_K H。`p2` 的生成元編號平移 `p1.ngens`；
/// `glue` 的每對 (u, v) 加入關係 u = v'（v' 為 v 的平移）。
pub fn amalgam(
  p1 : Presentation,
  p2 : Presentation,
  glue : Array[(Array[Int32], Array[Int32])],
) -> Presentation {
  let shift = fn(w : Array[Int32]) -> Array[Int32] {
    let out : Array[Int32] = []
    for x in w {
      out.push(x + 2 * p1.ngens)
    }
    out
  }
  let relators : Array[Array[Int32]] = []
  for r in p1.relators {
    relators.push(r)
  }
  for r in p2.relators {
    relators.push(shift(r))
  }
  for pair in glue {
    let (u, v) = pair
    relators.push(concat(u, inverse_word(shift(v))))
  }
  { ngens: p1.ngens + p2.ngens, relators, }
}

///|
/// 半直積（組合範例 8）：N ⋊_φ H。`action[h][n]` 為 H 的第 h 個生成元把 N 的第 n 個生成元
/// 共軛成的字（以 N 的字母寫）：h·n·h⁻¹ = φ_h(n)。
pub fn semidirect(
  n : Presentation,
  h : Presentation,
  action : Array[Array[Array[Int32]]],
) -> Presentation {
  let free = amalgam(n, h, [])
  let relators = free.relators.copy()
  for hi in 0..<h.ngens {
    for ni in 0..<n.ngens {
      let hl = 2 * (n.ngens + hi)
      // h n h⁻¹ φ_h(n)⁻¹
      let w = [hl, 2 * ni, hl ^ 1]
      relators.push(concat(w, inverse_word(action[hi][ni])))
    }
  }
  { ngens: free.ngens, relators, }
}
