///|
/// 強正規化判定結果。
#derive(Eq)
pub(all) enum SnVerdict {
  /// 約簡圖有限且無環 ⇔ 強正規化（König 引理）
  StronglyNormalizing
  /// 約簡圖含環 ⇒ 存在無窮約簡
  Cyclic
  /// 於預算內未能窮盡約簡圖
  BudgetExceeded
}

///|
pub extend SnVerdict with Eq::{equal, not_equal}

///|
/// 強正規化證書：窮舉約簡圖後的精確數據。
pub(all) struct SnCert {
  verdict : SnVerdict
  /// 約簡圖的節點數（相異約簡項數）與邊數
  nodes : Int32
  edges : Int32
  /// 自根出發的最長／最短約簡長度（僅於 StronglyNormalizing 時有效）
  longest : Int32
  shortest : Int32
  /// 可達的全部正規形（β 下由 Church–Rosser 必恰為一個）
  normal_forms : Array[Int32]
  /// Cyclic 時的環見證（首尾相接的項序列）
  cycle : Array[Int32]
}

///|
/// 建立 `t` 的完整約簡圖並判定強正規化。
/// 以 Kahn 拓樸排序自正規形反向傳播，對每個節點同時求最長與最短約簡長度；
/// 全程迭代、不使用遞迴，圖節點為駐留編號故判重為 O(1)。
pub fn Arena::sn_certificate(
  self : Arena,
  t : Int32,
  eta~ : Bool,
  budget~ : Int32,
) -> SnCert {
  let index : Map[Int32, Int32] = Map([])
  let terms : Array[Int32] = [t]
  let succs : Array[Array[Int32]] = []
  index[t] = 0
  let mut head = 0
  let mut edges = 0
  let mut exceeded = false
  while head < terms.length() {
    let cur = terms[head]
    head += 1
    let out : Array[Int32] = []
    for r in self.reducts(cur, eta~) {
      let j = match index.get(r) {
        Some(j) => j
        None => {
          let j = terms.length()
          index[r] = j
          terms.push(r)
          j
        }
      }
      out.push(j)
      edges += 1
    }
    succs.push(out)
    if terms.length() > budget {
      exceeded = true
      break
    }
  }
  if exceeded {
    return {
      verdict: BudgetExceeded,
      nodes: terms.length(),
      edges,
      longest: -1,
      shortest: -1,
      normal_forms: [],
      cycle: [],
    }
  }
  let n = terms.length()
  let preds : Array[Array[Int32]] = Array::makei(n, fn(_i) { [] })
  let remaining : Array[Int32] = Array::make(n, 0)
  for i in 0..<n {
    remaining[i] = succs[i].length()
    for j in succs[i] {
      preds[j].push(i)
    }
  }
  let longest : Array[Int32] = Array::make(n, 0)
  let shortest : Array[Int32] = Array::make(n, 0)
  let done : Array[Bool] = Array::make(n, false)
  let work : Array[Int32] = []
  let normal_forms : Array[Int32] = []
  for i in 0..<n {
    if remaining[i] == 0 {
      work.push(i)
      normal_forms.push(terms[i])
    }
  }
  let mut processed = 0
  while work.pop() is Some(i) {
    done[i] = true
    processed += 1
    if succs[i].length() > 0 {
      let mut lo = 1 + shortest[succs[i][0]]
      let mut hi = 0
      for j in succs[i] {
        if 1 + longest[j] > hi {
          hi = 1 + longest[j]
        }
        if 1 + shortest[j] < lo {
          lo = 1 + shortest[j]
        }
      }
      longest[i] = hi
      shortest[i] = lo
    }
    for p in preds[i] {
      remaining[p] -= 1
      if remaining[p] == 0 {
        work.push(p)
      }
    }
  }
  if processed < n {
    // 未被處理的節點各自至少有一個未被處理的後繼：沿之行走必然重訪而得環。
    let mut cur = 0
    for i in 0..<n {
      if !done[i] {
        cur = i
        break
      }
    }
    let position : Map[Int32, Int32] = Map([])
    let path : Array[Int32] = []
    while !position.contains(cur) {
      position[cur] = path.length()
      path.push(cur)
      for j in succs[cur] {
        if !done[j] {
          cur = j
          break
        }
      }
    }
    let start = position.get(cur).unwrap_or(0)
    let cycle : Array[Int32] = []
    for k in start..<path.length() {
      cycle.push(terms[path[k]])
    }
    cycle.push(terms[cur])
    return {
      verdict: Cyclic,
      nodes: n,
      edges,
      longest: -1,
      shortest: -1,
      normal_forms,
      cycle,
    }
  }
  {
    verdict: StronglyNormalizing,
    nodes: n,
    edges,
    longest: longest[0],
    shortest: shortest[0],
    normal_forms,
    cycle: [],
  }
}

///|
/// 局部合流缺陷：回傳一對不可合流的一步約簡結果（若存在）。
/// 以各自約簡圖的正規形集合是否相交判定；僅對強正規化項給出確定答案。
pub fn Arena::local_confluence_defect(
  self : Arena,
  t : Int32,
  eta~ : Bool,
  budget~ : Int32,
) -> (Int32, Int32)? {
  let rs = self.reducts(t, eta~)
  let nfs : Array[Array[Int32]] = []
  for r in rs {
    let cert = self.sn_certificate(r, eta~, budget~)
    if cert.verdict != StronglyNormalizing {
      return None
    }
    nfs.push(cert.normal_forms)
  }
  for i in 0..<rs.length() {
    for j in (i + 1)..<rs.length() {
      let mut meet = false
      for x in nfs[i] {
        if nfs[j].contains(x) {
          meet = true
        }
      }
      if !meet {
        return Some((rs[i], rs[j]))
      }
    }
  }
  None
}
