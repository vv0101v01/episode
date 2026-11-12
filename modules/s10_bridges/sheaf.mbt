///|
/// 組合範例 2 — 層的黏合。平坦聯絡的水平截面構成複形上的層：
/// 對子複形 U（以邊集給出），Γ(U) = {s : 頂點 → 纖維 | 每條邊 e : u → v 上 τ_e(s(u)) = s(v)}。
/// 截面以各頂點取值的陣列表示（不在 U 內的頂點記 -1）。
pub fn sections(
  x : @s4.Complex,
  conn : @s5.Connection,
  edges : Array[Int32],
) -> Array[Array[Int32]] {
  let touched = Array::make(x.nv, false)
  for e in edges {
    let (u, v) = x.edges[e]
    touched[u] = true
    touched[v] = true
  }
  let verts : Array[Int32] = []
  for v in 0..<x.nv {
    if touched[v] {
      verts.push(v)
    }
  }
  let out : Array[Array[Int32]] = []
  let cur = Array::make(x.nv, -1)
  // 回溯：依序為頂點賦值，隨即檢查兩端皆已賦值的邊
  fn go(k : Int32) -> Unit {
    if k == verts.length() {
      out.push(cur.copy())
      return
    }
    let v = verts[k]
    for val in 0..<conn.fiber {
      cur[v] = val
      let mut ok = true
      for e in edges {
        let (a, b) = x.edges[e]
        if (a == v || b == v) &&
          cur[a] >= 0 &&
          cur[b] >= 0 &&
          conn.tau[e][cur[a]] != cur[b] {
          ok = false
          break
        }
      }
      if ok {
        go(k + 1)
      }
    }
    cur[v] = -1
  }

  go(0)
  out
}

///|
pub(all) struct GluingReport {
  sections_u : Int32
  sections_v : Int32
  sections_union : Int32
  /// 在 U ∩ V 的頂點上相容的 (s_U, s_V) 對數
  compatible_pairs : Int32
  /// 每對相容截面恰黏合成唯一的整體截面
  unique_gluing : Bool
}

///|
pub fn GluingReport::is_sheaf(self : GluingReport) -> Bool {
  self.unique_gluing && self.compatible_pairs == self.sections_union
}

///|
/// 層條件：Γ(U ∪ V) → Γ(U) × Γ(V) ⇉ Γ(U ∩ V) 為等化子。
pub fn verify_gluing(
  x : @s4.Complex,
  conn : @s5.Connection,
  eu : Array[Int32],
  ev : Array[Int32],
) -> GluingReport {
  let su = sections(x, conn, eu)
  let sv = sections(x, conn, ev)
  let all : Array[Int32] = eu.copy()
  for e in ev {
    if !all.contains(e) {
      all.push(e)
    }
  }
  let sw = sections(x, conn, all)
  let key = fn(s : Array[Int32]) -> String {
    let sb = StringBuilder()
    for a in s {
      sb.write_string("\{a},")
    }
    sb.to_string()
  }
  let global : Map[String, Int32] = Map([])
  for s in sw {
    global[key(s)] = 0
  }
  let mut pairs = 0
  let mut unique = true
  for a in su {
    for b in sv {
      let mut compatible = true
      let glued = Array::make(x.nv, -1)
      for v in 0..<x.nv {
        if a[v] >= 0 && b[v] >= 0 && a[v] != b[v] {
          compatible = false
          break
        }
        glued[v] = if a[v] >= 0 { a[v] } else { b[v] }
      }
      if compatible {
        pairs += 1
        match global.get(key(glued)) {
          Some(c) => global[key(glued)] = c + 1
          None => unique = false
        }
      }
    }
  }
  for s in sw {
    if global.get(key(s)).unwrap_or(0) != 1 {
      unique = false
    }
  }
  {
    sections_u: su.length(),
    sections_v: sv.length(),
    sections_union: sw.length(),
    compatible_pairs: pairs,
    unique_gluing: unique,
  }
}

///|
/// 樣本：m×n 方格圓盤上的聯絡——先取隨機規範變換得到的純規範聯絡（平坦、和樂平凡，
/// 整體截面數 = 纖維大小），`twist ≥ 0` 時再把第 `twist` 條邊的平行移動複合上對換 (0 1)，
/// 使該邊所在面的和樂成為對換的共軛（整體截面只剩和樂的公共不動點）。
/// 覆蓋：U = 前半邊、V = 後半邊（共用中間一條邊）。
pub fn gluing_sample(
  m : Int32,
  n : Int32,
  fiber : Int32,
  seed : Int32,
  twist : Int32,
) -> GluingReport {
  let x = @s5.grid_disk(m, n)
  let lcg : @s5.Lcg = { state: seed, }
  let gauge : Array[Array[Int32]] = []
  for _ in 0..<x.nv {
    gauge.push(@s5.perm_unrank(fiber, lcg.next(@s5.factorial(fiber))))
  }
  let conn = @s5.pure_gauge(x, gauge, fiber)
  if twist >= 0 {
    let swap = @s5.perm_id(fiber)
    swap[0] = 1
    swap[1] = 0
    conn.tau[twist] = @s5.perm_then(conn.tau[twist], swap)
  }
  let eu : Array[Int32] = []
  let ev : Array[Int32] = []
  let half = x.edges.length() / 2
  for e in 0..<x.edges.length() {
    if e <= half {
      eu.push(e)
    }
    if e >= half {
      ev.push(e)
    }
  }
  verify_gluing(x, conn, eu, ev)
}
