///|
/// Eₙ(2) 的離散模型：邊長 1/N 的兩個帶標號小方體，位於 Nⁿ 格子的相異格。
/// 這是有序二點構形空間 Conf₂(ℝⁿ) ≃ Sⁿ⁻¹ 的方體複形模型：
///   頂點 = 狀態；邊 = 一個方體移到相鄰空格；
///   方格 = 兩個可交換的移動（兩方體各動一步，或同一方體沿兩個軸各動一步）。
pub(all) struct ConfReport {
  dim : Int32
  grid : Int32
  vertices : Int32
  edges : Int32
  squares : Int32
  /// 連通分支數 b₀ 與第一 Betti 數 b₁（𝔽₂ 係數）
  b0 : Int32
  b1 : Int32
}

///|
/// 𝔽₂ 上的秩（列以 30 位元分塊存放）。
fn rank_gf2(rows : Array[Array[Int32]], ncols : Int32) -> Int32 {
  let words = (ncols + 29) / 30
  let mut rank = 0
  let used = Array::make(rows.length(), false)
  for col in 0..<ncols {
    let w = col / 30
    let bit = 1 << (col % 30)
    let mut piv = -1
    for r in 0..<rows.length() {
      if !used[r] && (rows[r][w] & bit) != 0 {
        piv = r
        break
      }
    }
    if piv < 0 {
      continue
    }
    used[piv] = true
    rank += 1
    for r in 0..<rows.length() {
      if r != piv && (rows[r][w] & bit) != 0 {
        for k in 0..<words {
          rows[r][k] = rows[r][k] ^ rows[piv][k]
        }
      }
    }
  }
  rank
}

///|
/// 建立離散構形複形並計算 b₀、b₁。
pub fn configuration_space(dim : Int32, grid : Int32) -> ConfReport {
  let mut cells = 1
  for _ in 0..<dim {
    cells *= grid
  }
  // 相鄰格：沿軸 a 正向移動一步（越界為 -1）
  let step = fn(cell : Int32, axis : Int32) -> Int32 {
    let mut stride = 1
    for _ in 0..<axis {
      stride *= grid
    }
    let coord = cell / stride % grid
    if coord + 1 >= grid {
      -1
    } else {
      cell + stride
    }
  }
  let state = fn(p : Int32, q : Int32) -> Int32 { p * cells + q }
  let valid = fn(p : Int32, q : Int32) -> Bool { p >= 0 && q >= 0 && p != q }
  // 頂點編號
  let vid = Array::make(cells * cells, -1)
  let mut nv = 0
  for p in 0..<cells {
    for q in 0..<cells {
      if p != q {
        vid[state(p, q)] = nv
        nv += 1
      }
    }
  }
  // 邊：以（狀態, 哪個方體, 軸）編號，只取正向
  let eid : Map[Int32, Int32] = Map([])
  let edge_ends : Array[(Int32, Int32)] = []
  let edge_key = fn(s : Int32, who : Int32, axis : Int32) -> Int32 {
    (s * 2 + who) * dim + axis
  }
  for p in 0..<cells {
    for q in 0..<cells {
      if p == q {
        continue
      }
      for axis in 0..<dim {
        let p2 = step(p, axis)
        if valid(p2, q) {
          eid[edge_key(state(p, q), 0, axis)] = edge_ends.length()
          edge_ends.push((vid[state(p, q)], vid[state(p2, q)]))
        }
        let q2 = step(q, axis)
        if valid(p, q2) {
          eid[edge_key(state(p, q), 1, axis)] = edge_ends.length()
          edge_ends.push((vid[state(p, q)], vid[state(p, q2)]))
        }
      }
    }
  }
  let ne = edge_ends.length()
  // b₀：並查集
  let parent : Array[Int32] = []
  for i in 0..<nv {
    parent.push(i)
  }
  let find = fn(a : Int32) -> Int32 {
    let mut r = a
    while parent[r] != r {
      r = parent[r]
    }
    r
  }
  for e in edge_ends {
    let (u, v) = e
    let ru = find(u)
    let rv = find(v)
    if ru != rv {
      parent[ru] = rv
    }
  }
  let mut b0 = 0
  for i in 0..<nv {
    if parent[i] == i {
      b0 += 1
    }
  }
  // 方格的邊界（四條邊），以 𝔽₂ 列向量存放
  let words = (ne + 29) / 30
  let rows : Array[Array[Int32]] = []
  let add_square = fn(es : Array[Int32]) {
    let row = Array::make(words, 0)
    for e in es {
      row[e / 30] = row[e / 30] ^ (1 << (e % 30))
    }
    rows.push(row)
  }
  let get = fn(s : Int32, who : Int32, axis : Int32) -> Int32 {
    eid.get(edge_key(s, who, axis)).unwrap_or(-1)
  }
  for p in 0..<cells {
    for q in 0..<cells {
      if p == q {
        continue
      }
      let s = state(p, q)
      // (i) 兩個方體各動一步
      for a in 0..<dim {
        for b in 0..<dim {
          let p2 = step(p, a)
          let q2 = step(q, b)
          if p2 < 0 || q2 < 0 {
            continue
          }
          if p == q2 || p2 == q || p2 == q2 {
            continue
          }
          let e1 = get(s, 0, a)
          let e2 = get(s, 1, b)
          let e3 = get(state(p2, q), 1, b)
          let e4 = get(state(p, q2), 0, a)
          if e1 >= 0 && e2 >= 0 && e3 >= 0 && e4 >= 0 {
            add_square([e1, e2, e3, e4])
          }
        }
      }
      // (ii) 同一方體沿兩個軸各動一步
      for a in 0..<dim {
        for b in (a + 1)..<dim {
          // who = 0 移動 p、who = 1 移動 q；另一個方體留在原位
          for who in 0..<2 {
            let (mover, other) = if who == 0 { (p, q) } else { (q, p) }
            let ma = step(mover, a)
            let mb = step(mover, b)
            if ma < 0 || mb < 0 {
              continue
            }
            let mab = step(ma, b)
            if mab < 0 || ma == other || mb == other || mab == other {
              continue
            }
            let at = fn(m : Int32) -> Int32 {
              if who == 0 {
                state(m, q)
              } else {
                state(p, m)
              }
            }
            let e1 = get(s, who, a)
            let e2 = get(s, who, b)
            let e3 = get(at(ma), who, b)
            let e4 = get(at(mb), who, a)
            if e1 >= 0 && e2 >= 0 && e3 >= 0 && e4 >= 0 {
              add_square([e1, e2, e3, e4])
            }
          }
        }
      }
    }
  }
  let squares = rows.length()
  let r2 = rank_gf2(rows, ne)
  // b₁ = dim ker ∂₁ − rank ∂₂ = (E − (V − b₀)) − rank ∂₂
  let b1 = ne - (nv - b0) - r2
  { dim, grid, vertices: nv, edges: ne, squares, b0, b1, }
}

///|
/// 二維的辮子不變量：沿一條狀態路徑，差向量 q − p 繞原點的半圈數（以象限穿越計）。
/// 交換兩個方體的兩條路徑（自上方或自下方繞過）相差一整圈——純辮群 P₂ ≅ ℤ 的生成元。
/// 回傳（上繞路徑的四分之一圈數, 下繞路徑的四分之一圈數）。
pub fn swap_windings() -> (Int32, Int32) {
  // 3×3 格子；p 起於 (0,1)，q 起於 (2,1)；交換位置。
  // 狀態以座標對表示；路徑為手寫的合法移動序列（每步只動一個方體一格）。
  let quadrant = fn(dx : Int32, dy : Int32) -> Int32 {
    // 以半開象限編號，使軸上的點有確定歸屬
    if dx > 0 && dy >= 0 {
      0
    } else if dx <= 0 && dy > 0 {
      1
    } else if dx < 0 && dy <= 0 {
      2
    } else {
      3
    }
  }
  let winding = fn(path : Array[(Int32, Int32, Int32, Int32)]) -> Int32 {
    let mut total = 0
    for k in 1..<path.length() {
      let (px0, py0, qx0, qy0) = path[k - 1]
      let (px1, py1, qx1, qy1) = path[k]
      let a = quadrant(qx0 - px0, qy0 - py0)
      let b = quadrant(qx1 - px1, qy1 - py1)
      let d = (b - a + 4) % 4
      total += if d == 3 { -1 } else { d }
    }
    total
  }
  // 上繞：q 向上、向左越過 p 上方、再向下；p 同時向右
  let over : Array[(Int32, Int32, Int32, Int32)] = [
    (0, 1, 2, 1),
    (0, 1, 2, 2),
    (0, 1, 1, 2),
    (1, 1, 1, 2),
    (1, 1, 0, 2),
    (2, 1, 0, 2),
    (2, 1, 0, 1),
  ]
  let under : Array[(Int32, Int32, Int32, Int32)] = [
    (0, 1, 2, 1),
    (0, 1, 2, 0),
    (0, 1, 1, 0),
    (1, 1, 1, 0),
    (1, 1, 0, 0),
    (2, 1, 0, 0),
    (2, 1, 0, 1),
  ]
  (winding(over), winding(under))
}
