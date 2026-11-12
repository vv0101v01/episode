///|
/// Eₙ(2) 的離散模型：有序二點構形空間 Conf₂(ℝⁿ) ≃ Sⁿ⁻¹ 的方體複形（Abrams 式離散化）。
/// 兩個帶標號的點位於 gridⁿ 格點上；一個胞腔是格子複形中兩個閉包不交的胞腔之積
/// σ × τ：σ = 基點 p 加上可動軸集 S，τ = 基點 q 加上可動軸集 T，維數 |S| + |T|。
/// 0-胞腔為狀態，1-胞腔為一個點沿一個軸移動一步，2-胞腔為兩個可交換的移動，依此類推。
pub(all) struct ConfReport {
  dim : Int32
  grid : Int32
  /// 各維胞腔數（0 維至 `betti.length()` 維）
  cells : Array[Int32]
  /// 𝔽₂ 係數的 Betti 數 b₀ … b_top，top = max(1, dim − 1)
  betti : Array[Int32]
}

///|
/// 𝔽₂ 上一組稀疏向量（各以非零座標列表給出）的秩：逐一對「最低非零位 → 向量」的
/// 樞軸表消去。向量以 30 位元分塊存放。
fn rank_gf2(columns : Array[Array[Int32]], nrows : Int32) -> Int32 {
  let words = (nrows + 29) / 30
  let pivots : Map[Int32, Array[Int32]] = Map([])
  let mut rank = 0
  for col in columns {
    let v = Array::make(words, 0)
    for r in col {
      v[r / 30] = v[r / 30] ^ (1 << (r % 30))
    }
    let mut w = 0
    while w < words {
      if v[w] == 0 {
        w += 1
        continue
      }
      let low = w * 30 + v[w].ctz()
      match pivots.get(low) {
        Some(pv) =>
          for k in w..<words {
            v[k] = v[k] ^ pv[k]
          }
        None => {
          pivots[low] = v
          rank += 1
          break
        }
      }
    }
  }
  rank
}

///|
/// 建立離散構形複形並計算 Betti 數。
pub fn configuration_space(dim : Int32, grid : Int32) -> ConfReport {
  let top = if dim > 2 { dim - 1 } else { 1 }
  let mut points = 1
  for _ in 0..<dim {
    points *= grid
  }
  let masks = 1 << dim
  let coord = fn(p : Int32, axis : Int32) -> Int32 {
    let mut stride = 1
    for _ in 0..<axis {
      stride *= grid
    }
    p / stride % grid
  }
  let stride_of = fn(axis : Int32) -> Int32 {
    let mut stride = 1
    for _ in 0..<axis {
      stride *= grid
    }
    stride
  }
  // 格子胞腔 (p, S) 合法：S 中每個軸上 p 皆可再進一步
  let fits = fn(p : Int32, s : Int32) -> Bool {
    for a in 0..<dim {
      if ((s >> a) & 1) == 1 && coord(p, a) + 1 >= grid {
        return false
      }
    }
    true
  }
  // 兩個格子胞腔閉包不交 ⇔ 存在某軸使兩個閉區間不交
  let disjoint = fn(p : Int32, s : Int32, q : Int32, t : Int32) -> Bool {
    for a in 0..<dim {
      let pa = coord(p, a)
      let qa = coord(q, a)
      if pa + ((s >> a) & 1) < qa || qa + ((t >> a) & 1) < pa {
        return true
      }
    }
    false
  }
  let key = fn(p : Int32, s : Int32, q : Int32, t : Int32) -> Int32 {
    ((p * masks + s) * points + q) * masks + t
  }
  // 依維數列舉胞腔（至 top + 1 維）
  let index : Map[Int32, Int32] = Map([])
  let by_dim : Array[Array[(Int32, Int32, Int32, Int32)]] = []
  for _ in 0..<(top + 2) {
    by_dim.push([])
  }
  for p in 0..<points {
    for s in 0..<masks {
      if !fits(p, s) {
        continue
      }
      for q in 0..<points {
        for t in 0..<masks {
          let k = s.popcnt() + t.popcnt()
          if k > top + 1 || !fits(q, t) || !disjoint(p, s, q, t) {
            continue
          }
          index[key(p, s, q, t)] = by_dim[k].length()
          by_dim[k].push((p, s, q, t))
        }
      }
    }
  }
  // ∂ₖ 的秩：每個 k-胞腔的邊界為去掉一個可動軸後的前、後兩個面
  let ranks : Array[Int32] = [0]
  for k in 1..<(top + 2) {
    let columns : Array[Array[Int32]] = []
    for cell in by_dim[k] {
      let (p, s, q, t) = cell
      let faces : Array[Int32] = []
      for a in 0..<dim {
        let bit = 1 << a
        if (s & bit) != 0 {
          faces.push(index.get(key(p, s ^ bit, q, t)).unwrap_or(-1))
          faces.push(
            index.get(key(p + stride_of(a), s ^ bit, q, t)).unwrap_or(-1),
          )
        }
        if (t & bit) != 0 {
          faces.push(index.get(key(p, s, q, t ^ bit)).unwrap_or(-1))
          faces.push(
            index.get(key(p, s, q + stride_of(a), t ^ bit)).unwrap_or(-1),
          )
        }
      }
      columns.push(faces)
    }
    ranks.push(rank_gf2(columns, by_dim[k - 1].length()))
  }
  let cells : Array[Int32] = []
  let betti : Array[Int32] = []
  for k in 0..<(top + 2) {
    cells.push(by_dim[k].length())
  }
  for k in 0..<(top + 1) {
    betti.push(cells[k] - ranks[k] - ranks[k + 1])
  }
  { dim, grid, cells, betti, }
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
