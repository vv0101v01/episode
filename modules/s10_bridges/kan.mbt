///|
/// 組合範例 1 — Kan 擴展。把群看成單對象範疇，G-集即函子 BG → Set；
/// 沿包含 i : H ↪ G 的限制 Res = i* 有左伴隨 Lan_i（誘導 G ×_H X）與
/// 右伴隨 Ran_i（餘誘導 Hom_H(G, X)）。兩者皆顯式構造。
///
/// 左 Kan 擴展：G × X 模 (g h, x) ~ (g, h·x)，G 左乘第一分量。
pub fn left_kan(
  mul : Array[Array[Int32]],
  sub : Array[Int32],
  x : GSet,
) -> GSet {
  let n = mul.length()
  let cls = Array::make(n * x.size, -1)
  let mut count = 0
  let reps : Array[(Int32, Int32)] = []
  let inv = inverses(mul)
  for g in 0..<n {
    for p in 0..<x.size {
      if cls[g * x.size + p] >= 0 {
        continue
      }
      // 軌道：(g h⁻¹, h·p)
      for hi in 0..<sub.length() {
        let h = sub[hi]
        cls[mul[g][inv[h]] * x.size + x.act[hi][p]] = count
      }
      reps.push((g, p))
      count += 1
    }
  }
  let act : Array[Array[Int32]] = []
  for g in 0..<n {
    let row : Array[Int32] = []
    for c in 0..<count {
      let (g0, p) = reps[c]
      row.push(cls[mul[g][g0] * x.size + p])
    }
    act.push(row)
  }
  { size: count, act, }
}

///|
/// 右 Kan 擴展：{f : G → X | f(h g) = h·f(g)}，(g·f)(g′) = f(g′ g)。
/// f 由右陪集 H\G 代表元上的值決定，故共 |X|^[G:H] 個。
pub fn right_kan(
  mul : Array[Array[Int32]],
  sub : Array[Int32],
  x : GSet,
) -> GSet {
  let n = mul.length()
  // 右陪集 Hg：cls[g]、代表元 rep、以及 g = h·rep 中的 h（位置）
  let cls = Array::make(n, -1)
  let hpos = Array::make(n, 0)
  let rep : Array[Int32] = []
  for g in 0..<n {
    if cls[g] < 0 {
      for hi in 0..<sub.length() {
        let e = mul[sub[hi]][g]
        cls[e] = rep.length()
        hpos[e] = hi
      }
      rep.push(g)
    }
  }
  let idx = rep.length()
  let mut size = 1
  for _ in 0..<idx {
    size *= x.size
  }
  let act : Array[Array[Int32]] = []
  for g in 0..<n {
    let row : Array[Int32] = []
    for code in 0..<size {
      // 解碼 f 在代表元上的值
      let vals : Array[Int32] = []
      let mut c = code
      for _ in 0..<idx {
        vals.push(c % x.size)
        c = c / x.size
      }
      // (g·f)(rep_j) = f(rep_j g) = h·f(rep_k)，其中 rep_j g = h rep_k
      let mut out = 0
      let mut weight = 1
      for j in 0..<idx {
        let e = mul[rep[j]][g]
        out += weight * x.act[hpos[e]][vals[cls[e]]]
        weight *= x.size
      }
      row.push(out)
    }
    act.push(row)
  }
  { size, act, }
}

///|
pub(all) struct KanReport {
  group_order : Int32
  subgroup_order : Int32
  x_size : Int32
  y_size : Int32
  lan_size : Int32
  ran_size : Int32
  lan_is_action : Bool
  ran_is_action : Bool
  /// |Hom_G(Lan X, Y)| 與 |Hom_H(X, Res Y)|
  left_hom : (Int32, Int32)
  /// |Hom_G(Y, Ran X)| 與 |Hom_H(Res Y, X)|
  right_hom : (Int32, Int32)
}

///|
pub fn KanReport::holds(self : KanReport) -> Bool {
  let index = self.group_order / self.subgroup_order
  let mut pow = 1
  for _ in 0..<index {
    pow *= self.x_size
  }
  self.lan_is_action &&
  self.ran_is_action &&
  self.lan_size == index * self.x_size &&
  self.ran_size == pow &&
  self.left_hom.0 == self.left_hom.1 &&
  self.right_hom.0 == self.right_hom.1
}

///|
/// 定理（Lan ⊣ Res ⊣ Ran，Frobenius 互反）的計數檢驗。
/// `hgens`：H 的生成元；X = H/K（`kgens` 生成 K ≤ H）的不交併再加一個不動點；
/// Y = G/L（`lgens` 生成 L）再加一個不動點。
pub fn verify_kan(
  mul : Array[Array[Int32]],
  hgens : Array[Int32],
  kgens : Array[Int32],
  lgens : Array[Int32],
) -> KanReport {
  let sub = subgroup(mul, hgens)
  let hmul = subgroup_table(mul, sub)
  let pos = positions(mul.length(), sub)
  // K 的生成元須落在 H 內；其餘略去
  let kin : Array[Int32] = []
  for g in kgens {
    if pos[g] >= 0 {
      kin.push(pos[g])
    }
  }
  let x = coset_action(hmul, subgroup(hmul, kin)).with_fixed_point()
  let y = coset_action(mul, subgroup(mul, lgens)).with_fixed_point()
  let lan = left_kan(mul, sub, x)
  let ran = right_kan(mul, sub, x)
  let res = restrict(y, sub)
  {
    group_order: mul.length(),
    subgroup_order: sub.length(),
    x_size: x.size,
    y_size: y.size,
    lan_size: lan.size,
    ran_size: ran.size,
    lan_is_action: lan.is_action(mul),
    ran_is_action: ran.is_action(mul),
    left_hom: (count_equivariant(lan, y), count_equivariant(x, res)),
    right_hom: (count_equivariant(y, ran), count_equivariant(res, x)),
  }
}

///|
/// 橋接 S4 → S3：S4 重寫系統算出的乘法表作為 S3 弱 ω-群胚融貫子的模型。
/// 回傳（2 維融貫子數, 賦值數, 全成立）；群未能完備化或列舉時為 None。
pub fn coherences_in_rewriting_group(
  pres : @s4.Presentation,
) -> (Int32, Int32, Bool)? raise @s3.CattError {
  match group_table(pres, max_rules=200, limit=200) {
    None => None
    Some(table) => {
      let lib = @s3.Library::build(groupoid=true)
      Some(@s3.verify_group_model(lib, @s3.FinGroup::from_table(table)))
    }
  }
}
