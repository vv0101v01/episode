///|
/// 有限群（乘法表；0 為單位元）——作為單物件 1-群胚，即 1-截斷的 ω-群胚模型。
pub(all) struct FinGroup {
  mul : Array[Array[Int32]]
  inv : Array[Int32]
}

///|
pub fn FinGroup::from_table(mul : Array[Array[Int32]]) -> FinGroup {
  let n = mul.length()
  let inv = Array::make(n, 0)
  for a in 0..<n {
    for b in 0..<n {
      if mul[a][b] == 0 {
        inv[a] = b
      }
    }
  }
  { mul, inv, }
}

///|
pub fn FinGroup::cyclic(n : Int32) -> FinGroup {
  let mul : Array[Array[Int32]] = []
  for a in 0..<n {
    let row : Array[Int32] = []
    for b in 0..<n {
      row.push((a + b) % n)
    }
    mul.push(row)
  }
  FinGroup::from_table(mul)
}

///|
/// 對稱群 S₃（非交換）：元素為 {0,1,2} 的排列，依字典序編號，0 為恆等。
pub fn FinGroup::symmetric3() -> FinGroup {
  let perms = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
  let index = fn(p : Array[Int32]) -> Int32 {
    for k in 0..<6 {
      if perms[k] == p {
        return k
      }
    }
    0
  }
  let mul : Array[Array[Int32]] = []
  for a in 0..<6 {
    let row : Array[Int32] = []
    for b in 0..<6 {
      // 先 a 後 b
      row.push(
        index([
          perms[b][perms[a][0]],
          perms[b][perms[a][1]],
          perms[b][perms[a][2]],
        ]),
      )
    }
    mul.push(row)
  }
  FinGroup::from_table(mul)
}

///|
pub fn FinGroup::order(self : FinGroup) -> Int32 {
  self.mul.length()
}

///|
/// 粘貼圖式的 1-骨架是一條鏈 x₀ → x₁ → … → xₙ。回傳（每個 0 維變數在鏈上的位置（非 0 維為 -1），
/// 每段鏈所選的 1 維變數）。
fn chain_of(ps : Array[Ty]) -> (Array[Int32], Array[Int32]) {
  let pos = Array::make(ps.length(), -1)
  let edges : Array[Int32] = []
  let mut count = 0
  for k in 0..<ps.length() {
    match ps[k] {
      Obj => {
        pos[k] = count
        count += 1
      }
      Arr(Obj, Var(s), Var(_)) =>
        // 每段只取第一個 1 維變數（其餘平行者在模型中與之相等）
        if pos[s] == edges.length() {
          edges.push(k)
        }
      _ => ()
    }
  }
  (pos, edges)
}

///|
/// 1 維項在群模型中的值。`env[k]` 為上下文第 k 個變數的賦值（僅 1 維變數有意義）。
/// 融貫子 coh_{Δ, u→v}[σ] 的值 = Δ 的鏈上由 u 至 v 的有向積（逆向則取逆）——
/// 這正是「粘貼圖式可縮」在 1-截斷模型中的內容。
pub fn Theory::eval1(
  self : Theory,
  g : FinGroup,
  env : Array[Int32],
  t : Tm,
) -> Int32 raise CattError {
  match t {
    Var(k) => env[k]
    Coh(c, sigma) => {
      let coh = self.cohs[c]
      match coh.ty {
        Arr(Obj, Var(u), Var(v)) => {
          let (pos, edges) = chain_of(coh.ps)
          let pu = pos[u]
          let pv = pos[v]
          let mut acc = 0
          if pu <= pv {
            for k in pu..<pv {
              acc = g.mul[acc][self.eval1(g, env, sigma[edges[k]])]
            }
          } else {
            let mut k = pu - 1
            while k >= pv {
              acc = g.mul[acc][g.inv[self.eval1(g, env, sigma[edges[k]])]]
              k -= 1
            }
          }
          acc
        }
        _ => raise Reject("eval1: term is not 1-dimensional")
      }
    }
  }
}

///|
/// 健全性（於群模型）：對上下文 Γ 的一切「合法賦值」（每個 ≥2 維變數的源與靶取值相同），
/// 每個 2 維融貫子實例的源與靶取值相同。於庫中各 2 維融貫子的粘貼圖式上窮舉賦值。
/// 回傳（受檢融貫子數, 受檢賦值數, 全部成立）。
pub fn verify_group_model(
  lib : Library,
  g : FinGroup,
) -> (Int32, Int32, Bool) raise CattError {
  let th = lib.theory
  let mut cohs = 0
  let mut assignments = 0
  let mut ok = true
  for coh in th.cohs {
    let (s, t) = match coh.ty {
      Arr(Arr(Obj, _, _), s, t) => (s, t)
      _ => continue
    }
    cohs += 1
    let ps = coh.ps
    // 1 維變數清單
    let ones : Array[Int32] = []
    for k in 0..<ps.length() {
      if ps[k].dim() == 1 {
        ones.push(k)
      }
    }
    let n = g.order()
    let mut total = 1
    for _ in ones {
      total *= n
    }
    for code in 0..<total {
      let env = Array::make(ps.length(), 0)
      let mut c = code
      for k in ones {
        env[k] = c % n
        c = c / n
      }
      // 合法性：每個 2 維變數 a : f → g 要求 env[f] = env[g]
      let mut legal = true
      for k in 0..<ps.length() {
        match ps[k] {
          Arr(Arr(Obj, _, _), Var(f), Var(h)) =>
            if env[f] != env[h] {
              legal = false
            }
          _ => ()
        }
      }
      if !legal {
        continue
      }
      assignments += 1
      if th.eval1(g, env, s) != th.eval1(g, env, t) {
        ok = false
      }
    }
  }
  (cohs, assignments, ok)
}

///|
/// ω-範疇模式下應被拒的類型（逆元、非粘貼上下文等）；回傳被拒數與總數。
pub fn verify_rejections() -> (Int32, Int32) {
  let th = Theory::new(groupoid=false)
  let ps1 = [Obj, Obj, arr0(0, 1)]
  let cases : Array[(Array[Ty], Ty)] = [
    // 逆元 y → x：ω-範疇中不可導
    (ps1, arr0(1, 0)),
    // 端點自環 x → x：未用到 f
    (ps1, arr0(0, 0)),
    // 兩個孤立點：非粘貼圖式
    ([Obj, Obj], arr0(0, 1)),
    // 分叉 x→y, x→z：非粘貼圖式
    ([Obj, Obj, arr0(0, 1), Obj, arr0(0, 3)], arr0(1, 3)),
    // 匯合 x→z, y→z：非粘貼圖式
    ([Obj, Obj, Obj, arr0(0, 2), arr0(1, 2)], arr0(0, 1)),
    // 合成的反向 z → x
    ([Obj, Obj, arr0(0, 1), Obj, arr0(1, 3)], arr0(3, 0)),
  ]
  let mut rejected = 0
  for case in cases {
    let (ps, ty) = case
    try th.add_coherence("probe", ps, ty) catch {
      _ => rejected += 1
    } noraise {
      _ => ()
    }
  }
  (rejected, cases.length())
}
