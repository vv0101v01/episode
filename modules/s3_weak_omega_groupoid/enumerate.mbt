///|
/// 列舉恰有 n 個變數的全部球狀上下文（每個變數的類型為 * 或以先前兩個平行變數為端點的箭頭）。
pub fn globular_contexts(n : Int32) -> Array[Array[Ty]] {
  let out : Array[Array[Ty]] = []
  fn go(ctx : Array[Ty]) -> Unit {
    if ctx.length() == n {
      out.push(ctx.copy())
      return
    }
    ctx.push(Obj)
    go(ctx)
    ignore(ctx.pop())
    let k = ctx.length()
    for s in 0..<k {
      for t in 0..<k {
        if ty_equal(ctx[s], ctx[t]) {
          ctx.push(Arr(ctx[s], Var(s), Var(t)))
          go(ctx)
          ignore(ctx.pop())
        }
      }
    }
  }

  go([])
  out
}

///|
/// 依排列 perm（新位置 → 舊變數）重排球狀上下文；若違反依賴次序則回傳 None。
fn reorder(ctx : Array[Ty], perm : Array[Int32]) -> Array[Ty]? {
  let n = ctx.length()
  let new_pos = Array::make(n, 0)
  for p in 0..<n {
    new_pos[perm[p]] = p
  }
  fn rename(t : Ty, limit : Int32) -> Ty? {
    match t {
      Obj => Some(Obj)
      Arr(a, Var(s), Var(u)) => {
        if new_pos[s] >= limit || new_pos[u] >= limit {
          return None
        }
        match rename(a, limit) {
          Some(a2) => Some(Arr(a2, Var(new_pos[s]), Var(new_pos[u])))
          None => None
        }
      }
      Arr(_, _, _) => None
    }
  }

  let out : Array[Ty] = []
  for p in 0..<n {
    match rename(ctx[perm[p]], p) {
      Some(t) => out.push(t)
      None => return None
    }
  }
  Some(out)
}

///|
fn permutations(n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let cur : Array[Int32] = []
  let used = Array::make(n, false)
  fn go() -> Unit {
    if cur.length() == n {
      out.push(cur.copy())
      return
    }
    for i in 0..<n {
      if !used[i] {
        used[i] = true
        cur.push(i)
        go()
        ignore(cur.pop())
        used[i] = false
      }
    }
  }

  go()
  out
}

///|
/// 定理（粘貼圖式的兩種刻畫一致）的窮舉驗證：對一切 n 個變數的球狀上下文，
/// 「存在一個重排被 ⊢ps 接受」⇔「⊳ 為全序」。
/// 回傳（上下文數, 粘貼圖式數（計入同構重複）, 兩刻畫一致）。
pub fn verify_ps_characterization(n : Int32) -> (Int32, Int32, Bool) {
  let ctxs = globular_contexts(n)
  let perms = permutations(n)
  let mut ps_count = 0
  let mut agree = true
  for ctx in ctxs {
    let mut some_ps = false
    for perm in perms {
      if reorder(ctx, perm) is Some(c) && is_pasting_scheme(c) {
        some_ps = true
        break
      }
    }
    if some_ps {
      ps_count += 1
    }
    if some_ps != triangle_order_is_linear(ctx) {
      agree = false
    }
  }
  (ctxs.length(), ps_count, agree)
}
