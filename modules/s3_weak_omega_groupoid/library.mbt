///|
/// 標準融貫子庫的編號。
pub(all) struct Library {
  theory : Theory
  id : Int32
  comp : Int32
  assoc : Int32
  unit_l : Int32
  unit_r : Int32
  vcomp : Int32
  hcomp : Int32
  id2 : Int32
  interchange : Int32
  /// 僅 ω-群胚模式：逆元與抵消
  inv : Int32
  inv_r : Int32
  inv_l : Int32
}

///|
fn arr0(s : Int32, t : Int32) -> Ty {
  Arr(Obj, Var(s), Var(t))
}

///|
fn arr1(x : Int32, y : Int32, f : Int32, g : Int32) -> Ty {
  Arr(arr0(x, y), Var(f), Var(g))
}

///|
/// 建立標準庫。ω-範疇模式下逆元三項為 -1（且嘗試登錄時被拒）。
pub fn Library::build(groupoid~ : Bool) -> Library raise CattError {
  let th = Theory::new(groupoid~)
  // id : (x:*) ⊢ x → x
  let id = th.add_coherence("id", [Obj], arr0(0, 0))
  // comp : (x, y, f:x→y, z, g:y→z) ⊢ x → z
  let ps2 = [Obj, Obj, arr0(0, 1), Obj, arr0(1, 3)]
  let comp = th.add_coherence("comp", ps2, arr0(0, 3))
  let c = fn(x : Tm, y : Tm, f : Tm, z : Tm, g : Tm) -> Tm {
    Coh(comp, [x, y, f, z, g])
  }
  // assoc : (x,y,f,z,g,w,h) ⊢ (f·g)·h → f·(g·h)
  let ps3 = [Obj, Obj, arr0(0, 1), Obj, arr0(1, 3), Obj, arr0(3, 5)]
  let fg = c(Var(0), Var(1), Var(2), Var(3), Var(4))
  let gh = c(Var(1), Var(3), Var(4), Var(5), Var(6))
  let assoc = th.add_coherence(
    "assoc",
    ps3,
    Arr(
      arr0(0, 5),
      c(Var(0), Var(3), fg, Var(5), Var(6)),
      c(Var(0), Var(1), Var(2), Var(5), gh),
    ),
  )
  // 單位律：(x,y,f) ⊢ id x · f → f，f · id y → f
  let ps1 = [Obj, Obj, arr0(0, 1)]
  let unit_l = th.add_coherence(
    "unit-l",
    ps1,
    Arr(
      arr0(0, 1),
      c(Var(0), Var(0), Coh(id, [Var(0)]), Var(1), Var(2)),
      Var(2),
    ),
  )
  let unit_r = th.add_coherence(
    "unit-r",
    ps1,
    Arr(
      arr0(0, 1),
      c(Var(0), Var(1), Var(2), Var(1), Coh(id, [Var(1)])),
      Var(2),
    ),
  )
  // 垂直合成：(x,y,f,g,a:f→g,h,b:g→h) ⊢ f → h
  let psv = [
    Obj,
    Obj,
    arr0(0, 1),
    arr0(0, 1),
    arr1(0, 1, 2, 3),
    arr0(0, 1),
    arr1(0, 1, 3, 5),
  ]
  let vcomp = th.add_coherence("vcomp", psv, arr1(0, 1, 2, 5))
  // 水平合成：(x,y,f,g,a:f→g,z,h,k,b:h→k) ⊢ f·h → g·k
  let psh = [
    Obj,
    Obj,
    arr0(0, 1),
    arr0(0, 1),
    arr1(0, 1, 2, 3),
    Obj,
    arr0(1, 5),
    arr0(1, 5),
    arr1(1, 5, 6, 7),
  ]
  let hcomp = th.add_coherence(
    "hcomp",
    psh,
    Arr(
      arr0(0, 5),
      c(Var(0), Var(1), Var(2), Var(5), Var(6)),
      c(Var(0), Var(1), Var(3), Var(5), Var(7)),
    ),
  )
  // id2 : (x,y,f) ⊢ f → f
  let id2 = th.add_coherence("id2", ps1, arr1(0, 1, 2, 2))
  // 交換律（三維融貫子）：
  // (x,y,f,g,a,h,b, z,k,l,c,m,d) ⊢ (a∘b) * (c∘d) → (a*c) ∘ (b*d)
  let psi = [
    Obj,
    Obj,
    arr0(0, 1),
    arr0(0, 1),
    arr1(0, 1, 2, 3),
    arr0(0, 1),
    arr1(0, 1, 3, 5),
    Obj,
    arr0(1, 7),
    arr0(1, 7),
    arr1(1, 7, 8, 9),
    arr0(1, 7),
    arr1(1, 7, 9, 11),
  ]
  let v = fn(x : Tm, y : Tm, f : Tm, g : Tm, a : Tm, h : Tm, b : Tm) -> Tm {
    Coh(vcomp, [x, y, f, g, a, h, b])
  }
  let hz = fn(
    x : Tm,
    y : Tm,
    f : Tm,
    g : Tm,
    a : Tm,
    z : Tm,
    h : Tm,
    k : Tm,
    b : Tm,
  ) -> Tm {
    Coh(hcomp, [x, y, f, g, a, z, h, k, b])
  }
  let ab = v(Var(0), Var(1), Var(2), Var(3), Var(4), Var(5), Var(6))
  let cd = v(Var(1), Var(7), Var(8), Var(9), Var(10), Var(11), Var(12))
  let lhs = hz(Var(0), Var(1), Var(2), Var(5), ab, Var(7), Var(8), Var(11), cd)
  let ac = hz(
    Var(0),
    Var(1),
    Var(2),
    Var(3),
    Var(4),
    Var(7),
    Var(8),
    Var(9),
    Var(10),
  )
  let bd = hz(
    Var(0),
    Var(1),
    Var(3),
    Var(5),
    Var(6),
    Var(7),
    Var(9),
    Var(11),
    Var(12),
  )
  let f_k = c(Var(0), Var(1), Var(2), Var(7), Var(8))
  let g_l = c(Var(0), Var(1), Var(3), Var(7), Var(9))
  let h_m = c(Var(0), Var(1), Var(5), Var(7), Var(11))
  let rhs = v(Var(0), Var(7), f_k, g_l, ac, h_m, bd)
  let interchange = th.add_coherence(
    "interchange",
    psi,
    Arr(Arr(arr0(0, 7), f_k, h_m), lhs, rhs),
  )
  let mut inv = -1
  let mut inv_r = -1
  let mut inv_l = -1
  if groupoid {
    inv = th.add_coherence("inv", ps1, arr0(1, 0))
    let f_inv = Coh(inv, [Var(0), Var(1), Var(2)])
    inv_r = th.add_coherence(
      "inv-r",
      ps1,
      Arr(
        arr0(0, 0),
        c(Var(0), Var(1), Var(2), Var(0), f_inv),
        Coh(id, [Var(0)]),
      ),
    )
    inv_l = th.add_coherence(
      "inv-l",
      ps1,
      Arr(
        arr0(1, 1),
        c(Var(1), Var(0), f_inv, Var(1), Var(2)),
        Coh(id, [Var(1)]),
      ),
    )
  }
  {
    theory: th,
    id,
    comp,
    assoc,
    unit_l,
    unit_r,
    vcomp,
    hcomp,
    id2,
    interchange,
    inv,
    inv_r,
    inv_l,
  }
}
