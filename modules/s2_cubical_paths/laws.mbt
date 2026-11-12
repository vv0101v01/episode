///|
/// 路徑代數的判定性定律——全部由核心 NbE 判定，無任何公設等式。
pub(all) struct PathLaws {
  /// sym (sym p) ≡ p（德摩根對合）
  sym_involution : Bool
  /// sym refl ≡ refl
  sym_refl : Bool
  /// ap id p ≡ p；ap (g∘f) p ≡ ap g (ap f p)；ap f refl ≡ refl；ap f (sym p) ≡ sym (ap f p)
  ap_id : Bool
  ap_compose : Bool
  ap_refl : Bool
  ap_sym : Bool
  /// 路徑 η：⟨i⟩ p @ i ≡ p
  path_eta : Bool
  /// 函數外延性通過檢查，且 happly (funext h) ≡ h、funext (happly q) ≡ q
  funext_typed : Bool
  funext_roundtrip : Bool
  happly_roundtrip : Bool
  /// 連接方塊通過檢查；其對角線 ≡ p（∧ 冪等）
  meet_square_typed : Bool
  join_square_typed : Bool
  square_diagonal : Bool
  /// 德摩根：(meet-square p)@¬i@¬j ≡ (join-square (sym p))@i@j
  de_morgan_square : Bool
  /// 二維生成元 surf 的轉置與反轉皆通過檢查；其邊界化為 base
  surf_transpose_typed : Bool
  surf_boundary : Bool
  /// 端點不符的路徑被拒
  rejects_wrong_endpoint : Bool
  /// sym p 與 p 於 a ≠ b 時類型不同（被拒）
  rejects_sym_as_same : Bool
  /// 遙測
  beta : Int32
  path_beta : Int32
  boundary : Int32
  eta_expansions : Int32
}

///|
pub fn PathLaws::all(self : PathLaws) -> Bool {
  self.sym_involution &&
  self.sym_refl &&
  self.ap_id &&
  self.ap_compose &&
  self.ap_refl &&
  self.ap_sym &&
  self.path_eta &&
  self.funext_typed &&
  self.funext_roundtrip &&
  self.happly_roundtrip &&
  self.meet_square_typed &&
  self.join_square_typed &&
  self.square_diagonal &&
  self.de_morgan_square &&
  self.surf_transpose_typed &&
  self.surf_boundary &&
  self.rejects_wrong_endpoint &&
  self.rejects_sym_as_same
}

///|
/// 標準理論：類型 A、B、C、S2；點 a b : A；路徑 p : a = b；函數 f g f' ；
/// 逐點同倫 h : Π x. f x = f' x；球面 base 與 surf : refl = refl。
pub fn standard_theory() -> Theory raise CubicalError {
  let th = Theory::new()
  th.declare_base("A")
  th.declare_base("B")
  th.declare_base("C")
  th.declare_base("S2")
  let a_ty = TBase("A")
  let b_ty = TBase("B")
  th.add_const("a", a_ty)
  th.add_const("b", a_ty)
  th.add_const("p", path_ty(0, a_ty, Const("a"), Const("b")))
  th.add_const("f", TPi(a_ty, b_ty))
  th.add_const("f'", TPi(a_ty, b_ty))
  th.add_const("g", TPi(b_ty, TBase("C")))
  th.add_const(
    "h",
    TPi(
      a_ty,
      path_ty(0, b_ty, App(Const("f"), Var(0)), App(Const("f'"), Var(0))),
    ),
  )
  th.add_const("q", path_ty(0, TPi(a_ty, b_ty), Const("f"), Const("f'")))
  th.add_const("base", TBase("S2"))
  let loop_ty = path_ty(1, TBase("S2"), Const("base"), Const("base"))
  th.add_const(
    "surf",
    path_ty(0, loop_ty, refl(1, Const("base")), refl(1, Const("base"))),
  )
  th
}

///|
pub fn verify_path_laws() -> PathLaws raise CubicalError {
  let th = standard_theory()
  let a_ty = TBase("A")
  let b_ty = TBase("B")
  let c_ty = TBase("C")
  let a = Const("a")
  let b = Const("b")
  let p = Const("p")
  let f = Const("f")
  let g = Const("g")
  let pab = path_ty(0, a_ty, a, b)
  let pba = path_ty(0, a_ty, b, a)
  let paa = path_ty(0, a_ty, a, a)
  let sym_involution = th.definitionally_equal(
    sym(1, Ann(sym(2, p), pba)),
    p,
    pab,
  )
  let sym_refl = th.definitionally_equal(
    sym(1, Ann(refl(2, a), paa)),
    refl(3, a),
    paa,
  )
  let id_fn = Ann(Lam(Var(0)), TPi(a_ty, a_ty))
  let ap_id = th.definitionally_equal(ap(1, id_fn, p), p, pab)
  let gf = Ann(Lam(App(g, App(f, Var(0)))), TPi(a_ty, c_ty))
  let gfa = App(g, App(f, a))
  let gfb = App(g, App(f, b))
  let fa = App(f, a)
  let fb = App(f, b)
  let pfab = path_ty(0, b_ty, fa, fb)
  let ap_f_p = Ann(ap(1, f, p), pfab)
  let ap_compose = th.definitionally_equal(
    ap(1, gf, p),
    ap(2, g, ap_f_p),
    path_ty(0, c_ty, gfa, gfb),
  )
  let ap_refl = th.definitionally_equal(
    ap(1, f, Ann(refl(2, a), paa)),
    refl(3, fa),
    path_ty(0, b_ty, fa, fa),
  )
  let ap_sym = th.definitionally_equal(
    ap(1, f, Ann(sym(2, p), pba)),
    sym(3, ap_f_p),
    path_ty(0, b_ty, fb, fa),
  )
  let path_eta = th.definitionally_equal(PLam(5, PApp(p, dim(5))), p, pab)
  // 函數外延性
  let fn_ty = TPi(a_ty, b_ty)
  let pff = path_ty(0, fn_ty, f, Const("f'"))
  let h_ty = TPi(
    a_ty,
    path_ty(0, b_ty, App(f, Var(0)), App(Const("f'"), Var(0))),
  )
  let (funext_typed, _) = th.accepts(funext(1, Const("h")), pff)
  let funext_roundtrip = th.definitionally_equal(
    happly(2, Ann(funext(1, Const("h")), pff)),
    Const("h"),
    h_ty,
  )
  let happly_roundtrip = th.definitionally_equal(
    funext(1, Ann(happly(2, Const("q")), h_ty)),
    Const("q"),
    pff,
  )
  // 連接方塊：⟨i⟩⟨j⟩ p@(i∧j) : PathP (i. Path A a (p@i)) (⟨j⟩ a) p
  let meet_ty = TPathP(1, path_ty(0, a_ty, a, PApp(p, dim(1))), refl(2, a), p)
  let join_ty = TPathP(1, path_ty(0, a_ty, PApp(p, dim(1)), b), p, refl(2, b))
  let meet_sq = connection_square(1, 2, p, meet=true)
  let join_sq = connection_square(1, 2, p, meet=false)
  let (meet_square_typed, _) = th.accepts(meet_sq, meet_ty)
  let (join_square_typed, _) = th.accepts(join_sq, join_ty)
  let square_diagonal = th.definitionally_equal(
    PLam(3, PApp(PApp(Ann(meet_sq, meet_ty), dim(3)), dim(3))),
    p,
    pab,
  )
  // 德摩根：⟨i⟩⟨j⟩ meet_sq@¬i@¬j ≡ join-square(sym p)，類型 PathP (i. Path A ((sym p)@i) a) (sym p) refl
  let sp = Ann(sym(4, p), pba)
  let dm_ty = TPathP(1, path_ty(0, a_ty, PApp(sp, dim(1)), a), sp, refl(2, a))
  let lhs = PLam(
    5,
    PLam(
      6,
      PApp(PApp(Ann(meet_sq, meet_ty), @s1.Dm::co_name(5)), @s1.Dm::co_name(6)),
    ),
  )
  let rhs = connection_square(1, 2, sp, meet=false)
  let de_morgan_square = th.definitionally_equal(lhs, rhs, dm_ty)
  // 球面
  let loop_ty = path_ty(1, TBase("S2"), Const("base"), Const("base"))
  let surf_ty = path_ty(
    0,
    loop_ty,
    refl(1, Const("base")),
    refl(1, Const("base")),
  )
  let transpose = PLam(1, PLam(2, PApp(PApp(Const("surf"), dim(2)), dim(1))))
  let flipped = PLam(
    1,
    PLam(2, PApp(PApp(Const("surf"), @s1.Dm::co_name(1)), dim(2))),
  )
  let (t1, _) = th.accepts(transpose, surf_ty)
  let (t2, _) = th.accepts(flipped, surf_ty)
  let surf_boundary = th.definitionally_equal(
    PLam(1, PApp(PApp(Const("surf"), dim(1)), @s1.Dm::one())),
    refl(1, Const("base")),
    loop_ty,
  )
  let (wrong, _) = th.accepts(refl(1, a), pab)
  let (sym_same, _) = th.accepts(sym(1, p), pab)
  {
    sym_involution,
    sym_refl,
    ap_id,
    ap_compose,
    ap_refl,
    ap_sym,
    path_eta,
    funext_typed,
    funext_roundtrip,
    happly_roundtrip,
    meet_square_typed,
    join_square_typed,
    square_diagonal,
    de_morgan_square,
    surf_transpose_typed: t1 && t2,
    surf_boundary,
    rejects_wrong_endpoint: !wrong,
    rejects_sym_as_same: !sym_same,
    beta: th.beta,
    path_beta: th.path_beta,
    boundary: th.boundary,
    eta_expansions: th.eta + th.path_eta,
  }
}
