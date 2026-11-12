///|
/// 全域公理（伽羅瓦對應）在 S1 上的實例：德摩根否定是自伴的反變伽羅瓦對應，
///   x ≤ ¬y ⇔ y ≤ ¬x，
/// 其閉包算子 ¬¬ 為恆等（每個元素皆閉）。回傳（受檢對數, 成立）。
pub fn verify_negation_galois(names : Int32) -> (Int32, Bool) {
  let elems = @s1.free_algebra(names, limit=400)
  let negs = elems.map(fn(x) { x.neg() })
  let mut ok = true
  let mut n = 0
  for i in 0..<elems.length() {
    if !negs[i].neg().same(elems[i]) {
      ok = false
    }
    for j in 0..<elems.length() {
      n += 1
      if elems[i].leq(negs[j]) != elems[j].leq(negs[i]) {
        ok = false
      }
    }
  }
  (n, ok)
}

///|
/// 把 S1 的德摩根正規形翻成 H3 表層語法的布林項（名字 0、1 ↦ 變數 x、y）。
pub fn dm_to_bool(d : @s1.Dm) -> String {
  let vars = ["x", "y", "z", "w"]
  if d.ms.length() == 0 {
    return "ff"
  }
  let mut acc = ""
  for m in d.ms {
    let mut term = ""
    for i in 0..<vars.length() {
      let lits : Array[String] = []
      if ((m >> i) & 1) == 1 {
        lits.push(vars[i])
      }
      if ((m >> (i + @s1.MAX_NAMES)) & 1) == 1 {
        lits.push("(not " + vars[i] + ")")
      }
      for l in lits {
        term = if term == "" { l } else { "(and " + term + " " + l + ")" }
      }
    }
    if term == "" {
      term = "tt"
    }
    acc = if acc == "" { term } else { "(or " + acc + " " + term + ")" }
  }
  acc
}

///|
/// 布林真值表（兩個名字，四個賦值各一位元）。𝟜 = 𝟚×𝟚 的對角賦值即布林賦值。
fn truth_table(d : @s1.Dm) -> Int32 {
  let mut t = 0
  for a in 0..<4 {
    let x = if (a & 1) == 1 { 3 } else { 0 }
    let y = if (a & 2) == 2 { 3 } else { 0 }
    if d.eval4(x | (y << 2)) == 3 {
      t = t | (1 << a)
    }
  }
  t
}

///|
pub(all) struct BooleanQuotient {
  /// |F(2)|
  de_morgan_elements : Int32
  /// 布林商的類數（應為 2^(2^2) = 16）
  boolean_classes : Int32
  /// 交 S8 證明的等式數與核心接受數
  proved : Int32
  kernel_accepted : Int32
  /// 交 S8 反駁的不等式數（不同類的代表之間）
  refuted : Int32
  /// 德摩根代數中不等、布林下卻可證相等的樣本數
  collapsed : Int32
}

///|
/// 橋接 S1 × S8 × H3：自由德摩根代數 F(2) 到自由布林代數的商。
/// 每個布林類取一個代表；類內其餘至多 `per_class` 個元素與代表的相等交由 S8
/// 的符號執行證明並經 H3 核心重檢；相鄰類的代表之間則應被反駁（給出反例賦值）。
pub fn boolean_quotient(
  per_class : Int32,
) -> BooleanQuotient raise @h3.KernelError {
  let elems = @s1.free_algebra(2, limit=400)
  // 每個布林類一個代表；slot：真值表 ↦ 類編號
  let slot : Map[Int32, Int32] = Map([])
  let reps : Array[@s1.Dm] = []
  let used : Array[Int32] = []
  let mut proved = 0
  let mut accepted = 0
  let mut collapsed = 0
  let mut refuted = 0
  let state = fn(l : @s1.Dm, r : @s1.Dm) -> String {
    @s8.prelude() +
    "(Pi (x Bool) (y Bool) (Id Bool " +
    dm_to_bool(l) +
    " " +
    dm_to_bool(r) +
    "))"
  }
  for d in elems {
    let t = truth_table(d)
    match slot.get(t) {
      None => {
        slot[t] = reps.length()
        reps.push(d)
        used.push(0)
      }
      Some(c) =>
        if used[c] < per_class {
          used[c] += 1
          let report = @s8.prove_source(state(d, reps[c]))
          if report.status == "proved" {
            proved += 1
            if !d.same(reps[c]) {
              collapsed += 1
            }
          }
          if report.kernel_accepted {
            accepted += 1
          }
        }
    }
  }
  for i in 1..<reps.length() {
    if @s8.prove_source(state(reps[i - 1], reps[i])).status == "refuted" {
      refuted += 1
    }
  }
  {
    de_morgan_elements: elems.length(),
    boolean_classes: reps.length(),
    proved,
    kernel_accepted: accepted,
    refuted,
    collapsed,
  }
}

///|
pub(all) struct EckmannHilton {
  /// π₀(E₁(2))、π₀(E₂(2)) 的離散模型分支數
  e1_components : Int32
  e2_components : Int32
  /// E₁ 作用於群的乘法：θ(c; a, b) 依小區間次序相乘
  e1_action_is_product : Bool
  /// 乘法在交換標號下不變（⇔ 群交換 ⇔ 可延拓為 E₂-代數的必要條件）
  commutative : Bool
  /// S4 的 H₁ 計算：阿貝爾化的階等於群的階 ⇔ 群交換
  abelianization_order : Int32
  group_order : Int32
}

///|
/// 橋接 S9 × S4（組合範例 9）：Eckmann–Hilton。
/// E₂(2) 連通，故 E₂-代數（於集合）的二元運算與其對換同倫——於離散集合即相等；
/// E₁(2) 有兩個分支，對應 ab 與 ba。對 S4 完備化得到的有限群檢驗：
/// 「乘法在標號對換下不變」⇔「阿貝爾化不縮小群」。
pub fn eckmann_hilton(pres : @s4.Presentation) -> EckmannHilton? {
  match group_table(pres, max_rules=200, limit=400) {
    None => None
    Some(table) => {
      let n = table.length()
      let c = @s9.random_cubes(1, 2, 7)
      let swapped = c.permute([1, 0])
      let mut is_product = true
      let mut commutative = true
      for a in 0..<n {
        for b in 0..<n {
          let w = @s9.act_on_loops(c, [[a], [b]])
          let v = @s9.act_on_loops(swapped, [[a], [b]])
          let pw = table[w[0]][w[1]]
          let pv = table[v[0]][v[1]]
          let expect = if c.order()[0] == 0 { table[a][b] } else { table[b][a] }
          if pw != expect {
            is_product = false
          }
          if pw != pv {
            commutative = false
          }
        }
      }
      let (rank, torsion) = pres.abelianization()
      let mut ab = if rank == 0 { 1 } else { 0 }
      for t in torsion {
        ab *= t
      }
      Some({
        e1_components: @s9.configuration_space(1, 4).b0,
        e2_components: @s9.configuration_space(2, 3).b0,
        e1_action_is_product: is_product,
        commutative,
        abelianization_order: ab,
        group_order: n,
      })
    }
  }
}

///|
/// 第 2 回合總審計：逐一執行 S1–S10 的定理檢驗，回傳（名稱, 觀測值, 是否成立）。
/// 由 H6 的可執行檔呼叫，使各模組的檢驗入口在倉庫內有實際的執行動線。
pub fn round_two_audit() -> Array[(String, String, Bool)] raise {
  let out : Array[(String, String, Bool)] = []
  // ── S1
  let f2 = @s1.free_algebra(2, limit=400)
  let (laws, laws_ok) = @s1.verify_de_morgan_laws(f2)
  out.push(
    (
      "S1 De Morgan laws on F(2)",
      "\{f2.length()} elements, \{laws} instances",
      f2.length() == 168 && laws_ok,
    ),
  )
  let mut kalman = true
  for a in f2 {
    for b in f2 {
      if @s1.semantically_equal4(a, b, 2).0 != a.same(b) {
        kalman = false
      }
    }
  }
  out.push(
    ("S1 Kalman completeness", "\{f2.length() * f2.length()} pairs", kalman),
  )
  let (faces, sieves, faces_ok) = @s1.verify_face_semantics(2, f2)
  out.push(
    (
      "S1 face lattice = sieve lattice",
      "\{faces} faces, \{sieves} sieves",
      faces_ok && faces == sieves,
    ),
  )
  let (cub, cub_ok) = @s1.verify_cubical_identities(3)
  out.push(("S1 cubical identities", "\{cub} identities", cub_ok))
  let cr = @s1.complement_report(f2)
  out.push(
    (
      "S1 local complementedness",
      "centre \{cr.center}, boolean intervals \{cr.boolean_intervals}/\{cr.intervals}",
      cr.center == 2 && cr.neg_fixed_points == 0,
    ),
  )
  let (gal, gal_ok) = verify_negation_galois(2)
  out.push(("S1 negation is a Galois connection", "\{gal} pairs", gal_ok))
  // ── S2
  out.push(("S2 path laws", "all laws", @s2.verify_path_laws().all()))
  // ── S3
  let (ctxs, ps, ps_ok) = @s3.verify_ps_characterization(5)
  out.push(
    (
      "S3 pasting schemes = linear triangle order",
      "\{ctxs} contexts, \{ps} pasting schemes",
      ps_ok,
    ),
  )
  let (rej, rej_total) = @s3.verify_rejections()
  out.push(("S3 rejections", "\{rej}/\{rej_total}", rej == rej_total))
  let lib = @s3.Library::build(groupoid=true)
  let (c1, v1, m1) = @s3.verify_group_model(lib, @s3.FinGroup::symmetric3())
  let s3 = s3_presentation()
  let via_rewriting = coherences_in_rewriting_group(s3)
  out.push(
    (
      "S3×S4 coherences hold in S3 (table and rewriting models agree)",
      "\{c1} coherences, \{v1} valuations",
      m1 && via_rewriting is Some((c2, v2, true)) && c1 == c2 && v1 == v2,
    ),
  )
  // ── S4
  for sample in [("RP2", @s4.rp2()), ("Moore(5)", @s4.moore_complex(5))] {
    let (name, x) = sample
    let r = @s4.analyze_complex(x, max_rules=200, limit=200)
    out.push(
      (
        "S4 universal cover of " + name,
        "|pi1| \{r.group_order}, rules \{r.rules}, cover V\{r.cover_vertices} E\{r.cover_edges} F\{r.cover_faces}",
        r.group_finite &&
        r.convergent &&
        r.locally_confluent &&
        r.simply_connected &&
        r.euler_multiplicative &&
        r.fibers_uniform &&
        r.monodromy_faithful,
      ),
    )
  }
  let (torus_pres, _) = @s4.torus().fundamental_group()
  let torus_rws = torus_pres.complete(max_rules=200)
  let (words, unique) = torus_rws.verify_unique_normal_forms(5)
  out.push(
    (
      "S4 torus group: unique normal forms",
      "\{words} words",
      torus_rws.convergent && unique,
    ),
  )
  // ── S5
  let (st, st_ok) = @s5.verify_nonabelian_stokes(3, 2, 4, 40, 1)
  out.push(("S5 non-abelian Stokes", "\{st} connections", st_ok))
  let (hol, curv, as_ok) = @s5.verify_ambrose_singer(3, 3, 4, 7)
  out.push(("S5 Ambrose–Singer", "\{hol} = \{curv}", as_ok))
  let (gf, gf_ok) = @s5.verify_gauge_covariance(@s4.torus(), 3, 30, 3)
  out.push(("S5 gauge covariance", "\{gf} faces", gf_ok))
  let (flat, homs, flat_ok) = @s5.verify_flat_count(@s4.rp2(), 3)
  out.push(
    ("S5 flat connections on RP2", "\{flat} flat, \{homs} homs", flat_ok),
  )
  match @s5.representable_connection(@s4.rp2(), max_rules=200, limit=200) {
    Some(conn) => {
      let (loops, mono_ok) = @s5.verify_monodromy_representation(
        @s4.rp2(),
        conn,
        6,
        max_rules=200,
      )
      out.push(("S5 monodromy representation", "\{loops} loop pairs", mono_ok))
    }
    None => out.push(("S5 monodromy representation", "no connection", false))
  }
  match @s5.groupoid_model(@s4.rp2(), max_rules=200, limit=200) {
    Some(g) =>
      out.push(
        (
          "S5 groupoid model of RP2",
          "loop space \{g.loop_space}",
          g.uip_fails &&
          g.based_paths_flat &&
          g.based_paths_connected &&
          g.based_paths_simply_connected &&
          g.euler_multiplicative &&
          g.transport_functorial,
        ),
      )
    None => out.push(("S5 groupoid model of RP2", "not built", false))
  }
  // ── S6
  let torus = @s6.torus_dgla(@s6.sl2())
  let ax = torus.verify_axioms()
  let rep = torus.deformation_report(20)
  out.push(
    (
      "S6 sl2 torus DGLA",
      "\{ax.checks} checks, h = \{rep.h0} \{rep.h1} \{rep.h2}, Kuranishi \{rep.kuranishi_nonzero}/\{rep.kuranishi_trials}",
      ax.all() && rep.h0 == 3 && rep.h1 == 6 && rep.h2 == 3,
    ),
  )
  let tower = torus.moduli_tower(torus.random_element(1, 5), 4)
  let abelian_torus = @s6.torus_dgla(@s6.abelian(2))
  let free_tower = abelian_torus.moduli_tower(
    abelian_torus.random_element(1, 5),
    4,
  )
  out.push(
    (
      "S6 moduli tower",
      "sl2 obstructed at \{tower.obstructed_at}; abelian obstructed at \{free_tower.obstructed_at} with \{free_tower.levels.length()} levels",
      tower.truncations_mc &&
      free_tower.truncations_mc &&
      free_tower.obstructed_at == 0,
    ),
  )
  for pt in [([0, 0, 0], [0, 0, 0]), ([1, 0, 0], [2, 0, 0])] {
    let (a, b) = pt
    let ((z1, h2), (t1, t2), tan_ok) = @s6.verify_tangent_fiber_product(
      @s6.sl2(),
      a,
      b,
    )
    out.push(
      (
        "S6 tangent complex = derived fibre product",
        "\{z1} \{h2} vs \{t1} \{t2}",
        tan_ok,
      ),
    )
  }
  // 點 ×ʰ_C 點（兩個映射皆為零）：衍生纖維積多出迴路類
  let line : @s6.Cochain = {
    dims: [1, 0, 0],
    d: [@s6.Matrix::zero(0, 1), @s6.Matrix::zero(0, 0)],
  }
  let zero_map = [
    @s6.Matrix::zero(1, 1),
    @s6.Matrix::zero(0, 0),
    @s6.Matrix::zero(0, 0),
  ]
  let (got, predicted, mv_ok) = @s6.verify_mayer_vietoris(
    line, line, line, zero_map, zero_map,
  )
  let strict = @s6.strict_fiber_product_betti(
    line, line, line, zero_map, zero_map,
  )
  out.push(
    (
      "S6 Mayer–Vietoris for the derived fibre product",
      "derived \{got[0]} \{got[1]} \{got[2]}, predicted \{predicted[0]} \{predicted[1]} \{predicted[2]}, strict \{strict[0]} \{strict[1]} \{strict[2]}",
      mv_ok && got[1] == 1 && strict[1] == 0,
    ),
  )
  // ── S7
  let lnl = @s7.lnl_modes()
  for
    sample in [
      ("LNL", lnl, @s7.lnl_claims()),
      ("substructural", @s7.substructural_modes(), @s7.substructural_claims()),
      ("S4", @s7.s4_modes(), @s7.s4_claims()),
    ] {
    let (name, modes, claims) = sample
    let (good, total) = @s7.verify_claims(modes, claims)
    out.push(
      (
        "S7 claims in " + name,
        "\{good}/\{total}",
        modes.is_monotone() && good == total,
      ),
    )
  }
  let (adj, adj_a, adj_b) = @s7.verify_adjunction()
  out.push(("S7 down ⊣ up", "\{adj} instances", adj_a && adj_b))
  let (steps, preserved, terminated, _) = @s7.verify_subject_reduction(
    lnl,
    @s7.lnl_cut_examples(),
  )
  out.push(("S7 subject reduction", "\{steps} steps", preserved && terminated))
  // ── S8
  let (hit, total, kernel_ok) = @s8.verify_corpus()
  out.push(
    (
      "S8 symbolic execution corpus",
      "\{hit}/\{total}",
      hit == total && kernel_ok,
    ),
  )
  // ── S9
  for d in 1..<4 {
    let r = @s9.verify_operad_axioms(d, 12)
    out.push(
      (
        "S9 operad axioms, dimension \{d}",
        "\{r.instances} compositions",
        r.all(),
      ),
    )
  }
  let (acts, act_ok) = @s9.verify_loop_action(12)
  out.push(("S9 E1 action on loops", "\{acts} instances", act_ok))
  for cfg in [(1, 4, 2, 0), (2, 3, 1, 1), (3, 3, 1, 0)] {
    let (d, grid, b0, b1) = cfg
    let r = @s9.configuration_space(d, grid)
    out.push(
      (
        "S9 E\{d}(2) has the Betti numbers of S^\{d - 1}",
        "b0 \{r.b0}, b1 \{r.b1}",
        r.b0 == b0 && r.b1 == b1,
      ),
    )
  }
  let (over, under) = @s9.swap_windings()
  out.push(
    (
      "S9 the two swaps differ by a full turn",
      "\{over} and \{under} quarter turns",
      over - under == 4,
    ),
  )
  // ── S10
  match group_table(s3, max_rules=200, limit=200) {
    None => out.push(("S10 S3 multiplication table", "not built", false))
    Some(table) => {
      // 階 2 與階 3 的元素
      let mut o2 = 0
      let mut o3 = 0
      for g in 1..<table.length() {
        if table[g][g] == 0 {
          o2 = g
        } else if table[table[g][g]][g] == 0 {
          o3 = g
        }
      }
      for cfg in [([o2], [], [o3]), ([o3], [], [o2]), ([o2], [o2], [])] {
        let (h, k, l) = cfg
        let r = verify_kan(table, h, k, l)
        out.push(
          (
            "S10 Lan ⊣ Res ⊣ Ran along a subgroup of order \{r.subgroup_order}",
            "|Lan| \{r.lan_size}, |Ran| \{r.ran_size}, homs \{r.left_hom.0}=\{r.left_hom.1}, \{r.right_hom.0}=\{r.right_hom.1}",
            r.holds(),
          ),
        )
      }
      for alg in [("k[S3]", group_algebra(table)), ("T2", upper_triangular())] {
        let (name, a) = alg
        let (za, zm, ha, hm, assoc, same) = verify_morita(a, 2)
        out.push(
          (
            "S10 Morita invariance for " + name,
            "Z \{za}/\{zm}, HH0 \{ha}/\{hm}",
            a.is_associative() && assoc && same,
          ),
        )
      }
    }
  }
  for cfg in [(2, 2, 3, 1, -1, 3), (2, 2, 3, 2, 0, 1), (2, 2, 4, 5, 7, 2)] {
    let (m, n, fiber, seed, twist, expected) = cfg
    let g = gluing_sample(m, n, fiber, seed, twist)
    out.push(
      (
        "S10 flat sections glue",
        "U \{g.sections_u}, V \{g.sections_v}, global \{g.sections_union}, compatible \{g.compatible_pairs}",
        g.is_sheaf() && g.sections_union == expected,
      ),
    )
  }
  let q = boolean_quotient(2)
  out.push(
    (
      "S10 Boolean quotient of F(2)",
      "\{q.boolean_classes} classes, \{q.proved} proved, \{q.refuted} refuted",
      q.boolean_classes == 16 &&
      q.proved == q.kernel_accepted &&
      q.proved == q.collapsed &&
      q.refuted == q.boolean_classes - 1,
    ),
  )
  for sample in [("S3", s3, false), ("Z/6", cyclic_presentation(6), true)] {
    let (name, pres, abelian) = sample
    match eckmann_hilton(pres) {
      None => out.push(("S10 Eckmann–Hilton for " + name, "not built", false))
      Some(e) =>
        out.push(
          (
            "S10 Eckmann–Hilton for " + name,
            "pi0 E1(2) = \{e.e1_components}, pi0 E2(2) = \{e.e2_components}, commutative \{e.commutative}, |G^ab| \{e.abelianization_order} of \{e.group_order}",
            e.e1_action_is_product &&
            e.e1_components == 2 &&
            e.e2_components == 1 &&
            e.commutative == abelian &&
            e.commutative == (e.abelianization_order == e.group_order),
          ),
        )
    }
  }
  out
}
