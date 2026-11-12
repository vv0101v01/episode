///|
/// Module H6 — 十個概念的總成管線：
/// 原始碼 →（雙向精化）→ 核心項 →（類型檢查）→ 推導樹 →（NbE）→ η-長正規形
///        →（嵌入競技場）→ 強正規化證書／策略比較／主詞約簡／局部化
///        →（抽取）→ 惰性抽象機執行結果。
pub(all) struct PipelineReport {
  /// 精化後核心項的大小與其類型
  term_size : Int32
  /// 核心層定義數，與 ζ-展開（定義代入各使用處）後的項大小
  definitions : Int32
  expanded_size : Int32
  ty : String
  /// 推導樹：規則總數與（形成, 引入, 消除, 結構）分佈
  derivation_size : Int32
  formation : Int32
  introduction : Int32
  elimination : Int32
  structural : Int32
  /// NbE 正規形及其是否符合正規形文法
  normal_form : String
  normal_form_valid : Bool
  /// 核心遙測
  beta_steps : Int32
  iota_steps : Int32
  eta_expansions : Int32
  thunks_created : Int32
  thunks_forced : Int32
  /// 抽取程式：大小、機器讀回值、機器步數／配置數／更新數
  code_size : Int32
  machine_value : String
  machine_steps : Int32
  machine_allocs : Int32
  machine_updates : Int32
  /// 當結果為自然數時，機器值與 NbE 正規形一致
  machine_agrees : Bool
  /// 重寫側與語義側的橋接不變量
  bridge : @h4.BridgeReport
  /// 正規形的樹大小與 DAG 大小（共享後記憶體）
  nf_tree_size : Int32
  nf_dag_size : Int32
}

///|
/// 執行完整管線。`budget` 為約簡圖節點上限；`fuel` 為抽象機步數上限。
pub fn run_pipeline(
  src : String,
  budget~ : Int32,
  fuel~ : Int32,
) -> PipelineReport raise @h3.KernelError {
  let k = @h3.Kernel::new()
  let e = k.elaborate(src)
  let (f, i, el, st) = e.deriv.class_counts()
  let code = @h3.extract(e.deriv)
  let m = @h3.Machine::new(fuel~)
  let value = m.readback(m.run(code))
  // 先單獨正規化並擷取核心遙測，使計數只反映本項的一次 NbE
  let (nf, _) = k.normalize(@h3.Ctx::empty(), e.term)
  let beta_steps = k.beta
  let iota_steps = k.iota
  let eta_expansions = k.eta
  let thunks_created = k.thunks
  let thunks_forced = k.forced
  let arena = @h2.Arena::new()
  // 約簡圖分析作用於 ζ-展開後的項：核心層定義只在類型檢查與抽取機中保持共享
  let bridge = @h4.analyze(
    @h3.Kernel::new(),
    arena,
    @h3.zeta_expand(e.term),
    budget~,
  )
  let agrees = match @h3.as_numeral(nf) {
    Some(n) => value == "\{n}"
    None =>
      match nf {
        Tt => value == "tt"
        Ff => value == "ff"
        Star => value == "star"
        _ => true
      }
  }
  let nf_id = @h4.embed(arena, nf)
  {
    term_size: @h3.tm_size(e.term),
    definitions: @h3.let_count(e.term),
    expanded_size: @h3.tm_size(@h3.zeta_expand(e.term)),
    ty: @h3.show_tm(e.ty),
    derivation_size: e.deriv.size(),
    formation: f,
    introduction: i,
    elimination: el,
    structural: st,
    normal_form: @h3.show_tm(nf),
    normal_form_valid: @h3.is_normal(nf),
    beta_steps,
    iota_steps,
    eta_expansions,
    thunks_created,
    thunks_forced,
    code_size: @h3.code_size(code),
    machine_value: value,
    machine_steps: m.steps,
    machine_allocs: m.allocs,
    machine_updates: m.updates,
    machine_agrees: agrees,
    bridge,
    nf_tree_size: arena.tree_size(nf_id),
    nf_dag_size: arena.dag_size(nf_id),
  }
}

///|
/// 管線報告的全部不變量是否同時成立（強正規化、唯一正規形、F∞ = 最長、
/// 主詞約簡、局部化、NbE 與重寫定義性一致、機器與 NbE 一致）。
pub fn PipelineReport::certified(self : PipelineReport) -> Bool {
  let b = self.bridge
  self.normal_form_valid &&
  self.machine_agrees &&
  b.verdict == StronglyNormalizing &&
  b.unique_normal_form &&
  b.perpetual_is_longest &&
  (match b.measure_bound {
    Some(bound) => bound >= b.longest
    None => true
  }) &&
  b.subject_reduction &&
  b.reductions_inverted &&
  b.definitional_agreement
}

///|
pub fn PipelineReport::render(self : PipelineReport) -> String {
  let b = self.bridge
  let verdict = match b.verdict {
    StronglyNormalizing => "strongly normalizing"
    Cyclic => "cyclic"
    BudgetExceeded => "budget exceeded"
  }
  let sb = StringBuilder()
  sb.write_string("type            : \{self.ty}\n")
  sb.write_string("normal form     : \{self.normal_form}\n")
  sb.write_string(
    "term            : size \{self.term_size} with \{self.definitions} core definitions (\{self.expanded_size} after zeta-expansion)\n",
  )
  sb.write_string(
    "derivation      : \{self.derivation_size} rules (F \{self.formation}, I \{self.introduction}, E \{self.elimination}, S \{self.structural})\n",
  )
  sb.write_string(
    "nbe             : beta \{self.beta_steps}, iota \{self.iota_steps}, eta \{self.eta_expansions}, thunks \{self.thunks_forced}/\{self.thunks_created} forced\n",
  )
  sb.write_string(
    "machine         : \{self.machine_value} in \{self.machine_steps} steps (\{self.machine_allocs} allocs, \{self.machine_updates} updates, code \{self.code_size})\n",
  )
  sb.write_string(
    "reduction graph : \{verdict}; \{b.graph_nodes} terms, \{b.graph_edges} steps; shortest \{b.shortest}, longest \{b.longest}\n",
  )
  match b.measure_bound {
    Some(bound) =>
      sb.write_string(
        "type measure    : longest reduction <= \{bound} without enumeration (exhaustive longest \{b.longest})\n",
      )
    None => ()
  }
  sb.write_string(
    "strategies      : leftmost \{b.leftmost_steps}, perpetual \{b.perpetual_steps}, Gross-Knuth \{b.gross_knuth_rounds} rounds\n",
  )
  sb.write_string(
    "invariants      : unique-nf \{b.unique_normal_form}, F∞=longest \{b.perpetual_is_longest}, subject-reduction \{b.subject_reduction} (\{b.reducts_checked} terms), localized \{b.reductions_inverted}, nbe≡rewrite \{b.definitional_agreement}, machine≡nbe \{self.machine_agrees}\n",
  )
  sb.write_string(
    "memory          : normal form tree \{self.nf_tree_size} / dag \{self.nf_dag_size}\n",
  )
  sb.to_string()
}

///|
/// 系統層審計：規則綱要（H1）與核心行為（H3）之間的伽羅瓦／Chu 對偶。
pub(all) struct SystemAudit {
  formers : Array[@h5.FormerReport]
  chu : @h5.ChuReport
  /// 邏輯連接詞全域上的伽羅瓦定律（受檢配對數, 成立）與形式概念數
  logic_galois_pairs : Int32
  logic_galois_holds : Bool
  logic_concepts : Int32
  /// 不調和反例確被偵測：tonk 局部不健全、weak-∧ 局部不完備
  tonk_rejected : Bool
  weak_and_rejected : Bool
  /// 由引入規則合成的一般消除規則對每個連接詞皆調和
  general_elims_harmonious : Bool
}

///|
pub fn system_audit() -> SystemAudit {
  let k = @h3.Kernel::new()
  let logic = @h1.logical_connectives()
  let u = @h1.universe_of(logic)
  let (pairs, holds) = u.verify_galois_law()
  let mut tonk = false
  let mut weak = false
  let mut ge = true
  for c in [..logic, ..@h1.type_formers()] {
    let h = c.harmony()
    if c.name == "tonk" && !h.sound {
      tonk = true
    }
    if c.name == "weak-∧" && h.sound && !h.complete {
      weak = true
    }
    let g = c.with_general_elim().harmony()
    if !(g.sound && g.complete) {
      ge = false
    }
  }
  {
    formers: @h5.verify_all(k),
    chu: @h5.verify_chu_duality(k),
    logic_galois_pairs: pairs,
    logic_galois_holds: holds,
    logic_concepts: u.concepts().length(),
    tonk_rejected: tonk,
    weak_and_rejected: weak,
    general_elims_harmonious: ge,
  }
}

///|
pub fn SystemAudit::certified(self : SystemAudit) -> Bool {
  let mut ok = true
  for f in self.formers {
    if !f.consistent {
      ok = false
    }
  }
  ok &&
  self.chu.matrices_agree &&
  self.chu.formers_are_concepts &&
  self.chu.galois_holds &&
  self.logic_galois_holds &&
  self.tonk_rejected &&
  self.weak_and_rejected &&
  self.general_elims_harmonious
}

///|
pub fn SystemAudit::render(self : SystemAudit) -> String {
  let sb = StringBuilder()
  for f in self.formers {
    let p = match f.polarity {
      Negative => "negative"
      Positive => "positive"
      NoUniqueness => "none"
    }
    sb.write_string(
      "\{f.former}: \{p}; computation rules \{f.verified_rules}/\{f.predicted_rules}; eta definitional \{f.definitional_eta}, propositional \{f.propositional_eta}; consistent \{f.consistent}\n",
    )
  }
  let c = self.chu
  sb.write_string(
    "chu: \{c.intros} intros x \{c.elims} elims; operational = schematic \{c.matrices_agree}; \{c.fired_cells} cells fire; \{c.concepts} concepts; formers closed \{c.formers_are_concepts}; galois \{c.galois_holds} over \{c.galois_pairs} pairs\n",
  )
  sb.write_string(
    "logic: galois \{self.logic_galois_holds} over \{self.logic_galois_pairs} pairs; \{self.logic_concepts} concepts; tonk rejected \{self.tonk_rejected}; weak-and rejected \{self.weak_and_rejected}; synthesized GE rules harmonious \{self.general_elims_harmonious}\n",
  )
  sb.to_string()
}

///|
/// 內建語料：每項為（標題, 原始碼）。涵蓋證明即程式、歸納證明、η 規則與大消除。
pub fn corpus() -> Array[(String, String)] {
  let prelude =
    #|(def plus (-> Nat Nat Nat) (lam m n (rec (x Nat) n (k ih (S ih)) m)))
    #|(def cong (Pi (a Nat) (b Nat) (p (Id Nat a b)) (Id Nat (S a) (S b)))
    #|  (lam a b p (J (x y q (Id Nat (S x) (S y))) (w (refl (S w))) p)))
    #|(def plus-zero (Pi (n Nat) (Id Nat (plus n 0) n))
    #|  (lam n (rec (x (Id Nat (plus x 0) x)) refl (k ih (cong (plus k 0) k ih)) n)))
    #|
  [
    ("polymorphic identity", "((lam (A U0) (x A) x) Nat 3)"),
    ("addition by recursion", prelude + "(plus 2 1)"),
    ("inductive proof n + 0 = n, instantiated", prelude + "(plus-zero 1)"),
    (
      "witness extraction from an existence proof",
      prelude +
      "(def double (Pi (n Nat) (Sigma (m Nat) (Id Nat m (plus n n)))) (lam n (pair (plus n n) refl))) (fst (double 2))",
    ),
    (
      "symmetry of identity by J", "((lam (A U0) (a A) (b A) (p (Id A a b)) (J (x y q (Id A y x)) (w refl) p)) Nat 2 2 refl)",
    ),
    (
      "large elimination", "(the (if-as (x U1) ((lam (b Bool) b) tt) Nat Bool) ((lam (n Nat) (S n)) 2))",
    ),
    ("unit eta", "(lam (u Unit) u)"),
    (
      "simply-typed iteration (type-measure bound)", "((lam (f (-> Nat Nat)) (x Nat) (f (f x))) (lam (n Nat) (S n)) 0)",
    ),
    (
      "simply-typed Church exponent (type-measure bound)", "((lam (g (-> (-> Nat Nat) Nat Nat)) (f (-> Nat Nat)) (g (g f))) (lam (f (-> Nat Nat)) (x Nat) (f (f x))) (lam (n Nat) (S n)) 0)",
    ),
    (
      "erasing redex (type-measure bound)", "((lam (x Nat) (y Nat) x) 1 ((lam (f (-> Nat Nat)) (f (f 0))) (lam (n Nat) (S n))))",
    ),
    (
      "shared core definitions",
      prelude +
      "(def two Nat (plus 1 1)) (def four Nat (plus two two)) (fst (the (Sigma (m Nat) (Id Nat m four)) (pair four refl)))",
    ),
    (
      "erased argument under call-by-need",
      prelude + "((lam (x Nat) (y Nat) x) 1 (plus 1 1))",
    ),
  ]
}
