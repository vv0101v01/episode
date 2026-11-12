# 依賴類型論 03 — 流水帳本（README）

> 每回合更新。記錄：開發指示、已完成／未完成事項、聯網搜查結果、已決定但待辦事項。
> 統計表見 `Dev.xlsx`；工程約束見 `AGENT.md`。

## 1. 開發指示（第 1 回合，2026-11-12，首次開發）

- 主題：**證明即程式、引入規則、消除規則、計算規則、唯一性規則、β約簡、η轉換、正規化、強正規化、類型檢查**。
- 下載最新穩定版 MoonBit、聯網搜查最新語法與前沿論文後實作。
- 01、02 已完工於 <https://github.com/vv0101v01/dependent>（本倉庫為 03 的獨立倉庫，尚未與之合併）。
- 全域公理：伽羅瓦對應；局部公理：邏輯消元。

## 2. 工具鏈與語法搜查結果

| 項目 | 結果 |
| :-- | :-- |
| 工具鏈 | `moon 0.1.20261104`、`moonc v0.10.20+65efd5b93`（官方安裝腳本取得的最新穩定版） |
| 派生 | `#derive(Eq, Hash)` 屬性置於類型定義之上；舊的尾置 `derive(...)` 已棄用 |
| 方法提升 | 派生的 trait 方法需以 `pub extend T with Eq::{equal, not_equal}` 顯式提升 |
| 整數 | `Int`／`UInt` 更名為 `Int32`／`UInt32`（舊名為別名，`moon fmt` 自動遷移） |
| 建構 | `Map([])`、`StringBuilder()`、`Ref(x)` 取代 `::new()` |
| 迴圈 | 函數式 `loop` 已棄用；`for { }` 無限迴圈已棄用，改用 `while`／`for ;;` |
| 保留字 | `var`、`define` 不可作識別字 |
| 組態 | `moon.mod`／`moon.pkg`（非 JSON）；本地多模組以 `moon.work` 管理；可執行套件用 `pkgtype(kind: "executable")` |
| 錯誤 | `suberror`、`raise`、`try … catch { } noraise { }`；`try?` 已棄用 |
| 介面 | `moon check` 自動產生 `pkg.generated.mbti` |

來源：MoonBit 官方更新頁（v0.10.0、v0.10.9、v0.10.19 發行說明）與模組組態文件。

## 3. 前沿論文搜查結果與採用方式

| 論文 | 採用於 |
| :-- | :-- |
| Lennon-Bertrand,《What does it take to certify a conversion checker?》arXiv:2502.15500 | H3：無類型（項導向）轉換為快速路徑、類型導向 η-長比較為完備後備；Unit-η 為兩者的分界（T16） |
| Courant & Leroy,《A Lazy, Concurrent Convertibility Checker》arXiv:2510.18418 | H3：全面 call-by-need 懸置；懸置物理相等即判同而不求值；H4：駐留後類別比較 |
| 《Towards a Performance Comparison of Syntax and Type-Directed NbE》arXiv:2509.13489 | H3：以語法導向檢查為主、僅在失敗時付出類型導向成本 |
| Biernacka 等,《A Simple and Efficient Implementation of Strong Call by Need by an Abstract Machine》arXiv:2603.21949 | H3：記憶化懸置的強正規化求值器；抽取程式於帶更新標記的惰性 Krivine 機執行 |
| Accattoli 等,《Positive Sharing and Abstract Machines》arXiv:2506.14131 | H2：子項性質——駐留 DAG、代換與位移記憶化 |
| 《A Modular Lean 4 Framework for Confluence and Strong Normalization》arXiv:2512.09280 | H2：Takahashi 完全展開、Z 性質作為合流證明骨架 |
| Khasidashvili,《On the longest perpetual reductions in orthogonal expression reduction systems》(TCS 2001) | H2：推廣的 F∞ 永續策略給出最長約簡（T9） |
| Francez & Dyckhoff,《A Note on Harmony》；Pfenning–Davies 局部健全／完備；Walsh,《Categorical Harmony and Path Induction》(2025) | H1：由引入規則合成一般消除規則；調和性 = 伴隨／伽羅瓦極 |

## 4. 架構（六個模組，`moon.work` 工作區）

```text
h1_rule_harmony      [獨立] 引入／消除／計算／唯一性規則 ─────────┐
h2_beta_eta_sn       [獨立] β約簡、η轉換、強正規化 ──────┐       │
h3_nbe_typecheck     [獨立] 正規化、類型檢查、證明即程式 ─┼──┐    │
h4_reduction_localization  [橋接 H2×H3] 局部化、主詞約簡 ◄┘  │    │
h5_rule_kernel_chu         [橋接 H1×H3] Chu／伽羅瓦對偶 ◄────┴────┘
h6_unified_pipeline        [總成 H1..H5] 管線 + 系統審計 + cmd/main
```

採用的組合範例：#12 局部化（H4）、#10 楚空間（H5）、#3 纖維積／合流方塊（H4）、#14 管線合成（H6）。

### 4.1 各模組內容

- **H1**：規則以 64-bit 原子位元集表示；Horn 閉包實作反演原理；局部健全（計算規則存在）、局部完備（唯一性規則存在）、極性分類；由引入規則合成一般消除規則；規則全域上的左右極、形式概念列舉、穩定性；反例 tonk 與 weak-∧。
- **H2**：駐留 DAG 競技場（結構相等 = 編號相等）；每節點快取自由變數遮罩、β／η 可約式旗標、樹大小；記憶化位移與代換；8 條計算規則與 2 條 η 收縮；最左（主前提優先）、F∞ 永續、Gross–Knuth 三種策略；完全展開、Church–Rosser 合流見證、Z 性質檢驗；約簡圖窮舉的強正規化證書（最長／最短長度、環見證、正規形集合）。
- **H3**：Church 式全標註核心（Π、Σ、Unit、Empty、Bool、Nat、Id、累積宇宙）；call-by-need NbE 與類型導向 η-長回讀；無類型與類型導向兩種轉換；產生推導樹的核心檢查器；S-表達式表層語言與雙向精化（之後由核心獨立重檢）；類型抹除抽取與惰性抽象機。
- **H4**：核心項與競技場的雙向無損轉換；`Localizer`（定義性相等類別 = 駐留編號）；對約簡圖每個節點驗證主詞約簡與類別不變；NbE 與重寫的一致性；合流方塊。
- **H5**：每個類型形成子的計算規則實例與唯一性規則的兩種證明；「負極性 ⇔ 核心接受定義性 η」；操作矩陣（核心求值是否觸發）與綱要矩陣逐格相等。
- **H6**：`run_pipeline`、`system_audit`、內建語料與可執行入口。

### 4.2 動線與接口

- 全局檢驗：`moon fmt --check` → `moon check --deny-warn` → `moon build`（不使用 `--release`）。
- 執行：於 `modules/h6_unified_pipeline` 下 `moon run cmd/main`。
- 一體化入口：`@h6.run_pipeline(src, budget~, fuel~)`、`@h6.system_audit()`。
- 表層語法：`(Pi (x A) B)`、`(-> A B)`、`(lam (x A) b)`／`(lam x b)`、`(Sigma (x A) B)`、`(* A B)`、`(pair a b)`、`(fst p)`、`(snd p)`、`(if s t e)`、`(if-as (x C) s t e)`、`(rec (x C) z (m ih s) n)`、`(Id A a b)`、`refl`、`(refl a)`、`(J (x y q C) (w d) p)`、`(the T e)`、`(let (x T e) body)`、頂層 `(def x T e)`。

## 5. 本回合已完成

- [x] 安裝工具鏈、搜查語法與論文（§2、§3）。
- [x] H1–H6 全部實作，共約 5,300 行 MoonBit。
- [x] 局部編譯測試 + inspect：每個模組寫測試題、驗證、刪除（倉庫內不留測試檔）。
- [x] 全局：`moon fmt --check`、`moon check --deny-warn`、`moon build` 通過。
- [x] `cmd/main` 實跑：系統審計與 8 個語料項全部 `certified: true`。
- [x] CI 工作流 `.github/workflows/ci.yml`（全局格式、零警告檢查、建置）。
- [x] 本地 `git commit`。

### 5.1 inspect 驗證紀錄（測試題已刪除）

| 模組 | 觀測 |
| :-- | :-- |
| H1 | 7 個類型形成子與 →、∧、∨、⊤、⊥ 全部調和；極性 Π／Σ／Unit 為負，Empty／Bool／Nat／Id 為正；tonk 局部不健全；weak-∧ 局部不完備且不穩定；合成的 GE 規則 14／14 調和；伽羅瓦定律於 16,384 個子集配對成立；7 個形式概念 |
| H2 | Ω 判為含環；`(λx.*) Ω` 最左 1 步正規化而 F∞ 不終止；Church `2 2`：12 項 16 邊、最短 5、最長 6；F∞ 步數於全部樣本等於最長長度；Nederpelt 項 `λx:Nat.(λy:Bool.y) x` 在 βη 下有兩個正規形；Z 性質成立 |
| H3 | `plus-zero 3` 正規化為 `refl 3`；Π／Σ／Unit 的 η 以 `refl` 通過（Unit 需類型導向路徑）；Bool 的 η 以 `refl` 被拒、以 `if-as` 證得；`(λx.7)(plus 200 200)` 於惰性機僅 33 步（參數從未求值）；抽取程式 `fst (double 21)` 於機器得 42 |
| H4 | 18 個良類型樣本全部：強正規化、唯一正規形、F∞ = 最長、主詞約簡（最多 557 個節點）、類別不變、合流方塊成立；`λu:Unit.u` 為唯一語法不一致但定義性一致的樣本 |
| H5 | 7 個形成子全部一致；8×7 操作矩陣 = 綱要矩陣，8 格觸發；伽羅瓦定律於 32,768 個配對成立 |

## 6. 未完成／待辦（第 1 回合結束時；現況見 §9.4）

- [ ] **推送遠端與 CI 實跑**：本環境未連接 GitHub，亦未指定 03 的遠端倉庫；已完成本地 commit 與 CI 工作流檔，待提供遠端後 `git push`。
- [ ] 與 01／02（`vv0101v01/dependent`，M1–M14）合併：H3 核心與 `m3_pi_sigma_types`、H1 與 `m4_curry_howard_prop`、H2 與 `m1_syntax_context` 的橋接。
- [ ] 尚未使用的組合範例：#1 柯蘭擴展、#2 層黏合、#4 單子分配律、#5 張量—直和、#6 纖維範疇、#7 推出、#8 半直積、#9 操作子（遺傳代換）、#11 莫里塔等價、#13 短正合序列。
- [ ] 強正規化證書目前為逐項窮舉；可加入以類型為度量的界（Gandy／de Vrijer）以免窮舉。
- [ ] 表層 `let` 以代換展開；可改為核心層定義（δ／ζ 約簡）以免項膨脹。

## 7. 已決定事項

- 核心採 Church 式全標註，使每個項可合成主類型，主詞約簡得以對約簡圖逐節點檢驗。
- 子項走訪次序採「主前提優先」，使所有計算規則左式為 left-normal。
- 轉換檢查採「無類型快速路徑 + 類型導向後備」。
- 倉庫不保留測試檔；CI 僅作全局編譯檢驗。

## 8. 開發指示（第 2 回合，2026-11-12）

> 聯網搜最前沿論文，實做附件數學結構或模型，與組合結構和上回合，數學結構衍生出定理及導出演算法

附件 `工作內容依賴類型論S.md` 列出：德摩根立方體代數、形變函子與模塔、衍生纖維積、聯絡與曲率及水平分佈、弱歐米茄群胚、路徑類型、局部可補性、泛覆疊空間、高維群胚模型、可判定性與合流性、伴隨邏輯、符號動態執行與 NbE 整合、小立方體算子。

## 9. 第 2 回合

### 9.1 論文搜查結果與採用方式

| 來源 | 採用 |
| :-- | :-- |
| Sterling–Angiuli, *Normalization for Cubical Type Theory*（arXiv 2101.11479） | S2 以 NbE 判定立方體判斷相等；區間為 S1 的正規形 |
| Cohen–Coquand–Huber–Mörtberg（CCHM） | S1：區間 = 自由德摩根代數，面格為約束格 |
| Benjamin–Finster–Mimram, *Globular weak ω-categories as models of a type theory*（arXiv 2106.04475） | S3：CaTT 規則；Thm 40（黏貼方案 ⇔ ⊳ 全序）作窮舉比對 |
| Jang–Roshal–Pfenning–Pientka, *Adjoint Natural Deduction*（arXiv 2402.01428）；Pruiksma et al. 2018 | S7：模式前序、↓ ⊣ ↑、LNL 與 S4 的嵌入 |
| Mimram–Oleon, *Classifying covering types in HoTT*（arXiv 2512.10064） | S4：泛覆疊 = 平凡子群對應的覆疊；S5：單值表示 |
| Cherubini–Hutzler–Moeneclaey–Wärn, *Differential Geometry of Synthetic Schemes*（2025） | S5 的聯絡／曲率／水平分佈三種等價表述（此處為離散組合模型） |
| Ginot–Yalin（arXiv 1910.07255）；Brantner–Mathew（arXiv 1904.07352）；Lurie–Pridham | S6：形變函子 = DGLA 的 Maurer–Cartan 函子；模塔與阻礙類；切複形為衍生纖維積 |

上列論文只讀到搜尋摘要層級，未逐篇讀全文。

### 9.2 架構（新增十個模組）

```
S1 德摩根立方體 ──► S2 路徑類型
S3 弱 ω-群胚
S4 重寫／覆疊 ──► S5 聯絡／曲率
S6 形變／衍生
S7 伴隨邏輯
H3 ──► S8 符號執行 × NbE
S9 小立方體算子
S1 S3 S4 S5 S6 S8 S9 H3 ──► S10 橋接
```

各模組接口見其 `README.md`。組合範例的使用：#1 Kan 擴展（S10 `kan.mbt`）、#2 層黏合（S10 `sheaf.mbt`）、#3 極限／纖維積（S6 衍生纖維積）、#6 Grothendieck 構造（S5 `total_space`）、#7 推出（S4 `amalgam`）、#8 半直積（S4 `semidirect`）、#9 Operad（S9、S10 `eckmann_hilton`）、#11 Morita（S10 `morita.mbt`）、#13 短正合序列（S6 Mayer–Vietoris）。

### 9.3 inspect 驗證紀錄（測試題已刪除）

以下「成立」皆指所列樣本或窮舉範圍內的程式檢驗結果。

| 模組 | 觀測 |
| :-- | :-- |
| S1 | \|F(1)\| = 6、\|F(2)\| = 168；德摩根律 84,840 個實例成立；Kalman 完備性 28,224 對一致；F(2) 的布林中心 2 元、區間 7,581 個其中布林 1,421 個、最大布林區間 64 元、¬ 無不動點、Kleene 條件反例 2,592；面格 ≅ 篩格（n = 1：5，n = 2：48）；n = 3 的立方體恆等式 29 條成立 |
| S2 | `verify_path_laws` 18 項全成立；遙測 β 21、路徑 β 123、邊界化約 93、η 展開 88 |
| S3 | 範疇庫 9 個融貫子、群胚庫 12 個；拒絕案例 6／6；黏貼方案判準於 n ≤ 5（430 個上下文、20 個黏貼方案）全一致；群胚庫於 S₃ 中 8 個 2 維融貫子、288 個賦值成立 |
| S4 | RP²、Moore(5)、S₃ 表現複形：完備化收斂、局部合流、泛覆疊單連通且 χ 乘性成立（S₃：V6 E12 F18）；環面生長 1 4 8 12 16 20；ℤ/7 ⋊ ℤ/3 收斂得 21 元；ℤ/4 *_{ℤ/2} ℤ/6 的 H₁ = ℤ/12；三葉結群於 150 條規則預算內未完備 |
| S5 | 非交換 Stokes 於 40 個隨機聯絡成立；Ambrose–Singer 24 = 24、3 = 3；規範共變 30 面；平坦聯絡計數：環面 18、RP² 4、帶環圓盤 216；單值表示 5,454 對迴路；S₃ 複形的群胚模型迴路空間 6 元、UIP 失效 |
| S6 | sl₂ 環面 DGLA 公理 342 項檢查成立，h = 3 6 3，Kuranishi 二次型 19／20 非零；Heisenberg 型 DGLA 1,218 項檢查成立，h = 3 6 6；模塔：sl₂ 樣本於 2 階受阻（阻礙類閉而非正合），無阻樣本逐階提升至 5 階；切複形 = 衍生纖維積於三個點一致（`6 3 6 3`、`4 1 4 1`、`4 1 4 1`）；衍生纖維積 Betti `0 0 1` 合 Mayer–Vietoris 而嚴格纖維積為 `0 0 0` |
| S7 | 模式結構單調性；LNL 13／13、子結構 8／8、S4 4／4 的接受與拒絕皆如預期；↓ ⊣ ↑ 單位與餘單位可導；7 個含切證明項共 19 步約簡，類型保持且終止 |
| S8 | 語料 10／10 合預期：8 條 `proved`（核心全部接受）、「and = or」被反駁並給出反例 `a = tt, b = ff`、`double n = n + n` 回報 `stuck`；`plus (if a n 1) n` 深度 2 的執行樹 4 葉 1 截斷 |
| S9 | 維數 1、2、3 各 36 個合成實例：七項算子公理全成立；E₁ 於迴路字的作用 36 例成立；離散構形複形 (b₀, b₁)：E₁ 為 (2, 0)、E₂ 為 (1, 1)（3 格與 4 格）、E₃ 為 (1, 0)，與 Sⁿ⁻¹ 相符；兩條交換路徑繞數 +2 與 −2 個四分之一圈，相差一整圈 |
| S10 | Kan：S₃ 的五組 (H, X, Y) 上 \|Lan\| = [G:H]·\|X\|、\|Ran\| = \|X\|^[G:H]，兩側 Hom 計數相等（如 3 = 3、16 = 16）；層黏合：五個樣本相容對數 = 整體截面數（3、1、1、0、2）且黏合唯一；Morita：k[S₃] 的 Z 與 HH₀ 為 3／3、k[ℤ/6] 為 6／6、上三角 T₂ 為 1 與 2，於 M₂ 下不變；¬ 的伽羅瓦律 28,224 對成立；F(2) 的布林商 16 類，32 條類內等式全由 S8 證得且核心接受，15 對相鄰類代表全被反駁；Eckmann–Hilton：S₃ 不交換（阿貝爾化 2 元）、ℤ/6 交換 |

S10 的 ℤ/6 Kan 樣本取到的子群為整個群，屬退化情形，未計入上表。

### 9.4 未完成／待辦（第 2 回合結束時；現況見 §10.6）

- [ ] **推送遠端與 CI 實跑**：仍未取得 03 的遠端位址；第 2 回合已本地 commit。工作環境的快照未保存 `.git` 目錄，第 1 回合的本地提交紀錄（`1563ff8`）已遺失，本回合重新 `git init` 後以單一提交收錄兩回合全部內容。
- [ ] 與 01／02（M1–M14）合併。
- [ ] 尚未使用的組合範例：#4 單子分配律、#5 張量—直和對偶。
- [ ] H6 總成管線尚未納入 S 系列；現由 S10 橋接。
- [ ] S2 尚無 Kan 合成（`hcomp`／`transp`）與 Glue 類型；S4 無限群覆疊僅截斷建構；S8 歸納步無引理搜尋；S9 構形複形只算到 b₁。

### 9.5 已決定事項

- 第 2 回合模組採 `s<N>_` 前綴，與 H 系列同一工作區。
- 幾何結構（S4、S5、S6、S9）一律以有限組合模型與精確算術實作。

## 10. 開發指示（第 3 回合，2026-11-12）

> 除錯，減債，去重，清死碼，推送 https://github.com/vv0101v01/episode

### 10.1 除錯

以臨時探針（寫後即刪）對 S8、S9 作邊界輸入檢查，S8 找到三個缺陷並修正：

| 缺陷 | 重現命題 | 修正 |
| :-- | :-- | :-- |
| 先對自然數歸納，歸納步內的布林 `if` 無法再分歧，真命題回報 `stuck` | `Π b n. n + 0 = if b n n` | 分歧次序改為布林先於自然數（`stuck_split`） |
| 兩側無卡住的消除子但含自由自然數變數時，假命題回報 `stuck` | `Π n b. (if b n (S n)) = n` | 對剩餘自由變數分歧以具體化反例（`choose_split`） |
| 歸納步內建構子相異仍回報「需要引理」 | `Π n m. S n = S m` | 新增 `constructors_clash`，建構子相異即反駁 |

三個重現命題已併入 S8 語料（現 13 條）。

### 10.2 減債

- S4 `analyze_complex`：覆疊未完整建出時，`euler_multiplicative`、`fibers_uniform` 由空真改為 false。
- S10 `coherences_in_rewriting_group`：不再把 `CattError` 吞成 `None`，改為向上拋出。
- S10 `boolean_quotient`：以陣列存放類代表，去掉 `unwrap_or` 預設值。
- S10 `verify_kan`：不在 H 內的 K 生成元略去，免於越界。
- 各模組的檢驗入口原先在倉庫內無執行動線：新增 `@s10.round_two_audit()`（49 項），由 H6 可執行檔在第 1 回合審計之後呼叫。`moon run cmd/main`（於 `modules/h6_unified_pipeline`）實測：第 1 回合 9 項 `certified: true`，第 2 回合 49／49。

### 10.3 去重

- S10：群逆元表改用 S3 的 `FinGroup::from_table`（`inverses`）；添不動點（`GSet::with_fixed_point`）、子群位置表（`positions`）、基元交換子（`Algebra::commutator`）各收為單一函數。
- S9 `configuration_space`：兩個方體各一份的方格列舉合為一個迴圈。
- S6：兩處內嵌的線性同餘步收為 `lcg_step`。
- S8：`execute` 與 `search` 共用同一個分歧選擇。

S5、S6、S9 各自保有一份線性同餘產生器，S5、S9 各自保有一份並查集：三者為彼此無依賴的獨立模組，未為此引入依賴。

### 10.4 清死碼

刪除倉庫內無人引用、亦未列於任何 README 的函數：H2 `Arena::bvar`、`Arena::apps`、`Arena::is_beta_eta_normal`；H3 `Kernel::show_deriv` 及其專用輔助 `write_deriv`、`same_context_premises`。

### 10.5 推送

已推送至 `https://github.com/vv0101v01/episode`（`main`）。工作環境的快照不保存 `.git`，本地提交紀錄每回合遺失，故遠端以單一提交收錄三回合全部內容。

### 10.6 未完成／待辦

- [ ] 與 01／02（M1–M14）合併。
- [ ] 尚未使用的組合範例：#4 單子分配律、#5 張量—直和對偶。
- [ ] S2 尚無 Kan 合成與 Glue 類型；S4 無限群覆疊僅截斷建構；S8 歸納步內無布林分歧與引理搜尋；S9 構形複形只算到 b₁。
