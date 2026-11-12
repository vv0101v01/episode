# H1 — 規則調和性（引入／消除／計算／唯一性規則）

獨立模組，無依賴。

規則為 64-bit 原子位元集。計算規則 = 局部健全性（引入後消除可反演，Horn 閉包判定）；唯一性規則 = 局部完備性（負式或正式展開）。引入與消除以 `locally_sound` 為關係構成 Chu 空間，兩個極運算構成伽羅瓦對應。

| 檔案 | 公開接口 |
| :-- | :-- |
| `rules.mbt` | `Connective`、`IntroRule`、`ElimRule`；`horn_closure`、`locally_sound`、`Connective::harmony`、`derive_general_elim`、`with_general_elim`、`computation_rule_names` |
| `galois.mbt` | `RuleUniverse`：`right_polar`、`left_polar`、`verify_galois_law`、`concepts`、`stability`、`from_matrix` |
| `library.mbt` | `type_formers()`（Π、Σ、Unit、Empty、Bool、Nat、Id）、`logical_connectives()`（→、∧、∨、⊤、⊥、tonk、weak-∧）、`universe_of` |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §5.1。
