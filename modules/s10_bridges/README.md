# S10 — 橋接模組

依賴 S1–S9（S2、S7 僅供總審計）與 H3。把第 2 回合各結構以組合範例相互結合，並接回第 1 回合的核心。

| 檔案 | 組合範例 | 公開接口 |
| :-- | :-- | :-- |
| `groups.mbt` | — | `group_table`（S4 重寫系統 → 乘法表）、`GSet`（`is_action`、`with_fixed_point`）、`subgroup`、`subgroup_table`、`positions`、`inverses`、`restrict`、`coset_action`、`count_equivariant` |
| `kan.mbt` | #1 Kan 擴展 | `left_kan`（G ×_H X）、`right_kan`（Hom_H(G, X)）、`verify_kan`（Lan ⊣ Res ⊣ Ran 的計數檢驗）、`coherences_in_rewriting_group`（S4 的群作為 S3 融貫子的模型） |
| `sheaf.mbt` | #2 層黏合 | `sections`、`verify_gluing`（S5 聯絡的水平截面滿足等化子條件）、`gluing_sample` |
| `morita.mbt` | #11 Morita | `Algebra`、`matrices`、`group_algebra`、`upper_triangular`、`verify_morita`（中心與 HH₀ 於 A ↦ Mₙ(A) 下不變；線性代數取自 S6） |
| `logic.mbt` | 伽羅瓦對應、#9 Operad | `verify_negation_galois`（S1）、`dm_to_bool`、`boolean_quotient`（S1 × S8 × H3）、`eckmann_hilton`（S9 × S4）、`round_two_audit`（S1–S10 全部定理檢驗的總審計，由 H6 可執行檔呼叫） |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
