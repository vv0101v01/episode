# S9 — 小立方體算子

獨立模組，無依賴。座標為精確有理數。

| 檔案 | 公開接口 |
| :-- | :-- |
| `operad.mbt` | `Q`、`Box`、`Cubes`（`unit`／`compose`／`permute`／`suspend`／`order`／`is_valid`）、`ass_compose`、`random_cubes`、`verify_operad_axioms`（封閉、單位律、序列與平行結合律、等變性、穩定化 Eₙ → Eₙ₊₁、E₁ → Ass）、`act_on_loops`、`verify_loop_action` |
| `configuration.mbt` | `configuration_space(dim, grid)`：Eₙ(2) 的離散方體複形模型及其 b₀、b₁（𝔽₂）；`swap_windings`：二維中兩條交換路徑的繞數 |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
