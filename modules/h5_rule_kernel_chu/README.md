# H5 — 橋接 H1 × H3：Chu／伽羅瓦對偶

依賴 `h1_rule_harmony`、`h3_nbe_typecheck`。組合範例 #10 Chu 空間。

把 H1 由規則綱要預測的計算規則數與極性，對照 H3 核心的實際行為：每條計算規則以 `refl` 檢查；負極性形成子的 η 以 `refl` 通過，正極性形成子的 η 以 `refl` 被拒而以消除子證得。操作矩陣（核心求值是否觸發）與綱要矩陣逐格比較。

| 檔案 | 公開接口 |
| :-- | :-- |
| `chu.mbt` | `rule_cases`、`verify_former`、`verify_all`（`FormerReport`）、`verify_chu_duality`（`ChuReport`） |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §5.1。
