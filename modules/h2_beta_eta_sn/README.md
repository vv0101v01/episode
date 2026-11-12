# H2 — β約簡、η轉換、強正規化

獨立模組，無依賴。

項為 de Bruijn 駐留 DAG，結構相等等同編號相等。強正規化以約簡圖窮舉判定：有限且無環 ⇔ 強正規化；Kahn 拓樸排序求最長與最短約簡長度。

| 檔案 | 公開接口 |
| :-- | :-- |
| `arena.mbt` | `Node`、`Arena`（駐留）；O(1) `has_beta`／`has_eta`／`is_beta_normal`／`is_closed`；記憶化 `shift`、`subst`；`tree_size`、`dag_size` |
| `reduction.mbt` | `contract_head`（8 條計算規則）、`eta_head`（2 條 η 收縮）、`reducts`、`run_leftmost`、`run_perpetual`、`run_gross_knuth`、`complete_development`、`church_rosser_join`、`verify_z_property`、`eta_normalize` |
| `sn_graph.mbt` | `sn_certificate`（`SnCert`：判定、節點、邊、最長、最短、正規形）、`local_confluence_defect` |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §5.1。
