# S4 — 可判定性與合流性、泛覆疊空間

獨立模組，無依賴。

群表現的 Knuth–Bendix 完備化（shortlex 序）：收斂時字問題可判定、正規形唯一。2-複形的基本群由生成樹讀出；泛覆疊以正規形為頂點纖維顯式建構。

| 檔案 | 公開接口 |
| :-- | :-- |
| `rewriting.mbt` | `Presentation`、`Presentation::complete(max_rules~)`、`Rws::normal_form`／`equal`／`enumerate`／`growth`／`verify_local_confluence`、`abelianization`（Smith 型消元）、`amalgam`（推出）、`semidirect`（半直積） |
| `cover.mbt` | `Complex`、`fundamental_group`、`universal_cover`、`Cover::lift_path`、`analyze_complex`、樣本複形 `rp2`／`torus`／`klein_bottle`／`moore_complex`／`disk_with_loop`／`presentation_complex` |

無限群的覆疊於 `limit` 處截斷，此時 `euler_multiplicative`、`fibers_uniform` 兩欄為 false（未能成立）。

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
