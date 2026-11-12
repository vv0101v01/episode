# S6 — 形變函子與模塔、衍生纖維積

獨立模組，無依賴。係數為 𝔽_p（p = 32003）。

| 檔案 | 公開接口 |
| :-- | :-- |
| `linear.mbt` | 模算術、`Matrix`（秩、核、解方程）、`span_rank` |
| `complex.mbt` | `Cochain`、`derived_fiber_product`（同倫拉回 = 映射錐平移）、`strict_fiber_product_betti`、`verify_mayer_vietoris`、`is_chain_map` |
| `dgla.mbt` | `Dgla`（`d`／`bracket`／`curvature`／`is_maurer_cartan`／`cochain`／`verify_axioms`）、`sl2`、`abelian`、`torus_dgla`、`heisenberg_dgla` |
| `tower.mbt` | `Dgla::moduli_tower`（逐階提升 Maurer–Cartan 元素，回報阻礙類是否閉、是否正合、提升 torsor 維數）、`Dgla::deformation_report`（h⁰、h¹、h²、Kuranishi 二次型）、`verify_tangent_fiber_product` |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
