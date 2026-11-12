# S1 — 德摩根立方體代數、局部可補性

獨立模組，無依賴。

自由德摩根代數 F(n) 的元素以反鏈正規形（互不包含的單項式位元集）表示，相等即結構相等。面格 𝔽 為立方體類型論的餘纖維化約束；立方體範疇的態射為名字到 F(n) 的代換。

| 檔案 | 公開接口 |
| :-- | :-- |
| `de_morgan.mbt` | `Dm`（`meet`／`join`／`neg`／`leq`／`subst`／`face`／`eval4`）、`free_algebra`、`verify_de_morgan_laws`、`semantically_equal4`（Kalman 完備性：於 Belnap 𝟜 上語義相等 ⇔ 正規形相等）、`relative_complement`、`complement_report`（布林中心、布林區間、Kleene 條件反例） |
| `face_lattice.mbt` | `Face`、`Dm::eq_zero`／`eq_one`、`Face::sieve`、`count_sieves`、`verify_face_semantics`（面格 ≅ 篩格） |
| `cube_category.mbt` | `CubeMap`（面、退化、聯絡、反轉）、`verify_cubical_identities` |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
