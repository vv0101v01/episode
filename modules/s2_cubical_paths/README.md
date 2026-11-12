# S2 — 路徑類型

依賴 S1（區間項即 `Dm`）。

帶路徑類型 `Path A a b`、路徑抽象 `⟨i⟩ t`、路徑應用 `p @ r` 的立方體核心：NbE 求值，路徑應用於端點時依邊界化約，回讀時作路徑 η 展開；雙向類型檢查。

| 檔案 | 公開接口 |
| :-- | :-- |
| `syntax.mbt` | 項與類型語法 |
| `nbe.mbt` | `Theory`（求值、回讀、遙測：β、路徑 β、邊界化約、η 展開） |
| `checker.mbt` | `check_ty`／`infer`／`check`、`add_const`、`normalize`、`definitionally_equal` |
| `laws.mbt` | `verify_path_laws`：refl、sym（定義性對合）、ap 函子性、路徑 η、funext 與 happly 互逆、聯絡方塊、德摩根方塊，以及兩個拒絕案例 |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
