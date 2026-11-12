# H4 — 橋接 H2 × H3：局部化

依賴 `h2_beta_eta_sn`、`h3_nbe_typecheck`。組合範例 #12 局部化、#3 纖維積。

正規化即對約簡箭頭作局部化：`class_of` 把項送到其 η-長正規形的駐留編號，約簡箭頭全部變為恆等。`analyze` 走訪整個約簡圖，對每個節點重新類型檢查（主詞約簡）並比較類別。

| 檔案 | 公開接口 |
| :-- | :-- |
| `bridge.mbt` | `embed`、`reify`、`Localizer`（`class_of`、`equivalent`）、`analyze`（`BridgeReport`）、`verify_confluence_squares` |

**以類型為度量的強正規化上界**：`measure_bound(t)` 對簡單類型片段（變數、λ、應用、`0`／`S`／`tt`／`ff`／`star`）以 Gandy 的嚴格單調泛函解釋直接算出最長 β-約簡長度的上界，無需窮舉約簡圖；片段之外回傳 `None`。`BridgeReport.measure_bound` 與窮舉所得 `longest` 並列。`embed` 把 `Let` 嵌為 β-可約式。

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §5.1。
