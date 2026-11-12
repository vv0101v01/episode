# H6 — 總成管線

依賴 H1–H5。可執行入口 `cmd/main`（`moon run cmd/main`）。

原始碼 → 精化 → 類型檢查與推導樹 → NbE 正規形 → 約簡圖證書與策略比較 → 抽取程式於惰性機執行；另有規則層與核心層的系統審計。

| 檔案 | 公開接口 |
| :-- | :-- |
| `pipeline.mbt` | `run_pipeline`（`PipelineReport`：`certified`、`render`）、`system_audit`（`SystemAudit`：`certified`、`render`）、`corpus` |
| `cmd/main/main.mbt` | 印出系統審計與語料各項的管線報告 |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §5.1。

`cmd/main` 另依賴 S10：在第 1 回合的系統審計與語料管線之後，印出 `@s10.round_two_audit()` 的逐項結果（S1–S10）。
