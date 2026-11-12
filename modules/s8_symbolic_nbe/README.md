# S8 — 符號動態執行與 NbE 整合

依賴 H3（第 1 回合的 NbE 核心）。

開項以 H3 正規化；正規形中卡在符號變數上的 `if`／`rec` 決定分歧變數。分歧次序：卡住 `if` 的布林變數先兩路分歧，其次對卡住 `rec` 的自然數變數作歸納（歸納步以歸納假設經 `J` 改寫）；兩側已無卡住的消除子卻仍相異時，對剩餘自由變數分歧以取得具體反例。兩側建構子相異（`0` 對 `S`、`tt` 對 `ff`）即判反駁。執行樹編譯成消除子證明項，交 H3 核心對原命題重檢；閉正規形相異的葉給出反例路徑條件。

| 檔案 | 公開接口 |
| :-- | :-- |
| `symbolic.mbt` | `execute`（`SymTree`：`Leaf`／`BoolSplit`／`NatSplit`／`Cutoff`，`render`）、`prove`／`prove_source`（`ProofReport`：`proved`／`refuted`／`stuck`／`unsupported`）、`prelude`、`corpus`、`verify_corpus` |

歸納步只嘗試 `refl` 與單次歸納假設改寫；需要輔助引理的命題回報 `stuck` 並附兩側正規形。

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
