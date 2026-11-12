# S3 — 弱 ω-群胚

獨立模組，無依賴。

Finster–Mimram 的 CaTT：黏貼方案判定 `⊢ps`、融貫子的兩條引入規則（運算、相等），`groupoid~` 開關去掉滿性邊條件即得 Brunerie 式弱 ω-群胚理論。

| 檔案 | 公開接口 |
| :-- | :-- |
| `catt.mbt` | 類型／項／代換、`is_pasting_scheme`、`triangle_order_is_linear`（⊳ 全序判準）、融貫子檢查 |
| `enumerate.mbt` | `verify_ps_characterization(n)`：窮舉 n 個變數的球狀上下文，比對 `⊢ps` 與 ⊳ 全序判準 |
| `library.mbt` | `Library::build(groupoid~)`：恆等、合成、結合子、單位子、交換律方塊、逆與消去 |
| `model.mbt` | `FinGroup`、`verify_group_model`（融貫子在有限群 1-群胚中的解釋）、`verify_rejections` |

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
