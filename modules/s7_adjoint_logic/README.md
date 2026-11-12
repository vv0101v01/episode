# S7 — 伴隨邏輯

獨立模組，無依賴。

模式前序上的伴隨自然演繹：每個模式帶結構性質 σ(m) ⊆ {W, C}，移位 ↓ ⊣ ↑ 連接模式。檢查器以資源回傳方式處理上下文分裂。

| 檔案 | 公開接口 |
| :-- | :-- |
| `adjoint.mbt` | `Modes`、`Prop`、`Tm`、`Checker::new`／`infer`／`proves` |
| `reduce.mbt` | `step`、`normalize(fuel~)`、`tm_size` |
| `theorems.mbt` | `lnl_modes`（! = ↓↑）、`substructural_modes`、`s4_modes`（□ = ↓↑）、`verify_claims`、`verify_adjunction`、`lnl_cut_examples`、`verify_subject_reduction` |

`theorems.mbt` 另有 `tensor_additive_claims`（組合範例 5：⊗ 對 ⊕ 分配、柯里化、⊕ 為餘積、& 為積，及兩個反例）與 `tensor_additive_cuts`（分配與提取公因子的往返）。

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
