# H3 — 正規化、類型檢查、證明即程式

獨立模組，無依賴。

call-by-need NbE；回讀由類型導向，產出 η-長正規形。轉換先走無類型快速路徑，失敗時改走類型導向比較（涵蓋 Unit-η）。核心回傳推導樹，其規則分屬形成、引入、消除、結構四類。

| 檔案 | 公開接口 |
| :-- | :-- |
| `syntax.mbt` | `Tm`（Church 式核心）、`KernelError`、`shift_tm`、`subst_tm`、`is_normal`、`show_tm` |
| `domain.mbt` | `Val`、`Kernel`、`eval`、`force`、`quote_nf`、`quote_ty`、`conv`、`conv_typed`、`sub_ty` |
| `checker.mbt` | `Rule`、`Deriv`、`infer`、`check`、`normalize`、`convertible`、`convertible_untyped` |
| `surface.mbt` | S-表達式 `parse`、雙向精化 `Kernel::elaborate` |
| `machine.mbt` | `extract`（類型抹除）、`Machine`（惰性 Krivine 機）：`run`、`readback`、`read_nat` |

**核心層定義**：`Tm::Let(A, e, b)`（b 綁定 1）。類型檢查以規則 `LetDef` 把定義以懸置綁入語境（`Ctx::bind_def`），求值為惰性 ζ（計數器 `Kernel.zeta`），抽取機把定義編為惰性引數，定義體至多求值一次。表層 `let`／`def` 直接生成 `Let`，不再代換展開。`zeta_expand` 把定義全部代入，`let_count` 計定義數。

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §5.1。
