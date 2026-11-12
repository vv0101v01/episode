# S4 — 可判定性與合流性、泛覆疊空間

獨立模組，無依賴。

群表現的 Knuth–Bendix 完備化（shortlex 序）：收斂時字問題可判定、正規形唯一。2-複形的基本群由生成樹讀出；泛覆疊以正規形為頂點纖維顯式建構。

| 檔案 | 公開接口 |
| :-- | :-- |
| `rewriting.mbt` | `Presentation`、`Presentation::complete(max_rules~)`、`Rws::normal_form`／`equal`／`enumerate`／`growth`／`verify_local_confluence`、`abelianization`（Smith 型消元）、`amalgam`（推出）、`semidirect`（半直積） |
| `cover.mbt` | `Complex`、`fundamental_group`、`universal_cover`、`Cover::lift_path`、`analyze_complex`、樣本複形 `rp2`／`torus`／`klein_bottle`／`moore_complex`／`disk_with_loop`／`presentation_complex` |



## 泛覆疊作為 HIT 上的類型族

2-複形即 HIT 的簽名（點、路徑、2-路徑建構子）。泛覆疊由遞迴原理給出：`Code(v) = ‖base = v‖₀`，以收斂重寫系統的正規形為集合截斷的典範代表；每條邊的值為 `ua(· 右乘 [e])`；每個面的義務是邊界上等價的合成為恆等。纖維以正規形內涵表示、從不列舉，π₁ 有限與否無關（圓、環面、克萊因瓶、自由群皆同一套程式）。前提只有重寫系統收斂。

| 接口 | 內容 |
| :-- | :-- |
| `Complex::code_family` | 建立 `CodeFamily`（未收斂為 `None`） |
| `transport`／`lift` | 沿邊的傳送；全空間 Σ(v). Code(v) 中的唯一路徑提升 |
| `encode`／`decode` | `encode(p) = transport(p, ε)`（S¹ 上即纏繞數）；`decode` 把正規形還原為邊路 |
| `verify_encode_decode` | 族良定、`encode ∘ decode = id`、`decode ∘ encode ∼ id` |
| `UPath`、`ap_code`、`transport_along`、`canonical`、`verify_univalence_computation` | 集合層級的計算性單值性：宇宙路徑（refl、ua、合成、反向）有典範形，沿之傳送逐步可算 |
| `bouquet(n)` | n 個圓的楔和 |

`decode ∘ encode ∼ id` 的同倫以獨立於重寫系統的方式檢驗：無面時為自由約簡（充要），有面時為差迴路於 H₁ 為零（必要條件，π₁ 交換時充要）。

`universal_cover`／`analyze_complex` 是把全空間具體化成一個複形：π₁ 有限時為整個全空間，無限時只是其中一個有限球，此時 `euler_multiplicative`、`fibers_uniform` 記為 false。

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
