# S5 — 聯絡、曲率、水平分佈；高維群胚模型

依賴 S4。

2-複形上的離散主叢：聯絡為每條邊的纖維置換，曲率為每個面的邊界和樂，水平分佈為邊的提升集合。

| 檔案 | 公開接口 |
| :-- | :-- |
| `connection.mbt` | `Connection`（`holonomy`／`curvature`／`is_flat`／`gauge`／`horizontal`／`total_space`）、`Horizontal::to_connection`、`pure_gauge`、`random_connection`、置換工具 |
| `theorems.mbt` | `verify_nonabelian_stokes`、`verify_ambrose_singer`、`verify_gauge_covariance`、`verify_flat_count`（#平坦聯絡 = \|Hom(π₁, S_n)\|·\|S_n\|^(V−1)）、`verify_monodromy_representation`、`representable_connection`、`groupoid_model`（基本群胚作為類型的 1-截斷模型：迴路空間、UIP 失效、基點路徑空間可縮） |

**由泛覆疊導出纖維叢**：`associated_bundle(x, action)` 把 π₁ 在有限集上的作用變成平坦聯絡（伴隨叢 X̃ ×_{π₁} F；作用違反關係子則拒絕）；`classify_covering` 以 Grothendieck 構造建出全空間並讀出對應子群的表現與 H₁。π₁ 本身不必有限；推論為 Nielsen–Schreier 秩公式 1 + n(r − 1)。

定理與演算法編號見根目錄 `Dev.xlsx`；驗證紀錄見根目錄 `README.md` §9.3。「定理」為樣本或窮舉上的程式檢驗。
