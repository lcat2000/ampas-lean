# AMPAS — Lean 證明驗證管線，以及對它能力邊界的誠實說明

**English: [README.md](README.md)**

這個儲存庫把提交的 Lean 4 證明對照**凍結的參考陳述**做檢查，整個設計圍繞一個區分：

> Lean 核心接受一條定理，表示它的證明在**實際使用的公理與定義下**通過型別檢查。
> 這**不**表示原始自然語言的數學主張已被正確證明。

這裡大部分的工程都是在處理這兩件事之間的落差，以及避免高估任何單一檢查器所建立的東西。**偵測不到什麼，和偵測得到什麼，記錄得一樣仔細**：[ASSUMPTIONS.md](ASSUMPTIONS.md) 是在相信本儲存庫任何結果之前該先讀的檔案。

## 它實際做什麼

一份提交是一個 `.lean` 檔，聲稱證明了某條凍結的參考陳述。它會經過：

| 層 | 它建立了什麼 |
| --- | --- |
| **沙箱編譯** | 非特權使用者、唯讀的受信任 olean、CPU／記憶體／檔案大小上限、受信任產物編譯前後都做雜湊 |
| **核心重放**（`leanchecker`） | Lean 自己的核心從 olean 重新檢查每個宣告 |
| **第二套核心**（[lean4lean](https://github.com/digama0/lean4lean)） | 另一位作者獨立寫的核心重檢同一批 olean。認證要求**兩套都通過** |
| **第三道檢查**（[`harness/kernel3`](docs/review-third-check.md)） | 從零寫的 Python 型別檢查器，不共用 Lean 任何程式碼——只佐證**項層** |
| **公理稽核** | 遞移公理對照每條主張的政策；標記 `sorryAx`、原生求值、陳述中的 `opaque`、`unsafe`、`partial` |
| **closure 檢查** | 陳述依賴的每個常數，**含定義本體**，與參考逐一比對 |
| **陳述比對器** | elaborated 陳述與凍結版本比對，結構相同或核心定義等價 |
| **形式化簽核** | 內容定址凍結、機器推導的 guard 定理、Ed25519 簽章、漂移偵測 |

最後一列是**無法自動化**的那一列，本儲存庫不假裝相反。見 [docs/review-formalization.md](docs/review-formalization.md)。

## 已記錄執行的結果

| 語料 | 份數 | 結果 |
| --- | --- | --- |
| 核心（`corpus/manifest.json`） | 16（4 正確、12 攻擊） | 16/16 如預期；兩套 Lean 核心全部一致；第三道檢查佐證 15 份，並獨立抓到核心旁路攻擊 |
| Mathlib（`reference/claims_mathlib.json`） | 2 | 2/2 如預期 |
| 外部驗證（`corpus/manifest_fermat.json`） | 5 | 5/5 如預期 |
| 測試 | 51 | 乾淨 checkout 全部通過 |

每個攻擊都**由應該攔下它的那一層攔下**，不只是「被拒絕」——`build/ablation.json` 記錄每個攻擊觸發了哪些訊號，因為一套「某一層做完所有工作、其他層什麼都沒做」的系統，在通過／失敗的摘要上看起來完全一樣。

### 外部驗證題組

語料是寫管線的同一雙手寫的，所以另外用一個取自數學史的案例測試：

- **Fermat**（約 1640）斷言每個 Fermat 數 $F_n = 2^{2^n}+1$ 都是質數，他驗到 $F_0 \ldots F_4$。這個主張是**錯的**。
- **Euler**（1732）推翻它：$F_5 = 4294967297 = 641 \times 6700417$。

| 提交 | 預期 | 結果 | 被哪一層攔下 |
| --- | --- | --- | --- |
| Euler 的反駁，用因數分解 | certified | **CERTIFIED** | —（公理只有 `propext`） |
| Fermat 的主張：驗他驗過的幾項，然後 `sorry` | rejected | **REJECTED** | 公理政策（`sorryAx`）＋ `SORRY` 旗標 |
| Fermat 的主張，**完全沒有 `sorry`**，缺口藏進 `axiom` | rejected | **REJECTED** | 公理政策，並指名該公理 |
| Fermat 的主張，**每一行都真的證出來**——但證的是 `n ≤ 3` 的限制版本，掛著一般主張的名字 | rejected | **REJECTED** | 陳述比對器 |
| Euler 的陳述，但證的是 $2^{32}$ 而非 $2^{32}+1$ | rejected | **REJECTED** | 陳述比對器 |

第三列值得多看一眼：沒有 `sorry`、沒有外加公理、Lean 完全誠實、兩套核心都滿足——而形式化就只是**不是它掛名的那條主張**。擋在它與一張證書之間的，只有陳述比對器。

## 自己驗證

四個層級。每一層自成一體，你跑不了的層級不會讓你跑得了的層級失效。

```bash
git clone https://github.com/lcat2000/ampas-lean.git && cd ampas-lean

# tier 0 — 不需要 Lean，幾秒鐘
python3 -m pytest tests/test_third_check.py -q -k "not pipeline"

# tier 0–1 — 只需要固定版 Lean 工具鏈，約 6 分鐘
./scripts/bootstrap.sh
./scripts/verify.sh 1

# tier 2 — 加上第二套獨立核心
./scripts/build-lean4lean.sh && ./scripts/verify.sh 2

# tier 3 — 加上 Mathlib 主張（約 20 分鐘，從原始碼編譯 Mathlib）
./scripts/build-mathlib-tier.sh && ./scripts/verify.sh
```

完整說明（包含稽核器連結失敗時怎麼處理）在 [INSTALL.md](INSTALL.md)。

**建議先跑 tier 0。** 它完全不需要 Lean，而且它把第三道檢查的**範圍**釘在手寫的偽造匯出檔上：statement 模式必須被拒、兩個能證出 `False` 的偽造 inductive 規格不能被背書、小消去對照組必須仍被拒絕。這些測試存在的目的，是讓日後的任何改動都不能悄悄放寬「乾淨結果」的意義。

## 本儲存庫**沒有**建立什麼

簡版；[ASSUMPTIONS.md](ASSUMPTIONS.md) 有完整清單與各項的證據。

- **形式化忠實度不是機器判定的。** 凍結、簽署與 guard 讓人的判斷變得可稽核、可歸屬、且不會無聲漂移。它們不會讓那個判斷變成正確。
- **多套核心一致，證據力比看起來弱。** 2026 年有數個 Lean 核心健全性 bug 浮現；其中一個案例裡，用另一套獨立核心交叉檢查**也接受了**那個非法證明，原因是那套核心自身有個無關的 bug（[Tao, 2026-10-09](https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/)）。**實作的獨立性不等於失效的獨立性。**
- **第三道檢查只佐證項層。** 它不推導 inductive 規格是否合法，而 `tests/forgeries/` 裡兩個偽造就是從那個洞證出 `False`。它的來源界定閘門會把這類宣告**回報**出來，而不是替它們背書。
- **受信任基礎縮小了但沒有消失。** Lean 的 **elaborator**（產生 olean 的那一步）、作業系統與沙箱全都仍被信任。
- **Mathlib 只涵蓋一條主張**，依賴錐 387 個 olean，不是整個程式庫。
- **金鑰管理不在範圍內。** 這裡用的是示範金鑰。
- **`unreviewed/` 不是交付內容**，沒有任何東西載入它。見該目錄的 README。

## 目錄結構

```
reference/     凍結的陳述、guard、主張目錄、簽核紀錄、來源基準、版本固定、裁定紀錄
corpus/        測試資料：正確提交、13 個攻擊、Fermat 題組
harness/       驅動程式、Lean 稽核器、第三道檢查、基準與 ablation 工具
tests/         51 項測試，含離線範圍測試與偽造向量
scripts/       bootstrap 與分層驗證
evidence/      已記錄執行的結果，附每個檔案的索引
mathlib-tier/  選用的 Mathlib Lake 專案，刻意分開，核心主張才不會取得 Mathlib 依賴
docs/          兩份審查文件與建置註記
unreviewed/    隔離的程式碼，保留供比對，沒有任何東西載入
```

## 接下來要進行的工作

[ROADMAP.md](ROADMAP.md)，依優先順序。最前面幾項：

1. **不再把「兩套核心一致」當成最強證據**——它現在已知可被擊破。要換成更強的東西，並說清楚那是什麼。
2. **補上第三道檢查的 inductive 規格缺口，但只往安全的方向補**：先做正性檢查，並以兩套 Lean 核心做差分測試，而不是直接改那個受審查中的檢查器。
3. **取得尚未完成的審查者確認**：Fermat 題組的兩份形式化簽核，以及第三道檢查的裁定紀錄，目前都是 **PENDING**，而檔案本身明寫了這一點。

## 授權

Apache-2.0，見 [LICENSE](LICENSE)。

Lean 工具鏈與 Mathlib 是各自獨立的作品、各有授權（都是 Apache-2.0）；`lean4lean` 的上游在 [digama0/lean4lean](https://github.com/digama0/lean4lean)，是在建置時取得，不隨本儲存庫散布。
