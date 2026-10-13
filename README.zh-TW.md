# AMPAS — Lean 證明驗證管線，以及它做不到什麼

**English: [README.md](README.md)**

這個專案把送審的 Lean 4 證明，拿去跟**事先凍結的參考陳述**比對。整套設計只為了講清楚一件事：

> Lean 核心接受一條定理，意思是這份證明在**它實際用到的公理與定義之下**通過型別檢查。
> 不代表原本那句自然語言的數學主張被證明了。

這兩件事之間有一段距離，這裡大部分的工程都花在那段距離上，以及避免把任何單一檢查器的結論講得比實際更強。**哪些東西檢查不到，寫得跟檢查得到的一樣詳細**——要採信這裡的任何結果，請先讀 [ASSUMPTIONS.md](ASSUMPTIONS.md)。

## 實際上做了哪些檢查

一份送審證明是一個 `.lean` 檔，聲稱證出了某條凍結的參考陳述。它要通過這些關卡：

| 關卡 | 這一關能證明什麼 |
| --- | --- |
| **沙箱編譯** | 以非特權帳號執行，受信任的 olean 掛成唯讀，限制 CPU、記憶體與輸出檔大小，編譯前後都對受信任檔案做雜湊比對 |
| **核心重放**（`leanchecker`） | 用 Lean 自己的核心，從 olean 把每一個宣告重新檢查一遍 |
| **第二套核心**（[lean4lean](https://github.com/digama0/lean4lean)） | 另一位作者獨立寫的核心，重檢同一批 olean。**兩套都通過**才可能認證 |
| **第三道檢查**（[`harness/kernel3`](docs/review-third-check.md)） | 用 Python 從零寫的型別檢查器，和 Lean 不共用任何程式碼。只對**項層**提供旁證 |
| **公理稽核** | 把遞移用到的公理拿去對每條主張各自的政策；另外標記 `sorryAx`、原生求值、陳述裡出現的 `opaque`、`unsafe`、`partial` |
| **依賴閉包檢查** | 陳述依賴到的每一個常數，**連定義本體一起**，跟參考環境逐一比對 |
| **陳述比對器** | 把 elaborate 後的陳述跟凍結版本比對；可要求結構完全相同，或放寬到核心的定義等價 |
| **形式化簽核** | 內容定址的凍結、由機器推導型別的 guard 定理、Ed25519 簽章，加上漂移偵測 |

最後一關**沒辦法自動化**，這個專案也不裝作可以。詳見 [docs/review-formalization.md](docs/review-formalization.md)。

## 這份紀錄的執行結果

| 語料 | 份數 | 結果 |
| --- | --- | --- |
| 核心（`corpus/manifest.json`） | 16（4 份正確、12 份攻擊） | 16／16 與預期相符；兩套 Lean 核心判定全部一致；第三道檢查替其中 15 份背書，並自行抓到核心旁路攻擊 |
| Mathlib（`reference/claims_mathlib.json`） | 2 | 2／2 與預期相符 |
| 外部驗證（`corpus/manifest_fermat.json`） | 5 | 5／5 與預期相符 |
| 測試 | 51 | 從乾淨 checkout 全數通過 |

每個攻擊都是**被該攔它的那一關攔下來的**，不是只有「結果被拒絕」這麼籠統。`build/ablation.json` 記錄每個攻擊觸發了哪些訊號——因為如果一套系統裡只有一關在做事、其他關形同虛設，光看通過／失敗的總表會長得一模一樣。

### 外部驗證題組

語料是寫這套管線的人自己寫的，所以另外找了一組數學史上的真實案例來測：

- **Fermat**（約 1640 年）斷言每個 Fermat 數 $F_n = 2^{2^n}+1$ 都是質數，他手算驗到 $F_4$。這個主張是**錯的**。
- **Euler**（1732 年）推翻了它：$F_5 = 4294967297 = 641 \times 6700417$。

| 送審內容 | 預期 | 結果 | 被哪一關攔下 |
| --- | --- | --- | --- |
| Euler 的反駁，用因數分解證出來 | 認證通過 | **認證通過** | —（只用到 `propext` 一條公理） |
| Fermat 的主張：先驗他驗過的那幾項，剩下寫 `sorry` | 拒絕 | **拒絕** | 公理政策（`sorryAx`）＋ `SORRY` 標記 |
| Fermat 的主張，**完全沒有 `sorry`**，把缺口塞進一條 `axiom` | 拒絕 | **拒絕** | 公理政策，而且會指名那條公理 |
| Fermat 的主張，**每一行都真的證出來了**——但證的是 `n ≤ 3` 的限縮版，卻掛著一般主張的名字 | 拒絕 | **拒絕** | 陳述比對器 |
| Euler 的陳述，但證的是 $2^{32}$ 不是質數，不是 $2^{32}+1$ | 拒絕 | **拒絕** | 陳述比對器 |

第三列最值得停下來看：沒有 `sorry`、沒有多加公理、Lean 寫得完全誠實、兩套核心都接受——問題只在於這份形式化**根本不是它掛名的那條主張**。這種情況下，唯一擋在它和一張認證之間的，就只有陳述比對器。

## 自己動手驗證

分四個層級。每一層都能單獨成立：跑不到的層級，不會影響已經跑完的層級的結論。

```bash
git clone https://github.com/lcat2000/ampas-lean.git && cd ampas-lean

# 第 0 層 — 不需要 Lean，幾秒鐘跑完
pip install pytest
python3 -m pytest tests/test_third_check.py -q -k "not pipeline"

# 第 0–1 層 — 只需要固定版本的 Lean 工具鏈，約 6 分鐘
pip install -r requirements.txt
./scripts/bootstrap.sh
./scripts/verify.sh 1

# 第 2 層 — 加上第二套獨立核心
./scripts/build-lean4lean.sh && ./scripts/verify.sh 2

# 第 3 層 — 加上 Mathlib 的主張（約 20 分鐘，要從原始碼編譯 Mathlib）
./scripts/build-mathlib-tier.sh && ./scripts/verify.sh
```

完整步驟在 [INSTALL.md](INSTALL.md)，包含稽核器連結失敗時怎麼繞過。

**建議先跑第 0 層。** 它完全不需要 Lean，而它測的正是第三道檢查的**適用範圍**：拿手寫的偽造匯出檔去餵它，看它會不會拒絕——statement 模式的匯出必須被擋掉、兩個能證出 `False` 的偽造 inductive 規格不准被背書、而小消去那組對照必須照樣被拒。這些測試存在的理由，就是不讓日後任何改動悄悄放寬「結果乾淨」的意思。

## 這個專案不能證明的事

以下是簡版，完整清單和每一項的證據在 [ASSUMPTIONS.md](ASSUMPTIONS.md)。

- **形式化忠不忠實，機器判不出來。** 凍結、簽章和 guard 能做到的是：讓人的判斷變成可稽核、可歸責、而且不會無聲走鐘。它們沒辦法讓那個判斷變正確。
- **多套核心一致，證據力沒有看起來那麼高。** 2026 年陸續出現幾個 Lean 核心的健全性 bug，其中一個案例裡，拿另一套獨立核心去交叉檢查，結果**那套核心也接受了**那份非法證明——因為它自己有另一個無關的 bug（[Tao, 2026-10-09](https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/)）。**實作各自獨立，不等於失效各自獨立。**
- **第三道檢查只能旁證項層，僅此而已。** 它不會去推導一個 inductive 規格合不合法，而 `tests/forgeries/` 裡那兩個偽造，就是從這個缺口證出 `False` 的。它的來源查核會把這類宣告**明白列出來**，而不是替它們背書。
- **受信任的基礎縮小了，但沒有消失。** Lean 的 **elaborator**（也就是產生 olean 的那一步）、作業系統、沙箱，全都還在信任範圍內。
- **Mathlib 只涵蓋一條主張**，依賴錐 387 個 olean，不是整個程式庫。
- **金鑰管理不在範圍內，而且簽章不代表任何人背書。** 這把金鑰是在建置這個專案的容器裡生成的，沒有任何人保管它。它只能證明一份紀錄沒有被改過，再多就沒有了。
- **忠實度的判斷沒有經過獨立審查。** 13 條主張全部由**寫這套管線的同一個助理**審的（見 [REVIEW-CHECKLIST.md](REVIEW-CHECKLIST.md)），而擁有者的確認記錄為「委任」而非本人逐條看過。
- **`unreviewed/` 不是交付內容**，也沒有任何程式會載入它。說明見該目錄的 README。

## 目錄結構

```
reference/     凍結的陳述、guard、主張目錄、簽核紀錄、來源基準、版本固定、裁定紀錄
corpus/        測試資料：正確的送審證明、13 個攻擊、Fermat 題組
harness/       驅動程式、Lean 稽核器、第三道檢查、基準與歸因工具
tests/         51 項測試，含不需要 Lean 的範圍測試與偽造向量
scripts/       bootstrap 與分層驗證腳本
evidence/      這份紀錄的執行結果，附每個檔案的用途索引
mathlib-tier/  選用的 Mathlib Lake 專案。刻意獨立，核心主張才不會誤取 Mathlib 依賴
docs/          兩份審查文件與建置註記
unreviewed/    隔離起來的程式碼，留著供比對，沒有任何東西載入它
```

## 接下來要做的事

[ROADMAP.md](ROADMAP.md) 依優先順序排列，前三項是：

1. **別再把「兩套核心都通過」當成最強的證據**——它已經被證實擊得破。要換成更強的東西，而且要說清楚那是什麼。
2. **補第三道檢查的 inductive 規格缺口，但只能往安全的方向補。** 先做正性檢查，而且要拿兩套 Lean 核心做差分測試，不是直接改那個還在受審的檢查器。
3. **讓作者以外的人來審忠實度判斷。** 現在 13 條的 `reviewed_by` 都是寫這套管線的那個助理，擁有者的確認是「委任」的（見 [REVIEW-CHECKLIST.md](REVIEW-CHECKLIST.md)）。這件事記錄得很誠實，但誠實不等於獨立——而獨立性才是重點。

## 授權

Apache-2.0，見 [LICENSE](LICENSE)。

Lean 工具鏈與 Mathlib 是各自獨立的作品、各有授權（都是 Apache-2.0）。`lean4lean` 的上游在 [digama0/lean4lean](https://github.com/digama0/lean4lean)，建置時才取得，不隨這個專案一起散布。
