# 證據檔案

每個檔案都由本包內的指令重現（指令見 `README.md` 第 6 節）。

| 檔案 | 內容 | 產生指令 |
| --- | --- | --- |
| `environment.json` | 工具鏈、三道檢查各自的來源與雜湊、沙箱與資源上限；第三道檢查的 `provenance` / `covers` / `does_not_cover` 就在這裡 | 手動記錄＋雜湊計算 |
| `corpus_results_threechecks.json` | **本輪**：核心語料 16 份，三道檢查 | `harness/ampas_lean.py corpus/manifest.json`（`AMPAS_THIRD_CHECK=1`） |
| `corpus_results_mathlib3.json` | **本輪**：Mathlib 語料 2 份，三道檢查 | 同上，加 `AMPAS_CLAIMS` / `AMPAS_EXTRA_LEAN_PATH` / `AMPAS_KERNEL_BASELINE` |
| `ablation.json` | 每個攻擊實際被哪一層攔下（**不是**「全部被拒」而已） | `harness/ablation.py <上面兩個檔案>` |
| `review_verification.json` | 10 條核心主張的凍結＋簽章＋guard＋漂移偵測 | `harness/ampas_review.py verify` |
| `review_verification_mathlib.json` | Mathlib 主張（PRIMES）同上 | 同上，加 `AMPAS_CLAIMS` |
| `baseline_fresh_replay.json` | `leanchecker --fresh`：把 Init 全部重放進空核心（一次性基準，約 3 分鐘） | `harness/ampas_lean.py` 的 `baseline()` |
| `sample_reports.json` | 幾份提交的完整判定輸出範例 | 驅動程式輸出 |
| `positivity_differential.json` | 正性 pass 跑過受信任參考環境與 Mathlib 環境裡的每一個歸納型 | `harness/spec_diff.py`（見下） |
| `recursor_differential.json` | 遞子形狀 pass 跑過同樣這兩個環境裡的每一個遞子 | 同上，`--pass recursor` |
| `corpus_results.json` | 第一輪紀錄（單一核心） | 歷史 |
| `corpus_results_twokernels.json` | 第二輪紀錄（兩套核心，無第三道檢查） | 歷史 |
| `corpus_results_mathlib.json` | 第二輪的 Mathlib 紀錄 | 歷史 |

歷史檔案保留是為了可比對：第二輪與第三輪的差異應該只有第三道檢查的欄位，判定本身不該變。

## counterexample_search*.json — 有界反例搜尋

`build/counterexample_search.json`（核心）、`..._mathlib.json`、`..._fermat.json`，
重現已登錄的 `reference/counterexample_search*.json`。

    export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
    python3 harness/counterexample.py --out build/counterexample_search.json

各欄位的意思、以及「乾淨結果」到底能代表什麼，見 ASSUMPTIONS A1b。先看的數字
是 `checked_points` 對 `box_size`：前提不成立的點對結論毫無發言權，判定不出來的
點也一樣，所以真正檢查到陳述的只有剩下那些。驗證案例是 FERMAT-CLAIM，它必須回
報 REFUTED、witness 為 `[5]`。

## derivation_search.json — 有界推導搜尋

`build/derivation_search.json`，重現 `reference/derivation_search.json`，
產生的見證檔在 `build/refutations/`。

    export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
    python3 harness/derivation_search.py --out build/derivation_search.json

針對數值搜尋碰不到的那四條獨立性主張。PL-BOGUS 必須回報 REFUTED，而要看的欄位
在 `kernel` 底下：`kernel_replay` 與 `kernel_replay_fresh`（elaborate 過不等於
核心檢查過），以及 `statement_check.negates_frozen_statement_structurally`——
沒有這一項，一份「反駁」可能反駁的是跟凍結陳述相鄰的另一條陳述，那就是
`FermatWeaker` 的失效模式反過來用。`axioms: []` 表示這份反駁什麼公理都沒用到。

另外三條，先讀 `bound` 再讀 `outcome`：NO_DERIVATION 的意思是「在那個範圍內沒找
到」，僅此而已。完整說明見 ASSUMPTIONS A1c。

## positivity_differential.json、recursor_differential.json

`harness/kernel3` 三個假設性質裡已檢查的兩個，各自一道 pass，各自做過差分測試。

    export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
    LEAN_PATH=$AMPAS_TRUSTED_OLEAN lean --run harness/Export.lean \
        --specs AmpasRef.Guards build/guards.specs
    python3 harness/spec_diff.py --pass positivity build/positivity_core.json \
        AmpasRef.Guards=build/guards.specs
    python3 harness/spec_diff.py --pass recursor build/recursor_core.json \
        AmpasRef.Guards=build/guards.specs

`scripts/verify.sh` 在 tier 1 跑這兩段，tier 3 再加上 Mathlib 那一組——committed
的那兩份紀錄就是 tier 3 產生的。

`harness/kernel3/positivity.py` 判斷歸納型規格是否嚴格正性；
`harness/kernel3/recursor.py` 判斷產生的遞子形狀——各項元數、被消去的那個家族成員
每個建構子恰好一條 iota 規則、`k` flag，以及消去宇宙：`Prop` 的大消去只在它是
subsingleton 時才允許。**先讀這個不對稱，再讀數字：**

- 在這些集合上出現 **VIOLATION**，那是**這道 pass 的 bug**，不是對 Lean 的發
  現——這些宣告在模組編譯時全部被 Lean 自己的核心接受過。腳本遇到就以非零結束。
- **UNCLASSIFIED** 是這道 pass 拒絕下判斷，那是錯誤被允許走的方向。每一筆都連
  同理由記下來，所以它變多的時候看得見，而不是默默變多。
- **OK** 的意思是：在這道 pass 有意見的地方，它與 Lean 一致。它**不**表示那份
  規格被檢查過了。

紀錄本身：**3285 個歸納型、0 個違反、45 個 unclassified**——這 45 個全是同一種形
狀，即遞迴出現被放在另一個歸納型的參數底下（多半是 `Array`），要判它得先算那個
歸納型自己的正性。以及**3410 個遞子、0 個違反、263 個 unclassified**，分在兩個指
名的成因底下：欄位型別需要一個 `--specs` 匯出不帶的定義（80 個，因為那份匯出只有
assumed 宣告），以及嵌套歸納型在包裹型別上額外產生的輔助遞子（183 個）。

`unclassified_by_cause` 必須把每一筆拒判都算進某個指名成因，`other` 必須是 0。
新的成因躲在「其他」裡，正是這些 pass 會悄悄停止覆蓋某些東西的方式。

**乾淨的結果買不到什麼。** 這兩道 pass 抓到的是不同的偽造，而且誰也不涵蓋誰：
`forge_positivity.export` 的遞子是合法的，所以它通過遞子 pass；
`forge_large_elim.export` 的歸納型是合法的，所以它通過正性 pass。而第三個性質——
每條 iota 規則實際算出什麼——這裡沒有任何東西檢查。所以同時通過這兩道 pass 的宣
告仍然不是「被檢查過的規格」；擋下偽造的是來源查核，而這兩道 pass 都沒有放寬它。
見 ASSUMPTIONS A3 與 ROADMAP 2。

**做這一輪得到的一個發現**，因為它正是差分測試是必要條件而不是形式的理由：遞子
pass 第一版的規則檢查假設了「互遞歸家族的遞子帶有整個家族每個建構子的 iota 規
則」。十九個 Mathlib 遞子回報 VIOLATION，而它們全都是合法的——互遞歸遞子帶的是它
所消去的那個成員的規則。現在這道 pass 從遞子的結論讀出那個成員。一條在「拒絕」方
向錯掉的規則，同樣可能在「接受」方向錯掉。
