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
| `iota_differential.json` | 每個遞子的 iota 規則，從建構子與遞子重新導出後比對 | 同上，`--pass iota` |
| `history_validation.json` | 另外三段數學史：6 條主張、11 份送審（ROADMAP 6a） | `harness/ampas_lean.py corpus/manifest_history.json` 配 `reference/claims_history.json` |
| `ablation_external.json` | **兩組**外部語料裡每個攻擊被哪一層抓到——共 12 個攻擊 | `harness/ablation.py` 跑過那兩份外部結果檔 |
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

## positivity_differential.json、recursor_differential.json、iota_differential.json

`harness/kernel3` 的三個假設性質，各自一道 pass，各自做過差分測試。

    export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
    LEAN_PATH=$AMPAS_TRUSTED_OLEAN lean --run harness/Export.lean \
        --specs AmpasRef.Guards build/guards.specs
    python3 harness/spec_diff.py --pass positivity build/positivity_core.json \
        AmpasRef.Guards=build/guards.specs
    python3 harness/spec_diff.py --pass recursor build/recursor_core.json \
        AmpasRef.Guards=build/guards.specs
    python3 harness/spec_diff.py --pass iota build/iota_core.json \
        AmpasRef.Guards=build/guards.specs

`scripts/verify.sh` 在 tier 1 跑這三段，tier 3 再加上 Mathlib 那一組——committed
的那三份紀錄就是 tier 3 產生的。

`harness/kernel3/positivity.py` 判斷歸納型規格是否嚴格正性；
`harness/kernel3/recursor.py` 判斷產生的遞子形狀——各項元數、被消去的那個家族成員
每個建構子恰好一條 iota 規則、`k` flag，以及消去宇宙：`Prop` 的大消去只在它是
subsingleton 時才允許；`harness/kernel3/iota.py` 把每條 iota 規則的右手邊從建構子
與遞子**重新導出**再比對，所以那裡的 `OK` 意思是「存的那條規則就是導出來的那
條」。**先讀這個不對稱，再讀數字：**

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

再加上 iota 那一份：**3410 個遞子、0 個違反、183 個 unclassified**，這 183 個全是
嵌套歸納型的輔助遞子——也就是 3227 個遞子的規則可以被精確重新導出。

**乾淨的結果買不到什麼。** 這三道 pass 抓到的是不同的偽造，而且誰也不涵蓋誰：四份
偽造向量各自只失敗一道、通過另外兩道。但三道查的都是「宣告是否符合 Lean 會遵守的
規則」——沒有一道能證明**那份匯出真的來自 Lean**。一份規格可以同時滿足三道，卻仍
然不是 Lean 會產生的東西，所以擋下偽造的仍然是來源查核，三道 pass 都沒有放寬它。
假設是**移位**了，從「宣告的形狀」移到「匯出的來源」，而那是比「規格層已被檢查」
更窄的一句話。見 ASSUMPTIONS A3 與 ROADMAP 2。

**做這幾輪得到的四個發現**，因為它們正是差分測試是必要條件而不是形式的理由。每一
個都是 pass 自己的 bug，而且沒有一個能從它自己的單元測試看出來：

* 遞子 pass 假設了「互遞歸家族的遞子帶有整個家族每個建構子的 iota 規則」。十九個
  Mathlib 遞子回報 VIOLATION，全都是合法的——互遞歸遞子帶的是它所消去的那個成員
  的規則；
* iota pass 用了規則主體的 binder 深度去處理欄位自己的 binder 型別（627 個核心遞
  子裡有 491 個被讀成偽造）；
* 它沒有進到 `let` 裡面，而 Lean 自己有六個結構的某個欄位型別是以 `let` 開頭的；
* 它把遞迴呼叫的 callee 寫死成「自己」，這對 Lean Init 裡全部 137 個遞迴呼叫都是
  對的（那個集合裡沒有互遞歸歸納型），對 Mathlib 裡的 25 個是錯的。**只跑核心那一
  組的差分測試會讓這個錯誤出廠**——這就是為什麼兩個環境都是必要的。

一條在「拒絕」方向錯掉的規則，同樣可能在「接受」方向錯掉。

## history_validation.json、ablation_external.json — 史實語料

    export AMPAS_CLAIMS=$PWD/reference/claims_history.json
    export AMPAS_KERNEL_BASELINE=$PWD/build/kernel_baseline_history.json
    python3 harness/ampas_lean.py corpus/manifest_history.json \
        --out build/history_validation.json
    python3 scripts/check_expectations.py build/history_validation.json
    python3 harness/ablation.py build/fermat_validation.json \
        build/history_validation.json --out build/ablation_external.json

`scripts/verify.sh` 在 tier 3 跑這兩段。三段史實，每段是一條歷史上**錯**的主張配
上當年定案推翻它的那條**真**陳述：Mersenne 1644 清單的 p = 67 對 Cole 1903 的因數
分解、Euler 1769 sum-of-powers 猜想的 n = 5 對 Lander 與 Parkin 1966 的反例、以及
Euler 1772 多項式的全稱過度解讀對它在 n = 40 的失敗。完整經過見 ROADMAP 6a。

**一條史實主張買到什麼、買不到什麼。** 它固定下**答案**：`2^67 - 1` 是不是質數不
是這個倉庫說了算，而那正是自己寫的語料無法自己修掉的那個弱點。它**沒有**固定下
**形式化**。每條 Lean 陳述是否真的在說那句歷史句子所說的事，仍然是人的判斷，而
`reference/claims_history.json` 裡每個 `review` 區塊的 `reviewed_by` 與
`confirmed_by` 都是 `PENDING`，因為沒有人做過那個判斷。把「Mersenne 1644 清單」縮
到它的 p = 67 那一項、把 Euler 的一般猜想縮到 n = 5 那一例，是最該先讀的兩步。

**讀 `ablation_external.json` 的時候要知道它補的是什麼缺口。** `harness/ablation.py`
以前用 `A` 開頭的檔名前綴認定哪些是攻擊——那只是核心語料剛好這樣命名。外部送審是
用數學家的名字命名的，所以**所有外部攻擊——Fermat 那四個從它加進來那天起，加上史
實那八個——全部不在層歸因表裡**，而那張表還對「語料是寫管線的人自己寫的」這個問題
回報「0 attacks, all rejected: True」。現在攻擊是從每份紀錄自己的 `expected` 欄位
讀出來的。同一類錯誤換個地方，就是 `reference/claims_history.json` 一開始把欄位寫
成 `target_claim_is` 而程式讀的是 `target_claim_is_true`：對人是對的，對程式不存在。

## counterexample_search_history.json — 搜尋在「不是我們挑的」主張上

    AMPAS_CLAIMS=$PWD/reference/claims_history.json \
      python3 harness/counterexample.py --out build/counterexample_search_history.json

這一輪最有資訊量的一份檔，因為六個結果裡有兩個講的是**搜尋本身**，不是那些主張：

| 主張 | 結果 | 意思 |
| --- | --- | --- |
| `EULER-POLY` | **REFUTED**，見證 n = 40 | 反例落在盒子裡，搜尋自己找到它 |
| `MERSENNE-67` | **REFUTED** | 盒子只有一個點，而 `Nat.Prime` 的判定程序用試除在幾分鐘內找出因數 193707721——所以搜尋自己重現了 Cole 1903 年的結果。`reference/counterexample_bounds.json` 原本寫它做不到；那句話已就地改正，並把改正本身記下來 |
| `EULER-SUM-5` | NO_COUNTEREXAMPLE | **這條主張是假的。** Lander 與 Parkin 的見證需要五個變數都到 144，約 6.2e10 個點，所以這個搜尋負擔得起的任何盒子都碰不到它。這是搜尋層的一個**已記錄的極限**，而且是在一條不是這個倉庫挑的主張上 |
| `LANDER-PARKIN` | NO_COUNTEREXAMPLE_PARTIAL | 五個變數的純存在陳述；搜尋也無法確認它。見證來自送審，由核心檢查 |
| `COLE-67`、`EULER-POLY-40` | NO_COUNTEREXAMPLE | 單點盒子、沒找到東西，真陳述本來就該是這樣 |

一條被紀錄為假的主張必須有東西背書——這個搜尋、推導搜尋，或是一句說明為什麼兩者
都做不到。EULER-SUM-5 三者皆無，而它確實被推翻了，就在這個倉庫裡，由 LANDER-PARKIN
推翻。`harness/counterexample.py` 現在認得這第三種情況，而且是**重算**出來的，不是
接受一句話：`control.refuted_by` 必須指向同一份目錄裡一條本身不被宣告為假、而且在
某次執行紀錄裡確實被認證的主張。它預設失敗；當手上沒有執行紀錄時，欄位會寫明這次
背書是結構性檢查過的，不是靠執行驗證的。
