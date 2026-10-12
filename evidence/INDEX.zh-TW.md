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
| `corpus_results.json` | 第一輪紀錄（單一核心） | 歷史 |
| `corpus_results_twokernels.json` | 第二輪紀錄（兩套核心，無第三道檢查） | 歷史 |
| `corpus_results_mathlib.json` | 第二輪的 Mathlib 紀錄 | 歷史 |

歷史檔案保留是為了可比對：第二輪與第三輪的差異應該只有第三道檢查的欄位，判定本身不該變。
