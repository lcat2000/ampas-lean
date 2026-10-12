# 偽造匯出檔（第三道檢查的對抗性測試向量）

這三個檔案是**手寫的** Lean 匯出檔，用來實測 `harness/kernel3` 未檢查 inductive 規格
的後果（見 `harness/kernel3/REVIEW.md` 的 F-2）。它們**不是** Lean 產生的，也**不可能**
由 Lean 產生——這正是重點：偽造的遞子過不了 Lean 自己的核心。

| 檔案 | 內容 | 原始程式的結果 | 修正後 |
| --- | --- | --- | --- |
| `forge_large_elim.export` | `P : Prop` 兩個建構子 + 偽造消去到 `Sort u` 的遞子（Prop 大消去） | `9/9 checked, 0 errors`，`bad : MyFalse` 被接受 | `introduced_assumptions` 非空 → 不背書 |
| `forge_positivity.export` | `Bad.mk : (Bad → MyFalse) → Bad`（非正性）+ 對角線論證 | `7/7 checked, 0 errors`，`False` 被證出 | 同上 |
| `control_small_elim.export` | 對照組：同一個遞子只消去到 `Prop`（小消去，合法限制） | **正確拒絕**（`expected P → Sort 0, got P → Sort 1`） | 同樣拒絕 |

對照組的作用是證明這個洞確實位於**被假設的 inductive 規格**，而不是檢查器普遍崩壞：
型別層的限制它抓得到，規格層的偽造它抓不到。
