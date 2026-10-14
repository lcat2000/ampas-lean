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

## 2026-10-14：三道規格 pass 之後

`harness/kernel3` 對一個 inductive 宣告假設三件事。三件現在都有一道獨立的 pass：
`positivity.py`、`recursor.py`、`iota.py`。上面那兩份偽造各自被該管它的那道 pass
從**它的規格上**抓到，而且各自**通過**另外兩道——`forge_positivity` 的遞子與規則
是合法的，`forge_large_elim` 的歸納型與規則是合法的。這個分離是刻意測出來的：一道
被「簡化」成跟著別人拒絕的 pass，看起來同樣像在抓東西。

### iota 規則的那一對（Lean 產生，不是手寫）

`iota.py` 需要的向量和上面三份不同，而且**必須由 Lean 產生**：要示範的是「一條被
動過的規則在乾淨的匯出裡看不見」，所以基底得先是乾淨的。`control_small_elim`
本身是「應該被拒絕」的那一份，從它衍生示範不出這件事。

| 檔案 | 內容 | 第三道檢查 | iota pass |
| --- | --- | --- | --- |
| `control_iota.export` | Lean 產生：`Two`（兩個建構子）+ `pick a b t = Two.rec a b t` | `8/8 checked, 0 errors` | 乾淨 |
| `forge_iota.export` | 同上，只把 `Two.rec` 兩條 iota 規則的右手邊**對調** | `8/8 checked, 0 errors` | **VIOLATION** |
| `control_iota_exercised.export` | 多一條 `pick_fst : pick a b Two.fst = a := rfl` | `12/12 checked, 0 errors` | 乾淨 |
| `forge_iota_exercised.export` | 同上，規則對調 | **拒絕** `pick_fst`（value does not have the declared type） | **VIOLATION** |

兩對檔案各差**一行**（`#REC` 那一行），`diff` 看得到。

* 第一對是**那個洞**：規則被動過，但匯出裡沒有任何項用到它的歸約，所以型別檢查看
  不見差別——兩份都是 `0 errors`，只有 iota pass 分得出來。
* 第二對是**後果**：一旦有項用到，核心證得出的東西就變了。`pick a b Two.fst = a`
  對 `pick` 的宣告而言是真的，而且只因為 `Two.fst` 的規則回傳第一個 minor 才能用
  `rfl` 證；規則對調之後這條真命題證不出來，而對調的對稱性表示 `rfl` 反而證得出
  `pick a b Two.fst = b`——那條對 `pick` 的宣告而言是假的。

**和前兩份偽造不同，這一對都沒有證出 `False`，而且做不到。** minor premise 的型別
是由遞子的**型別**決定的，被偽造的歸約只影響結果那一側，所以要構造 `False` 時那條
難的 minor 仍然擋著。一條錯的 iota 規則給出的是一個**一致但算錯東西**的系統：它證
明的命題對「宣告所說的那個函數」而言是假的。那正是 ASSUMPTIONS A1 講的失效模式
——Lean 接受一個定理，表示其證明在**所使用的**定義下通過檢查——而不是系統不一致。
