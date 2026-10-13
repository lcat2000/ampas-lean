# 形式化忠實度審查工作表

這份是給**審查者**用的，不是說明文件。目的是讓你不用在檔案之間翻找，就能回答每條主張的那一個問題。

- 每條主張附：自然語言 `text`、**Lean elaborate 之後**的陳述（這才是被凍結與雜湊的東西）、忠實度真正依賴的定義原始碼、機器算出型別的 guard，以及一個你要回答的具體問題。
- 判定只有兩種：**接受**（這條陳述忠實呈現了那句話）或**不接受**（附理由）。
- **不必全做。** 紀錄是逐條的，你可以只升級其中幾條，其餘維持 `delegated`。

準備工作：無。這份可以在瀏覽器裡讀完。只有在你決定要簽的時候才需要裝 Lean。

> **誰寫的這份：** 我（寫這套管線的同一個助理）。所以這份工作表本身也不是獨立的——它整理材料、提出問題，但**不應該代替你看定義**。每一節的「要回答的問題」都是我認為的關鍵點；如果你覺得關鍵點不在那裡，那個不同意見比我的整理更有價值。

---

## A 組：六條算術（約 10 分鐘）

這組的忠實度風險只有一種：**Lean 的慣例陷阱**。全部不依賴任何自訂定義（closure 裡 0 個 AMPAS 常數），所以沒有「定義被偷換」的空間。

| 主張 | text | elaborate 後的陳述 |
| --- | --- | --- |
| ADD | Addition of natural numbers is commutative. | `∀ (a b : Nat), a + b = b + a` |
| SUB | For natural numbers a and b with b ≤ a, (a − b) + b = a. | `∀ (a b : Nat), b ≤ a → a - b + b = a` |
| EVEN | The sum of two even natural numbers is even. | `∀ (a b : Nat), IsEven a → IsEven b → IsEven (a + b)` |
| DVD | Divisibility of natural numbers is transitive. | `∀ (a b c : Nat), a ∣ b → b ∣ c → a ∣ c` |
| GREATER | Every natural number has a strictly greater natural number. | `∀ (n : Nat), ∃ m, n < m` |
| DIV | For every positive natural number n, n / n = 1. | `∀ (n : Nat), 0 < n → n / n = 1` |

**機器算出的 guard（型別由稽核器從陳述本身推導，不是人填的）：**

```
Guards.sub_witness   : ∃ a b, b ≤ a                      -- 假設可同時成立
Guards.sub_necessity : ¬∀ (a b : Nat), a - b + b = a     -- 拿掉假設就是假的
Guards.div_witness   : ∃ n, 0 < n
Guards.div_necessity : ¬∀ (n : Nat), n / n = 1
Guards.even_witness  : ∃ a b, IsEven a ∧ IsEven b
Guards.dvd_witness   : ∃ a b c, a ∣ b ∧ b ∣ c
```

EVEN 用到的唯一定義：

```lean
def Ampas.IsEven : Nat → Prop := fun n => ∃ k, n = 2 * k
```

**要回答的問題（A 組共一題）：**

> SUB 的 `b ≤ a` 和 DIV 的 `0 < n` 這兩個假設，是**真的必要**，還是在把命題弄弱？
>
> 判斷依據：Lean 的 `Nat` 減法截斷（`0 - 1 = 0`，所以 `0 - 1 + 1 = 1 ≠ 0`），而 `n / 0 = 0`（所以 `0 / 0 = 0 ≠ 1`）。兩條 `necessity` guard 正是這兩個事實，而且是**核心檢查過**的。
>
> 附帶確認：`IsEven` 的 `∃ k, n = 2 * k` 是不是你要的「偶數」？（注意它讓 0 是偶數）

A 組判定：□ 接受　□ 不接受（理由：＿＿＿）

---

## B 組：三條獨立性（約 30 分鐘，**這組是重點**）

這組的忠實度**完全活在定義裡**。陳述本身短得看不出問題——`PL.Independent PL.T_imp (PL.Fm.var 1)` 這行，忠不忠實取決於 `Derives` 到底是什麼系統。這也是為什麼它們的 closure 各有 13–30 個 AMPAS 常數，而 A 組是 0 個。

### 共用的演算系統定義（`reference/AmpasRef/Defs.lean`）

```lean
/-- 公式：命題變數 var i，加上 → 與 ¬ -/
inductive Fm where
  | var : Nat → Fm
  | imp : Fm → Fm → Fm
  | neg : Fm → Fm

/-- Derives T φ：φ 可由假設集 T（以述詞表示）用公理模式 A1-A3 與 modus ponens 導出 -/
inductive Derives (T : Fm → Prop) : Fm → Prop where
  | hyp {φ : Fm} : T φ → Derives T φ
  | a1  {φ ψ : Fm} : Derives T (imp φ (imp ψ φ))
  | a2  {φ ψ χ : Fm} : Derives T (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | a3  {φ ψ : Fm} : Derives T (imp (imp (neg φ) (neg ψ)) (imp ψ φ))
  | mp  {φ ψ : Fm} : Derives T (imp φ ψ) → Derives T φ → Derives T ψ

/-- 同一個系統的正片段：A1、A2、modus ponens，沒有 A3 -/
inductive DerivesPos (T : Fm → Prop) : Fm → Prop where
  | hyp {φ : Fm} : T φ → DerivesPos T φ
  | a1  {φ ψ : Fm} : DerivesPos T (imp φ (imp ψ φ))
  | a2  {φ ψ χ : Fm} : DerivesPos T (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | mp  {φ ψ : Fm} : DerivesPos T (imp φ ψ) → DerivesPos T φ → DerivesPos T ψ
```

```lean
/-- 等式邏輯：項、以及由方程組 E 導出的等式 -/
inductive Term where
  | var : Nat → Term
  | one : Term
  | mul : Term → Term → Term

inductive Derives (E : Eqn → Prop) : Term → Term → Prop where
  | ax    {e : Eqn} (σ : Nat → Term) : E e → Derives E (e.lhs.subst σ) (e.rhs.subst σ)
  | refl  (t : Term) : Derives E t t
  | symm  {s t : Term} : Derives E s t → Derives E t s
  | trans {s t u : Term} : Derives E s t → Derives E t u → Derives E s u
  | congr {s s' t t' : Term} : Derives E s s' → Derives E t t' → Derives E (mul s t) (mul s' t')
```

### B1 — PL-IND

- **text：** 在古典命題邏輯（Hilbert 系統 A1–A3 ＋ modus ponens）中，理論 {p0 → p1} 既不證明也不否證 p1。
- **陳述：** `PL.Independent PL.T_imp (PL.Fm.var 1)`
- **展開後：**
  ```lean
  Independent T φ = ¬Derives T φ ∧ ¬Derives T φ.neg
  T_imp          = fun φ => φ = (Fm.var 0).imp (Fm.var 1)      -- 即 {p0 → p1}
  ```

> **要回答的問題：** `Derives` 的 a1／a2／a3 是不是古典命題邏輯的標準 Hilbert 公理（Łukasiewicz 那三條）？
>
> 這題是整組的關鍵：如果那三條**不是**完整的古典公理集（例如少一條、或某條寫弱了），那麼「{p0 → p1} 導不出 p1」就會變成一個**廉價**的結論——在一個太弱的系統裡什麼都導不出來，獨立性就不代表任何事。
>
> 對照標準寫法：A1 = `φ → (ψ → φ)`；A2 = `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`；A3 = `(¬φ → ¬ψ) → (ψ → φ)`。

B1 判定：□ 接受　□ 不接受（理由：＿＿＿）

### B2 — EL-IND

- **text：** 單群公理導不出交換律，且加入交換律不會讓理論變得不一致（x = y 仍然導不出來）。
- **陳述：** `EL.Independent EL.monoid EL.comm`
- **展開後：**
  ```lean
  Independent E e = ¬Derives E e.lhs e.rhs ∧ ¬Derives (fun f => E f ∨ f = e) x y
  monoid = (xy)z = x(yz)  ∨  1·x = x  ∨  x·1 = x
  comm   = xy = yx
  ```

> **要回答的問題（兩個）：**
>
> 1. `Derives` 那五條規則（ax／refl／symm／trans／congr）是不是等式邏輯的**完整**規則集？少任何一條，「導不出來」同樣變廉價。（提示：`one` 是常數，所以不需要自己的 congruence 規則；`ax` 帶替換 σ，所以那三條公理實際上是**模式**不是單一等式。）
> 2. 第二個合取項（加入 comm 後 `x = y` 仍導不出）有沒有真的排除掉「因為不一致所以獨立」？在等式邏輯裡，不一致的表現就是所有項都相等。

B2 判定：□ 接受　□ 不接受（理由：＿＿＿）

### B3 — PL-AXIOM-IND

- **text：** 在 `AmpasRef.Defs` 的 Hilbert 系統中，A3 對 p0、p1 的實例 `(¬p0 → ¬p1) → (p1 → p0)` 無法僅由 A1、A2 加 modus ponens 導出。由於可導出的模式會給出所有實例，這顯示 A3 是該演算的獨立公理。
- **陳述：** `¬PL.DerivesPos PL.Empty PL.a3_instance`
- **展開後：**
  ```lean
  Empty       = fun _ => False                                        -- 空理論
  a3_instance = ((var 0).neg.imp (var 1).neg).imp ((var 1).imp (var 0))
  ```
- **nontriviality guard（核心檢查過）：**
  ```
  Guards.pos_nontrivial : PL.DerivesPos PL.Empty ((PL.Fm.var 0).imp (PL.Fm.var 0))
  ```

> **要回答的問題（兩個）：**
>
> 1. `DerivesPos` 是不是真的就是「`Derives` 拿掉 A3」、其餘完全一樣？（把上面兩段 inductive 並排看）
> 2. **這題只有人能判斷**：這條主張是 `¬P` 形式，所以 witness／necessity guard 不適用，稽核器改要求 nontriviality guard。我選的是「A1+A2 片段仍能導出 `p0 → p0`」，用意是排除「這個演算根本證不出東西，所以什麼都獨立」。
>
>    **你同意這是該排除的退化讀法嗎？** guard 本身過核心檢查，但「選哪一條」是判斷，不是推導。

B3 判定：□ 接受　□ 不接受（理由：＿＿＿）

---

## C 組：其餘四條（約 10 分鐘）

### C1 — PRIMES（Mathlib）

- **text：** 存在任意大的質數：對每個 n 都有質數 p 使 n ≤ p（Euclid 定理）。
- **陳述：** `∀ (n : Nat), ∃ p, n ≤ p ∧ Nat.Prime p`
- 用的是 **Mathlib 的** `Nat.Prime`，所以 Mathlib 的定義進入這條主張的受信任集與凍結範圍（closure 345 個常數）。

> **要回答的問題：** 量詞順序 `∀n ∃p` 正確嗎？`n ≤ p`（而非 `n < p`）足以表達「任意大」嗎？Mathlib 的 `Nat.Prime` 是你要的質數概念嗎？

C1 判定：□ 接受　□ 不接受

### C2 — FERMAT-F5

- **text：** （Euler, 1732）第五個 Fermat 數 2^(2^5)+1 不是質數。（它等於 4294967297 = 641 × 6700417；因數分解是證據，陳述本身只斷言合成性。）
- **陳述：** `¬ Nat.Prime (2 ^ (2 ^ 5) + 1)`
- **nontriviality guard：** `Nat.Prime (2 ^ (2 ^ 3) + 1)` ——即 F3 = 257 是質數

> **要回答的問題：** 算術：$2^{32}+1 = 4294967297$，且 $641 \times 6700417 = 4294967297$。
> 以及同 B3 的那個人為判斷：用「F3 是質數」來排除「`Nat.Prime` 對所有 Fermat 數都不成立」這種退化讀法，你同意嗎？
> （F4 = 65537 會是更貼切的 guard——那是 Fermat 本人驗到的最後一個——但 `decide` 在核心上跑不完，因為可判定性實例會試每一個除數。）

C2 判定：□ 接受　□ 不接受

### C3／C4 — PL-BOGUS 與 FERMAT-CLAIM（刻意的假主張對照組）

- **PL-BOGUS：** `PL.Independent PL.T_imp ((PL.Fm.var 1).imp (PL.Fm.var 1))`
  text 明寫「這是假的，p1 → p1 是純邏輯定理，永遠不得被認證」。
- **FERMAT-CLAIM：** `∀ (n : Nat), Nat.Prime (2 ^ (2 ^ n) + 1)`
  text 明寫「Fermat 約 1640 年的斷言，是錯的，Euler 1732 年推翻」。

> **要回答的問題：** 這兩條的 `faithful: true` 意思是「這條 Lean 陳述忠實呈現了那句**假的**話」，不是「這句話是真的」。這個讀法你接受嗎？

C3／C4 判定：□ 接受　□ 不接受

---

## 完成後

把你的判定告訴我，我改 `reference/claims*.json`：接受的改成

```json
"confirmation_mode": "personally_reviewed",
"confirmation_basis": "<你怎麼審的，一兩句話>"
```

不接受的維持原狀或退回 `faithful: null`，由我依你的理由修正陳述或 guard。

然後**你**在自己機器上跑（私鑰不能離開你的機器，否則簽章一樣不歸屬任何人）：

```bash
python3 harness/ampas_review.py keygen \
  --private ~/.ampas/kai-ed25519.pem --public reference/reviewer_key.json \
  --key-id kai-chang-2026-10

export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
python3 harness/ampas_review.py freeze
python3 harness/ampas_review.py sign --key ~/.ampas/kai-ed25519.pem --key-id kai-chang-2026-10
python3 harness/ampas_review.py verify
```

`freeze` 一定要重跑：review 欄位是在凍結時寫進簽核紀錄的，`sign` 只簽現成的紀錄。

**部分完成是合理的結果。** 只升級 B 組三條、其餘維持 `delegated`，比全部一次點頭誠實得多——而且 B 組正是最可能出錯、也最需要第二雙眼睛的地方。
