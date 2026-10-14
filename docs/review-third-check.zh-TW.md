# 第三道檢查：Python 型別檢查器的逐行審查

## 來源與歸屬

這份程式碼（`terms.py`、`parse.py`、`check.py`，約 1,300 行，連同 `harness/Export.lean`）**不是**本輪作者撰寫的。它在 session 中出現在 `harness/`，當時被接到判定路徑上但未經任何審查，因此先被移出受信任路徑（見 `unreviewed/README.md`）。本文件是依要求所做的逐行審查結果。

- **原始實作：** 來源不明，非本輪作者。
- **審查、以下的發現、以及第 4 節的修正：** 本輪作者。
- `unreviewed/kernel/` 保留未修改的原件以供比對。

## 它做對的事

審查過程中值得記錄的是：項層（term layer）的實作相當謹慎，有幾個最容易寫錯的地方是對的。

| 項目 | 評語 |
| --- | --- |
| K-like reduction (`_to_ctor_when_k`) | **正確**。它在把主前提替換成建構子之前，驗證該建構子應用的型別確實與主前提同型。少了這個檢查，只要存在一個等式證明就會讓任意兩項定義等價——程式碼裡還留了註解說明這點。 |
| 定義性證明無關 (`_proof_irrel`) | **正確**。檢查 `a` 的型別之型別是 `Sort 0`，再要求 `ta ≡ tb`，兩者皆具備才成立。 |
| `level_leq` | 標準演算法（剝 succ、分配 max、對 imax 的參數分裂成 0 與 succ）。不完備之處一律回傳 False，**錯在拒絕而非接受**，對檢查器是安全方向。 |
| `Nat` 字面值運算 | `n/0 = 0`、`n%0 = n`、截斷減法都與 Lean 一致。 |
| `Quot.lift` / `Quot.ind` 參數位置 | 與實際簽章相符（5／3 與 4／3）。 |
| `infer` 遇到游離 de Bruijn 變數 | **拋錯**，而非默默代換——這是 fail-closed，也正好補住下面 F-3 的風險。 |
| 投影型別推導 (`_infer_proj`) | 先要求值的型別頭部就是所指的結構，再逐欄位以投影取代前面的欄位。正確。 |

它也確實抓得到東西，不是空轉：A01 核心旁路被獨立抓出（`declared False, inferred True`），把匯出檔的定理型別打亂後抓出 24 筆錯誤。

## 發現

### F-1（嚴重，已修）：statement 模式的匯出會回報「全部檢查通過」

`Export.lean` 在 `--statement` 模式下把定理輸出為 `#THMTYPE`（只有型別、沒有證明）。`check_decl` 對 `thmtype` **沒有任何分支**：只驗證型別是個型別，然後把它計入 `checked`。`env.mode` 雖然被解析，但**全程沒有任何地方檢查它**。

實測：對 statement 模式的匯出，原始程式回報 `checked 27/27, errors 0`，而其中唯一的定理是未經證明的假設。呼叫端若把這個結果當成「已獨立驗證」，就被誤導了。管線當時碰巧以 proof 模式呼叫，但沒有任何機制保證或驗證這一點。

### F-2（嚴重，無法以合理成本修補；已改為界定範圍）：inductive 規格完全被假設

程式自述假設 inductive 宣告合法。逐行確認後，實際被檢查與未被檢查的範圍是：

| 宣告 | 有檢查 | **沒有**檢查 |
| --- | --- | --- |
| `ind` | 型別是合法型別 | 嚴格正性（strict positivity）、建構子的宇宙上界 |
| `ctor` | 型別合法；剝掉 `nparams+nfields` 個 Pi 後頭部確實是該 inductive | 欄位中該 inductive 只出現在嚴格正位置 |
| `rec` | 每條規則的建構子存在、欄位數相符、rhs 封閉且**型別正確** | 遞子型別是否就是該 inductive 應產生的那個、**Prop 的大消去限制**、規則 rhs 是否真的是 iota 該給的結果 |

**這正是經典不健全性的所在。** 我寫了兩個偽造匯出檔實測（`tests/forgeries/`）：

1. **Prop 大消去**：`P : Prop` 兩個建構子，偽造一個消去到 `Sort u` 的遞子。證明無關使 `P.a ≡ P.b`，於是 `P.rec m X Y t ≡ P.rec m X Y u`（經 `_def_eq_app` 逐引數比較＋證明無關），`MyTrue` 與 `MyFalse` 作為型別可互換。結果：**`checked 9/9, errors 0`，`False` 被證出**。
2. **非正性 inductive**：`Bad.mk : (Bad → MyFalse) → Bad` 加對應遞子，標準對角線論證。結果：**`checked 7/7, errors 0`，`False` 被證出**。

對照組確認這兩個洞確實位於被假設的區域、而非一般性的崩壞：把同一個遞子改成只消去到 `Prop`（小消去），檢查器正確拒絕（`expected P → Sort 0, got P → Sort 1`）。

要真正補上這個洞，需要自行推導 inductive 應產生的遞子型別與規則，並實作正性檢查——那大致是 Lean 的 `inductive.cpp` 的工作量。更重要的是：**在寬鬆方向寫錯這個檢查，比明確宣告「這部分是假設」更糟**。所以我沒有嘗試實作它，改為界定範圍（見第 4 節）。

### F-3（低，目前不可觸發）：`instantiate` 不提升被代入項的游離索引

`terms.py` 的 `instantiate` 直接放入 `vals[i]`，不依穿越的 binder 數提升其游離 de Bruijn 索引。只有在被代入項本身 bvar-封閉時才正確。實際上整個檢查器用 locally-nameless 風格（區域變數都是 `fvar`），且 `infer` 遇到游離 bvar 就拋錯，所以目前的呼叫路徑都滿足這個前提。但這是個**隱含、未被斷言的不變式**，改動時容易破壞。建議（未實作）：在 `instantiate` 入口加一道 assert。

### F-4（低）：`_reduce_proj` 不核對投影所指的結構

`proj Foo i (Bar.mk ...)` 會歸約為 `Bar.mk` 的第 i 個欄位，即使 `Foo ≠ Bar`。`_infer_proj` 有核對（值的型別頭部必須是 `Foo`），所以型別正確的項不受影響；但 whnf 可能在型別推導完成前就被呼叫。目前無法構成可利用路徑，記錄備查。

### F-6（中，不修；已改為界定與裁定）：iota 缺少 to-constructor-when-structure，對程式庫等級的程式碼不完備

這一項不是讀程式碼讀出來的，是**把它接上 Mathlib 之後跑出來的**。它拒絕了 3 個宣告，而兩套 Lean 核心都接受：

```
Prod.instLawfulBEq
Nat.Internal.Linear.Poly.denote_reverse
Nat.Internal.Linear.ExprCnstr.denote_toNormPoly
```

三個都是 **Lean core 的程式庫宣告**，不是提交的程式碼：把它們單獨從參考環境匯出、完全不涉及任何提交，一樣是這 3 筆失敗（520/523 通過）。

機制已定位到具體一步。以 `Prod.instLawfulBEq` 為例，需要證明

```
BEq.beq (α × β) (instBEqProd α β instA instB) p q  ≡  (p.1 == q.1) && (p.2 == q.2)
```

展開 instance 後右側是對 pair 的 match，編譯成 `Prod.rec`，而其主前提是中性項 `p`。**Lean 的核心會把結構型別的中性項 eta 展開成建構子應用**（`p` ⟶ `Prod.mk p.1 p.2`），iota 便可觸發；`check.py` 的 `_reduce_rec` 只做 `_nat_to_ctor` 與 `_to_ctor_when_k`（後者要求建構子無欄位），所以 `Prod.rec … p` 卡住，兩邊都是中性項，比較失敗。

**方向是不完備，不是不健全**：它是「歸約不出來所以拒絕」，不可能讓它接受假的東西。

**為什麼不修**：往一個正在審查的檢查器裡加歸約規則，是在**放寬**它接受的範圍——正是出錯會變成不健全的方向。與 F-2 同一個原則。改成：把這 3 筆逐筆裁定並記錄（`reference/third_check_adjudications.json`，含裁定者、日期、機制與重現方式），同時**改掉閘門**（見第 5 節）。

**這一項同時推翻了我原本的閘門設計。** 原本「第三道檢查報錯 → 認證失敗」在核心語料上看起來沒問題（16/16 都對），但一接上 Mathlib 就讓一條**兩套 Lean 核心都通過**的正確證明（PRIMES）被否決。讓三者中最不完備的那一個否決另兩個，是錯的。

### F-5（低，可用性）：`Nat.pow` 未設上限

`a ** b` 直接計算，匯出檔中的巨大指數可使檢查器耗盡記憶體。是阻斷服務問題，不是健全性問題；沙箱的記憶體與時間上限已涵蓋。

## 4. 本次所做的修正

不試圖補 F-2 的洞，而是讓這個檢查器**只為它真正檢查過的東西背書**。

1. **拒絕 statement 模式**（修 F-1）。`check_env` 現在對 `mode != "proof"` 直接回報錯誤，並把所有 `#THMTYPE` 宣告列為 `unproved_theorems` 錯誤。`thmtype` 不再計入 `checked`。
2. **來源界定（provenance gate）**。新增 `decl_fingerprint(d)`：對 inductive／建構子／遞子／quot，把其型別與所有規格欄位（含遞子的每條規則的 rhs）做結構化序列化。`check_env(..., baseline=...)` 把匯出檔中每個被假設的宣告分成兩類：
   - 指紋與受信任基準相符 → `baseline_assumptions`（受信任核心本來就承擔的假設）；
   - 其餘 → `introduced_assumptions`，**明確回報為「本檢查器未涵蓋」**。

   指紋涵蓋型別與整個規格（遞子連每條規則的 rhs 都算進去），所以偽造的遞子無法冒充基準中的同名宣告。

3. **基準的正確定義**（第一版做錯，實測才發現）。基準必須是**受信任核心的全部被假設宣告**，而不只是從參考陳述可達的那些。第一版用參考陳述的 closure（213 個），結果三份**正確**的提交被報出 `Subtype`、`Ordering`、`Ord`、`Std.TransCmp`、以及 `Ampas.PL.Derives.rec` 等「未涵蓋」——那些都是 Init 與受信任參考本來就有的合法宣告，只是陳述本身沒用到（陳述提到 `Derives`，但不提到 `Derives.rec`）。

   方向上是安全的（它多報而非少報），但實質上是錯的：噪音會把真正的新增假設淹掉。修正方式是給 `Export.lean` 加 `--specs` 模式——走整個環境（匯入模組在 `map₁`、本模組在 `map₂`），只輸出 ind／ctor／rec／quot 的宣告行、不做依賴 closure（算指紋只需要宣告自己的型別與規則）——並以 `harness/make_baseline.py` 固定重現：

   | 基準 | 來源模組 | 被假設的宣告 |
   | --- | --- | --- |
   | `reference/kernel_baseline.json` | `AmpasRef.Guards` + `AmpasRef.Challenge`（含 Init） | 2,157 |
   | `reference/kernel_baseline_mathlib.json` | `AmpasRef.ChallengeMathlib`（含 Mathlib 依賴錐） | 9,638 |

   基準檔存的是**指紋的 SHA-256**（`fingerprint_id`），不是指紋本身：閘門只需要集合成員判定，而完整序列化的型別對 Mathlib 依賴錐來說是 12 MB。

修正後實測：

| 情境 | 結果 |
| --- | --- |
| 真正的證明 | `errors=0, introduced=0, baseline=24` → **CONFIRMED** |
| A01 核心旁路 | `errors=1` → CORROBORATION（Lean 核心也拒絕了同一個宣告） |
| 偽造大消去 | `errors=0` 但 `introduced=7`（`P`, `P.a`, `P.b`, `P.rec`, …）→ **NOT CONFIRMED** |
| 偽造非正性 inductive | `errors=0` 但 `introduced=4`（`Bad`, `Bad.mk`, `Bad.rec`, …）→ **NOT CONFIRMED** |
| statement 模式 | 直接拒絕 |

這**沒有**讓它能驗證 inductive 規格；而是讓它拒絕為自己無法驗證的東西背書。偽造路徑不再可能產出乾淨的結論。

## 5. 判定：可作為第三道檢查，但範圍須在程式中強制

**可以。** 條件是：

1. **它的乾淨結論只代表**：每個宣告的型別都重新檢查過，且所有被依賴的 inductive 規格都與受信任基準逐欄位相符。這句話就是 `covers` 欄位的內容，會進入證據紀錄。
2. **它絕不可作為唯一或決定性的核心證據。** inductive 層它是三者中最弱的——Lean 自己的核心與 lean4lean 都檢查 inductive，它不檢查。
3. **閘門設定（F-6 之後改過）：** 認證建立在兩套 Lean 核心加稽核器上；第三道檢查是**佐證**，不是否決權。
   - 它沒報錯 → `CONFIRMED`，記入該主張的 `corroboration`。
   - 它報錯，而該宣告**未經裁定** → `DISAGREEMENT (unadjudicated)`，**阻擋認證**。這一點保留了它的價值：它拒絕了預期之外的東西時，先停下來讓人看。
   - 它報錯，而該宣告已有裁定紀錄（裁定者、日期、機制、重現方式） → 不阻擋認證，但狀態與裁定都記入證據。
   - 它回報 `introduced_assumptions` → 不阻擋認證（那一層由另兩套核心涵蓋），但該筆限制會記入證據。
4. 管線中這個洞實際上**不可觸達**：匯出檔來自提交者編譯後的 olean，而提交者只能給 `.lean` 原始碼，偽造的 inductive 或遞子過不了 Lean 自己的 elaborator／核心。換句話說，F-2 的假設在管線裡是由**主核心**解除的，不是由「沒有人」解除的。但若把這個檢查器用於來源不明的 olean（獨立核心最有價值的場景），這個洞就是活的。

**它真正加入的價值：** 對項層的一個獨立意見——不同語言、不同作者、不共用 Lean 的 elaborator。它在 A01 核心旁路上反對了同一個被 Lean 核心拒絕的宣告——那是**佐證**，不是抓到 Lean 核心漏掉的東西（這一點到 2026-10-14 之前被套件誤記為「分歧」）。它**沒有**加入的，是對 inductive 層的獨立意見；而依 F-6，它對程式庫等級的程式碼也不是完備的。

## 6. 一句話總結

它值得當第三道檢查，但只能當**第三**道：
- 核心語料 16 份全部重檢、0 錯、0 筆未涵蓋的假設，並在 A01 上佐證了 Lean 核心；
- Mathlib 等級上有 3 筆已裁定的不完備（F-6），加上 inductive 規格層本來就不檢查（F-2）；
- 所以它**佐證**項層，不**建立**任何東西。任何只靠它成立的結論都是過度宣稱。
