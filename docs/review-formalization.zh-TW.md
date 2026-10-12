# 形式化忠實度的審查流程（Formalization Correctness）

Lean 核心能回答「這個證明在這些公理與定義下通過檢查嗎」，**不能**回答「這條 Lean 陳述是否忠實對應原始自然語言命題」。後者只能由人判斷。這份流程的目的不是把它自動化，而是讓這個判斷成為**可稽核的產物**：綁定到一個確切的數學對象、由機器檢查的保證支撐、可歸屬到一把金鑰，而且事後不能無聲漂移。

## 四個組成部分

### 1. 內容定址的凍結（不是原始碼文字）

每條參考陳述凍結兩個雜湊（`reference/attestations/<CLAIM>.json`）：

| 欄位 | 內容 | 為什麼 |
| --- | --- | --- |
| `statement_sha256` | **elaborated** 陳述的結構化序列化 | 重排版、改註解、改 binder 名稱都不影響；改變意義一定改變雜湊 |
| `closure_sha256` | 陳述遞移依賴的每個常數的序列化，**含定義本體** | 偷改 `IsEven` 的定義時，陳述文字可以完全不動——但這個雜湊會變 |

序列化由 `harness/Audit.lean`（`freeze` 模式）自己走過 `Expr` 的每個建構子產生，不依賴 pretty printer，也不依賴任何 Lean 版本的 `ToString`。定理的**證明不納入**凍結（proof irrelevance）：凍結的是陳述，不是某一個證法。

另外逐常數記 `closure_entries`，所以漂移偵測能指名是哪個常數變了。

### 2. 機器檢查的保證（guards）

人的判斷由兩類 Lean 定理支撐，它們本身和其他定理一樣過核心檢查（`reference/AmpasRef/Guards.lean`）：

- **非空洞性（non-vacuity）：** 假設可以同時成立，所以陳述不是空洞為真。
- **假設必要性（necessity）：** 拿掉**任一**假設，陳述就是**假的**。這擋掉「多加一個假設把命題悄悄弄弱」。

關鍵在於：這些 guard 的型別**不是**由人填寫，而是由稽核器從參考陳述本身算出來（`sanity` 模式），再用核心的定義等價比對。所以 guard 不可能是某個更弱命題的證明。例如 SUB：

```
expected_witness:    ∃ a b, b ≤ a
expected_necessity:  ¬∀ (a b : Nat), a - b + b = a
```

第二條正是 Lean 慣例陷阱的機器化：Nat 減法截斷，`0 - 1 + 1 = 1 ≠ 0`，所以 `b ≤ a` 這個假設**必須**在。DIV 同理（`0 / 0 = 0 ≠ 1`）。

目前有 guard 的主張：SUB、DIV、EVEN、DVD（共 6 條必要性、4 條非空洞性，全部 OK）。無假設的主張（ADD、GREATER、PL-IND、EL-IND、PL-BOGUS）記為 `NO_HYPOTHESES`。

### 3. 可歸屬的簽核

審查者對每條主張記錄：身分、日期、`faithful` 判斷、審查備註，以及檢查清單：

| 檢查項 | 問的是 |
| --- | --- |
| `statement_matches_text` | Lean 陳述說的就是文字說的 |
| `no_unintended_convention` | Nat 截斷、除以零、隱式轉換都看過 |
| `quantifier_order_checked` | 量詞順序正確 |
| `hypotheses_necessary_and_satisfiable` | 由上面的 guard 支撐 |
| `definitions_reviewed` | closure 裡每個定義都讀過 |
| `conclusion_not_weakened` | 結論沒有被弱化 |

整份紀錄以 **Ed25519 分離簽章**簽署（`reference/reviewer_key.json` 是公鑰；私鑰**不在**本包內）。簽章涵蓋除簽章本身以外的全部欄位，所以連 `text` 欄位被改都會失效。

### 4. 漂移偵測

`harness/ampas_review.py verify` 從**當下**的參考重新推導全部內容並比對，任何差異都失敗：

| 情境 | 偵測結果（實測） |
| --- | --- |
| 參考陳述被改（SUB 拿掉假設） | `STATEMENT DRIFT` |
| closure 裡的定義被改（`IsEven := True`，陳述文字不動） | `CLOSURE DRIFT — changed: Ampas.IsEven` |
| 簽核紀錄被竄改（prose 偷偷拿掉假設） | `SIGNATURE INVALID` |
| 簽核紀錄被刪除 | `no attestation (statement is not signed off)` |
| guard 不再成立 | `guards no longer satisfied` |
| 檢查清單未完成 / 未簽核 faithful | 失敗並列出缺項 |

第二列是整套設計的重點：**陳述文字沒有變，但意義變了，流程照樣擋下來。** 附帶效果是 `IsEven := True` 也讓 guards 編不過（`¬IsEven 1` 不再可證），形成第二個獨立訊號。

## 操作步驟

```
# 1. 看稽核器要求什麼 guard（寫 guard 之前）
harness/audit sanity_req.json        # 印出 expected_witness / expected_necessity

# 2. 在 reference/AmpasRef/Guards.lean 證出來，編譯

# 3. 凍結（guard 不通過會拒絕凍結）
python3 harness/ampas_review.py freeze

# 4. 審查者簽署（私鑰在審查者手上）
python3 harness/ampas_review.py sign --key <private.pem> --key-id <id>

# 5. 每次驗證都跑（CI）
python3 harness/ampas_review.py verify --out evidence/review_verification.json
```

`freeze` 在 guard 未滿足時會**拒絕**凍結（除非明確傳 `--allow-guard-failure`，那會把失敗記錄進紀錄裡）。

## 這套流程**沒有**解決的事

- **它不證明忠實度。** 凍結、簽署、guard 齊備的陳述，仍然只是一條「有人判斷為忠實」的陳述。guard 只排除兩類具體錯誤（空洞、假設過強），不排除「陳述講的是另一件事」。
- **審查者的判斷品質不在範圍內。** 流程保證判斷有歸屬、有時間、不會漂移；不保證判斷正確。
- **自然語言本身可能有歧義。** 文字若本身不精確，凍結的只是對某一種讀法的承諾。
- **私鑰管理不在模型內。** 本輪用示範金鑰；正式部署需要真正的金鑰保管與審查者身分綁定（這與 Run 1–16 的身分軌是同一類問題）。
