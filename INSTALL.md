# Install and verify

Nothing here needs root, a container, or network access beyond fetching the
Lean toolchain (and Mathlib / lean4lean for the optional tiers).

## Requirements

| | Needed for | Notes |
| --- | --- | --- |
| Python ≥ 3.11 | every tier | `pip install -r requirements.txt` — `pytest` for the suites, and `cryptography` for the Ed25519 sign-off (tier 1 and up). Tier 0 alone needs only `pytest`. |
| `elan` + Lean 4.33.0 | tiers 1–3 | `lean-toolchain` pins the version; elan honours it |
| `git` | tiers 2–3 | fetching lean4lean and Mathlib |
| A C toolchain | nothing required | only to *compile* the auditor; there is a fallback |
| ~2 GB disk | tiers 1–2 | tier 3 needs several GB more for Mathlib |

Tested on Linux x86-64. The harness's sandbox uses POSIX `setuid`/`setrlimit`,
so the sandboxed path is Linux/macOS only; see
[Running without the sandbox](#running-without-the-sandbox).

**If a script will not run** (`Permission denied`), the executable bit was
dropped — git does not track it on Windows, so a commit made there loses mode
755. `bash ./scripts/verify.sh` works regardless; to fix the bit,
`git update-index --chmod=+x scripts/<file>`. `tests/test_portability.py`
fails on this, so a clone whose bits are intact will say so.

### Windows

Install elan with PowerShell (7.4.1 or later; `$PSVersionTable.PSVersion`
tells you). The commands are from elan's own README:

```powershell
curl -O --location https://elan.lean-lang.org/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1
```

On Windows PowerShell 5.1 the script may not run; take the release zip from
[leanprover/elan releases](https://github.com/leanprover/elan/releases)
instead, unpack it and run the installer inside. Either way, open a new shell
afterwards so `elan` is on PATH. `lean-toolchain` pins the version and elan
installs it on first use from this directory, so there is nothing else to
choose.

The shell scripts need bash — use Git Bash, which comes with Git for Windows
(they find `python` when `python3` does not exist). To avoid bash entirely,
the two steps that matter can be run directly:

```powershell
lake build AmpasRef                                   # the trusted reference
$env:AMPAS_TRUSTED_OLEAN = "$PWD\.lake\build\lib\lean"
$env:PYTHONUTF8 = "1"                                 # belt and braces
python harness/ampas_review.py freeze                 # re-freeze the records
python scripts/sign_attestations.py $HOME\.ampas\<key>.pem <key-id>
```

**On Windows**, the parts that need no sandbox do work: the formalization
sign-off (`keygen`, `sign`, `scripts/sign_attestations.py`) and most of tier 0.
Three tier-0 tests import the driver and are skipped, because verifying a
submission means confining it and there is no `setrlimit` to confine it with.
Every file the harness reads is UTF-8 and the code says so explicitly, so a
non-UTF-8 system locale (cp950, cp1252) is not a problem — it was, which is
why `tests/test_portability.py` exists.

## Tier 0 — no Lean at all

```bash
python3 -m pytest tests/test_third_check.py -q -k "not pipeline"
```

Eighteen tests, under a second. They run the third checker against fixed
export files committed in `tests/forgeries/` and pin what a clean result from
it is allowed to mean. Worth running first: it is the part of this repository
that is hardest to fake and easiest to check.

## Tiers 0–1 — the pinned Lean toolchain

```bash
# install elan if you do not have it (Linux/macOS)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

pip install -r requirements.txt    # pytest + cryptography
./scripts/bootstrap.sh     # toolchain, trusted reference, provenance baseline
./scripts/verify.sh 1      # ~6 minutes
```

`bootstrap.sh` prints one `declaration uses 'sorry'` warning per frozen
statement while building `AmpasRef` — ten for the core catalogue. **Those are
expected.** The reference statements are deliberately unproved: they are the
statements a submission has to prove, and a `sorry` stub is how they are
frozen without presupposing a proof. (This said "three" until 2026-10-14,
left over from a round with three claims.)

What tier 1 runs:

- all 16 core submissions through compile → kernel replay → third check →
  auditor, each compared against the verdict the manifest predicted;
- `harness/ablation.py`, which prints *which layer* caught each attack;
- the formalization sign-off: freeze, guards, Ed25519 signature, drift
  detection;
- the bounded counterexample search over the frozen statements, which should
  reproduce `reference/counterexample_search.json`;
- the six test suites: 115 pass and 11 skip at tier 1, out of 125 collected
  across `tests/` — the Mathlib fixtures skip without `AMPAS_MATHLIB_PATH`.

## Tier 2 — the second independent kernel

```bash
./scripts/build-lean4lean.sh
./scripts/verify.sh 2
```

Clones [lean4lean](https://github.com/digama0/lean4lean) at the pinned
revision from `reference/lean4lean_pin.json` and builds it. `verify.sh` picks
the binary up automatically; certification then requires both Lean kernels.

Note `reference/lean4lean_pin.json`: the upstream repository declares toolchain
`v4.33.0-rc2` while this suite pins `v4.33.0`. The recorded run built it with
`v4.33.0` and the pin file records the discrepancy rather than hiding it.

## Tier 3 — the Mathlib claims

```bash
./scripts/build-mathlib-tier.sh    # ~20 min on two cores, from source
./scripts/verify.sh                # all tiers
```

The Mathlib tier is a **separate Lake project** (`mathlib-tier/`) that requires
the core package by path. That is deliberate: a claim stated over Mathlib's
`Nat.Prime` pulls Mathlib into that claim's trusted set and into its freeze,
and keeping it separate means the core claims cannot acquire that dependency by
accident.

The script tries `lake exe cache get` first. The recorded run could not use it
— the cache host was reachable but served an archive format the pinned
toolchain's `leantar` could not read — so the recorded results are from a
source build, and `reference/mathlib_pin.json` says so. Either route gives the
same verdicts; `scripts/check_mathlib_pin.py` verifies the resolved revisions
against the pin and fails loudly if they drift.

Tier 3 also runs the external validation pair (Fermat 1640 / Euler 1732),
which needs Mathlib's `Nat.Prime`.

## Verifying a submission of your own

This is the most informative thing you can do with this repository, since the
committed corpus was written by the same hands as the harness.

```bash
export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
export AMPAS_THIRD_CHECK=1
export AMPAS_KERNEL_BASELINE=$PWD/build/kernel_baseline.json

python3 harness/ampas_lean.py path/to/YourProof.lean \
    --module YourProof --claims EVEN
```

`--claims` takes claim ids from `reference/claims.json`. Your file must declare
the theorem with the reference's exact name (`Ampas.Claims.even_add_even` for
`EVEN`) and may import only `AmpasRef.Defs`, not `AmpasRef.Challenge` — the
latter holds the `sorry` stubs.

To add a claim of your own you also have to write the reference statement, its
guards, and the sign-off; `docs/review-formalization.md` is the process. The
freeze will refuse the statement until a counterexample search has run against
it:

```bash
python3 harness/counterexample.py --out reference/counterexample_search.json
python3 harness/ampas_review.py freeze
```

Set the claim's box in `reference/counterexample_bounds.json` if the default
(each `Nat` variable over 0…24, existential witnesses hunted to 96) is wrong
for it — too large a box can be slower than you expect, because the search
*evaluates* the statement at every point. What the result is allowed to mean
is in ASSUMPTIONS A1b; the one-line version is that finding a counterexample
is decisive and finding none is not.

## Running without the sandbox

The sandbox needs root and a system user:

```bash
sudo useradd --system --no-create-home --shell /usr/sbin/nologin ampas-sub
```

Without root (`geteuid() != 0`) or without that user, the driver runs
submissions **as you**, with the resource limits still applied, and nothing
else changes about the verdicts. Compiling a submission means running arbitrary
Lean elaboration, including its macros, so for anything you did not write
yourself, do this in a VM or container.

Override the user name with `AMPAS_SANDBOX_USER`.

## When the auditor will not link

`lake build audit` compiles `harness/Audit.lean` to a native executable. It
fails on some Lean distributions — a conda-forge build records placeholder
library paths, so the linker looks for `libgmp`/`libuv`/`libssl` under a
nonexistent `/home/conda/feedstock_root/...`.

**You can ignore it.** The driver detects the missing binary and runs
`lean --run harness/Audit.lean` instead: roughly 3× slower, identical results,
no C toolchain needed. The trusted fingerprint then hashes `Audit.lean` rather
than the binary, so what ran is still what was hashed.

If you want the binary, `harness/relink.py` links it with the system compiler
against the system libraries; `docs/build-notes.md` has the command.

## Environment variables

| Variable | Default | Meaning |
| --- | --- | --- |
| `LEAN_ROOT` | from `lean --print-prefix` | Lean toolchain prefix |
| `AMPAS_TRUSTED_OLEAN` | `./build` | the trusted reference oleans |
| `AMPAS_EXTRA_LEAN_PATH` | — | extra olean paths (Mathlib tier) |
| `AMPAS_AUDIT_BIN` | `harness/audit` | compiled auditor; falls back to `lean --run` |
| `AMPAS_CLAIMS` | `reference/claims.json` | which claim catalogue |
| `AMPAS_THIRD_CHECK` | off | set to `1` to run the third check |
| `AMPAS_KERNEL_BASELINE` | `reference/kernel_baseline.json` | its provenance baseline |
| `AMPAS_LEAN4LEAN` | — | path to the lean4lean binary |
| `AMPAS_MATHLIB_PATH` | — | used by the Mathlib test fixtures |
| `AMPAS_CPU_SECONDS` / `AMPAS_WALL_SECONDS` | 120 / 180 | per-submission limits |
| `AMPAS_MEM_BYTES` | 10 GiB | per-submission address-space cap |
| `AMPAS_EXPORT_MEM_BYTES` | 24 GiB | cap for the exporter — `lean --run` mmaps the whole library, and `RLIMIT_AS` caps address space, not resident memory |
| `AMPAS_LEAN_THREADS` | 2 | `LEAN_NUM_THREADS` |
| `AMPAS_SANDBOX_USER` | `ampas-sub` | unprivileged user |

## Reproducing the recorded evidence

`evidence/` holds the results of the recorded run;
`evidence/INDEX.zh-TW.md` lists each file with the command that produces it.
`verify.sh` writes fresh results into `build/` rather than overwriting
`evidence/`, so you can diff your run against the recorded one.
