#!/usr/bin/env python3
"""AMPAS math-verification round 1: the driver.

For one submission (a Lean file proving the reference theorems of one or
more claims) this:

  1. compiles the submission in a sandbox (an unprivileged user, a scratch
     LEAN_PATH it may write, the trusted oleans read-only, a time and memory
     limit); elaboration runs the submission's own code, so it is confined;
  2. replays every declaration of the compiled submission through the Lean
     kernel with `leanchecker` (this is the step that makes acceptance mean
     "the kernel checked it"), and with `--fresh` for a second, independent
     replay into an empty environment;
  3. runs the auditor (harness/Audit.lean, compiled) against the trusted
     reference environment and the submission's, which reports the statement
     comparison, axioms, dependencies and flags without running submission
     code;
  4. decides, per claim and under the claim's policy, whether the claim is
     CERTIFIED, and records why.

A claim is CERTIFIED only if, for its reference theorem:
  - the submission declares it as a theorem (not an axiom or a def);
  - the kernel replay (both modes) succeeded;
  - the statement matches: the closure check passes (every constant the
    reference statement rests on means the same in the submission) and the
    elaborated statements are equal, under the claim's comparator policy
    (strict alpha-equivalence, or kernel definitional equality);
  - the axioms the proof uses are within the claim's axiom policy;
  - no flag fires that the policy forbids (sorry and native evaluation are
    forbidden for every claim; opaque-in-statement and untrusted statement
    constants are always forbidden).

Nothing here establishes that the reference statement faithfully renders the
natural-language claim: that is the human-reviewed attestation in
reference/claims.json, surfaced in the result but never inferred.
"""
from __future__ import annotations

import json
import os
try:
    import resource          # POSIX only
except ModuleNotFoundError:  # Windows
    # The sandbox (rlimits, setuid) is POSIX-only and the module documents
    # that. But IMPORTING the driver must not fail for it: tier 0 needs no
    # Lean and no sandbox, and a reviewer on Windows should be able to run it
    # -- three tier-0 tests died at this import line rather than at the step
    # that actually needs a sandbox.
    resource = None  # type: ignore[assignment]
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field, asdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
def _lean_root() -> Path:
    """Where the Lean toolchain lives.

    LEAN_ROOT wins; otherwise ask Lean itself (`lean --print-prefix`), which
    works for an elan-managed toolchain as well as an unpacked one; otherwise
    fall back to the parent of whatever `lean` is on PATH. No path in this
    file is specific to the machine the suite was developed on.
    """
    env = os.environ.get("LEAN_ROOT")
    if env:
        return Path(env)
    try:
        out = subprocess.run(["lean", "--print-prefix"], capture_output=True,
                             text=True, encoding="utf-8", timeout=60)
        if out.returncode == 0 and out.stdout.strip():
            return Path(out.stdout.strip())
    except (OSError, subprocess.SubprocessError):
        pass
    found = shutil.which("lean")
    if found:
        return Path(found).resolve().parent.parent
    # Deliberately NOT fatal here. Tier 0 of the verification runs with no
    # Lean at all, and it imports this module; raising at import time would
    # make the no-Lean tier impossible. Anything that actually needs Lean
    # calls require_lean() first.
    return None


LEAN_ROOT = _lean_root() or Path("/nonexistent-lean-toolchain")
LEAN_FOUND = _lean_root() is not None


def require_lean() -> None:
    """Fail with something actionable, at the point Lean is actually needed."""
    if not LEAN_FOUND:
        raise SystemExit(
            "Lean not found: put `lean` on PATH or set LEAN_ROOT. "
            "See INSTALL.md; ./scripts/bootstrap.sh installs the pinned "
            "toolchain. (Tier 0 of the verification needs no Lean: "
            "python3 -m pytest tests/test_third_check.py -q -k 'not pipeline')")
LEAN_BIN = LEAN_ROOT / "bin"


def lean_exe(name: str) -> Path:
    """The toolchain's `name` binary, with the platform's extension.

    On Windows these are `lean.exe` and `leanchecker.exe`. Building the path
    without the suffix is not merely untidy: it produced

        OSError: [WinError 193] %1 is not a valid Win32 application

    from inside subprocess, which tells a reader nothing about what was
    wrong. So the probe is explicit, and when it fails it names what it
    looked for. This is the one definition; the other harness modules import
    it from here.
    """
    require_lean()
    base = _lean_root() / "bin" / name
    candidates = ([base.with_name(base.name + ".exe"), base] if os.name == "nt"
                  else [base])
    for c in candidates:
        if c.is_file():
            return c
    raise SystemExit(
        f"no Lean `{name}` binary under {base.parent}. Looked for: "
        + ", ".join(c.name for c in candidates)
        + ". Set LEAN_ROOT to the toolchain prefix (`lean --print-prefix`).")


def usable_binary(p: Path) -> bool:
    """`os.access(X_OK)` is true for ANY existing file on Windows, so it
    cannot tell a native executable from a Linux ELF left behind by a build on
    another machine. Require the extension there."""
    if not p.is_file():
        return False
    if os.name == "nt":
        return p.suffix.lower() in (".exe", ".bat", ".cmd")
    return os.access(p, os.X_OK)
TRUSTED_OLEAN = Path(os.environ.get("AMPAS_TRUSTED_OLEAN", ROOT / "build"))
AUDIT_BIN = Path(os.environ.get("AMPAS_AUDIT_BIN", HERE / "audit"))

def audit_cmd() -> list[str]:
    """How to invoke the auditor.

    The compiled executable when it exists, otherwise `lean --run` on its
    source. The interpreted route is roughly 3x slower but needs no C
    toolchain and no linking, so a reviewer who only ran
    `elan`/`lake build AmpasRef` can still verify everything. Linking the
    executable fails outright on some Lean distributions (a conda build
    records placeholder library paths); docs/build-notes.md has the fix.
    """
    if usable_binary(AUDIT_BIN):
        return [str(AUDIT_BIN)]
    require_lean()
    src = HERE / "Audit.lean"
    if not src.exists():
        raise SystemExit(f"auditor not found: no executable at {AUDIT_BIN} and no {src}")
    return [str(lean_exe("lean")), "--run", str(src)]


def audit_fingerprint_path() -> Path:
    """What to hash as "the auditor" in the trusted fingerprint: the compiled
    binary if it is what runs, otherwise its source."""
    if usable_binary(AUDIT_BIN):
        return AUDIT_BIN
    return HERE / "Audit.lean"

# Round 2: a second, independently written kernel (lean4lean). When
# configured, a claim is certified only if BOTH kernels accept the
# submission, and any disagreement is recorded as a finding in its own right.
L4L_BIN = os.environ.get("AMPAS_LEAN4LEAN", "")
# Further read-only olean directories a submission may import from (a pinned
# library such as Mathlib). They are part of the trusted set: their contents
# are hashed by trusted_fingerprint() and enter each claim's freeze through
# the auditor's closure check.
EXTRA_LEAN_PATH = os.environ.get("AMPAS_EXTRA_LEAN_PATH", "")
# A third check: a type checker written from the rules of Lean's type theory
# in Python (harness/kernel3, reviewed in harness/kernel3/REVIEW.md). It
# shares no code with Lean, so it corroborates the TERM layer independently
# of both Lean-based kernels. It does NOT derive that an inductive
# specification is legitimate, so it only vouches for inductives whose
# fingerprint matches the trusted baseline; anything else it reports as an
# assumption it did not cover. Set to "1" to run it.
THIRD_CHECK = os.environ.get("AMPAS_THIRD_CHECK", "") == "1"
KERNEL_BASELINE = Path(os.environ.get(
    "AMPAS_KERNEL_BASELINE", ROOT / "reference" / "kernel_baseline.json"))
# Declarations this checker rejects while BOTH Lean kernels accept them, with
# a reviewer's adjudication of why (reference/third_check_adjudications.json).
# A disagreement that is NOT in that file blocks certification: the third
# check may have found something. An adjudicated one does not, because a less
# complete third implementation must not be able to veto a proof two Lean
# kernels accept -- see finding TC-01 in that file.
ADJUDICATIONS = Path(os.environ.get(
    "AMPAS_THIRD_CHECK_ADJUDICATIONS",
    ROOT / "reference" / "third_check_adjudications.json"))
SANDBOX_USER = os.environ.get("AMPAS_SANDBOX_USER", "ampas-sub")

# limits for a single submission compilation / check
CPU_SECONDS = int(os.environ.get("AMPAS_CPU_SECONDS", "120"))
WALL_SECONDS = int(os.environ.get("AMPAS_WALL_SECONDS", "180"))
# RLIMIT_AS caps ADDRESS SPACE, not resident memory, and a thread's stack is
# an mmap -- so a tight cap makes pthread_create fail ("failed to create
# thread") rather than reporting memory exhaustion. 10 GiB was tight enough
# for the largest submission to fail that way on a GitHub runner. It is not
# what bounds a submission anyway: CPU time, wall clock, output size and the
# unprivileged user are.
MEM_BYTES = int(os.environ.get("AMPAS_MEM_BYTES", str(24 * 1024 ** 3)))
# `lean --run` (the exporter) loads the whole Lean library and the
# interpreter, and RLIMIT_AS caps *address space*, not resident memory: the
# mmapped oleans alone reserve more than the submission limit above, so the
# export step gets its own cap. CPU, wall clock, file size and the
# unprivileged user still apply, and the exporter only reads.
EXPORT_MEM_BYTES = int(os.environ.get("AMPAS_EXPORT_MEM_BYTES", str(24 * 1024 ** 3)))
LEAN_THREADS = os.environ.get("AMPAS_LEAN_THREADS", "2")
# 512 was low enough that thread creation failed on the largest submission
# when the machine was loaded, which was then misreported as a rejection.
NPROC_LIMIT = int(os.environ.get("AMPAS_NPROC_LIMIT", "2048"))

FORBIDDEN_ALWAYS = ("SORRY", "NATIVE_EVALUATION", "OPAQUE_IN_STATEMENT",
                    "UNSAFE", "PARTIAL")


def _preexec(as_user: dict | None, limits: bool = True, mem: int | None = None):
    if resource is None:
        # No rlimits and no setuid here, so nothing may run as another user.
        if as_user is not None:
            raise SystemExit(
                "a sandbox user was requested but this platform has no setuid; "
                "run the verification on Linux or macOS")
        return None
    def fn():
        if not limits:
            return
        resource.setrlimit(resource.RLIMIT_CPU, (CPU_SECONDS, CPU_SECONDS + 5))
        m = mem or MEM_BYTES
        resource.setrlimit(resource.RLIMIT_AS, (m, m))
        try:
            resource.setrlimit(resource.RLIMIT_NPROC, (NPROC_LIMIT, NPROC_LIMIT))
        except (ValueError, OSError):
            pass
        resource.setrlimit(resource.RLIMIT_FSIZE, (512 * 1024 ** 2, 512 * 1024 ** 2))
        if as_user is not None:
            os.setgid(as_user["gid"])
            os.setuid(as_user["uid"])
    return fn


def _sandbox_user() -> dict | None:
    # os.geteuid and pwd are POSIX-only too, so ask the platform rather than
    # assume it: on Windows there is no unprivileged-user sandbox and the
    # driver says so where it matters instead of failing at import.
    if not hasattr(os, "geteuid") or os.geteuid() != 0:
        return None
    import pwd
    try:
        p = pwd.getpwnam(SANDBOX_USER)
    except KeyError:
        return None
    return {"uid": p.pw_uid, "gid": p.pw_gid}


def _clip(text: str, n: int = 2000) -> str:
    """Keep the head AND tail of a checker's output. The verdict is at the
    start -- `(kernel) declaration type mismatch ...` -- while a crash can
    append pages of stack trace, so a tail-only clip can discard the only
    line that says what happened."""
    if len(text) <= 2 * n:
        return text
    return text[:n] + f"\n...[{len(text) - 2 * n} characters omitted]...\n" + text[-n:]


def _run(cmd, cwd, lean_path, as_user, env_extra=None, limits=True, wall=None, mem=None):
    env = {"PATH": f"{LEAN_BIN}:/usr/bin:/bin", "LEAN_PATH": lean_path,
           "HOME": str(cwd), "LEAN_ABORT_ON_PANIC": "1",
           "LEAN_NUM_THREADS": LEAN_THREADS}
    if env_extra:
        env.update(env_extra)
    try:
        return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, encoding="utf-8",
                              timeout=wall or WALL_SECONDS,
                              preexec_fn=_preexec(as_user, limits, mem))
    except subprocess.TimeoutExpired as e:
        return subprocess.CompletedProcess(cmd, 124, e.stdout or "", (e.stderr or "") + "\nTIMEOUT")


def _exhausted(r) -> bool:
    """Did this run hit a resource limit rather than reach a verdict? A
    checker killed by the CPU limit (SIGXCPU, -24), the wall clock (124) or
    the memory limit (-9 / a MemoryError) has NOT rejected the proof: taking
    its non-zero exit for a rejection makes a verdict depend on machine load.
    Two concurrent runs on this 2-core machine were enough to do it."""
    if r.returncode == 0:
        return False
    if r.returncode in (124, -24, -9, 137):
        return True
    text = ((r.stdout or "") + (r.stderr or "")).lower()
    # A checker can also run out of memory without being signalled: Lean's C++
    # kernel throws std::bad_alloc and exits non-zero, which earlier code read
    # as a rejection. Found while packaging, on the largest submission.
    # Lean reports resource failures as thrown exceptions with specific
    # messages, so they have to be recognized by signature. Three of these
    # were found one at a time, each having first been misreported as a
    # kernel rejection: SIGXCPU, then std::bad_alloc, then thread exhaustion.
    # This list is therefore KNOWN INCOMPLETE -- see ASSUMPTIONS.md A5. What
    # actually protects a run is that every submission has a predicted verdict
    # in the manifest, so a resource failure on a submission expected to
    # certify fails the run loudly instead of passing as a rejection.
    return any(m in text for m in (
        "timeout", "out of memory", "bad_alloc", "cannot allocate memory",
        "memoryerror", "killed",
        "failed to create thread", "resource temporarily unavailable",
        "too many open files", "cannot allocate"))


def _why(r) -> str:
    named = {124: "wall-clock timeout", -24: "SIGXCPU (CPU limit)",
             -9: "SIGKILL (memory limit)", 137: "SIGKILL (memory limit)"}
    if r.returncode in named:
        return named[r.returncode]
    text = ((r.stdout or "") + (r.stderr or "")).lower()
    if "bad_alloc" in text or "cannot allocate" in text or "memoryerror" in text:
        return f"out of memory (exit {r.returncode})"
    if "failed to create thread" in text or "resource temporarily unavailable" in text:
        return f"thread/process limit (exit {r.returncode})"
    if "too many open files" in text:
        return f"file-descriptor limit (exit {r.returncode})"
    if "timeout" in text:
        return f"timeout (exit {r.returncode})"
    return f"exit {r.returncode}"


@dataclass
class ClaimVerdict:
    claim: str
    theorem: str
    certified: bool
    reasons: list[str] = field(default_factory=list)
    axioms: list[str] = field(default_factory=list)
    flags: list[str] = field(default_factory=list)
    statement: dict = field(default_factory=dict)
    kind: str = ""
    review: dict = field(default_factory=dict)
    # what the third check said about this submission's closure: CONFIRMED,
    # DISAGREEMENT (adjudicated/unadjudicated), or NOT_RUN. Certification
    # rests on the two Lean kernels; this records the corroboration.
    corroboration: str = "NOT_RUN"
    # Which LAYER blocked, as tags rather than prose. harness/ablation.py used
    # to classify the `reasons` strings by substring match, so a
    # meaning-preserving reword of a reason silently removed a signal from the
    # "which layer caught each attack" table -- and that table is the evidence
    # that no single layer is doing all the work. Tags are set where the reason
    # is appended, by the code that knows which layer it was.
    signals: list[str] = field(default_factory=list)
    # true when no verdict was reached because a checker ran out of CPU, wall
    # clock or memory. NOT certified, but not a rejection either.
    inconclusive: bool = False


@dataclass
class SubmissionResult:
    submission: str
    module: str
    compiled: bool
    kernel_replay: bool
    kernel_replay_independent: object
    kernel_agreement: str
    third_check: dict
    kernel_replay_fresh: object
    compile_stderr: str
    solution_imports: list[str] = field(default_factory=list)
    claims: list[ClaimVerdict] = field(default_factory=list)
    error: str = ""
    # checkers that hit a resource limit instead of reaching a verdict. A
    # claim is never certified while this is non-empty, but the result says
    # INCONCLUSIVE rather than claiming a kernel rejected the proof.
    resource_exhausted: list[str] = field(default_factory=list)

    def to_json(self) -> dict:
        d = asdict(self)
        return d


def _sha256(path: Path) -> str:
    import hashlib
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def trusted_fingerprint() -> dict:
    """SHA-256 of every trusted artifact a submission is checked against:
    the reference oleans, the auditor, the Lean and leanchecker binaries,
    and the Init oleans of the toolchain."""
    files = sorted(TRUSTED_OLEAN.rglob("*.olean")) + [audit_fingerprint_path(),
                                                      lean_exe("lean"),
                                                      lean_exe("leanchecker")]
    for extra in filter(None, EXTRA_LEAN_PATH.split(os.pathsep)):
        files += sorted(Path(extra).rglob("*.olean"))
    files += sorted((LEAN_ROOT / "lib" / "lean" / "Init").rglob("*.olean"))
    files.append(LEAN_ROOT / "lib" / "lean" / "Init.olean")
    return {str(p): _sha256(p) for p in files}


def baseline(module: str = "AmpasRef.Challenge") -> dict:
    """Once per toolchain and reference: replay everything the reference
    imports (Init and AmpasRef.Defs) and defines into an empty kernel."""
    require_lean()
    import time
    t0 = time.time()
    r = _run([str(lean_exe("leanchecker")), "--fresh", module], ROOT, str(TRUSTED_OLEAN),
             None, {"LEAN_NUM_THREADS": LEAN_THREADS}, limits=False, wall=1800)
    return {"module": module, "ok": r.returncode == 0, "returncode": r.returncode,
            "seconds": round(time.time() - t0, 1), "output": (r.stdout + r.stderr)[-1000:]}


def load_catalogue() -> dict:
    path = Path(os.environ.get("AMPAS_CLAIMS", ROOT / "reference" / "claims.json"))
    return json.loads(path.read_text(encoding="utf-8"))


def check_submission(sub_path: Path, module: str, claims: list[dict],
                     reference_module: str, trusted_modules: list[str],
                     defeq_default: bool = True) -> SubmissionResult:
    require_lean()
    as_user = _sandbox_user()
    work = Path(tempfile.mkdtemp(prefix="ampas-sub-"))
    try:
        build = work / "build"
        build.mkdir()
        # the submission is compiled against the trusted oleans (read-only)
        # and writes only into its own build dir
        lean_path = f"{TRUSTED_OLEAN}:{build}"
        if EXTRA_LEAN_PATH:
            lean_path = f"{lean_path}{os.pathsep}{EXTRA_LEAN_PATH}"
        src = work / f"{module.replace('.', '/')}.lean"
        src.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(sub_path, src)
        if as_user is not None:
            for p in (work, build, src, src.parent):
                os.chown(p, as_user["uid"], as_user["gid"])
        olean = build / f"{module.replace('.', '/')}.olean"
        olean.parent.mkdir(parents=True, exist_ok=True)
        if as_user is not None:
            os.chown(olean.parent, as_user["uid"], as_user["gid"])
        res = SubmissionResult(submission=sub_path.name, module=module, compiled=False,
                               kernel_replay=False, kernel_replay_independent=None,
                               kernel_agreement="not_run", third_check={"run": False},
                               kernel_replay_fresh=False, compile_stderr="")
        before = trusted_fingerprint()
        cc = _run([str(lean_exe("lean")), "-o", str(olean), str(src)], work, lean_path, as_user)
        if trusted_fingerprint() != before:
            res.error = "TRUSTED_ARTIFACT_MODIFIED during compilation"
            return res
        res.compile_stderr = (cc.stdout + cc.stderr)[-4000:]
        if _exhausted(cc):
            # A resource failure while COMPILING is not "it did not compile",
            # and it is certainly not a statement about the proof. This was
            # the one step the exhaustion check was never applied to, and it
            # is where CI hit it: `failed to create thread` on the largest
            # submission, reported as a plain rejection.
            res.resource_exhausted.append(f"lean (compile) ({_why(cc)})")
            res.compile_stderr = _clip(cc.stdout + cc.stderr)
            return res
        if cc.returncode != 0 or not olean.exists():
            return res
        res.compiled = True
        # kernel replay: the olean is in build, so leanchecker finds it there
        kc = _run([str(lean_exe("leanchecker")), module], work, lean_path, as_user)
        res.kernel_replay = kc.returncode == 0
        if _exhausted(kc):
            res.resource_exhausted.append(f"leanchecker ({_why(kc)})")
        if not res.kernel_replay:
            res.compile_stderr += "\n[leanchecker]\n" + _clip(kc.stdout + kc.stderr)
        # second, independent kernel: a different implementation by a
        # different author, re-checking the same compiled oleans
        if L4L_BIN:
            l4 = _run([L4L_BIN, module], work, lean_path, as_user,
                      wall=max(WALL_SECONDS, 900))
            res.kernel_replay_independent = l4.returncode == 0
            if _exhausted(l4):
                res.resource_exhausted.append(f"lean4lean ({_why(l4)})")
            if res.kernel_replay_independent != res.kernel_replay:
                res.kernel_agreement = "DISAGREE"
                res.compile_stderr += (f"\n[KERNEL DISAGREEMENT] leanchecker="
                                       f"{res.kernel_replay} lean4lean="
                                       f"{res.kernel_replay_independent}\n"
                                       + _clip(l4.stdout + l4.stderr))
            else:
                res.kernel_agreement = "agree"
            if not res.kernel_replay_independent:
                res.compile_stderr += "\n[lean4lean]\n" + _clip(l4.stdout + l4.stderr)
        # the fresh replay (all of Init into an empty kernel, ~3 minutes) is
        # run once per toolchain and reference (baseline()), not per submission;
        # the imported oleans are the baseline's, checked by hash below
        res.kernel_replay_fresh = None
        # auditor
        req = {"reference_module": reference_module, "solution_module": module,
               "trusted_modules": trusted_modules,
               "kernel_defeq": defeq_default,
               "theorems": [c["theorem"] for c in claims]}
        req_path = work / "req.json"
        req_path.write_text(json.dumps(req), encoding="utf-8", newline="\n")
        if as_user is not None:
            os.chown(req_path, as_user["uid"], as_user["gid"])
        au = _run(audit_cmd() + [str(req_path)], work, lean_path, as_user,
                  mem=EXPORT_MEM_BYTES if not AUDIT_BIN.exists() else None)
        if au.returncode != 0:
            res.error = "auditor failed: " + (au.stdout + au.stderr)[-2000:]
            return res
        audit = json.loads(au.stdout.strip().splitlines()[-1])
        res.solution_imports = sorted(set(audit.get("solution_imports", [])))
        by_name = {t["name"]: t for t in audit["theorems"]}
        if THIRD_CHECK:
            res.third_check = _third_check(
                work, lean_path, as_user, module,
                [c["theorem"] for c in claims
                 if by_name.get(c["theorem"], {}).get("found")])
        for c in claims:
            # Certification rests on the two Lean-based kernels. The third
            # check corroborates; an UNADJUDICATED disagreement still blocks,
            # because it may be a real finding rather than its incompleteness.
            replay_ok = res.kernel_replay and (res.kernel_replay_independent is not False)
            tc = res.third_check
            # The third check runs without knowing the Lean kernels' result, so
            # its own label can only say "I objected". Whether that objection is
            # a DISAGREEMENT or a CORROBORATION depends on whether the Lean
            # kernels accepted the module, which is known here and not there.
            # Correcting it here keeps the printed table from reporting a
            # disagreement where all three checkers agreed -- A01_kernel_bypass
            # was reported that way for every run until 2026-10-14.
            if tc.get("status", "").startswith("DISAGREEMENT") and not replay_ok:
                tc["status"] = ("CORROBORATION (the third check also rejected; the Lean "
                                "kernels rejected too)")
                tc["corroborated_rejection"] = True
                tc["unadjudicated_disagreement"] = False
            # `replay_ok` is passed separately so the recorded reason can say
            # WHICH of the two blocked. It used to report "the third check
            # rejects a declaration the Lean kernels accept" whenever the third
            # check had errors -- including when the Lean kernels had rejected
            # the module too, which is the opposite of what happened.
            kernel_ok = replay_ok and not tc.get("unadjudicated_disagreement")
            res.claims.append(_verdict(c, by_name.get(c["theorem"], {}), kernel_ok,
                                       tc.get("status", "NOT_RUN"),
                                       res.resource_exhausted, replay_ok))
        return res
    finally:
        shutil.rmtree(work, ignore_errors=True)


def _third_check(work: Path, lean_path: str, as_user, module: str, roots: list) -> dict:
    """Export the closure of the given constants and re-check it with the
    Python checker. Exporting loads the olean without environment extensions,
    so none of the submission's code runs; the checker runs none either."""
    if not roots:
        return {"run": False, "summary": "no theorems to check"}
    exp = work / "closure.export"
    r = _run([str(lean_exe("lean")), "--run", str(HERE / "Export.lean"), module, str(exp)]
             + roots, work, lean_path, as_user, mem=EXPORT_MEM_BYTES)
    if r.returncode != 0 or not exp.exists():
        return {"run": False, "summary": "export failed",
                "output": (r.stdout + r.stderr)[-1200:]}
    sys.path.insert(0, str(HERE))
    try:
        from kernel3.parse import parse_export
        from kernel3.check import check_env
    except Exception as e:                                  # pragma: no cover
        return {"run": False, "summary": f"checker unavailable: {e}"}
    baseline = None
    if KERNEL_BASELINE.exists():
        baseline = set(json.loads(KERNEL_BASELINE.read_text(encoding="utf-8")))
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(60000)
    try:
        out = check_env(parse_export(str(exp)), baseline=baseline)
    except Exception as e:
        return {"run": True, "errors": [["<checker>", f"{type(e).__name__}: {e}"[:300]]],
                "summary": "the checker itself failed"}
    finally:
        sys.setrecursionlimit(old)
    # a rejection the two Lean kernels do not share is a DISAGREEMENT, and it
    # is only discounted where a reviewer has adjudicated that declaration
    adj = {}
    if ADJUDICATIONS.exists():
        adj = {d["name"]: d for d in
               json.loads(ADJUDICATIONS.read_text(encoding="utf-8")).get("declarations", [])}
    disputed = [n for n, _ in out["errors"]]
    unadjudicated = [n for n in disputed if n not in adj]
    if not out["errors"]:
        status = "CONFIRMED"
    elif unadjudicated:
        status = "DISAGREEMENT (unadjudicated)"
    else:
        status = "DISAGREEMENT (adjudicated: checker incompleteness)"
    return {"run": True, "status": status, "checked": out["checked"], "total": out["total"],
            "errors": out["errors"][:5],
            "disagreements": disputed,
            "unadjudicated_disagreement": bool(unadjudicated),
            "unadjudicated": unadjudicated,
            "introduced_assumptions": out["introduced_assumptions"],
            "baseline_assumptions": out["baseline_assumptions"],
            "unproved_theorems": out["unproved_theorems"],
            "covers": ("every declaration's type; inductive specifications only where they "
                       "match the trusted baseline"),
            "summary": (f"{out['checked']}/{out['total']} declarations re-checked, "
                        f"{len(out['introduced_assumptions'])} assumption(s) not covered"
                        if not out["errors"] else
                        f"{out['checked']}/{out['total']} re-checked; "
                        f"{len(disputed)} disagreement(s), "
                        f"{len(unadjudicated)} unadjudicated")}


def _verdict(claim: dict, t: dict, kernel_ok: bool,
             corroboration: str = "NOT_RUN",
             resource_exhausted: list | None = None,
             replay_ok: bool | None = None) -> ClaimVerdict:
    v = ClaimVerdict(claim=claim["id"], theorem=claim["theorem"], certified=False,
                     review=claim.get("review", {}), corroboration=corroboration)
    if resource_exhausted:
        # not a rejection: no verdict was reached. Saying "the kernel rejected
        # it" here would make the result depend on how busy the machine is.
        v.inconclusive = True
        v.reasons.append("INCONCLUSIVE: a checker hit a resource limit rather than "
                         "reaching a verdict: " + ", ".join(resource_exhausted)
                         + ". Re-run on an unloaded machine or raise the limits; "
                           "this is not a statement about the proof.")
        return v
    if not t or not t.get("found"):
        v.signals.append("theorem missing")
        v.reasons.append("the submission does not declare this theorem")
        return v
    v.kind = t.get("kind", "")
    v.axioms = t.get("axioms", [])
    v.flags = t.get("flags", [])
    v.statement = t.get("statement", {})
    policy = claim.get("policy", {})
    allowed_axioms = set(policy.get("axioms", []))
    comparator = policy.get("comparator", "strict")  # strict | defeq

    if v.kind != "theorem":
        v.reasons.append(f"declared as {v.kind}, not a theorem")
        v.signals.append("kind!=theorem")
    if not kernel_ok:
        # Two different things block here and they must not be reported as one.
        # A third-check objection is a DISAGREEMENT only when the Lean kernels
        # ACCEPTED the module; when they rejected it too, the third check
        # corroborated them and saying otherwise inverts what happened.
        disagrees = corroboration.startswith("DISAGREEMENT (unadjudicated")
        if replay_ok is False:
            v.reasons.append("kernel replay did not succeed (primary or independent kernel)")
            if disagrees:
                v.reasons.append("the third check also rejected a declaration, corroborating "
                                 "the Lean kernels rather than disagreeing with them")
        elif disagrees:
            v.reasons.append("the third check rejects a declaration the Lean kernels accept, "
                             "and that disagreement has not been adjudicated")
        else:
            v.reasons.append("kernel replay did not succeed (primary or independent kernel)")
    st = v.statement
    if not st.get("closure_ok"):
        diff = st.get("closure_differing", []) + st.get("closure_missing", [])
        v.signals.append("closure")
        v.reasons.append("statement rests on redefined or missing constants: "
                         + ", ".join(diff[:8]))
    if st.get("extra_constants"):
        v.signals.append("closure")
        v.reasons.append("statement uses constants outside the reference: "
                         + ", ".join(st["extra_constants"][:8]))
    match_ok = st.get("strict_equal") if comparator == "strict" else (
        st.get("strict_equal") or st.get("kernel_defeq") is True)
    if not match_ok:
        v.signals.append("statement")
        v.reasons.append(f"statement does not match the reference ({comparator})")
    extra_axioms = sorted(set(v.axioms) - allowed_axioms)
    if extra_axioms:
        v.signals.append("axiom-policy")
        v.reasons.append("axioms outside the policy: " + ", ".join(extra_axioms))
    bad_flags = [f for f in v.flags if f.split(":")[0] in FORBIDDEN_ALWAYS]
    if bad_flags:
        v.reasons.append("forbidden: " + ", ".join(bad_flags))
    v.certified = not v.reasons
    if v.certified:
        v.reasons.append("kernel-checked; statement matches the reference; axioms within "
                         "policy")
    return v


def main(argv: list[str]) -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("manifest", help="corpus manifest JSON, or a single submission .lean")
    ap.add_argument("--module", help="module name for a single submission")
    ap.add_argument("--claims", nargs="*", help="claim ids for a single submission")
    ap.add_argument("--out", help="write the full result JSON here")
    args = ap.parse_args(argv)

    cat = load_catalogue()   # AMPAS_CLAIMS selects the catalogue
    ref_mod = cat["reference_module"]
    trusted = cat["trusted_modules"]
    by_id = {c["id"]: c for c in cat["claims"]}

    results = []
    if args.manifest.endswith(".lean"):
        claims = [by_id[c] for c in (args.claims or [])]
        r = check_submission(Path(args.manifest), args.module or "Solution", claims,
                             ref_mod, trusted)
        results.append(r.to_json())
    else:
        manifest = json.loads(Path(args.manifest).read_text(encoding="utf-8"))
        base = Path(args.manifest).resolve().parent
        for item in manifest["submissions"]:
            if not all(c in by_id for c in item["claims"]):
                # this submission targets another catalogue (e.g. the pinned
                # Mathlib one, which needs its own olean path): run it with
                # AMPAS_CLAIMS and AMPAS_EXTRA_LEAN_PATH set for that catalogue
                continue
            claims = [by_id[c] for c in item["claims"]]
            r = check_submission(base / item["file"], item["module"], claims,
                                 ref_mod, trusted)
            r_json = r.to_json()
            r_json["expected"] = item.get("expected")
            r_json["note"] = item.get("note", "")
            results.append(r_json)
    # ROADMAP 1.1: a verdict that does not name the kernel which issued it
    # cannot be found again after a soundness disclosure. The provenance block
    # goes in the VERDICT record rather than the signed formalization
    # attestation, so adding it needs no re-signing: the attestation is about
    # whether a statement says what a claim says, which no kernel version
    # affects.
    try:
        from provenance import snapshot
        prov = snapshot()
    except Exception as e:                      # never fail a run over metadata
        prov = {"error": f"{type(e).__name__}: {e}"}
    out = {"provenance": prov, "results": results}
    if args.out:
        Path(args.out).write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8", newline="\n")
    print(json.dumps(out, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
