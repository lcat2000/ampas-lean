# Building the auditor executable

Audit.lean is compiled to C by Lean and linked against the Lean shared
runtime. From a checkout with Lean 4.33.0 on PATH:

    cd harness
    lean -c Audit.c Audit.lean
    L=<lean-sysroot>        # e.g. /home/claude/tools/lean4
    gcc -O1 -fPIC -I $L/include Audit.c -o audit \
        -L $L/lib/lean -lleanshared -Wl,-rpath,$L/lib/lean \
        /lib/x86_64-linux-gnu/libgmp.so.10 /lib/x86_64-linux-gnu/libuv.so.1 \
        -lstdc++ -lm -ldl -pthread

`leanc` would normally link this, but its bundled C compiler
(x86_64-conda-linux-gnu-cc) is absent here, so we link with the system gcc
and the system gmp/libuv shared libraries. The auditor also runs under
`lean --run harness/Audit.lean <req.json>` with no build step, about 3x
slower; the driver uses the compiled binary when AMPAS_AUDIT_BIN points to it.

# The third check (harness/kernel3) and its baseline

No build step: it is pure Python and runs in-process from the driver when
`AMPAS_THIRD_CHECK=1`. Its scope, findings and the conditions under which it
may be used are in `harness/kernel3/REVIEW.md` — read that before relying on
a result from it.

The exporter that feeds it is `harness/Export.lean`, run through
`lean --run` (no build step either). Three modes:

    lean --run harness/Export.lean <module> <out> [roots...]   # proof closure
    lean --run harness/Export.lean --statement <module> <out> [roots...]
    lean --run harness/Export.lean --specs <module> <out>      # assumed decls

The provenance baseline must be regenerated whenever the trusted reference
or the toolchain changes, otherwise legitimate declarations are reported as
introduced assumptions:

    LEAN_PATH=$PWD/build \
      python3 harness/make_baseline.py reference/kernel_baseline.json \
        AmpasRef.Guards AmpasRef.Challenge

    LEAN_PATH=$PWD/build-mathlib:$PWD/build:<mathlib libs> \
      python3 harness/make_baseline.py reference/kernel_baseline_mathlib.json \
        AmpasRef.ChallengeMathlib

Note on limits: `lean --run` loads the whole Lean library plus the
interpreter, and RLIMIT_AS caps *address space* rather than resident memory,
so the export step runs under `AMPAS_EXPORT_MEM_BYTES` (24 GB by default)
instead of the submission limit (10 GB). At 10 GB the exporter fails while
mmapping a toolchain olean. CPU time, wall clock, file size and the
unprivileged sandbox user still apply, and the exporter only reads.
