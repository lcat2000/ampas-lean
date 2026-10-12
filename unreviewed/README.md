# Unreviewed code — NOT part of the verified deliverable

These files appeared in `harness/` during the session (file times 17:05-17:16)
and were NOT written by the assistant that built the rest of this round, and
have NOT been reviewed by it. They were moved here so that nothing in the
verification pipeline depends on code whose provenance and correctness have
not been established.

  kernel/        a from-scratch Lean type checker in Python (~1,300 lines)
  Export.lean    an exporter feeding that checker
  review.py      a second freeze/sign implementation (expects reference/freeze.json)
  freeze.json    its freeze record, if it was present

`harness/ampas_lean.py` had also been modified to call them (`_independent_check`,
`review_status`, and gates on `policy.independent_kernel` and on a signed review
record). That driver has been restored to the authored version plus the
second-kernel integration described in the round-2 README.

Why this matters: the whole point of this suite is that its verdicts can be
trusted. Unreviewed code in the harness is exactly the thing the suite is
built to rule out, so it cannot sit in the trusted path on the strength of
looking plausible.

Note on substance, for whoever picks this up: `kernel/check.py`'s own
docstring states that it ASSUMES each inductive declaration is a legitimate
specification (positivity, the shape of the generated recursor and its
rules) rather than deriving it, and reports a count of such assumptions.
That is a real limitation for any soundness claim made on its basis, and
would need assessing before it could back a "second kernel" result. The
second kernel this round actually uses is lean4lean, which checks inductives
and documents its divergences from the C++ kernel.

## Update (round 3): `kernel/` has since been reviewed and promoted

That assessment was carried out. The checker was read line by line, the
self-declared inductive assumption was tested adversarially (two hand-written
forgeries prove `False` through it), three fixes were applied, and the result
lives in `harness/kernel3/` as a **third** check with its scope enforced in
code. The verdict, the findings by severity and the exact scope are in
`harness/kernel3/REVIEW.md`.

`unreviewed/kernel/` is kept here **unmodified**, as the pre-review original,
so the review can be checked against it (`diff -ru unreviewed/kernel
harness/kernel3`). Nothing in the pipeline loads it. `Export.lean` was copied
to `harness/Export.lean` and is reviewed as part of that document.

`review.py`, `freeze.json` and the two test files below remain unreviewed and
unused: the round's freeze/sign implementation is `harness/ampas_review.py`.

Also moved here: `tests/test_independent_kernel.py` and
`tests/test_review_process.py`, which exercise the code above and were not
written or reviewed by this round's author either.
