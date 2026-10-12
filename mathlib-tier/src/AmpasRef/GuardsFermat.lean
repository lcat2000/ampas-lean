/-
Review guards for the Fermat pair. Kernel-checked like any other theorem.

FERMAT-F5 is a refutation (its conclusion is False), so the non-vacuity and
necessity guards do not apply; the auditor requires a nontriviality guard
instead. The degenerate reading to rule out is "¬ Nat.Prime X is trivial
because Nat.Prime holds of nothing" -- or, worse for this particular claim,
"Nat.Prime holds of no Fermat number", which would make Euler's result
uninteresting rather than the sharp counterexample it is.

The guard therefore shows that ANOTHER Fermat number IS prime: F3 = 257.
That is exactly the shape of the historical situation -- F0..F4 prime, F5
composite -- so the guard rules out the degenerate reading with the same
evidence Fermat himself had.

(F4 = 65537 would be the sharpest guard, being the last case Fermat checked,
but `decide` on it does not finish inside this suite's kernel limits: the
decidability instance tries every divisor. F3 makes the same point.)
-/
import AmpasRef.ChallengeFermat

namespace Ampas.Guards

-- Nontriviality for FERMAT-F5: `Nat.Prime` is not degenerate on Fermat
-- numbers -- F3 = 2^(2^3) + 1 = 257 is prime. So `¬ Nat.Prime (2^(2^5) + 1)`
-- is a statement about F5 specifically, not about the predicate being empty.
set_option maxRecDepth 10000

theorem fermat_nontrivial : Nat.Prime (2 ^ (2 ^ 3) + 1) := by decide

end Ampas.Guards
