-- Attack: with debug.skipKernelTC the elaborator adds a declaration WITHOUT
-- the kernel type-check. Add `false_thm : False` with the proof `True.intro`
-- (ill-typed; the kernel would reject it), then derive the target from it.
-- The file compiles; leanchecker must reject it at kernel replay.
import AmpasRef.Defs
import Lean
open Lean Elab Command
namespace Ampas.Claims
set_option debug.skipKernelTC true in
run_cmd liftCoreM do
  let v : TheoremVal := { name := `Ampas.Claims.false_thm, levelParams := [],
                          type := mkConst ``False, value := mkConst ``True.intro }
  addDecl (.thmDecl v)
theorem add_comm_nat : ∀ a b : Nat, a + b = b + a := fun _ _ => (false_thm).elim
end Ampas.Claims
