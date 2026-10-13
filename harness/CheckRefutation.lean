/-
AMPAS: check a generated refutation against the statement it claims to refute.

A refutation is a Lean term proving `¬ P`. On its own, that the file compiles
establishes only that SOME proposition was refuted -- and the external
validation pair is the standing demonstration of why that is not enough:
`FermatWeaker` compiles, uses no `sorry`, satisfies both kernels, and proves a
statement adjacent to the one it is filed under. A refutation has exactly the
same failure mode, so the same check applies to it:

  1. the refutation's type must be `Not` applied to the frozen statement's
     type -- compared structurally, and (reported separately) up to kernel
     definitional equality;
  2. the refutation's own axioms must be within policy, and `sorryAx` in
     particular would make it worthless;
  3. its statement must mention no constant the trusted reference does not
     already define, so a refutation cannot smuggle in its own version of
     `Derives`.

Usage:
  lean --run CheckRefutation.lean <request.json>

Request: {"reference_module": "AmpasRef.Challenge",
          "frozen_decl": "Ampas.Claims.pl_bogus_independent",
          "refutation_module": "PL_BOGUS_refutation",
          "refutation_decl": "Ampas.Refutations.pl_bogus_refuted"}
-/
import Lean
open Lean

namespace Ampas.CheckRef

def jstr (s : String) : Json := Json.str s

/-- Every constant a declaration's TYPE mentions (not its proof). -/
partial def typeConsts (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => typeConsts a (typeConsts f acc)
  | .lam _ d b _ => typeConsts b (typeConsts d acc)
  | .forallE _ d b _ => typeConsts b (typeConsts d acc)
  | .letE _ t v b _ => typeConsts b (typeConsts v (typeConsts t acc))
  | .mdata _ b => typeConsts b acc
  | .proj n _ b => typeConsts b (acc.insert n)
  | _ => acc

/-- The axioms a proof transitively rests on. -/
partial def axiomsOf (env : Environment) (n : Name) : NameSet :=
  go n {} |>.1
where
  go (n : Name) (seen : NameSet) : NameSet × NameSet :=
    if seen.contains n then ({}, seen) else
    let seen := seen.insert n
    match env.find? n with
    | none => ({}, seen)
    | some ci =>
      let acc := if ci matches .axiomInfo _ then ({} : NameSet).insert n else {}
      let deps := (ci.type.getUsedConstants ++
                   (ci.value?.map Expr.getUsedConstants |>.getD #[]))
      deps.foldl (fun (a, s) d =>
        let (a', s') := go d s
        (a'.toList.foldl (fun x y => x.insert y) a, s')) (acc, seen)

unsafe def main (args : List String) : IO UInt32 := do
  let some reqPath := args.head? | do
    IO.eprintln "usage: lean --run CheckRefutation.lean <request.json>"; return 1
  let req ← match Json.parse (← IO.FS.readFile reqPath) with
    | .ok j => pure j
    | .error e => do IO.eprintln s!"bad request: {e}"; return 1
  let getStr (k : String) : IO String := match req.getObjValAs? String k with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"request field {k}: {e}")
  let refMod := (← getStr "reference_module").toName
  let frozen := (← getStr "frozen_decl").toName
  let refutMod := (← getStr "refutation_module").toName
  let refutDecl := (← getStr "refutation_decl").toName

  initSearchPath (← findSysroot)
  -- The refutation is GENERATED code, so its initializers are not run: the
  -- same rule the auditor applies to a submission applies here.
  let env ← importModules #[{ module := refMod }, { module := refutMod }] {}
      (loadExts := false)

  let some fci := env.find? frozen
    | do IO.println (Json.mkObj [("error", jstr s!"no such frozen declaration: {frozen}")]).compress
         return 1
  let some rci := env.find? refutDecl
    | do IO.println (Json.mkObj [("error", jstr s!"no such refutation: {refutDecl}")]).compress
         return 1

  -- 1. the refutation must negate exactly the frozen statement
  let expected := mkApp (mkConst ``Not) fci.type
  let structural := rci.type == expected
  let defeq := match Kernel.isDefEq env {} rci.type expected with
    | .ok b => b
    | .error _ => false

  -- 2. what the refutation rests on
  let axs := (axiomsOf env refutDecl).toList.map toString |>.toArray.qsort (· < ·)
  let isThm := rci matches .thmInfo _

  -- 3. its statement may mention only constants the trusted reference has
  let refEnv ← importModules #[{ module := refMod }] {} (loadExts := false)
  let foreign := (typeConsts rci.type).toList.filter (fun n =>
    !(refEnv.contains n) && n != ``Not)

  IO.println (Json.mkObj [
    ("frozen_decl", jstr frozen.toString),
    ("refutation_decl", jstr refutDecl.toString),
    ("is_theorem", Json.bool isThm),
    ("negates_frozen_statement_structurally", Json.bool structural),
    ("negates_frozen_statement_up_to_defeq", Json.bool defeq),
    ("axioms", Json.arr (axs.map jstr)),
    ("uses_sorry", Json.bool (axs.contains "sorryAx")),
    ("foreign_statement_constants",
      Json.arr ((foreign.map (fun n => jstr n.toString)).toArray))]).compress
  return 0

end Ampas.CheckRef

unsafe def main (args : List String) : IO UInt32 := Ampas.CheckRef.main args
