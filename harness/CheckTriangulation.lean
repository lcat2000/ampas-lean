/-
AMPAS: check that an equivalence relates the two statements it claims to.

A theorem of type `A ↔ B` establishes nothing about a claim unless A and B
are the two statements on record. An `Iff` between two other propositions
compiles just as well -- the `FermatWeaker` failure mode, pointed at
equivalences instead of proofs -- so both sides are resolved from the
environment BY NAME and compared against the theorem's actual type.

Reported, not decided here, because the driver records them and
ASSUMPTIONS A1d says what they are worth:

  * whether the type is `Iff` applied to exactly those two statements,
    structurally and up to kernel definitional equality;
  * the axioms the proof rests on, and whether `sorryAx` is among them;
  * whether the proof is TRIVIAL in the sense that matters: if both sides are
    independently provable then the equivalence is vacuous, so the check also
    reports whether each side is itself a proved theorem in this environment.
    An equivalence between two theorems tells a reader nothing about meaning,
    and a record that does not say so invites exactly the wrong reading.

Usage:
  lean --run CheckTriangulation.lean <request.json>

Request: {"module": "AmpasRef.Triangulation",
          "equiv_decl": "Ampas.Triangulation.even_equiv",
          "left": "Ampas.Claims.even_add_even",
          "right": "Ampas.Alt.even_add_even_mod"}
-/
import Lean
open Lean

namespace Ampas.CheckTri

def jstr (s : String) : Json := Json.str s

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

/-- A declaration that is a theorem with a proof is "independently proved":
if both sides of an equivalence are, the equivalence is vacuous. A `sorry`
stub -- which is how the frozen reference statements are written -- does not
count, so the frozen side is correctly reported as NOT proved. -/
def provedHere (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo ti) => !ti.value.hasSorry
  | _ => false

unsafe def main (args : List String) : IO UInt32 := do
  let some reqPath := args.head? | do
    IO.eprintln "usage: lean --run CheckTriangulation.lean <request.json>"; return 1
  let req ← match Json.parse (← IO.FS.readFile reqPath) with
    | .ok j => pure j
    | .error e => do IO.eprintln s!"bad request: {e}"; return 1
  let getStr (k : String) : IO String := match req.getObjValAs? String k with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"request field {k}: {e}")
  let mod := (← getStr "module").toName
  let equiv := (← getStr "equiv_decl").toName
  let leftN := (← getStr "left").toName
  let rightN := (← getStr "right").toName

  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := mod }] {} (loadExts := false)

  let fetch (n : Name) : IO ConstantInfo := do
    match env.find? n with
    | some ci => pure ci
    | none => throw (IO.userError s!"no such declaration: {n}")
  let eci ← fetch equiv
  let lci ← fetch leftN
  let rci ← fetch rightN

  let expected := mkApp2 (mkConst ``Iff) lci.type rci.type
  let structural := eci.type == expected
  let defeq := match Kernel.isDefEq env {} eci.type expected with
    | .ok b => b | .error _ => false
  let axs := (axiomsOf env equiv).toList.map toString |>.toArray.qsort (· < ·)
  let lProved := provedHere env leftN
  let rProved := provedHere env rightN

  IO.println (Json.mkObj [
    ("equiv_decl", jstr equiv.toString),
    ("left", jstr leftN.toString),
    ("right", jstr rightN.toString),
    ("is_theorem", Json.bool (eci matches .thmInfo _)),
    ("relates_the_named_statements", Json.bool structural),
    ("relates_up_to_defeq", Json.bool defeq),
    ("axioms", Json.arr (axs.map jstr)),
    ("uses_sorry", Json.bool (axs.contains "sorryAx")),
    -- Whether each side is proved IN THIS MODULE. This is a weaker test than
    -- vacuity and must not be read as its negation: the equivalence is
    -- vacuous whenever both sides are TRUE, wherever that truth is
    -- established. EVEN's frozen side is a `sorry` stub here while the corpus
    -- contains a kernel-checked proof of it, so `both_proved_here: false`
    -- and the equivalence is vacuous all the same. The honest reading is in
    -- ASSUMPTIONS A1d; `Ampas.Triangulation.indistinguishable` proves the
    -- general point.
    ("left_proved_here", Json.bool lProved),
    ("right_proved_here", Json.bool rProved),
    ("both_proved_here", Json.bool (lProved && rProved))]).compress
  return 0

end Ampas.CheckTri

unsafe def main (args : List String) : IO UInt32 := Ampas.CheckTri.main args
