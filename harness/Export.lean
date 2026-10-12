/-
AMPAS math-verification: environment exporter.

Writes the transitive closure of a set of root constants, in dependency
order, as a flat index-based text format (documented in EXPORT_FORMAT.md).
The point is to hand the SAME declarations the Lean kernel accepted to an
independently written type checker (harness/kernel/), so that acceptance
does not rest on Lean's kernel alone.

Trust note: this exporter reads Lean's `Environment` and serializes it with
Lean's own `Expr`, so a faithful export is trusted. What the independent
checker establishes is that the exported declarations type-check under an
independently implemented version of the type theory. This is the same
trust split as trepplein and nanoda (which also consume a Lean-produced
export).

Usage:
  lean --run Export.lean <module> <out.txt> <root-const> [<root-const>...]
or with no roots: every constant of the module's own environment.
-/
import Lean
open Lean

structure Tables where
  names : Std.HashMap Name Nat := ({} : Std.HashMap Name Nat).insert Name.anonymous 0
  levels : Std.HashMap Level Nat := ({} : Std.HashMap Level Nat).insert Level.zero 0
  exprs : Std.HashMap Expr Nat := {}
  out : Array String := #[]
  deriving Inhabited

abbrev ExM := StateRefT Tables IO

def emit (line : String) : ExM Unit :=
  modify fun t => { t with out := t.out.push line }

partial def putName (n : Name) : ExM Nat := do
  if let some i := (← get).names[n]? then return i
  match n with
  | .anonymous => return 0
  | .str p s =>
    let pi ← putName p                       -- parent first: it may take an index
    let i := (← get).names.size
    modify fun t => { t with names := t.names.insert n i }
    emit s!"{i} #NS {pi} {s}"
    return i
  | .num p k =>
    let pi ← putName p
    let i := (← get).names.size
    modify fun t => { t with names := t.names.insert n i }
    emit s!"{i} #NI {pi} {k}"
    return i

partial def putLevel (l : Level) : ExM Nat := do
  if let some i := (← get).levels[l]? then return i
  match l with
  | .zero => return 0
  | .succ a =>
    let ai ← putLevel a
    let i := (← get).levels.size
    modify fun t => { t with levels := t.levels.insert l i }
    emit s!"{i} #US {ai}"
    return i
  | .max a b =>
    let ai ← putLevel a; let bi ← putLevel b
    let i := (← get).levels.size
    modify fun t => { t with levels := t.levels.insert l i }
    emit s!"{i} #UM {ai} {bi}"
    return i
  | .imax a b =>
    let ai ← putLevel a; let bi ← putLevel b
    let i := (← get).levels.size
    modify fun t => { t with levels := t.levels.insert l i }
    emit s!"{i} #UIM {ai} {bi}"
    return i
  | .param n =>
    let ni ← putName n
    let i := (← get).levels.size
    modify fun t => { t with levels := t.levels.insert l i }
    emit s!"{i} #UP {ni}"
    return i
  | .mvar _ => throw (IO.userError "level metavariable in export")

def binfo : BinderInfo → String
  | .default => "#BD"
  | .implicit => "#BI"
  | .strictImplicit => "#BS"
  | .instImplicit => "#BC"

/-- Hex of the bytes of a string literal, so the format stays ASCII. -/
def hexOf (s : String) : String :=
  String.intercalate " " (s.toUTF8.toList.map fun b =>
    let hi := b / 16; let lo := b % 16
    let d : Nat → String := fun x => if x < 10 then toString x else
      ["a","b","c","d","e","f"][x - 10]!
    d hi.toNat ++ d lo.toNat)

partial def putExpr (e : Expr) : ExM Nat := do
  if let some i := (← get).exprs[e]? then return i
  let mk (line : Nat → String) : ExM Nat := do
    let i := (← get).exprs.size
    modify fun t => { t with exprs := t.exprs.insert e i }
    emit (line i)
    return i
  match e with
  | .bvar k => mk fun i => s!"{i} #EV {k}"
  | .sort l => do let li ← putLevel l; mk fun i => s!"{i} #ES {li}"
  | .const n us => do
    let ni ← putName n
    let uis ← us.mapM putLevel
    mk fun i => s!"{i} #EC {ni}" ++ String.join (uis.map fun u => s!" {u}")
  | .app f a => do let fi ← putExpr f; let ai ← putExpr a; mk fun i => s!"{i} #EA {fi} {ai}"
  | .lam n d b bi => do
    let ni ← putName n; let di ← putExpr d; let bi' ← putExpr b
    mk fun i => s!"{i} #EL {binfo bi} {ni} {di} {bi'}"
  | .forallE n d b bi => do
    let ni ← putName n; let di ← putExpr d; let bi' ← putExpr b
    mk fun i => s!"{i} #EP {binfo bi} {ni} {di} {bi'}"
  | .letE n t v b _ => do
    let ni ← putName n; let ti ← putExpr t; let vi ← putExpr v; let bi' ← putExpr b
    mk fun i => s!"{i} #EZ {ni} {ti} {vi} {bi'}"
  | .proj s k st => do
    let si ← putName s; let sti ← putExpr st
    mk fun i => s!"{i} #EJ {si} {k} {sti}"
  | .lit (.natVal n) => mk fun i => s!"{i} #ELN {n}"
  | .lit (.strVal s) => mk fun i => s!"{i} #ELS {hexOf s}"
  | .mdata _ b => putExpr b          -- metadata is not part of the term
  | .mvar _ => throw (IO.userError "expression metavariable in export")
  | .fvar _ => throw (IO.userError "free variable in export")

def putParams (ps : List Name) : ExM String := do
  let is ← ps.mapM putName
  return s!"{ps.length}" ++ String.join (is.map fun i => s!" {i}")

/-- Constants a declaration depends on (type, value, and the pieces an
inductive family needs), used to emit declarations in dependency order. -/
def deps (env : Environment) (ci : ConstantInfo) (stmtMode : Bool := false) : Array Name :=
  let fromVal := if stmtMode && (ci matches .thmInfo _) then #[] else match ci with
    | .defnInfo v => v.value.getUsedConstants
    | .thmInfo v => v.value.getUsedConstants
    | .opaqueInfo v => v.value.getUsedConstants
    | .recInfo v => v.rules.foldl (fun acc r => acc ++ r.rhs.getUsedConstants) #[]
    | _ => #[]
  let extra := match ci with
    | .inductInfo v => v.all.toArray ++ v.ctors.toArray
    | .ctorInfo v => #[v.induct]
    | .recInfo v => v.all.toArray
    | _ => #[]
  ci.type.getUsedConstants ++ fromVal ++ extra
    |>.filter (fun n => (env.find? n).isSome)

def exportDecl (env : Environment) (n : Name) (stmtMode : Bool := false) : ExM Unit := do
  let some ci := env.find? n | throw (IO.userError s!"unknown constant {n}")
  let ni ← putName n
  let ti ← putExpr ci.type
  let ps ← putParams ci.levelParams
  match ci with
  | .axiomInfo _ => emit s!"#AX {ni} {ti} {ps}"
  | .defnInfo v => do let vi ← putExpr v.value; emit s!"#DEF {ni} {ti} {vi} {ps}"
  | .thmInfo v =>
    if stmtMode then
      emit s!"#THMTYPE {ni} {ti} {ps}"      -- statement mode: proofs are irrelevant
    else do let vi ← putExpr v.value; emit s!"#THM {ni} {ti} {vi} {ps}"
  | .opaqueInfo v => do let vi ← putExpr v.value; emit s!"#OPAQ {ni} {ti} {vi} {ps}"
  | .quotInfo _ => emit s!"#QUOT {ni} {ti} {ps}"
  | .inductInfo v => do
    let ctors ← v.ctors.mapM putName
    let alls ← v.all.mapM putName
    emit (s!"#IND {ni} {ti} {v.numParams} {v.numIndices} " ++
          s!"{if v.isRec then 1 else 0} {if v.isReflexive then 1 else 0} " ++
          s!"{alls.length}" ++ String.join (alls.map fun a => s!" {a}") ++
          s!" {ctors.length}" ++ String.join (ctors.map fun c => s!" {c}") ++ s!" {ps}")
  | .ctorInfo v => do
    let ii ← putName v.induct
    emit s!"#CTOR {ni} {ti} {ii} {v.cidx} {v.numParams} {v.numFields} {ps}"
  | .recInfo v => do
    let alls ← v.all.mapM putName
    let mut ruleStrs := #[]
    for r in v.rules do
      let ci' ← putName r.ctor
      let rhsi ← putExpr r.rhs
      ruleStrs := ruleStrs.push s!"{ci'} {r.nfields} {rhsi}"
    emit (s!"#REC {ni} {ti} {v.numParams} {v.numIndices} {v.numMotives} {v.numMinors} " ++
          s!"{if v.k then 1 else 0} {alls.length}" ++
          String.join (alls.map fun a => s!" {a}") ++
          s!" {v.rules.length}" ++ String.join (ruleStrs.toList.map fun s => s!" {s}") ++
          s!" {ps}")

/-- Dependency-ordered closure of the roots. -/
partial def order (env : Environment) (roots : Array Name) (stmtMode : Bool := false)
    : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut stack : Array (Name × Bool) := roots.reverse.map (·, false)
  while !stack.isEmpty do
    let (n, expanded) := stack.back!
    stack := stack.pop
    if expanded then
      if !seen.contains n then
        seen := seen.insert n
        out := out.push n
      continue
    if seen.contains n then continue
    if stack.any (fun (m, e) => m == n && e) then continue
    let some ci := env.find? n | continue
    stack := stack.push (n, true)
    for d in deps env ci stmtMode do
      if !seen.contains d then stack := stack.push (d, false)
  return out

/-- Is this an *assumed* declaration — one whose specification the Python
checker believes rather than derives (see harness/kernel3/REVIEW.md F-2)? -/
def isSpec : ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => true
  | _ => false

unsafe def main (args : List String) : IO UInt32 := do
  let (specMode, args) :=
    match args with
    | "--specs" :: rest => (true, rest)
    | _ => (false, args)
  let (stmtMode, args) :=
    match args with
    | "--statement" :: rest => (true, rest)
    | _ => (false, args)
  let (mod, outPath, roots) ← match args with
    | m :: o :: rs => pure (m.toName, o, rs.map String.toName)
    | _ => throw (IO.userError
        "usage: Export.lean [--statement] <module> <out> [roots...]")
  initSearchPath (← findSysroot)
  -- a module that imports Lean itself needs the private-level oleans, which
  -- some toolchain builds do not ship; fall back to the exported level
  let env ←
    try
      importModules #[{ module := mod }] {} (loadExts := false)
    catch _ =>
      importModules #[{ module := mod }] {} (loadExts := false) (level := OLeanLevel.exported)
  -- --specs: every assumed declaration of the whole environment (imported
  -- modules live in map₁, the module's own in map₂), with NO dependency
  -- closure. This is the baseline of what the trusted core already assumes;
  -- fingerprinting a declaration needs its own type and rules, not the
  -- definitions those mention.
  if specMode then
    let mut specs : Array Name := #[]
    for (n, ci) in env.constants.map₁.toList do
      if isSpec ci then specs := specs.push n
    specs := env.constants.map₂.foldl
      (fun acc n ci => if isSpec ci then acc.push n else acc) specs
    specs := specs.qsort (fun a b => toString a < toString b)
    let (_, tables) ← (do for n in specs do exportDecl env n) |>.run (default : Tables)
    let header := s!"#VERSION 1\n#MODE specs\n#MODULE {mod}\n#ROOTS\n"
    IO.FS.writeFile outPath (header ++ String.intercalate "\n" tables.out.toList ++ "\n")
    IO.println s!"exported {specs.size} assumed declarations to {outPath}"
    return 0
  let rootArr : Array Name :=
    if roots.isEmpty then
      -- every constant declared by the module itself
      env.constants.map₂.foldl (fun acc n _ => acc.push n) #[]
    else roots.toArray
  let ordered := order env rootArr stmtMode
  let (_, tables) ← (do
    for n in ordered do exportDecl env n stmtMode
    ) |>.run (default : Tables)
  let header := s!"#VERSION 1\n#MODE {if stmtMode then "statement" else "proof"}\n" ++
    s!"#MODULE {mod}\n#ROOTS " ++
    String.intercalate " " (rootArr.toList.map toString) ++ "\n"
  IO.FS.writeFile outPath (header ++ String.intercalate "\n" tables.out.toList ++ "\n")
  IO.println s!"exported {ordered.size} declarations, {tables.out.size} lines to {outPath}"
  return 0
