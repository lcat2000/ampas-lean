/-
AMPAS math-verification round 1: the auditor.

Run as `lean --run harness/Audit.lean <request.json>` with LEAN_PATH set to
the compiled reference and submission modules. It loads the reference
environment and the submission environment separately and reports facts as
JSON on standard output; the Python driver (harness/ampas_lean.py) turns the
facts into a verdict under the claim's policy. Kernel checking itself is
not done here: the driver runs `leanchecker`, which replays every
declaration of the submission through the kernel.

Facts reported, for each theorem the request names:
  * whether the submission declares it, and as what (theorem, axiom, ...);
  * statement: the reference statement and the submitted one compared
    structurally (alpha-equivalence, Expr.eqv) and, when every constant the
    reference statement depends on means the same in both environments, by
    the kernel's definitional equality in the submission's environment;
    the constants whose meaning differs, or that are missing, are listed
    (closure check);
  * axioms: every axiom the submitted theorem depends on, found by walking
    its type and proof and every constant they use, transitively;
  * dependencies: every constant used that comes from a module outside the
    trusted ones (the submission's own lemmas, other imports);
  * flags: native evaluation (Lean.ofReduceBool, Lean.ofReduceNat,
    Lean.trustCompiler), sorryAx, opaque constants in the statement,
    partial / unsafe constants reached. (implemented_by and extern are
    attributes, stored in environment extensions; the submission's
    environment is loaded without extensions, so that none of its code runs
    here, and they matter for the kernel only through native evaluation,
    which is flagged.)

Request mode "sanity" checks the reference itself: a non-vacuity witness
(the hypotheses of the statement can hold together) and, for each
hypothesis, a proof that the statement without it is false.
-/
import Lean
open Lean Meta

def jstr (s : String) : Json := Json.str s
def jarr (xs : List Json) : Json := Json.arr xs.toArray
def jnames (xs : List Name) : Json := jarr (xs.map fun n => jstr n.toString)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Constants a declaration mentions directly: its type, its value (for
definitions, theorems, opaque constants) and, for an inductive type, its
constructors and recursors (so that their types are compared too). -/
def directConsts (ci : ConstantInfo) (withValue : Bool := true) : Array Name :=
  let fromType := ci.type.getUsedConstants
  let fromValue := if withValue then
      match ci with
      | .defnInfo v => v.value.getUsedConstants
      | .thmInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | _ => #[]
    else #[]
  let extra := match ci with
    | .inductInfo v => (v.ctors ++ v.all).toArray ++ #[mkRecName v.name]
    | .ctorInfo v => #[v.induct]
    | .recInfo v => v.all.toArray
    | _ => #[]
  fromType ++ fromValue ++ extra

/-- Every constant reachable from the roots, following types and values
(theorem proofs too when `proofs`), in the given environment. Names the
environment does not know are returned separately. -/
partial def closure (env : Environment) (roots : Array Name) (proofs : Bool) :
    NameSet × NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut missing : NameSet := {}
  let mut todo := roots.toList
  while !todo.isEmpty do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n || missing.contains n then continue
      match env.find? n with
      | none => missing := missing.insert n
      | some ci =>
        seen := seen.insert n
        let withValue := match ci with
          | .thmInfo _ => proofs
          | _ => true
        todo := (directConsts ci withValue).toList ++ todo
  return (seen, missing)

/-- Two declarations mean the same: same kind, universe parameters and type,
and (for definitions and opaque constants) the same value; for an inductive
type the same parameters, indices and constructors. Theorems are compared by
type (proof irrelevance). -/
def sameMeaning (a b : ConstantInfo) : Bool :=
  kindOf a == kindOf b && a.levelParams == b.levelParams && a.type == b.type &&
  match a, b with
  | .defnInfo x, .defnInfo y => x.value == y.value
  | .opaqueInfo x, .opaqueInfo y => x.value == y.value
  | .inductInfo x, .inductInfo y =>
      x.numParams == y.numParams && x.numIndices == y.numIndices && x.ctors == y.ctors
  | .ctorInfo x, .ctorInfo y => x.induct == y.induct && x.cidx == y.cidx
  | _, _ => true

def nativeAxioms : List Name := [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

def ppIn (env : Environment) (e : Expr) : IO String := do
  try
    let ctx : Core.Context := { fileName := "<audit>", fileMap := default,
                                options := ({} : Options) }
    let (fmt, _) ← (PrettyPrinter.ppExpr e).run' {} {} |>.toIO ctx { env := env }
    return toString fmt
  catch _ => return toString e

def kernelDefEq (env : Environment) (a b : Expr) : Json :=
  match Kernel.isDefEq env {} a b with
  | .ok r => Json.bool r
  | .error _ => Json.null

/-! ### Structural serialization (mode "freeze")

A canonical, explicit rendering of an `Expr` and of a declaration, used to
freeze a reference statement by content rather than by source text. It walks
every constructor itself, so the freeze does not depend on the pretty
printer, on binder *names* being insignificant, or on any Lean version's
`ToString`. The driver hashes these strings; reformatting the reference
source cannot change them, and changing a definition the statement rests on
must change them.
-/

def serLevel : Level → String
  | .zero => "0"
  | .succ l => s!"(S {serLevel l})"
  | .max a b => s!"(max {serLevel a} {serLevel b})"
  | .imax a b => s!"(imax {serLevel a} {serLevel b})"
  | .param n => s!"(param {n})"
  | .mvar _ => "(mvar)"

def serBI : BinderInfo → String
  | .default => "d" | .implicit => "i"
  | .strictImplicit => "si" | .instImplicit => "ii"

partial def serExpr : Expr → String
  | .bvar i => s!"(bvar {i})"
  | .fvar id => s!"(fvar {id.name})"
  | .mvar _ => "(mvar)"
  | .sort l => s!"(sort {serLevel l})"
  | .const n ls => s!"(const {n} [{String.intercalate " " (ls.map serLevel)}])"
  | .app f a => s!"(app {serExpr f} {serExpr a})"
  -- binder names are NOT serialized: alpha-equivalent statements freeze alike
  | .lam _ t b bi => s!"(lam {serBI bi} {serExpr t} {serExpr b})"
  | .forallE _ t b bi => s!"(all {serBI bi} {serExpr t} {serExpr b})"
  | .letE _ t v b _ => s!"(let {serExpr t} {serExpr v} {serExpr b})"
  | .lit (.natVal n) => s!"(nat {n})"
  | .lit (.strVal v) => s!"(str {v.quote})"
  | .mdata _ e => serExpr e            -- metadata carries no logical content
  | .proj n i e => s!"(proj {n} {i} {serExpr e})"

/-- The logical content of a declaration: kind, universe parameters, type,
and the value for anything whose value matters definitionally (a theorem's
proof does not: proof irrelevance). For an inductive type, its arity and
constructor names. -/
def serDecl (ci : ConstantInfo) : String :=
  let head := s!"{kindOf ci} [{String.intercalate " " (ci.levelParams.map toString)}] {serExpr ci.type}"
  match ci with
  | .defnInfo v => s!"{head} := {serExpr v.value}"
  | .opaqueInfo v => s!"{head} := {serExpr v.value}"
  | .thmInfo _ => head                 -- proof irrelevance: the proof is not frozen
  | .axiomInfo _ => head
  | .inductInfo v =>
      s!"{head} params={v.numParams} indices={v.numIndices} ctors=[{String.intercalate " " (v.ctors.map toString)}]"
  | .ctorInfo v => s!"{head} of={v.induct} idx={v.cidx}"
  | .recInfo v => s!"{head} rules={v.rules.length}"
  | .quotInfo _ => head

structure TheoremReport where
  json : Json

def auditTheorem (refEnv solEnv : Environment) (trusted : List Name) (n : Name)
    (defeq : Bool) : IO Json := do
  let isTrusted (m : Name) : Bool := trusted.any (fun t => t.isPrefixOf m)
  let refCI? := refEnv.find? n
  let solCI? := solEnv.find? n
  let some refCI := refCI?
    | return Json.mkObj [("name", jstr n.toString), ("error", jstr "not in the reference")]
  let some solCI := solCI?
    | return Json.mkObj [("name", jstr n.toString), ("found", Json.bool false)]
  -- closure check: every constant the reference statement depends on, through
  -- definitions, means the same in the submission's environment
  let (refClosure, _) := closure refEnv refCI.type.getUsedConstants false
  let mut differing : List Name := []
  let mut missing : List Name := []
  for c in refClosure.toList do
    match solEnv.find? c with
    | none => missing := c :: missing
    | some sc =>
      let rc := (refEnv.find? c).get!
      if !(sameMeaning rc sc) || moduleOf refEnv c != moduleOf solEnv c then
        differing := c :: differing
  let closureOk := differing.isEmpty && missing.isEmpty
  -- constants the submitted statement uses that the reference statement does not
  let (solTypeClosure, _) := closure solEnv solCI.type.getUsedConstants false
  let extraInStatement := solTypeClosure.toList.filter (fun c => !refClosure.contains c)
  let strictEq := refCI.type == solCI.type && refCI.levelParams == solCI.levelParams
  let kdefeq := if closureOk && refCI.levelParams == solCI.levelParams
    then kernelDefEq solEnv refCI.type solCI.type else Json.null
  -- axioms and dependencies of the submitted theorem (type and proof)
  let (solClosure, solMissing) := closure solEnv #[n] true
  let mut axioms : List Name := []
  let mut untrusted : List Json := []
  let mut flags : List String := []
  for c in solClosure.toList do
    let ci := (solEnv.find? c).get!
    let m := moduleOf solEnv c
    if let .axiomInfo _ := ci then axioms := c :: axioms
    if !isTrusted m && c != n then
      untrusted := Json.mkObj [("name", jstr c.toString), ("module", jstr m.toString),
                               ("kind", jstr (kindOf ci))] :: untrusted
    if ci.isUnsafe then flags := s!"UNSAFE:{c}" :: flags
    if ci.isPartial then flags := s!"PARTIAL:{c}" :: flags
  for a in axioms do
    let an := a.toString
    if nativeAxioms.contains a || (an.splitOn "ofReduce").length > 1 || (an.splitOn "native_decide").length > 1
        || (an.splitOn "trustCompiler").length > 1 then
      flags := s!"NATIVE_EVALUATION:{a}" :: flags
    if a == ``sorryAx then flags := "SORRY" :: flags
  for c in refClosure.toList do
    if let some (.opaqueInfo _) := refEnv.find? c then
      flags := s!"OPAQUE_IN_STATEMENT:{c}" :: flags
  let refPP ← ppIn refEnv refCI.type
  let solPP ← ppIn solEnv solCI.type
  return Json.mkObj [
    ("name", jstr n.toString),
    ("found", Json.bool true),
    ("kind", jstr (kindOf solCI)),
    ("reference_kind", jstr (kindOf refCI)),
    ("module", jstr (moduleOf solEnv n).toString),
    ("statement", Json.mkObj [
      ("strict_equal", Json.bool strictEq),
      ("kernel_defeq", kdefeq),
      ("closure_ok", Json.bool closureOk),
      ("closure_differing", jnames differing.reverse),
      ("closure_missing", jnames missing.reverse),
      ("extra_constants", jnames extraInStatement),
      ("reference_pp", jstr refPP),
      ("solution_pp", jstr solPP)]),
    ("axioms", jnames (axioms.toArray.qsort Name.lt).toList),
    ("missing_constants", jnames solMissing.toList),
    ("untrusted_dependencies", jarr untrusted.reverse),
    ("flags", jarr ((flags.toArray.qsort (· < ·)).toList.map jstr))]

/-! ### Reference sanity (mode "sanity") -/

/-- The statement's binders, split into data and hypotheses (binders whose
type is a proposition). -/
def hypothesesOf (stmt : Expr) : MetaM (Array Expr × Array Expr × Expr) := do
  forallTelescopeReducing stmt fun xs body => do
    let mut data := #[]
    let mut hyps := #[]
    for x in xs do
      if ← isProp (← inferType x) then hyps := hyps.push x else data := data.push x
    -- abstract to closed terms
    return (data, hyps, body)

/-- ∃ data, h₁ ∧ ... ∧ hₖ for the statement's hypotheses (None if there
are none, or if a hypothesis is a dependency of another binder). -/
def witnessType (stmt : Expr) : MetaM (Option Expr) := do
  forallTelescopeReducing stmt fun xs _ => do
    let mut data := #[]
    let mut hypTys := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then hypTys := hypTys.push t else data := data.push x
    if hypTys.isEmpty then return none
    let mut conj := hypTys.back!
    for t in hypTys.pop.reverse do
      conj := mkApp2 (mkConst ``And) t conj
    -- hypotheses must not be used by later binders or the conclusion type
    let mut e := conj
    for x in data.reverse do
      let ty ← inferType x
      let lvl ← getLevel ty
      e := mkApp2 (mkConst ``Exists [lvl]) ty (← mkLambdaFVars #[x] e)
    return some e

/-- For hypothesis i: ¬ (the statement with hypothesis i removed), or None
if a later binder or the conclusion depends on it. -/
def withoutHypothesis (stmt : Expr) (i : Nat) : MetaM (Option Expr) := do
  forallTelescopeReducing stmt fun xs body => do
    let mut hypIdx := 0
    let mut keep := #[]
    let mut dropped : Option Expr := none
    for x in xs do
      if ← isProp (← inferType x) then
        if hypIdx == i then dropped := some x else keep := keep.push x
        hypIdx := hypIdx + 1
      else keep := keep.push x
    let some h := dropped | return none
    if body.containsFVar h.fvarId! then return none
    for k in keep do
      if (← inferType k).containsFVar h.fvarId! then return none
    let s ← mkForallFVars keep body
    return some (mkApp (mkConst ``Not) s)

/-- A statement whose conclusion is `False` refutes its hypothesis rather
than asserting something under it. Demanding a non-vacuity witness there
would demand a proof of the very thing being refuted, and dropping the
"hypothesis" leaves `False` itself; so neither guard applies. -/
def isRefutation (stmt : Expr) : MetaM Bool := do
  forallTelescopeReducing stmt fun _ body => do
    return body.isConstOf ``False

def countHyps (stmt : Expr) : MetaM Nat := do
  let (_, hyps, _) ← hypothesesOf stmt
  return hyps.size

def runMeta (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<audit>", fileMap := default, options := {} }
  let (a, _) ← (x.run' {} {}).toIO ctx { env := env }
  return a

def sanityTheorem (env : Environment) (n : Name) (witness : Option Name)
    (necessity : List Name) : IO Json := do
  let some ci := env.find? n | return Json.mkObj [("name", jstr n.toString), ("error", jstr "missing")]
  if ← runMeta env (isRefutation ci.type) then
    -- the claim denies its antecedent; see `isRefutation`
    let nt := (necessity.head?).map (·.toString)
    return Json.mkObj [("name", jstr n.toString), ("hypotheses", Json.num 0),
                       ("non_vacuity", jstr "REFUTATION"),
                       ("necessity", jarr []),
                       ("expected_witness", jstr ""), ("expected_necessity", jarr []),
                       ("refutation", Json.bool true),
                       ("nontriviality_cited", match nt with
                          | some x => jstr x | none => Json.null)]
  let nh ← runMeta env (countHyps ci.type)
  let expected ← runMeta env (witnessType ci.type)
  let expectedWitnessPP ← match expected with
    | some e => ppIn env e
    | none => pure ""
  let witnessJson : Json ← match expected, witness with
    | none, _ => pure (jstr "NO_HYPOTHESES")
    | some _, none => pure (jstr "MISSING")
    | some e, some w =>
      match env.find? w with
      | none => pure (jstr "MISSING")
      | some wci =>
        let ok := match Kernel.isDefEq env {} e wci.type with | .ok r => r | .error _ => false
        pure (jstr (if ok && kindOf wci == "theorem" then "OK" else "MISMATCH"))
  let mut nec : List Json := []
  for i in [0:nh] do
    let expectedNeg ← runMeta env (withoutHypothesis ci.type i)
    let status : String := match expectedNeg, necessity[i]? with
      | none, _ => "DEPENDENT"
      | some _, none => "MISSING"
      | some e, some t =>
        match env.find? t with
        | none => "MISSING"
        | some tci =>
          let ok := match Kernel.isDefEq env {} e tci.type with | .ok r => r | .error _ => false
          if ok && kindOf tci == "theorem" then "OK" else "MISMATCH"
    nec := jstr status :: nec
  let mut necPP : List Json := []
  for i in [0:nh] do
    match ← runMeta env (withoutHypothesis ci.type i) with
    | some e => necPP := jstr (← ppIn env e) :: necPP
    | none => necPP := jstr "" :: necPP
  return Json.mkObj [("name", jstr n.toString), ("hypotheses", Json.num nh),
                     ("non_vacuity", witnessJson), ("necessity", jarr nec.reverse),
                     ("expected_witness", jstr expectedWitnessPP),
                     ("expected_necessity", jarr necPP.reverse)]

/-! ### main -/

def getStr (j : Json) (k : String) : IO String :=
  match j.getObjValAs? String k with
  | .ok s => pure s
  | .error e => throw (IO.userError s!"request: {k}: {e}")

def getStrs (j : Json) (k : String) : List String :=
  match j.getObjValAs? (Array String) k with
  | .ok a => a.toList
  | .error _ => []

unsafe def main (args : List String) : IO UInt32 := do
  let [reqPath] := args | throw (IO.userError "usage: Audit.lean <request.json>")
  let req ← match Json.parse (← IO.FS.readFile reqPath) with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"request: {e}")
  initSearchPath (← findSysroot)
  -- the reference (trusted) is loaded with its extensions, for printing
  enableInitializersExecution
  let mode := (req.getObjValAs? String "mode").toOption.getD "audit"
  let trusted := (getStrs req "trusted_modules").map String.toName
  if mode == "freeze" then
    let refEnv ← importModules #[{ module := (← getStr req "reference_module").toName }] {}
      (loadExts := true)
    let mut out := #[]
    for nstr in getStrs req "theorems" do
      let n := nstr.toName
      match refEnv.find? n with
      | none => out := out.push (Json.mkObj [("name", jstr nstr), ("error", jstr "missing")])
      | some ci =>
        -- the statement, and every constant it rests on, with its own content
        let (cl, missing) := closure refEnv ci.type.getUsedConstants false
        let names := (cl.toArray.qsort Name.lt).toList
        let entries := names.map fun c =>
          match refEnv.find? c with
          | some d => Json.mkObj [("name", jstr c.toString),
                                  ("module", jstr (moduleOf refEnv c).toString),
                                  ("decl", jstr (serDecl d))]
          | none => Json.mkObj [("name", jstr c.toString), ("decl", jstr "<missing>")]
        out := out.push (Json.mkObj [
          ("name", jstr nstr), ("kind", jstr (kindOf ci)),
          ("statement", jstr (serExpr ci.type)),
          ("level_params", jnames ci.levelParams),
          ("closure", jarr entries),
          ("closure_missing", jnames missing.toList)])
    IO.println (Json.mkObj [("freeze", Json.arr out)]).compress
    return 0
  if mode == "sanity" then
    let refEnv ← importModules #[{ module := (← getStr req "reference_module").toName }] {}
      (loadExts := true)
    let mut out := #[]
    let items := match req.getObjValAs? (Array Json) "theorems" with | .ok a => a | .error _ => #[]
    for item in items do
      let n := (← getStr item "name").toName
      let w := (item.getObjValAs? String "witness").toOption.map String.toName
      let necs := (getStrs item "necessity").map String.toName
      out := out.push (← sanityTheorem refEnv n w necs)
    IO.println (Json.mkObj [("sanity", Json.arr out)]).compress
    return 0
  let refEnv ← importModules #[{ module := (← getStr req "reference_module").toName }] {}
    (loadExts := true)
  let solMod := (← getStr req "solution_module").toName
  -- no extensions: loading them runs the module's initializers, that is,
  -- code of the submission (an `initialize` block); the auditor runs none
  let solEnv ← importModules #[{ module := solMod }] {} (loadExts := false)
  let defeq := (req.getObjValAs? Bool "kernel_defeq").toOption.getD true
  -- the submission's own imports (its header records them)
  let names := solEnv.header.moduleNames
  let imports := match names.findIdx? (· == solMod) with
    | some i => (solEnv.header.moduleData[i]!).imports.toList.map (·.module)
    | none => []
  let mut out := #[]
  for n in getStrs req "theorems" do
    out := out.push (← auditTheorem refEnv solEnv trusted n.toName defeq)
  IO.println (Json.mkObj [("solution_module", jstr solMod.toString),
                          ("solution_imports", jnames imports),
                          ("theorems", Json.arr out)]).compress
  return 0
