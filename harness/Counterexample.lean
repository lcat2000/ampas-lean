/-
AMPAS math-verification: bounded counterexample search against a FROZEN
reference statement.

Why this exists. The external validation pair showed the hole this closes:
`FermatWeaker` has no `sorry`, no extra axiom, every line genuinely proved,
and both kernels accept it -- it simply proves a different statement from the
one it is filed under. Freezing and signing make a human judgement auditable;
they do not make it correct. The cheapest filter against a reference statement
that is outright FALSE is to try to falsify it before freezing it. Fermat's
claim is caught at n = 5.

What this program does NOT do, stated up front because the result is easy to
over-read:

  * It cannot establish that a statement is true. A bounded search that finds
    nothing says "no counterexample in this box", never "no counterexample".
  * It cannot establish FIDELITY -- whether the statement says what the
    natural-language claim says. A faithful formalization of a false claim and
    an unfaithful formalization of a true one are both refutable; this program
    cannot tell them apart. That judgement stays with a human reviewer.
  * It refuses to guess. Where a hypothesis or the conclusion cannot be
    decided, the tuple is reported UNRESOLVED and the claim's record says so.
    A claim whose conclusion is not decidable at all comes back
    NOT_SEARCHABLE with the reason, which is a gap, not a pass.

How a Prop becomes a decision procedure. Three cases, in order:

  1. A `Decidable` instance synthesizes. The resulting `decide p` is EXACT:
     true means true, false means false.
  2. The Prop is `∃ x : Nat, q`. Rewritten to `(List.range (eb+1)).any`,
     which is ONE-SIDED: true means a witness was found, so the Prop holds;
     false means only that no witness is in range. `Ampas.IsEven` and `a ∣ b`
     both arrive here when core has no instance for them.
  3. Conjunction, disjunction -- one-sidedness in the "true means true"
     direction survives both. NEGATION DOES NOT, so a negated one-sided term
     is refused rather than reported.

A counterexample is therefore only ever claimed when every hypothesis
evaluated true (sound in all three cases) and the conclusion is EXACT and
evaluated false. Everything weaker is UNRESOLVED.

Usage:
  lean --run Counterexample.lean <request.json>

Request: {"module": "AmpasRef.Challenge", "decl": "Ampas.Claims.add_comm_nat",
          "bound": 24, "exists_bound": 64}
-/
import Lean
open Lean Meta

namespace Ampas.Cex

/-- A Bool-valued decision term for a Prop, with how much it is allowed to
mean. `exact := false` is one-sided: `true` implies the Prop holds, `false`
implies nothing. -/
structure Dec where
  term : Expr
  exact : Bool
deriving Inhabited

def tyListNat : Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)

def jstr (s : String) : Json := Json.str s

/-- Turn a Prop into a Bool term, or fail with a reason. -/
partial def decidify (p : Expr) (eb : Nat) (depth : Nat := 6) : MetaM (Except String Dec) := do
  -- 1. a real Decidable instance: exact in both directions
  let decCls ← mkAppM ``Decidable #[p]
  match ← trySynthInstance decCls with
  | .some inst =>
    return .ok { term := mkApp2 (mkConst ``decide) p inst, exact := true }
  | _ =>
    match p.getAppFnArgs with
    -- 2. a bounded witness hunt for an existential over Nat: one-sided
    | (``Exists, #[dom, pred]) =>
      if !(← isDefEq dom (mkConst ``Nat)) then
        return .error s!"existential over {← ppExpr dom}, not Nat"
      withLocalDeclD `w (mkConst ``Nat) fun w => do
        let body := (mkApp pred w).headBeta
        match ← decidify body eb depth with
        | .error e => return .error s!"inside an existential: {e}"
        | .ok d =>
          let f ← mkLambdaFVars #[w] d.term
          let range := mkApp (mkConst ``List.range) (mkNatLit (eb + 1))
          let anyE ← mkAppM ``List.any #[range, f]
          -- one-sided even if the body was exact: absence of a witness in
          -- range is not absence of a witness
          return .ok { term := anyE, exact := false }
    -- 3. connectives, which preserve the "true means true" direction
    | (``And, #[a, b]) =>
      match ← decidify a eb depth, ← decidify b eb depth with
      | .ok da, .ok db =>
        return .ok { term := ← mkAppM ``and #[da.term, db.term],
                     exact := da.exact && db.exact }
      | .error e, _ => return .error e
      | _, .error e => return .error e
    | (``Or, #[a, b]) =>
      match ← decidify a eb depth, ← decidify b eb depth with
      | .ok da, .ok db =>
        return .ok { term := ← mkAppM ``or #[da.term, db.term],
                     exact := da.exact && db.exact }
      | .error e, _ => return .error e
      | _, .error e => return .error e
    -- negation of a one-sided term would be unsound in the other direction,
    -- so it is refused. (`¬ p` with p decidable never reaches here: the
    -- instance in case 1 covers it.)
    | (``Not, #[a]) =>
      match ← decidify a eb depth with
      | .ok d => if d.exact
                 then return .ok { term := ← mkAppM ``not #[d.term], exact := true }
                 else return .error s!"negation of a one-sided test ({← ppExpr a})"
      | .error e => return .error s!"inside a negation: {e}"
    | _ =>
      -- a definition standing in front of a shape we do handle: `IsEven n`
      -- is `∃ k, n = 2 * k`, and stopping at the name would report a gap
      -- that is not there. Bounded to one unfolding step per level so a
      -- recursive definition cannot spin.
      if depth > 0 then
        if let some p' ← unfoldDefinition? p then
          return ← decidify p' eb (depth - 1)
      return .error s!"no Decidable instance for {← ppExpr p}"

/-- `(List.range (b+1)).findSome? ...`, nested once per data variable, whose
body is `cond (pred x₀ … xₖ) (some [x₀,…,xₖ]) none`. findSome? short-circuits,
so a claim refuted early never evaluates the rest of the box. -/
partial def nest (k bound : Nat) (pred : Expr) (acc : Array Expr) : MetaM Expr := do
  if acc.size ≥ k then
    let b := mkAppN pred acc
    let lst ← mkListLit (mkConst ``Nat) acc.toList
    let s ← mkAppOptM ``Option.some #[some tyListNat, some lst]
    let n ← mkAppOptM ``Option.none #[some tyListNat]
    mkAppM ``cond #[b, s, n]
  else
    withLocalDeclD (Name.mkSimple s!"x{acc.size}") (mkConst ``Nat) fun v => do
      let inner ← nest k bound pred (acc.push v)
      let f ← mkLambdaFVars #[v] inner
      mkAppM ``List.findSome? #[f, mkApp (mkConst ``List.range) (mkNatLit (bound + 1))]

/-- The same nesting, but collecting one Bool per point of the box instead of
stopping at the first hit, so a partial result can say HOW partial it is.
A record that says "no counterexample" over a box that was mostly unresolved
means much less than one over a box that was not, and the difference should
not need a reader's guess. -/
partial def nestCount (k bound : Nat) (pred : Expr) (acc : Array Expr) : MetaM Expr := do
  if acc.size ≥ k then
    mkListLit (mkConst ``Bool) [mkAppN pred acc]
  else
    withLocalDeclD (Name.mkSimple s!"x{acc.size}") (mkConst ``Nat) fun v => do
      let inner ← nestCount k bound pred (acc.push v)
      let f ← mkLambdaFVars #[v] inner
      mkAppM ``List.flatMap #[f, mkApp (mkConst ``List.range) (mkNatLit (bound + 1))]

unsafe def evalTuple (e : Expr) : MetaM (Option (List Nat)) :=
  evalExpr (Option (List Nat)) (mkApp (mkConst ``Option [Level.zero]) tyListNat) e

unsafe def evalCount (e : Expr) : MetaM Nat :=
  evalExpr Nat (mkConst ``Nat) e

/-- The search. Returns the JSON record for one claim. -/
unsafe def search (decl : Name) (bound eb : Nat) : MetaM Json := do
  let ci ← getConstInfo decl
  forallTelescopeReducing ci.type fun xs body => do
    -- classify the binders: Nat data, or a decidable-ish hypothesis
    let mut dataVars : Array Expr := #[]
    let mut hyps : Array Dec := #[]
    for x in xs do
      let t ← inferType x
      if ← isDefEq t (mkConst ``Nat) then
        dataVars := dataVars.push x
      else if ← isProp t then
        match ← decidify t eb with
        | .ok d => hyps := hyps.push d
        | .error e =>
          return Json.mkObj [("outcome", jstr "NOT_SEARCHABLE"),
                             ("reason", jstr s!"hypothesis {← ppExpr t}: {e}")]
      else
        return Json.mkObj [("outcome", jstr "NOT_SEARCHABLE"),
                           ("reason", jstr s!"binder of type {← ppExpr t}; only Nat is enumerated")]
    let conc ← match ← decidify body eb with
      | .ok d => pure d
      | .error e =>
        return Json.mkObj [("outcome", jstr "NOT_SEARCHABLE"),
                           ("reason", jstr s!"conclusion {← ppExpr body}: {e}")]
    -- every hypothesis test, conjoined: true means all hypotheses hold
    let mut allHyps : Expr := mkConst ``Bool.true
    for h in hyps do allHyps ← mkAppM ``and #[allHyps, h.term]
    -- a tuple is a counterexample only when the conclusion is exact
    let mode := if conc.exact then "refutation" else "verification_only"
    let mut cexWitness : Option (List Nat) := none
    if conc.exact then
      let notConc ← mkAppM ``not #[conc.term]
      let cexPred ← mkAppM ``and #[allHyps, notConc]
      let lam ← mkLambdaFVars dataVars cexPred
      if (← instantiateMVars lam).hasFVar then
        return Json.mkObj [("outcome", jstr "NOT_SEARCHABLE"),
          ("reason", jstr "the test depends on a proof binder, so it cannot be enumerated")]
      cexWitness ← evalTuple (← nest dataVars.size bound lam #[])
    -- a tuple is unresolved when a one-sided test came back false: either a
    -- hypothesis whose truth is unknown, or (verification-only) a conclusion
    -- that could not be confirmed
    let oneSided := hyps.filter (fun h => !h.exact)
    let mut unresPred : Expr := mkConst ``Bool.false
    for h in oneSided do
      unresPred ← mkAppM ``or #[unresPred, ← mkAppM ``not #[h.term]]
    if !conc.exact then
      unresPred ← mkAppM ``or #[unresPred,
        ← mkAppM ``and #[allHyps, ← mkAppM ``not #[conc.term]]]
    let mut unresolved : Option (List Nat) := none
    let mut unresolvedCount : Option Nat := none
    if !oneSided.isEmpty || !conc.exact then
      let lamU ← mkLambdaFVars dataVars unresPred
      if !(← instantiateMVars lamU).hasFVar then
        unresolved ← evalTuple (← nest dataVars.size bound lamU #[])
        if unresolved.isSome then
          let flags ← nestCount dataVars.size bound lamU #[]
          let idB ← withLocalDeclD `b (mkConst ``Bool) fun b => mkLambdaFVars #[b] b
          unresolvedCount ← evalCount (← mkAppM ``List.countP #[idB, flags])
    -- A point where a hypothesis fails is VACUOUS: the statement says nothing
    -- there, and counting it as checked would inflate the box. Only counted
    -- when every hypothesis is exact; a one-sided hypothesis that came back
    -- false is unresolved, not vacuous, and is already counted as such.
    -- ...except when the conclusion is `False`, i.e. the statement was a
    -- negation `¬ P` that the telescope turned into `P → False`. There the
    -- "hypothesis" IS the statement's content and its failing is exactly what
    -- makes the negation hold, so counting those points as vacuous would
    -- report that nothing was checked about a statement that was in fact
    -- fully decided. FERMAT-F5 is the case: one point, and it settles it.
    let mut vacuousCount : Option Nat := none
    if !hyps.isEmpty && oneSided.isEmpty && !body.isConstOf ``False then
      let vacPred ← mkAppM ``not #[allHyps]
      let lamV ← mkLambdaFVars dataVars vacPred
      if !(← instantiateMVars lamV).hasFVar then
        let flags ← nestCount dataVars.size bound lamV #[]
        let idB ← withLocalDeclD `b (mkConst ``Bool) fun b => mkLambdaFVars #[b] b
        vacuousCount ← evalCount (← mkAppM ``List.countP #[idB, flags])
    let tuples := (bound + 1) ^ dataVars.size
    let base := [("decl", jstr decl.toString), ("bound", Json.num bound),
                 ("exists_bound", Json.num eb), ("mode", jstr mode),
                 ("data_variables", Json.num dataVars.size),
                 ("hypotheses", Json.num hyps.size),
                 ("one_sided_hypotheses", Json.num oneSided.size),
                 ("conclusion_exact", Json.bool conc.exact),
                 ("box_size", Json.num tuples)] ++
               (match vacuousCount with
                | some v => [("vacuous_points", Json.num v)]
                | none => [])
    let unres : List (String × Json) := match unresolved with
      | some t => [("first_unresolved", Json.arr (t.map (fun n => Json.num (n : Nat))).toArray)]
                  ++ (match unresolvedCount with
                      | some c => [("unresolved_points", Json.num c),
                                   ("resolved_points", Json.num (tuples - c))]
                      | none => [])
      | none => [("unresolved_points", Json.num 0), ("resolved_points", Json.num tuples)]
    match cexWitness with
    | some t =>
      return Json.mkObj (base ++ unres ++
        [("outcome", jstr "REFUTED"),
         ("witness", Json.arr (t.map (fun n => Json.num (n : Nat))).toArray)])
    | none =>
      return Json.mkObj (base ++ unres ++
        [("outcome", jstr (if unresolved.isSome then "NO_COUNTEREXAMPLE_PARTIAL"
                           else "NO_COUNTEREXAMPLE"))])

unsafe def run (args : List String) : IO UInt32 := do
  let some reqPath := args.head? | do
    IO.eprintln "usage: lean --run Counterexample.lean <request.json>"; return 1
  let req ← match Json.parse (← IO.FS.readFile reqPath) with
    | .ok j => pure j
    | .error e => do IO.eprintln s!"bad request: {e}"; return 1
  let getStr (k : String) : IO String := match req.getObjValAs? String k with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"request field {k}: {e}")
  let getNat (k : String) (d : Nat) : Nat := (req.getObjValAs? Nat k).toOption.getD d
  let mod := (← getStr "module").toName
  let decl := (← getStr "decl").toName
  initSearchPath (← findSysroot)
  -- loadExts is required: the search EVALUATES decision procedures, which
  -- needs instances and compiled code, not just the kernel's view. It also
  -- means the reference module's own initializers run -- acceptable here
  -- because this program only ever runs against the TRUSTED reference
  -- statements, never against a submission.
  enableInitializersExecution
  let env ← importModules #[{ module := mod }] {} (loadExts := true)
  let (res, _) ← (search decl (getNat "bound" 24) (getNat "exists_bound" 64)).toIO
      { fileName := "<cex>", fileMap := default } { env := env }
  IO.println res.compress
  return 0

end Ampas.Cex

unsafe def main (args : List String) : IO UInt32 := Ampas.Cex.run args
