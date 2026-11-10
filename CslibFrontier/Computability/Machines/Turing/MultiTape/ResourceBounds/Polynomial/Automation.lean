/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
public import Mathlib.Data.Nat.Sqrt
public meta import Lean.Elab.Tactic

/-!
# Compositional polynomial resource bounds

`growth_poly` proves `Turing.MultiTapeTM.PolyBounded size cost` by the existing constant,
input-size, addition, multiplication and fixed-power rules, together with logarithm, square
root, maximum, truncated subtraction and division bounds. It also accepts
`Cslib.PolynomiallyBounded` goals through the existing `fun_prop` rules.

The leaves come from the local context:

* `PolyBounded` hypotheses, also inside conjunctions and inside definitions that unfold to them,
  such as a native certificate's `IsPolynomial`;
* certificates whose output length is polynomially bounded, such as
  `ComputableInPolyTime f encIn encOut`; with `encOut = encUnary` the value `f a` itself is
  bounded, and with `encOut = encBits` the length of the word `f a`;
* `Cslib.PolynomiallyBounded p` hypotheses, or `fun_prop` facts, applied as `p (u a)`;
* a `PolyBounded size' v` hypothesis at another size applied as `v (g a)`, which leaves the
  substitution `PolyBounded size (fun a => size' (g a))`.

A certificate supplies a leaf only through a lemma, and this module does not import those lemmas,
so that it stays below the machine layers. For each kind of certificate the proof uses, import
the module that proves its lemma (names relative to `CslibFrontier.Computability.Machines.Turing`,
the last one to `CslibFrontier.Computability`):

* `ComputableInPolyTime`, output length: `MultiTape.Internal.PolyTimePrimitives`, which
  `MultiTape.Complexity.PolyTime.Basic` imports;
* `ComputableInPolyTime` with `encUnary` output, the value: `MultiTape.Internal.PolyTimeLoops`,
  which `MultiTape.Complexity.PolyTime.Fold` imports;
* `ComputableInPolySpace`: `MultiTape.Complexity.PolySpace.Plain`;
* `ComputableInLogSpace`: `MultiTape.Complexity.LogSpace`;
* `DegreeBounded`: `MultiTape.ResourceBounds.Degree`;
* `Cslib.GenericRAM.NativeCertificate`: `GenericRAM.Native.Certificate`.

When a certificate in the context gives no leaf because its lemma is not imported, the failure
message names the module to import.

Local `let` values, and definitions whose bodies are arithmetic, are unfolded. The tactic proves
polynomial growth only. Word admission, exact time bounds and signed overflow conditions remain
separate obligations, and it does not guess an intermediate size measure: a substitution needs
the outer bound as a fact. Each step follows the syntax of the bound without backtracking, so a
goal outside these rules fails at once and names the term it could not bound.

## Main declarations

* `Turing.MultiTapeTM.PolyBounded.log`, `sqrt`, `max`, `sub`, `div`: further closure rules.
* `Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded_comp`: substitution into a polynomially
  bounded function of one natural number.
* `growth_poly`, `growth_poly [h₁, h₂]`: prove polynomial growth from these rules and the local
  context, with extra facts `h₁` and `h₂`.
* `Cslib.Tactic.GrowthPoly.certificateLemmas`: the certificate lemmas the tactic uses, with the
  modules that prove them.

The closure layer adapts Samuel Schlesinger's existing polynomial-bound API. The input-size
logarithm and square-root rules and the first `growth_poly` tactic are by Erik Demaine.
-/

public section

namespace Turing.MultiTapeTM.PolyBounded

variable {α : Type*} {size u v : α → ℕ}

/-- Natural logarithms preserve polynomial growth in any input-size measure. -/
theorem log (b : ℕ) (hu : PolyBounded size u) :
    PolyBounded size (fun a => Nat.log b (u a)) :=
  hu.mono fun a => Nat.log_le_self b (u a)

/-- Natural square roots preserve polynomial growth in any input-size measure. -/
theorem sqrt (hu : PolyBounded size u) : PolyBounded size (fun a => Nat.sqrt (u a)) :=
  hu.mono fun a => Nat.sqrt_le_self (u a)

/-- The maximum of two polynomially bounded functions is polynomially bounded. -/
theorem max (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => Max.max (u a) (v a)) :=
  (hu.add hv).mono fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- Truncated subtraction preserves a polynomial bound on its first argument. -/
theorem sub (hu : PolyBounded size u) (v : α → ℕ) : PolyBounded size (fun a => u a - v a) :=
  hu.mono fun a => Nat.sub_le (u a) (v a)

/-- Natural division preserves a polynomial bound on its dividend. -/
theorem div (hu : PolyBounded size u) (v : α → ℕ) : PolyBounded size (fun a => u a / v a) :=
  hu.mono fun a => Nat.div_le_self (u a) (v a)

/-- Substitute a polynomially bounded argument into a polynomially bounded function of one
natural number. -/
theorem of_polynomiallyBounded_comp {p : ℕ → ℕ} (hp : Cslib.PolynomiallyBounded p)
    (hu : PolyBounded size u) : PolyBounded size (fun a => p (u a)) :=
  (of_polynomiallyBounded id hp).comp hu

end Turing.MultiTapeTM.PolyBounded

/-- `growth_poly` proves `Turing.MultiTapeTM.PolyBounded size cost` by the closure rules for
constants, the input size, `+`, `*`, fixed powers, `Nat.log`, `Nat.sqrt`, `max`, truncated `-`
and `/`. The leaves come from local `PolyBounded` facts, also inside conjunctions and definitions
that unfold to them; from local certificates, through their output-length bound; and from local
`Cslib.PolynomiallyBounded` functions or `PolyBounded` facts at another size, applied to a
bounded argument. `growth_poly [h₁, h₂]` adds the facts `h₁` and `h₂`.

A certificate gives a leaf only when the module proving its bound is imported; the module
docstring lists them, for example `MultiTape.Internal.PolyTimePrimitives` for the output length
of `ComputableInPolyTime`. When a certificate in the context gives no leaf for this reason, the
failure names the module to import.

Local `let` values and arithmetic definitions are unfolded. The search follows the syntax of the
bound without backtracking: a goal outside these rules fails at once and names the term it could
not bound. `Cslib.PolynomiallyBounded` goals go to `fun_prop`. -/
syntax (name := growthPoly) "growth_poly" (" [" term,* "]")? : tactic

public meta section

namespace Cslib.Tactic.GrowthPoly

open Lean Meta Elab Tactic

/-- A lemma from a certificate to a `PolyBounded` fact or to another certificate. -/
structure CertificateLemma where
  /-- The lemma, applied to the local hypotheses whose head it matches when it is in scope. -/
  name : Name
  /-- The head constant of the certificate it takes, its last explicit hypothesis. -/
  head : Name
  /-- The output encoding, the certificate's last argument, that the lemma requires, if any. -/
  outEnc : Option Name := none
  /-- The module proving the lemma, named when the lemma is not in scope. -/
  module : Name

/-- The certificate lemmas, applied when they are in scope. This module does not import them,
which would make it depend on the machine layers. A lemma that requires an output encoding comes
before the general lemma with the same head, and its module imports that lemma's module.
The drift check in the `PolynomialGrowth` test checks that each lemma is proved in its `module`. -/
def certificateLemmas : List CertificateLemma :=
  [{ name := `Turing.MultiTapeTM.ComputableInPolyTime.polyBounded
     head := `Turing.MultiTapeTM.ComputableInPolyTime
     outEnc := `Turing.MultiTapeTM.encUnary
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops },
   { name := `Turing.MultiTapeTM.ComputableInPolyTime.polyBounded_length
     head := `Turing.MultiTapeTM.ComputableInPolyTime
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives },
   { name := `Turing.MultiTapeTM.ComputableInPolySpace.polyBounded_length
     head := `Turing.MultiTapeTM.ComputableInPolySpace
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain },
   { name := `Turing.MultiTapeTM.ComputableInLogSpace.polyBounded_length
     head := `Turing.MultiTapeTM.ComputableInLogSpace
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace },
   { name := `Turing.MultiTapeTM.DegreeBounded.polyBounded
     head := `Turing.MultiTapeTM.DegreeBounded
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Degree },
   { name := `Cslib.GenericRAM.NativeCertificate.polyTime
     head := `Cslib.GenericRAM.NativeCertificate.IsPolynomial
     module := `CslibFrontier.Computability.GenericRAM.Native.Certificate }]

/-- The facts available to `growth_poly`. -/
private structure Facts where
  /-- Proofs of `PolyBounded size v`, with their `size`. -/
  bounds : Array (Expr × Expr) := #[]
  /-- Proofs of `Cslib.PolynomiallyBounded p`, with their `p`. -/
  polys : Array (Expr × Expr) := #[]
  /-- Certificates that give no fact because their lemma is not in scope, with that lemma. -/
  unused : Array (Expr × CertificateLemma) := #[]

/-- The size and the bounded function of `PolyBounded size u`. -/
private def polyBoundedArgs? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Turing.MultiTapeTM.PolyBounded 3 then
    some (e.getArg! 1, e.getArg! 2)
  else none

/-- Read the bound a certificate gives in the form goals use: drop the identity encoding
`encBits` from `(encBits w).length`, and write `(f ∘ g) a` as `f (g a)`. -/
private def normalizeFact (ty : Expr) : CoreM Expr := do
  let ty := ty.replace fun e =>
    if e.isAppOfArity ``DFunLike.coe 6 && e.getArg! 4 == mkConst `Turing.MultiTapeTM.encBits then
      some e.appArg!
    else if e.isAppOfArity ``Function.comp 6 then
      some (mkApp (e.getArg! 3) (mkApp (e.getArg! 4) e.appArg!))
    else if e.isAppOfArity ``Function.comp 5 then
      some (.lam `x (e.getArg! 0) (mkApp ((e.getArg! 3).liftLooseBVars 0 1)
        (mkApp ((e.getArg! 4).liftLooseBVars 0 1) (.bvar 0))) .default)
    else none
  Core.betaReduce ty

/-- Record `pf : ty`, splitting conjunctions and unfolding definitions until a `PolyBounded` or
`Cslib.PolynomiallyBounded` fact appears, at most `depth` steps deep. -/
private partial def addFact (facts : Facts) (pf ty : Expr) (depth : Nat := 3) :
    MetaM Facts := do
  let ty ← whnfR (← instantiateMVars ty)
  if let some (size, _) := polyBoundedArgs? ty then
    let ty' ← normalizeFact ty
    let pf ← if ty' == ty then pure pf else mkExpectedTypeHint pf ty'
    return { facts with bounds := facts.bounds.push (pf, size) }
  if ty.isAppOfArity ``Cslib.PolynomiallyBounded 1 then
    return { facts with polys := facts.polys.push (pf, ty.appArg!) }
  if depth == 0 then return facts
  if ty.isAppOfArity ``And 2 then
    let facts ← addFact facts (← mkAppM ``And.left #[pf]) ty.appFn!.appArg! (depth - 1)
    return ← addFact facts (← mkAppM ``And.right #[pf]) ty.appArg! (depth - 1)
  if let some ty' ← unfoldDefinition? ty then
    return ← addFact facts pf ty' (depth - 1)
  return facts

/-- The head constant of the type of the last explicit hypothesis of `lem`. -/
private def certificateHead? (lem : Name) : MetaM (Option Name) := do
  forallTelescopeReducing (← getConstInfo lem).type fun xs _ => do
    for x in xs.reverse do
      if (← x.fvarId!.getBinderInfo).isExplicit then
        return (← inferType x).getAppFn.constName?
    return none

/-- `lem` applied to `h` as its last explicit hypothesis, with every other argument determined by
unification up to reducible unfolding, or `none`. -/
private def applyCertificate? (lem : Name) (h : Expr) : MetaM (Option Expr) := do
  let c ← mkConstWithFreshMVarLevels lem
  let (args, binders, _) ← forallMetaTelescopeReducing (← inferType c)
  let some i := (List.range args.size).reverse.find? (binders[·]!.isExplicit) | return none
  unless ← withReducible (isDefEq (← inferType args[i]!) (← inferType h)) do return none
  args[i]!.mvarId!.assign h
  let pf ← instantiateMVars (mkAppN c args)
  return if pf.hasExprMVar then none else some pf

/-- The facts from the local context and the extra `hints`, with the bounds that certificates
give, following certificate lemmas at most two steps. Certificates whose lemma is not in scope are
recorded in `unused`. -/
private def collectFacts (hints : Array Expr) : MetaM Facts := do
  let env ← getEnv
  let (present, absent) := certificateLemmas.partition (env.contains ·.name)
  let lemmas ← present.filterMapM fun l => return (← certificateHead? l.name).map (l.name, ·)
  let locals ← (← getLCtx).foldlM (init := #[]) fun acc decl =>
    if decl.isImplementationDetail then pure acc else pure (acc.push decl.toExpr)
  let mut facts : Facts := {}
  let mut work := (hints ++ locals).map (·, 2)
  while !work.isEmpty do
    let (pf, depth) := work.back!
    work := work.pop
    let ty ← instantiateMVars (← inferType pf)
    unless ← isProp ty do continue
    facts ← addFact facts pf ty (if depth == 2 then 3 else 0)
    if depth == 0 then continue
    let head := ty.getAppFn.constName?
    for (lem, lemHead) in lemmas do
      if head == some lemHead then
        if let some pf' ← applyCertificate? lem pf then
          work := work.push (pf', depth - 1)
    -- Name one missing module per certificate: the first matching lemma's, which is the specific
    -- one when there is one, and whose module imports the general lemma's.
    if let some l := absent.find? fun l => head == some l.head &&
        l.outEnc.all fun enc => ty.getAppArgs.back?.any (·.isConstOf enc) then
      unless facts.unused.any fun (pf', l') => pf' == pf && l'.name == l.name do
        facts := { facts with unused := facts.unused.push (pf, l) }
  return facts

/-- Replace a local `let` variable or `let` at the head of `e` by its value, and beta reduce. -/
private partial def zetaHead (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  match e.getAppFn with
  | .fvar id =>
    match ← id.getValue? with
    | some v => zetaHead (v.beta e.getAppArgs)
    | none => return e
  | .letE _ _ v b _ => zetaHead ((b.instantiate1 v).beta e.getAppArgs)
  | .mdata _ b => zetaHead (b.beta e.getAppArgs)
  | _ => return e

/-- The closure rule for an arithmetic operation, by head constant and arity. -/
private def opRule? (body : Expr) : Option Name :=
  match body.getAppFn.constName?, body.getAppNumArgs with
  | some ``HAdd.hAdd, 6 => some ``Turing.MultiTapeTM.PolyBounded.add
  | some ``HMul.hMul, 6 => some ``Turing.MultiTapeTM.PolyBounded.mul
  | some ``HPow.hPow, 6 => some ``Turing.MultiTapeTM.PolyBounded.pow
  | some ``HSub.hSub, 6 => some ``Turing.MultiTapeTM.PolyBounded.sub
  | some ``HDiv.hDiv, 6 => some ``Turing.MultiTapeTM.PolyBounded.div
  | some ``Max.max, 4 => some ``Turing.MultiTapeTM.PolyBounded.max
  | some ``Nat.log, 2 => some ``Turing.MultiTapeTM.PolyBounded.log
  | some ``Nat.sqrt, 1 => some ``Turing.MultiTapeTM.PolyBounded.sqrt
  | _, _ => none

/-- The arguments of an operation that must not depend on the input: a power's exponent and a
logarithm's base. -/
private def fixedArgs (body : Expr) : Array Expr :=
  match body.getAppFn.constName? with
  | some ``HPow.hPow => #[body.getArg! 5]
  | some ``Nat.log => #[body.getArg! 0]
  | _ => #[]

/-- How `growth_poly` takes a goal apart. -/
private inductive Step where
  /-- Close the goal with this proof. -/
  | close (pf : Expr)
  /-- Apply this closure rule and continue with its `PolyBounded` subgoals. -/
  | apply (rule : Name)
  /-- Apply this rule to the fact `pf` and continue with the remaining `PolyBounded` subgoals. -/
  | applyTo (rule : Name) (pf : Expr)
  /-- Continue with this definitionally equal bounded function. -/
  | change (u : Expr)

/-- Is `e` a function from natural numbers to natural numbers? -/
private def isNatFun (e : Expr) : MetaM Bool := do
  match ← whnfR (← inferType e) with
  | .forallE _ d b _ => return d.isConstOf ``Nat && !b.hasLooseBVars && b.isConstOf ``Nat
  | _ => return false

/-- Prove `Cslib.PolynomiallyBounded p` by `fun_prop`, if it can. -/
private def polynomiallyBoundedByFunProp? (p : Expr) : MetaM (Option Expr) := do
  let hp ← mkFreshExprMVar (mkApp (mkConst ``Cslib.PolynomiallyBounded) p)
  try
    let gs ← (Tactic.run hp.mvarId! do evalTactic (← `(tactic| fun_prop))).run'
    unless gs.isEmpty do return none
    return some (← instantiateMVars hp)
  catch _ => return none

/-- `n` applied to `pf` as its first explicit argument, with metavariables for the arguments
before it; the remaining arguments stay for `MVarId.apply`. -/
private def applyTo (n : Name) (pf : Expr) : MetaM Expr := do
  let c ← mkConstWithFreshMVarLevels n
  let (args, binders, _) ← forallMetaTelescopeReducing (← inferType c)
  let some i := binders.findIdx? (·.isExplicit) |
    throwError "growth_poly: {n} has no explicit argument"
  unless ← isDefEq (← inferType args[i]!) (← inferType pf) do
    throwError "growth_poly: {pf} does not fit {n}"
  args[i]!.mvarId!.assign pf
  return mkAppN c args[:i + 1]

/-- Drop an `id` at the head of `e`. -/
private def stripId (e : Expr) : Expr :=
  if e.isAppOfArity ``id 2 then e.appArg! else e

/-- Is `pf` a proof of `goalTy` up to reducible unfolding? -/
private def provesReducible (pf goalTy : Expr) : MetaM Bool := do
  withReducible <| withNewMCtxDepth <| isDefEq (← inferType pf) goalTy

/-- Choose the next step for the goal `goalTy`, which is `PolyBounded size u`, or throw an error
naming the term that no rule bounds. -/
private def chooseStep (facts : Facts) (goalTy size u : Expr) : MetaM Step := do
  for (pf, _) in facts.bounds do
    if ← provesReducible pf goalTy then return .close pf
  let .forallE _ α _ _ ← whnfR (← inferType u) |
    throwError "growth_poly: {u} is not a function"
  withLocalDeclD `a α fun a => do
    let body₀ := (u.beta #[a]).headBeta
    let body ← zetaHead body₀
    if body != body₀ then return .change (← mkLambdaFVars #[a] body)
    let dependsOnInput (e : Expr) := e.containsFVar a.fvarId!
    if !dependsOnInput body then return .apply ``Turing.MultiTapeTM.PolyBounded.const
    if ← withReducible (isDefEq body (stripId (size.beta #[a]).headBeta)) then
      return .apply ``Turing.MultiTapeTM.PolyBounded.self
    let fail : MetaM Step := do
      let unused := facts.unused.toList.map fun (pf, l) =>
        m!"\nThe certificate `{pf}` gives no bound: `{l.name}` is not imported. \
          Import `{l.module}`."
      throwError "growth_poly: no rule or local fact bounds{indentExpr body}\n\
        by a polynomial in{indentExpr (size.beta #[a]).headBeta}\n\
        Add a `PolyBounded` fact or a certificate for it to the context, or pass one as \
        `growth_poly [h]`.{MessageData.joinSep unused ""}"
    if body.isAppOfArity ``Nat.succ 1 then
      return .change (← mkLambdaFVars #[a] (mkNatAdd body.appArg! (mkNatLit 1)))
    if let some rule := opRule? body then
      if (fixedArgs body).any dependsOnInput then return ← fail
      return .apply rule
    let natFunApp ← pure body.isApp <&&> pure !(dependsOnInput body.appFn!) <&&>
      isNatFun body.appFn!
    -- A polynomially bounded function of one natural number, known from the context.
    if natFunApp then
      for (pf, p) in facts.polys do
        if ← withReducible <| withNewMCtxDepth <| isDefEq body.appFn! p then
          return .applyTo ``Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded_comp pf
    -- A bounded function at another size, applied to a function of the input.
    for (pf, size') in facts.bounds do
      if ← withReducible <| withNewMCtxDepth <| isDefEq size' size then continue
      let fits ← withNewMCtxDepth do
        let comp ← applyTo ``Turing.MultiTapeTM.PolyBounded.comp pf
        let (_, _, concl) ← forallMetaTelescopeReducing (← inferType comp)
        withReducible (isDefEq concl goalTy)
      if fits then return .applyTo ``Turing.MultiTapeTM.PolyBounded.comp pf
    -- An arithmetic definition.
    if let some c := body.getAppFn.constName? then
      if !c.isInternal then
        if let some body' ← unfoldDefinition? body then
          let body' ← zetaHead body'
          if (opRule? body').isSome || !dependsOnInput body' then
            return .change (← mkLambdaFVars #[a] body')
    -- A polynomially bounded function of one natural number, by `fun_prop`.
    if natFunApp then
      if let some hp ← polynomiallyBoundedByFunProp? body.appFn! then
        return .applyTo ``Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded_comp hp
    fail

/-- Prove the `PolyBounded` goal `g` from `facts`, within `fuel` steps. -/
private partial def prove (facts : Facts) (g : MVarId) (fuel : Nat) : MetaM Unit :=
  g.withContext do
  if fuel == 0 then
    throwError "growth_poly: step limit reached at{indentExpr (← g.getType)}"
  let goalTy ← whnfR (← instantiateMVars (← g.getType))
  let some (size, u) := polyBoundedArgs? goalTy |
    throwError "growth_poly: expected a `PolyBounded` goal, got{indentExpr goalTy}"
  let rule ← match ← chooseStep facts goalTy size u with
    | .close pf => g.assign pf; return
    | .change u' =>
      let g' ← g.replaceTargetDefEq (mkAppN goalTy.getAppFn #[goalTy.getArg! 0, size, u'])
      return ← prove facts g' (fuel - 1)
    | .apply rule => mkConstWithFreshMVarLevels rule
    | .applyTo rule pf => applyTo rule pf
  let gs ← g.apply rule
  for g' in gs do
    unless ← g'.isAssigned do
      let ty ← whnfR (← instantiateMVars (← g'.getType))
      if (polyBoundedArgs? ty).isSome then prove facts g' (fuel - 1)
  for g' in gs do
    unless ← g'.isAssigned do
      throwError "growth_poly: could not determine{indentExpr (← g'.getType)}"

elab_rules : tactic
  | `(tactic| growth_poly $[[$hints,*]]?) => focus do
    let goal ← getMainGoal
    let goalTy ← whnfR (← instantiateMVars (← goal.getType))
    if goalTy.isAppOfArity ``Cslib.PolynomiallyBounded 1 then
      evalTactic (← `(tactic| fun_prop))
      return
    goal.withContext do
      let hints ← ((hints.map (·.getElems)).getD #[]).mapM fun h => elabTerm h none
      prove (← collectFacts hints) goal 256
    replaceMainGoal []

end Cslib.Tactic.GrowthPoly

end
