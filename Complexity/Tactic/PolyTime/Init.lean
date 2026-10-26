/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Aesop
public import Mathlib.Tactic.FunProp

/-!
# Rule sets and certificates for polynomial-time programs

`polytime` searches the Aesop rule set `PolyTime`. A certificate for a named program is registered
with `@[program_certificate]`. Certificates are indexed by their efficiency predicate and by the
constant at the head of the program, looking through an output encoding. A goal's certificates
are looked up using its own program head, so similarly implemented algorithms do not unfold into
each other's rules.
Certificates are also registered with `fun_prop`, reusing any existing global registration, so the
same annotation supports calls inside larger functional programs without duplicating search rules.
Parameterized `IsPPT` certificates are uncurried to the definitionally equal `IsPPTOn` statement
before registration, keeping both tactic interfaces on the same encoded-input contract.

The certificate index is adapted from the cslib `crypto` branch. Both computation predicates use
separate input and output encodings. `Tactic.PPT` combines the `PPT` and `PolyTime`
rule sets for closed probabilistic programs; machine witnesses remain behind their certificates.

## Main definitions

* `program_certificate`: register a named efficiency theorem before its implementation unfolds.

Aesop's index cannot see inside the program, which is a function, so the lookup is a single tactic
rule for each efficiency predicate rather than one `apply` rule for each certificate.

## References

Adapted from Cslib/Tactic/PolyTime/Init.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, sharing routine-call matching between both tactics.
-/

public section

declare_aesop_rule_sets [PolyTime, PPT]

end

public meta section

open Lean Meta Elab Tactic

namespace Cslib.Tactic

/-- Inspect an ordinary conditional under its function binders, including reducible aliases.
The callback runs while those binders are in scope; no expression with escaped fvars is returned
by the recognizer itself. Named opaque programs are not unfolded. -/
def withConditionalBody? {α : Type} (program : Expr)
    (inspect : Expr → MetaM α) : MetaM (Option α) := do
  let program ← Core.betaReduce (← etaExpand program)
  lambdaTelescope program fun _ body => do
    let body ← if body.isAppOf ``ite then pure body else whnfR body
    if body.isAppOf ``ite then return some (← inspect body)
    return none

/-- The constant naming a program body, and whether it was found under an output encoding. An
application of an encoding is looked through, and so is `List.replicate n true`, the simp-normal
form of a unary encoding. -/
def programHead? (body : Expr) : Option (Name × Bool) :=
  let body := body.consumeMData
  if body.isAppOf `DFunLike.coe then
    body.getAppArgs.back!.consumeMData.getAppFn.constName?.map (·, true)
  else if body.isAppOfArity ``List.replicate 3 && body.getAppArgs.back!.isConstOf ``Bool.true then
    body.getAppArgs[1]!.consumeMData.getAppFn.constName?.map (·, true)
  else
    body.getAppFn.constName?.map (·, false)

/-- The efficiency predicate and program head of an efficiency statement, and whether the program
returns its result under an encoding. `IsPPT` statements are indexed under `IsPPTOn`, which they
unfold to. A certificate stated under an encoding only applies to goals stated the same way. -/
def efficiencyKey (statement : Expr) : MetaM (Name × Name × Bool) := do
  let statement := statement.consumeMData
  let some predicate := statement.getAppFn.constName?
    | throwError "expected an efficiency statement"
  unless predicate == `Turing.MultiTapeTM.ComputableInPolyTime ||
      predicate == `Turing.MultiTapeTM.ComputableTidilyInPolyTime ||
      predicate == `Cslib.Probability.IsPPTOn || predicate == `Cslib.Probability.IsPPT ||
      predicate == `Cslib.WordRAM.Refines ||
      predicate == `Cslib.WordRAM.ComputableInPolyTime ||
      predicate == `Cslib.WordRAM.UniformComputableInPolyTime do
    throwError "unsupported efficiency predicate `{predicate}` for `program_certificate`; \
      expected TM polynomial time, PPT, or a documented word-RAM certificate"
  let argument := if predicate == `Turing.MultiTapeTM.ComputableTidilyInPolyTime ||
      predicate == `Turing.MultiTapeTM.ComputableInPolyTime then
    statement.getAppArgs[2]! else statement.getAppArgs.back!
  let program ← Core.betaReduce (← etaExpand argument)
  let some (head, encoded) ← lambdaTelescope program fun _ body => pure (programHead? body)
    | throwError "the program body is not an application of a constant"
  let predicate := if predicate == `Cslib.Probability.IsPPT then
    `Cslib.Probability.IsPPTOn else predicate
  return (predicate, head, encoded)

/-- Expose parameterized PPT in a certificate's premises and conclusion for encoded-input
automation. The generated theorem is definitionally the original proof. -/
private def encodedCertificate (declName : Name) : MetaM Name := do
  let info ← getConstInfo declName
  let type ← deltaExpand info.type (· == `Cslib.Probability.IsPPT)
  if type == info.type then return declName
  let name ← mkFreshUserName (declName ++ `_pptOn)
  addDecl <| .thmDecl {
    name
    levelParams := info.levelParams
    type
    value := mkConst declName (info.levelParams.map Level.param) }
  return name

/-- Registered certificates, indexed by efficiency predicate and program head. Each certificate
carries the hypotheses to solve as soon as it is applied. -/
initialize certificateExt : SimpleScopedEnvExtension ((Name × Name × Bool) × Name × Array Name)
    (Std.HashMap (Name × Name × Bool) (Array (Name × Array Name))) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun certificates (key, entry) =>
      certificates.insert key ((certificates.getD key #[]).push entry)
    initial := {}
  }

/-- Check persistent entries rather than the active index: a local or scoped registration must
not suppress a registration that remains available after leaving its scope. -/
private def hasGlobalEntry {α σ : Type} (ext : SimpleScopedEnvExtension α σ)
    (name : α → Name) (decl : Name) : CoreM Bool := do
  let state := ext.ext.toEnvExtension.getState (← getEnv)
  let isEntry : ScopedEnvExtension.Entry α → Bool
    | .global entry => name entry == decl
    | .scoped _ _ => false
  return state.state.newEntries.any isEntry || state.importedEntries.any (·.any isEntry)

open Mathlib.Meta.FunProp in
/-- Preserve an existing `fun_prop` entry, including its priority. Distinct certificates for the
same function are still registered independently. -/
private def hasGlobalFunProp (decl : Name) : CoreM Bool := do
  return (← hasGlobalEntry functionTheoremsExt (·.thmOrigin.name) decl) ||
    (← hasGlobalEntry lambdaTheoremsExt (·.thmName) decl) ||
    (← hasGlobalEntry morTheoremsExt (·.thmName) decl) ||
    (← hasGlobalEntry transitionTheoremsExt (·.thmName) decl)

/-- `@[program_certificate]` registers an efficiency certificate for `polytime` and `ppt`. Its
conclusion must be a `ComputableInPolyTime`, `ComputableTidilyInPolyTime`, `IsPPTOn` or `IsPPT`
statement, or one of the word-RAM predicates `WordRAM.Refines`, `WordRAM.ComputableInPolyTime`,
`WordRAM.UniformComputableInPolyTime` used by `Tactic.WordRAM`. The indexed argument must apply
a constant, possibly under an output encoding. Other predicates are rejected rather than indexed
by an unrelated final argument.
Certificates are also registered with `fun_prop` for use in larger compositions, unless the same
declaration already has a global registration.

`@[program_certificate h₁ … hₙ]` additionally solves the hypotheses `h₁ … hₙ` immediately after the
certificate is applied. This is needed when such a hypothesis determines an encoding that other
hypotheses mention, so that proof search does not reach those goals with the encoding unknown. -/
syntax (name := programCertificate) "program_certificate" (ppSpace ident)* : attr

initialize registerBuiltinAttribute {
  name := `programCertificate
  descr := "an efficiency certificate used by `polytime` and `ppt`, indexed by program head"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    unless stx.isOfKind ``programCertificate do throwUnsupportedSyntax
    let eager := stx[1].getArgs.map (·.getId)
    let (certificate, key) ← MetaM.run' do
      let certificate ← encodedCertificate declName
      let key ← forallTelescope (← getConstInfo certificate).type fun _ conclusion =>
        efficiencyKey conclusion
      return (certificate, key)
    if key.1 == `Turing.MultiTapeTM.ComputableTidilyInPolyTime ||
        key.1 == `Turing.MultiTapeTM.ComputableInPolyTime ||
        key.1 == `Cslib.Probability.IsPPTOn then
      unless ← hasGlobalFunProp certificate do
        Attribute.add certificate `fun_prop .missing kind
    certificateExt.add (key, certificate, eager) kind
}

/-- Solve the goal tagged `name`, or else one whose tag ends in `name` as for `case`, by proof
search: `PPT` and `PolyTime` rules for a PPT goal, and `PolyTime` rules otherwise. -/
def solveTagged (name : Name) : TacticM Unit := do
  let goals ← getGoals
  let some goal ← (do
      if let some goal ← goals.findM? fun goal => return (← goal.getTag) == name then
        return some goal
      goals.findM? fun goal => return name.isSuffixOf (← goal.getTag))
    | throwError "no goal named `{name}`"
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let isPPTGoal :=
    target.isAppOf `Cslib.Probability.IsPPTOn || target.isAppOf `Cslib.Probability.IsPPT
  let tactic ← if isPPTGoal then
    `(tactic| solve |
      aesop (config := { terminal := true, assumptionTransparency := .reducible })
        (rule_sets := [PPT, PolyTime]))
  else
    `(tactic| solve |
      aesop (config := { terminal := true, assumptionTransparency := .reducible })
        (rule_sets := [PolyTime]))
  let remaining ← evalTacticAt tactic goal
  unless remaining.isEmpty do throwError "proof search did not discharge `{name}`"
  -- Nested tactic elaboration can recover an error by admitting its goal. Reject that candidate
  -- before Aesop records it as a successful certificate application.
  if ← Aesop.hasSorry (mkMVar goal) then
    throwError "proof search did not discharge `{name}`"
  setGoals (goals.filter (· != goal))

/-- Preserve premise names even when Lean's `apply` gives a lone remaining goal its parent's
tag. The applied proof records the actual argument metavariables, including inferred ones. -/
private def tagPremises (goal : MVarId) (certificate : Name) (goals : List MVarId) :
    MetaM Unit := do
  let some proof ← getExprMVarAssignment? goal
    | throwError "the certificate did not assign its goal"
  let names ← forallTelescope (← getConstInfo certificate).type fun xs _ =>
    xs.mapM fun x => return (← x.fvarId!.getDecl).userName
  let parent ← goal.getTag
  for name in names, argument in proof.getAppArgs do
    if let .mvar premise := argument then
      if goals.contains premise then premise.setTag (appendTag parent name)

/-- Apply a named certificate and preserve its remaining premise names. -/
private def applyNamedCertificate (goal : MVarId) (certificate : Name) : MetaM (List MVarId) := do
  let goals ← goal.applyConst certificate
  tagPremises goal certificate goals
  return goals

/-- Expose every matching named certificate as an Aesop alternative. Eager premises are solved
before exposing the remaining obligations, while different certificates keep independent
metavariable assignments until the surrounding proof search has also succeeded. -/
def applyCertificates (predicate : Name) : Aesop.RuleTac := fun input => input.goal.withContext do
  let target := (← instantiateMVars (← input.goal.getType)).consumeMData
  unless target.isAppOf predicate do throwError "expected an efficiency goal for {predicate}"
  let key ← efficiencyKey target
  let initial ← saveState
  let mut applications := #[]
  for (certificate, eager) in (certificateExt.getState (← getEnv)).getD key #[] do
    try
      let goals ← (Lean.Elab.Tactic.run input.goal <|
          Term.withoutErrToSorry <| withoutRecover do
        liftMetaTactic fun goal => applyNamedCertificate goal certificate
        eager.forM solveTagged).run'
      if ← Aesop.hasSorry (mkMVar input.goal) then
        throwError "certificate application contains an admitted premise"
      let goals ← goals.toArray.mapM (Aesop.mvarIdToSubgoal input.goal)
      applications := applications.push {
        goals
        postState := ← saveState
        scriptSteps? := none
        successProbability? := none }
    catch _ => pure ()
    finally initial.restore
  if applications.isEmpty then throwError "no certificate for `{key.2.1}` applies"
  return ⟨applications⟩

/-- Apply a rule with known arguments, leaving all remaining hypotheses as goals. -/
private def applyWithArguments (rule : Name) (arguments : Array (Name × Expr)) : TacticM Unit := do
  let mut proof ← mkConstWithFreshMVarLevels rule
  let mut type ← inferType proof
  while let .forallE name domain body _ := type do
    let arg ← match arguments.find? (fun argument => argument.1 == name) with
      | some (_, value) => pure value
      | none => mkFreshExprMVar domain
    unless ← isDefEq (← inferType arg) domain do throwError "argument type mismatch"
    proof := mkApp proof arg
    type := body.instantiate1 arg
    if name == arguments.back!.1 then
      let goal ← getMainGoal
      let goals ← goal.apply proof
      tagPremises goal rule goals
      replaceMainGoal goals
      return
  throwError "argument not found"

/-- Expose tuple components before higher-order unification matches a subroutine call. -/
private partial def prepareArgument (domain type : Expr) : MetaM Expr := do
  let type ← whnf type
  if type.isAppOf ``Prod then
    let args := type.getAppArgs
    let left ← prepareArgument domain args[0]!
    let right ← prepareArgument domain args[1]!
    withLocalDeclD `input domain fun input => do
      mkLambdaFVars #[input] (← mkAppM ``Prod.mk #[mkApp left input, mkApp right input])
  else
    mkFreshExprMVar (← mkArrow domain type)

/-- Apply local routine certificates through a composition rule, exposing tuple arguments.
Predicate parameters select the program; rule parameter names select the argument and certificate.
Each candidate retains separate assignments and leaves argument preparation to the surrounding
proof search, so other obligations can constrain its encoding. -/
def applyKnownCall (predicate : Name) (programIndex : Nat) (rule : Name)
    (argumentName certificateName : Name) : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    let target := (← instantiateMVars (← input.goal.getType)).consumeMData
    unless target.isAppOf predicate do throwError "expected an efficiency goal for {predicate}"
    let program := target.getAppArgs[programIndex]!
    if program.hasExprMVar then throwError "the called program is not determined"
    let head ← lambdaTelescope (← Core.betaReduce (← etaExpand program)) fun _ body =>
      pure body.getAppFn
    let initial ← saveState
    let mut applications := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || !decl.type.isAppOf predicate then continue
      let certified := decl.type.getAppArgs[programIndex]!
      let called ← lambdaTelescope (← Core.betaReduce (← etaExpand certified)) fun _ body =>
        pure body.getAppFn
      unless called == head do continue
      try
        let goals ← (Lean.Elab.Tactic.run input.goal <|
            Term.withoutErrToSorry <| withoutRecover do
          let domain := target.getAppArgs[0]!
          let argument ← prepareArgument domain decl.type.getAppArgs[0]!
          let composed ← withLocalDeclD `input domain fun input =>
            mkLambdaFVars #[input] (mkApp certified (mkApp argument input))
          unless ← isDefEq (← withReducible (reduce composed)) program do
            throwError "the certificate does not match this call"
          let argument ← instantiateMVars argument
          let idArg := mkLambda `x .default domain (mkBVar 0)
          if !argument.hasExprMVar && (← withReducible (isDefEq argument idArg)) then
            unless ← withReducible (isDefEq decl.type target) do
              throwError "the certificate encoding does not match this call"
            input.goal.assign decl.toExpr
            replaceMainGoal []
          else
            applyWithArguments rule #[(argumentName, argument), (certificateName, decl.toExpr)]
            if ← (← getGoals).anyM (fun goal => do isDefEq (← goal.getType) target) then
              throwError "composition made no progress").run'
        if ← Aesop.hasSorry (mkMVar input.goal) then
          throwError "routine application contains an admitted premise"
        let goals ← goals.toArray.mapM (Aesop.mvarIdToSubgoal input.goal)
        applications := applications.push {
          goals
          postState := ← saveState
          scriptSteps? := none
          successProbability? := none }
      catch _ => pure ()
      finally initial.restore
    if applications.isEmpty then throwError "no applicable local routine certificate"
    return ⟨applications⟩

/-- Apply a scan through each matching supplied callback before checking its list. Argument
preparation must prove the callback's exact encoding contract. Each application is independent;
ordinary certificate lookup remains a separate fallback if a later obligation rejects it. -/
def applyScanWithLocalCallback (predicate certificate : Name) : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    let initial ← saveState
    let mut applications := #[]
    try
      let goals ← applyNamedCertificate input.goal certificate
      let some callback ← goals.findM? fun goal => return (`htest).isSuffixOf (← goal.getTag)
        | throwError "scan has no callback premise"
      let knownCalls ← applyKnownCall predicate 2 (predicate ++ `comp) `g `hf
        { input with goal := callback }
      for matched in knownCalls.applications do
        try
          matched.postState.restore
          let remaining ← (Lean.Elab.Tactic.run input.goal <|
              Term.withoutErrToSorry <| withoutRecover do
            setGoals (matched.goals.toList.map (·.mvarId))
            evalTactic (← `(tactic| all_goals solve |
              aesop (config := { terminal := true, assumptionTransparency := .reducible })
                (rule_sets := [PolyTime])))
            if ← Aesop.hasSorry (mkMVar callback) then
              throwError "callback preparation contains an admitted premise"
            setGoals (← goals.filterM fun goal => return !(← goal.isAssigned))
            solveTagged `hlist).run'
          if ← Aesop.hasSorry (mkMVar input.goal) then
            throwError "scan application contains an admitted premise"
          applications := applications.push {
            goals := ← remaining.toArray.mapM (Aesop.mvarIdToSubgoal input.goal)
            postState := ← saveState
            scriptSteps? := none
            successProbability? := none }
        catch _ => pure ()
        finally initial.restore
    catch _ => pure ()
    finally initial.restore
    if applications.isEmpty then throwError "no supplied callback guides this scan"
    return ⟨applications⟩

end Cslib.Tactic
