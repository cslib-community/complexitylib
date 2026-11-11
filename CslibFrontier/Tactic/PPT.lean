/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.PPT.Init
public import CslibFrontier.Tactic.PolyTime
public import CslibFrontier.Computability.Probabilistic.PPT.Capture
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Computability.Probabilistic.Adaptive
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Computability.Probabilistic.Memoize
public import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# Certifying functional probabilistic programs

`ppt` combines the proved closed and oracle PPT rules with deterministic `polytime` automation.
Programs use ordinary `do` notation, captured inputs and conditionals with plain
`ComputableInPolyTime` guards (`cond'`, `ite'`). Named and local certificates are reused, and
tuple arguments are prepared with the shared routine-call matcher. Closed proofs supply the
uniform strict fair-coin machine contract of `IsPPTOn`; `IsPPT` goals and local certificates
expose the standard unary-parameter/word encoding automatically.

Unknown algorithms need certificates. Fair bits, uniform words with efficiently computed unary
lengths, memoized closed samplers and bounded loops with additive state growth polynomial in the
original input are certified here. General loop invariants use `IsPPTOn.iterate_spec`.

Strict oracle PPT goals (`IsOraclePPTOn`, `IsOraclePPT`) search with the `OraclePPT`, `PPT` and
`PolyTime` Aesop rule sets while keeping `simp` disabled on oracle goals so charged reply prefixes
(`List.take _ <$> ProbOracleComp.query _`) are never fused into surrounding maps or binds. Local
and structure-field oracle routine calls prepare tuple arguments with `IsOraclePPTOn.preprocess'`;
`pure`, `ProbOracleComp.sample` and `query_take'` bridge to deterministic `PolyTime`, closed `PPT`
and plain request/limit bounds; sequencing, captured maps, plain conditionals and bounded-growth
`OracleComp.iterate` loops search jointly. Handler substitution and general adaptive loop
invariants keep their explicit theorems (`IsOraclePPT.run_interpret_preprocess'`,
`IsOraclePPTOn.iterate_spec'`, `IsOraclePPTOn.iterateWith_spec'`).

Before searching, `ppt [f, g]` unfolds the hinted definitions in the goal and inlines the `let`s
they expose. Every form also unfolds local encoding `let`s and adds the certificates stored in
fields of local structures as local facts, as `polytime` does.
On ordinary failure, `ppt` includes one failed compositional attempt when the backend has
reported one, as `polytime` does.

## Main definitions

* `ppt`: prove a closed or oracle encoded PPT certificate, searching with `[PPT, PolyTime]` on
  closed goals and `[OraclePPT, PPT, PolyTime]` (without `simp` on oracle goals) on oracle goals.

## References

Adapted from Cslib/Tactic/PPT.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine realization and tidy calculus.
-/

public section

namespace Cslib.Tactic.PPT

open Lean Meta Elab Tactic Probability

/-- Iteration of a strict oracle PPT step that never increases its encoded state needs no
additive growth constant. -/
theorem Internal.oracleIterate_of_length_le {Operation α σ : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {stateEncoding : σ ↪ List Bool}
    {initial : α → σ} {count : α → ℕ} {step : σ → WordOracleComp Operation σ}
    (hcount : Turing.MultiTapeTM.ComputableInPolyTime count input Turing.MultiTapeTM.encUnary)
    (hinitial : Turing.MultiTapeTM.ComputableInPolyTime initial input stateEncoding)
    (hstep : IsOraclePPTOn stateEncoding stateEncoding step)
    (hshrink : ∀ state, ∀ next ∈ OracleComp.support (step state),
      (stateEncoding next).length ≤ (stateEncoding state).length) :
    IsOraclePPTOn input stateEncoding
      (fun a => OracleComp.iterate (count a) step (initial a)) :=
  IsOraclePPTOn.iterate_of_bounded_growth' hcount hinitial hstep (growth := 0)
    (by simpa only [Nat.add_zero] using hshrink)

attribute [aesop norm unfold (rule_sets := [PPT])] IsPPT

/-- Prepare local probabilistic routine calls through the same matcher as deterministic calls. -/
@[aesop unsafe 99% tactic (rule_sets := [PPT])]
private meta def pptKnownCall : Aesop.RuleTac :=
  Cslib.Tactic.applyKnownCall ``IsPPTOn 4 ``IsPPTOn.preprocess `prepare `hprogram

/-- Expose named probabilistic certificates as search alternatives. -/
@[aesop unsafe 99% tactic (rule_sets := [PPT])]
private meta def pptCertificate : Aesop.RuleTac :=
  Cslib.Tactic.applyCertificates ``IsPPTOn

/-- Apply a composition theorem with named explicit or implicit arguments, leaving remaining
premises as subgoals. -/
private meta def applyWithArguments (rule : Name) (arguments : Array (Name × Expr)) :
    TacticM Unit := do
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
      replaceMainGoal goals
      return
  throwError "argument not found"

/-- Expose tuple components before higher-order unification matches an oracle subroutine call. -/
private meta partial def prepareOracleArgument (domain type : Expr) : MetaM Expr := do
  let type ← whnf type
  if type.isAppOf ``Prod then
    let args := type.getAppArgs
    let left ← prepareOracleArgument domain args[0]!
    let right ← prepareOracleArgument domain args[1]!
    withLocalDeclD `input domain fun input => do
      mkLambdaFVars #[input] (← mkAppM ``Prod.mk #[mkApp left input, mkApp right input])
  else
    mkFreshExprMVar (← mkArrow domain type)

/-- Prepare local strict oracle PPT routine calls through `IsOraclePPTOn.preprocess'`, reading the
input domain after the leading `Operation` parameter of `IsOraclePPTOn`. -/
@[aesop unsafe 99% tactic (rule_sets := [OraclePPT])]
private meta def oraclePptKnownCall : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    let target := (← instantiateMVars (← input.goal.getType)).consumeMData
    unless target.isAppOfArity ``IsOraclePPTOn 7 do
      throwError "expected an encoded-input oracle PPT goal"
    let program := target.getAppArgs[6]!
    if program.hasExprMVar then throwError "the called oracle program is not determined"
    let head ← lambdaTelescope (← Core.betaReduce (← etaExpand program)) fun _ body =>
      pure body.getAppFn
    let initial ← saveState
    let mut applications := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || !decl.type.isAppOfArity ``IsOraclePPTOn 7 then continue
      let certified := decl.type.getAppArgs[6]!
      let called ← lambdaTelescope (← Core.betaReduce (← etaExpand certified)) fun _ body =>
        pure body.getAppFn
      unless called == head do continue
      try
        let goals ← (Lean.Elab.Tactic.run input.goal <|
            Term.withoutErrToSorry <| withoutRecover do
          let domain := target.getAppArgs[1]!
          let argument ← prepareOracleArgument domain decl.type.getAppArgs[1]!
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
            applyWithArguments ``IsOraclePPTOn.preprocess'
              #[(`prepare, argument), (`hprogram, decl.toExpr)]
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
    if applications.isEmpty then throwError "no applicable local oracle routine certificate"
    return ⟨applications⟩

/-- Whether `fn` is `List.take n` or `fun r => List.take n r`. -/
private meta def isListTakeFn (fn : Expr) : MetaM Bool := do
  if fn.isAppOf ``List.take then return true
  lambdaTelescope fn fun xs body =>
    return xs.size == 1 && body.isAppOfArity ``List.take 3 && body.getAppArgs[2]! == xs[0]!

/-- Select the primitive oracle bridge matching a syntactic or reducible program body. -/
private meta def oracleCertificateForBody? (body : Expr) : MetaM (Option Name) := do
  if body.isAppOf ``Pure.pure then
    return some ``Turing.MultiTapeTM.ComputableInPolyTime.isOraclePPTOn
  if body.isAppOf ``ProbOracleComp.sample then
    return some ``Cslib.Probability.IsPPTOn.isOraclePPTOn
  if body.isAppOfArity ``Functor.map 6 && body.getAppArgs[5]!.isAppOf ``ProbOracleComp.query then
    if ← isListTakeFn body.getAppArgs[4]! then
      return some ``Cslib.Probability.IsOraclePPTOn.query_take'
  return none

/-- Bridge pure values, sampled closed programs and charged `List.take` oracle queries to their
plain subgoals so surrounding `PolyTime` and `PPT` rules can discharge them. -/
@[aesop unsafe 99% tactic (rule_sets := [OraclePPT])]
private meta def oraclePptCertificate : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    let target := (← instantiateMVars (← input.goal.getType)).consumeMData
    unless target.isAppOfArity ``IsOraclePPTOn 7 do
      throwError "expected an encoded-input oracle PPT goal"
    let program := target.getAppArgs[6]!
    if program.hasExprMVar then throwError "the oracle program is not determined"
    let rule ← lambdaTelescope (← Core.betaReduce (← etaExpand program)) fun _ body => do
      if let some rule ← oracleCertificateForBody? body then return rule
      if let some rule ← oracleCertificateForBody? (← whnfR body) then return rule
      throwError "no primitive oracle PPT certificate for program head"
    let initial ← saveState
    try
      let goals ← (Lean.Elab.Tactic.run input.goal <|
          Term.withoutErrToSorry <| withoutRecover do
        liftMetaTactic fun goal => goal.applyConst rule).run'
      if ← goals.anyM fun g => return !(← isProp (← g.getType)) then
        throwError "oracle certificate left an undetermined data parameter"
      if ← Aesop.hasSorry (mkMVar input.goal) then
        throwError "certificate application contains an admitted premise"
      let subgoals ← goals.toArray.mapM (Aesop.mvarIdToSubgoal input.goal)
      let app : Aesop.RuleApplication := {
        goals := subgoals
        postState := ← saveState
        scriptSteps? := none
        successProbability? := none }
      initial.restore
      return ⟨#[app]⟩
    catch e =>
      initial.restore
      throw e

/-- Let compositional rules finish a closed PPT goal before exposing individual monadic binds. -/
@[aesop safe -20 tactic (rule_sets := [PPT])]
private meta def pptFunProp : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOfArity ``IsPPTOn 5 do throwError "expected an encoded-input PPT goal"
    if target.getAppArgs[2]!.hasExprMVar then throwError "input encoding is not yet determined"
    Cslib.Tactic.PolyTime.Internal.funPropWithPlainBoundary 128

/-- Let plain compositional rules finish an oracle PPT goal before splitting binds, while
delegating top-level conditionals and `OracleComp.iterate` loops directly to their rules. -/
@[aesop safe -20 tactic (rule_sets := [OraclePPT])]
private meta def oraclePptFunProp : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOfArity ``IsOraclePPTOn 7 do
      throwError "expected an encoded-input oracle PPT goal"
    if target.getAppArgs[4]!.hasExprMVar then throwError "input encoding is not yet determined"
    let program := target.getAppArgs[6]!
    if (program.find? (·.isConstOf ``OracleComp.iterate)).isSome then
      throwError "oracle iterations use explicit loop rules"
    if (← Cslib.Tactic.withConditionalBody? program fun _ => pure true).isSome then
      throwError "conditional alternatives precede generic composition"
    Cslib.Tactic.PolyTime.Internal.funPropWithPlainBoundary 128

attribute [program_certificate]
  Turing.MultiTapeTM.ComputableInPolyTime.isPPTOn
  isPPTOn_sampleList
  Turing.MultiTapeTM.ComputableInPolyTime.sampleList
  isPPTOn_uniform_bool
  IsPPTOn.memoize

/-- Expose monadic sequencing and captured maps to Aesop's joint search, retaining alternatives for
the intermediate encoding until both stages have been proved. -/
private meta def applyCaptured (predicate bindRule mapRule : Name) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
    unless target.isAppOf predicate do throwError "expected an encoded-input {predicate} goal"
    let rule ← lambdaTelescope target.getAppArgs.back! fun _ body => do
      if body.isAppOf ``Bind.bind then return bindRule
      if body.isAppOf ``Functor.map then return mapRule
      throwError "expected probabilistic sequencing"
    liftMetaTactic fun goal => goal.applyConst rule

/-- Expose closed probabilistic sequencing and captured maps. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptCaptured : TacticM Unit :=
  applyCaptured ``IsPPTOn ``IsPPTOn.bind_with ``IsPPTOn.map_with

/-- Expose strict oracle probabilistic sequencing and plain captured maps. -/
@[aesop unsafe 80% tactic (rule_sets := [OraclePPT])]
private meta def oraclePptCaptured : TacticM Unit :=
  applyCaptured ``IsOraclePPTOn ``IsOraclePPTOn.bind_with ``IsOraclePPTOn.map_with'

/-- Only a syntactic conditional can use branch selection. Trying these theorems on arbitrary
named programs can unfold their implementations during unification before certificate children
are explored. Named calls retain their existing alternative search. -/
private meta def applyConditional (predicate rule : Name) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf predicate do throwError "expected an encoded-input {predicate} goal"
    let conditional? ← Cslib.Tactic.withConditionalBody? target.getAppArgs.back!
      fun _ => pure true
    unless conditional?.isSome do throwError "expected a conditional program"
    liftMetaTactic fun goal => goal.applyConst rule

/-- Closed Boolean branch selection with a plain polynomial-time condition. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptCond : TacticM Unit :=
  applyConditional ``IsPPTOn ``IsPPTOn.cond'

/-- Closed proposition branch selection with a plain polynomial-time decision. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptIte : TacticM Unit :=
  applyConditional ``IsPPTOn ``IsPPTOn.ite'

/-- Strict oracle Boolean branch selection with a plain polynomial-time condition. -/
@[aesop unsafe 80% tactic (rule_sets := [OraclePPT])]
private meta def oraclePptCond : TacticM Unit :=
  applyConditional ``IsOraclePPTOn ``IsOraclePPTOn.cond'

/-- Strict oracle proposition branch selection with a plain polynomial-time decision. -/
@[aesop unsafe 80% tactic (rule_sets := [OraclePPT])]
private meta def oraclePptIte : TacticM Unit :=
  applyConditional ``IsOraclePPTOn ``IsOraclePPTOn.ite'

/-- Loop rules inspect only an actual iteration, including reducible wrappers. Arbitrary named
programs must not unfold during loop-rule unification before their certificate children run. -/
private meta def applyIterate (predicate rule : Name) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf predicate do throwError "expected an encoded-input {predicate} goal"
    let program ← Core.betaReduce (← etaExpand target.getAppArgs.back!)
    let iteration ← lambdaTelescope program fun _ body => do
      if body.isAppOf ``OracleComp.iterate then return true
      return (← whnfR body).isAppOf ``OracleComp.iterate
    unless iteration do throwError "expected a probabilistic iteration"
    liftMetaTactic fun goal => goal.applyConst rule

/-- Retain the nonincreasing-state closed iteration alternative at its original priority. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptIterateLength : TacticM Unit :=
  applyIterate ``IsPPTOn ``IsPPTOn.iterate_of_length_le

/-- Retain the fixed additive growth closed iteration alternative. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptIterateGrowth : TacticM Unit :=
  applyIterate ``IsPPTOn ``IsPPTOn.iterate_of_bounded_growth

/-- Retain captured closed iteration with its polynomial input-dependent growth obligation. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptIterateCaptured : TacticM Unit :=
  applyIterate ``IsPPTOn ``IsPPTOn.iterateWith_of_bounded_growth

/-- Nonincreasing-state strict oracle iteration. -/
@[aesop unsafe 80% tactic (rule_sets := [OraclePPT])]
private meta def oraclePptIterateLength : TacticM Unit :=
  applyIterate ``IsOraclePPTOn ``Internal.oracleIterate_of_length_le

/-- Constant additive-growth strict oracle iteration. -/
@[aesop unsafe 80% tactic (rule_sets := [OraclePPT])]
private meta def oraclePptIterateGrowth : TacticM Unit :=
  applyIterate ``IsOraclePPTOn ``IsOraclePPTOn.iterate_of_bounded_growth'

/-- Captured strict oracle iteration with a polynomially bounded input-dependent growth
allowance. -/
@[aesop unsafe 80% tactic (rule_sets := [OraclePPT])]
private meta def oraclePptIterateCaptured : TacticM Unit :=
  applyIterate ``IsOraclePPTOn ``IsOraclePPTOn.iterateWith_of_bounded_growth'

/-- Unfold parameterized oracle PPT (`IsOraclePPT`) to its encoded-input form in the goal and
the hypotheses, and expose bundled `Finite Operation` facts from local `IsOraclePPTOn`
certificates when typeclass synthesis does not already find one. -/
private meta def unfoldOracleParameter : TacticM Unit := withMainContext do
  let parameterized := (· == `Cslib.Probability.IsOraclePPT)
  let mut goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let expanded ← deltaExpand target parameterized
  if expanded != target then goal ← goal.replaceTargetDefEq expanded
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    let expanded ← deltaExpand type parameterized
    if expanded != type then goal ← goal.replaceLocalDeclDefEq decl.fvarId expanded
  let ops ← goal.withContext do
    let mut ops : Array Expr := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || decl.isLet then continue
      let type ← instantiateMVars decl.type
      if type.isAppOfArity ``IsOraclePPTOn 7 then
        let opType := type.getAppArgs[0]!
        let finType ← mkAppM ``Finite #[opType]
        if (← synthInstance? finType).isNone then
          ops := ops.push (← mkAppM ``IsOraclePPTOn.finite_operations #[decl.toExpr])
    pure ops
  for proof in ops do
    let finType ← inferType proof
    let hasNow ← goal.withContext do pure (← synthInstance? finType).isSome
    unless hasNow do
      let (_, next) ← goal.note (← mkFreshUserName `finiteOp) proof
      goal := next
  replaceMainGoal [goal]

/-- Whether `type` is an oracle PPT goal (possibly under binders or conjunctions) whose `List.take`
reply prefixes must not be rewritten by `@[simp]` lemmas such as `Functor.map_map` or
`bind_map_left`. -/
private meta partial def hasOraclePPTGoal (type : Expr) : Bool :=
  match type.consumeMData with
  | .forallE _ _ body _ => hasOraclePPTGoal body
  | .letE _ _ _ body _ => hasOraclePPTGoal body
  | e =>
    if e.isAppOfArity ``And 2 then
      hasOraclePPTGoal e.getAppArgs[0]! || hasOraclePPTGoal e.getAppArgs[1]!
    else
      let fn := e.getAppFn
      fn.isConstOf ``IsOraclePPTOn || fn.isConstOf `Cslib.Probability.IsOraclePPT

/-- Delegate a non-oracle subgoal to a `PolyTime` `TacticM Unit` rule identified by suffix. -/
private meta def runNonOraclePolyTimeSimp (suffix : Name) : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    if hasOraclePPTGoal (← instantiateMVars (← input.goal.getType)) then
      throwError "oracle PPT goals preserve query structure"
    let (ext, _, _, _, _) ← Aesop.Frontend.getGlobalRuleSetData `PolyTime
    let state := ext.getState (← getEnv)
    let some decl := state.ruleNames.foldl (init := none) fun found name _ =>
        if suffix.isSuffixOf name then some name else found
      | throwError "expected PolyTime rule `{suffix}`"
    Aesop.RuleTac.tacticM decl input

/-- `PolyTime` normalization simp skipped on oracle PPT goals so charged queries stay intact. -/
meta def Internal.nonOracleNormSimp : Aesop.RuleTac :=
  runNonOraclePolyTimeSimp `polytimeNormSimp

/-- `PolyTime` fallback simp skipped on oracle PPT goals so charged queries stay intact. -/
meta def Internal.nonOracleSimpFallback : Aesop.RuleTac :=
  runNonOraclePolyTimeSimp `polytimeSimpFallback

/-- Modify only the current search's scoped rule-set copy inside `withEnv`. -/
private meta def modifyLocalRuleState {α β σ : Type} (ext : ScopedEnvExtension α β σ)
    (env : Environment) (f : σ → σ) : Environment :=
  ext.ext.modifyState (asyncMode := .local) (log := .unlogged) env fun s =>
    match s.stateStack with
    | top :: stack =>
      { s with stateStack := { top with state := f top.state } :: stack }
    | [] => s

/-- Guard `PolyTime`'s custom simp rules against rewriting oracle PPT goals during oracle search,
while keeping full normalization on deterministic, closed PPT and arithmetic side goals. -/
private meta def oraclePolyTimeEnvironment (env : Environment) : MetaM Environment := do
  let (ext, _, _, _, _) ← Aesop.Frontend.getGlobalRuleSetData `PolyTime
  let state := ext.getState env
  let initNorm := (({} : Aesop.Index Aesop.NormRuleInfo), ({} : Std.HashSet Aesop.RuleName))
  let (normRules, matchedNorm) := state.normRules.fold (init := initNorm)
    fun (index, matched) rule =>
      let isTarget := (`polytimeNormSimp).isSuffixOf rule.name.name
      let matched := if isTarget then matched.insert rule.name else matched
      let rule := if isTarget then
        { rule with tac := .ruleTac ``Internal.nonOracleNormSimp } else rule
      (index.add rule rule.indexingMode, matched)
  unless matchedNorm.size == 1 do throwError "expected one PolyTime norm simp rule"
  let initUnsafe := (({} : Aesop.Index Aesop.UnsafeRuleInfo), ({} : Std.HashSet Aesop.RuleName))
  let (unsafeRules, matchedUnsafe) := state.unsafeRules.fold (init := initUnsafe)
    fun (index, matched) rule =>
      let isTarget := (`polytimeSimpFallback).isSuffixOf rule.name.name
      let matched := if isTarget then matched.insert rule.name else matched
      let rule := if isTarget then
        { rule with tac := .ruleTac ``Internal.nonOracleSimpFallback } else rule
      (index.add rule rule.indexingMode, matched)
  unless matchedUnsafe.size == 1 do throwError "expected one PolyTime fallback simp rule"
  return modifyLocalRuleState ext env fun state => { state with normRules, unsafeRules }

/-- Certify a closed or oracle probabilistic program using proved sampling, composition and
deterministic rules. Goals may be `IsPPTOn`, `IsPPT`, `IsOraclePPTOn` or `IsOraclePPT`.

`ppt [f, g]` first unfolds the definitions `f` and `g` in the goal. Like `polytime`, every form
replaces local encoding `let`s by their values and adds the certificates stored in fields of local
structures (`S.encrypt_ppt`, `hA.guess`, …) as local facts. -/
syntax (name := pptTactic) "ppt" (" [" ident,* "]")? : tactic

/-- Elaborate `ppt`: prepare the goal and unfold `IsOraclePPT` before and after exposing structure
fields, then search with `[OraclePPT, PPT, PolyTime]` (preserving query syntax) on oracle goals or
`[PPT, PolyTime]` on closed goals. -/
@[tactic pptTactic] meta def evalPPT : Tactic := fun stx => do
  let hints := match stx with
    | `(tactic| ppt [$hints,*]) => hints.getElems
    | _ => #[]
  unfoldOracleParameter
  Cslib.Tactic.PolyTime.Internal.prepareGoal hints
  unfoldOracleParameter
  let oracle := hasOraclePPTGoal (← instantiateMVars (← getMainTarget))
  Cslib.Tactic.PolyTime.Internal.withFailureHint "ppt" <|
      Cslib.Tactic.PolyTime.Internal.withPlainRuleCache do
    if oracle then
      let env ← oraclePolyTimeEnvironment (← getEnv)
      withEnv env do
        evalTactic (← `(tactic| solve |
          aesop
            (config :=
              { terminal := true
                enableSimp := false
                assumptionTransparency := .reducible })
            (rule_sets := [OraclePPT, PPT, PolyTime])))
    else
      evalTactic (← `(tactic| solve |
        aesop (config := { terminal := true, assumptionTransparency := .reducible })
          (rule_sets := [PPT, PolyTime])))

end Cslib.Tactic.PPT

end
