/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Tactic.PolyTime.Init

/-!
# Synthesizing polynomial-time certificates

Adapted from the cslib `crypto` branch: named certificates are tried before their implementations
are unfolded. `fun_prop` handles composition; Aesop chooses loop rules and uses local growth
contracts. Plain and internal tidy goals use separate rules, with fixed machines and polynomial
bounds across all encoded inputs. Plain search applies plain statements directly; it does not
lower a goal or restate its hypotheses tidily. Unknown algorithms still require certificates.
On ordinary failure, `polytime` includes one failed compositional attempt when the backend has
reported one. This is a search hint, not a claim that the subterm is uncomputable. Resource-limit
and interrupt exceptions are unchanged.

## Main definitions

* `polytime`: prove a polynomial-time certificate using the `PolyTime` Aesop rule set.

## References

Adapted from Cslib/Tactic/PolyTime.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`; deterministic search consumes the canonical
plain calculus.
-/

public section

namespace Cslib.Tactic.PolyTime

open Turing.MultiTapeTM

-- These plain rules keep the public search in its own predicate. Their machine proofs may use
-- tidy witnesses, but the search never installs a transition between the two goal families.
-- Runtime `applyConst` needs these kernel declarations under a normal tactic import.
-- Keeping only private names makes source clients depend on unrelated producer proof imports.
namespace Internal

/-- Prepend a computed bit with both intermediate raw encodings fixed for the tactic. -/
theorem plainBitsCons {α : Type} {encIn : α ↪ List Bool}
    {f : α → Bool} {g : α → List Bool}
    (hf : ComputableInPolyTime f encIn encBool) (hg : ComputableInPolyTime g encIn encBits) :
    ComputableInPolyTime (fun a => f a :: g a) encIn encBits :=
  ComputableInPolyTime.bitsCons hf hg

/-- Append computed framed lists with their element encoding fixed for the tactic. -/
theorem plainListAppend {α β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool}
    {f g : α → List β} (hf : ComputableInPolyTime f encIn (encList enc))
    (hg : ComputableInPolyTime g encIn (encList enc)) :
    ComputableInPolyTime (fun a => f a ++ g a) encIn (encList enc) :=
  ComputableInPolyTime.listAppend' hf hg

/-- Prepend a computed element to a framed list with its element encoding fixed. -/
theorem plainListCons {α β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool}
    {f : α → β} {g : α → List β} (hf : ComputableInPolyTime f encIn enc)
    (hg : ComputableInPolyTime g encIn (encList enc)) :
    ComputableInPolyTime (fun a => f a :: g a) encIn (encList enc) :=
  ComputableInPolyTime.cons' hf hg

end Internal

@[aesop safe apply (rule_sets := [PolyTime])]
private theorem plainBoolNot {α : Type} {encIn : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInPolyTime f encIn encBool) :
    ComputableInPolyTime (fun a => !(f a)) encIn encBool :=
  ComputableInPolyTime.bool_not.comp hf

@[aesop unsafe 75% apply (rule_sets := [PolyTime])]
private theorem plainPiApply {α Index Value : Type} [Fintype Index]
    {input : α ↪ List Bool} {enc : Value ↪ List Bool} {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding) :
    ComputableInPolyTime (fun a => values a (index a)) input enc :=
  ComputableInPolyTime.pi_apply' hvalues hindex

-- Fix the pair-valued function before selecting its component encoding conversion.
attribute [aesop unsafe 80% apply (rule_sets := [PolyTime])]
  ComputableInPolyTime.fstWithEncoding ComputableInPolyTime.sndWithEncoding

attribute [aesop safe apply (rule_sets := [PolyTime])] ComputableInPolyTime.of_finite

-- Boolean scans hide the element encoding in their result. Resolve the list certificate before
-- searching for a joint callback certificate, including when the callback captures local values.
attribute [program_certificate hlist]
  ComputableInPolyTime.anyWithInput ComputableInPolyTime.allWithInput
  ComputableInPolyTime.mapToBitsWithInput
  ComputableInPolyTime.bitsFoldlWithInput
attribute [program_certificate] ComputableInPolyTime.bitsStrictMajorityWithInput

-- Expose inner table and loop obligations to Aesop when composition alone cannot finish them.
attribute [program_certificate hvalues] ComputableInPolyTime.pi_update'
attribute [program_certificate]
  ComputableInPolyTime.bitsReverseWithInput ComputableInPolyTime.listReverseWithInput

-- Require the growth contract before exploring encodings on alternative computation branches.
-- Each contract keeps the evidence that must agree on a bound or an encoding in one search.
attribute [program_certificate hbound hcompute]
  ComputableInPolyTime.foldlWithInput_of_bounded_growth
attribute [program_certificate hbound]
  ComputableInPolyTime.iterateWithInput_of_bounded_growth

open Lean Meta Elab Tactic in
/-- Synthesize a list interface once the list and element encodings are determined. -/
@[aesop safe tactic (rule_sets := [PolyTime])
  (index := [target ListEncoding _ _, target SizedListEncoding _ _])]
private meta def polytimeListInstance : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  if target.hasExprMVar then throwError "encoding is not yet determined"
  goal.assign (← synthInstance target)
  replaceMainGoal []

-- Computed finite tables use the ordinary application rule. Its function-valued head cannot
-- be registered as a `fun_prop` theorem, so Aesop supplies this closure step.
attribute [aesop unsafe 75% apply (rule_sets := [PolyTime])]
  ComputableInPolyTime.pi_apply'

open Lean Meta in
/-- Select the certificate family before searching, keeping plain goals in the plain calculus. -/
private meta def polytimePredicate (target : Expr) : MetaM Name := do
  let target := (← instantiateMVars target).consumeMData
  if target.isAppOf ``ComputableInPolyTime then return ``ComputableInPolyTime
  if target.isAppOf ``ComputableTidilyInPolyTime then return ``ComputableTidilyInPolyTime
  throwError "expected a polynomial-time goal"

open Lean Meta in
/-- Choose only the order of existing plain conditional recipes. Boolean guards retain their
arbitrary encoding; proposition guards use the decision encoding of `ite_decide`. Inspection
does not retain metavariable assignments, and both recipes remain available. -/
private meta def plainConditionalRules? (target : Expr) : MetaM (Option (Array Name)) := do
  let saved ← saveState
  try
    let target := (← instantiateMVars target).consumeMData
    unless target.isAppOf ``ComputableInPolyTime do return none
    Cslib.Tactic.withConditionalBody? target.getAppArgs[2]! fun body => do
      let condition ← whnfR body.getAppArgs[1]!
      let boolean := condition.isAppOfArity ``Eq 3 &&
        condition.getAppArgs[0]!.isConstOf ``Bool &&
        condition.getAppArgs[2]!.isConstOf ``Bool.true
      return if boolean then #[``ComputableInPolyTime.ite, ``ComputableInPolyTime.ite_decide]
        else #[``ComputableInPolyTime.ite_decide, ``ComputableInPolyTime.ite]
  finally saved.restore

/-- Expose local routine certificates and their argument obligations as search alternatives. -/
-- Equal priority lets argument goals run before expensive alternatives at the parent goal.
@[aesop unsafe 100% tactic (rule_sets := [PolyTime])]
private meta def polytimeKnownCall : Aesop.RuleTac := fun input => do
  let predicate ← input.goal.withContext do polytimePredicate (← input.goal.getType)
  Cslib.Tactic.applyKnownCall predicate 2 (predicate ++ `comp) `g `hf input

open Lean Meta Elab Tactic in
/-- Test whether any local routine certificate applies to the current goal. -/
private meta def hasLocalCall (goal : MVarId) : MetaM Bool := do
  try
    discard <| (polytimeKnownCall { (default : Aesop.RuleTacInput) with goal }).run' {}
    pure true
  catch _ => pure false

open Lean Meta Elab Tactic in
/-- Commit to decomposition only when no local certificate supplies an alternative. The matcher
restores the caller's state and leaves argument preparation open, so this tests applicability
without choosing an intermediate encoding. -/
private meta def withoutLocalCall (tactic : TacticM Unit) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  discard <| polytimePredicate (← goal.getType)
  if ← hasLocalCall goal then throwError "a local certificate is an alternative to decomposition"
  tactic

open Lean Meta Elab Tactic in
/-- Retain decomposition as an alternative when a local certificate competes with it. -/
private meta def withLocalCall (tactic : TacticM Unit) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  discard <| polytimePredicate (← goal.getType)
  unless ← hasLocalCall goal do throwError "no competing local certificate"
  tactic

/-- Expose named deterministic certificates as search alternatives. -/
@[aesop unsafe 99% tactic (rule_sets := [PolyTime])]
private meta def polytimeCertificate : Aesop.RuleTac := fun input => do
  let predicate ← input.goal.withContext do polytimePredicate (← input.goal.getType)
  Cslib.Tactic.applyCertificates predicate input

open Lean Meta in
/-- A supplied scan callback may constrain compatible encodings before the eager list proof.
The ordinary named-certificate rule retains the complete list-first alternative. -/
@[aesop unsafe 100% tactic (rule_sets := [PolyTime])]
private meta def polytimeScanKnownCallback : Aesop.RuleTac := fun input => input.goal.withContext do
  let target := (← instantiateMVars (← input.goal.getType)).consumeMData
  unless target.isAppOf ``ComputableInPolyTime do throwError "expected a plain scan goal"
  let key ← Cslib.Tactic.efficiencyKey target
  unless key.2.1 == ``List.any do throwError "expected a Boolean list scan"
  Cslib.Tactic.applyScanWithLocalCallback ``ComputableInPolyTime
    ``ComputableInPolyTime.anyWithInput input

open Lean Meta Elab Tactic in
/-- Decompose constructors before generic composition can guess intermediate encodings. -/
private meta def polytimeConstruct (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    let predicate ← polytimePredicate target
    let plain := predicate == ``ComputableInPolyTime
    let rawBits := target.getAppArgs[4]!.isConstOf ``encBits
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let rule ← lambdaTelescope program fun _ body => do
      if body.isAppOf ``HAppend.hAppend || body.isAppOf ``List.append then
        return if plain then
          (if rawBits then ``ComputableInPolyTime.bitsAppend else ``Internal.plainListAppend)
          else if rawBits then ``ComputableInPolyTime.bitsAppend
          else ``ComputableInPolyTime.listAppend'
      if body.isAppOf ``List.cons then
        return if plain then
          (if rawBits then ``Internal.plainBitsCons else ``Internal.plainListCons)
          else if rawBits then ``ComputableInPolyTime.bitsCons
          else ``ComputableInPolyTime.cons'
      if body.isAppOf ``Prod.mk then return ``ComputableInPolyTime.prod
      throwError "expected a constructor"
    guard <| liftMetaTactic fun goal => do
      let goals ← if plain then pure [goal] else goal.applyConst ``ComputableInPolyTime.tidy
      goals.flatMapM fun goal => goal.applyConst rule

open Lean Meta Elab Tactic in
/-- Restate complete supplied certificates using an explicit proved conversion. No premise is
synthesized, and quantified families retain all their data arguments. -/
private meta def restateKnownFacts (source conversion : Name) : TacticM Unit := withMainContext do
  let mut goal ← getMainGoal
  let mut added := false
  for h in ← getLCtx do
    unless h.isImplementationDetail do
      let proof? ← forallTelescopeReducing (← instantiateMVars h.type) fun xs conclusion => do
        -- Parameters may determine a complete supplied certificate family. Proof premises are
        -- not evidence: do not turn conditional implications into a request for raw search.
        if ← xs.anyM (fun x => return ← isProof x) then return none
        let conclusion := (← whnfR conclusion).consumeMData
        unless conclusion.isAppOf source && !conclusion.hasExprMVar do return none
        let proof ← mkAppM conversion #[mkAppN h.toExpr xs]
        return some (← mkLambdaFVars xs proof)
      if let some proof := proof? then
        let type ← inferType proof
        let found ← (← getLCtx).anyM fun other => do
          if other.isImplementationDetail then return false
          isDefEq other.type type
        unless found do
          let (_, next) ← goal.note (← mkFreshUserName `knownCertificate) proof
          goal := next
          added := true
  unless added do throwError "no new known certificate"
  replaceMainGoal [goal]

open Lean Meta Elab Tactic in
/-- Restate known local certificates in the goal's family. This introduces proof facts only;
it never changes the goal or searches the other calculus. -/
@[aesop safe -30 tactic (rule_sets := [PolyTime])]
private meta def polytimeKnownFacts : TacticM Unit := withMainContext do
  let predicate ← polytimePredicate (← getMainTarget)
  let (source, conversion) := if predicate == ``ComputableInPolyTime then
      (``ComputableTidilyInPolyTime, ``ComputableInPolyTime.of_tidy)
    else (``ComputableInPolyTime, ``ComputableInPolyTime.tidy)
  restateKnownFacts source conversion

open Lean Meta in
/-- Inspect proposition aliases with the same reducible transparency used by `fun_prop`.
`Meta.transform` maintains binder context, including dependent and quantified premises; data and
proof implementations are not unfolded merely to classify a transition's proposition. -/
private meta def rawTransitionPremise (type : Expr) : MetaM Bool := do
  let rawName := fun n : Name =>
    n.toString.startsWith "Turing.MultiTapeTM.ComputableTidily" ||
      n.toString.startsWith "Turing.MultiTapeTM.ComputesTidily"
  if (type.find? fun e => match e with
      | .const n _ => rawName n
      | _ => false).isSome then
    return true
  let inspect : StateRefT Bool MetaM Unit := do
    discard <| Meta.transform type (pre := fun e => do
      if ← get then return .done e
      let reduced ← if ← isProp e then whnfR e else pure e
      if let .const name _ := reduced.getAppFn then
        if rawName name then
          set true
          return .done reduced
      return .continue (some reduced))
  return (← inspect.run false).2

open Lean in
private meta structure PlainRuleCache where
  premises : Std.HashMap Name Bool := {}
  properties : Std.HashMap Name Bool := {}

/-- Empty per-invocation classification state. -/
private meta instance : Inhabited PlainRuleCache := ⟨{}⟩

open Lean in
private meta initialize rawPremiseCache : EnvExtension (Option PlainRuleCache) ←
  registerEnvExtension (pure none) (asyncMode := .local)

open Lean Meta in
/-- Inspect premises under their data parameters; a complete certificate has no raw premise. -/
private meta def typeHasRawPremise (type : Expr) : MetaM Bool :=
  forallTelescope type fun xs _ =>
    xs.anyM fun x => do
      let premise ← inferType x
      if ← isProp premise then rawTransitionPremise premise else pure false

open Lean Meta in
/-- Inspect a registered rule's hypotheses, including reducible proposition aliases. -/
private meta def hasRawPremise (name : Name) : MetaM Bool := do
  if let some result := (rawPremiseCache.getState (← getEnv)).bind
      (fun memo => memo.premises.get? name) then return result
  let some info := (← getEnv).find? name | return true
  typeHasRawPremise info.type

open Lean in
/-- Modify only the search's environment copy, including during asynchronous proof elaboration.
The change cannot escape `withEnv`, so it is local and needs no persistent write log. -/
private meta def searchRuleState {α β σ : Type} (ext : ScopedEnvExtension α β σ)
    (env : Environment) (f : σ → σ) : Environment :=
  ext.ext.modifyState (asyncMode := .local) (log := .unlogged) env fun s =>
    match s.stateStack with
    | top :: stack =>
      { s with stateStack := { top with state := f top.state } :: stack }
    | [] => s

open Lean Meta in
/-- Recognize raw properties themselves, including full-arity reducible aliases. -/
private meta def isRawProperty (name : Name) : MetaM Bool := do
  if let some result := (rawPremiseCache.getState (← getEnv)).bind
      (fun memo => memo.properties.get? name) then return result
  let some info := (← getEnv).find? name | return true
  forallTelescope info.type fun xs _ => do
    rawTransitionPremise (mkAppN (← mkConstWithLevelParams name) xs)

open Lean Meta Mathlib.Meta.FunProp in
/-- Shadow global function and composition rules only during public search. Local proof entries
and the original databases remain available outside it, including explicit raw construction. -/
private meta def plainRuleEnvironment (env : Environment) : MetaM Environment := do
  let mut seen : Std.HashSet Name := {}
  let mut blocked : Std.HashSet Name := {}
  for (_, properties) in (functionTheoremsExt.getState env).theorems do
    for (_, rules) in properties do
      for rule in rules do
        if let .decl name := rule.thmOrigin then
          unless seen.contains name do
            seen := seen.insert name
            if ← hasRawPremise name then blocked := blocked.insert name
  for (_, rules) in (lambdaTheoremsExt.getState env).theorems do
    for rule in rules do
      unless seen.contains rule.thmName do
        seen := seen.insert rule.thmName
        if ← hasRawPremise rule.thmName then blocked := blocked.insert rule.thmName
  let env := searchRuleState functionTheoremsExt env fun s =>
    { s with theorems := s.theorems.map fun _ properties => properties.map fun _ rules =>
      rules.filter fun rule => match rule.thmOrigin with
        | .decl name => !blocked.contains name
        | .fvar _ => true }
  let env := searchRuleState lambdaTheoremsExt env fun s =>
    { s with theorems := s.theorems.map fun _ rules =>
        rules.filter fun rule => !blocked.contains rule.thmName }
  let rawProperties ← (funPropDeclsExt.getState env).decls.foldValuesM
    (init := ({} : Std.HashSet Name)) fun names decl => do
      return if ← isRawProperty decl.funPropName then names.insert decl.funPropName else names
  -- Local implications are enumerated independently of the theorem tables. Their raw premises
  -- may use supplied assumptions, but cannot initiate raw function-property proof search.
  return searchRuleState funPropDeclsExt env fun s =>
    { s with decls := s.decls.fold (init := {}) fun tree _ decl =>
        if rawProperties.contains decl.funPropName then tree
        else tree.insertKeyValue decl.path decl }

open Lean Meta Mathlib.Meta.FunProp in
/-- Retain ordinary general rules while excluding raw construction premises.
Both evaluated entries and lazy entries must be removed from this per-search tree. -/
private meta def plainGeneralTheorems (thms : GeneralTheorems) : MetaM GeneralTheorems := do
  let mut names : Std.HashSet Name := {}
  for node in thms.theorems.tries do
    for rule in node.values do names := names.insert rule.thmName
    for (_, rule) in node.pending do names := names.insert rule.thmName
  let mut blocked : Std.HashSet Name := {}
  for name in names do
    if ← hasRawPremise name then blocked := blocked.insert name
  return { thms with theorems := { thms.theorems with
    tries := thms.theorems.tries.map fun node =>
      { node with
        values := node.values.filter fun rule => !blocked.contains rule.thmName
        pending := node.pending.filter fun entry => !blocked.contains entry.2.thmName } } }

open Lean Meta in
/-- Retain Aesop's local application alternatives and priority, excluding only rules which would
start raw search from a plain goal. Adapted from `Aesop.BuiltinRules.applyHyps` (Jannis Limperg). -/
meta def Internal.applyLocalCertificates : Aesop.RuleTac := fun input => input.goal.withContext do
  let rawGoal ← try
    pure ((← polytimePredicate (← input.goal.getType)) == ``ComputableTidilyInPolyTime)
  catch _ => pure false
  if rawGoal then return ← Aesop.BuiltinRules.applyHyps input
  let mut applications := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || (← typeHasRawPremise decl.type) then continue
    let saved ← saveState
    try
      applications := applications.push (← Aesop.BuiltinRules.applyHyp decl.fvarId input.goal
        input.options.applyHypsTransparency)
    catch _ => pure ()
    finally saved.restore
  return ⟨applications⟩

open Lean Meta in
/-- Project only the builtin local-application descriptor. Nested eager searches read this same
scoped rule set; all rule identity, indexing, priority, simp and simproc data are retained. -/
private meta def plainBuiltinEnvironment (env : Environment) : MetaM Environment := do
  let (ext, _, _, _, _) ← Aesop.Frontend.getGlobalRuleSetData `builtin
  let state := ext.getState env
  let initial := (({} : Aesop.Index Aesop.UnsafeRuleInfo), ({} : Std.HashSet Aesop.RuleName))
  let (index, matched) := state.unsafeRules.fold (init := initial) fun (index, matched) rule =>
    let isTarget := rule.name.name == ``Aesop.BuiltinRules.applyHyps
    let matched := if isTarget then matched.insert rule.name else matched
    let rule := if isTarget then
      { rule with tac := .ruleTac ``Internal.applyLocalCertificates } else rule
    (index.add rule rule.indexingMode, matched)
  unless matched.size == 1 do throwError "expected one builtin local-application rule"
  return searchRuleState ext env fun state => { state with unsafeRules := index }

open Lean Meta Mathlib.Meta.FunProp in
/-- Prepare only immutable global declaration classifications, never proofs or local evidence. -/
private meta def preparePlainRuleMemo : MetaM PlainRuleCache := do
  let env ← getEnv
  let mut names : Std.HashSet Name := {}
  for (_, properties) in (functionTheoremsExt.getState env).theorems do
    for (_, rules) in properties do
      for rule in rules do
        if let .decl name := rule.thmOrigin then names := names.insert name
  for (_, rules) in (lambdaTheoremsExt.getState env).theorems do
    for rule in rules do names := names.insert rule.thmName
  for (_, entries) in (Cslib.Tactic.certificateExt.getState env) do
    for (name, _) in entries do names := names.insert name
  for rules in #[morTheoremsExt.getState env, transitionTheoremsExt.getState env] do
    for node in rules.theorems.tries do
      for rule in node.values do names := names.insert rule.thmName
      for (_, rule) in node.pending do names := names.insert rule.thmName
  -- Imports are dependency-first. A theorem in a module with no raw-family declaration in
  -- its import closure cannot hide one behind an alias: aliases cannot refer to later modules.
  -- Unknown module metadata remains conservative, and current-module rules are always checked.
  let mut rawModules : Std.HashMap Name Bool := {}
  for i in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    let data := env.header.moduleData[i]!
    let ownsRaw := data.constNames.any fun name =>
      name.toString.startsWith "Turing.MultiTapeTM.ComputableTidily" ||
        name.toString.startsWith "Turing.MultiTapeTM.ComputesTidily"
    let importsRaw := data.imports.any fun imported => rawModules.getD imported.module true
    rawModules := rawModules.insert moduleName (ownsRaw || importsRaw)
  let mut cache : Std.HashMap Name Bool := {}
  for name in names do
    let mayUseRaw := match env.getModuleIdxFor? name with
      | some i => rawModules.getD env.header.moduleNames[i.toNat]! true
      | none => true
    cache := cache.insert name (← if mayUseRaw then hasRawPremise name else pure false)
  let properties ← (funPropDeclsExt.getState env).decls.foldValuesM
    (init := ({} : Std.HashMap Name Bool)) fun properties decl => do
      let mayUseRaw := match env.getModuleIdxFor? decl.funPropName with
        | some i => rawModules.getD env.header.moduleNames[i.toNat]! true
        | none => true
      let raw ← if mayUseRaw then isRawProperty decl.funPropName else pure false
      return properties.insert decl.funPropName raw
  return { premises := cache, properties }

open Lean Meta Elab Tactic in
/-- Reuse only global classification answers across one invocation. Rule tables, certificate
lookup, matching and local evidence are not projected or cached by this wrapper. -/
meta def Internal.withPlainRuleMemo (action : TacticM Unit) : TacticM Unit := do
  let env ← getEnv
  if (rawPremiseCache.getState env).isSome then
    action
  else
    let memo ← preparePlainRuleMemo
    withEnv (rawPremiseCache.setState env (some memo)) action

open Lean Meta Elab Tactic in
/-- Apply the deterministic boundary using the current tables and scoped classification memo.
Explicit raw construction entries and all named-certificate metadata retain their old policy. -/
meta def Internal.withPlainRuleCache (action : TacticM Unit) : TacticM Unit :=
  Internal.withPlainRuleMemo do
    let env ← getEnv
    let certificates ← (Cslib.Tactic.certificateExt.getState env).foldM (init := {})
      fun certificates key entries => do
        let entries ← if key.1 == ``ComputableTidilyInPolyTime then pure entries
          else entries.filterM fun (name, _) => return !(← hasRawPremise name)
        return certificates.insert key entries
    let env := searchRuleState Cslib.Tactic.certificateExt env fun _ => certificates
    let env ← plainBuiltinEnvironment env
    withEnv env action

open Lean Meta in
/-- Apply an existing fact only when matching its conclusion determines every argument. -/
private meta def matchLocalCertificate (fact : Expr) (target : Expr) : MetaM (Option Expr) := do
  let (xs, _, conclusion) ← forallMetaTelescope (← inferType fact)
  unless ← isDefEq conclusion target do return none
  let args ← xs.mapM instantiateMVars
  if args.any Expr.hasExprMVar then return none
  return some (mkAppN fact args)

open Lean Meta in
/-- Instantiate a supplied local certificate family without proving any new premise. Every
argument must be determined by the requested type; implications with missing evidence fail. -/
private meta def knownLocalCertificate (target : Expr) : MetaM (Option Expr) := do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let saved ← saveState
      let proof? ← matchLocalCertificate decl.toExpr target
      if proof?.isSome then return proof?
      saved.restore
  return none

open Lean Meta in
/-- Keep conditional guards and branches in joint search. Complete supplied guard evidence may
fix an encoding without an unsafe child-step penalty. The unprepared application is retained,
so that evidence and encoding alternatives remain available if later premises fail. -/
@[aesop unsafe 98% tactic (rule_sets := [PolyTime])]
private meta def polytimeConditional : Aesop.RuleTac := fun input => input.goal.withContext do
  let some rules ← plainConditionalRules? (← input.goal.getType)
    | throwError "expected a plain conditional program"
  let capture (goals : List MVarId) (probability : Float) : Aesop.BaseM Aesop.RuleApplication := do
    let goals ← goals.toArray.mapM (Aesop.mvarIdToSubgoal input.goal)
    return {
      goals
      postState := ← saveState
      scriptSteps? := none
      successProbability? := some ⟨probability⟩ }
  let initial ← saveState
  let mut applications := #[]
  for i in [:rules.size] do
    try
      let goals ← input.goal.applyConst rules[i]!
      let applied ← saveState
      let probability := if i == 0 then 0.98 else 0.97
      try
        let name := if rules[i]! == ``ComputableInPolyTime.ite then `hc else `hcondition
        if let some guard ← goals.findM? fun goal => return name.isSuffixOf (← goal.getTag) then
          let proof? ← guard.withContext do knownLocalCertificate (← guard.getType)
          if let some proof := proof? then
            guard.assign proof
            let remaining ← goals.filterM fun goal => return !(← goal.isAssignedOrDelayedAssigned)
            applications := applications.push (← capture remaining probability)
      catch _ => pure ()
      finally applied.restore
      applications := applications.push (← capture goals probability)
    catch _ => pure ()
    finally initial.restore
  if applications.isEmpty then throwError "no conditional recipe applies"
  return ⟨applications⟩

open Lean Meta Elab Tactic in
/-- Finish a supplied-guard conditional before a generic unsafe rule can close its parent.
Only supplied local evidence and conditional recipes run in this optional attempt; complete
proofs alone commit. Unresolved targets and competing local/named calls retain the
ordinary joint alternatives, including every unprepared application. -/
@[aesop safe -21 tactic (rule_sets := [PolyTime])]
private meta def polytimeConditionalFast : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  if target.hasExprMVar then throwError "conditional target is not yet determined"
  unless (← plainConditionalRules? target).isSome do
    throwError "expected a plain conditional program"
  if ← hasLocalCall goal then throwError "a local certificate precedes conditional decomposition"
  let key ← Cslib.Tactic.efficiencyKey target
  unless ((Cslib.Tactic.certificateExt.getState (← getEnv)).getD key #[]).isEmpty do
    throwError "a named certificate precedes conditional decomposition"
  let output ← (polytimeConditional { (default : Aesop.RuleTacInput) with goal }).run' {}
  for application in output.applications do
    let before ← saveState
    try
      application.postState.restore
      let goals := application.goals.toList.map (·.mvarId)
      if ← goals.anyM fun goal => do
          let tag ← goal.getTag
          return (`hc).isSuffixOf tag || (`hcondition).isSuffixOf tag then
        throwError "conditional guard needs joint search"
      setGoals goals
      unless goals.isEmpty do
        let known := mkIdent ``Internal.applyLocalCertificates
        -- Reuse the registered descriptor: resolving its private declaration by syntax
        -- would depend on whether the caller is elaborating an exported theorem.
        let env ← getEnv
        let (ext, _, _, _, _) ← Aesop.Frontend.getGlobalRuleSetData `PolyTime
        let index := (ext.getState env).unsafeRules.fold (init := {}) fun index rule =>
          if rule.name.name == ``polytimeConditional then index.add rule rule.indexingMode
          else index
        let env := searchRuleState ext env fun _ =>
          { Aesop.BaseRuleSet.empty with unsafeRules := index }
        withEnv env do
          evalTactic (← `(tactic| solve | all_goals
            aesop (config := { terminal := true, assumptionTransparency := .reducible })
              (rule_sets := [-builtin, -default, PolyTime])
              (add unsafe 100% tactic $known:ident)))
      if ← Aesop.hasSorry (mkMVar goal) then throwError "conditional premise was admitted"
      return
    catch _ => before.restore
  throwError "no supplied-guard conditional proof closed all premises"

open Lean in
/-- The current invocation's rendered hint. The reference survives search backtracking, but the
local environment containing it is discarded when the invocation finishes. -/
private meta initialize failureHint : EnvExtension (Option (IO.Ref (Option String))) ←
  registerEnvExtension (pure none) (asyncMode := .local)

open Lean Elab Tactic in
/-- Collect one backend hint without rerunning search. Each invocation, including a nested one,
has its own reference; `withEnv` restores the caller's environment even on resource exceptions.
The ordinary `catch` does not intercept Lean's resource-limit or interrupt exceptions. -/
private meta def withFailureHint (action : TacticM Unit) : TacticM Unit := do
  let hint ← IO.mkRef (none : Option String)
  try
    withEnv (failureHint.setState (← getEnv) (some hint)) action
  catch ex =>
    let some message ← hint.get | throw ex
    match ex with
    | .error ref messageData =>
      throw <| .error ref (messageData ++ .note m!"polytime could not certify a subterm in one \
        attempted route:\n{message}")
    | .internal .. => throw ex

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
/-- Shared compositional backend with a fresh alias-aware raw-premise boundary. The standard
assumption discharger and ordinary transition depth are retained; callers keep their step limit.
Consumers can reuse the same boundary for nested plain deterministic goals. -/
meta def Internal.funPropWithPlainBoundary (maxSteps : Nat) : TacticM Unit := do
  let saved ← saveState
  try
    restateKnownFacts ``ComputableTidilyInPolyTime ``ComputableInPolyTime.of_tidy
  catch _ => saved.restore
  -- `note` creates a generated goal context; nested search must use that current context.
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let disch : Expr → MetaM (Option Expr) := fun e => do
      if let some proof ← tacticToDischarge
          (← `(tactic| first | with_reducible assumption | infer_param)) e then return some proof
      if ← rawTransitionPremise e then knownLocalCertificate e else pure none
    let ctx : Mathlib.Meta.FunProp.Context := { config := { maxSteps }, disch }
    let env ← getEnv
    let state : Mathlib.Meta.FunProp.State := {
      morTheorems := ← plainGeneralTheorems (morTheoremsExt.getState env)
      transitionTheorems := ← plainGeneralTheorems (transitionTheoremsExt.getState env) }
    let ruleEnv ← plainRuleEnvironment env
    let (result, state) ← withEnv ruleEnv <| (funProp target ctx).run state
    let some result := result | do
      if let some hint := failureHint.getState (← getEnv) then
        if (← hint.get).isNone then
          -- FunProp rendered these strings while its telescope variables were in scope.
          -- Keep its first report, without retaining expressions from its failure cache.
          hint.set state.msgLog.getLast?
      throwError "no compositional plain certificate: {state.msgLog}"
    goal.assign result.proof
    replaceMainGoal []
open Lean Elab Tactic in
/-- Plain deterministic goals use the shared backend at their original step limit. -/
private meta def polytimePlainFunProp : TacticM Unit :=
  Internal.funPropWithPlainBoundary 256

open Lean Meta Elab Tactic in
/-- Check existing finite-domain or supplied-table recipes without retaining a proof,
encoding choice or metavariable assignment. The actual search keeps all alternatives. -/
private meta def hasPlainConstructionRecipe (goal : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    replaceMainGoal (← goal.applyConst ``ComputableInPolyTime.tidy)
    try polytimeKnownFacts catch _ => pure ()
    let plainGoal ← getMainGoal
    let before ← saveState
    try
      if (← plainGoal.applyConst ``ComputableInPolyTime.of_finite).isEmpty then return true
    catch _ => pure ()
    before.restore
    for rule in [``ComputableInPolyTime.pi_apply', ``ComputableInPolyTime.pi_update'] do
      let before ← saveState
      try
        let goals ← plainGoal.applyConst rule
        if let some values ← goals.findM? fun g => return (`hvalues).isSuffixOf (← g.getTag) then
          let known ← values.withContext do
            knownLocalCertificate (← values.getType)
          if known.isSome then return true
      catch _ => pure ()
      before.restore
    return false
  finally saved.restore

open Lean Meta Elab Tactic in
/-- An explicit raw construction goal may use an indexed plain certificate, an existing finite
recipe or a table recipe supported by complete local evidence. Nested search remains plain;
this rule never applies to a plain goal. -/
@[aesop unsafe 70% tactic (rule_sets := [PolyTime])]
private meta def polytimeRawFromPlain : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let goal ← getMainGoal
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOf ``ComputableTidilyInPolyTime do
      throwError "expected an explicit raw polynomial-time goal"
    let indexed ← try
      let key ← Cslib.Tactic.efficiencyKey target
      let plainKey := (``ComputableInPolyTime, key.2.1, key.2.2)
      let named := (Cslib.Tactic.certificateExt.getState (← getEnv)).getD plainKey #[]
      let functions ← Mathlib.Meta.FunProp.getTheoremsForFunction key.2.1 ``ComputableInPolyTime
      pure (!named.isEmpty || !functions.isEmpty)
    catch _ => pure false
    unless indexed || (← hasPlainConstructionRecipe goal) do
      throwError "no indexed or locally supported plain construction for this raw goal"
    -- Unification with a raw rule alone does not prove its premises. Retain this plain
    -- alternative after raw search fails, rather than vetoing it on application alone.
    replaceMainGoal (← goal.applyConst ``ComputableInPolyTime.tidy)
    evalTactic (← `(tactic| solve |
      aesop (config := { terminal := true, assumptionTransparency := .reducible })
        (rule_sets := [PolyTime])))
    if ← Aesop.hasSorry (mkMVar goal) then
      throwError "plain certificate search admitted a premise"

open Lean Meta Elab Tactic in
/-- Let compositional certificates finish a goal before trying loop specifications. -/
private meta def polytimeFunProp : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let predicate ← polytimePredicate (← getMainTarget)
    -- Plain search uses plain lemmas, never a transition to a raw construction predicate.
    -- A failed compositional attempt must leave time for the specification rules.
    if predicate == ``ComputableInPolyTime then
      polytimePlainFunProp
    else
      evalTactic (← `(tactic| solve | fun_prop (config := { maxSteps := 256 })))

/-- Expose a negated guard to loop rules when compositional proof search needs their help. -/
@[aesop unsafe 80% apply (rule_sets := [PolyTime])]
theorem bool_not_rule {α : Type} {input : α ↪ List Bool} {guard : α → Bool}
    (hguard : ComputableTidilyInPolyTime guard input encBool) :
    ComputableTidilyInPolyTime (fun a => !(guard a)) input encBool :=
  (ComputableInPolyTime.bool_not.comp (.of_tidy hguard)).tidy

/-- Fix a raw bit list's encoding and expose the two growth cases before proof search. -/
theorem foldl_bits_rule {γ β : Type} {encIn : γ ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List Bool} {init : γ → β} {step : β → Bool → β}
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun pair : β × Bool => step pair.1 pair.2)
      (encPair encB encBool) encB) {growth : ℕ}
    (hgrowth : ∀ state, (encB (step state false)).length ≤ (encB state).length + growth ∧
      (encB (step state true)).length ≤ (encB state).length + growth) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  (ComputableInPolyTime.foldl_of_bounded_growth (.of_tidy hlist) (.of_tidy hinit)
    (.of_tidy hstep)
    (fun state bit => by cases bit; exacts [(hgrowth state).1, (hgrowth state).2])).tidy

/-- Fix a framed list's encoding before proof search infers the element encoding. -/
theorem foldl_list_rule {γ α β : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun pair : β × α => step pair.1 pair.2)
      (encPair encB encA) encB) {growth : ℕ}
    (hgrowth : ∀ state value, (encB (step state value)).length ≤ (encB state).length + growth) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  (ComputableInPolyTime.foldl_of_bounded_growth (.of_tidy hlist) (.of_tidy hinit)
    (.of_tidy hstep) hgrowth).tidy

namespace Internal

/-- Fix a raw bit list's encoding and expose the two growth cases before proof search. -/
theorem plain_foldl_bits_rule {γ β : Type} {encIn : γ ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List Bool} {init : γ → β} {step : β → Bool → β}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun pair : β × Bool => step pair.1 pair.2)
      (encPair encB encBool) encB) {growth : ℕ}
    (hgrowth : ∀ state, (encB (step state false)).length ≤ (encB state).length + growth ∧
      (encB (step state true)).length ≤ (encB state).length + growth) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  ComputableInPolyTime.foldl_of_bounded_growth hlist hinit hstep
    (fun state bit => by cases bit; exacts [(hgrowth state).1, (hgrowth state).2])

/-- Fix a framed list's encoding before proof search infers the element encoding. -/
theorem plain_foldl_list_rule {γ α β : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun pair : β × α => step pair.1 pair.2)
      (encPair encB encA) encB) {growth : ℕ}
    (hgrowth : ∀ state value, (encB (step state value)).length ≤ (encB state).length + growth) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  ComputableInPolyTime.foldl_of_bounded_growth hlist hinit hstep hgrowth

end Internal

open Lean Meta Elab Tactic in
/-- Resolve the traversed list's encoding before certifying the step. Try a nonincreasing state
bound first, committing to it only after its growth obligation has been proved. -/
private meta def polytimeFold (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    let predicate ← polytimePredicate target
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let isFold ← lambdaTelescope program fun _ body => pure (body.isAppOf ``List.foldl)
    unless isFold do throwError "expected a list fold"
    guard do
      let rules := if predicate == ``ComputableInPolyTime then
        [``Internal.plain_foldl_bits_rule, ``Internal.plain_foldl_list_rule]
        else [``foldl_bits_rule, ``foldl_list_rule]
      for rule in rules do
        let saved ← saveState
        try
          liftMetaTactic fun goal => goal.applyConst rule
          evalTactic (← `(tactic| case hlist => solve |
            aesop (config := { terminal := true, assumptionTransparency := .reducible })
              (rule_sets := [PolyTime])))
          let afterList ← saveState
          try
            evalTactic (← `(tactic| case growth => exact 0))
            Cslib.Tactic.solveTagged `hgrowth
          catch _ =>
            afterList.restore
          return
        catch _ => saved.restore
      throwError "no supported list encoding"

namespace Internal

/-- The plain iteration rule retains the same constant additive growth contract. -/
theorem plainIterate {α β : Type} {encIn : α ↪ List Bool} {encState : β ↪ List Bool}
    {count : α → ℕ} {init : α → β} {step : β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    {growth : ℕ} (hgrowth : ∀ state, (encState (step state)).length ≤
      (encState state).length + growth) :
    ComputableInPolyTime (fun x => step^[count x] (init x)) encIn encState :=
  ComputableInPolyTime.iterate_of_bounded_growth hcount hinit hstep hgrowth

end Internal

open Lean Meta Elab Tactic in
/-- Apply the bounded-growth iteration rule once the goal is seen to be an iteration. -/
private meta def polytimeIterate (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    let predicate ← polytimePredicate target
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let isIter ← lambdaTelescope program fun _ body => pure (body.isAppOf ``Nat.iterate)
    unless isIter do throwError "expected an iteration"
    guard <| liftMetaTactic fun goal => do
      let goals ← if predicate == ``ComputableInPolyTime then pure [goal]
        else goal.applyConst ``ComputableInPolyTime.tidy
      goals.flatMapM fun goal => goal.applyConst ``Internal.plainIterate

attribute [aesop safe apply (rule_sets := [PolyTime])] Nat.le_refl

attribute [aesop norm simp (rule_sets := [PolyTime])] forall_and

-- Keep inexpensive structural successes and failures when no local certificate competes.
-- Aesop postpones safe rules that assign encoding metavariables. Complementary guards avoid
-- duplicating those alternatives while retaining decomposition if a local certificate fails.
@[aesop safe -25 tactic (rule_sets := [PolyTime])]
private meta def polytimeConstructFast : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    -- A raw constructor may also have an ordinary raw compositional proof. Preserve it as
    -- an alternative instead of committing to plain premises with no plain provider.
    if (← polytimePredicate (← Lean.Elab.Tactic.getMainTarget)) ==
        ``ComputableTidilyInPolyTime then
      throwError "raw construction retains compositional alternatives"
    polytimeConstruct withoutLocalCall

@[aesop safe -20 tactic (rule_sets := [PolyTime])]
private meta def polytimeFunPropFast : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    if (← plainConditionalRules? (← Lean.Elab.Tactic.getMainTarget)).isSome then
      throwError "conditional alternatives precede generic composition"
    withoutLocalCall polytimeFunProp

@[aesop safe 50 tactic (rule_sets := [PolyTime])]
private meta def polytimeFoldFast : Lean.Elab.Tactic.TacticM Unit :=
  polytimeFold withoutLocalCall

@[aesop safe tactic (rule_sets := [PolyTime])]
private meta def polytimeIterateFast : Lean.Elab.Tactic.TacticM Unit :=
  polytimeIterate withoutLocalCall

@[aesop unsafe 95% tactic (rule_sets := [PolyTime])]
private meta def polytimeConstructAlternative : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    if (← polytimePredicate (← Lean.Elab.Tactic.getMainTarget)) ==
        ``ComputableTidilyInPolyTime then
      polytimeConstruct (fun action => action)
    else
      polytimeConstruct withLocalCall

@[aesop unsafe 90% tactic (rule_sets := [PolyTime])]
private meta def polytimeFunPropAlternative : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    if (← plainConditionalRules? (← Lean.Elab.Tactic.getMainTarget)).isSome then
      polytimeFunProp
    else
      withLocalCall polytimeFunProp

@[aesop unsafe 85% tactic (rule_sets := [PolyTime])]
private meta def polytimeFoldAlternative : Lean.Elab.Tactic.TacticM Unit :=
  polytimeFold withLocalCall

@[aesop unsafe 85% tactic (rule_sets := [PolyTime])]
private meta def polytimeIterateAlternative : Lean.Elab.Tactic.TacticM Unit :=
  polytimeIterate withLocalCall

/-- Prove a polynomial-time certificate from known routines and controlled loop rules. -/
-- Unfold only reducible aliases when comparing assumptions. Ordinary program definitions may
-- contain large fixed enumerations; their named certificates should be tried before unfolding.
elab "polytime" : tactic => withFailureHint <| Internal.withPlainRuleCache do
  Lean.Elab.Tactic.evalTactic (← `(tactic| solve |
    aesop (config := { terminal := true, assumptionTransparency := .reducible })
      (rule_sets := [PolyTime])))

end Cslib.Tactic.PolyTime
