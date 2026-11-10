/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Tactic.PPT
import all CslibFrontier.Tactic.PolyTime

/-! # Shared classification of imported plain-search rules

`polytime` and `ppt` classify each imported rule once per file (#1155), not once per call. These
controls check that this classification gives the answers a fresh one gives, that local attribute
changes keep each call's outcome, and that the per-call cost stays below its old floor.
`ppt` failures name the subterm they could not certify, like `polytime` failures.
-/

open Lean Meta Elab Tactic Turing.MultiTapeTM Cslib.Tactic.PolyTime

namespace CslibFrontierTests.PolyTimeRuleClassCache

/-- Check one invocation's classification state: whether it uses the file's shared
classifications, that its own memo then holds no imported rule, and that every shared answer
equals a fresh classification under the current environment. -/
private meta def checkClassifications (expectShared : Bool) : TacticM Unit :=
  Internal.withPlainRuleMemo do
    let env ← getEnv
    let some memo := rawPremiseCache.getState env | throwError "no classification memo"
    unless memo.shared.isSome == expectShared do
      throwError "expected shared classifications: {expectShared}"
    let some shared := memo.shared | return
    if memo.premises.toList.any fun (name, _) => (env.getModuleIdxFor? name).isSome then
      throwError "the invocation memo classified an imported rule"
    let cache ← shared.get
    if cache.premises.isEmpty then throwError "no imported rule has been classified"
    let rawModules := (rawImportClosureExt.getState env).get
    for (name, cached) in cache.premises.toList do
      let some info := env.find? name | throwError "unknown rule {name}"
      let some i := env.getModuleIdxFor? name | throwError "{name} is not imported"
      let fresh ← if rawModules.getD env.header.moduleNames[i.toNat]! true then
        typeHasRawPremise info.type else pure false
      unless fresh == cached do throwError "stale classification of {name}"

elab (name := expectSharedClassifications) "expect_shared_classifications" : tactic =>
  checkClassifications true

elab (name := expectInvocationClassifications) "expect_invocation_classifications" : tactic =>
  checkClassifications false

local allow_unused_tactic expectSharedClassifications expectInvocationClassifications

variable {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}

set_option maxHeartbeats 20000 in
-- Each call pays only for its own search once imported rules are classified. Classifying them
-- on every call made these eight calls cost about 36,000 heartbeats; with shared classification
-- they cost about 5,400, or 11,400 when this proof is the first to classify them.
example (f g : List Bool → List Bool)
    (hf : ComputableInPolyTime f encBits encBits)
    (hg : ComputableInPolyTime g encBits encBits) :
    ComputableInPolyTime (fun word => g (f word) ++ word) encBits encBits := by
  have h₁ : ComputableInPolyTime (fun word => g (f word) ++ word) encBits encBits := by polytime
  have : ComputableInPolyTime (fun word => f (g word) ++ word) encBits encBits := by polytime
  have : ComputableInPolyTime (fun word => f (f word) ++ word) encBits encBits := by polytime
  have : ComputableInPolyTime (fun word => g (g word) ++ word) encBits encBits := by polytime
  have : ComputableInPolyTime (fun word => word ++ g (f word)) encBits encBits := by polytime
  have : ComputableInPolyTime (fun word => word ++ f (g word)) encBits encBits := by polytime
  have : ComputableInPolyTime (fun word => f word ++ g word) encBits encBits := by polytime
  have : ComputableInPolyTime (fun word => g word ++ f word) encBits encBits := by polytime
  exact h₁

example : True := by
  expect_shared_classifications
  trivial

-- A local `fun_prop` registration of an imported rule takes effect, and ends with its section.
example {list : α → List β} {f : α → β → List Bool}
    (_hlist : ComputableInPolyTime list input (encList enc))
    (_hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2) (encPair input enc) encBits) :
    True := by
  fail_if_success
    have : ComputableInPolyTime (fun a => (list a).flatMap (f a)) input encBits := by polytime
  trivial

section

attribute [local fun_prop] ComputableInPolyTime.flatMapToBitsWithInput

example {list : α → List β} {f : α → β → List Bool}
    (hlist : ComputableInPolyTime list input (encList enc))
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2) (encPair input enc) encBits) :
    ComputableInPolyTime (fun a => (list a).flatMap (f a)) input encBits := by
  expect_shared_classifications
  polytime

end

-- So does a local `program_certificate` registration of an imported theorem.
section

attribute [local program_certificate] ComputableInPolyTime.flatMapToBitsWithInput

example {list : α → List β} {f : α → β → List Bool}
    (hlist : ComputableInPolyTime list input (encList enc))
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2) (encPair input enc) encBits) :
    ComputableInPolyTime (fun a => (list a).flatMap (f a)) input encBits := by
  polytime

end

example {list : α → List β} {f : α → β → List Bool}
    (_hlist : ComputableInPolyTime list input (encList enc))
    (_hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2) (encPair input enc) encBits) :
    True := by
  fail_if_success
    have : ComputableInPolyTime (fun a => (list a).flatMap (f a)) input encBits := by polytime
  trivial

-- Making the `Prop`-valued predicate irreducible keeps the shared classifications and outcomes.
section

attribute [local irreducible] ComputableInPolyTime

example (f g : List Bool → List Bool)
    (hf : ComputableInPolyTime f encBits encBits)
    (hg : ComputableInPolyTime g encBits encBits) :
    ComputableInPolyTime (fun word => g (f word) ++ word) encBits encBits := by
  expect_shared_classifications
  fail_if_success (clear hg; polytime)
  polytime

end

-- A local reducibility change to another imported definition makes each call classify imported
-- rules itself, with the same outcomes.
section

attribute [local irreducible] encBits

example (f g : List Bool → List Bool)
    (hf : ComputableInPolyTime f encBits encBits)
    (hg : ComputableInPolyTime g encBits encBits) :
    ComputableInPolyTime (fun word => g (f word) ++ word) encBits encBits := by
  expect_invocation_classifications
  fail_if_success (clear hg; polytime)
  polytime

end

/-- Check that a failed `ppt` call names the subterm it could not certify. -/
private meta def checkPPTFailure (type : Expr) (required : String) : TacticM Unit := do
  let saved ← saveState
  try
    let goal ← mkFreshExprSyntheticOpaqueMVar type
    setGoals [goal.mvarId!]
    let result ← observing <| Term.withoutErrToSorry <| withoutRecover <|
      evalTactic (← `(tactic| ppt))
    let .error ex := result | throwError "expected ppt to fail"
    let message ← ex.toMessageData.toString
    unless message.contains "ppt could not certify a subterm" && message.contains required do
      throwError "expected a failure hint naming {required}\n{message}"
  finally
    saved.restore

elab (name := checkPPTFailureHint) "check_ppt_failure " target:term " naming " name:str :
    tactic => do
  checkPPTFailure (← Term.elabType target) name.getString

local allow_unused_tactic checkPPTFailureHint

example (missingSampler : List Bool → Cslib.ProbComp Bool) :
    missingSampler = missingSampler := by
  check_ppt_failure (Cslib.Probability.IsPPTOn encBits encBool missingSampler)
    naming "missingSampler"
  rfl

end CslibFrontierTests.PolyTimeRuleClassCache
