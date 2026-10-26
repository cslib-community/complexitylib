/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Tactic.PPT

/-! # Ordered plain conditional search under a normal tactic import

No theorem here is a named or compositional certificate. Generic inputs and outputs prevent a
finite-domain lookup from replacing the conditional proof. Existing direct `fun_prop` fixtures
remain in AutomationBooleanMinimal and AutomationBooleanPPT.
-/

open Turing.MultiTapeTM
namespace ConditionalDispatchTests

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
/-- The driver selects the direct Boolean recipe with arbitrary guard encoding. -/
public theorem booleanDriver {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {guardEncoding : Bool ↪ List Bool}
    {guard : α → Bool} {yes no : α → β}
    (hc : ComputableInPolyTime guard input guardEncoding)
    (hy : ComputableInPolyTime yes input output) (hn : ComputableInPolyTime no input output) :
    ComputableInPolyTime (fun a => if guard a then yes a else no a) input output := by
  polytime

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
/-- The driver selects the direct proposition decision recipe. -/
public theorem propositionDriver {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {guard : α → Prop} [∀ a, Decidable (guard a)]
    {yes no : α → β}
    (hc : ComputableInPolyTime (fun a => decide (guard a)) input encBool)
    (hy : ComputableInPolyTime yes input output) (hn : ComputableInPolyTime no input output) :
    ComputableInPolyTime (fun a => if guard a then yes a else no a) input output := by
  polytime

-- Inspect the proof produced by the actual driver, not a manually selected rule. In particular,
-- the Boolean proof must use the direct recipe rather than the library's `ite'` wrapper.
run_meta do
  for (name, expected) in [(``booleanDriver, ``ComputableInPolyTime.ite),
      (``propositionDriver, ``ComputableInPolyTime.ite_decide)] do
    let info ← Lean.getConstInfo name
    let some value := info.value? (allowOpaque := true) | throwError "missing driver proof"
    let head ← Lean.Meta.lambdaTelescope value fun _ body =>
      pure body.consumeMData.getAppFn.constName?
    unless head == some expected do
      throwError "driver did not select {expected}: got {head}"

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {p q : α → Bool} {P Q : α → Prop} [∀ a, Decidable (P a)] [∀ a, Decidable (Q a)]
    {yes no : α → β} (hp : ComputableInPolyTime p input encBool)
    (hq : ComputableInPolyTime q input encBool)
    (hP : ComputableInPolyTime (fun a => decide (P a)) input encBool)
    (hQ : ComputableInPolyTime (fun a => decide (Q a)) input encBool)
    (hy : ComputableInPolyTime yes input output) (hn : ComputableInPolyTime no input output) :
    ComputableInPolyTime (fun a => if p a then
      (if P a then (if q a then (if Q a then yes a else no a) else no a) else no a)
      else no a) input output := by
  polytime

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {_guard : α → Bool} {yes no : α → β}
    (_hy : ComputableInPolyTime yes input output) (_hn : ComputableInPolyTime no input output) :
    True := by
  fail_if_success
    have : ComputableInPolyTime (fun a => if _guard a then yes a else no a) input output := by
      polytime
  trivial

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {p q : α → Bool} {P Q : α → Prop} [∀ a, Decidable (P a)] [∀ a, Decidable (Q a)]
    {_yes no : α → β} (_hp : ComputableInPolyTime p input encBool)
    (_hq : ComputableInPolyTime q input encBool)
    (_hP : ComputableInPolyTime (fun a => decide (P a)) input encBool)
    (_hQ : ComputableInPolyTime (fun a => decide (Q a)) input encBool)
    (_hn : ComputableInPolyTime no input output) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun a => if p a then
        (if P a then (if q a then (if Q a then _yes a else no a) else no a) else no a)
        else no a) input output := by
      polytime
  trivial

private abbrev conditionalAlias {α β : Type} (guard : α → Bool) (yes no : α → β) :=
  fun a => if guard a then yes a else no a

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {guard : α → Bool} {yes no : α → β} (hc : ComputableInPolyTime guard input encBool)
    (hy : ComputableInPolyTime yes input output) (hn : ComputableInPolyTime no input output) :
    ComputableInPolyTime (conditionalAlias guard yes no) input output := by
  polytime

-- Two supplied complete families compete. The wrong input encoding must not bind the valid
-- alternative's metavariables, and the whole-program family needs no separate branch premises.
set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
example {α β : Type} {input otherInput : α ↪ List Bool} {output : β ↪ List Bool}
    {guard : ℕ → α → Bool} {yes no : ℕ → α → β}
    (_wrong : ∀ n, ComputableInPolyTime (conditionalAlias (guard n) (yes n) (no n))
      otherInput output)
    (known : ∀ n, ComputableInPolyTime (conditionalAlias (guard n) (yes n) (no n)) input output)
    (n : ℕ) : ComputableInPolyTime (conditionalAlias (guard n) (yes n) (no n)) input output := by
  polytime

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
example {α β : Type} {input otherInput : α ↪ List Bool} {output : β ↪ List Bool}
    {guard : ℕ → α → Bool} {yes no : ℕ → α → β}
    (known : ∀ n, ComputableInPolyTime (conditionalAlias (guard n) (yes n) (no n)) input output)
    (_wrong : ∀ n, ComputableInPolyTime (conditionalAlias (guard n) (yes n) (no n))
      otherInput output)
    (n : ℕ) : ComputableInPolyTime (conditionalAlias (guard n) (yes n) (no n)) input output := by
  polytime

-- Both direct recipes demand the opaque branch, but generic reduction can discard it. No
-- local routine certificate competes with decomposition here.
set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
example (unknown : List Bool → List Bool) : ComputableInPolyTime
    (fun a => if (false : Bool) then unknown a else a) encBits encBits := by
  polytime

-- This Boolean-shaped guard is supplied through its decision view. Retaining the proposition
-- recipe allows proof search to recover if the direct Boolean guard obligation cannot close.
set_option maxHeartbeats 200000 in
-- Keep the original default budget for this driver control.
example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {guard : α → Bool} {yes no : α → β}
    (hc : ComputableInPolyTime (fun a => decide (guard a = true)) input encBool)
    (hy : ComputableInPolyTime yes input output) (hn : ComputableInPolyTime no input output) :
    ComputableInPolyTime (fun a => if guard a then yes a else no a) input output := by
  polytime

-- These source-only controls enter the supplied-guard fast attempt, then require a branch
-- certificate. A globally registered raw certificate must not supply that missing branch.
@[irreducible] private def rawBranch (word : List Bool) : List Bool := word.reverse

private theorem rawBranch_certificate :
    ComputableTidilyInPolyTime rawBranch encBits encBits := by
  unfold rawBranch
  exact ComputableInPolyTime.bitsReverse.tidy

attribute [local fun_prop] rawBranch_certificate

private abbrev RawBranchAlias {α β : Type} (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) :=
  ComputableTidilyInPolyTime f input output

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this conditional privacy control.
example (guard : List Bool → Bool)
    (hc : ComputableInPolyTime guard encBits encBool)
    (_hn : ComputableInPolyTime (fun word : List Bool => word) encBits encBits) :
    ComputableInPolyTime
      (fun word => if guard word then rawBranch word else word) encBits encBits := by
  fail_if_success polytime
  -- The failed scoped command restores the ordinary raw-to-plain FunProp route.
  fun_prop

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this conditional privacy control.
example (guard : List Bool → Bool) (yes no : List Bool → List Bool)
    (hy : ComputableInPolyTime yes encBits encBits)
    (hn : ComputableInPolyTime no encBits encBits)
    (h : RawBranchAlias rawBranch encBits encBits →
      ComputableInPolyTime guard encBits encBool) :
    ComputableInPolyTime
      (fun word => if guard word then yes word else no word) encBits encBits := by
  fail_if_success polytime
  -- The implication cannot supply a complete guard; ordinary search is restored afterward.
  fun_prop

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this conditional supplied-evidence control.
example (guard : List Bool → Bool) (yes no : List Bool → List Bool)
    (hy : ComputableInPolyTime yes encBits encBits)
    (hn : ComputableInPolyTime no encBits encBits)
    (h : RawBranchAlias rawBranch encBits encBits →
      ComputableInPolyTime guard encBits encBool)
    (hf : RawBranchAlias rawBranch encBits encBits) :
    ComputableInPolyTime
      (fun word => if guard word then yes word else no word) encBits encBits := by
  polytime

-- Register only after the other controls: this deliberately indexes the conditional head
-- itself. Every direct guard/branch certificate is available, so the fast attempt could close
-- the goal if it incorrectly ran ahead of the indexed certificate.
private theorem indexedConditional {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {guard : ℕ → α → Bool} {yes no : α → β} (n : ℕ)
    (_hbound : n ≤ n) (hc : ComputableInPolyTime (guard n) input encBool)
    (hy : ComputableInPolyTime yes input output) (hn : ComputableInPolyTime no input output) :
    ComputableInPolyTime (fun a => if guard n a then yes a else no a) input output := by
  clear _hbound
  exact ComputableInPolyTime.ite hc hy hn

-- Eager premises make the indexed application close at its parent, so a later generic
-- unsafe application cannot hide an inert index while its children await expansion.
attribute [local program_certificate _hbound hc hy hn] indexedConditional

set_option maxHeartbeats 200000 in
-- Keep the original default budget for this indexed conditional precedence control.
private theorem indexedConditionalDriver {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {guard : ℕ → α → Bool} {yes no : α → β} (n : ℕ)
    (hc : ComputableInPolyTime (guard n) input encBool)
    (hy : ComputableInPolyTime yes input output) (hn : ComputableInPolyTime no input output) :
    ComputableInPolyTime (fun a => if guard n a then yes a else no a) input output := by
  polytime

run_meta do
  let certificate := ``indexedConditional
  let type := (← Lean.getConstInfo certificate).type
  let key ← Lean.Meta.forallTelescope type fun _ conclusion =>
    Cslib.Tactic.efficiencyKey conclusion
  let entries := (Cslib.Tactic.certificateExt.getState (← Lean.getEnv)).getD key #[]
  unless key.2.1 == ``ite && entries.any (fun entry => entry.1 == certificate) do
    throwError "conditional certificate is not indexed by its actual conditional head"
  let info ← Lean.getConstInfo ``indexedConditionalDriver
  let some value := info.value? (allowOpaque := true) | throwError "missing indexed driver proof"
  let head ← Lean.Meta.lambdaTelescope value fun _ body =>
    pure body.consumeMData.getAppFn.constName?
  unless head == some certificate do
    throwError "conditional driver bypassed its indexed certificate: {head}"

end ConditionalDispatchTests
