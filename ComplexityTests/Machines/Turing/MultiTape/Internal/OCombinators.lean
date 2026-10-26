/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-! # Direct independent charged budgets and streaming word combinators -/

@[expose] public section

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree] do
    if (← Lean.getEnv).contains name then
      throwError "unexpected higher tidy calculus: {name}"

namespace ComplexityTests.Internal.OCombinators

def word : List Bool ↪ List Bool := Function.Embedding.refl _

theorem copy : ComputableInO (fun w : List Bool => w) word word List.length List.length :=
  .of_eq fun _ => rfl

-- A fixed long result is charged to the existential constant, not assumed to have zero length.
example : ComputableInO (fun _ : List Bool => List.replicate 20 true) word word
    List.length (fun _ => 0) := .constZero _

example : ComputableInO (fun w : List Bool => frame w) word word List.length List.length := by
  have hf : ComputableInLinearTimeAndSpace frame word word := .of_frame fun _ => rfl
  exact (ComputableInO.of_linear hf).comp_linear copy

example : ComputableInO (fun w : List Bool => w ++ w) word word
    (fun w => w.length + w.length) (fun w => w.length + w.length) :=
  copy.append copy fun _ => rfl

example : ComputableInO (fun w : List Bool => (w, false)) word (encPair word encBool)
    (fun w => w.length + w.length) (fun w => w.length + 0) :=
  copy.prod (ComputableInO.constZero false)

-- The conclusion keeps both original functions, without requiring S ≤ T or output ≤ workspace
-- as a new premise: the latter charge already belongs to the inner certificate.
example {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : β → γ} {g : α → β} {T S : α → ℕ}
    (hf : ComputableInO f encB encC (fun b => (encB b).length) (fun b => (encB b).length))
    (hg : ComputableInO g encA encB T S) : ComputableInO (f ∘ g) encA encC T S :=
  hf.comp_linear hg

-- Pair-valued projections retain an input universe unrelated to the two value universes.
example {α : Type 1} {β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {f : α → β × γ} {T S : α → ℕ}
    (hf : ComputableInO f encA (encPair encB encC) T S) :
    ComputableInO (fun a => (f a).1) encA encB T S := hf.fst'

-- An exact realization and workspace bound alone cannot discharge the output obligation.
example {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α → β} {t s T S : α → ℕ}
    (h : ComputableInTimeAndSpace f encA encB t s)
    (ht : ∀ a, t a ≤ T a + 1) (hs : ∀ a, s a ≤ S a + 1)
    (hl : ∀ a, (encB (f a)).length ≤ S a + 1) : ComputableInO f encA encB T S := by
  fail_if_success exact ComputableInO.of_bounds h 1 (by simpa using ht) (by simpa using hs)
  exact ComputableInO.of_bounds h 1 (by simpa using ht) (by simpa using hs) (by simpa using hl)

/-- info: 'Turing.MultiTapeTM.ComputableInO.comp_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInO.comp_linear

/-- info: 'Turing.MultiTapeTM.ComputableInO.prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInO.prod

end ComplexityTests.Internal.OCombinators
