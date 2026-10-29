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

-- A fixed long result is charged to the existential constant, linear composition and pair-valued
-- projections preserve independent budgets/universes, and an exact realization plus workspace
-- bound alone cannot discharge the output obligation.
example {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : β → γ} {g : α → β} {T S : α → ℕ}
    (hf : ComputableInO f encB encC (fun b => (encB b).length) (fun b => (encB b).length))
    (hg : ComputableInO g encA encB T S)
    {α₁ : Type 1} {β₁ γ₁ : Type} {encA₁ : α₁ ↪ List Bool}
    {encB₁ : β₁ ↪ List Bool} {encC₁ : γ₁ ↪ List Bool} {f₁ : α₁ → β₁ × γ₁} {T₁ S₁ : α₁ → ℕ}
    (hf₁ : ComputableInO f₁ encA₁ (encPair encB₁ encC₁) T₁ S₁)
    {α₀ β₀ : Type} {encA₀ : α₀ ↪ List Bool} {encB₀ : β₀ ↪ List Bool}
    {f₀ : α₀ → β₀} {t s T₀ S₀ : α₀ → ℕ}
    (h : ComputableInTimeAndSpace f₀ encA₀ encB₀ t s)
    (ht : ∀ a, t a ≤ T₀ a + 1) (hs : ∀ a, s a ≤ S₀ a + 1)
    (hl : ∀ a, (encB₀ (f₀ a)).length ≤ S₀ a + 1) :
    ComputableInO (fun _ : List Bool => List.replicate 20 true) word word
      List.length (fun _ => 0) ∧
    ComputableInO (fun w : List Bool => frame w) word word List.length List.length ∧
    ComputableInO (fun w : List Bool => w ++ w) word word
      (fun w => w.length + w.length) (fun w => w.length + w.length) ∧
    ComputableInO (fun w : List Bool => (w, false)) word (encPair word encBool)
      (fun w => w.length + w.length) (fun w => w.length + 0) ∧
    ComputableInO (f ∘ g) encA encC T S ∧
    ComputableInO (fun a => (f₁ a).1) encA₁ encB₁ T₁ S₁ ∧
    ComputableInO f₀ encA₀ encB₀ T₀ S₀ := by
  have hframe : ComputableInLinearTimeAndSpace frame word word := .of_frame fun _ => rfl
  refine ⟨.constZero _, (ComputableInO.of_linear hframe).comp_linear copy,
    copy.append copy fun _ => rfl, copy.prod (ComputableInO.constZero false),
    hf.comp_linear hg, hf₁.fst', ?_⟩
  fail_if_success exact ComputableInO.of_bounds h 1 (by simpa using ht) (by simpa using hs)
  exact ComputableInO.of_bounds h 1 (by simpa using ht) (by simpa using hs) (by simpa using hl)

end ComplexityTests.Internal.OCombinators
