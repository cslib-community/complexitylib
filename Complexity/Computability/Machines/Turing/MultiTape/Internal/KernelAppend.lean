/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Basic.Finite.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelFacts

/-! # The existing concatenation machine and its run theorem

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol S₁ S₂ : Type*}

/-- Run `tm₁` and then `tm₂`, both with their work tapes padded to `max k₁ k₂`. -/
public noncomputable def appendTM (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (tm₂ : MultiTapeTM k₂ Symbol S₂) : MultiTapeTM (max k₁ k₂) Symbol (S₁ ⊕ S₂) :=
  (tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).seq
    (tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))

/-- If `tm₁` computes `y₁` from `x` tidily and `tm₂` computes `y₂` from `x` tidily, then
`appendTM tm₁ tm₂` computes `y₁ ++ y₂` from `x` tidily. -/
public theorem ComputesTidilyInTimeAndSpace.append {tm₁ : MultiTapeTM k₁ Symbol S₁}
    {tm₂ : MultiTapeTM k₂ Symbol S₂} {x y₁ y₂ : List Symbol} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x y₁ t₁ s₁)
    (h₂ : tm₂.ComputesTidilyInTimeAndSpace x y₂ t₂ s₂) :
    (appendTM tm₁ tm₂).ComputesTidilyInTimeAndSpace x (y₁ ++ y₂) (t₁ + t₂)
      (s₁ + s₂ + 2 * max k₁ k₂) :=
  (transformsTapes_seq (h₁.extendTapes _) (h₂.extendTapes _)
    fun _ _ _ _ hP hQ => ⟨hP.1, hQ.1⟩).imp (fun _ _ h => h)
    (by rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩; exact ⟨hws, rfl⟩) le_rfl
    (by omega)

end Turing.MultiTapeTM
