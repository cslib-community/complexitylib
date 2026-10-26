/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.MagnificationAbstract
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Concrete clients and non-vacuity checks for the McKay–Murray–Williams formal abstract

Verifies that the public complexity classes `P`, `NP`, and `PPoly` in `MagnificationAbstract`
match the library's native definitions, tests `tableIndex`, `tableFunction`, `HasCircuitOfSize`,
and `DecidesMCSPSlice` on concrete small circuits and truth tables, and derives the infinitely-often
(`∃ᶠ n in Filter.atTop`) hardness magnification corollaries from the public theorems.
-/

namespace ComplexityTests.Abstracts.MagnificationTests

open ComplexityAbstracts.MagnificationAbstract
open Filter

-- The public classes match the library's native classes over `encBits`.
example : P = Cslib.Complexity.P Turing.MultiTapeTM.encBits := rfl

example : NP = Cslib.Complexity.NP Turing.MultiTapeTM.encBits :=
  ComplexityAbstracts.MagnificationBridge.np_eq

example : PPoly = Cslib.Circuits.Boolean.PPolyOn Turing.MultiTapeTM.encBits :=
  ComplexityAbstracts.MagnificationBridge.ppoly_eq

-- Concrete checks of `tableIndex` at `n = 1` and `n = 2` (coordinate zero least significant).
example : (tableIndex 1 (fun _ => false)).val = 0 := by decide

example : (tableIndex 1 (fun _ => true)).val = 1 := by decide

example : (tableIndex 2 ![true, false]).val = 1 := by decide

example : (tableIndex 2 ![false, true]).val = 2 := by decide

-- A 0-gate wire circuit computes the projection `fun x : Fin 1 → Bool => x 0`.
theorem hasCircuitOfSize_proj_zero :
    HasCircuitOfSize (fun x : Fin 1 → Bool => x 0) 0 := by
  refine ⟨Cslib.Circuits.Circuit.wiring Cslib.Circuits.Boolean.signature (fun _ => 0),
    fun _ => rfl, le_rfl⟩

-- Consequently, the truth table `![false, true]` of `x ↦ x 0` satisfies `HasCircuitOfSize`
-- at `k = 0`.
example : HasCircuitOfSize (tableFunction (n := 1) ![false, true]) 0 := by
  have h : tableFunction (n := 1) ![false, true] = fun x : Fin 1 → Bool => x 0 := by
    funext x
    have hx : x = (fun _ => false) ∨ x = (fun _ => true) := by
      cases h0 : x 0
      · left; ext i; rw [Subsingleton.elim i 0, h0]
      · right; ext i; rw [Subsingleton.elim i 0, h0]
    rcases hx with rfl | rfl <;> rfl
  rw [h]
  exact hasCircuitOfSize_proj_zero

-- Infinitely-often (`∃ᶠ n in atTop`) lower bounds immediately satisfy the public `∃ n` hypothesis.
example (k : ℕ)
    (h : ∀ c > 0, ∃ᶠ n in atTop, ∀ C : DeMorganCircuit (2 ^ n),
      DecidesMCSPSlice C (fun m => m ^ k) → 2 ^ n * c * (n + 1) ^ c < C.size) :
    ¬ (NP ⊆ PPoly) :=
  np_not_subset_ppoly_of_mcsp_hard k fun c hc => (h c hc).exists

example (k : ℕ)
    (h : ∀ c > 0, ∃ᶠ n in atTop, ∀ C : DeMorganCircuit (2 ^ n),
      DecidesMCSPSlice C (fun m => m ^ k) → 2 ^ n * c * (n + 1) ^ c < C.size) :
    P ≠ NP :=
  p_ne_np_of_mcsp_hard k fun c hc => (h c hc).exists

end ComplexityTests.Abstracts.MagnificationTests
