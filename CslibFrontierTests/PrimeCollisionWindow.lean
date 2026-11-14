/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Foundations.NumberTheory.PrimeCollisionWindow

/-!
# Ordinary-import clients of closed prime collision windows

The small numerical example checks endpoints, not the conservative asymptotic threshold.
-/

set_option linter.privateModule false

open Nat

example : closedPrimes 3 7 = {3, 5, 7} := by decide
example : closedPrimes 7 14 = {7, 11, 13} := by decide

example : ((closedPrimes 3 7).filter fun p => Nat.ModEq p 0 21).card = 2 := by decide
example : ((closedPrimes 7 14).filter fun p => Nat.ModEq p 0 21).card = 1 := by decide
example : Nat.ModEq 7 0 21 := by decide

example : (((closedPrimes 3 7).filter fun p => Nat.ModEq p 0 21).card : ℝ) /
    (closedPrimes 3 7).card = 2 / 3 := by
  have hbad : ((closedPrimes 3 7).filter fun p => Nat.ModEq p 0 21).card = 2 := by
    decide
  have hcard : (closedPrimes 3 7).card = 3 := by decide
  rw [hbad, hcard]
  norm_num
example : (((closedPrimes 7 14).filter fun p => Nat.ModEq p 21 0).card : ℝ) /
    (closedPrimes 7 14).card = 1 / 3 := by
  have hbad : ((closedPrimes 7 14).filter fun p => Nat.ModEq p 21 0).card = 1 := by
    decide
  have hcard : (closedPrimes 7 14).card = 3 := by decide
  rw [hbad, hcard]
  norm_num

example (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    (Q.filter fun p => Nat.ModEq p 0 1).card = 0 := by
  have := card_filter_modEq_le_log hQ (M := 1) (a := 0) (b := 1) (by omega) (by omega) (by decide)
  simpa using this

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, C ≤ L →
      ∀ Q ∈ [closedPrimes 3 L, closedPrimes L (2 * L)],
        Q.Nonempty ∧ ∀ a b : ℕ, a ≤ 2 → b ≤ 2 → a ≠ b →
          ((Q.filter fun p => Nat.ModEq p a b).card : ℝ) / Q.card ≤ δ := by
  obtain ⟨C, hC, h⟩ := exists_closedPrimes_collision_bound hδ
  refine ⟨C, hC, fun L hL => ?_⟩
  exact h 2 L (by decide) (by simpa using hL)

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M →
      let L := ⌈C * (Nat.log2 M : ℝ) ^ 2⌉₊
      ∀ Q ∈ [closedPrimes 3 L, closedPrimes L (2 * L)],
        Q.Nonempty ∧ ∀ a b : ℕ, a ≤ M → b ≤ M → a ≠ b →
          ((Q.filter fun p => Nat.ModEq p a b).card : ℝ) / Q.card ≤ δ :=
  exists_ceil_closedPrimes_collision_bound hδ
