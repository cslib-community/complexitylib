/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.Additive.SumsetCover
import Complexity.Foundations.Combinatorics.SmallSubsets
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

open Cslib Cslib.BitString Finset Module
open scoped Pointwise

-- The monomial basis works over fields of both characteristic zero and characteristic two.
example : finrank ℚ (lowDegree ℚ (Fin 3) 1) = 4 := by
  rw [finrank_lowDegree, card_filter_card_le_eq_sum_choose]
  decide

example : finrank (ZMod 2) (lowDegree (ZMod 2) (Fin 3) 2) = 7 := by
  rw [finrank_lowDegree, card_filter_card_le_eq_sum_choose]
  decide

-- Saturation above the cube's dimension, and the empty-coordinate edge case.
example : finrank ℚ (lowDegree ℚ (Fin 2) 4) = 4 := by
  rw [finrank_lowDegree, card_filter_card_le_eq_sum_choose]
  decide

example : finrank ℚ (lowDegree ℚ (Fin 0) 0) = 1 := by
  rw [finrank_lowDegree, card_filter_card_le_eq_sum_choose]
  decide

-- A genuinely smaller-than-the-cube cover bound, with arbitrary summands and no degree premise.
example (A B : Finset (BitString 9)) :
    ∃ A₀ B₀, A₀ ⊆ A ∧ B₀ ⊆ B ∧ A + B = (A₀ + B) ∪ (A + B₀) ∧
      A₀.card + B₀.card ≤ 390 := by
  obtain ⟨A₀, B₀, hA, hB, hcover, hcard⟩ := exists_add_cover A B
  refine ⟨A₀, B₀, hA, hB, hcover, ?_⟩
  simp only [card_filter_card_le_eq_sum_choose, Fintype.card_fin] at hcard
  norm_num [sum_range_succ, Nat.choose] at hcard
  exact hcard

-- Asymmetric degree choices are usable directly, before optimizing the common cutoff.
example (A B : Finset (BitString 3)) :
    ∃ A₀ B₀, A₀ ⊆ A ∧ B₀ ⊆ B ∧ A + B = (A₀ + B) ∪ (A + B₀) ∧
      A₀.card + B₀.card ≤ 6 := by
  obtain ⟨A₀, B₀, hA, hB, hcover, hcard⟩ := exists_add_cover_of_degree A B 0 1
  refine ⟨A₀, B₀, hA, hB, hcover, ?_⟩
  simp only [card_filter_card_le_eq_sum_choose, Fintype.card_fin] at hcard
  norm_num [sum_range_succ, Nat.choose] at hcard
  exact hcard
