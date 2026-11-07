/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.InclusionMatrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod

/-!
# Tests: inclusion matrices

Gottlieb's theorem on the inclusion matrix of singletons against pairs of a three-element set
over `ℚ` and over `ZMod 3`, and the failure of its conclusion in characteristic two, where the
hypothesis on the field does not hold.
-/

namespace ComplexityTests.InclusionMatrix

open Finset

/-- Over `ℚ`, weights of the singletons of a three-element set vanishing on every pair vanish. -/
example (a : Finset (Fin 3) → ℚ)
    (ha : ∀ B ∈ (univ : Finset (Fin 3)).powersetCard 2, ∑ A ∈ B.powersetCard 1, a A = 0) :
    ∀ A ∈ (univ : Finset (Fin 3)).powersetCard 1, a A = 0 :=
  eq_zero_of_sum_powersetCard_eq_zero (by omega) (by simp)
    (fun j hj _ => Nat.cast_ne_zero.2 (by omega)) ha

/-- The field only needs `1, …, s` to be nonzero, not `1, …, #U`: over `ZMod 3`, where `#U = 3`
vanishes, weights of the singletons of a three-element set vanishing on every pair vanish. -/
example (a : Finset (Fin 3) → ZMod 3)
    (ha : ∀ B ∈ (univ : Finset (Fin 3)).powersetCard 2, ∑ A ∈ B.powersetCard 1, a A = 0) :
    ∀ A ∈ (univ : Finset (Fin 3)).powersetCard 1, a A = 0 :=
  eq_zero_of_sum_powersetCard_eq_zero (t := 1) (s := 2) (by omega) (by simp)
    (fun j hj hj2 => by
      obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
      all_goals decide) ha

/-- In characteristic two the constant weight `1` on singletons sums to zero on every pair, so
the hypothesis on the field in Gottlieb's theorem cannot be dropped: here `s = 2` vanishes. -/
example : (∀ B ∈ (univ : Finset (Fin 3)).powersetCard 2,
      ∑ A ∈ B.powersetCard 1, (fun _ => (1 : ZMod 2)) A = 0) ∧
    ¬ ∀ A ∈ (univ : Finset (Fin 3)).powersetCard 1, (fun _ => (1 : ZMod 2)) A = 0 := by
  decide

/-- The hypothesis `t + s ≤ #U` cannot be dropped: on a two-element set, the weights `1, -1` of
the singletons sum to zero on the only pair. -/
example : (∀ B ∈ (univ : Finset (Fin 2)).powersetCard 2,
      ∑ A ∈ B.powersetCard 1, (fun A : Finset (Fin 2) => if 0 ∈ A then (1 : ℚ) else -1) A = 0) ∧
    ¬ ∀ A ∈ (univ : Finset (Fin 2)).powersetCard 1,
      (fun A : Finset (Fin 2) => if 0 ∈ A then (1 : ℚ) else -1) A = 0 := by
  refine ⟨fun B hB => ?_, fun h => ?_⟩
  · rw [mem_powersetCard] at hB
    rw [eq_univ_of_card B (by rw [hB.2, Fintype.card_fin]), powersetCard_one, sum_map]
    simp [Fin.sum_univ_two]
  · have := h {0} (by decide)
    norm_num at this

end ComplexityTests.InclusionMatrix
