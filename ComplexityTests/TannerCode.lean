/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.Expander.TannerCode

/-! Tests for Tanner codes on small-bias Cayley graphs. -/

namespace ComplexityTests.TannerCode

open Finset Cslib Cslib.BitString Cslib.BitString.Tanner Cslib.RotationMap Cslib.Probability.PMF
open scoped BigOperators

/-! ### Local codes -/

/-- A nonzero string of length two lies in the kernel of half of the one-row matrices. -/
example : #{A : Fin 1 → Fin 2 → Bool | ∀ i, A i ⬝ᵥ ![true, false] = false} = 2 := by
  rw [card_kernel (by decide)]
  rfl

/-- The union-bound hypothesis is satisfiable: three nonzero strings of length three have weight at
most one, fewer than `2 ^ 2`, so a `2 × 3` matrix detects every single error. -/
example : ∃ A : Fin 2 → Fin 3 → Bool, ∀ w, w ≠ 0 → weight w ≤ 1 → ∃ i, A i ⬝ᵥ w = true :=
  exists_forall_weight_le (by decide)

/-- Such a matrix, explicitly: the checks `x₀ + x₁` and `x₁ + x₂`. -/
example : ∀ w : Fin 3 → Bool, w ≠ 0 → weight w ≤ 1 →
    ∃ i, (![![true, true, false], ![false, true, true]] : Fin 2 → Fin 3 → Bool) i ⬝ᵥ w = true := by
  decide

/-! ### A complete instance of the distance bound -/

/-- The two strings of one bit are unbiased. -/
theorem isSmallBias_zero_pair :
    IsSmallBias 0 ((uniformOfFintype (Fin 2)).map ![![false], ![true]]) := by
  intro S hS
  have hS' : S = {0} := by
    obtain ⟨i, hi⟩ := hS
    ext j
    fin_cases i
    fin_cases j
    simpa using hi
  subst hS'
  rw [bias_uniformOfFintype_map, Fintype.expect_eq_sum_div_card]
  simp [chi, Fin.sum_univ_two]

/-- The single parity check `x₀ + x₁` has distance two: its nonzero kernel words have weight more
than one. -/
theorem parityCheck_distance : ∀ w : Fin 2 → Bool, w ≠ 0 →
    (∀ i, (![![true, true]] : Fin 1 → Fin 2 → Bool) i ⬝ᵥ w = false) → 1 < weight w := by
  decide

/-- On the one-bit cube with generators `0` and `1`, the Tanner code of `x₀ + x₁` has distance at
least `2 · 2 · 2 / 2 = 4`: its only nonzero word uses all four edges. -/
example {x : (Fin 1 → Bool) × Fin 2 → Bool}
    (hx : IsWord ![![false], ![true]] ![![true, true]] x) (hx0 : x ≠ 0) : 4 ≤ weight x := by
  have h := le_weight_of_isWord ![![false], ![true]] le_rfl isSmallBias_zero_pair
    ![![true, true]] parityCheck_distance hx hx0
  have : (8 : ℝ) ≤ 2 * weight x := by norm_num at h; linarith
  exact_mod_cast (by linarith : (4 : ℝ) ≤ weight x)

/-! ### Shortening -/

/-- Every row of a shortened code has at most `d` ones. -/
example (emb : Fin 3 ↪ (Fin 1 → Bool) × Fin 2) (r : Bool × (Fin 1 → Bool) × Fin 1) :
    weight (shortRow ![![false], ![true]] ![![true, true]] emb r) ≤ 2 :=
  weight_shortRow_le _ _ _ _

end ComplexityTests.TannerCode
