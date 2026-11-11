/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Corollary

/-!
# Tests for weight optimality and the explicit `4N - O(N / log N)` lower bound
-/

namespace CslibFrontierTests.AffineDisperser4nCorollary

open Filter Cslib.BitString Cslib.Circuits Cslib.Complexity
open Cslib.Circuits.Boolean.AffineDisperser4n

/-- Weight-constraint optimality check (constraints recorded in `#4322`): `(α, β, c) = (6, 4, 10)`
attains `c - α = 4` tightly across all three inequalities, any solution has `c - α ≤ 4`, and
equality forces `10 ≤ c`. -/
example :
    (6 : ℚ) ≤ 4 + 2 ∧ (10 : ℚ) ≤ 2 * 4 + 2 ∧ (10 : ℚ) ≤ 2 * 6 - 4 + 2 ∧ (10 : ℚ) - 6 = 4 := by
  norm_num

example {α β c : ℚ} (h₁ : α ≤ β + 2) (h₂ : c ≤ 2 * β + 2) (h₃ : c ≤ 2 * α - β + 2)
    (h₄ : c - α = 4) : c - α ≤ 4 ∧ 10 ≤ c := by
  obtain ⟨_, _, hc, _⟩ := weight_lower_bounds_of_sub_eq_four h₁ h₂ h₃ h₄
  exact ⟨weight_sub_le_four h₁ h₃, hc⟩

/-- An explicit language in `P` whose `N`-bit slices eventually require Boolean circuit size at
least `3.6 * N` (strictly exceeding `3.5 * N`). -/
example : ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (L.slice N)) →
      36 * N ≤ 10 * C.size := by
  refine ⟨Cslib.AffineDisperser.explicitDisperserLanguage,
    Cslib.AffineDisperser.explicitDisperserLanguage_mem_P, ?_⟩
  have hev : ∀ᶠ N in atTop, 2 ^ 200 ≤ N := Filter.eventually_ge_atTop _
  filter_upwards [eventually_four_mul_le_size_add_explicitDisperser, hev] with N hlb hN C hC
  rw [Cslib.AffineDisperser.slice_explicitDisperserLanguage] at hC
  have hC' := hlb C hC
  have hN0 : N ≠ 0 := by have : 0 < 2 ^ 200 := Nat.two_pow_pos 200; omega
  have hlog : 200 ≤ Nat.log 2 N := (Nat.le_log_iff_pow_le (by omega) hN0).2 hN
  have hdiv : 60 * N / (Nat.log 2 N + 1) ≤ 60 * N / 201 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h100 : 100 ≤ N := le_trans (by decide) hN
  omega

end CslibFrontierTests.AffineDisperser4nCorollary
