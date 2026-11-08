/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.SaksZhou

/-! The Saks–Zhou rounding and iteration: concrete values, Lemma A.3, the `pow` hypothesis holding
and failing, and the necessity of `n₁ ≥ 2` in the form `n w 2 ^ (1 - d)` of Lemma A.4. -/

namespace ComplexityTests.SaksZhou

open Cslib.Probability.SaksZhou

/-! ### Snap -/

-- At precision `d = 1`, shift `0` keeps `1/2`, while shift `1` rounds it down to `0`.
example : snap 1 (1 / 2) 0 = 1 / 2 := by
  rw [snap_def]
  norm_num

example : snap 1 (1 / 2) 1 = 0 := by
  rw [snap_def]
  norm_num

-- Both shifts round `3/4` to `1/2`, so `1/2` and `3/4` are snapped differently exactly at shift
-- `1`: one shift out of two, within Lemma A.3's bound `2 ^ d ε + 2 ^ (-d) = 1` for `ε = 1/4`.
example : snap 1 (3 / 4) 0 = 1 / 2 := by
  rw [snap_def]
  norm_num

example : snap 1 (3 / 4) 1 = 1 / 2 := by
  rw [snap_def]
  norm_num

example : (({y : Fin (2 ^ 1) | snap 1 (1 / 2) y ≠ snap 1 (3 / 4) y} : Finset _).dens : ℝ) ≤
    2 ^ 1 * (1 / 4) + (2 ^ 1)⁻¹ :=
  dens_snap_ne_le 1 (by rw [abs_le]; constructor <;> norm_num)

/-! ### Dyadic substochastic matrices -/

example : IsDyadicSubstochastic 1 (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℝ) where
  nonneg i j := by
    fin_cases i
    fin_cases j
    norm_num
  sum_le_one i := by
    fin_cases i
    norm_num
  dyadic i j := by
    fin_cases i
    fin_cases j
    exact ⟨1, by norm_num⟩

-- `1/3` is not a multiple of `1/2`.
example : ¬ IsDyadicSubstochastic 1 (!![1 / 3] : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro h
  obtain ⟨k, hk⟩ := h.dyadic 0 0
  have hk' : (2 : ℝ) = 3 * k := by
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one] at hk
    field_simp at hk
    linarith
  have : (2 : ℕ) = 3 * k := by exact_mod_cast hk'
  omega

/-! ### The hypothesis on `pow` -/

-- The exact power satisfies the hypothesis with `ε = 0`: the set of bad seeds is empty.
example (d n₁ : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (_ : A = M ∨ IsDyadicSubstochastic d A) :
    (({y : Unit | ∃ i j, (0 : ℝ) < |(fun A (_ : Unit) => A ^ n₁) A y i j - (A ^ n₁) i j|} :
      Finset Unit).dens : ℝ) ≤ 0 := by
  simp

-- A `pow` that always returns `0` violates the hypothesis at `A = 1`, `n₁ = 1` and `ε = 1/2`.
example :
    ¬ (({_y : Unit | ∃ i j, (1 / 2 : ℝ) <
        |(0 : Matrix (Fin 1) (Fin 1) ℝ) i j - ((1 : Matrix (Fin 1) (Fin 1) ℝ) ^ 1) i j|} :
      Finset Unit).dens : ℝ) ≤ 1 / 2 := by
  norm_num [Finset.filter_true_of_mem]

-- With the exact power (`ε = 0`), Lemma A.4 bounds the density of the far set by
-- `n₂ w ^ 2 2 ^ (-d)`; here `w = 2`, `n₁ = 2`, `n₂ = 3` and `d = 10` give `12 / 1024`.
-- Restating the far set at `ι = Fin 2` elaborates its `∃ i` with `Nat.decidableExistsFin`
-- instead of `Fintype.decidableExistsFintype`, so the set is matched by `congr!` rather than by
-- unification.
example (M : Matrix (Fin 2) (Fin 2) ℝ) (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i, ∑ j, M i j ≤ 1) :
    (({p : Unit × (Fin 3 → Fin (2 ^ 10)) | ∃ i,
        ((2 : ℕ) : ℝ) ^ 3 * (Fintype.card (Fin 2) * (2 / 2 ^ 10)) <
          ∑ j, |snapIter 10 (fun A => A ^ 2) M 3 p.2 i j - (M ^ 2 ^ 3) i j|} :
          Finset _).dens : ℝ) ≤ 3 / 256 := by
  convert dens_snapIter_far_le_of_two_le 10 3 le_rfl (fun A (_ : Unit) => A ^ 2) h0 h1 le_rfl
    (fun A _ => by simp) using 1
  · congr!
  · norm_num

/-! ### `n₁ = 1` -/

-- With `n₁ = 1`, every round can lose `2 ^ (-d)`: from `M = 1` at `d = 2` with shifts `3`, the
-- iterates are `3/4`, `1/2`, `1/4`.
example : snapIter 2 (· ^ 1) (1 : Matrix (Fin 1) (Fin 1) ℝ) 3 (fun _ => 3) 0 0 = 1 / 4 := by
  norm_num [snapIter_succ, snapMatrix_apply, snap_def, Fin.init]

-- So the error `3/4` exceeds `n w 2 ^ (1 - d) = 1/2` for `n = 1 ^ 3`, while the exact bound
-- `(∑_{k < 3} 1 ^ k) w 2 ^ (1 - d) = 3/2` of `sum_abs_snapIter_sub_pow_le` holds.
example : (1 : ℝ) ^ 3 * (Fintype.card (Fin 1) * (2 / 2 ^ 2)) <
    ∑ j, |snapIter 2 (· ^ 1) (1 : Matrix (Fin 1) (Fin 1) ℝ) 3 (fun _ => 3) 0 j -
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) ^ 1 ^ 3) 0 j| := by
  norm_num [snapIter_succ, snapMatrix_apply, snap_def, Fin.init, abs_of_nonneg]

end ComplexityTests.SaksZhou
