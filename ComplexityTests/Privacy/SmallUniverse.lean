/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Privacy.DifferentialPrivacy.SmallUniverse

/-!
# De's lower bound over a small universe: instances and edge cases

* The histogram excess ignores the order of the rows: swapping the two rows of a dataset gives
  excess `0` although the Hamming distance is `2`. Two datasets with different histograms have
  positive excess.
* The hypotheses of the Dwork–Roth form are satisfiable: `80` rows over a universe of `33` items,
  `k = 2` and `ε = 1 / 40` (`min (k, d) / ε = 80`).
* A mechanism ignoring its input is `(0, 0)`-private, so the theorem applies to it: for the query
  it provides, some dataset sees noise at least `2 / (1024 ε) = 5 / 64` with probability more than
  `1 / 2`.
-/

namespace ComplexityTests.Privacy.SmallUniverse

open Cslib Cslib.Privacy
open scoped ENNReal

/-! ### The histogram excess -/

/-- Swapping the two rows does not change the histogram, so the excess is `0`. -/
example : countExcess (![0, 1] : Fin 2 → Fin 2) ![1, 0] = 0 := by
  have h : (![1, 0] : Fin 2 → Fin 2) = ![0, 1] ∘ Equiv.swap 0 1 := by
    funext i
    fin_cases i <;> rfl
  rw [h, countExcess_comp_equiv_right, countExcess_self]

/-- The same two datasets are at Hamming distance `2`. -/
example : hammingDist (![0, 1] : Fin 2 → Fin 2) ![1, 0] = 2 := by decide

/-- One row of `![0, 0]` has no match in `![0, 1]`. -/
example : countExcess (![0, 0] : Fin 2 → Fin 2) ![0, 1] = 1 := by
  rw [countExcess_apply, Fin.sum_univ_two, rowCount_apply, rowCount_apply, rowCount_apply,
    rowCount_apply]
  decide

/-! ### The Dwork–Roth form -/

/-- The hypotheses of `exists_symmetric_query_forall_exists_half_lt` hold for `80` rows over a
universe of `33` items, `k = 2` and `ε = 1 / 40`. -/
example : min ((2 : ℕ) : ℝ) (Fintype.card (Fin 33)) / (1 / 40) ≤ Fintype.card (Fin 80) := by
  simp only [Fintype.card_fin]
  norm_num

/-- For the query `F` provided by the theorem, the constant mechanism `fun _ => PMF.pure 0` sees
noise at least `5 / 64` with probability more than `1 / 2` on some dataset. -/
example : ∃ F : (Fin 80 → Fin 33) → Fin 2 → ℝ,
    (∀ (x : Fin 80 → Fin 33) (σ : Equiv.Perm (Fin 80)), F (x ∘ σ) = F x) ∧
    (∀ x y : Fin 80 → Fin 33, HammingAdjacent x y → ∀ j, |F x j - F y j| ≤ 1) ∧
    ∃ x, 2⁻¹ < (PMF.pure (0 : Fin 2 → ℝ)).toOuterMeasure {a | ∃ j, 5 / 64 ≤ |a j - F x j|} := by
  obtain ⟨F, hsymm, hsens, hF⟩ := exists_symmetric_query_forall_exists_half_lt
    (ι := Fin 80) (X := Fin 33) (k := 2) le_rfl (by simp) (ε := 1 / 40) (by norm_num)
    (by norm_num) (by simp only [Fintype.card_fin]; norm_num)
  have hdp : DifferentiallyPrivate HammingAdjacent
      (fun _ : Fin 80 → Fin 33 => PMF.pure (0 : Fin 2 → ℝ)) (1 / 40) 0 :=
    DifferentiallyPrivate.of_apply_le fun _ _ _ r => by
      have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (1 / 40)) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by norm_num))
      calc (PMF.pure (0 : Fin 2 → ℝ)) r = 1 * (PMF.pure (0 : Fin 2 → ℝ)) r := (one_mul _).symm
        _ ≤ _ := by gcongr
  obtain ⟨x, hx⟩ := hF _ hdp
  refine ⟨F, hsymm, hsens, x, hx.trans_le ((PMF.pure _).toOuterMeasure.mono fun a ha => ?_)⟩
  obtain ⟨j, hj⟩ := ha
  refine ⟨j, le_of_eq_of_le ?_ hj⟩
  norm_num

/-- The largest admissible `ε = 1 / 18` needs only `36` rows over `33` items for `k = 2`, and the
noise bound is `2 / (1024 / 18) = 9 / 256`. -/
example : ∃ F : (Fin 36 → Fin 33) → Fin 2 → ℝ,
    (∀ (x : Fin 36 → Fin 33) (σ : Equiv.Perm (Fin 36)), F (x ∘ σ) = F x) ∧
    (∀ x y : Fin 36 → Fin 33, HammingAdjacent x y → ∀ j, |F x j - F y j| ≤ 1) ∧
    ∀ M : (Fin 36 → Fin 33) → PMF (Fin 2 → ℝ), DifferentiallyPrivate HammingAdjacent M (1 / 18) 0 →
      ∃ x, 2⁻¹ < (M x).toOuterMeasure {a | ∃ j, 9 / 256 ≤ |a j - F x j|} := by
  obtain ⟨F, hsymm, hsens, hF⟩ := exists_symmetric_query_forall_exists_half_lt
    (ι := Fin 36) (X := Fin 33) (k := 2) le_rfl (by simp) (ε := 1 / 18) (by norm_num) le_rfl
    (by simp only [Fintype.card_fin]; norm_num)
  refine ⟨F, hsymm, hsens, fun M hM => ?_⟩
  obtain ⟨x, hx⟩ := hF M hM
  refine ⟨x, hx.trans_le ((M x).toOuterMeasure.mono fun a ha => ?_)⟩
  obtain ⟨j, hj⟩ := ha
  refine ⟨j, le_of_eq_of_le ?_ hj⟩
  norm_num

end ComplexityTests.Privacy.SmallUniverse
