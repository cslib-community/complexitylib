/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Privacy.DifferentialPrivacy.RandomReconstruction
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Reconstruction from random `±1` queries: instances and edge cases

* `signDot` on concrete sign vectors.
* `AnswersWithin` holds for exact answers and fails for answers that are off by one on the only
  query.
* Theorem 8.2's failure probability is below `1` for `20` queries per row at `η = 1 / 2`, both
  with the corrected constant and in Dwork and Roth's form at `α = 1 / 2`.
* The source's constant fails for small `α`: for every choice of `10` queries on `2` rows, two
  databases at Hamming distance `2` both answer `7 / 10` of the queries exactly, and at
  `α = 1 / 20`, `η = 1 / 5` every attack errs in at least one position, more than
  `(2 α / η) ^ 2 = 1 / 4`.
* The privacy consequence is not vacuous. There are `1500` queries on `60` rows that no
  `(1, 0)`-private mechanism answers exactly on `3 / 4` of them with probability one.
-/

namespace ComplexityTests.Privacy.RandomReconstruction

open Cslib Cslib.Privacy
open scoped ENNReal

/-! ### Answers -/

/-- Both rows of the database are `true` (sign `-1`); the query reads row `0` as `true` (sign
`-1`) and row `1` as `false` (sign `1`). The answer is `(-1)(-1) + (1)(-1) = 0`. -/
example : signDot (![true, false] : Fin 2 → Bool) ![true, true] = 0 := by
  rw [signDot_apply, Fin.sum_univ_two]
  norm_num

/-- A query equal to the database answers `n`. -/
example : signDot (![true, false, true] : Fin 3 → Bool) ![true, false, true] = 3 := by
  rw [signDot_apply, Fin.sum_univ_three]
  norm_num

/-- Exact answers fit at every `η ≤ 1 / 2`, even with `α = 0`. -/
example (A : Fin 4 → Fin 3 → Bool) (d : Fin 3 → Bool) :
    AnswersWithin A (fun j => signDot (A j) d) d 0 (1 / 2) :=
  answersWithin_signDot A d le_rfl le_rfl

/-- An answer off by one on the only query does not fit at `α = 1 / 2`. -/
example : ¬ AnswersWithin (fun _ : Fin 1 => (![false] : Fin 1 → Bool)) (fun _ => 2) ![false]
    (1 / 2) 0 := by
  rw [answersWithin_iff]
  have h : signDot (![false] : Fin 1 → Bool) ![false] = 1 := by
    rw [signDot_apply, Fin.sum_univ_one]
    norm_num
  simp only [h]
  norm_num

/-! ### The failure probability -/

/-- `η b / 4 = 5 / 2 > ln 3` for `b = 20` and `η = 1 / 2`, so the bound is below `1`. -/
private theorem exp_lt_one_of_card_pos (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (Real.exp (-((Fintype.card (Fin n) : ℝ) * (1 / 2 * 20 / 4 - Real.log 3)))) <
      1 := by
  rw [ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
  have hlog : Real.log 3 < 5 / 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hn' : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast hn
  nlinarith

/-- With `20` queries per row and `η = 1 / 2`, the attack fails with probability below `1` for
every `α`. At `α = 0` the error bound is `((0 + 1) / (1 / 2)) ^ 2 = 4`. -/
example (n : ℕ) (hn : 0 < n) (α : ℝ) :
    (Probability.PMF.uniformOfFintype (Fin (20 * n) → Fin n → Bool)).toOuterMeasure
        {A | ∃ (d : Fin n → Bool) (y : Fin (20 * n) → ℝ), AnswersWithin A y d α (1 / 2) ∧
          ((⌊α⌋₊ + 1 : ℝ) / (1 / 2)) ^ 2 ≤ hammingDist (reconstructSigned A α (1 / 2) y) d} <
      1 :=
  (toOuterMeasure_exists_le_hammingDist_reconstructSigned_le (b := 20) (by norm_num)
    (by simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, le_refl])).trans_lt
    (exp_lt_one_of_card_pos n hn)

/-- Dwork and Roth's form at `α = 1 / 2`, `η = 1 / 2`: except with probability below `1`, the
adversary errs in at most `(2 α / η) ^ 2 = 4` positions. -/
example (n : ℕ) (hn : 0 < n) :
    (Probability.PMF.uniformOfFintype (Fin (20 * n) → Fin n → Bool)).toOuterMeasure
        {A | ∃ (d : Fin n → Bool) (y : Fin (20 * n) → ℝ), AnswersWithin A y d (1 / 2) (1 / 2) ∧
          ((2 : ℝ) * (1 / 2) / (1 / 2)) ^ 2 <
            hammingDist (reconstructSigned A (1 / 2) (1 / 2) y) d} <
      1 :=
  (toOuterMeasure_exists_lt_hammingDist_reconstructSigned_le_of_half_le (ι := Fin n)
    (κ := Fin (20 * n)) (α := 1 / 2) (η := 1 / 2) (b := 20) le_rfl (by norm_num)
    (by simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, le_refl])).trans_lt
    (exp_lt_one_of_card_pos n hn)

/-! ### The constant for small `α` -/

/-- Whatever the `10` queries on `2` rows, two databases at Hamming distance `2` both answer
`7 / 10` of them exactly. Dwork and Roth's `(2 α / η) ^ 2` would be `0` here. -/
example (A : Fin 10 → Fin 2 → Bool) :
    ∃ (y : Fin 10 → ℝ) (c d : Fin 2 → Bool), AnswersWithin A y c 0 (1 / 5) ∧
      AnswersWithin A y d 0 (1 / 5) ∧ (2 * 0 / (1 / 5) : ℝ) ^ 2 < hammingDist c d := by
  obtain ⟨y, c, d, hc, hd, h2⟩ := exists_answersWithin_answersWithin_hammingDist_eq_two
    (show (0 : Fin 2) ≠ 1 by decide) A (by simp)
  exact ⟨y, c, d, hc, hd, by rw [h2]; norm_num⟩

/-- At `α = 1 / 20`, `η = 1 / 5`, every attack on these `10` queries errs in at least one
position on some database with fitting answers, more than Dwork and Roth's
`(2 α / η) ^ 2 = 1 / 4`. -/
example (A : Fin 10 → Fin 2 → Bool) (attack : (Fin 10 → ℝ) → Fin 2 → Bool) :
    ∃ (d : Fin 2 → Bool) (y : Fin 10 → ℝ), AnswersWithin A y d (1 / 20) (1 / 5) ∧
      (1 / 4 : ℝ) < hammingDist (attack y) d := by
  obtain ⟨d, y, hd, h⟩ := exists_answersWithin_lt_hammingDist
    (show (0 : Fin 2) ≠ 1 by decide) A (by simp) (α := 1 / 20) (η := 1 / 5) (by norm_num)
    (by norm_num) le_rfl (by norm_num) attack
  exact ⟨d, y, hd, by norm_num at h ⊢; linarith⟩

/-- The corrected constant `((⌊α⌋₊ + 1) / η) ^ 2 = 25` at `α = 0`, `η = 1 / 5` exceeds the
distance `2` of the first example. -/
example : ((⌊(0 : ℝ)⌋₊ + 1 : ℝ) / (1 / 5)) ^ 2 = 25 := by
  norm_num

/-! ### Differential privacy -/

/-- No `(1, 0)`-private mechanism answers `3 / 4` of these `1500` queries on `60` rows exactly
with probability one on every database: that would force `60 ≤ 16 (1 + e)`. -/
example : ∃ A : Fin 1500 → Fin 60 → Bool, ∀ (M : (Fin 60 → Bool) → PMF (Fin 1500 → ℝ)),
    DifferentiallyPrivate HammingAdjacent M 1 0 →
      ¬ ∀ d, (M d).toOuterMeasure {y | AnswersWithin A y d 0 (1 / 4)} = 1 := by
  have hlog : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  obtain ⟨A, hA⟩ := DifferentiallyPrivate.exists_forall_card_mul_one_sub_le_of_answersWithin
    (ι := Fin 60) (κ := Fin 1500) (α := 0) (η := 1 / 4) (by norm_num)
    (by simp only [Fintype.card_fin]; nlinarith)
  refine ⟨A, fun M hM hall => ?_⟩
  have h := hA M 1 0 id hM ENNReal.zero_ne_top hall
  simp only [Fintype.card_fin, ENNReal.toReal_zero] at h
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  norm_num at h
  linarith

end ComplexityTests.Privacy.RandomReconstruction
