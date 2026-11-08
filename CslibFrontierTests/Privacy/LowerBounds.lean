/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Privacy.DifferentialPrivacy.Packing
import CslibFrontier.Privacy.DifferentialPrivacy.Reconstruction
import CslibFrontier.Privacy.DifferentialPrivacy.RandomizedResponse

/-!
# Lower bounds for differential privacy: instances and edge cases

* Packing: randomized response on one respondent separates its two inputs with probability
  `3 / 4`, and the packing bound `2 · 3 / 4 ≤ exp (ln 3)` holds with room to spare.
* One-way marginals: exact answers are accurate when there is at least one row, and no answer is
  accurate on a dataset with no rows, so the accuracy hypothesis is not vacuous. A mechanism
  ignoring its input is `(0, 0)`-private, and the theorem shows it is inaccurate on some dataset
  once there are two marginals.
* Reconstruction: exact answers determine the database (`E = 0` gives distance `0`).
* Exact answers to all subset-count queries are not `(ε, δ)`-private for any `δ < 1`.
* The bit-guessing bound is attained: for randomized response (`ε = ln 3`, `δ = 0`), each bit is
  guessed correctly with probability `3 / 4 = (exp ε + δ) / (1 + exp ε)`.
-/

namespace CslibFrontierTests.Privacy.LowerBounds

open Cslib Cslib.Privacy
open scoped ENNReal

/-! ### Packing -/

/-- Randomized response on one respondent reports the true bit with probability `3 / 4`. -/
theorem rr_toOuterMeasure_eq (b : Bool) :
    (ProbComp.eval (randomizedResponse b)).toOuterMeasure {b} = 3 / 4 := by
  rw [PMF.toOuterMeasure_apply_singleton, eval_randomizedResponse_apply, ite_eq_left rfl]

/-- The packing bound for randomized response on one respondent: the two datasets are within
Hamming distance one of `fun _ => false`, and the events `{false}` and `{true}` are disjoint. -/
example :
    (Finset.univ : Finset Bool).card * (3 / 4 : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp ((1 : ℕ) * Real.log 3)) :=
  (differentiallyPrivate_randomizedResponseSurvey 1).card_mul_le_of_hammingDist_le_of_pure
    Finset.univ (fun _ => false) (fun b _ => b) (m := 1)
    (fun _ _ => (hammingDist_le_card_fintype).trans (by simp))
    (B := fun b => {fun _ => b})
    (fun b _ b' _ hbb' => Set.disjoint_singleton.mpr fun h => hbb' (congrFun h 0))
    (fun b _ => by
      rw [eval_randomizedResponseSurvey, PMF.toOuterMeasure_apply_singleton,
        Probability.PMF.pi_apply, Fin.prod_univ_one, eval_randomizedResponse_apply,
        ite_eq_left rfl])

/-! ### One-way marginals -/

/-- Exact answers are accurate for every dataset with at least one row. -/
example {ι κ : Type} [Fintype ι] [Nonempty ι] (x : ι → κ → Bool) :
    oneWayMarginals x ∈ accurateMarginals x := fun j => by
  rw [sub_self, abs_zero]
  have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  linarith

/-- With no rows, no answers are accurate, so the accuracy hypothesis fails. -/
example {κ : Type} [Nonempty κ] (x : Fin 0 → κ → Bool) (a : κ → ℝ) :
    a ∉ accurateMarginals x := fun ha => by
  obtain ⟨j⟩ := ‹Nonempty κ›
  have := ha j
  simp only [Fintype.card_fin, Nat.cast_zero, zero_div] at this
  exact absurd this (not_lt.mpr (abs_nonneg _))

/-- A mechanism ignoring its input is `(0, 0)`-private, so by the one-way marginals bound it
cannot be accurate with probability `3 / 4` on every dataset of one row with two marginals
(`2 ^ 2 · 3 / 4 = 3 > 1 = exp (1 · 0)`). -/
example (p : PMF (Fin 2 → ℝ)) :
    ¬ ∀ x : Fin 1 → Fin 2 → Bool, (3 / 4 : ℝ≥0∞) ≤ p.toOuterMeasure (accurateMarginals x) := by
  intro hp
  have hdp : DifferentiallyPrivate HammingAdjacent (fun _ : Fin 1 → Fin 2 → Bool => p) 0 0 :=
    DifferentiallyPrivate.of_apply_le fun _ _ _ r => by simp
  have := hdp.two_pow_mul_le_of_oneWayMarginals hp
  rw [mul_zero, Real.exp_zero, ENNReal.ofReal_one, Fintype.card_fin] at this
  have h3 : (2 : ℝ≥0∞) ^ 2 * (3 / 4) = 3 := by
    rw [ENNReal.div_eq_inv_mul, ← mul_assoc]
    norm_num
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  rw [h3] at this
  exact absurd this (by norm_num)

/-! ### Reconstruction -/

/-- Exact answers let the adversary recover the database exactly. -/
example {n : ℕ} (d : Fin n → Bool) : reconstruct 0 (fun S => (subsetCount d S : ℝ)) = d := by
  have := hammingDist_reconstruct_le (subsetCountsWithin_subsetCount d)
  rw [mul_zero, Nat.cast_nonpos, hammingDist_eq_zero] at this
  exact this

/-- Exact answers to all subset-count queries are not `(ε, δ)`-private for any `δ < 1`, once
there is a row. -/
example {n : ℕ} (hn : n ≠ 0) (ε : ℝ) {δ : ℝ≥0∞} (hδ : δ < 1) :
    ¬ DifferentiallyPrivate HammingAdjacent
      (fun d : Fin n → Bool => PMF.pure fun S => (subsetCount d S : ℝ)) ε δ := by
  intro h
  have := h.card_mul_one_sub_le_of_subsetCountsWithin hδ.ne_top id (E := 0) fun d => by
    rw [PMF.toOuterMeasure_apply_eq_one_iff, PMF.support_pure, Set.singleton_subset_iff]
    exact subsetCountsWithin_subsetCount d
  have hδ' : δ.toReal < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hδ
  rw [Fintype.card_fin, mul_zero, zero_mul] at this
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  nlinarith

/-! ### The bit-guessing bound is attained -/

/-- For randomized response with one respondent, summing over both databases, the bit is guessed
correctly with total probability `3 / 2`, the bound `2 ^ 1 · (exp (ln 3) + 0) / (1 + exp (ln 3))`
of `DifferentiallyPrivate.mul_sum_toOuterMeasure_apply_eq_le`. -/
example :
    ∑ d : Fin 1 → Bool, (ProbComp.eval (randomizedResponseSurvey d)).toOuterMeasure
      {c | c 0 = d 0} = 3 / 2 := by
  have hev (d : Fin 1 → Bool) :
      (ProbComp.eval (randomizedResponseSurvey d)).toOuterMeasure {c | c 0 = d 0} = 3 / 4 := by
    have hset : {c : Fin 1 → Bool | c 0 = d 0} = {fun _ => d 0} := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun h => funext fun i => by rw [Subsingleton.elim i 0, h], fun h => by rw [h]⟩
    rw [hset, eval_randomizedResponseSurvey, PMF.toOuterMeasure_apply_singleton,
      Probability.PMF.pi_apply, Fin.prod_univ_one, eval_randomizedResponse_apply, ite_eq_left rfl]
  simp only [hev, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, pow_one, Nat.cast_ofNat]
  have h4 : (4 : ℝ≥0∞)⁻¹ = 2⁻¹ * 2⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    norm_num
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, h4, ← mul_assoc, ← mul_assoc,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

end CslibFrontierTests.Privacy.LowerBounds
