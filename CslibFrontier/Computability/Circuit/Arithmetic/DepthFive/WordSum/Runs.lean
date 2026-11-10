/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# The weight of the runs of a type word

A word `τ : ℕ → Bool` gives every layer a type, `true` for type `𝒟`. Layer `t` has a weight
`c t`, and the weight of a word is the product of the weights of its layers of type `𝒟`. If the
weights of every interval of layers multiply to at most `B ^ 2`, then every run of `𝒟` layers
weighs at most `B ^ 2`, and a word with `w` switches of type has at most `w / 2 + 1` runs, so
that it weighs at most `B ^ (w + 2)` [OpenAI, §5][OpenAI2026DepthFive].

The bound allows for isolated layers: a marked layer of type `𝒩` whose two neighbours have type
`𝒟` may contribute twice its weight. Such a layer joins the two runs around it, and its two
switches pay for the factor two.

## Main definitions

* `runWeight`: the weight of the layers `0, …, j` of a word, with its isolated layers.
* `switchCount`: the number of switches of type among the layers `0, …, j`.

## Main results

* `runWeight_le`: `runWeight τ S c N ≤ B ^ (switchCount τ N + 2)`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §5 (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive

open Finset

variable (τ : ℕ → Bool) (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℝ)

/-- The number of switches of type among the layers `0, …, j`. -/
def switchCount (j : ℕ) : ℕ :=
  ∑ t ∈ range (j + 1), if 1 ≤ t ∧ τ (t - 1) ≠ τ t then 1 else 0

/-- The weight of the layers `0, …, j`: a layer of type `𝒟` contributes its weight, and a layer
in `S` of type `𝒩` between two layers of type `𝒟` contributes twice its weight. -/
noncomputable def runWeight (j : ℕ) : ℝ :=
  (∏ t ∈ range (j + 1), if τ t then c t else 1) *
    ∏ t ∈ range j, if 1 ≤ t ∧ S t ∧ τ (t - 1) ∧ τ t = false ∧ τ (t + 1) then 2 * c t else 1

variable {τ S c}

/-- A word with `w` switches weighs at most `B ^ (w + 2)` when every interval of layers weighs
at most `B ^ 2`. -/
theorem runWeight_le {B : ℝ} {N : ℕ} (hc : ∀ t, 0 ≤ c t) (hB : 1 ≤ B) (h2 : 2 ≤ B ^ 2)
    (hM : ∀ i j, j ≤ N + 1 → ∏ t ∈ Ico i j, c t ≤ B ^ 2) :
    runWeight τ S c N ≤ B ^ (switchCount τ N + 2) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hP (i j : ℕ) : 0 ≤ ∏ t ∈ Ico i j, c t := prod_nonneg fun t _ => hc t
  -- The invariant: an open run of type `𝒟` starts at some layer `i`; after a run has ended,
  -- it may still be joined to the next one by an isolated layer.
  have key (j : ℕ) (hj : j ≤ N) :
      (τ j = true → ∃ i ≤ j, runWeight τ S c j ≤
        B ^ switchCount τ j * ∏ t ∈ Ico i (j + 1), c t) ∧
      (τ j = false → runWeight τ S c j ≤ B ^ (switchCount τ j + 1) ∧
        (1 ≤ j → τ (j - 1) = true → ∃ i ≤ j, runWeight τ S c j * B ≤
          B ^ switchCount τ j * ∏ t ∈ Ico i j, c t)) := by
    induction j with
    | zero =>
      have h0 : switchCount τ 0 = 0 := by
        rw [switchCount, sum_range_one]; simp
      refine ⟨fun h => ⟨0, le_rfl, ?_⟩, fun h => ⟨?_, by simp⟩⟩ <;>
        simp [runWeight, h0, h, hB]
    | succ j ih =>
      obtain ⟨ihT, ihF⟩ := ih (by omega)
      have hw : switchCount τ (j + 1) = switchCount τ j + if τ j ≠ τ (j + 1) then 1 else 0 := by
        rw [switchCount, sum_range_succ]
        simp only [switchCount, Nat.add_sub_cancel, Nat.le_add_left, true_and]
      have hg : runWeight τ S c (j + 1) = runWeight τ S c j *
          (if τ (j + 1) then c (j + 1) else 1) *
          (if 1 ≤ j ∧ S j ∧ τ (j - 1) ∧ τ j = false ∧ τ (j + 1) then 2 * c j else 1) := by
        simp only [runWeight, prod_range_succ _ (j + 1), prod_range_succ _ j]
        ring
      have hpow := pow_pos hB0 (switchCount τ j)
      rcases Bool.eq_false_or_eq_true (τ j) with hj' | hj' <;>
        rcases Bool.eq_false_or_eq_true (τ (j + 1)) with hj1 | hj1
      · -- a run of type `𝒟` continues
        have hw' : switchCount τ (j + 1) = switchCount τ j := by simp [hw, hj', hj1]
        have hg' : runWeight τ S c (j + 1) = runWeight τ S c j * c (j + 1) := by
          simp [hg, hj', hj1]
        refine ⟨fun _ => ?_, by simp [hj1]⟩
        obtain ⟨i, hi, h⟩ := ihT hj'
        refine ⟨i, by omega, ?_⟩
        rw [hw', hg', prod_Ico_succ_top (by omega), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right h (hc _)
      · -- a run of type `𝒟` ends
        have hw' : switchCount τ (j + 1) = switchCount τ j + 1 := by simp [hw, hj', hj1]
        have hg' : runWeight τ S c (j + 1) = runWeight τ S c j := by simp [hg, hj', hj1]
        refine ⟨by simp [hj1], fun _ => ?_⟩
        obtain ⟨i, hi, h⟩ := ihT hj'
        rw [hw', hg']
        refine ⟨?_, fun _ _ => ⟨i, by omega, ?_⟩⟩
        · calc runWeight τ S c j ≤ B ^ switchCount τ j * B ^ 2 :=
                h.trans (mul_le_mul_of_nonneg_left (hM _ _ (by omega)) hpow.le)
            _ = _ := by ring
        · rw [pow_succ, mul_right_comm]
          exact mul_le_mul_of_nonneg_right h hB0.le
      · -- a run of type `𝒟` starts, possibly joined to the previous one by an isolated layer
        have hw' : switchCount τ (j + 1) = switchCount τ j + 1 := by simp [hw, hj', hj1]
        refine ⟨fun _ => ?_, by simp [hj1]⟩
        obtain ⟨hcl, hpend⟩ := ihF hj'
        by_cases hiso : 1 ≤ j ∧ S j ∧ τ (j - 1) = true
        · have hg' : runWeight τ S c (j + 1) = runWeight τ S c j * c (j + 1) * (2 * c j) := by
            simp [hg, hj', hj1, hiso]
          obtain ⟨i, hi, h⟩ := hpend hiso.1 hiso.2.2
          refine ⟨i, by omega, ?_⟩
          rw [hw', hg', prod_Ico_succ_top (by omega), prod_Ico_succ_top (by omega)]
          refine le_of_mul_le_mul_right ?_ hB0
          have hcc := mul_nonneg (hc j) (hc (j + 1))
          calc runWeight τ S c j * c (j + 1) * (2 * c j) * B
              = runWeight τ S c j * B * (2 * (c j * c (j + 1))) := by ring
            _ ≤ B ^ switchCount τ j * (∏ t ∈ Ico i j, c t) * (B ^ 2 * (c j * c (j + 1))) :=
              mul_le_mul h (mul_le_mul_of_nonneg_right h2 hcc)
                (mul_nonneg zero_le_two hcc) (mul_nonneg hpow.le (hP _ _))
            _ = _ := by ring
        · have hg' : runWeight τ S c (j + 1) = runWeight τ S c j * c (j + 1) := by
            rw [hg]
            simp only [hj', hj1, and_true, ite_true]
            rw [ite_eq_right_of_eq_false _ _ (eq_false hiso), mul_one]
          refine ⟨j + 1, le_rfl, ?_⟩
          rw [hw', hg', Nat.Ico_succ_singleton, prod_singleton]
          exact mul_le_mul_of_nonneg_right hcl (hc _)
      · -- no run is open
        have hw' : switchCount τ (j + 1) = switchCount τ j := by simp [hw, hj', hj1]
        have hg' : runWeight τ S c (j + 1) = runWeight τ S c j := by simp [hg, hj', hj1]
        rw [hw', hg']
        exact ⟨by simp [hj1], fun _ => ⟨(ihF hj').1, by simp [hj']⟩⟩
  obtain ⟨hT, hF⟩ := key N le_rfl
  rcases h : τ N with _ | _
  · exact (hF h).1.trans (pow_le_pow_right₀ hB (by omega))
  · obtain ⟨i, -, hi⟩ := hT h
    calc runWeight τ S c N ≤ B ^ switchCount τ N * B ^ 2 := by
          refine hi.trans ?_; gcongr; exact hM _ _ le_rfl
      _ = _ := by ring

end Cslib.Circuits.DepthFive
