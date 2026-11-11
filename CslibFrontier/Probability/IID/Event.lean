/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Event

/-!
# Events of independent draws

The probability that all of `k` independent draws from `μ` land in an event `E` is `μ(E) ^ k`
(`Cslib.Probability.PMF.toOuterMeasure_iid_forall`). The probability that at least one does is
`1 - (1 - μ(E)) ^ k` (`Cslib.Probability.PMF.toOuterMeasure_iid_exists`). Neither statement needs
finiteness of the sample space. On finite types, `Cslib.Probability.PMF.toOuterMeasure_pi_forall`
proves the first identity for products with coordinate-dependent events.

## Main results

* `Cslib.Probability.PMF.iid_map_eval`, `Cslib.Probability.PMF.toOuterMeasure_iid_eval`: each
  coordinate is distributed as `μ`.
* `Cslib.Probability.PMF.toOuterMeasure_iid_forall`: every draw lands in `E`.
* `Cslib.Probability.PMF.toOuterMeasure_iid_exists`: some draw lands in `E`.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α : Type*}

/-- All of `k` independent draws from `μ` land in `E` with probability `μ(E) ^ k`. -/
theorem toOuterMeasure_iid_forall (μ : PMF α) (E : Set α) :
    ∀ k : ℕ, (iid μ k).toOuterMeasure {v | ∀ i, v i ∈ E} = μ.toOuterMeasure E ^ k
  | 0 => by
    rw [pow_zero, iid, PMF.toOuterMeasure_pure_apply]
    exact ite_eq_left fun i => i.elim0
  | k + 1 => by
    have hpre (a : α) : ((iid μ k).map (Fin.cons a)).toOuterMeasure
        {v : Fin (k + 1) → α | ∀ i, v i ∈ E} =
        E.indicator (fun _ => μ.toOuterMeasure E ^ k) a := by
      rw [PMF.toOuterMeasure_map_apply]
      by_cases ha : a ∈ E
      · have hset : Fin.cons (n := k) (α := fun _ => α) a ⁻¹' {v | ∀ i, v i ∈ E} =
            {v | ∀ i, v i ∈ E} := by
          ext v
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero,
            Fin.cons_succ, ha, true_and]
        rw [Set.indicator_of_mem ha, hset, toOuterMeasure_iid_forall μ E k]
      · have hset : Fin.cons (n := k) (α := fun _ => α) a ⁻¹' {v | ∀ i, v i ∈ E} = ∅ := by
          ext v
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, ha,
            false_and, Set.mem_empty_iff_false]
        rw [Set.indicator_of_notMem ha, hset, MeasureTheory.measure_empty]
    rw [iid, monad_bind_eq_bind, PMF.toOuterMeasure_bind_apply, pow_succ']
    generalize μ.toOuterMeasure E ^ k = q at hpre ⊢
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [hpre]
    by_cases ha : a ∈ E
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero, zero_mul]

/-- Each coordinate of `k` independent draws from `μ` is distributed as `μ`. -/
theorem iid_map_eval (μ : PMF α) : ∀ {k : ℕ} (j : Fin k), (iid μ k).map (fun v => v j) = μ
  | 0, j => j.elim0
  | k + 1, j => by
    rw [iid, monad_bind_eq_bind, PMF.map_bind]
    refine Fin.cases ?_ (fun j => ?_) j
    · have h (a : α) : ((iid μ k).map (Fin.cons a)).map (fun v : Fin (k + 1) → α => v 0) =
          PMF.pure a := by
        rw [PMF.map_comp]
        exact PMF.map_const _ _
      simp only [h]
      exact PMF.bind_pure μ
    · have h (a : α) : ((iid μ k).map (Fin.cons a)).map (fun v : Fin (k + 1) → α => v j.succ) =
          μ := by
        rw [PMF.map_comp]
        exact iid_map_eval μ j
      simp only [h]
      exact PMF.bind_const μ μ

/-- The `j`-th of `k` independent draws from `μ` lands in `E` with probability `μ(E)`. -/
theorem toOuterMeasure_iid_eval (μ : PMF α) {k : ℕ} (j : Fin k) (E : Set α) :
    (iid μ k).toOuterMeasure {v | v j ∈ E} = μ.toOuterMeasure E := by
  have h := PMF.toOuterMeasure_map_apply (fun v : Fin k → α => v j) (iid μ k) E
  rw [iid_map_eval] at h
  exact h.symm

/-- At least one of `k` independent draws from `μ` lands in `E` with probability
`1 - (1 - μ(E)) ^ k`. -/
theorem toOuterMeasure_iid_exists (μ : PMF α) (E : Set α) (k : ℕ) :
    (iid μ k).toOuterMeasure {v | ∃ i, v i ∈ E} = 1 - (1 - μ.toOuterMeasure E) ^ k := by
  have hc : {v : Fin k → α | ∃ i, v i ∈ E} = {v | ∀ i, v i ∈ Eᶜ}ᶜ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_forall, not_not]
  have hE : μ.toOuterMeasure Eᶜ = 1 - μ.toOuterMeasure E := by
    rw [← toOuterMeasure_add_compl_ennreal μ E,
      ENNReal.add_sub_cancel_left (toOuterMeasure_ne_top μ E)]
  have h := toOuterMeasure_add_compl_ennreal (iid μ k) {v | ∀ i, v i ∈ Eᶜ}
  rw [toOuterMeasure_iid_forall, hE] at h
  rw [hc]
  exact ENNReal.eq_sub_of_add_eq (ENNReal.pow_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top))
    (by rw [add_comm]; exact h)

end Cslib.Probability.PMF
