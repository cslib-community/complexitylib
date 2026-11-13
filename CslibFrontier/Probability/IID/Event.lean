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
finiteness of the sample space. For independent draws `Cslib.Probability.PMF.piFin p` from a
family, every coordinate lands in its own event with the product of the probabilities
(`Cslib.Probability.PMF.toOuterMeasure_piFin_forall`), and some coordinate does with at most their
sum (`Cslib.Probability.PMF.toOuterMeasure_piFin_exists_le`). On finite types,
`Cslib.Probability.PMF.toOuterMeasure_pi_forall` proves the first identity for products with
coordinate-dependent events.

## Main results

* `Cslib.Probability.PMF.iid_map_eval`, `Cslib.Probability.PMF.toOuterMeasure_iid_eval`: each
  coordinate is distributed as `μ`.
* `Cslib.Probability.PMF.toOuterMeasure_piFin_forall`,
  `Cslib.Probability.PMF.toOuterMeasure_iid_forall`: every draw lands in its event.
* `Cslib.Probability.PMF.toOuterMeasure_piFin_exists_le`,
  `Cslib.Probability.PMF.toOuterMeasure_toReal_piFin_exists_le`: the union bound for coordinate
  events.
* `Cslib.Probability.PMF.toOuterMeasure_iid_exists`: some draw lands in `E`.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α : Type*}

/-- Every coordinate of independent draws from a family lands in its own event with the product of
the probabilities. -/
theorem toOuterMeasure_piFin_forall :
    ∀ {k : ℕ} (p : Fin k → PMF α) (E : Fin k → Set α),
      (piFin p).toOuterMeasure {v | ∀ i, v i ∈ E i} = ∏ i, (p i).toOuterMeasure (E i)
  | 0, _, _ => by
    rw [Fin.prod_univ_zero, piFin, PMF.toOuterMeasure_pure_apply]
    exact ite_eq_left fun i => i.elim0
  | k + 1, p, E => by
    have hpre (a : α) : ((piFin fun j => p j.succ).map (Fin.cons a)).toOuterMeasure
        {v : Fin (k + 1) → α | ∀ i, v i ∈ E i} =
        (E 0).indicator (fun _ => ∏ i : Fin k, (p i.succ).toOuterMeasure (E i.succ)) a := by
      rw [PMF.toOuterMeasure_map_apply]
      by_cases ha : a ∈ E 0
      · have hset : Fin.cons (n := k) (α := fun _ => α) a ⁻¹' {v | ∀ i, v i ∈ E i} =
            {v | ∀ i, v i ∈ E i.succ} := by
          ext v
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero,
            Fin.cons_succ, ha, true_and]
        rw [Set.indicator_of_mem ha, hset, toOuterMeasure_piFin_forall]
      · have hset : Fin.cons (n := k) (α := fun _ => α) a ⁻¹' {v | ∀ i, v i ∈ E i} = ∅ := by
          ext v
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, ha,
            false_and, Set.mem_empty_iff_false]
        rw [Set.indicator_of_notMem ha, hset, MeasureTheory.measure_empty]
    rw [piFin, PMF.toOuterMeasure_bind_apply, Fin.prod_univ_succ]
    generalize ∏ i : Fin k, (p i.succ).toOuterMeasure (E i.succ) = q at hpre ⊢
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [hpre]
    by_cases ha : a ∈ E 0
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero, zero_mul]

/-- All of `k` independent draws from `μ` land in `E` with probability `μ(E) ^ k`. -/
theorem toOuterMeasure_iid_forall (μ : PMF α) (E : Set α) (k : ℕ) :
    (iid μ k).toOuterMeasure {v | ∀ i, v i ∈ E} = μ.toOuterMeasure E ^ k := by
  rw [← piFin_const, ← Fin.prod_const]
  exact toOuterMeasure_piFin_forall (fun _ => μ) (fun _ => E)

/-- Each coordinate of `k` independent draws from `μ` is distributed as `μ`. -/
theorem iid_map_eval (μ : PMF α) {k : ℕ} (j : Fin k) : (iid μ k).map (fun v => v j) = μ := by
  rw [← piFin_const, piFin_map_eval]

/-- **Union bound** for independent draws from a family: some coordinate lands in its own event
with probability at most the sum of the probabilities. -/
theorem toOuterMeasure_piFin_exists_le {k : ℕ} (p : Fin k → PMF α) (E : Fin k → Set α) :
    (piFin p).toOuterMeasure {v | ∃ i, v i ∈ E i} ≤ ∑ i, (p i).toOuterMeasure (E i) := by
  have hset : {v : Fin k → α | ∃ i, v i ∈ E i} = ⋃ i, (fun v : Fin k → α => v i) ⁻¹' E i := by
    ext
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
  rw [hset]
  calc
    _ ≤ ∑ i, (piFin p).toOuterMeasure ((fun v => v i) ⁻¹' E i) :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ = _ := by
      congr 1 with i : 1
      rw [← PMF.toOuterMeasure_map_apply, piFin_map_eval]

/-- The union bound `toOuterMeasure_piFin_exists_le` for real-valued probabilities. -/
theorem toOuterMeasure_toReal_piFin_exists_le {k : ℕ} (p : Fin k → PMF α) (E : Fin k → Set α) :
    ((piFin p).toOuterMeasure {v | ∃ i, v i ∈ E i}).toReal ≤
      ∑ i, ((p i).toOuterMeasure (E i)).toReal := by
  rw [← ENNReal.toReal_sum fun i _ => toOuterMeasure_ne_top _ _]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => toOuterMeasure_ne_top _ _)
    (toOuterMeasure_piFin_exists_le p E)

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
