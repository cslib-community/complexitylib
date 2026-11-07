/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.IID
public import Cslib.Probability.StatisticalDistance
import Complexity.Probability.PMF
import Complexity.Probability.StatisticalDistance.Event

/-!
# Sample-based distribution testers

A *`k`-sample tester* for a property `P` of distributions on a finite type `α` is a randomized
decision rule `T : (Fin k → α) → PMF Bool` applied to `k` independent samples of the unknown
distribution `p` (`Cslib.Probability.PMF.iid p k`). It must accept every `p ∈ P` with probability
at least `2 / 3` and accept with probability at most `1 / 3` every `p` at statistical distance at
least `ε` from all of `P` (`IsTester`) [Canonne][Canonne2020]. Statistical distance is the total
variation distance `dist` of the metric space on `PMF α` scoped to `Cslib.Probability.PMF`. The
tester is a semantic Markov kernel: this file counts samples and does not bound running time.

Le Cam's two-point method in mixture form (`one_third_le_dist_iid_bind`) turns a tester into a
lower bound: the `k`-sample distribution of any `p ∈ P` is at statistical distance at least
`1 / 3` from every mixture of `k`-sample distributions of distributions `ε`-far from `P`. Testers
transport along bijections of the domain (`IsTester.map_equiv`).

## Main definitions

* `Cslib.DistributionTesting.acceptProb`: the acceptance probability of a decision rule on `k`
  independent samples.
* `Cslib.DistributionTesting.IsTester`: the `k`-sample tester property with proximity `ε`.

## Main results

* `Cslib.DistributionTesting.abs_acceptProb_sub_le`: acceptance probabilities differ by at most
  the statistical distance of the sample distributions.
* `Cslib.DistributionTesting.one_third_le_dist_iid_bind`: Le Cam's method for testers.
* `Cslib.DistributionTesting.IsTester.map_equiv`, `.comp_equiv_uniform`: relabelling the domain.

## References

* [C. L. Canonne, *A Survey on Distribution Testing: Your Data is Big. But is it
  Blue?*][Canonne2020]
-/

public section

namespace Cslib.DistributionTesting

open Cslib.Probability.PMF Finset

variable {α β : Type*}

/-- The probability that the randomized decision rule `T` accepts `k` independent samples of
`p`. -/
noncomputable def acceptProb {k : ℕ} (T : (Fin k → α) → PMF Bool) (p : PMF α) : ℝ :=
  ((iid p k).bind T true).toReal

/-- Unfolding lemma for `acceptProb`. -/
theorem acceptProb_eq {k : ℕ} (T : (Fin k → α) → PMF Bool) (p : PMF α) :
    acceptProb T p = ((iid p k).bind T true).toReal := by
  rw [acceptProb]

/-- `T` is a `k`-sample tester for the property `P` with proximity `ε`: it accepts every member of
`P` with probability at least `2 / 3`, and accepts with probability at most `1 / 3` every
distribution at statistical distance at least `ε` from all of `P`. -/
structure IsTester [Fintype α] {k : ℕ} (T : (Fin k → α) → PMF Bool) (P : Set (PMF α)) (ε : ℝ) :
    Prop where
  accept : ∀ p ∈ P, 2 / 3 ≤ acceptProb T p
  reject : ∀ p, (∀ q ∈ P, ε ≤ dist p q) → acceptProb T p ≤ 1 / 3

section Fintype

variable [Fintype α]

/-- A deterministic decision rule accepts with the probability of its acceptance region. -/
theorem acceptProb_pure {k : ℕ} (A : (Fin k → α) → Bool) (p : PMF α) :
    acceptProb (fun x => PMF.pure (A x)) p = ∑ x, (iid p k x).toReal * (if A x then 1 else 0) := by
  rw [acceptProb, bind_apply_toReal]
  refine sum_congr rfl fun x _ => ?_
  cases A x <;> simp

/-- A deterministic rule accepts with probability one minus the mass of its rejection region. -/
theorem acceptProb_pure_eq_one_sub {k : ℕ} (A : (Fin k → α) → Bool) (p : PMF α) :
    acceptProb (fun x => PMF.pure (A x)) p =
      1 - ∑ x, (iid p k x).toReal * (if !A x then 1 else 0) := by
  rw [acceptProb_pure, eq_sub_iff_add_eq, ← sum_add_distrib]
  refine (sum_congr rfl fun x _ => ?_).trans (sum_toReal (iid p k))
  cases A x <;> simp

/-- Acceptance probabilities differ by at most the statistical distance of the `k`-sample
distributions. -/
theorem abs_acceptProb_sub_le {k : ℕ} (T : (Fin k → α) → PMF Bool) (p q : PMF α) :
    |acceptProb T p - acceptProb T q| ≤ dist (iid p k) (iid q k) :=
  abs_bind_apply_toReal_sub_le_dist _ _ T true

/-- **Le Cam's method** for testers: if `T` is a `k`-sample tester for `P`, then the `k`-sample
distribution of any `p ∈ P` is at statistical distance at least `1 / 3` from every mixture of
`k`-sample distributions of distributions that are `ε`-far from `P`. -/
theorem one_third_le_dist_iid_bind {ι : Type*} [Finite ι] {k : ℕ}
    {T : (Fin k → α) → PMF Bool} {P : Set (PMF α)} {ε : ℝ} (hT : IsTester T P ε) {p : PMF α}
    (hp : p ∈ P) (μ : PMF ι) (f : ι → PMF α) (hf : ∀ i, ∀ q ∈ P, ε ≤ dist (f i) q) :
    1 / 3 ≤ dist (iid p k) (μ.bind fun i => iid (f i) k) := by
  cases nonempty_fintype ι
  have h1 : 2 / 3 ≤ ((iid p k).bind T true).toReal := hT.accept p hp
  have h2 : ((μ.bind fun i => iid (f i) k).bind T true).toReal ≤ 1 / 3 := by
    rw [PMF.bind_bind, bind_apply_toReal]
    calc ∑ i, (μ i).toReal * ((iid (f i) k).bind T true).toReal
        ≤ ∑ i, (μ i).toReal * (1 / 3) :=
          sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hT.reject _ (hf i)) ENNReal.toReal_nonneg
      _ = 1 / 3 := by rw [← sum_mul, sum_toReal, one_mul]
  have h3 := abs_bind_apply_toReal_sub_le_dist (iid p k) (μ.bind fun i => iid (f i) k) T true
  rw [abs_le] at h3
  linarith

end Fintype

/-- Relabelling the samples of a decision rule along a bijection. -/
theorem acceptProb_comp_equiv {k : ℕ} (e : α ≃ β) (T : (Fin k → α) → PMF Bool) (p : PMF β) :
    acceptProb (fun x => T fun i => e.symm (x i)) p = acceptProb T (p.map e.symm) := by
  rw [acceptProb, acceptProb, iid_map, PMF.bind_map]
  rfl

/-- A tester transports along any bijection of the domain. -/
theorem IsTester.map_equiv [Fintype α] [Fintype β] {k : ℕ} {T : (Fin k → α) → PMF Bool}
    {P : Set (PMF α)} {ε : ℝ} (hT : IsTester T P ε) (e : α ≃ β) :
    IsTester (fun x => T fun i => e.symm (x i)) ((PMF.map e) '' P) ε where
  accept p hp := by
    obtain ⟨q, hq, rfl⟩ := hp
    rw [acceptProb_comp_equiv, PMF.map_comp, e.symm_comp_self, PMF.map_id]
    exact hT.accept q hq
  reject p hp := by
    rw [acceptProb_comp_equiv]
    refine hT.reject _ fun q hq => ?_
    have h := hp (q.map e) ⟨q, hq, rfl⟩
    rwa [← dist_map_of_injective _ _ e.injective, PMF.map_comp, e.self_comp_symm, PMF.map_id]

/-- A uniformity tester transports along any bijection of the domain. -/
theorem IsTester.comp_equiv_uniform [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] {k : ℕ}
    {T : (Fin k → α) → PMF Bool} {ε : ℝ} (hT : IsTester T {uniformOfFintype α} ε) (e : α ≃ β) :
    IsTester (fun x => T fun i => e.symm (x i)) {uniformOfFintype β} ε := by
  simpa only [Set.image_singleton, uniformOfFintype_map_equiv] using hT.map_equiv e

end Cslib.DistributionTesting
