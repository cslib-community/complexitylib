/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.IID
public import Cslib.Probability.StatisticalDistance
import Complexity.Probability.IID.Occurrence
import Complexity.Probability.PMF
import Complexity.Probability.PMF.ToReal
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
transport along bijections of the domain (`IsTester.map_equiv`) and, more generally, along any
randomized map `F` of the samples that sends `P` into a property `P'` and far distributions to far
distributions (`IsTester.bind_pi`): a tester for `P'` run on the mapped samples tests `P`.

A *`k`-sample closeness tester* (`IsClosenessTester`) receives `k` independent samples of each of
two unknown distributions `p` and `q` (`acceptProb₂`). It must accept with probability at least
`2 / 3` when `p = q` and with probability at most `1 / 3` when `p` and `q` are at statistical
distance at least `ε` [Canonne][Canonne2020]. A two-sample rule run on both sample tuples passed
independently through a randomized map `F` accepts `p, q` with the probability that the rule
accepts `p.bind F, q.bind F` (`acceptProb₂_bind_pi`). With `m + k` samples of each distribution,
the acceptance probability averages, over the first `m` samples of each, the acceptance
probability of the rule on the other `k` (`acceptProb₂_append`).

## Main definitions

* `Cslib.DistributionTesting.acceptProb`: the acceptance probability of a decision rule on `k`
  independent samples.
* `Cslib.DistributionTesting.IsTester`: the `k`-sample tester property with proximity `ε`.
* `Cslib.DistributionTesting.acceptProb₂`: the acceptance probability of a decision rule on `k`
  independent samples of each of two distributions.
* `Cslib.DistributionTesting.IsClosenessTester`: the `k`-sample closeness tester property.

## Main results

* `Cslib.DistributionTesting.abs_acceptProb_sub_le`: acceptance probabilities differ by at most
  the statistical distance of the sample distributions.
* `Cslib.DistributionTesting.one_third_le_dist_iid_bind`: Le Cam's method for testers.
* `Cslib.DistributionTesting.IsTester.map_equiv`, `.comp_equiv_uniform`: relabelling the domain.
* `Cslib.DistributionTesting.acceptProb_bind_pi`, `IsTester.bind_pi`: reductions along a
  randomized map of the samples.
* `Cslib.DistributionTesting.acceptProb₂_pure`, `acceptProb₂_pure_eq_one_sub`: deterministic
  two-sample rules.
* `Cslib.DistributionTesting.acceptProb₂_bind_pi`: two-sample reductions along a randomized map.
* `Cslib.DistributionTesting.acceptProb₂_append`: conditioning on the first samples of each
  distribution.

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

/-- The probability that the randomized decision rule `T` accepts `k` independent samples of `p`
together with `k` further independent samples of `q`. -/
noncomputable def acceptProb₂ {k : ℕ} (T : (Fin k → α) → (Fin k → α) → PMF Bool)
    (p q : PMF α) : ℝ :=
  (((iid p k).bind fun x => (iid q k).bind fun y => T x y) true).toReal

/-- Unfolding lemma for `acceptProb₂`. -/
theorem acceptProb₂_eq {k : ℕ} (T : (Fin k → α) → (Fin k → α) → PMF Bool) (p q : PMF α) :
    acceptProb₂ T p q = (((iid p k).bind fun x => (iid q k).bind fun y => T x y) true).toReal := by
  rw [acceptProb₂]

/-- Two-sample acceptance probabilities are nonnegative. -/
theorem acceptProb₂_nonneg {k : ℕ} (T : (Fin k → α) → (Fin k → α) → PMF Bool) (p q : PMF α) :
    0 ≤ acceptProb₂ T p q := by
  rw [acceptProb₂_eq]
  exact ENNReal.toReal_nonneg

/-- Two-sample acceptance probabilities are at most one. -/
theorem acceptProb₂_le_one {k : ℕ} (T : (Fin k → α) → (Fin k → α) → PMF Bool) (p q : PMF α) :
    acceptProb₂ T p q ≤ 1 := by
  rw [acceptProb₂_eq]
  exact toReal_apply_le_one _ true

/-- `T` is a `k`-sample closeness tester with proximity `ε`: given `k` independent samples of each
of two unknown distributions, it accepts with probability at least `2 / 3` when they are equal and
with probability at most `1 / 3` when they are at statistical distance at least `ε`. -/
structure IsClosenessTester [Fintype α] {k : ℕ} (T : (Fin k → α) → (Fin k → α) → PMF Bool)
    (ε : ℝ) : Prop where
  accept : ∀ p, 2 / 3 ≤ acceptProb₂ T p p
  reject : ∀ p q, ε ≤ dist p q → acceptProb₂ T p q ≤ 1 / 3

section Fintype

variable [Fintype α]

/-- The two-sample acceptance probability as an expectation over both sample tuples. -/
theorem acceptProb₂_eq_sum {k : ℕ} (T : (Fin k → α) → (Fin k → α) → PMF Bool) (p q : PMF α) :
    acceptProb₂ T p q =
      ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (T x y true).toReal := by
  rw [acceptProb₂_eq, bind_apply_toReal]
  refine sum_congr rfl fun x _ => ?_
  rw [bind_apply_toReal, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  ring

/-- **Conditioning on the first samples.** With `m + k` samples of each distribution, the
acceptance probability averages, over the first `m` samples `x₁, y₁` of each, the acceptance
probability of the rule with `x₁, y₁` fixed on the other `k` samples. -/
theorem acceptProb₂_append {m k : ℕ} (T : (Fin (m + k) → α) → (Fin (m + k) → α) → PMF Bool)
    (p q : PMF α) :
    acceptProb₂ T p q = ∑ x₁, ∑ y₁, (iid p m x₁).toReal * (iid q m y₁).toReal *
      acceptProb₂ (fun x₂ y₂ => T (Fin.append x₁ x₂) (Fin.append y₁ y₂)) p q := by
  rw [acceptProb₂_eq_sum]
  simp only [acceptProb₂_eq_sum, mul_sum]
  calc ∑ x, ∑ y, (iid p (m + k) x).toReal * (iid q (m + k) y).toReal * (T x y true).toReal
      = ∑ x, (iid p (m + k) x).toReal * ∑ y, (iid q (m + k) y).toReal *
          (T x y true).toReal := by
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        ring
    _ = ∑ x₁, (iid p m x₁).toReal * ∑ x₂, (iid p k x₂).toReal * ∑ y₁, (iid q m y₁).toReal *
          ∑ y₂, (iid q k y₂).toReal * (T (Fin.append x₁ x₂) (Fin.append y₁ y₂) true).toReal := by
        rw [sum_iid_add_mul]
        refine sum_congr rfl fun x₁ _ => ?_
        congr 1
        refine sum_congr rfl fun x₂ _ => ?_
        rw [sum_iid_add_mul]
    _ = _ := by
        simp only [mul_sum]
        refine sum_congr rfl fun x₁ _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun y₁ _ => ?_
        refine sum_congr rfl fun x₂ _ => ?_
        refine sum_congr rfl fun y₂ _ => ?_
        ring

/-- A deterministic two-sample decision rule accepts with the probability of its acceptance
region. -/
theorem acceptProb₂_pure {k : ℕ} (A : (Fin k → α) → (Fin k → α) → Bool) (p q : PMF α) :
    acceptProb₂ (fun x y => PMF.pure (A x y)) p q =
      ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (if A x y then 1 else 0) := by
  rw [acceptProb₂, bind_apply_toReal]
  refine sum_congr rfl fun x _ => ?_
  rw [bind_apply_toReal, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  cases A x y <;> simp

/-- A deterministic two-sample rule accepts with probability one minus the mass of its rejection
region. -/
theorem acceptProb₂_pure_eq_one_sub {k : ℕ} (A : (Fin k → α) → (Fin k → α) → Bool)
    (p q : PMF α) :
    acceptProb₂ (fun x y => PMF.pure (A x y)) p q =
      1 - ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (if !A x y then 1 else 0) := by
  rw [acceptProb₂_pure, eq_sub_iff_add_eq, ← sum_add_distrib]
  refine (sum_congr rfl fun x _ => ?_).trans (sum_toReal (iid p k))
  rw [← sum_add_distrib]
  calc ∑ y, ((iid p k x).toReal * (iid q k y).toReal * (if A x y then 1 else 0) +
        (iid p k x).toReal * (iid q k y).toReal * (if !A x y then 1 else 0))
      = ∑ y, (iid p k x).toReal * (iid q k y).toReal :=
        sum_congr rfl fun y _ => by cases A x y <;> simp
    _ = (iid p k x).toReal := by rw [← mul_sum, sum_toReal, mul_one]

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

/-- Running a decision rule on samples passed independently through a randomized map `F` accepts
`p` with the probability that the rule accepts `p.bind F`. -/
theorem acceptProb_bind_pi [Finite α] [Finite β] {k : ℕ} (F : α → PMF β)
    (T : (Fin k → β) → PMF Bool) (p : PMF α) :
    acceptProb (fun x => (pi fun i => F (x i)).bind T) p = acceptProb T (p.bind F) := by
  rw [acceptProb_eq, acceptProb_eq, iid_bind, PMF.bind_bind]

/-- Running a two-sample decision rule on both sample tuples passed independently through a
randomized map `F` accepts `p, q` with the probability that the rule accepts `p.bind F, q.bind F`.
-/
theorem acceptProb₂_bind_pi [Finite α] [Finite β] {k : ℕ} (F : α → PMF β)
    (T : (Fin k → β) → (Fin k → β) → PMF Bool) (p q : PMF α) :
    acceptProb₂ (fun x y => (pi fun i => F (x i)).bind fun x' =>
        (pi fun i => F (y i)).bind fun y' => T x' y') p q =
      acceptProb₂ T (p.bind F) (q.bind F) := by
  rw [acceptProb₂_eq, acceptProb₂_eq, iid_bind, iid_bind]
  simp only [PMF.bind_bind]
  congr 2
  congr 1
  funext x
  rw [PMF.bind_comm]

/-- **Reduction along a randomized map.** If `F` sends every member of `P` into `P'` and every
distribution `ε`-far from `P` to one `ε'`-far from `P'`, then a `k`-sample tester for `P'` with
proximity `ε'`, run on the samples passed independently through `F`, is a `k`-sample tester for `P`
with proximity `ε`. -/
theorem IsTester.bind_pi [Fintype α] [Fintype β] {k : ℕ} {T : (Fin k → β) → PMF Bool}
    {P' : Set (PMF β)} {ε' : ℝ} (hT : IsTester T P' ε') (F : α → PMF β) {P : Set (PMF α)}
    {ε : ℝ} (hmem : ∀ q ∈ P, q.bind F ∈ P')
    (hfar : ∀ p, (∀ q ∈ P, ε ≤ dist p q) → ∀ q' ∈ P', ε' ≤ dist (p.bind F) q') :
    IsTester (fun x => (pi fun i => F (x i)).bind T) P ε where
  accept q hq := by
    rw [acceptProb_bind_pi]
    exact hT.accept _ (hmem q hq)
  reject p hp := by
    rw [acceptProb_bind_pi]
    exact hT.reject _ (hfar p hp)

/-- A uniformity tester transports along any bijection of the domain. -/
theorem IsTester.comp_equiv_uniform [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] {k : ℕ}
    {T : (Fin k → α) → PMF Bool} {ε : ℝ} (hT : IsTester T {uniformOfFintype α} ε) (e : α ≃ β) :
    IsTester (fun x => T fun i => e.symm (x i)) {uniformOfFintype β} ε := by
  simpa only [Set.image_singleton, uniformOfFintype_map_equiv] using hT.map_equiv e

end Cslib.DistributionTesting
