/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.StatisticalDistance
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.IID

/-!
# Statistical distance of independent products

Replacing independent coordinates costs at most the sum of their individual distances. The same
bound holds when the coordinates are conditionally independent given a shared public sample:
the sample is drawn once and remains visible on both sides. For `k` independent draws from one
law, replacing the law costs at most `k` times its distance; this is the statistical hop that
replaces approximately sampled values by exactly sampled ones.

## Main results

* `Cslib.Probability.PMF.dist_pi_le_sum`: distance between products is at most the sum of distances.
* `Cslib.Probability.PMF.dist_bind_pair_pi_le_sum`: retain the shared public sample in that bound.
* `Cslib.Probability.PMF.dist_iid_le`: `k` independent draws are at distance at most `k` times the
  distance of one draw.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 3.11.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- Replacing one independent coordinate cannot cost more than its own statistical distance. -/
theorem dist_pi_update_le [DecidableEq ι] (p : ∀ i, PMF (α i)) (i : ι)
    (a b : PMF (α i)) :
    dist (pi (Function.update p i a)) (pi (Function.update p i b)) ≤ dist a b := by
  have law (q : PMF (α i)) : pi (Function.update p i q) =
      q.bind (fun value => pi (Function.update p i (PMF.pure value))) := by
    simpa only [Function.update_self, Function.update_idem] using
      (pi_bind_update (Function.update p i q) i).symm
  rw [law a, law b]
  exact dist_bind_le _ _ _

open Classical in
/-- The statistical distance of finite independent products is at most the sum of distances. -/
theorem dist_pi_le_sum [DecidableEq ι] (p q : ∀ i, PMF (α i)) :
    dist (pi p) (pi q) ≤ ∑ i, dist (p i) (q i) := by
  classical
  have bound (s : Finset ι) :
      dist (pi (fun i => if i ∈ s then p i else q i)) (pi q) ≤
        ∑ i ∈ s, dist (p i) (q i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      let mixed := fun j => if j ∈ s then p j else q j
      have insert_eq : (fun j => if j ∈ insert i s then p j else q j) =
          Function.update mixed i (p i) := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [hji, mixed]
      have mixed_eq : mixed = Function.update mixed i (q i) := by
        funext j
        by_cases hji : j = i
        · subst j; simp [mixed, hi]
        · simp [hji]
      calc
        _ ≤ dist (pi (Function.update mixed i (p i))) (pi mixed) +
            dist (pi mixed) (pi q) := by rw [insert_eq]; exact dist_triangle _ _ _
        _ ≤ dist (p i) (q i) + ∑ j ∈ s, dist (p j) (q j) := by
          apply add_le_add _ ih
          conv_lhs => rw [mixed_eq]
          simpa only [Function.update_idem] using dist_pi_update_le mixed i (p i) (q i)
        _ = _ := by rw [Finset.sum_insert hi]
  simpa using bound Finset.univ

open Classical in
/-- A common public sample may be retained when replacing conditionally independent coordinates.
There is no requirement that the coordinates be independent after the public sample is hidden. -/
theorem dist_bind_pair_pi_le_sum [DecidableEq ι] {Seed : Type*} [Fintype Seed] (seed : PMF Seed)
    (p q : Seed → ∀ i, PMF (α i)) :
    dist (seed.bind (fun s => (pi (p s)).map (s, ·)))
        (seed.bind (fun s => (pi (q s)).map (s, ·))) ≤
      ∑ i, dist (seed.bind (fun s => (p s i).map (s, ·)))
        (seed.bind (fun s => (q s i).map (s, ·))) := by
  rw [dist_bind_pair]
  calc
    _ ≤ ∑ s, (seed s).toReal * ∑ i, dist (p s i) (q s i) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (dist_pi_le_sum _ _) ENNReal.toReal_nonneg
    _ = _ := by
      simp only [Finset.mul_sum, dist_bind_pair]
      exact Finset.sum_comm

/-- **Independent draws.** `k` independent draws from `μ` and from `ν` are at statistical distance
at most `k` times the distance between `μ` and `ν`. -/
theorem dist_iid_le {β : Type*} [Fintype β] (μ ν : PMF β) (k : ℕ) :
    dist (iid μ k) (iid ν k) ≤ k * dist μ ν := by
  classical
  rw [iid_eq_pi, iid_eq_pi]
  refine (dist_pi_le_sum _ _).trans ?_
  simp

end Cslib.Probability.PMF
