/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Randomized
public import Complexity.Foundations.Data.BitString.ParityInterpolation
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Three queries are necessary for one-sided linearity testing

A decision tree of depth at most two that accepts every parity accepts every table `f` with
`f 0 = false`. On the path taken by `f`, at most two points are queried. Their answers agree
with a parity, so that parity reaches the same accepting leaf, even when the second query
depends on the first answer.

Consequently, any distribution on decision trees with perfect completeness on every parity
that rejects such a normalized table with positive probability has a supported tree making
at least three queries. The PMF statement has no finite-support assumption. The finite-simplex
randomized-decision-tree model has the corresponding lower bound on its worst-case depth.
These are supportwise query bounds, with no lower bound on the expected number of queries.

## Main results

* `Cslib.DecisionTree.eval_eq_true_of_depth_le_two_of_parity_complete`: two adaptive queries
  cannot reject a normalized table while accepting all parities.
* `Cslib.DecisionTree.three_le_card_queries_of_parity_complete`: rejection requires three
  distinct queried points on that input, even if other paths are long or queries repeat.
* `Cslib.BitString.exists_three_le_depth_of_parity_complete`: the lower bound for an arbitrary PMF.
* `Cslib.RandomizedDecisionTree.three_le_depth_of_parity_complete`: the lower bound in the existing
  finitely supported randomized model.

## References

The two-point interpolation and indistinguishability argument is elementary and original to this
formalization.
-/

public section

namespace Cslib

open Finset

private theorem exists_subset_pair_of_card_le_two {α : Type*} [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.card ≤ 2) : ∃ a b, s ⊆ {a, b} := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have herase : (s.erase a).card ≤ 1 := by
      rw [card_erase_of_mem ha]
      omega
    obtain ⟨b, hb⟩ := card_le_one_iff_subset_singleton.1 herase
    refine ⟨a, b, ?_⟩
    intro x hx
    by_cases hxa : x = a
    · exact mem_insert.2 (Or.inl hxa)
    · exact mem_insert.2 (Or.inr (hb (mem_erase.2 ⟨hxa, hx⟩)))
  · obtain ⟨a⟩ := ‹Nonempty α›
    exact ⟨a, a, by rw [not_nonempty_iff_eq_empty.1 hne]; exact empty_subset _⟩

namespace DecisionTree

variable {ι : Type*}

private theorem eval_eq_true_of_card_queries_le_two_of_parity_complete
    (t : DecisionTree (ι → Bool) Bool)
    (hcomplete : ∀ S : Finset ι, t.eval (parityOn S) = true)
    {f : (ι → Bool) → Bool} (hf : f 0 = false)
    [DecidableEq (ι → Bool)] (hcard : (t.queries f).card ≤ 2) : t.eval f = true := by
  classical
  obtain ⟨x, y, hqueries⟩ := exists_subset_pair_of_card_le_two (t.queries f) hcard
  obtain ⟨S, hSx, hSy⟩ := BitString.exists_parityOn_agrees_pair hf x y
  have hagree : ∀ z ∈ t.queries f, parityOn S z = f z := by
    intro z hz
    have h := hqueries hz
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl
    · exact hSx
    · exact hSy
  rw [← t.eval_eq_of_forall_mem_queries hagree]
  exact hcomplete S

/-- A tree that accepts all parities and makes at most two adaptive queries accepts every table
that is false at zero. -/
theorem eval_eq_true_of_depth_le_two_of_parity_complete
    (t : DecisionTree (ι → Bool) Bool) (hd : t.depth ≤ 2)
    (hcomplete : ∀ S : Finset ι, t.eval (parityOn S) = true)
    {f : (ι → Bool) → Bool} (hf : f 0 = false) : t.eval f = true := by
  classical
  exact t.eval_eq_true_of_card_queries_le_two_of_parity_complete hcomplete hf
    ((t.card_queries_le_depth f).trans hd)

/-- Rejecting a normalized table while accepting all parities requires three distinct queried
points on that input. This remains true when other paths are longer or positions are repeated. -/
theorem three_le_card_queries_of_parity_complete
    (t : DecisionTree (ι → Bool) Bool)
    (hcomplete : ∀ S : Finset ι, t.eval (parityOn S) = true)
    {f : (ι → Bool) → Bool} (hf : f 0 = false) (hreject : t.eval f ≠ true)
    [DecidableEq (ι → Bool)] : 3 ≤ (t.queries f).card := by
  by_contra! hcard
  exact hreject (t.eval_eq_true_of_card_queries_le_two_of_parity_complete hcomplete hf (by omega))

end DecisionTree

namespace BitString

variable {ι : Type*}

/-- Perfect completeness on parities and positive rejection of a normalized table force a
positive-mass tree of depth at least three. No finite-support hypothesis on `μ` is needed. -/
theorem exists_three_le_depth_of_parity_complete
    (μ : PMF (DecisionTree (ι → Bool) Bool))
    (hcomplete : ∀ S : Finset ι, μ.toOuterMeasure {t | t.eval (parityOn S) ≠ true} = 0)
    {f : (ι → Bool) → Bool} (hf : f 0 = false)
    (hreject : 0 < μ.toOuterMeasure {t | t.eval f ≠ true}) :
    ∃ t ∈ μ.support, 3 ≤ t.depth := by
  classical
  by_contra! hdepth
  have hzero : μ.toOuterMeasure {t | t.eval f ≠ true} = 0 := by
    apply (PMF.toOuterMeasure_apply_eq_zero_iff μ _).2
    apply Set.disjoint_left.2
    intro t ht hfail
    apply hfail
    apply t.eval_eq_true_of_depth_le_two_of_parity_complete (by have := hdepth t ht; omega)
    · intro S
      have hdisjoint := (PMF.toOuterMeasure_apply_eq_zero_iff μ _).1 (hcomplete S)
      by_contra hnot
      exact Set.disjoint_left.1 hdisjoint ht hnot
    · exact hf
  rw [hzero] at hreject
  exact lt_irrefl _ hreject

end BitString

namespace RandomizedDecisionTree

variable {ι : Type*}

/-- In the existing finite-simplex randomized-tree model, a perfectly complete parity tester
rejecting a normalized table with positive probability has worst-case query depth at least three. -/
theorem three_le_depth_of_parity_complete (μ : RandomizedDecisionTree (ι → Bool) Bool)
    (hcomplete : ∀ S : Finset ι, μ.errorProb (fun _ => true) (parityOn S) = 0)
    {f : (ι → Bool) → Bool} (hf : f 0 = false)
    (hreject : 0 < μ.errorProb (fun _ => true) f) : 3 ≤ μ.depth := by
  by_contra! hdepth
  have hzero : μ.errorProb (fun _ => true) f = 0 := by
    apply errorProb_eq_zero_iff.2
    intro t ht
    apply t.eval_eq_true_of_depth_le_two_of_parity_complete
      ((depth_le_depth ht).trans (by omega))
    · intro S
      exact errorProb_eq_zero_iff.1 (hcomplete S) t ht
    · exact hf
  rw [hzero] at hreject
  exact lt_irrefl _ hreject

end RandomizedDecisionTree

end Cslib
