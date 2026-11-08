/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Cost
public import Complexity.Computability.QueryComplexity.Randomized
public import Mathlib.Algebra.BigOperators.Expect

/-!
# Zero-error randomized decision trees and expected query cost

A randomized decision tree `μ` (`RandomizedDecisionTree`) draws a deterministic decision tree and
runs it. Its *expected cost* on an input `x` is the expected number of queries the drawn tree makes
on `x` (`RandomizedDecisionTree.expectedCost`). The *zero-error* (Las Vegas) randomized decision
tree complexity `R₀(f)` is the least `c` such that some randomized decision tree that is always
correct (`μ.Computes 0 f`) makes at most `c` queries in expectation on every input
(`QueryComplexity.zeroErrorComplexity`) [BuhrmanDeWolf2002], [MotwaniRaghavan95].

This differs from `QueryComplexity.randomizedComplexity 0 f`, which charges the worst case over the
coins and equals the deterministic complexity `D(f)`. Expected cost can be much smaller: for the
complete binary AND–OR tree on `n = 4 ^ k` leaves `D = n` while `R₀ ≤ n ^ (log₄ 3)`
(`Complexity.Computability.QueryComplexity.AndOrTree.Randomized`). Always `R₀(f) ≤ D(f)`
(`QueryComplexity.zeroErrorComplexity_le_complexity`).

The uniform mixture of a finite family of trees (`RandomizedDecisionTree.uniformMixture`) draws a
member of the family uniformly; its expected cost is the average of the costs
(`RandomizedDecisionTree.expectedCost_uniformMixture`). This describes a randomized algorithm whose
coin tosses select a deterministic tree.

## Main definitions

* `Cslib.RandomizedDecisionTree.expectedCost`: the expected number of queries on an input.
* `Cslib.RandomizedDecisionTree.uniformMixture`: the uniform mixture of a finite family of trees.
* `Cslib.QueryComplexity.zeroErrorComplexity`: the zero-error randomized complexity `R₀(f)`.

## Main results

* `Cslib.RandomizedDecisionTree.expectedCost_uniformMixture`: the expected cost of a uniform
  mixture is the average cost.
* `Cslib.RandomizedDecisionTree.errorProb_uniformMixture`: the error probability of a uniform
  mixture is the fraction of wrong members.
* `Cslib.RandomizedDecisionTree.computes_uniformMixture`: a mixture of correct trees is always
  correct.
* `Cslib.QueryComplexity.zeroErrorComplexity_le`: an always-correct randomized tree bounds `R₀`.
* `Cslib.QueryComplexity.zeroErrorComplexity_le_complexity`: `R₀(f) ≤ D(f)`.
* `Cslib.QueryComplexity.one_le_zeroErrorComplexity`: `1 ≤ R₀(f)` for nonconstant `f`.

## References

* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
* [R. Motwani, P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan95]
-/

public section

namespace Cslib

open Convexity Finset
open scoped BigOperators

namespace RandomizedDecisionTree

variable {ι β : Type*}

/-- The expected number of queries that the tree drawn from `μ` makes on the input `x`. -/
noncomputable def expectedCost (μ : RandomizedDecisionTree ι β) (x : ι → Bool) : ℝ :=
  μ.weights.sum fun t w => w * (t.cost x : ℝ)

variable {μ : RandomizedDecisionTree ι β} {x : ι → Bool}

theorem expectedCost_nonneg : 0 ≤ μ.expectedCost x :=
  Finset.sum_nonneg fun t _ => mul_nonneg (μ.weights_nonneg t) (Nat.cast_nonneg _)

/-- A deterministic tree makes its own number of queries. -/
@[simp] theorem expectedCost_single (t : DecisionTree ι β) (x : ι → Bool) :
    expectedCost (StdSimplex.single t : RandomizedDecisionTree ι β) x = t.cost x := by
  simp [expectedCost]

/-- The expected cost is at most the depth, the worst case over the inputs and the coins. -/
theorem expectedCost_le_depth : μ.expectedCost x ≤ μ.depth :=
  StdSimplex.sum_mul_le_of_forall_le fun t ht =>
    Nat.cast_le.2 ((t.cost_le_depth x).trans (depth_le_depth ht))

section UniformMixture

variable {C : Type*} [Fintype C] [Nonempty C]

/-- The uniform mixture of a finite family `g` of decision trees: draw `c` uniformly from `C` and
run `g c`. -/
noncomputable def uniformMixture (g : C → DecisionTree ι β) : RandomizedDecisionTree ι β :=
  StdSimplex.map g
    { weights := Finsupp.equivFunOnFinite.symm fun _ => (Fintype.card C : ℝ)⁻¹
      nonneg := fun _ => inv_nonneg.2 (Nat.cast_nonneg _)
      total := by
        rw [Finsupp.sum_fintype _ _ fun _ => rfl]
        simp [Finset.card_univ, Fintype.card_ne_zero] }

/-- Every tree that the uniform mixture can draw is a member of the family. -/
theorem exists_eq_of_mem_support_uniformMixture {g : C → DecisionTree ι β}
    {t : DecisionTree ι β} (ht : t ∈ (uniformMixture g).weights.support) : ∃ c, g c = t := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support ht)
  exact ⟨c, hc⟩

/-- The uniform mixture of trees computing `f` computes `f` with error `0`. -/
theorem computes_uniformMixture {g : C → DecisionTree ι β} {f : (ι → Bool) → β}
    (hg : ∀ c, (g c).Computes f) : (uniformMixture g).Computes 0 f :=
  computes_zero_iff.2 fun t ht => by
    obtain ⟨c, rfl⟩ := exists_eq_of_mem_support_uniformMixture ht
    exact hg c

/-- The expected cost of the uniform mixture of `g` is the average over `c` of the cost of
`g c`. -/
theorem expectedCost_uniformMixture (g : C → DecisionTree ι β) (x : ι → Bool) :
    (uniformMixture g).expectedCost x = 𝔼 c, ((g c).cost x : ℝ) := by
  rw [expectedCost, uniformMixture, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _, Fintype.expect_eq_sum_div_card, sum_div]
  refine sum_congr rfl fun c _ => ?_
  simp [div_eq_inv_mul]

/-- The error probability of the uniform mixture of `g` on `x` is the fraction of the members of
the family that answer wrongly on `x`. -/
theorem errorProb_uniformMixture [DecidableEq β] (g : C → DecisionTree ι β)
    (f : (ι → Bool) → β) (x : ι → Bool) :
    (uniformMixture g).errorProb f x =
      (#{c | (g c).eval x ≠ f x} : ℝ) / Fintype.card C := by
  rw [errorProb_eq_sum, uniformMixture, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _, card_filter, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun c _ => ?_
  by_cases h : (g c).eval x = f x <;> simp [h, div_eq_inv_mul]

end UniformMixture

end RandomizedDecisionTree

namespace QueryComplexity

open RandomizedDecisionTree

variable {ι β : Type*} {f : (ι → Bool) → β}

/-- The zero-error (Las Vegas) randomized decision tree complexity `R₀(f)`: the least `c` such
that some randomized decision tree computing `f` with error `0` makes at most `c` queries in
expectation on every input. It is the junk value `0` (`Real.sInf_empty`) when no decision tree
computes `f`, which cannot happen over finitely many variables
(`QueryComplexity.zeroErrorComplexity_le_complexity`). -/
noncomputable def zeroErrorComplexity (f : (ι → Bool) → β) : ℝ :=
  sInf {c | ∃ μ : RandomizedDecisionTree ι β, μ.Computes 0 f ∧ ∀ x, μ.expectedCost x ≤ c}

/-- An always-correct randomized decision tree making at most `c` queries in expectation on every
input bounds `R₀(f)` by `c`. -/
theorem zeroErrorComplexity_le {μ : RandomizedDecisionTree ι β} {c : ℝ} (hμ : μ.Computes 0 f)
    (hc : ∀ x, μ.expectedCost x ≤ c) : zeroErrorComplexity f ≤ c :=
  csInf_le ⟨0, fun _ ⟨_, _, h⟩ => expectedCost_nonneg.trans (h fun _ => false)⟩ ⟨μ, hμ, hc⟩

theorem zeroErrorComplexity_nonneg : 0 ≤ zeroErrorComplexity f := by
  by_cases h : {c | ∃ μ : RandomizedDecisionTree ι β, μ.Computes 0 f ∧
      ∀ x, μ.expectedCost x ≤ c}.Nonempty
  · exact le_csInf h fun _ ⟨_, _, hc⟩ => expectedCost_nonneg.trans (hc fun _ => false)
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [zeroErrorComplexity, h, Real.sInf_empty]

/-- Randomness with zero error does not hurt: `R₀(f) ≤ D(f)`. -/
theorem zeroErrorComplexity_le_complexity [Finite ι] (f : (ι → Bool) → β) :
    zeroErrorComplexity f ≤ DecisionTree.complexity f := by
  obtain ⟨t, ht, hd⟩ := DecisionTree.exists_computes_depth_eq_complexity f
  refine zeroErrorComplexity_le (computes_single ht le_rfl) fun x => ?_
  rw [expectedCost_single, ← hd]
  exact Nat.cast_le.2 (t.cost_le_depth x)

/-- A nonconstant function needs at least one query in expectation: `1 ≤ R₀(f)`. Every tree
computing `f` is a node, so it makes at least one query on every input. -/
theorem one_le_zeroErrorComplexity [Finite ι] (hf : ∃ x y, f x ≠ f y) :
    1 ≤ zeroErrorComplexity f := by
  obtain ⟨t, ht, -⟩ := DecisionTree.exists_computes_depth_eq_complexity f
  refine le_csInf ⟨t.depth, StdSimplex.single t, computes_single ht le_rfl, fun x => by
    rw [expectedCost_single]
    exact Nat.cast_le.2 (t.cost_le_depth x)⟩ ?_
  rintro c ⟨μ, hμ, hc⟩
  obtain ⟨t, ht, hle⟩ :=
    StdSimplex.exists_mem_support_le_sum_mul μ fun t => (t.cost fun _ => false : ℝ)
  refine le_trans ?_ (hle.trans (hc fun _ => false))
  cases t with
  | leaf b =>
    obtain ⟨x, y, hxy⟩ := hf
    exact absurd ((computes_zero_iff.1 hμ _ ht x).symm.trans (computes_zero_iff.1 hμ _ ht y)) hxy
  | node i t₀ t₁ =>
    simp only [DecisionTree.cost, DecisionTree.weightedCost_node, Nat.cast_add, Nat.cast_one]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)

end QueryComplexity

end Cslib
