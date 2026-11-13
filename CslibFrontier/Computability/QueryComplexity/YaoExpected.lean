/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Prune
public import CslibFrontier.Computability.QueryComplexity.Randomized.DistributionalCost
public import CslibFrontier.Probability.Minimax.Value

/-!
# Expected-cost Yao minimax principle

For a total function on finitely many Boolean coordinates, there is a zero-error randomized
decision tree and an input distribution achieving matching upper and lower expected-query-cost
bounds. This is the saddle-witness form of [AroraBarak07], public draft Theorem 11.17, printed
page 216 / PDF 232. Its randomized cost is expected executed queries, not bounded-error depth.

`zeroErrorComplexity_eq_iSup_distributionalExpectedComplexity` proves the numerical equality;
`exists_optimal_expectedCost` supplies an optimal algorithm and a hard distribution, and
`exists_computes_distributionalCost_eq` supplies an optimal deterministic tree for each input law.

The private finite game has attainable bounded cost profiles as rows. It does not enumerate
output labels or require a finite output type. Repeated-query pruning makes these rows cofinal
under pointwise domination among all correct deterministic trees.

## Main definitions

* `Cslib.QueryComplexity.distributionalExpectedComplexity`: minimum distributional cost of an
  everywhere-correct deterministic tree.

## Main results

* `Cslib.QueryComplexity.zeroErrorComplexity_eq_iSup_distributionalExpectedComplexity`:
  expected-cost Yao equality.
* `Cslib.QueryComplexity.exists_optimal_expectedCost`: matching primal and dual witnesses.
* `Cslib.QueryComplexity.exists_computes_distributionalCost_eq`: deterministic minimum attainment.

## References

* [AroraBarak07], Definitions 11.13, 11.15–11.16 and Theorem 11.17, printed pages 215–216
  (public draft PDF pages 231–232).
-/

public section

namespace Cslib

open Convexity Finset

namespace QueryComplexity

variable {ι β : Type*}

/-- The minimum expected executed-query cost of an everywhere-correct deterministic tree
under `ν`. This keeps zero error on all inputs, including inputs outside the support of `ν`.
Finiteness of the coordinates ensures that correct trees exist. -/
@[nolint unusedArguments]
noncomputable def distributionalExpectedComplexity [Finite ι]
    (ν : StdSimplex ℝ (ι → Bool)) (f : (ι → Bool) → β) : ℝ :=
  sInf {c | ∃ t : DecisionTree ι β, t.Computes f ∧ t.distributionalCost ν ≤ c}

private theorem distributionalExpectedComplexity_nonempty [Finite ι]
    (ν : StdSimplex ℝ (ι → Bool)) (f : (ι → Bool) → β) :
    {c | ∃ t : DecisionTree ι β, t.Computes f ∧ t.distributionalCost ν ≤ c}.Nonempty := by
  let := Fintype.ofFinite ι
  obtain ⟨t, ht, _⟩ := DecisionTree.exists_computes f
  exact ⟨t.distributionalCost ν, t, ht, le_rfl⟩

/-- Any everywhere-correct deterministic tree bounds the distributional optimum. -/
theorem distributionalExpectedComplexity_le [Finite ι]
    {ν : StdSimplex ℝ (ι → Bool)} {f : (ι → Bool) → β}
    {t : DecisionTree ι β} {c : ℝ} (ht : t.Computes f) (hc : t.distributionalCost ν ≤ c) :
    distributionalExpectedComplexity ν f ≤ c :=
  csInf_le ⟨0, fun _ ⟨s, _, hs⟩ => (s.distributionalCost_nonneg ν).trans hs⟩ ⟨t, ht, hc⟩

/-- A common lower bound on all correct trees bounds the distributional optimum below. -/
theorem le_distributionalExpectedComplexity [Finite ι]
    {ν : StdSimplex ℝ (ι → Bool)} {f : (ι → Bool) → β} {c : ℝ}
    (hc : ∀ t : DecisionTree ι β, t.Computes f → c ≤ t.distributionalCost ν) :
    c ≤ distributionalExpectedComplexity ν f :=
  le_csInf (distributionalExpectedComplexity_nonempty ν f)
    fun _ ⟨t, ht, h⟩ => (hc t ht).trans h

section Profiles

variable {ι β : Type*} [Fintype ι]

/-- Finite action encoding used only by the minimax proof. A profile is bounded; its witness
need not have bounded structural depth. -/
private def CostProfile (f : (ι → Bool) → β) :=
  {p : (ι → Bool) → Fin (Fintype.card ι + 1) //
    ∃ t : DecisionTree ι β, t.Computes f ∧ ∀ x, t.cost x = (p x).val}

private noncomputable instance costProfileFintype (f : (ι → Bool) → β) :
    Fintype (CostProfile f) := by
  classical
  unfold CostProfile
  infer_instance

private theorem costProfile_nonempty (f : (ι → Bool) → β) :
    Nonempty (CostProfile f) := by
  classical
  obtain ⟨t, ht, hd⟩ := DecisionTree.exists_computes f
  let p : (ι → Bool) → Fin (Fintype.card ι + 1) := fun x =>
    ⟨t.cost x, Nat.lt_succ_of_le ((t.cost_le_depth x).trans hd)⟩
  exact ⟨⟨p, t, ht, fun _ => rfl⟩⟩

private noncomputable def profileTree (f : (ι → Bool) → β) (p : CostProfile f) :
    DecisionTree ι β :=
  Classical.choose p.property

private theorem profileTree_computes (f : (ι → Bool) → β) (p : CostProfile f) :
    (profileTree f p).Computes f :=
  (Classical.choose_spec p.property).1

private theorem profileTree_cost (f : (ι → Bool) → β) (p : CostProfile f)
    (x : ι → Bool) : (profileTree f p).cost x = (p.val x).val :=
  (Classical.choose_spec p.property).2 x

/-- Every correct deterministic tree is pointwise dominated by a finite game action. -/
private theorem exists_costProfile_le (f : (ι → Bool) → β) (t : DecisionTree ι β)
    (ht : t.Computes f) : ∃ p : CostProfile f, ∀ x, (p.val x).val ≤ t.cost x := by
  classical
  let s := t.prune BitString.PartialAssignment.empty
  have hs : s.Computes f := by
    intro x
    change (t.prune BitString.PartialAssignment.empty).eval x = f x
    rw [DecisionTree.eval_prune_empty]
    exact ht x
  have hd : s.depth ≤ Fintype.card ι := t.depth_prune_empty_le_card
  let p : (ι → Bool) → Fin (Fintype.card ι + 1) := fun x =>
    ⟨s.cost x, Nat.lt_succ_of_le ((s.cost_le_depth x).trans hd)⟩
  refine ⟨⟨p, s, hs, fun _ => rfl⟩, ?_⟩
  intro x
  exact t.cost_prune_empty_le x

end Profiles

private theorem exists_min_distributionalCost [Finite ι] (ν : StdSimplex ℝ (ι → Bool))
    (f : (ι → Bool) → β) : ∃ t : DecisionTree ι β, t.Computes f ∧
      ∀ s : DecisionTree ι β, s.Computes f → t.distributionalCost ν ≤ s.distributionalCost ν := by
  classical
  let := Fintype.ofFinite ι
  have : Nonempty (CostProfile f) := costProfile_nonempty f
  obtain ⟨p, _, hp⟩ := Finset.exists_min_image Finset.univ
    (fun p : CostProfile f => (profileTree f p).distributionalCost ν) Finset.univ_nonempty
  refine ⟨profileTree f p, profileTree_computes f p, ?_⟩
  intro t ht
  obtain ⟨q, hq⟩ := exists_costProfile_le f t ht
  refine (hp q (Finset.mem_univ q)).trans (DecisionTree.distributionalCost_mono ?_ ν)
  intro x
  rw [profileTree_cost]
  exact hq x

/-- Finite-game saddle witnesses obtained from the bounded cost profiles. -/
private theorem exists_expectedCost_saddle_finite [Finite ι] (f : (ι → Bool) → β) :
    ∃ (v : ℝ) (μ : RandomizedDecisionTree ι β) (ν : StdSimplex ℝ (ι → Bool)),
      μ.Computes 0 f ∧ (∀ x, μ.expectedCost x ≤ v) ∧
        ∀ t : DecisionTree ι β, t.Computes f → v ≤ t.distributionalCost ν := by
  classical
  let := Fintype.ofFinite ι
  have : Nonempty (CostProfile f) := costProfile_nonempty f
  let M : CostProfile f → (ι → Bool) → ℝ := fun p x => ((p.val x).val : ℝ)
  obtain ⟨v, ⟨p, hp⟩, q, hq⟩ := Probability.exists_isMinimaxValue M
  let μ : RandomizedDecisionTree ι β := StdSimplex.map (profileTree f) p
  refine ⟨v, μ, q, ?_, ?_, ?_⟩
  · apply RandomizedDecisionTree.computes_zero_iff.mpr
    intro t ht
    have hs : t ∈ (p.weights.mapDomain (profileTree f)).support := by
      simpa only [μ, StdSimplex.weights_map] using ht
    obtain ⟨a, _, hat⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hs)
    subst t
    exact profileTree_computes f a
  · intro x
    change RandomizedDecisionTree.expectedCost (p.map (profileTree f)) x ≤ v
    rw [RandomizedDecisionTree.expectedCost_map,
      Finsupp.sum_fintype _ _ fun _ => zero_mul _]
    calc
      ∑ a, p.weights a * ((profileTree f a).cost x : ℝ) =
          ∑ a, p.weights a * M a x := by
        apply Finset.sum_congr rfl
        intro a _
        rw [profileTree_cost]
      _ ≤ v := hp x
  · intro t ht
    obtain ⟨a, ha⟩ := exists_costProfile_le f t ht
    rw [DecisionTree.distributionalCost_eq_sum, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
    calc
      v ≤ ∑ x, q.weights x * M a x := hq a
      _ ≤ ∑ x, q.weights x * (t.cost x : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (ha x)) (q.weights_nonneg x)

/-- Each input distribution has a correct deterministic tree attaining its optimum. -/
theorem exists_computes_distributionalCost_eq [Finite ι]
    (ν : StdSimplex ℝ (ι → Bool)) (f : (ι → Bool) → β) :
    ∃ t : DecisionTree ι β, t.Computes f ∧
      t.distributionalCost ν = distributionalExpectedComplexity ν f := by
  let := Fintype.ofFinite ι
  obtain ⟨t, ht, hmin⟩ := exists_min_distributionalCost ν f
  exact ⟨t, ht, le_antisymm (le_distributionalExpectedComplexity hmin)
    (distributionalExpectedComplexity_le ht le_rfl)⟩

/-- **Expected-cost Yao witnesses** at the numerical zero-error complexity: an optimal
finite-support randomized algorithm and a hardest finite-support input distribution. -/
theorem exists_optimal_expectedCost [Finite ι] (f : (ι → Bool) → β) :
    ∃ (μ : RandomizedDecisionTree ι β) (ν : StdSimplex ℝ (ι → Bool)),
      μ.Computes 0 f ∧ (∀ x, μ.expectedCost x ≤ zeroErrorComplexity f) ∧
        ∀ t : DecisionTree ι β, t.Computes f →
          zeroErrorComplexity f ≤ t.distributionalCost ν := by
  obtain ⟨v, μ, ν, hμ, hupper, hlower⟩ := exists_expectedCost_saddle_finite f
  have hv : zeroErrorComplexity f = v := by
    refine le_antisymm (zeroErrorComplexity_le hμ hupper) ?_
    apply le_zeroErrorComplexity
    intro η c hη hc
    obtain ⟨t, ht, hcost⟩ := hη.exists_distributionalCost_le ν hc
    exact (hlower t ht).trans hcost
  exact ⟨μ, ν, hμ, fun x => (hupper x).trans_eq hv.symm,
    fun t ht => hv.trans_le (hlower t ht)⟩

/-- The averaging direction of expected-cost Yao: any input distribution lower-bounds the
worst-input expected cost of the optimal zero-error randomized algorithm. -/
theorem distributionalExpectedComplexity_le_zeroErrorComplexity [Finite ι]
    (ν : StdSimplex ℝ (ι → Bool)) (f : (ι → Bool) → β) :
    distributionalExpectedComplexity ν f ≤ zeroErrorComplexity f := by
  obtain ⟨μ, _, hμ, hc, _⟩ := exists_optimal_expectedCost f
  obtain ⟨t, ht, hcost⟩ := hμ.exists_distributionalCost_le ν hc
  exact distributionalExpectedComplexity_le ht hcost

/-- Some input distribution attains the zero-error expected complexity. -/
theorem exists_distributionalExpectedComplexity_eq_zeroErrorComplexity [Finite ι]
    (f : (ι → Bool) → β) : ∃ ν : StdSimplex ℝ (ι → Bool),
    distributionalExpectedComplexity ν f = zeroErrorComplexity f := by
  obtain ⟨_, ν, _, _, hlower⟩ := exists_optimal_expectedCost f
  exact ⟨ν, le_antisymm (distributionalExpectedComplexity_le_zeroErrorComplexity ν f)
    (le_distributionalExpectedComplexity hlower)⟩

/-- **Expected-cost Yao's minimax principle**, Arora–Barak Theorem 11.17: zero-error
randomized expected complexity is the maximum optimized distributional expected complexity. -/
theorem zeroErrorComplexity_eq_iSup_distributionalExpectedComplexity [Finite ι]
    (f : (ι → Bool) → β) :
    zeroErrorComplexity f = ⨆ ν : StdSimplex ℝ (ι → Bool),
      distributionalExpectedComplexity ν f := by
  have hbdd : BddAbove (Set.range fun ν : StdSimplex ℝ (ι → Bool) =>
      distributionalExpectedComplexity ν f) :=
    ⟨zeroErrorComplexity f, Set.forall_mem_range.mpr fun ν =>
      distributionalExpectedComplexity_le_zeroErrorComplexity ν f⟩
  obtain ⟨ν, hν⟩ := exists_distributionalExpectedComplexity_eq_zeroErrorComplexity f
  exact le_antisymm (hν.symm.trans_le (le_ciSup hbdd ν))
    (ciSup_le fun ν => distributionalExpectedComplexity_le_zeroErrorComplexity ν f)

end QueryComplexity
end Cslib
