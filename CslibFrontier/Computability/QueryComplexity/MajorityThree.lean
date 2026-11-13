/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized.DistributionalCost
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.Data.BitString.PartialAssignment.Agreement
import Mathlib.Data.Fintype.Perm

/-!
# Exact expected query complexity of three-bit majority

Uniformly choose one of the six query orders, stopping after two equal answers. The expected
query cost is two on constant inputs and `8 / 3` otherwise. The uniform input law on the six
nonconstant words forces expected cost at least `8 / 3` on every everywhere-correct decision
tree, including adaptive trees with repeated queries. A residual-subcube potential proves the
lower bound by structural induction; the proof never classifies arbitrary trees as query orders.
Local computation and random choice are uncharged, as in the existing zero-error query model.

## Main definitions

* `Cslib.QueryComplexity.MajorityThree.queryOrder`: a short-circuit tree for a given permutation.
* `Cslib.QueryComplexity.MajorityThree.algorithm`: the uniform mixture of six such trees.
* `Cslib.QueryComplexity.MajorityThree.hardDistribution`: uniform on the six nonconstant inputs.

## Main results

* `Cslib.QueryComplexity.zeroErrorComplexity_majority_three`: exact complexity `8 / 3`.
* `Cslib.QueryComplexity.MajorityThree.algorithm_expectedCost`: exact input-specific mean.
* `Cslib.QueryComplexity.MajorityThree.hardDistribution_lower`: a matching lower bound for all
  correct deterministic trees.

## References

* [AroraBarak07], Examples 11.14 and 11.18, printed pages 215–216 / PDF pages 231–232.
-/

public section

namespace Cslib.QueryComplexity

namespace MajorityThree
open Finset Convexity
open BitString

private abbrev Restriction := PartialAssignment (Fin 3)

/-- The six nonconstant inputs used by AB2007 Example 11.18. -/
private def hardInputs : Finset (Fin 3 → Bool) :=
  univ.filter fun x => x ≠ (fun _ => false) ∧ x ≠ (fun _ => true)

private theorem hardInputs_card : hardInputs.card = 6 := by decide

/-- Lower bound on the total residual cost over consistent hard inputs. -/
private def potential (ρ : Restriction) : ℕ :=
  match ρ 0, ρ 1, ρ 2 with
  | none, none, none => 16
  | some _, none, none | none, some _, none | none, none, some _ => 5
  | some a, some b, none | some a, none, some b | none, some a, some b =>
      if a = b then 0 else 2
  | _, _, _ => 0

private def hardMass (ρ : Restriction) : ℕ :=
  (hardInputs.filter ρ.Agrees).card

private def hardCost (t : DecisionTree (Fin 3) Bool) (ρ : Restriction) : ℕ :=
  ∑ x ∈ hardInputs.filter ρ.Agrees, t.cost x

/-- Each leaf correct on its residual subcube has zero potential. This finite check involves
27 partial assignments, two output labels, and eight total inputs, not an enumeration of trees. -/
private theorem potential_leaf : ∀ (ρ : Restriction) (b : Bool),
    (∀ x, ρ.Agrees x → majority 3 x = b) → potential ρ = 0 := by
  decide

/-- Bellman lower inequality for every possible fresh coordinate query. -/
private theorem potential_query : ∀ (ρ : Restriction) (i : Fin 3), ρ i = none →
    potential ρ ≤ hardMass ρ +
      potential (Function.update ρ i (some false)) +
      potential (Function.update ρ i (some true)) := by
  decide

private theorem hardCost_node_fixed (i : Fin 3) (left right : DecisionTree (Fin 3) Bool)
    (ρ : Restriction) (b : Bool) (hρ : ρ i = some b) :
    hardCost (.node i left right) ρ =
      (if b then hardCost right ρ else hardCost left ρ) + hardMass ρ := by
  have hsum : hardCost (.node i left right) ρ =
      hardCost (if b then right else left) ρ + hardMass ρ := by
    calc
      _ = ∑ x ∈ hardInputs.filter ρ.Agrees, ((if b then right else left).cost x + 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxi := (Finset.mem_filter.mp hx).2 i b hρ
        cases b <;> simp [DecisionTree.cost_node, hxi]
      _ = _ := by simp [hardCost, hardMass, Finset.sum_add_distrib]
  cases b <;> exact hsum

private theorem hardCost_node_free (i : Fin 3) (left right : DecisionTree (Fin 3) Bool)
    (ρ : Restriction) (hi : ρ i = none) :
    hardCost (.node i left right) ρ = hardMass ρ +
      hardCost left (Function.update ρ i (some false)) +
      hardCost right (Function.update ρ i (some true)) := by
  have hmass : hardMass ρ = ∑ x ∈ hardInputs.filter ρ.Agrees, (1 : ℕ) := by
    simp [hardMass]
  rw [hmass]
  simp only [hardCost, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [PartialAssignment.agrees_update_iff_of_eq_none hi false x,
    PartialAssignment.agrees_update_iff_of_eq_none hi true x]
  by_cases hx : ρ.Agrees x
  · cases hxi : x i <;> simp [hx, hxi, DecisionTree.cost_node, Nat.add_comm]
  · simp [hx]

private theorem potential_le_hardCost (t : DecisionTree (Fin 3) Bool) :
    ∀ ρ, (∀ x, ρ.Agrees x → t.eval x = majority 3 x) →
      potential ρ ≤ hardCost t ρ := by
  induction t with
  | leaf b =>
    intro ρ hc
    rw [potential_leaf ρ b (fun x hx => (hc x hx).symm)]
    exact Nat.zero_le _
  | node i left right ihl ihr =>
    intro ρ hc
    cases hρ : ρ i with
    | some b =>
      rw [hardCost_node_fixed i left right ρ b hρ]
      cases b with
      | false =>
        have hleft := ihl ρ fun x hx => by
          have hxi := hx i false hρ
          simpa only [DecisionTree.eval_node, hxi, Bool.cond_false] using hc x hx
        exact hleft.trans (Nat.le_add_right _ _)
      | true =>
        have hright := ihr ρ fun x hx => by
          have hxi := hx i true hρ
          simpa only [DecisionTree.eval_node, hxi, Bool.cond_true] using hc x hx
        exact hright.trans (Nat.le_add_right _ _)
    | none =>
      have hchild (b : Bool) (x : (Fin 3 → Bool))
          (hx : PartialAssignment.Agrees (Function.update ρ i (some b)) x) :
          (if b then right else left).eval x = majority 3 x := by
        obtain ⟨hbase, hxi⟩ := (PartialAssignment.agrees_update_iff_of_eq_none hρ b x).mp hx
        cases b <;> simpa only [DecisionTree.eval_node, hxi, Bool.cond_false,
          Bool.cond_true, Bool.false_eq_true, ↓reduceIte] using hc x hbase
      have hl := ihl (Function.update ρ i (some false)) (hchild false)
      have hr := ihr (Function.update ρ i (some true)) (hchild true)
      rw [hardCost_node_free i left right ρ hρ]
      exact (potential_query ρ i hρ).trans (by omega)

private theorem hardCost_lower (t : DecisionTree (Fin 3) Bool) (ht : t.Computes (majority 3)) :
    16 ≤ ∑ x ∈ hardInputs, t.cost x := by
  simpa [potential, hardCost, PartialAssignment.empty] using
    potential_le_hardCost t PartialAssignment.empty (fun x _ => ht x)

/-- Read π(0), π(1); stop if they agree, and otherwise read π(2). -/
@[expose] def queryOrder (π : Equiv.Perm (Fin 3)) : DecisionTree (Fin 3) Bool :=
  .node (π 0)
    (.node (π 1) (.leaf false) (.node (π 2) (.leaf false) (.leaf true)))
    (.node (π 1) (.node (π 2) (.leaf false) (.leaf true)) (.leaf true))

theorem queryOrder_eval : ∀ (π : Equiv.Perm (Fin 3)) (x : (Fin 3 → Bool)),
    (queryOrder π).eval x = majority 3 x := by
  decide

/-- This computation concerns only the explicit upper algorithm: six orders on eight inputs.
It does not classify the arbitrary trees in the lower-bound proof. -/
private theorem queryOrder_totalCost : ∀ x : (Fin 3 → Bool),
    (∑ π : Equiv.Perm (Fin 3), (queryOrder π).cost x) =
      if x 0 = x 1 ∧ x 1 = x 2 then 12 else 16 := by
  decide

/-- Choose one of the six short-circuit majority query orders uniformly. -/
noncomputable def algorithm : RandomizedDecisionTree (Fin 3) Bool :=
  RandomizedDecisionTree.uniformMixture queryOrder

theorem algorithm_computes : algorithm.Computes 0 (majority 3) :=
  RandomizedDecisionTree.computes_uniformMixture fun π x => queryOrder_eval π x

/-- Uniform on the six hard inputs, with no mass on 000 or 111. -/
noncomputable def hardDistribution : StdSimplex ℝ (Fin 3 → Bool) where
  weights := Finsupp.equivFunOnFinite.symm fun x => if x ∈ hardInputs then 1 / 6 else 0
  nonneg := by
    intro x
    change 0 ≤ (if x ∈ hardInputs then (1 / 6 : ℝ) else 0)
    split_ifs <;> norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    change (∑ x : (Fin 3 → Bool), if x ∈ hardInputs then (1 / 6 : ℝ) else 0) = 1
    simp [hardInputs_card]

/-- The hard law excludes the two constant inputs and assigns mass `1 / 6` to every other word. -/
theorem weights_hardDistribution (x : Fin 3 → Bool) :
    hardDistribution.weights x =
      if x = (fun _ => false) ∨ x = (fun _ => true) then 0 else 1 / 6 := by
  change (if x ∈ hardInputs then (1 / 6 : ℝ) else 0) = _
  by_cases h : x = (fun _ => false) ∨ x = (fun _ => true)
  · rcases h with rfl | rfl <;> simp [hardInputs]
  · simp [hardInputs, (not_or.mp h).1, (not_or.mp h).2]

private theorem hardDistribution_cost (t : DecisionTree (Fin 3) Bool) :
    t.distributionalCost hardDistribution = (∑ x ∈ hardInputs, (t.cost x : ℝ)) / 6 := by
  rw [DecisionTree.distributionalCost_eq_sum,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  change (∑ x : (Fin 3 → Bool), (if x ∈ hardInputs then (1 / 6 : ℝ) else 0) * (t.cost x : ℝ)) = _
  simp only [ite_mul, zero_mul, one_div]
  rw [← Finset.sum_filter]
  simp [div_eq_inv_mul, Finset.mul_sum]

theorem hardDistribution_lower (t : DecisionTree (Fin 3) Bool)
    (ht : t.Computes (majority 3)) : (8 : ℝ) / 3 ≤ t.distributionalCost hardDistribution := by
  rw [hardDistribution_cost, ← Nat.cast_sum]
  have h : (16 : ℝ) ≤ (∑ x ∈ hardInputs, t.cost x : ℕ) := by
    exact_mod_cast hardCost_lower t ht
  linarith

theorem algorithm_expectedCost (x : (Fin 3 → Bool)) :
    algorithm.expectedCost x = if x 0 = x 1 ∧ x 1 = x 2 then 2 else 8 / 3 := by
  rw [algorithm, RandomizedDecisionTree.expectedCost_uniformMixture,
    Fintype.expect_eq_sum_div_card, ← Nat.cast_sum, queryOrder_totalCost]
  split_ifs <;> norm_num [Fintype.card_perm]

end MajorityThree

/-- Three-bit majority has zero-error expected query complexity exactly `8 / 3`. -/
theorem zeroErrorComplexity_majority_three :
    zeroErrorComplexity (majority 3) = 8 / 3 := by
  refine le_antisymm (zeroErrorComplexity_le MajorityThree.algorithm_computes ?_) ?_
  · intro x
    rw [MajorityThree.algorithm_expectedCost]
    split_ifs <;> norm_num
  · apply le_zeroErrorComplexity
    intro μ c hμ hc
    obtain ⟨t, ht, hcost⟩ := hμ.exists_distributionalCost_le MajorityThree.hardDistribution hc
    exact (MajorityThree.hardDistribution_lower t ht).trans hcost

end Cslib.QueryComplexity
