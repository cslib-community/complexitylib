/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Cost
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment.Agreement

/-!
# Removing repeated decision-tree queries

`prune` remembers every observed answer in a partial assignment. Queries already answered are
skipped. On agreeing inputs it preserves evaluation and decreases pointwise natural weighted
cost; on a finite coordinate space its depth is bounded by the initially free coordinates.

## Main definitions

* `Cslib.DecisionTree.prune`: remove queries already fixed along the execution path.

## Main results

* `Cslib.DecisionTree.eval_prune_of_agrees`: agreeing inputs retain their output.
* `Cslib.DecisionTree.weightedCost_prune_le_of_agrees`: their weighted query cost does not grow.
* `Cslib.DecisionTree.depth_prune_le_card_free`: each initially free coordinate is read at most
  once along any remaining structural path.
-/

public section

namespace Cslib.DecisionTree

open BitString

variable {ι β : Type*} [DecidableEq ι]

/-- Prune queries whose answers are known, recording each newly queried coordinate before
recursing. Unlike `restrict`, the assignment grows along each branch. -/
@[expose] def prune : DecisionTree ι β → PartialAssignment ι → DecisionTree ι β
  | leaf b, _ => leaf b
  | node i left right, ρ => match ρ i with
    | some false => left.prune ρ
    | some true => right.prune ρ
    | none => node i (left.prune (Function.update ρ i (some false)))
        (right.prune (Function.update ρ i (some true)))

private theorem prune_spec (t : DecisionTree ι β) (ρ : PartialAssignment ι)
    (x : ι → Bool) (hx : ρ.Agrees x) (w : ι → ℕ) :
    (t.prune ρ).eval x = t.eval x ∧
      (t.prune ρ).weightedCost w x ≤ t.weightedCost w x := by
  induction t generalizing ρ with
  | leaf b => simp [prune]
  | node i left right ihl ihr =>
    cases hρ : ρ i with
    | some b =>
      have hxi : x i = b := hx i b hρ
      cases b with
      | false =>
        obtain ⟨he, hc⟩ := ihl ρ hx
        simp only [prune, hρ, eval_node, weightedCost_node, hxi, Bool.cond_false]
        exact ⟨he, by omega⟩
      | true =>
        obtain ⟨he, hc⟩ := ihr ρ hx
        simp only [prune, hρ, eval_node, weightedCost_node, hxi, Bool.cond_true]
        exact ⟨he, by omega⟩
    | none =>
      have hupdate := hx.update (i := i) rfl
      cases hxi : x i with
      | false =>
        have hx' : PartialAssignment.Agrees (Function.update ρ i (some false)) x := by
          simpa only [hxi] using hupdate
        obtain ⟨he, hc⟩ := ihl _ hx'
        simp only [prune, hρ, eval_node, weightedCost_node, hxi, Bool.cond_false]
        exact ⟨he, Nat.add_le_add_right hc _⟩
      | true =>
        have hx' : PartialAssignment.Agrees (Function.update ρ i (some true)) x := by
          simpa only [hxi] using hupdate
        obtain ⟨he, hc⟩ := ihr _ hx'
        simp only [prune, hρ, eval_node, weightedCost_node, hxi, Bool.cond_true]
        exact ⟨he, Nat.add_le_add_right hc _⟩

/-- Pruning preserves evaluation on inputs agreeing with the initial assignment. -/
theorem eval_prune_of_agrees (t : DecisionTree ι β) (ρ : PartialAssignment ι)
    {x : ι → Bool} (hx : ρ.Agrees x) : (t.prune ρ).eval x = t.eval x :=
  (prune_spec t ρ x hx (fun _ => 0)).1

/-- Pruning never increases the weighted cost on an agreeing input. Costs may be zero. -/
theorem weightedCost_prune_le_of_agrees (t : DecisionTree ι β) (ρ : PartialAssignment ι)
    {x : ι → Bool} (hx : ρ.Agrees x) (w : ι → ℕ) :
    (t.prune ρ).weightedCost w x ≤ t.weightedCost w x :=
  (prune_spec t ρ x hx w).2

/-- The depth after pruning is at most the number of initially free coordinates. -/
theorem depth_prune_le_card_free [Fintype ι] (t : DecisionTree ι β) (ρ : PartialAssignment ι) :
    (t.prune ρ).depth ≤ ρ.free.card := by
  induction t generalizing ρ with
  | leaf b => simp [prune]
  | node i left right ihl ihr =>
    cases hρ : ρ i with
    | some b =>
      cases b with
      | false => simpa only [prune, hρ] using ihl ρ
      | true => simpa only [prune, hρ] using ihr ρ
    | none =>
      have hi : i ∈ ρ.free := PartialAssignment.mem_free.mpr hρ
      have hl := ihl (Function.update ρ i (some false))
      have hr := ihr (Function.update ρ i (some true))
      rw [PartialAssignment.free_update] at hl hr
      have hcard := Finset.card_erase_add_one hi
      simp only [prune, hρ, depth_node]
      omega

@[simp] theorem eval_prune_empty (t : DecisionTree ι β) (x : ι → Bool) :
    (t.prune PartialAssignment.empty).eval x = t.eval x :=
  eval_prune_of_agrees t _ (PartialAssignment.agrees_empty x)

theorem cost_prune_empty_le (t : DecisionTree ι β) (x : ι → Bool) :
    (t.prune PartialAssignment.empty).cost x ≤ t.cost x :=
  weightedCost_prune_le_of_agrees t _ (PartialAssignment.agrees_empty x) (fun _ => 1)

theorem depth_prune_empty_le_card [Fintype ι] (t : DecisionTree ι β) :
    (t.prune PartialAssignment.empty).depth ≤ Fintype.card ι := by
  simpa only [PartialAssignment.free_empty, Finset.card_univ] using
    depth_prune_le_card_free t PartialAssignment.empty

end Cslib.DecisionTree
