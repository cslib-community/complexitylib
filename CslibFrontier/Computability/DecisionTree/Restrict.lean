/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.NormalForm
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment

/-!
# Restricting decision trees

Fixing some variables can only make a function easier to compute by decision trees: answering the
queries fixed by a restriction (partial assignment) `ρ` in a tree for `f` gives a tree for the
restricted function `f ∘ ρ.fill` that is no deeper (`DecisionTree.restrict`,
`DecisionTree.complexity_comp_fill_le`).
Post-processing the output does not make it harder either (`DecisionTree.complexity_comp_le`), and
post-processing by an injective map, such as negation, does not change it
(`DecisionTree.complexity_comp_of_injective`).

## Main definitions

* `Cslib.DecisionTree.restrict`: a tree with some queries answered.

## Main results

* `Cslib.DecisionTree.complexity_comp_fill_le`: restricting does not raise decision tree
  complexity.
* `Cslib.DecisionTree.complexity_comp_of_injective`: post-processing by an injective map preserves
  decision tree complexity.
-/

@[expose] public section

namespace Cslib.DecisionTree

open BitString

variable {ι β γ : Type*}

/-- `t` with the queries fixed by `ρ` answered: a variable `i` with `ρ i = some b` reads `b`. -/
def restrict (ρ : PartialAssignment ι) : DecisionTree ι β → DecisionTree ι β
  | leaf b => leaf b
  | node i t₀ t₁ => match ρ i with
    | some b => cond b (restrict ρ t₁) (restrict ρ t₀)
    | none => node i (restrict ρ t₀) (restrict ρ t₁)

/-- The restricted tree computes the restricted function. -/
theorem eval_restrict (ρ : PartialAssignment ι) (t : DecisionTree ι β) (x : ι → Bool) :
    (t.restrict ρ).eval x = t.eval (ρ.fill x) := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [restrict, eval_node]
    cases h : ρ i with
    | none => simp [ih₀, ih₁, PartialAssignment.fill_of_eq_none h]
    | some b => cases b <;> simp [ih₀, ih₁, PartialAssignment.fill_of_eq_some h]

theorem depth_restrict_le (ρ : PartialAssignment ι) (t : DecisionTree ι β) :
    (t.restrict ρ).depth ≤ t.depth := by
  induction t with
  | leaf b => simp [restrict]
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [restrict, depth_node]
    cases ρ i with
    | none => simp only [depth_node]; omega
    | some b => cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega

variable [Finite ι]

/-- **Restricting does not raise decision tree complexity.** -/
theorem complexity_comp_fill_le (ρ : PartialAssignment ι) (f : (ι → Bool) → β) :
    complexity (f ∘ ρ.fill) ≤ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  refine (complexity_le_depth (t := t.restrict ρ) fun x => ?_).trans
    ((depth_restrict_le ρ t).trans hd.le)
  rw [eval_restrict, ht, Function.comp_apply]

/-- Post-processing the output does not raise decision tree complexity. -/
theorem complexity_comp_le (g : β → γ) (f : (ι → Bool) → β) :
    complexity (g ∘ f) ≤ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  refine (complexity_le_depth (t := t.map g) fun x => ?_).trans (by rw [depth_map, hd])
  rw [eval_map, ht, Function.comp_apply]

/-- **Post-processing by an injective map preserves decision tree complexity**: a left inverse
undoes it. -/
theorem complexity_comp_of_injective {g : β → γ} (hg : Function.Injective g)
    (f : (ι → Bool) → β) : complexity (g ∘ f) = complexity f := by
  have : Nonempty β := ⟨f fun _ => false⟩
  refine le_antisymm (complexity_comp_le g f) ?_
  simpa only [← Function.comp_assoc, (Function.leftInverse_invFun hg).comp_eq_id,
    Function.id_comp] using complexity_comp_le (Function.invFun g) (g ∘ f)

/-- Negation preserves decision tree complexity. -/
theorem complexity_not (f : (ι → Bool) → Bool) :
    complexity (fun x => !f x) = complexity f :=
  complexity_comp_of_injective (fun _ _ => Bool.not_inj) f

end Cslib.DecisionTree
