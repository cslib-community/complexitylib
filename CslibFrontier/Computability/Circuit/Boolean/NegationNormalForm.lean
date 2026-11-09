/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula

/-!
# Negation normal form of De Morgan formulas

Pushing the negations of a De Morgan formula to the inputs by De Morgan's laws, cancelling double
negations and evaluating negated constants, gives a formula in *negation normal form*
(`Formula.nnf`), with negations only directly on inputs (`Formula.IsNNF`, `Formula.isNNF_nnf`).
It computes the same function (`Formula.eval_nnf`) with the same leaves
(`Formula.leafSize_nnf`) [Jukna, Chapter 6][Jukna2012]. Its depth counts every gate, negations
included, and is at most one more than the number of AND and OR gates on a path of the original
formula (`Formula.depth_nnf_le`). So the depth of a function with negations and constants free,
`Boolean.formulaDepth`, and its depth with every gate counted differ by at most one
(`Formula.depthWith_le_depth`, `Boolean.exists_computes_depth_le_formulaDepth_add_one`).

## Main definitions

* `Cslib.Circuits.Formula.IsNNF`: formulas whose negations apply directly to inputs.
* `Cslib.Circuits.Formula.nnf`: the negation normal form of a De Morgan formula or of its
  negation.

## Main results

* `Cslib.Circuits.Formula.isNNF_nnf`: the negation normal form is in negation normal form.
* `Cslib.Circuits.Formula.eval_nnf`, `Cslib.Circuits.Formula.leafSize_nnf`: the negation normal
  form computes the same function with the same leaves.
* `Cslib.Circuits.Formula.depth_nnf_le`: its depth is at most one more than the depth with
  negations and constants free.
* `Cslib.Circuits.Boolean.exists_computes_depth_le_formulaDepth_add_one`: every function has a
  formula whose depth exceeds its formula depth by at most one.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean Formula

variable {n : ℕ}

/-- The negation normal form of a De Morgan formula, of its negation when `b` is true: negations
are pushed to the inputs by De Morgan's laws, double negations cancel, and negated constants are
evaluated. -/
def Formula.nnf : Formula signature n → Bool → Formula signature n
  | input i, false => input i
  | input i, true => (input i).not
  | gate (.const c) _, b => const (c ^^ b)
  | gate .not args, b => nnf (args 0) (!b)
  | gate .and args, false => (nnf (args 0) false).and (nnf (args 1) false)
  | gate .and args, true => (nnf (args 0) true).or (nnf (args 1) true)
  | gate .or args, false => (nnf (args 0) false).or (nnf (args 1) false)
  | gate .or args, true => (nnf (args 0) true).and (nnf (args 1) true)

/-- A De Morgan formula is in *negation normal form* when its negations apply directly to inputs:
it is built from inputs, negated inputs and constants by conjunctions and disjunctions. -/
inductive Formula.IsNNF : Formula signature n → Prop
  /-- An input. -/
  | input (i : Fin n) : (input i).IsNNF
  /-- A negated input. -/
  | not_input (i : Fin n) : (input i).not.IsNNF
  /-- A constant. -/
  | const (b : Bool) : (const b).IsNNF
  /-- A conjunction of formulas in negation normal form. -/
  | and {F G : Formula signature n} : F.IsNNF → G.IsNNF → (F.and G).IsNNF
  /-- A disjunction of formulas in negation normal form. -/
  | or {F G : Formula signature n} : F.IsNNF → G.IsNNF → (F.or G).IsNNF

/-- A balanced disjunction of formulas in negation normal form is in negation normal form. -/
theorem Formula.IsNNF.orList {l : List (Formula signature n)} (hl : ∀ F ∈ l, F.IsNNF) :
    (orList l).IsNNF :=
  List.balancedFold_induction (p := fun l (F : Formula signature n) => (∀ G ∈ l, G.IsNNF) → F.IsNNF)
    (fun _ => .const false) (fun F h => h F (List.mem_singleton_self F))
    (fun _ _ _ _ _ _ h₁ h₂ h => .or (h₁ fun G hG => h G (List.mem_append_left _ hG))
      (h₂ fun G hG => h G (List.mem_append_right _ hG))) l hl

/-- A balanced conjunction of formulas in negation normal form is in negation normal form. -/
theorem Formula.IsNNF.andList {l : List (Formula signature n)} (hl : ∀ F ∈ l, F.IsNNF) :
    (andList l).IsNNF :=
  List.balancedFold_induction (p := fun l (F : Formula signature n) => (∀ G ∈ l, G.IsNNF) → F.IsNNF)
    (fun _ => .const true) (fun F h => h F (List.mem_singleton_self F))
    (fun _ _ _ _ _ _ h₁ h₂ h => .and (h₁ fun G hG => h G (List.mem_append_left _ hG))
      (h₂ fun G hG => h G (List.mem_append_right _ hG))) l hl

/-- The negation normal form is in negation normal form. -/
theorem Formula.isNNF_nnf (F : Formula signature n) (b : Bool) : (F.nnf b).IsNNF := by
  induction F generalizing b with
  | input i => cases b <;> simp only [nnf] <;> constructor
  | gate op args ih =>
    cases op with
    | const c => exact .const _
    | not => exact ih 0 _
    | and =>
      cases b
      · exact .and (ih 0 _) (ih 1 _)
      · exact .or (ih 0 _) (ih 1 _)
    | or =>
      cases b
      · exact .or (ih 0 _) (ih 1 _)
      · exact .and (ih 0 _) (ih 1 _)

/-- The negation normal form computes the formula, negated when `b` is true. -/
@[simp] theorem Formula.eval_nnf (F : Formula signature n) (b : Bool) (x : BitString n) :
    (F.nnf b).eval interpretation x = (F.eval interpretation x ^^ b) := by
  induction F generalizing b with
  | input i => cases b <;> simp [nnf]
  | gate op args ih =>
    cases op <;> cases b <;> simp [nnf, interpretation, ih]

/-- The negation normal form has the leaves of the formula. -/
@[simp] theorem Formula.leafSize_nnf (F : Formula signature n) (b : Bool) :
    (F.nnf b).leafSize = F.leafSize := by
  induction F generalizing b with
  | input i => cases b <;> simp [nnf]
  | gate op args ih =>
    cases op <;> cases b <;> simp [nnf, ih, Fin.sum_univ_two]

/-- The negation normal form is deeper than the formula with negations and constants free by at
most one. -/
theorem Formula.depth_nnf_le (F : Formula signature n) (b : Bool) :
    (F.nnf b).depth ≤ F.depthWith binaryCost + 1 := by
  induction F generalizing b with
  | input i => cases b <;> simp [nnf, Formula.not]
  | gate op args ih =>
    cases op with
    | const c => simp [nnf, Formula.const]
    | not => simpa [nnf] using ih 0 !b
    | and | or =>
      have h₀ := (ih 0 b).trans (Nat.add_le_add_right
        (Finset.le_sup (f := fun j => (args j).depthWith binaryCost) (Finset.mem_univ 0)) 1)
      have h₁ := (ih 1 b).trans (Nat.add_le_add_right
        (Finset.le_sup (f := fun j => (args j).depthWith binaryCost) (Finset.mem_univ 1)) 1)
      cases b <;> simp only [nnf, ← depthWith_one, depthWith_and, depthWith_or] <;>
        simp only [depthWith_one, depthWith_gate, binaryCost_and, binaryCost_or, Pi.one_apply] <;>
        exact Nat.add_le_add_right (max_le h₀ h₁) 1

/-- Every Boolean function has a De Morgan formula whose depth, counting every gate, is at most
its formula depth plus one. -/
theorem Boolean.exists_computes_depth_le_formulaDepth_add_one (f : BooleanFunction n) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧ F.depth ≤ formulaDepth f + 1 := by
  obtain ⟨F, hF, hd⟩ := exists_computes_depthWith_eq_formulaDepth f
  exact ⟨F.nnf false, fun x => by simp [hF x], hd ▸ F.depth_nnf_le false⟩

end Cslib.Circuits
