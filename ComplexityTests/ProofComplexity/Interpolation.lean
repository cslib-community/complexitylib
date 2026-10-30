/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.Interpolation
import Complexity.Computability.Circuit.Monotone.Formula
import Complexity.Computability.Circuit.Unfolding

/-!
# Tests: feasible interpolation for resolution

A concrete split formula, `A(x, y) = y ∧ (y → x)` and `B(x, z) = z ∧ (z → ¬x)`, with a refutation
of seven lines. Its only interpolant is `x`: the interpolant circuit extracted from the refutation
has at most `28` gates and computes `x` exactly. A constant function is not an interpolant.

The shared variable occurs positively in `A` and negatively in `B`, so both monotone variants
apply and give monotone circuits with at most `14` gates computing `x`. With the polarities
swapped, the only interpolant is `¬x`, and no monotone circuit is an interpolant, although the
swapped formula has a refutation of the same shape.
-/

namespace ComplexityTests.ProofComplexity.Interpolation

open Cslib Cslib.Circuits Cslib.Logic.PL

/-- `A(x, y) = y ∧ (¬y ∨ x)`, which forces `x`. -/
private def A : CNF (Fin 1 ⊕ Unit) := [[(.inr (), true)], [(.inr (), false), (.inl 0, true)]]

/-- `B(x, z) = z ∧ (¬z ∨ ¬x)`, which forces `¬x`. -/
private def B : CNF (Fin 1 ⊕ Unit) := [[(.inr (), true)], [(.inr (), false), (.inl 0, false)]]

/-- The shared variable `x`, the `A`-private `y` and the `B`-private `z`. -/
private abbrev x : Fin 1 ⊕ (Unit ⊕ Unit) := .inl 0
private abbrev y : Fin 1 ⊕ (Unit ⊕ Unit) := .inr (.inl ())
private abbrev z : Fin 1 ⊕ (Unit ⊕ Unit) := .inr (.inr ())

/-- The clauses of `A` followed by those of `B`, over the joint variables. -/
example : A.appendShared B =
    [[(y, true)], [(y, false), (x, true)], [(z, true)], [(z, false), (x, false)]] := by
  decide

/-- Resolve on `y` to `x`, on `z` to `¬x`, and on `x` to the empty clause. -/
private theorem isProof : (A.appendShared B).IsProof
    [[], [(x, false)], [(x, true)], [(z, false), (x, false)], [(z, true)],
      [(y, false), (x, true)], [(y, true)]] := by
  have h₄ : (A.appendShared B).IsProof
      [[(z, false), (x, false)], [(z, true)], [(y, false), (x, true)], [(y, true)]] :=
    (((CNF.IsProof.nil.mem (by decide)).mem (by decide)).mem (by decide)).mem (by decide)
  have h₅ := h₄.resolvent (c₁ := [(y, true)]) (c₂ := [(y, false), (x, true)]) y (by decide)
    (by decide) (by decide) (by decide)
  have h₆ := h₅.resolvent (c₁ := [(z, true)]) (c₂ := [(z, false), (x, false)]) z (by decide)
    (by decide) (by decide) (by decide)
  exact h₆.resolvent (c₁ := [(x, true)]) (c₂ := [(x, false)]) x (by decide) (by decide)
    (by decide) (by decide)

/-- Every model of `A` sets `x`. -/
private theorem eq_true_of_eval_A {a : Fin 1 → Bool} {y : Unit → Bool}
    (h : A.eval (Sum.elim a y) = true) : a 0 = true := by
  simp only [A, CNF.eval, Clause.eval, List.all_cons, List.any_cons, List.all_nil, List.any_nil,
    Literal.eval_mk, Sum.elim_inl, Sum.elim_inr, Bool.or_false, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hy, hy' | hx⟩ := h
  · exact absurd (hy.symm.trans hy') (by decide)
  · exact hx

/-- Every model of `B` clears `x`. -/
private theorem eq_false_of_eval_B {a : Fin 1 → Bool} {z : Unit → Bool}
    (h : B.eval (Sum.elim a z) = true) : a 0 = false := by
  simp only [B, CNF.eval, Clause.eval, List.all_cons, List.any_cons, List.all_nil, List.any_nil,
    Literal.eval_mk, Sum.elim_inl, Sum.elim_inr, Bool.or_false, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hz, hz' | hx⟩ := h
  · exact absurd (hz.symm.trans hz') (by decide)
  · exact hx

/-- `x` is an interpolant; the constants are not. -/
example :
    A.IsInterpolant B (fun a => a 0) ∧
    ¬ A.IsInterpolant B (fun _ => true) ∧
    ¬ A.IsInterpolant B (fun _ => false) :=
  ⟨⟨fun _ _ => eq_true_of_eval_A, fun _ _ => eq_false_of_eval_B⟩,
    fun h => Bool.noConfusion (h.2 (fun _ => false) (fun _ => true) (by decide)),
    fun h => Bool.noConfusion (h.1 (fun _ => true) (fun _ => true) (by decide))⟩

/-- An interpolant witnesses unsatisfiability. -/
example : ¬ (A.appendShared B).Satisfiable :=
  CNF.IsInterpolant.not_satisfiable (f := fun a => a 0)
    ⟨fun _ _ => eq_true_of_eval_A, fun _ _ => eq_false_of_eval_B⟩

/-- Without the implications, `y ∧ z` is satisfiable, so no function is an interpolant of `y` and
`z`. -/
example : ¬ ∃ f, CNF.IsInterpolant (X := Fin 1) (Y := Unit) (Z := Unit) [[(.inr (), true)]]
    [[(.inr (), true)]] f :=
  fun h => CNF.exists_isInterpolant_iff.1 h ⟨fun _ => true, by decide⟩

/-- The interpolant circuit of the seven-line refutation has at most `28` gates and computes the
shared variable `x`: assignments with `x` extend to models of `A`, those with `¬x` to models of
`B`. -/
example : ∃ C : Circuit Boolean.signature 1 1, C.size ≤ 28 ∧
    ∀ a, C.eval Boolean.interpretation a 0 = a 0 := by
  obtain ⟨C, hsize, hC⟩ := isProof.exists_interpolant (by decide)
  refine ⟨C, hsize, fun a => ?_⟩
  have ha : a = fun _ => a 0 := funext fun i => by rw [Subsingleton.elim i 0]
  cases h0 : a 0 <;> rw [h0] at ha <;> subst ha
  · exact hC.2 _ (fun _ => true) (by decide)
  · exact hC.1 _ (fun _ => true) (by decide)

/-- The same bound from refutation size. -/
example : ∃ C : Circuit Boolean.signature 1 1, C.size ≤ 28 ∧
    A.IsInterpolant B fun a => C.eval Boolean.interpretation a 0 :=
  CNF.RefutableInSize.exists_interpolant ⟨_, isProof, by decide, le_rfl⟩

/-! ### Monotone interpolants -/

/-- `x` occurs only positively in `A` and only negatively in `B`. -/
private theorem positive : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true := by decide
private theorem negative : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → b = false := by decide

/-- A monotone interpolant of `A` and `B` computes `x`. -/
private theorem eval_eq_of_isInterpolant {C : Circuit Monotone.signature 1 1}
    (hC : A.IsInterpolant B fun a => C.eval Monotone.interpretation a 0) (a : Fin 1 → Bool) :
    C.eval Monotone.interpretation a 0 = a 0 := by
  have ha : a = fun _ => a 0 := funext fun i => by rw [Subsingleton.elim i 0]
  cases h0 : a 0 <;> rw [h0] at ha <;> subst ha
  · exact hC.2 _ (fun _ => true) (by decide)
  · exact hC.1 _ (fun _ => true) (by decide)

/-- Both monotone variants give a monotone circuit with at most `14` gates computing `x`. -/
example : ∃ C : Circuit Monotone.signature 1 1, C.size ≤ 14 ∧
    ∀ a, C.eval Monotone.interpretation a 0 = a 0 := by
  obtain ⟨C, hsize, hC⟩ := isProof.exists_monotone_interpolant_of_positive (by decide) positive
  exact ⟨C, hsize, eval_eq_of_isInterpolant hC⟩

example : ∃ C : Circuit Monotone.signature 1 1, C.size ≤ 14 ∧
    ∀ a, C.eval Monotone.interpretation a 0 = a 0 := by
  obtain ⟨C, hsize, hC⟩ := isProof.exists_monotone_interpolant_of_negative (by decide) negative
  exact ⟨C, hsize, eval_eq_of_isInterpolant hC⟩

example : ∃ C : Circuit Monotone.signature 1 1, C.size ≤ 14 ∧
    A.IsInterpolant B fun a => C.eval Monotone.interpretation a 0 :=
  CNF.RefutableInSize.exists_monotone_interpolant_of_positive ⟨_, isProof, by decide, le_rfl⟩
    positive

/-- `A` and `B` with the polarity of `x` swapped: `y ∧ (y → ¬x)` and `z ∧ (z → x)`. -/
private def A' : CNF (Fin 1 ⊕ Unit) := [[(.inr (), true)], [(.inr (), false), (.inl 0, false)]]
private def B' : CNF (Fin 1 ⊕ Unit) := [[(.inr (), true)], [(.inr (), false), (.inl 0, true)]]

/-- The swapped formula has a seven-line refutation, but neither polarity hypothesis holds. -/
example : (A'.appendShared B').RefutableInSize 7 ∧
    ¬ (∀ d ∈ A', ∀ i b, (.inl i, b) ∈ d → b = true) ∧
    ¬ (∀ d ∈ B', ∀ i b, (.inl i, b) ∈ d → b = false) := by
  refine ⟨⟨[[], [(x, true)], [(x, false)], [(z, false), (x, true)], [(z, true)],
    [(y, false), (x, false)], [(y, true)]], ?_, by decide, le_rfl⟩, by decide, by decide⟩
  have h₄ : (A'.appendShared B').IsProof
      [[(z, false), (x, true)], [(z, true)], [(y, false), (x, false)], [(y, true)]] :=
    (((CNF.IsProof.nil.mem (by decide)).mem (by decide)).mem (by decide)).mem (by decide)
  have h₅ := h₄.resolvent (c₁ := [(y, true)]) (c₂ := [(y, false), (x, false)]) y (by decide)
    (by decide) (by decide) (by decide)
  have h₆ := h₅.resolvent (c₁ := [(z, true)]) (c₂ := [(z, false), (x, true)]) z (by decide)
    (by decide) (by decide) (by decide)
  exact h₆.resolvent (c₁ := [(x, true)]) (c₂ := [(x, false)]) x (by decide) (by decide)
    (by decide) (by decide)

/-- No monotone circuit is an interpolant of the swapped formula: an interpolant is `true` at
`x = false` and `false` at `x = true`. -/
example : ¬ ∃ C : Circuit Monotone.signature 1 1,
    A'.IsInterpolant B' fun a => C.eval Monotone.interpretation a 0 := by
  rintro ⟨C, hC⟩
  have hmono : Monotone fun a => C.eval Monotone.interpretation a 0 := fun a b hab => by
    simp only [← Circuit.eval_toFormula]
    exact Monotone.monotone_eval _ hab
  have h₀ : C.eval Monotone.interpretation (fun _ => false) 0 = true :=
    hC.1 _ (fun _ => true) (by decide)
  have h₁ : C.eval Monotone.interpretation (fun _ => true) 0 = false :=
    hC.2 _ (fun _ => true) (by decide)
  have : C.eval Monotone.interpretation (fun _ => false) 0 ≤
      C.eval Monotone.interpretation (fun _ => true) 0 :=
    hmono (show (fun _ : Fin 1 => false) ≤ fun _ => true from fun _ => Bool.false_le _)
  rw [h₀, h₁] at this
  exact absurd this (by decide)

end ComplexityTests.ProofComplexity.Interpolation
