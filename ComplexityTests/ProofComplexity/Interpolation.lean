/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.Interpolation

/-!
# Tests: feasible interpolation for resolution

A concrete split formula, `A(x, y) = y ∧ (y → x)` and `B(x, z) = z ∧ (z → ¬x)`, with a refutation
of seven lines. Its only interpolant is `x`: the interpolant circuit extracted from the refutation
has at most `28` gates and computes `x` exactly. A constant function is not an interpolant.
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

end ComplexityTests.ProofComplexity.Interpolation
