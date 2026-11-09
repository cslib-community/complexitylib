/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import CslibFrontier.Computability.Circuit.Formula
import Mathlib.Algebra.BigOperators.Fin

/-!
# Arithmetic formulas for linear forms

A linear form is an ordinary formula over the arithmetic signature. Coefficient symbols and
their interpretation are separate, and a selection map permits repeated or permuted inputs.
The formula includes one named zero, one constant and multiplication per coefficient, and one
addition per summand, including the initial addition to zero. `Formula.toCircuit` compiles it
with exactly the same arbitrary weighted cost.

## Main definitions

* `Cslib.Circuits.Formula.linearForm`: a linear form in selected input variables.

## Main results

* `Cslib.Circuits.Formula.eval_linearForm`: evaluation is the corresponding finite sum.
* `Cslib.Circuits.Formula.cost_linearForm`: exact cost including coefficient constants.

## References

* Adapted from LowerBound/Fusion/SumOfTerms/Waring/Translation.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
  This uses the generic formula compiler instead of a separate arithmetic expression language.
-/

@[expose] public section

namespace Cslib.Circuits.Formula

universe v u

variable {C : Type v} {R : Type u} {n : ℕ}

/-- A linear form with coefficient symbols `a`, input selection `select`, and a named zero.
The selected inputs may repeat. The sum is accumulated from left to right, starting at zero. -/
def linearForm (zero : C) : {k : ℕ} → (Fin k → C) → (Fin k → Fin n) →
    Formula (arithSignature C) n
  | 0, _, _ => .gate (.const zero) Fin.elim0
  | k + 1, a, select => .gate₂ .add rfl
      (linearForm zero (a ∘ Fin.castSucc) (select ∘ Fin.castSucc))
      (.gate₂ .mul rfl (.gate (.const (a (Fin.last k))) Fin.elim0)
        (.input (select (Fin.last k))))

/-- Interpreting a linear form gives its finite sum of coefficient products. -/
theorem eval_linearForm [Semiring R] (zero : C) (constant : C → R)
    (hzero : constant zero = 0) {k : ℕ} (a : Fin k → C) (select : Fin k → Fin n)
    (x : Fin n → R) :
    (linearForm zero a select).eval (arithInterpretationWith C constant) x =
      ∑ i, constant (a i) * x (select i) := by
  induction k with
  | zero => simp [linearForm, arithInterpretationWith, hzero]
  | succ k ih =>
    rw [linearForm, eval_gate₂, eval_gate₂, Fin.sum_univ_castSucc]
    simp [arithInterpretationWith, eval, ih, Function.comp_def]

/-- Exact weighted cost, charging the named zero and every coefficient constant. -/
theorem cost_linearForm (zero : C) (weight : ArithOp C → ℕ) {k : ℕ}
    (a : Fin k → C) (select : Fin k → Fin n) :
    (linearForm zero a select).cost weight =
      weight (.const zero) + ∑ i, (weight (.const (a i)) + weight .mul + weight .add) := by
  induction k with
  | zero => simp [linearForm]
  | succ k ih =>
    rw [linearForm, cost_gate₂, cost_gate₂, ih, Fin.sum_univ_castSucc]
    simp [cost, Nat.add_assoc]

end Cslib.Circuits.Formula
