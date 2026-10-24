/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Defs

/-!
# Executable matrix evaluation and finite tests

Rational formulas are evaluated on square rational matrices by the native formula evaluation
`Cslib.Circuits.Formula.eval` under an interpretation in `Option (Mat d)`, which rejects a
singular operand at every inverse node and otherwise inverts it exactly through the adjugate.
Partiality here is the computable stand-in for the relational semantics `Formula.Eval`, to which
it is proved equal in `Cslib.Circuits.Rational.Formula.evalMatrix?_eq_some_iff`. The finite tests
inspect the exact rational matrix values on a list; their correctness does not assert a bit-time
bound.

## Main definitions

* `Cslib.Circuits.Rational.matrixInterpretation`: the partial interpretation on rational matrices.
* `Cslib.Circuits.Rational.Formula.evalMatrix?`: executable evaluation on a matrix tuple.
* `Cslib.Circuits.Rational.Output.admissibilityTest`, `Cslib.Circuits.Rational.Output.nonzeroTest`:
  search a list for a defined, respectively an invertible, value.

## Main results

* `Cslib.Circuits.Rational.Formula.evalMatrix?_add` and its siblings: the executable evaluation
  unfolds along the constructors.

## References

* From the complexitylib port [Schlesinger2026RationalHitting] at revision
  add0aca8ee0d71e68969f2cb45cf91554a50f787 (file
  Complexitylib/RationalHitting/Evaluation/Defs.lean), built on OpenAI's formalization
  [OpenAI2026RationalHitting] at revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

@[expose] public section

namespace Cslib.Circuits.Rational

/-- The partial interpretation of the rational operations on `d × d` rational matrices: an
inverse node is undefined at a singular operand, and otherwise takes the exact inverse
`det⁻¹ • adjugate`. -/
def matrixInterpretation (d : ℕ) : Interpretation ratSignature (Option (Mat d))
  | .const q, _ => some (algebraMap ℚ (Mat d) q)
  | .add, a => do pure ((← a 0) + (← a 1))
  | .mul, a => do pure ((← a 0) * (← a 1))
  | .inv, a => do
      let v ← a 0
      if v.det = 0 then none else some (v.det⁻¹ • v.adjugate)

namespace Formula

variable {n d : ℕ}

/-- Compute a matrix value, rejecting a singular operand at every inverse node. -/
def evalMatrix? (f : Formula n) (X : Tuple n d) : Option (Mat d) :=
  f.eval (matrixInterpretation d) fun i => some (X i)

/-- Executable matrix evaluation of a variable returns the assigned matrix. -/
@[simp] theorem evalMatrix?_var (i : Fin n) (X : Tuple n d) :
    (var i).evalMatrix? X = some (X i) := rfl

/-- Executable matrix evaluation of a scalar constant embeds it via `algebraMap`. -/
@[simp] theorem evalMatrix?_const (q : ℚ) (X : Tuple n d) :
    (const q : Formula n).evalMatrix? X = some (algebraMap ℚ (Mat d) q) := rfl

/-- Executable matrix evaluation of a sum adds the two operand matrices when both are defined. -/
@[simp] theorem evalMatrix?_add (f g : Formula n) (X : Tuple n d) :
    (add f g).evalMatrix? X =
      (do
        let a ← f.evalMatrix? X
        let b ← g.evalMatrix? X
        return a + b) :=
  rfl

/-- Executable matrix evaluation of a product multiplies the operand matrices when defined. -/
@[simp] theorem evalMatrix?_mul (f g : Formula n) (X : Tuple n d) :
    (mul f g).evalMatrix? X =
      (do
        let a ← f.evalMatrix? X
        let b ← g.evalMatrix? X
        return a * b) :=
  rfl

/-- Executable matrix evaluation of an inverse returns `det⁻¹ • adjugate` when nonsingular. -/
@[simp] theorem evalMatrix?_inv (f : Formula n) (X : Tuple n d) :
    (inv f).evalMatrix? X =
      (do
        let v ← f.evalMatrix? X
        if v.det = 0 then none else some (v.det⁻¹ • v.adjugate)) :=
  rfl

end Formula

/-- Test whether at least one tuple belongs to the formula's domain. -/
def Output.admissibilityTest {n : ℕ} (H : Output n) (f : Formula n) : Bool :=
  H.tuples.any fun X => (f.evalMatrix? X).isSome

/-- Test whether at least one tuple yields an invertible matrix value. -/
def Output.nonzeroTest {n : ℕ} (H : Output n) (f : Formula n) : Bool :=
  H.tuples.any fun X => (f.evalMatrix? X).any fun v => decide (v.det ≠ 0)

end Cslib.Circuits.Rational
