/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# CNF as polynomial equations

A clause is represented by a polynomial that vanishes when the clause holds. The variables
of the polynomial are literals, interpreted at their truth values by
`Cslib.Logic.PL.Literal.toPolyAssignment`: for a Boolean assignment `σ`, the positive coordinate
`(v, true)` receives `σ v` and the negative coordinate `(v, false)` its complement, viewed as
`0` or `1` in a commutative semiring. Over a ring these values are `a` and `1 - a`.

`Cslib.Logic.PL.Clause.toPoly` multiplies the variables for the negations of the clause's
literals. Thus `x ∨ ¬y` becomes `X (x, false) * X (y, true)`, with value `(1 - a x) * a y`
over a ring. At the literal truth values of any fixed Boolean assignment, the polynomial is
`0` for a satisfied clause and `1` otherwise. With nontrivial coefficients, a CNF is therefore
satisfied exactly when all its clause polynomials vanish at that same assignment. This
correspondence is pointwise at those Boolean and complementary coordinates; the encoding
constructs only the clause polynomials.

This is the twin-variable clause encoding used in polynomial calculus resolution (PCR)
[AlekhnovichBenSassonRazborovWigderson2002, §4.1, p. 1197]. Here the coordinates record literal
truth values and clause polynomials multiply their complements. The Boolean and complementarity
axioms of PCR are not adjoined; `Literal.toPolyAssignment` supplies their intended values directly.

## Main definitions

* `Cslib.Logic.PL.Literal.toPolyAssignment`: lift a Boolean assignment to literal truth values.
* `Cslib.Logic.PL.Clause.toPoly`: the product of variables for complementary literals.

## Main results

* `Cslib.Logic.PL.Clause.eval_toPoly`: the clause polynomial evaluates to `0` for a satisfied
  clause and `1` for a falsified clause.
* `Cslib.Logic.PL.Clause.eval_eq_true_iff_eval_toPoly_eq_zero`: clause satisfaction is equivalent
  to vanishing at the corresponding assignment.
* `Cslib.Logic.PL.CNF.eval_eq_true_iff_forall_eval_toPoly_eq_zero`: CNF satisfaction is equivalent
  to the vanishing of all clause polynomials at that same assignment.

## References

* [M. Alekhnovich, E. Ben-Sasson, A. A. Razborov, A. Wigderson,
  *Space Complexity in Propositional Calculus*, §4.1,
  p. 1197][AlekhnovichBenSassonRazborovWigderson2002]
-/

public section

namespace Cslib.Logic.PL

open MvPolynomial

variable {V : Type*}

/-- Extend a Boolean assignment to the truth values of both polarities, interpreted as `0` or `1`.
The positive coordinate receives the original bit and the negative coordinate its complement. -/
@[expose] def Literal.toPolyAssignment (R : Type*) [CommSemiring R] (σ : V → Bool) :
    Literal V → R := fun l => if Literal.eval σ l then 1 else 0

/-- The polynomial of a clause: multiply the variables for the complements of its literals.
Repeated literals contribute repeated factors. -/
@[expose] noncomputable def Clause.toPoly (c : Clause V) (R : Type*) [CommSemiring R] :
    MvPolynomial (Literal V) R := (c.map fun l => X l.negate).prod

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The positive coordinate is the original Boolean bit, interpreted in the coefficient semiring. -/
@[simp] theorem Literal.toPolyAssignment_pos (σ : V → Bool) (v : V) :
    toPolyAssignment R σ (v, true) = (σ v).toNat := by
  cases h : σ v <;> simp [toPolyAssignment, Literal.eval, h]

/-- The negative coordinate is the complementary Boolean bit. -/
@[simp] theorem Literal.toPolyAssignment_neg (σ : V → Bool) (v : V) :
    toPolyAssignment R σ (v, false) = (!σ v).toNat := by
  cases h : σ v <;> simp [toPolyAssignment, Literal.eval, h]

/-- The empty clause has polynomial `1`, expressing its falsity. -/
@[simp] theorem Clause.toPoly_nil : Clause.toPoly ([] : Clause V) R = 1 := rfl

/-- Adding a literal multiplies by its complementary variable. -/
@[simp] theorem Clause.toPoly_cons (l : Literal V) (c : Clause V) :
    Clause.toPoly (l :: c) R = X l.negate * c.toPoly R := rfl

/-- On a Boolean assignment, the clause polynomial is `0` if the clause holds and `1` otherwise. -/
theorem Clause.eval_toPoly (c : Clause V) (σ : V → Bool) :
    (c.toPoly R).eval (Literal.toPolyAssignment R σ) = if c.eval σ then 0 else 1 := by
  induction c with
  | nil => simp
  | cons l c ih =>
    simp only [Clause.toPoly_cons, map_mul, eval_X, Literal.toPolyAssignment,
      Literal.eval_negate, ih, Clause.eval_cons]
    grind

/-- A fixed Boolean assignment satisfies a clause exactly when its polynomial evaluates to zero
at the corresponding literal truth values. -/
theorem Clause.eval_eq_true_iff_eval_toPoly_eq_zero [Nontrivial R] (c : Clause V)
    (σ : V → Bool) :
    c.eval σ = true ↔ (c.toPoly R).eval (Literal.toPolyAssignment R σ) = 0 := by
  rw [Clause.eval_toPoly]
  cases c.eval σ <;> simp

/-- A fixed Boolean assignment satisfies a CNF exactly when all its clause polynomials vanish
at the same Boolean and complementary coordinates. -/
theorem CNF.eval_eq_true_iff_forall_eval_toPoly_eq_zero [Nontrivial R] (φ : CNF V)
    (σ : V → Bool) :
    φ.eval σ = true ↔ ∀ c ∈ φ, (c.toPoly R).eval (Literal.toPolyAssignment R σ) = 0 := by
  simp only [CNF.eval_eq_true_iff, Clause.eval_eq_true_iff_eval_toPoly_eq_zero (R := R)]

end CommSemiring

/-- Over a ring, the negative literal coordinate is `1 - a` when the positive coordinate is `a`. -/
theorem Literal.toPolyAssignment_neg_eq_one_sub {R : Type*} [CommRing R]
    (σ : V → Bool) (v : V) :
    toPolyAssignment R σ (v, false) = 1 - (σ v).toNat := by
  cases h : σ v <;> simp [h]

end Cslib.Logic.PL
