/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.VP
public import CslibFrontier.Foundations.LinearAlgebra.FreeAlgebra

/-!
# Non-commutative polynomials computed by arithmetic circuits

An arithmetic circuit over `arithSignature K` computes a polynomial in every `K`-algebra. Evaluated
in the free algebra `FreeAlgebra K (Fin n)` at the variables, with the constant symbol `a`
denoting `algebraMap K _ a`, it computes the *non-commutative polynomial*
`Cslib.Circuits.Circuit.noncommPolynomial`. Multiplication gates keep the order of their two
arguments, so this is the circuit's polynomial in the non-commutative sense of Nisan
[Nisan1991NonCommutative].

* Evaluating the circuit in any `K`-algebra `A`, commutative or not, at `x : Fin n → A`
  substitutes `x` into the non-commutative polynomial (`Circuit.lift_noncommPolynomial`).
* Substituting the commuting variables gives the commutative polynomial `Circuit.polynomial`
  (`Circuit.lift_X_noncommPolynomial`).

## Main definitions

* `Cslib.Circuits.Circuit.noncommPolynomial`: the non-commutative polynomial of an output.

## Main results

* `Cslib.Circuits.Circuit.lift_noncommPolynomial`: evaluation in a `K`-algebra.
* `Cslib.Circuits.Circuit.lift_X_noncommPolynomial`: abelianization gives `Circuit.polynomial`.

## References

* [N. Nisan, *Lower bounds for non-commutative computation*][Nisan1991NonCommutative]
-/

public section

namespace Cslib.Circuits

open FreeAlgebra

variable {K : Type*} [CommSemiring K] {n m : ℕ}

/-- The non-commutative polynomial computed at output `j` of an arithmetic circuit with constants
from `K`: the circuit evaluated in `FreeAlgebra K (Fin n)` at the variables, the constant symbol
`a` denoting `algebraMap K _ a`. -/
noncomputable def Circuit.noncommPolynomial (c : Circuit (arithSignature K) n m) (j : Fin m) :
    FreeAlgebra K (Fin n) :=
  c.eval (arithInterpretationWith K (algebraMap K _)) (ι K) j

/-- The non-commutative polynomial is the evaluation in the free algebra at the variables. -/
theorem Circuit.noncommPolynomial_eq_eval (c : Circuit (arithSignature K) n m) (j : Fin m) :
    c.noncommPolynomial j = c.eval (arithInterpretationWith K (algebraMap K _)) (ι K) j := by
  rw [Circuit.noncommPolynomial]

/-- Evaluating a circuit in a `K`-algebra, commutative or not, substitutes the inputs into its
non-commutative polynomial. -/
theorem Circuit.lift_noncommPolynomial {A : Type*} [Semiring A] [Algebra K A]
    (c : Circuit (arithSignature K) n m) (x : Fin n → A) (j : Fin m) :
    FreeAlgebra.lift K x (c.noncommPolynomial j) =
      c.eval (arithInterpretationWith K (algebraMap K A)) x j := by
  let h : Homomorphism (arithInterpretationWith K (algebraMap K (FreeAlgebra K (Fin n))))
      (arithInterpretationWith K (algebraMap K A)) :=
    ⟨FreeAlgebra.lift K x, fun op args => by cases op <;> simp [arithInterpretationWith]⟩
  refine (congrFun (c.map_eval h (ι K)) j).trans ?_
  congr 1
  exact ι_comp_lift x

/-- Substituting the commuting variables into the non-commutative polynomial of a circuit gives
its commutative polynomial. -/
theorem Circuit.lift_X_noncommPolynomial (c : Circuit (arithSignature K) n m) (j : Fin m) :
    FreeAlgebra.lift K MvPolynomial.X (c.noncommPolynomial j) = c.polynomial j := by
  rw [c.lift_noncommPolynomial]
  rfl

end Cslib.Circuits
