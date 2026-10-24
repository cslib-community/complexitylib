/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
import Complexity.Computability.Circuit.Program

/-!
# Affine, polynomial and arithmetic bases

Three ways of computing over a commutative semiring `F`:

* the *affine basis* (`Cslib.Circuits.affineSignature`), whose operations of arity `k` are the
  affine maps `x ↦ a₀ x₀ + ... + a_{k-1} x_{k-1} + b`;
* *polynomial interpretations* (`Cslib.Circuits.Interpretation.IsPolynomial`), in which every
  operation of a signature is a polynomial in its arguments, with any coefficients and of any
  degree;
* the *arithmetic basis* (`Cslib.Circuits.arithSignature`): addition and multiplication of
  arity two, and a constant gate of arity zero for each element of `F`.

The affine and arithmetic bases are polynomial. Over a finite field every operation is a
polynomial, so the distinction matters only over infinite fields, where it is essential: an
infinite field admits injections `F × F → F`, through which a single wire can carry any amount
of information.

In an arithmetic circuit the constants are leaves, and `Cslib.Circuits.Circuit.innerSize` counts
exactly the additions and multiplications.

## Main definitions

* `Cslib.Circuits.affineSignature`, `Cslib.Circuits.affineInterpretation`: the affine basis.
* `Cslib.Circuits.ArithOp`, `Cslib.Circuits.ArithOp.arity`,
  `Cslib.Circuits.arithSignature`, `Cslib.Circuits.arithInterpretation`: the arithmetic basis.
* `Cslib.Circuits.arithInterpretationWith`: interpret the constant symbols in another carrier.
* `Cslib.Circuits.ArithOp.mulCost`: count multiplications, including scalar multiplications.
* `Cslib.Circuits.ArithOp.addCost`: count additions.
* `Cslib.Circuits.Interpretation.IsPolynomial`: every operation is a polynomial.

## Main results

* `Cslib.Circuits.isPolynomial_affineInterpretation`,
  `Cslib.Circuits.isPolynomial_arithInterpretation`: both bases are polynomial.
* `Cslib.Circuits.Circuit.fanInAtMost_two_arith`: arithmetic circuits have fan-in two.

## References

* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997], Chapter 4
-/

@[expose] public section

namespace Cslib.Circuits

universe u

variable (F : Type u)

/-- The *affine basis* over `F`: an operation of arity `k` is a vector of `k` coefficients and a
constant. -/
abbrev affineSignature : Signature.{u} where
  Op := Σ k : ℕ, (Fin k → F) × F
  Arity o := o.1

/-- An affine operation with coefficients `a` and constant `b` computes
`x ↦ ∑ i, a i * x i + b`. -/
def affineInterpretation [Semiring F] : Interpretation (affineSignature F) F :=
  fun o x => ∑ i, o.2.1 i * x i + o.2.2

/-- An affine operation with arity `k`, coefficients `a` and constant `b`. -/
@[simp] theorem affineInterpretation_apply [Semiring F] (k : ℕ) (a : Fin k → F) (b : F)
    (x : Fin k → F) : affineInterpretation F ⟨k, a, b⟩ x = ∑ i, a i * x i + b :=
  rfl

/-- The operations of the arithmetic basis. -/
inductive ArithOp : Type u
  /-- Addition. -/
  | add
  /-- Multiplication. -/
  | mul
  /-- A constant. -/
  | const (c : F)

/-- The arity of an arithmetic operation: two for addition and multiplication, zero for a
constant. -/
abbrev ArithOp.arity : ArithOp F → ℕ
  | .add => 2
  | .mul => 2
  | .const _ => 0

/-- The *arithmetic basis*: addition and multiplication of arity two, and constants of arity
zero. -/
abbrev arithSignature : Signature.{u} where
  Op := ArithOp F
  Arity := ArithOp.arity F

/-- Addition and multiplication in `R`, with constant symbols interpreted by `constant`.
For example, `MvPolynomial.C` interprets field constants as constant polynomials. -/
def arithInterpretationWith {R : Type*} [Add R] [Mul R] (constant : F → R) :
    Interpretation (arithSignature F) R
  | .add, x => x 0 + x 1
  | .mul, x => x 0 * x 1
  | .const c, _ => constant c

/-- Addition, multiplication and constants. -/
def arithInterpretation [Semiring F] : Interpretation (arithSignature F) F :=
  arithInterpretationWith F id

variable {F}

/-- Evaluating `.add` under `arithInterpretationWith` adds the two arguments. -/
@[simp] theorem arithInterpretationWith_add {R : Type*} [Add R] [Mul R] (constant : F → R)
    (x : Fin 2 → R) : arithInterpretationWith F constant .add x = x 0 + x 1 := rfl

/-- Evaluating `.mul` under `arithInterpretationWith` multiplies the two arguments. -/
@[simp] theorem arithInterpretationWith_mul {R : Type*} [Add R] [Mul R] (constant : F → R)
    (x : Fin 2 → R) : arithInterpretationWith F constant .mul x = x 0 * x 1 := rfl

/-- Evaluating `.const c` under `arithInterpretationWith` applies `constant` to `c`. -/
@[simp] theorem arithInterpretationWith_const {R : Type*} [Add R] [Mul R] (constant : F → R)
    (c : F) (x : Fin 0 → R) : arithInterpretationWith F constant (.const c) x = constant c := rfl

/-- Multiplications cost one; additions and constants are free. Multiplication by a scalar
still costs one. -/
def ArithOp.mulCost : ArithOp F → ℕ
  | .mul => 1
  | .add | .const _ => 0

/-- Additions cost one; multiplications and constants are free. -/
def ArithOp.addCost : ArithOp F → ℕ
  | .add => 1
  | .mul | .const _ => 0

/-- Evaluating the formal polynomial computed by a circuit agrees with evaluating the circuit
in the coefficient semiring. The converse need not hold over a finite field. -/
theorem Circuit.eval_arithInterpretationWith_mvPolynomial {R : Type*} [CommSemiring R]
    {n m : ℕ} (c : Circuit (arithSignature F) n m) (constant : F → R) (x : Fin n → R)
    (j : Fin m) :
    MvPolynomial.eval x
        (c.eval (arithInterpretationWith F (MvPolynomial.C ∘ constant)) MvPolynomial.X j) =
      c.eval (arithInterpretationWith F constant) x j := by
  let h : Homomorphism (arithInterpretationWith F (MvPolynomial.C ∘ constant))
      (arithInterpretationWith F constant) :=
    ⟨MvPolynomial.eval x, fun op args => by cases op <;> simp [arithInterpretationWith]⟩
  simpa [h, Function.comp_def] using congrFun (c.map_eval h MvPolynomial.X) j

/-- An interpretation is *polynomial* when every operation is given by a polynomial in its
arguments. -/
def Interpretation.IsPolynomial [CommSemiring F] {σ : Signature} (I : Interpretation σ F) :
    Prop :=
  ∀ o, ∃ P : MvPolynomial (Fin (σ.Arity o)) F, ∀ x, I o x = MvPolynomial.eval x P

/-- The affine basis is polynomial. -/
theorem isPolynomial_affineInterpretation [CommSemiring F] :
    (affineInterpretation F).IsPolynomial := by
  rintro ⟨k, a, b⟩
  exact ⟨∑ i, .C (a i) * .X i + .C b, fun x => by simp [affineInterpretation]⟩

/-- The arithmetic basis is polynomial. -/
theorem isPolynomial_arithInterpretation [CommSemiring F] :
    (arithInterpretation F).IsPolynomial := by
  rintro (_ | _ | c)
  · exact ⟨.X 0 + .X 1, fun x => by simp [arithInterpretation]⟩
  · exact ⟨.X 0 * .X 1, fun x => by simp [arithInterpretation]⟩
  · exact ⟨.C c, fun x => by simp [arithInterpretation]⟩

/-- Arithmetic circuits have fan-in at most two. -/
theorem Circuit.fanInAtMost_two_arith {n m : ℕ} (c : Circuit (arithSignature F) n m) :
    c.FanInAtMost 2 :=
  Program.fanInAtMost_iff.mpr fun k => by
    rcases (c.program.lines k).op with _ | _ | _ <;> simp

end Cslib.Circuits
