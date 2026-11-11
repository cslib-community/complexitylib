/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.Boolean
public import CslibFrontier.Logics.Propositional.Algebraic.CNF
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Refuting CNF formulas over the Boolean cube

The pointwise CNF arithmetization of `CslibFrontier.Logics.Propositional.Algebraic.CNF` (#2887)
encodes a clause by a polynomial `Cslib.Logic.PL.Clause.toPoly` in the twin variables
`Literal V`, one for each polarity of each variable. This module substitutes `X v` for the
positive variable `(v, true)` and `1 - X v` for the negative variable `(v, false)`
(`Cslib.Logic.PL.Literal.truthPoly`). The result is the standard product encoding of clauses
[CleggEdmondsImpagliazzo1996] in the original variables, with variables read as `1 = true`
(`Cslib.BitString.bitPoint`): a clause becomes `∏_{v ∈ c} (1 - X v) * ∏_{¬v ∈ c} X v`
(`Cslib.Logic.PL.Clause.toBoolPoly`). At a point of the cube the clause polynomial is `0` when
the clause is satisfied and `1` when it is falsified (`Cslib.Logic.PL.Clause.eval_toBoolPoly`).
This comes from `Cslib.Logic.PL.Clause.eval_toPoly` through the substitution.

A formula `φ` becomes the list of its clause polynomials (`Cslib.Logic.PL.CNF.toBoolPolys`),
refuted with the Boolean axioms of the variables. The Boolean solutions are the satisfying
assignments (`Cslib.Logic.PL.CNF.isBoolSolution_toBoolPolys_iff`). Soundness and completeness of
`CslibFrontier.Logics.Propositional.Algebraic.Boolean` then give:

* a Nullstellensatz or polynomial calculus refutation certifies that `φ` is unsatisfiable
  (`Cslib.Logic.PL.CNF.not_satisfiable_of_ns`, `Cslib.Logic.PL.CNF.not_satisfiable_of_pc`);
* over a field, a formula with clauses of at most `w` literals in the variables of a finite type
  `V` is refutable in degree `card V + w` exactly when it is unsatisfiable
  (`Cslib.Logic.PL.CNF.ns_refutableInDegree_iff`, `Cslib.Logic.PL.CNF.pc_refutableInDegree_iff`).

## Main definitions

* `Cslib.Logic.PL.Literal.truthPoly`: `X v` for `v` and `1 - X v` for `¬v`.
* `Cslib.Logic.PL.Clause.toBoolPoly`, `Cslib.Logic.PL.CNF.toBoolPolys`: the clause polynomials in
  the original variables.

## Main results

* `Cslib.Logic.PL.Clause.eval_toBoolPoly`: the clause polynomial is `0` exactly where the clause is
  satisfied.
* `Cslib.Logic.PL.CNF.isBoolSolution_toBoolPolys_iff`: Boolean solutions are satisfying
  assignments.
* `Cslib.Logic.PL.CNF.not_satisfiable_of_ns`, `Cslib.Logic.PL.CNF.not_satisfiable_of_pc`:
  soundness.
* `Cslib.Logic.PL.CNF.ns_refutableInDegree_iff`, `Cslib.Logic.PL.CNF.pc_refutableInDegree_iff`:
  refutability in degree `card V + w` exactly when the formula is unsatisfiable.

## References

* [M. Clegg, J. Edmonds, R. Impagliazzo, *Using the Groebner basis algorithm to find proofs of
  unsatisfiability*][CleggEdmondsImpagliazzo1996]
-/

public section

open MvPolynomial Cslib.BitString Cslib.Logic.PL.Algebraic

namespace Cslib.Logic.PL

variable {V : Type*}

/-- The truth value of a literal as a polynomial in the variables: `X v` for `v` and `1 - X v` for
`¬v`. -/
@[expose] noncomputable def Literal.truthPoly (R : Type*) [CommRing R] (l : Literal V) :
    MvPolynomial V R :=
  if l.2 then X l.1 else 1 - X l.1

/-- The polynomial of a clause in the original variables: the twin-variable clause polynomial
`Cslib.Logic.PL.Clause.toPoly` with every literal variable replaced by its truth value. -/
@[expose] noncomputable def Clause.toBoolPoly (R : Type*) [CommRing R] (c : Clause V) :
    MvPolynomial V R :=
  bind₁ (Literal.truthPoly R) (c.toPoly R)

/-- The clause polynomials of a CNF formula in the original variables. -/
@[expose] noncomputable def CNF.toBoolPolys (R : Type*) [CommRing R] (φ : CNF V) :
    List (MvPolynomial V R) :=
  φ.map (Clause.toBoolPoly R)

variable {R : Type*} [CommRing R]

/-- The truth polynomial of the negated literal is `1` minus the truth polynomial. -/
theorem Literal.truthPoly_negate (l : Literal V) :
    Literal.truthPoly R l.negate = 1 - l.truthPoly R := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [Literal.truthPoly, Std.Sat.Literal.negate]

/-- The empty clause has polynomial `1`. -/
@[simp] theorem Clause.toBoolPoly_nil : Clause.toBoolPoly R ([] : Clause V) = 1 := by
  simp [Clause.toBoolPoly]

/-- Adding a literal `l` multiplies the clause polynomial by `1 - truthPoly l`. -/
@[simp] theorem Clause.toBoolPoly_cons (l : Literal V) (c : Clause V) :
    Clause.toBoolPoly R (l :: c) = (1 - l.truthPoly R) * c.toBoolPoly R := by
  simp [Clause.toBoolPoly, Literal.truthPoly_negate]

/-- At a point of the cube, the truth polynomial of a literal is the truth value used by
`Cslib.Logic.PL.Clause.eval_toPoly`. -/
theorem Literal.eval_truthPoly (x : V → Bool) (l : Literal V) :
    MvPolynomial.eval (bitPoint x) (l.truthPoly R) = Literal.toPolyAssignment R x l := by
  obtain ⟨v, b⟩ := l
  cases b <;> cases hx : x v <;> simp [Literal.truthPoly, Literal.toPolyAssignment, hx, bitVal]

/-- At a point of the cube, the clause polynomial is `0` when the clause is satisfied and `1`
when it is falsified. -/
theorem Clause.eval_toBoolPoly (x : V → Bool) (c : Clause V) :
    MvPolynomial.eval (bitPoint x) (c.toBoolPoly R) = if c.eval x then 0 else 1 := by
  refine (eval₂Hom_bind₁ (RingHom.id R) (bitPoint x) (Literal.truthPoly R) (c.toPoly R)).trans ?_
  have h : (fun l => eval₂Hom (RingHom.id R) (bitPoint x) (Literal.truthPoly R l)) =
      Literal.toPolyAssignment R x :=
    funext fun l => Literal.eval_truthPoly x l
  rw [h]
  exact Clause.eval_toPoly c x

/-- A literal's truth polynomial has total degree at most one. -/
theorem Literal.totalDegree_truthPoly_le (l : Literal V) : (l.truthPoly R).totalDegree ≤ 1 := by
  have hX : (X l.1 : MvPolynomial V R).totalDegree ≤ 1 :=
    (totalDegree_monomial_le _ _).trans (by simp)
  unfold Literal.truthPoly
  split_ifs
  · exact hX
  · exact (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_one]; omega) hX)

/-- A clause polynomial has total degree at most the number of literals. -/
theorem Clause.totalDegree_toBoolPoly_le (c : Clause V) :
    (c.toBoolPoly R).totalDegree ≤ c.length := by
  induction c with
  | nil => simp
  | cons l c ih =>
    rw [Clause.toBoolPoly_cons, List.length_cons]
    have h1 : (1 - l.truthPoly R).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_one]; omega)
        (Literal.totalDegree_truthPoly_le l))
    have := totalDegree_mul (1 - l.truthPoly R) (Clause.toBoolPoly R c)
    omega

/-- The Boolean solutions of the clause polynomials of a formula are its satisfying
assignments. -/
theorem CNF.isBoolSolution_toBoolPolys_iff [Nontrivial R] (φ : CNF V) (x : V → Bool) :
    IsBoolSolution (φ.toBoolPolys R) x ↔ φ.eval x = true := by
  simp only [IsBoolSolution, CNF.toBoolPolys, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Clause.eval_toBoolPoly, CNF.eval_eq_true_iff]
  refine forall₂_congr fun c _ => ?_
  cases Clause.eval x c <;> simp

variable [Fintype V]

/-- **Soundness for CNF formulas.** A Nullstellensatz refutation of the clause polynomials with
the Boolean axioms, over a nontrivial commutative ring, certifies that the formula is
unsatisfiable. -/
theorem CNF.not_satisfiable_of_ns [Nontrivial R] {φ : CNF V}
    {P : Fin (φ.toBoolPolys R ++ boolAxioms V R).length → MvPolynomial V R}
    (h : NS.IsProof (φ.toBoolPolys R ++ boolAxioms V R) P 1) : ¬ φ.Satisfiable :=
  fun ⟨x, hx⟩ => h.not_isBoolSolution x ((φ.isBoolSolution_toBoolPolys_iff x).2 hx)

/-- **Soundness for CNF formulas.** A polynomial calculus refutation of the clause polynomials
with the Boolean axioms, over a nontrivial commutative ring, certifies that the formula is
unsatisfiable. -/
theorem CNF.not_satisfiable_of_pc [Nontrivial R] {φ : CNF V} {ls : List (MvPolynomial V R)}
    (h : PC.IsProof (φ.toBoolPolys R ++ boolAxioms V R) ls) (h1 : 1 ∈ ls) : ¬ φ.Satisfiable :=
  fun ⟨x, hx⟩ => h.not_isBoolSolution h1 x ((φ.isBoolSolution_toBoolPolys_iff x).2 hx)

variable {K : Type*} [Field K]

omit [Fintype V] in
private theorem CNF.totalDegree_le_of_mem_toBoolPolys {φ : CNF V} {w : ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ w) : ∀ f ∈ φ.toBoolPolys K, f.totalDegree ≤ w := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
  exact (Clause.totalDegree_toBoolPoly_le c).trans (hw c hc)

/-- Over a field, a formula in the variables of a finite type `V` whose clauses have at most `w`
literals has a Nullstellensatz refutation of degree at most `card V + w` exactly when it is
unsatisfiable. -/
theorem CNF.ns_refutableInDegree_iff {φ : CNF V} {w : ℕ} (hw : ∀ c ∈ φ, c.length ≤ w) :
    NS.RefutableInDegree (φ.toBoolPolys K ++ boolAxioms V K) (Fintype.card V + w) ↔
      ¬ φ.Satisfiable := by
  rw [NS.refutableInDegree_iff (totalDegree_le_of_mem_toBoolPolys hw)]
  simp only [CNF.isBoolSolution_toBoolPolys_iff, CNF.Satisfiable, not_exists]

/-- Over a field, a formula in the variables of a finite type `V` whose clauses have at most `w`
literals has a polynomial calculus refutation of degree at most `card V + w` exactly when it is
unsatisfiable. -/
theorem CNF.pc_refutableInDegree_iff {φ : CNF V} {w : ℕ} (hw : ∀ c ∈ φ, c.length ≤ w) :
    PC.RefutableInDegree (φ.toBoolPolys K ++ boolAxioms V K) (Fintype.card V + w) ↔
      ¬ φ.Satisfiable := by
  rw [PC.refutableInDegree_iff (totalDegree_le_of_mem_toBoolPolys hw)]
  simp only [CNF.isBoolSolution_toBoolPolys_iff, CNF.Satisfiable, not_exists]

end Cslib.Logic.PL
