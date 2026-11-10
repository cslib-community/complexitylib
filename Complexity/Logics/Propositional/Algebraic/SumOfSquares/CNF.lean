/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Algebraic.SumOfSquares.Positivstellensatz
public import Complexity.Logics.Propositional.CuttingPlanes
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.LinearCombination

/-!
# Positivstellensatz refutations of CNF formulas

A CNF formula `φ` becomes polynomial constraints through its cutting-planes inequalities: the
clause `C` gives `∑_{v ∈ C} xᵥ + ∑_{¬v ∈ C} (1 - xᵥ) - 1 ≥ 0` (`Clause.toIneq`, through
`Ineq.toPoly`, which sends `∑ᵥ aᵥ xᵥ ≥ b` to `∑ᵥ aᵥ xᵥ - b`), and every variable gives the box
constraints `xᵥ ≥ 0` and `1 - xᵥ ≥ 0` (`SOS.Psatz.cnfIneqs`). The Boolean axioms `xᵥ ² - xᵥ = 0`
are the equations (`SOS.Psatz.booleanAxioms`). This is the translation of [Grigoriev, Hirsch and
Pasechnik, Section 2.3, inequalities (2.4)–(2.6)][GrigorievHirschPasechnik2002] with the Boolean
axioms as equations.

Over a strictly ordered ring the common solutions of these constraints are exactly the satisfying
assignments (`SOS.Psatz.exists_feasible_iff`), so a Positivstellensatz refutation shows that `φ` is
unsatisfiable (`SOS.Psatz.not_satisfiable_of_refutableInDegree`). In degree at most `1` the
Boolean axioms impose nothing, since every nonzero multiple of `xᵥ ² - xᵥ` has degree at least `2`
(`SOS.Psatz.eq_zero_of_totalDegree_mul_le_one`). A point of the box that satisfies the clause
inequalities, fractional or not, is then a pseudo-expectation of degree `1`
(`SOS.Psatz.degreeOnePseudoExpectation`), which rules out refutations of degree `1`
(`SOS.Psatz.not_refutableInDegree_one_of_eval_nonneg`).

## Main definitions

* `Cslib.Logic.PL.Ineq.toPoly`: the polynomial `∑ᵥ aᵥ xᵥ - b` of `∑ᵥ aᵥ xᵥ ≥ b`.
* `Cslib.Logic.PL.SOS.Psatz.cnfIneqs`: the inequality constraints of a CNF formula.
* `Cslib.Logic.PL.SOS.Psatz.booleanAxioms`: the Boolean axioms `xᵥ ² - xᵥ = 0`.
* `Cslib.Logic.PL.SOS.Psatz.degreeOnePseudoExpectation`: the degree-`1` pseudo-expectation of a
  fractional point.

## Main results

* `Cslib.Logic.PL.SOS.Psatz.exists_feasible_iff`: the constraints of `φ` have a common solution
  exactly when `φ` is satisfiable.
* `Cslib.Logic.PL.SOS.Psatz.not_satisfiable_of_refutableInDegree`: soundness for CNF formulas.
* `Cslib.Logic.PL.SOS.Psatz.not_refutableInDegree_one_of_eval_nonneg`: a fractional point that
  satisfies the inequality constraints rules out refutations of degree `1`.

## References

* [D. Grigoriev, E. A. Hirsch, D. V. Pasechnik, *Complexity of semialgebraic proofs*]
  [GrigorievHirschPasechnik2002]
-/

public section

namespace Cslib.Logic.PL

open MvPolynomial Finset

namespace Ineq

variable {V R : Type*} [CommRing R]

/-- The polynomial `∑ᵥ aᵥ Xᵥ - b` of the inequality `∑ᵥ aᵥ xᵥ ≥ b`. -/
noncomputable def toPoly (I : Ineq V) : MvPolynomial V R :=
  (I.coeff.sum fun v a => C (a : R) * X v) - C (I.bound : R)

theorem toPoly_add (I J : Ineq V) : (I + J).toPoly (R := R) = I.toPoly + J.toPoly := by
  simp only [toPoly, coeff_add, bound_add, Int.cast_add, map_add]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  ring

/-- `Ineq.toPoly` as an additive homomorphism. -/
noncomputable def toPolyHom : Ineq V →+ MvPolynomial V R where
  toFun := toPoly
  map_zero' := by simp [toPoly]
  map_add' := toPoly_add

theorem toPoly_sum {ι : Type*} (s : Finset ι) (f : ι → Ineq V) :
    (∑ i ∈ s, f i).toPoly (R := R) = ∑ i ∈ s, (f i).toPoly :=
  map_sum (toPolyHom (V := V) (R := R)) f s

@[simp] theorem toPoly_contra : (contra : Ineq V).toPoly (R := R) = -1 := by
  simp [toPoly]

@[simp] theorem toPoly_nonneg (v : V) : (nonneg v).toPoly (R := R) = X v := by
  simp [toPoly]

@[simp] theorem toPoly_leOne (v : V) : (leOne v).toPoly (R := R) = 1 - X v := by
  rw [toPoly, coeff_leOne, bound_leOne, Finsupp.sum_single_index (by simp)]
  simp only [Int.cast_neg, Int.cast_one, map_neg, map_one]
  ring

/-- The polynomial of an inequality is affine. -/
theorem totalDegree_toPoly_le (I : Ineq V) : (I.toPoly (R := R)).totalDegree ≤ 1 := by
  rw [toPoly]
  refine (totalDegree_sub _ _).trans (max_le ?_ (by rw [totalDegree_C]; omega))
  refine totalDegree_finsetSum_le fun v _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, X]
  exact (totalDegree_monomial_le _ _).trans (by simp)

/-- At a `0/1` point, the polynomial of an inequality is its slack `lhs - bound`. -/
theorem eval_toPoly_toInt (σ : V → Bool) (I : Ineq V) :
    eval (fun v => ((σ v).toInt : R)) (I.toPoly (R := R)) = ((I.lhs σ - I.bound : ℤ) : R) := by
  obtain ⟨c, b⟩ := I
  induction c using Finsupp.induction_linear generalizing b with
  | zero =>
    have h0 : (⟨0, b⟩ : Ineq V).lhs σ = 0 := by
      rw [lhs_of_coeff_eq_smul σ (J := 0) (c := 0) (by simp), zero_mul]
    simp [toPoly, h0]
  | add f g hf hg =>
    have hsplit : (⟨f + g, b⟩ : Ineq V) = ⟨f, b⟩ + ⟨g, 0⟩ := by
      ext <;> simp
    rw [hsplit, toPoly_add, map_add, hf, hg, lhs_add, bound_add]
    push_cast
    ring
  | single v a =>
    simp [toPoly]

/-- Over a strictly ordered ring, an inequality holds at a `0/1` point exactly when its
polynomial is nonnegative there. -/
theorem holds_iff_eval_toPoly_nonneg [LinearOrder R] [IsStrictOrderedRing R] (σ : V → Bool)
    (I : Ineq V) :
    I.Holds σ ↔ 0 ≤ eval (fun v => ((σ v).toInt : R)) (I.toPoly (R := R)) := by
  rw [eval_toPoly_toInt, Int.cast_nonneg_iff, sub_nonneg, Holds]

end Ineq

/-- The polynomial of the inequality of a clause: `∑_{v ∈ C} Xᵥ + ∑_{¬v ∈ C} (1 - Xᵥ) - 1`, over
the distinct literals of `C`. -/
theorem Clause.toPoly_toIneq {V R : Type*} [CommRing R] [DecidableEq V] (c : Clause V) :
    (c.toIneq.toPoly : MvPolynomial V R) =
      ∑ l ∈ c.toFinset, (bif l.2 then X l.1 else 1 - X l.1) - 1 := by
  rw [Clause.toIneq, Ineq.toPoly_add, Ineq.toPoly_contra, Ineq.toPoly_sum, neg_add_eq_sub]
  refine congrArg (· - 1) (Finset.sum_congr rfl fun l _ => ?_)
  rcases l with ⟨v, _ | _⟩ <;> simp

namespace SOS.Psatz

variable {V R : Type*} [CommRing R] [DecidableEq V]

/-- The **inequality constraints of a CNF formula**: the polynomials of its clause inequalities and
the box constraints `Xᵥ ≥ 0`, `1 - Xᵥ ≥ 0`. -/
noncomputable def cnfIneqs (φ : CNF V) : Set (MvPolynomial V R) :=
  Ineq.toPoly '' (φ.toIneqs ∪ Set.range Ineq.nonneg ∪ Set.range Ineq.leOne)

/-- The **Boolean axioms** `Xᵥ ² - Xᵥ = 0`. -/
noncomputable def booleanAxioms (V R : Type*) [CommRing R] : Set (MvPolynomial V R) :=
  Set.range fun v => X v ^ 2 - X v

theorem toPoly_mem_cnfIneqs {φ : CNF V} {c : Clause V} (hc : c ∈ φ) :
    (c.toIneq.toPoly : MvPolynomial V R) ∈ cnfIneqs φ :=
  ⟨_, Or.inl (Or.inl (CNF.toIneq_mem_toIneqs hc)), rfl⟩

theorem X_mem_cnfIneqs (φ : CNF V) (v : V) : (X v : MvPolynomial V R) ∈ cnfIneqs φ :=
  ⟨_, Or.inl (Or.inr ⟨v, rfl⟩), Ineq.toPoly_nonneg v⟩

theorem one_sub_X_mem_cnfIneqs (φ : CNF V) (v : V) :
    (1 - X v : MvPolynomial V R) ∈ cnfIneqs φ :=
  ⟨_, Or.inr ⟨v, rfl⟩, Ineq.toPoly_leOne v⟩

/-- A property holds on the inequality constraints of `φ` exactly when it holds on the clause
polynomials and the box constraints. -/
theorem forall_mem_cnfIneqs_iff {φ : CNF V} {p : MvPolynomial V R → Prop} :
    (∀ f ∈ cnfIneqs φ, p f) ↔
      (∀ c ∈ φ, p c.toIneq.toPoly) ∧ (∀ v, p (X v)) ∧ ∀ v, p (1 - X v) := by
  constructor
  · intro h
    exact ⟨fun c hc => h _ (toPoly_mem_cnfIneqs hc), fun v => h _ (X_mem_cnfIneqs φ v),
      fun v => h _ (one_sub_X_mem_cnfIneqs φ v)⟩
  · rintro ⟨hc, hX, h1⟩ _ ⟨I, (⟨c, hc', rfl⟩ | ⟨v, rfl⟩) | ⟨v, rfl⟩, rfl⟩
    · exact hc c hc'
    · rw [Ineq.toPoly_nonneg]
      exact hX v
    · rw [Ineq.toPoly_leOne]
      exact h1 v

omit [DecidableEq V] in
theorem mem_booleanAxioms {g : MvPolynomial V R} :
    g ∈ booleanAxioms V R ↔ ∃ v, X v ^ 2 - X v = g :=
  Iff.rfl

omit [DecidableEq V] in
theorem X_sq_sub_X_mem_booleanAxioms (v : V) :
    (X v ^ 2 - X v : MvPolynomial V R) ∈ booleanAxioms V R :=
  ⟨v, rfl⟩

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- **The encoding is faithful**: over a strictly ordered ring, the constraints of `φ` have a common
solution exactly when `φ` is satisfiable. -/
theorem exists_feasible_iff (φ : CNF V) :
    (∃ x : V → R, (∀ f ∈ cnfIneqs φ, 0 ≤ eval x f) ∧ ∀ g ∈ booleanAxioms V R, eval x g = 0) ↔
      φ.Satisfiable := by
  constructor
  · rintro ⟨x, hI, hE⟩
    have h01 (v : V) : x v = 0 ∨ x v = 1 := by
      have := hE _ (X_sq_sub_X_mem_booleanAxioms v)
      simp only [map_sub, map_pow, eval_X] at this
      have : x v * (x v - 1) = 0 := by linear_combination this
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · exact Or.inr (by linear_combination h)
    let σ : V → Bool := fun v => decide (x v = 1)
    have hx : x = fun v => ((σ v).toInt : R) := by
      funext v
      rcases h01 v with h | h <;> simp [σ, h]
    refine ⟨σ, (CNF.holds_toIneqs_iff σ φ).1 fun I hI' => ?_⟩
    rw [Ineq.holds_iff_eval_toPoly_nonneg (R := R), ← hx]
    exact hI _ ⟨I, Or.inl (Or.inl hI'), rfl⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨fun v => ((σ v).toInt : R), ?_, ?_⟩
    · rintro _ ⟨I, hI', rfl⟩
      rw [← Ineq.holds_iff_eval_toPoly_nonneg]
      rcases hI' with (hI' | ⟨v, rfl⟩) | ⟨v, rfl⟩
      · exact (CNF.holds_toIneqs_iff σ φ).2 hσ I hI'
      · exact Ineq.holds_nonneg σ v
      · exact Ineq.holds_leOne σ v
    · rintro _ ⟨v, rfl⟩
      cases σ v <;> simp [Bool.toInt]

/-- **Soundness for CNF formulas**: a CNF formula whose constraints have a Positivstellensatz
refutation is unsatisfiable. -/
theorem not_satisfiable_of_refutableInDegree {φ : CNF V} {d : ℕ}
    (h : RefutableInDegree (cnfIneqs φ) (booleanAxioms V R) d) : ¬ φ.Satisfiable := by
  rw [← exists_feasible_iff (R := R)]
  exact h.not_exists_eval

omit [DecidableEq V] in
/-- In degree at most `1` the Boolean axioms impose nothing: every multiple of `Xᵥ ² - Xᵥ` of
total degree at most `1` is zero. -/
theorem eq_zero_of_totalDegree_mul_le_one {g q : MvPolynomial V R} (hg : g ∈ booleanAxioms V R)
    (hq : (q * g).totalDegree ≤ 1) : q * g = 0 := by
  obtain ⟨v, rfl⟩ := hg
  by_contra hne
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hne
  have hg0 : (X v ^ 2 - X v : MvPolynomial V R) ≠ 0 := by
    rintro h
    simp [h] at hne
  have hdeg : (X v ^ 2 - X v : MvPolynomial V R).totalDegree = 2 := by
    rw [sub_eq_add_neg, totalDegree_add_eq_left_of_totalDegree_lt] <;>
      simp [totalDegree_X_pow, totalDegree_neg, totalDegree_X]
  rw [totalDegree_mul_of_isDomain hq0 hg0, hdeg] at hq
  omega

/-- **The degree-`1` pseudo-expectation of a fractional point**: evaluation at a point, not
necessarily `0/1`, that satisfies the inequality constraints of `φ` is a pseudo-expectation of
degree `1`, since in degree `1` the Boolean axioms impose nothing. -/
noncomputable def degreeOnePseudoExpectation {φ : CNF V} (x : V → R)
    (hx : ∀ f ∈ cnfIneqs φ, 0 ≤ eval x f) :
    PseudoExpectation (cnfIneqs φ) (booleanAxioms V R) 1 :=
  PseudoExpectation.ofEval x hx fun _ hg _ hq => by
    rw [eq_zero_of_totalDegree_mul_le_one hg hq, map_zero]

/-- The pseudo-expectation `degreeOnePseudoExpectation x hx` is evaluation at `x`. -/
@[simp] theorem degreeOnePseudoExpectation_apply {φ : CNF V} (x : V → R)
    (hx : ∀ f ∈ cnfIneqs φ, 0 ≤ eval x f) (p : MvPolynomial V R) :
    (degreeOnePseudoExpectation x hx).toLinearMap p = eval x p := by
  simp [degreeOnePseudoExpectation]

/-- **Degree-`1` lower bounds from fractional points**: if a point, not necessarily `0/1`,
satisfies the inequality constraints of `φ`, then `φ` has no Positivstellensatz refutation of degree
at most `1`. -/
theorem not_refutableInDegree_one_of_eval_nonneg {φ : CNF V} (x : V → R)
    (hx : ∀ f ∈ cnfIneqs φ, 0 ≤ eval x f) :
    ¬ RefutableInDegree (cnfIneqs φ) (booleanAxioms V R) 1 :=
  (degreeOnePseudoExpectation x hx).not_refutableInDegree

end SOS.Psatz

end Cslib.Logic.PL
