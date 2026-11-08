/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Algebraic.CNF.Boolean
public import Complexity.Logics.Propositional.CNF.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Clause polynomials of parity constraints

The clause `Cslib.Logic.PL.Clause.exclude B y`, which excludes the values of `y` on `B`, has clause
polynomial `∏_{i ∈ B} [x_i = y_i]`, where `[x_i = 1]` is `X i` and `[x_i = 0]` is `1 - X i`
(`Cslib.Logic.PL.Clause.toBoolPoly_exclude`). Over a domain its total degree is exactly `#B`
(`Cslib.Logic.PL.Clause.totalDegree_toBoolPoly_exclude`).

Over a ring of characteristic `2`, the clause polynomials of the parity constraint
`Cslib.Logic.PL.CNF.parityOnEq B c` add up to `[c = 1] + ∑_{i ∈ B} X i`
(`Cslib.Logic.PL.CNF.sum_toBoolPoly_parityOnEq`): both sides are the indicator of
`parityOn B x ≠ c` on the Boolean cube. This is the identity behind the degree-`Δ` Nullstellensatz
refutations of Tseitin formulas in characteristic `2`.

## Main results

* `Cslib.Logic.PL.Clause.toBoolPoly_exclude`,
  `Cslib.Logic.PL.Clause.totalDegree_toBoolPoly_exclude`: the polynomial of the clause excluding
  the values of `y` on `B`, and its degree.
* `Cslib.Logic.PL.CNF.sum_toBoolPoly_parityOnEq`: in characteristic `2`, the clause polynomials of a
  parity constraint add up to `[c = 1] + ∑_{i ∈ B} X i`.
-/

public section

namespace Cslib.Logic.PL

open Finset MvPolynomial

variable {ι R : Type*}

/-- The clause excluding the values of `y` on `B` has polynomial `∏_{i ∈ B} [x_i = y_i]`, where
`[x_i = 1]` is `X i` and `[x_i = 0]` is `1 - X i`. -/
theorem Clause.toBoolPoly_exclude [CommRing R] (B : Finset ι) (y : ι → Bool) :
    (Clause.exclude B y).toBoolPoly R =
      ∏ i ∈ B, (if y i then X i else 1 - X i : MvPolynomial ι R) := by
  have h (l : List ι) : Clause.toBoolPoly R (l.map fun i => (i, !y i)) =
      (l.map fun i => (if y i then X i else 1 - X i : MvPolynomial ι R)).prod := by
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.map_cons, Clause.toBoolPoly_cons, ih, List.map_cons, List.prod_cons]
      cases y i <;> simp [Literal.truthPoly]
  rw [Clause.exclude, h, prod_map_toList]

private theorem totalDegree_one_sub_X [CommRing R] [Nontrivial R] (i : ι) :
    (1 - X i : MvPolynomial ι R).totalDegree = 1 := by
  classical
  rw [← totalDegree_neg, neg_sub]
  refine le_antisymm ((totalDegree_sub_C_le (X i) 1).trans_eq (totalDegree_X i)) ?_
  have hi : (Finsupp.single i 1 : ι →₀ ℕ) ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
  have h : Finsupp.single i 1 ∈ (X i - 1 : MvPolynomial ι R).support := by
    simp [mem_support_iff, coeff_X, coeff_one, hi.symm]
  simpa using le_totalDegree h

private theorem totalDegree_ite [CommRing R] [Nontrivial R] (y : ι → Bool) (i : ι) :
    (if y i then X i else 1 - X i : MvPolynomial ι R).totalDegree = 1 := by
  cases y i
  · exact totalDegree_one_sub_X i
  · exact totalDegree_X i

/-- Over a domain, the clause excluding the values of `y` on `B` has polynomial of total degree
exactly `#B`. -/
theorem Clause.totalDegree_toBoolPoly_exclude [CommRing R] [IsDomain R] (B : Finset ι)
    (y : ι → Bool) : ((Clause.exclude B y).toBoolPoly R).totalDegree = #B := by
  classical
  rw [Clause.toBoolPoly_exclude]
  have hne (j : ι) : (if y j then X j else 1 - X j : MvPolynomial ι R) ≠ 0 := fun h => by
    have := totalDegree_ite (R := R) y j
    rw [h, totalDegree_zero] at this
    exact zero_ne_one this
  induction B using Finset.induction_on with
  | empty => simp
  | insert i B hi ih =>
    rw [prod_insert hi, totalDegree_mul_of_isDomain (hne i) (prod_ne_zero_iff.2 fun j _ => hne j),
      totalDegree_ite, ih, card_insert_of_notMem hi, add_comm]

variable [DecidableEq ι]

/-- The sum of the polynomials of the clauses excluding the assignments `A ⊆ B` of parity other
than `c`. -/
private noncomputable def parityClauseSum (R : Type*) [CommRing R] (B : Finset ι) (c : Bool) :
    MvPolynomial ι R :=
  ∑ A ∈ B.powerset with parityOn B (fun i => decide (i ∈ A)) ≠ c,
    ∏ i ∈ B, (if i ∈ A then X i else 1 - X i)

/-- Adding a new variable `j` to `B`: the assignments not setting `j` contribute `1 - X j` times
the old sum, and those setting `j` contribute `X j` times the old sum for the other parity. -/
private theorem parityClauseSum_insert [CommRing R] {j : ι} {B : Finset ι} (hj : j ∉ B)
    (c : Bool) :
    parityClauseSum R (insert j B) c =
      (1 - X j) * parityClauseSum R B c + X j * parityClauseSum R B (!c) := by
  rw [parityClauseSum, parityClauseSum, parityClauseSum, sum_filter, sum_filter, sum_filter,
    sum_powerset_insert hj, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun A hA => ?_
    have hjA : j ∉ A := fun h => hj (mem_powerset.1 hA h)
    rw [parityOn_insert hj, decide_eq_false hjA, Bool.false_xor, prod_insert hj, ite_eq_right hjA]
    split_ifs <;> ring
  · refine sum_congr rfl fun A hA => ?_
    have hjA : j ∉ A := fun h => hj (mem_powerset.1 hA h)
    have hmem : ∀ i ∈ B, (i ∈ insert j A ↔ i ∈ A) := fun i hi => by
      rw [mem_insert, or_iff_right fun h : i = j => hj (h ▸ hi)]
    have hpar : parityOn B (fun i => decide (i ∈ insert j A)) =
        parityOn B (fun i => decide (i ∈ A)) :=
      parityOn_congr fun i hi => by simp only [hmem i hi]
    have hprod : ∏ i ∈ B, (if i ∈ insert j A then X i else 1 - X i : MvPolynomial ι R) =
        ∏ i ∈ B, (if i ∈ A then X i else 1 - X i) :=
      prod_congr rfl fun i hi => by simp only [hmem i hi]
    rw [parityOn_insert hj, decide_eq_true (mem_insert_self j A), Bool.true_xor, hpar,
      prod_insert hj, ite_eq_left (mem_insert_self j A), hprod]
    have hneg (a : Bool) : ((!a) ≠ c) ↔ (a ≠ !c) := by cases a <;> cases c <;> decide
    by_cases h : parityOn B (fun i => decide (i ∈ A)) ≠ !c
    · rw [ite_eq_left ((hneg _).2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((hneg _).1 h')), ite_eq_right h, mul_zero]

/-- In characteristic `2`, the polynomials of the clauses excluding the assignments `A ⊆ B` of
parity other than `c` add up to `[c = 1] + ∑_{i ∈ B} X i`. -/
private theorem parityClauseSum_eq [CommRing R] [CharP R 2] (B : Finset ι) (c : Bool) :
    parityClauseSum R B c = (if c then 1 else 0) + ∑ i ∈ B, X i := by
  have h2 : (2 : MvPolynomial ι R) = 0 := CharTwo.two_eq_zero
  induction B using Finset.induction_on generalizing c with
  | empty =>
    cases c <;> simp [parityClauseSum]
  | insert j B hj ih =>
    rw [parityClauseSum_insert hj, ih, ih, sum_insert hj]
    cases c
    · simp only [Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
      ring
    · simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
      linear_combination (-X j) * h2

/-- In characteristic `2`, **the clause polynomials of a parity constraint add up to
`[c = 1] + ∑_{i ∈ B} X i`**: both sides are the indicator of `parityOn B x ≠ c` on the Boolean
cube. -/
theorem CNF.sum_toBoolPoly_parityOnEq [CommRing R] [CharP R 2] (B : Finset ι) (c : Bool) :
    ∑ A ∈ B.powerset with parityOn B (fun i => decide (i ∈ A)) ≠ c,
        (Clause.exclude B fun i => decide (i ∈ A)).toBoolPoly R =
      (if c then 1 else 0) + ∑ i ∈ B, X i := by
  rw [← parityClauseSum_eq]
  refine sum_congr rfl fun A _ => ?_
  rw [Clause.toBoolPoly_exclude]
  exact prod_congr rfl fun i _ => by simp only [decide_eq_true_eq]

end Cslib.Logic.PL
