/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.CNF
public import CslibFrontier.Logics.Propositional.Pigeonhole
import CslibFrontier.Logics.Propositional.CuttingPlanes.Pigeonhole
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Degree-`2` Positivstellensatz refutations of the pigeonhole principle

With the cutting-planes inequalities of `PHP^m_n` (`SOS.Psatz.cnfIneqs`), the pigeon clauses give
`Pᵢ = ∑ⱼ xᵢⱼ - 1 ≥ 0` and the hole clauses give `Hᵢᵢ'ⱼ = 1 - xᵢⱼ - xᵢ'ⱼ ≥ 0`. For `m > n` the
identity

`∑ᵢ Pᵢ + ∑ⱼ (1 - ∑ᵢ xᵢⱼ) ² + ∑ⱼ ∑_{i ≠ i'} xᵢⱼ Hᵢᵢ'ⱼ + (m - n - 1) · 1 ²
  + (m - 2) ∑ᵢⱼ (xᵢⱼ ² - xᵢⱼ) = -1`

is a Positivstellensatz refutation of degree `2` with the Boolean axioms
(`SOS.Psatz.refutableInDegree_two_pigeonhole`). Each summand `xᵢⱼ Hᵢᵢ'ⱼ` multiplies two inequality
constraints, a box constraint and a hole inequality. For `m = n + 1` this is the identity of
[Grigoriev, Hirsch and Pasechnik, Example 2.1][GrigorievHirschPasechnik2002], stated there as a
static `LS₊` proof. For `m > n + 1` the extra summand `(m - n - 1) · 1 ²` is added. All coefficients
are integers, so the refutation exists over every strictly ordered commutative ring, `ℤ` included.

Degree `2` is optimal for `n ≥ 2`: over a strictly ordered field the fractional point
`xᵢⱼ = 1 / n` satisfies every inequality (`Pᵢ = 0`, `Hᵢᵢ'ⱼ = 1 - 2 / n ≥ 0`), so there is no
refutation of degree `1` (`SOS.Psatz.eval_inv_nonneg_of_mem_cnfIneqs_pigeonhole`,
`SOS.Psatz.not_refutableInDegree_one_pigeonhole`).
`SOS.Psatz.refutableInDegree_pigeonhole_iff` combines both with soundness: for `n ≥ 2`, `PHP^m_n`
has a refutation of degree at most `d` exactly when `n < m` and `2 ≤ d`.

For comparison, and as a separate fact about a different proof system, resolution refutations of
`PHP^{n+1}_n` have size at least `2 ^ (n / 24)` (`CNF.two_pow_le_of_refutableInSize_pigeonhole`).
This module bounds degree only. It makes no claim about the size of Positivstellensatz refutations
or about simulations between the two systems.

## Main results

* `Cslib.Logic.PL.SOS.Psatz.refutableInDegree_two_pigeonhole`: for `m > n`, `PHP^m_n` has a
  Positivstellensatz refutation of degree `2`.
* `Cslib.Logic.PL.SOS.Psatz.eval_inv_nonneg_of_mem_cnfIneqs_pigeonhole`,
  `Cslib.Logic.PL.SOS.Psatz.not_refutableInDegree_one_pigeonhole`: for `n ≥ 2`, the point
  `xᵢⱼ = 1 / n` satisfies the inequalities, so there is no refutation of degree `1`.
* `Cslib.Logic.PL.SOS.Psatz.refutableInDegree_pigeonhole_iff`: for `n ≥ 2`, refutability in degree
  `d` is `n < m ∧ 2 ≤ d`.

## References

* [D. Grigoriev, E. A. Hirsch, D. V. Pasechnik, *Complexity of semialgebraic proofs*]
  [GrigorievHirschPasechnik2002]
-/

public section

namespace Cslib.Logic.PL.SOS.Psatz

open MvPolynomial Finset CNF Ineq

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- The polynomial of the pigeon clause of pigeon `i`: `∑ⱼ Xᵢⱼ - 1`. -/
theorem toPoly_toIneq_pigeonClause (i : Fin m) :
    ((pigeonClause n i).toIneq.toPoly : MvPolynomial (Fin m × Fin n) R) = ∑ j, X (i, j) - 1 := by
  rw [toIneq_pigeonClause, toPoly_add, toPoly_contra, toPoly_sum]
  simp only [toPoly_nonneg]
  ring

/-- The polynomial of the hole clause of pigeons `i ≠ i'` and hole `j`: `1 - Xᵢⱼ - Xᵢ'ⱼ`. -/
theorem toPoly_toIneq_holeClause {i i' : Fin m} (hii' : i ≠ i') (j : Fin n) :
    ((holeClause i i' j).toIneq.toPoly : MvPolynomial (Fin m × Fin n) R) =
      1 - X (i, j) - X (i', j) := by
  rw [toIneq_holeClause hii', toPoly_add, toPoly_add, toPoly_contra, toPoly_leOne, toPoly_leOne]
  ring

theorem pigeonPoly_mem_cnfIneqs (i : Fin m) :
    (∑ j, X (i, j) - 1 : MvPolynomial (Fin m × Fin n) R) ∈ cnfIneqs (pigeonhole m n) := by
  rw [← toPoly_toIneq_pigeonClause]
  exact toPoly_mem_cnfIneqs (mem_pigeonhole.2 (Or.inl ⟨i, rfl⟩))

theorem holePoly_mem_cnfIneqs {i i' : Fin m} (hii' : i ≠ i') (j : Fin n) :
    (1 - X (i, j) - X (i', j) : MvPolynomial (Fin m × Fin n) R) ∈ cnfIneqs (pigeonhole m n) := by
  rcases lt_or_gt_of_ne hii' with h | h
  · rw [← toPoly_toIneq_holeClause hii']
    exact toPoly_mem_cnfIneqs (mem_pigeonhole.2 (Or.inr ⟨i, i', j, h, rfl⟩))
  · rw [show (1 - X (i, j) - X (i', j) : MvPolynomial (Fin m × Fin n) R) =
      1 - X (i', j) - X (i, j) by ring, ← toPoly_toIneq_holeClause hii'.symm]
    exact toPoly_mem_cnfIneqs (mem_pigeonhole.2 (Or.inr ⟨i', i, j, h, rfl⟩))

/-- The identity for one hole, in any commutative ring:
`∑_{i ≠ i'} xᵢ (1 - xᵢ - xᵢ') + (1 - ∑ᵢ xᵢ) ² + (m - 2) ∑ᵢ (xᵢ ² - xᵢ) = 1 - ∑ᵢ xᵢ`. -/
private theorem sum_hole_identity {A : Type*} [CommRing A] (x : Fin m → A) :
    ∑ i, ∑ i', (if i = i' then 0 else x i * (1 - x i - x i')) + (1 - ∑ i, x i) ^ 2 +
      ((m : A) - 2) * ∑ i, (x i ^ 2 - x i) = 1 - ∑ i, x i := by
  have hin (i : Fin m) : ∑ i', (if i = i' then 0 else x i * (1 - x i - x i')) =
      x i * ((m : A) * (1 - x i) - ∑ i', x i') - x i * (1 - 2 * x i) := by
    rw [← Finset.sum_erase_add _ _ (mem_univ i), ite_eq_left rfl, add_zero,
      Finset.sum_congr rfl fun i' hi' => ite_eq_right (Ne.symm (ne_of_mem_erase hi')),
      Finset.sum_erase_eq_sub (mem_univ i), ← mul_sum]
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  have key : ∑ i, (x i * ((m : A) * (1 - x i) - ∑ i', x i') - x i * (1 - 2 * x i)) +
      ((m : A) - 2) * ∑ i, (x i ^ 2 - x i) = ∑ i, x i - (∑ i', x i') * ∑ i, x i := by
    rw [mul_sum, ← sum_add_distrib, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  simp only [hin]
  linear_combination key

private theorem X_ne_holePoly [Nontrivial R] (i i' : Fin m) (j : Fin n) :
    (X (i, j) : MvPolynomial (Fin m × Fin n) R) ≠ 1 - X (i, j) - X (i', j) := fun h => by
  have := congrArg constantCoeff h
  simp at this

/-- The summands of the refutation: `1 · 1 ² · Pᵢ`, `1 · (1 - ∑ᵢ Xᵢⱼ) ²`,
`1 · 1 ² · Xᵢⱼ · Hᵢᵢ'ⱼ` for `i ≠ i'`, and `(m - n - 1) · 1 ²`. -/
private noncomputable def phpSummand [DecidableEq R] (m n : ℕ) :
    Fin m ⊕ Fin n ⊕ (Fin n × Fin m × Fin m) ⊕ Unit → Summand (Fin m × Fin n) R
  | .inl i => ⟨{∑ j, X (i, j) - 1}, 1, 1⟩
  | .inr (.inl j) => ⟨∅, 1, 1 - ∑ i, X (i, j)⟩
  | .inr (.inr (.inl (j, i, i'))) =>
    if i = i' then ⟨∅, 0, 0⟩ else ⟨{X (i, j), 1 - X (i, j) - X (i', j)}, 1, 1⟩
  | .inr (.inr (.inr _)) => ⟨∅, ((m - n - 1 : ℕ) : R), 1⟩

private theorem totalDegree_X_le (v : Fin m × Fin n) :
    (X v : MvPolynomial (Fin m × Fin n) R).totalDegree ≤ 1 := by
  rw [X]
  exact (totalDegree_monomial_le _ _).trans (by simp)

private theorem totalDegree_one_sub_sum_le (j : Fin n) :
    (1 - ∑ i, X (i, j) : MvPolynomial (Fin m × Fin n) R).totalDegree ≤ 1 :=
  (totalDegree_sub _ _).trans (max_le (by simp) (totalDegree_finsetSum_le fun i _ =>
    totalDegree_X_le _))

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- **Degree-`2` refutation of the pigeonhole principle**: for `m > n`, the inequality constraints
of `PHP^m_n` and the Boolean axioms have a Positivstellensatz refutation of degree `2`, over every
strictly ordered commutative ring. For `m = n + 1` this is [Grigoriev, Hirsch and Pasechnik,
Example 2.1][GrigorievHirschPasechnik2002]. -/
theorem refutableInDegree_two_pigeonhole (h : n < m) :
    RefutableInDegree (cnfIneqs (pigeonhole m n) : Set (MvPolynomial (Fin m × Fin n) R))
      (booleanAxioms (Fin m × Fin n) R) 2 := by
  refine RefutableInDegree.of_sum (ι := Fin n × Fin m) (fun _ => C ((m : R) - 2))
    (fun p => X (p.2, p.1) ^ 2 - X (p.2, p.1)) (phpSummand m n)
    (fun p => X_sq_sub_X_mem_booleanAxioms _) (fun p => ?_) (fun k => ?_) (fun k => ?_)
    (fun k => ?_) ?_
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans
      (max_le (totalDegree_X_pow _ _).le ((totalDegree_X _).le.trans (by norm_num)))
  · rcases k with i | j | ⟨j, i, i'⟩ | -
    · simpa [phpSummand] using pigeonPoly_mem_cnfIneqs i
    · simp [phpSummand]
    · simp only [phpSummand]
      split_ifs with hii'
      · simp
      · rw [coe_pair, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨X_mem_cnfIneqs _ _, holePoly_mem_cnfIneqs hii' j⟩
    · simp [phpSummand]
  · rcases k with i | j | ⟨j, i, i'⟩ | -
    · simp [phpSummand]
    · simp [phpSummand]
    · simp only [phpSummand]
      split_ifs <;> simp
    · simp [phpSummand]
  · rcases k with i | j | ⟨j, i, i'⟩ | -
    · simp only [phpSummand, Summand.degree_def, totalDegree_one, mul_zero, sum_singleton,
        zero_add]
      rw [← toPoly_toIneq_pigeonClause]
      exact (totalDegree_toPoly_le _).trans (by norm_num)
    · simp only [phpSummand, Summand.degree_def, sum_empty, add_zero]
      have := totalDegree_one_sub_sum_le (R := R) (m := m) j
      omega
    · simp only [phpSummand]
      split_ifs with hii'
      · simp [Summand.degree_def]
      · simp only [Summand.degree_def, totalDegree_one, mul_zero, zero_add]
        rw [sum_pair (X_ne_holePoly i i' j), ← toPoly_toIneq_holeClause hii']
        have h1 := totalDegree_toPoly_le (R := R) (holeClause i i' j).toIneq
        have h2 := totalDegree_X_le (R := R) (i, j)
        omega
    · simp [phpSummand, Summand.degree_def]
  · have hT (j : Fin n) (i i' : Fin m) :
        (phpSummand (R := R) m n (.inr (.inr (.inl (j, i, i'))))).toPoly =
          if i = i' then 0 else X (i, j) * (1 - X (i, j) - X (i', j)) := by
      simp only [phpSummand]
      split_ifs with hii'
      · simp [Summand.toPoly_def]
      · simp [Summand.toPoly_def, prod_pair (X_ne_holePoly i i' j)]
    have hsum : ∑ j : Fin n, (∑ i, ∑ i', (if i = i' then 0 else
        X (i, j) * (1 - X (i, j) - X (i', j))) + (1 - ∑ i, X (i, j)) ^ 2 +
        ((m : MvPolynomial (Fin m × Fin n) R) - 2) * ∑ i, (X (i, j) ^ 2 - X (i, j))) =
        ∑ j : Fin n, (1 - ∑ i, X (i, j)) :=
      sum_congr rfl fun j _ => sum_hole_identity fun i => X (i, j)
    have hcomm : ∑ i : Fin m, ∑ j : Fin n, (X (i, j) : MvPolynomial (Fin m × Fin n) R) =
        ∑ j, ∑ i, X (i, j) := sum_comm
    have hcast : ((m - n - 1 : ℕ) : MvPolynomial (Fin m × Fin n) R) = m - n - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub h.le]
      simp
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, hT]
    simp only [phpSummand, Summand.toPoly_def, prod_singleton, prod_empty, map_one, one_pow,
      one_mul, mul_one, map_natCast, map_sub, map_ofNat, hcast]
    simp only [sum_add_distrib, ← mul_sum] at hsum
    simp only [← mul_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hsum ⊢
    linear_combination hsum + hcomm

end Cslib.Logic.PL.SOS.Psatz

namespace Cslib.Logic.PL.SOS.Psatz

open MvPolynomial Finset CNF

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-- **The fractional point `xᵢⱼ = 1 / n`** satisfies the inequality constraints of `PHP^m_n` for
`n ≥ 2`, over a strictly ordered field: `Pᵢ = 0`, `Hᵢᵢ'ⱼ = 1 - 2 / n ≥ 0`, and
`0 ≤ 1 / n ≤ 1`. -/
theorem eval_inv_nonneg_of_mem_cnfIneqs_pigeonhole (hn : 2 ≤ n) :
    ∀ f ∈ (cnfIneqs (pigeonhole m n) : Set (MvPolynomial (Fin m × Fin n) R)),
      0 ≤ eval (fun _ => (n : R)⁻¹) f := by
  have hn0 : (0 : R) < n := by exact_mod_cast (by omega : 0 < n)
  have hinv : 0 < (n : R)⁻¹ := inv_pos.2 hn0
  have hhalf : 2 * (n : R)⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (show (2 : R) ≤ n by exact_mod_cast hn) hinv.le
    rwa [inv_mul_cancel₀ hn0.ne', mul_comm] at h
  refine forall_mem_cnfIneqs_iff.2 ⟨fun c hc => ?_, fun v => ?_, fun v => ?_⟩
  · rcases mem_pigeonhole.1 hc with ⟨i, rfl⟩ | ⟨i, i', j, hii', rfl⟩
    · rw [toPoly_toIneq_pigeonClause]
      simp [mul_inv_cancel₀ hn0.ne']
    · rw [toPoly_toIneq_holeClause hii'.ne]
      simp only [map_sub, map_one, eval_X]
      linarith
  · simp
  · simp only [map_sub, map_one, eval_X, sub_nonneg]
    linarith

/-- **Degree `2` is optimal**: for `n ≥ 2`, the constraints of `PHP^m_n` have no
Positivstellensatz refutation of degree at most `1` over a strictly ordered field, for every `m`.
The fractional point `xᵢⱼ = 1 / n` is a pseudo-expectation of degree `1`. -/
theorem not_refutableInDegree_one_pigeonhole (hn : 2 ≤ n) :
    ¬ RefutableInDegree (cnfIneqs (pigeonhole m n) : Set (MvPolynomial (Fin m × Fin n) R))
      (booleanAxioms (Fin m × Fin n) R) 1 :=
  not_refutableInDegree_one_of_eval_nonneg _ (eval_inv_nonneg_of_mem_cnfIneqs_pigeonhole hn)

/-- **The degree of `PHP^m_n`**: for `n ≥ 2`, over a strictly ordered field, the constraints of
`PHP^m_n` have a Positivstellensatz refutation of degree at most `d` exactly when `n < m` and
`2 ≤ d`. -/
theorem refutableInDegree_pigeonhole_iff (hn : 2 ≤ n) {d : ℕ} :
    RefutableInDegree (cnfIneqs (pigeonhole m n) : Set (MvPolynomial (Fin m × Fin n) R))
      (booleanAxioms (Fin m × Fin n) R) d ↔ n < m ∧ 2 ≤ d := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hle
      exact not_satisfiable_of_refutableInDegree h (satisfiable_pigeonhole_iff.2 (by omega))
    · by_contra hd
      exact not_refutableInDegree_one_pigeonhole hn (h.mono le_rfl le_rfl (by omega))
  · rintro ⟨hnm, hd⟩
    exact (refutableInDegree_two_pigeonhole hnm).mono le_rfl le_rfl hd

end Cslib.Logic.PL.SOS.Psatz
