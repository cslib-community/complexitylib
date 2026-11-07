/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CuttingPlanes
public import Complexity.Logics.Propositional.Pigeonhole
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Polynomial-size cutting planes refutations of the pigeonhole principle

[Cook, Coullard and Turán][CookCoullardTuran1987] observed that cutting planes refute the
pigeonhole formula `PHP^m_n` (`Cslib.Logic.PL.CNF.pigeonhole m n`), for `m > n`, in polynomial size
(see also [Jukna, Section 19.2][Jukna2012]), whereas resolution needs exponential size
([Haken][Haken1985]; see `Complexity.Logics.Propositional.CuttingPlanes.Separation`).

In the translation of `PHP^m_n` into inequalities, pigeon `i` gives `∑ⱼ x_{ij} ≥ 1`
(`Cslib.Logic.PL.CNF.toIneq_pigeonClause`) and pigeons `i ≠ i'` and hole `j` give
`-x_{ij} - x_{i'j} ≥ -1` (`Cslib.Logic.PL.CNF.toIneq_holeClause`). The refutation has two steps.

1. **At most one pigeon per hole** (`Cslib.Logic.PL.CuttingPlanes.derivableInSize_holeSum`). For a
   nonempty set `P` of pigeons, `-∑_{i ∈ P} x_{ij} ≥ -1` (`Cslib.Logic.PL.CuttingPlanes.holeSum`)
   is derived by induction on `P`: from it, adding a new pigeon `a` gives
   `#P (-∑_{i ∈ P} x_{ij} ≥ -1) + ∑_{i ∈ P} (-x_{ij} - x_{aj} ≥ -1) + (-x_{aj} ≥ -1)`, which is
   `-(#P + 1) ∑_{i ∈ P ∪ {a}} x_{ij} ≥ -(2 #P + 1)`, and dividing by `#P + 1` rounds the bound up to
   `-1`. This takes at most `#P (#P + 3)` lines.
2. **Counting** (`Cslib.Logic.PL.CuttingPlanes.refutableInSize_pigeonhole`). Adding the `m` pigeon
   inequalities and the `n` hole inequalities for all pigeons gives `0 ≥ m - n`, and dividing by
   `m - n` gives `0 ≥ 1`. In total there are at most `(n + 1) (m + 1)²` lines.

Coefficients stay at most `m` and bounds at most `2 m` in absolute value. The intermediate lines
of step 1 are derived afresh for each hole, so the refutation is in fact tree-like, as in Jukna's
statement; this file records its number of lines but does not define tree-like cutting planes.

## Main definitions

* `Cslib.Logic.PL.CuttingPlanes.holeSum`: the inequality `-∑_{i ∈ P} x_{ij} ≥ -1`.

## Main results

* `Cslib.Logic.PL.CNF.toIneq_pigeonClause`, `Cslib.Logic.PL.CNF.toIneq_holeClause`: the
  inequalities of `PHP^m_n`.
* `Cslib.Logic.PL.CuttingPlanes.derivableInSize_holeSum`: at most one pigeon per hole.
* `Cslib.Logic.PL.CuttingPlanes.refutableInSize_pigeonhole`,
  `Cslib.Logic.PL.CuttingPlanes.refutableInSize_pigeonhole_succ`: `PHP^m_n` has a cutting planes
  refutation of at most `(n + 1) (m + 1)²` lines.

## References

* [W. Cook, C. R. Coullard, Gy. Turán, *On the complexity of cutting-plane
  proofs*][CookCoullardTuran1987]
* [A. Haken, *The intractability of resolution*][Haken1985]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 19.2][Jukna2012]
-/

public section

open Finset

namespace Cslib.Logic.PL

open Ineq

variable {m n : ℕ}

/-- The inequality of a hole clause: `-x_{ij} - x_{i'j} ≥ -1`, written as `0 ≥ 1` plus the axioms
`-x_{ij} ≥ -1` and `-x_{i'j} ≥ -1`. -/
theorem CNF.toIneq_holeClause {i i' : Fin m} (hii' : i ≠ i') (j : Fin n) :
    (CNF.holeClause i i' j).toIneq = contra + (leOne (i, j) + leOne (i', j)) := by
  rw [Clause.toIneq_of_nodup (by simp [CNF.holeClause, hii'])]
  simp [CNF.holeClause]

/-- The inequality of a pigeon clause: `∑ⱼ x_{ij} ≥ 1`, written as `0 ≥ 1` plus the axioms
`x_{ij} ≥ 0`. -/
theorem CNF.toIneq_pigeonClause (i : Fin m) :
    (CNF.pigeonClause n i).toIneq = contra + ∑ j, nonneg (i, j) := by
  rw [CNF.pigeonClause,
    Clause.toIneq_of_nodup ((List.nodup_finRange n).map fun j j' h => by simpa using h),
    Fin.sum_univ_def]
  simp [Function.comp_def]

namespace CuttingPlanes

open CNF

/-- `-x_{ij} - x_{i'j} ≥ -1` is an inequality of `PHP^m_n` for all pigeons `i ≠ i'`. -/
private theorem mem_toIneqs_pigeonhole {i i' : Fin m} (hii' : i ≠ i') (j : Fin n) :
    contra + (leOne (i, j) + leOne (i', j)) ∈ (pigeonhole m n).toIneqs := by
  rcases lt_or_gt_of_ne hii' with h | h
  · exact ⟨_, mem_pigeonhole.2 (Or.inr ⟨i, i', j, h, rfl⟩), toIneq_holeClause hii' j⟩
  · refine ⟨_, mem_pigeonhole.2 (Or.inr ⟨i', i, j, h, rfl⟩), ?_⟩
    rw [toIneq_holeClause hii'.symm, add_comm (leOne _)]

/-- The inequality `-∑_{i ∈ P} x_{ij} ≥ -1`: at most one of the pigeons `P` sits in hole `j`. -/
noncomputable def holeSum (P : Finset (Fin m)) (j : Fin n) : Ineq (Fin m × Fin n) :=
  ⟨∑ i ∈ P, Finsupp.single (i, j) (-1), -1⟩

/-- **At most one pigeon per hole** [Cook, Coullard and Turán][CookCoullardTuran1987]: for a
nonempty set `P` of pigeons, `-∑_{i ∈ P} x_{ij} ≥ -1` has a cutting planes derivation from `PHP^m_n`
of at most `#P (#P + 3)` lines. -/
theorem derivableInSize_holeSum {P : Finset (Fin m)} (hP : P.Nonempty) (j : Fin n) :
    DerivableInSize (pigeonhole m n).toIneqs (holeSum P j) (#P * (#P + 3)) := by
  induction hP using Finset.Nonempty.cons_induction with
  | singleton a =>
    have : holeSum {a} j = leOne (a, j) := by ext <;> simp [holeSum]
    rw [this]
    exact (DerivableInSize.leOne _).mono (by simp)
  | cons a P ha hP ih =>
    have hhole : ∀ i ∈ P, DerivableInSize (pigeonhole m n).toIneqs
        (contra + (leOne (i, j) + leOne (a, j))) 1 := fun i hi =>
      .hyp (mem_toIneqs_pigeonhole (ne_of_mem_of_not_mem hi ha) j)
    have hd := ((ih.smul #P hP.card_pos).add_sum P hhole).add (DerivableInSize.leOne (a, j))
    have hcoeff : (#P • holeSum P j + ∑ i ∈ P, (contra + (leOne (i, j) + leOne (a, j))) +
        leOne (a, j)).coeff = ((#P + 1 : ℕ) : ℤ) • (holeSum (cons a P ha) j).coeff := by
      simp only [holeSum, coeff_add, coeff_nsmul, coeff_sum, coeff_contra, coeff_leOne,
        sum_add_distrib, sum_const, sum_cons]
      push_cast
      module
    have hdiv := hd.div (#P + 1) (Nat.succ_pos _) fun v => by
      rw [hcoeff, Finsupp.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    rw [div_eq_of (Nat.succ_pos _) hcoeff (by simp [holeSum]; omega)
      (by simp [holeSum]; omega)] at hdiv
    refine hdiv.mono (le_of_eq ?_)
    rw [card_cons]
    ring

/-- **Cutting planes refute the pigeonhole principle in polynomial size** [Cook, Coullard and
Turán][CookCoullardTuran1987] [Jukna, Section 19.2][Jukna2012]: for `m > n`, `PHP^m_n` has a
cutting planes refutation of at most `(n + 1) (m + 1)²` lines. Summing `-∑ᵢ x_{ij} ≥ -1` over the
holes and `∑ⱼ x_{ij} ≥ 1` over the pigeons gives `0 ≥ m - n`, and dividing by `m - n` gives
`0 ≥ 1`. -/
theorem refutableInSize_pigeonhole (h : n < m) :
    RefutableInSize (pigeonhole m n).toIneqs ((n + 1) * (m + 1) ^ 2) := by
  have hm : (univ : Finset (Fin m)).Nonempty := univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩
  have hp := DerivableInSize.sum hm (r := 1) (Γ := (pigeonhole m n).toIneqs)
    (f := fun i => contra + ∑ j, nonneg (i, j)) fun i _ => by
      rw [← toIneq_pigeonClause]
      exact .hyp (toIneq_mem_toIneqs (mem_pigeonhole.2 (Or.inl ⟨i, rfl⟩)))
  have hh := hp.add_sum (univ : Finset (Fin n)) fun j _ => derivableInSize_holeSum hm j
  have hcoeff : (∑ i : Fin m, (contra + ∑ j : Fin n, nonneg (i, j)) +
      ∑ j : Fin n, holeSum univ j).coeff =
        ((m - n : ℕ) : ℤ) • (contra : Ineq (Fin m × Fin n)).coeff := by
    simp only [holeSum, coeff_add, coeff_sum, coeff_contra, coeff_nonneg, zero_add, smul_zero]
    rw [sum_comm (s := (univ : Finset (Fin n)))]
    simp only [Finsupp.single_neg, sum_neg_distrib, add_neg_cancel]
  have hd := hh.div (m - n) (by omega) fun v => by
    rw [hcoeff, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  rw [div_eq_of (by omega) hcoeff (by simp [holeSum]; omega) (by simp [holeSum]; omega)] at hd
  refine hd.mono ?_
  simp only [card_univ, Fintype.card_fin]
  nlinarith [Nat.mul_le_mul_left m h.le]

/-- `PHP^{n+1}_n` has a cutting planes refutation of at most `(n + 1) (n + 2)²` lines. -/
theorem refutableInSize_pigeonhole_succ (n : ℕ) :
    RefutableInSize (pigeonhole (n + 1) n).toIneqs ((n + 1) * (n + 2) ^ 2) :=
  refutableInSize_pigeonhole n.lt_succ_self

end CuttingPlanes

end Cslib.Logic.PL
