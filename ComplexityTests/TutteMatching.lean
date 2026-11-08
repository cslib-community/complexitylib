/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the Tutte matrix criterion)

import Complexity.Algorithms.Matching.Tutte
import Complexity.Foundations.Combinatorics.SimpleGraph.PermMatching
import Complexity.Foundations.LinearAlgebra.Matrix.SkewDeterminant
import Mathlib.GroupTheory.Perm.Fin

/-! The Tutte matrix of small simple graphs, checked as a `module` client: the single edge `K₂`
(determinant `r²`, detection from `{0, 1, 2}`, the probability bound `2 / 3`), `K₄` (a perfect
matching extracted from the rotation of `Fin 4`, a single even cycle, then detected), the triangle
(singular at all values) and the star `K₁,₃` (zero Tutte polynomial), and the skew-symmetric
determinant lemmas on a `3 × 3` alternating matrix and a `1 × 1` matrix over `ZMod 2`, which is
skew-symmetric but not alternating. -/

set_option linter.privateModule false

namespace ComplexityTests.TutteMatching

open Finset Matrix Cslib.Algorithms.Matching

/-! ### A single edge -/

/-- The single edge `K₂` on `Fin 2` has a perfect matching. -/
theorem top_two_isPerfectMatching : ∃ M : (⊤ : SimpleGraph (Fin 2)).Subgraph,
    M.IsPerfectMatching :=
  ⟨⊤, SimpleGraph.Subgraph.isPerfectMatching_iff.2 fun v =>
    ⟨if v = 0 then 1 else 0, by fin_cases v <;> simp, fun w hw => by
      fin_cases v <;> fin_cases w <;> simp_all⟩⟩

/-- Its Tutte matrix at `r` has determinant `r s(0, 1) ^ 2`. -/
example (r : Sym2 (Fin 2) → ℤ) :
    (tutteEval (⊤ : SimpleGraph (Fin 2)) r).det = r s(0, 1) ^ 2 := by
  rw [det_fin_two, tutteEval_apply, tutteEval_apply, tutteEval_apply, tutteEval_apply]
  have h : s((1 : Fin 2), 0) = s(0, 1) := Sym2.eq_swap
  simp [h, sq]

/-- Its Tutte determinant is a nonzero polynomial. -/
example : (tutteMatrix (R := ℤ) (⊤ : SimpleGraph (Fin 2))).det ≠ 0 :=
  (det_tutteMatrix_ne_zero_iff _).2 top_two_isPerfectMatching

/-- Values from `{0, 1, 2}`, more than `|V| = 2` of them, detect the perfect matching. -/
example : ∃ r : Sym2 (Fin 2) → ℤ, (∀ e, r e ∈ ({0, 1, 2} : Finset ℤ)) ∧
    (tutteEval (⊤ : SimpleGraph (Fin 2)) r).det ≠ 0 :=
  exists_det_tutteEval_ne_zero _ top_two_isPerfectMatching.choose_spec (by decide)

/-- Over `{0, 1, 2}`, the Tutte matrix of `K₂` is singular with probability at most `2 / 3`. -/
example : #{r ∈ Fintype.piFinset fun _ : Sym2 (Fin 2) => ({0, 1, 2} : Finset ℤ) |
      (tutteEval (⊤ : SimpleGraph (Fin 2)) r).det = 0} / (3 ^ 3 : ℚ≥0) ≤ 2 / 3 := by
  have h := card_det_tutteEval_eq_zero_div_le _ top_two_isPerfectMatching.choose_spec
    ({0, 1, 2} : Finset ℤ)
  have h3 : #({0, 1, 2} : Finset ℤ) = 3 := by decide
  have hs : Fintype.card (Sym2 (Fin 2)) = 3 := by decide
  simpa [h3, hs] using h

/-! ### The complete graph on four vertices -/

/-- The rotation of `Fin 4` moves every vertex to a neighbour in `K₄` and is a single `4`-cycle,
so it gives a perfect matching of `K₄`. -/
theorem top_four_isPerfectMatching : ∃ M : (⊤ : SimpleGraph (Fin 4)).Subgraph,
    M.IsPerfectMatching := by
  refine SimpleGraph.exists_isPerfectMatching_of_perm (finRotate 4) (fun v => ?_) ?_
  · rw [SimpleGraph.top_adj, ne_comm]
    exact Equiv.Perm.mem_support.1 (by simp [support_finRotate])
  · rw [cycleType_finRotate (n := 2)]
    simp only [Multiset.mem_singleton, forall_eq]
    decide

/-- Its Tutte determinant is a nonzero polynomial, and values from `{0, 1, 2, 3, 4}` detect the
perfect matching. -/
example : (tutteMatrix (R := ℤ) (⊤ : SimpleGraph (Fin 4))).det ≠ 0 ∧
    ∃ r : Sym2 (Fin 4) → ℤ, (∀ e, r e ∈ ({0, 1, 2, 3, 4} : Finset ℤ)) ∧
      (tutteEval (⊤ : SimpleGraph (Fin 4)) r).det ≠ 0 :=
  ⟨(det_tutteMatrix_ne_zero_iff _).2 top_four_isPerfectMatching,
    exists_det_tutteEval_ne_zero _ top_four_isPerfectMatching.choose_spec (by decide)⟩

/-! ### Graphs without a perfect matching -/

/-- The triangle has odd order, so it has no perfect matching. -/
theorem not_triangle : ¬ ∃ M : (⊤ : SimpleGraph (Fin 3)).Subgraph, M.IsPerfectMatching :=
  fun ⟨_, hM⟩ => by
    have h := hM.even_card
    rw [Fintype.card_fin] at h
    exact absurd h (by decide)

/-- The Tutte matrix of the triangle has determinant `0` at all values. -/
example (r : Sym2 (Fin 3) → ℚ) : (tutteEval (⊤ : SimpleGraph (Fin 3)) r).det = 0 :=
  det_tutteEval_eq_zero _ not_triangle r

/-- The star `K₁,₃` with center `0`. -/
def star : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun i j => i = 0 ∧ j ≠ 0

instance : DecidableRel star.Adj := fun i j => by
  unfold star
  infer_instance

/-- The star has even order but no perfect matching: the three leaves are adjacent only to the
center. -/
theorem not_star : ¬ ∃ M : star.Subgraph, M.IsPerfectMatching := by
  rintro ⟨M, hM⟩
  obtain ⟨w1, h1, -⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hM 1
  obtain ⟨w2, h2, -⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hM 2
  obtain ⟨w0, -, hu0⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hM 0
  have e1 := M.adj_sub h1
  have e2 := M.adj_sub h2
  simp only [star, SimpleGraph.fromRel_adj] at e1 e2
  have hw1 : w1 = 0 := by omega
  have hw2 : w2 = 0 := by omega
  subst hw1 hw2
  have := (hu0 1 h1.symm).trans (hu0 2 h2.symm).symm
  exact absurd this (by decide)

/-- The Tutte determinant of the star is the zero polynomial even though the order is even. -/
example : (tutteMatrix (R := ℤ) star).det = 0 :=
  det_tutteMatrix_eq_zero _ not_star

/-! ### Skew-symmetric determinants -/

/-- An alternating `3 × 3` matrix has determinant `0`. -/
example (a b c : ℤ) : (!![0, a, b; -a, 0, c; -b, -c, 0] : Matrix (Fin 3) (Fin 3) ℤ).det = 0 :=
  det_eq_zero_of_transpose_eq_neg_of_odd (by ext i j; fin_cases i <;> fin_cases j <;> simp)
    (fun i => by fin_cases i <;> rfl) (by decide)

/-- Over `ZMod 2` the `1 × 1` matrix `1` satisfies `Aᵀ = -A` but has determinant `1`, so the zero
diagonal hypothesis of `det_eq_zero_of_transpose_eq_neg_of_odd` cannot be dropped. -/
example : (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))ᵀ = -1 ∧
    (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)).det ≠ 0 := by
  refine ⟨by ext i j; fin_cases i; fin_cases j; decide, by simp⟩

end ComplexityTests.TutteMatching
