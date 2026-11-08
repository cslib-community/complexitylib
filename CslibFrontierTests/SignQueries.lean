/-
Copyright (c) 2026 lean-canny contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.Polynomial.SignQueries

/-!
# Sign-query counting tests

Check all three requested signs, a pattern involving two polynomials, an empty pattern,
and the distinction between repeated roots and distinct roots. The zero-polynomial example
shows why root existence needs the nonzero hypothesis.
-/

namespace CslibFrontierTests.SignQueries

open Cslib.SignQueries Polynomial
open scoped BigOperators

private theorem threePointCount (s : SignType) :
    signCount {-1, 0, 1} (fun _ : Unit => (X : ℝ[X])) (fun _ => s) = 1 := by
  classical
  cases s <;> norm_num [signCount, Finset.filter_insert, Finset.filter_singleton, sign_apply]

-- Each sign occurs once on these three points, so its weighted query sum is two.
example (s : SignType) :
    (∑ e : Unit → Fin 3, patternWeight (fun _ => s) e *
      signSum {-1, 0, 1} (queryPolynomial (fun _ => (X : ℝ[X])) e)) = 2 := by
  rw [weighted_queries_eq_count, threePointCount]
  norm_num

-- Only -1 makes X negative and X² positive.
private theorem twoPolynomialCount : signCount {-1, 0, 1}
    (fun b : Bool => if b then (X : ℝ[X]) else X ^ 2)
    (fun b => if b then .neg else .pos) = 1 := by
  classical
  norm_num [signCount, Bool.forall_bool, Finset.filter_insert, Finset.filter_singleton, sign_apply]

example : (∑ e : Bool → Fin 3, patternWeight (fun b => if b then .neg else .pos) e *
    signSum {-1, 0, 1}
      (queryPolynomial (fun b => if b then (X : ℝ[X]) else X ^ 2) e)) = 4 := by
  rw [weighted_queries_eq_count, twoPolynomialCount]
  norm_num

example : Fintype.card (Bool → Fin 3) = 9 := by
  rw [query_count]
  decide

-- An empty pattern imposes no conditions, and its scale factor is one.
example (Z : Finset ℝ) :
    signCount Z (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i) = Z.card := by
  classical
  simp [signCount]

example (p : ℝ[X]) :
    scaledRootCount p (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i) =
      (p.roots.toFinset.card : ℤ) := by
  classical
  rw [scaledRootCount_eq]
  simp [signCount]

-- X² has a double root at zero, but the distinct-root count is one and the scaled count two.
example : scaledRootCount (X ^ 2) (fun _ : Unit => (X : ℝ[X])) (fun _ => .zero) = 2 := by
  rw [scaledRootCount_eq]
  norm_num [signCount, roots_pow, roots_X, Finset.filter_singleton]

-- Apply the root-existence interface with a concrete nonzero polynomial and positive sign.
example : 0 < scaledRootCount (X - C 1) (fun _ : Unit => (X : ℝ[X])) (fun _ => .pos) := by
  rw [scaledRootCount_pos_iff _ (X_sub_C_ne_zero 1)]
  exact ⟨1, by simp, by simp⟩

-- The zero polynomial vanishes at 0, while the library's finite-root convention counts none.
example : scaledRootCount 0 (fun _ : Unit => (X : ℝ[X])) (fun _ => .zero) = 0 ∧
    ∃ x : ℝ, (0 : ℝ[X]).eval x = 0 ∧
      ∀ _ : Unit, SignType.sign ((X : ℝ[X]).eval x) = .zero := by
  exact ⟨scaledRootCount_zero_left _ _, 0, by simp, by simp⟩

end CslibFrontierTests.SignQueries
