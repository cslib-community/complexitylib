/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Matching.Edmonds

/-! The Edmonds matrix of small bipartite graphs: the `2 × 2` determinant of the complete graph and
its detection from three values, a graph without a perfect matching, the empty vertex type, the
strictness of the size bound in `exists_det_edmondsEval_ne_zero`, and axiom guards. -/

namespace ComplexityTests.EdmondsMatching

open Finset Matrix Cslib.Algorithms.Matching Cslib.Circuits.BipartiteMatching

/-! ### The complete bipartite graph on two vertices -/

/-- The complete bipartite graph on `Fin 2` has a perfect matching. -/
theorem complete_hasPerfectMatching : HasPerfectMatching fun _ : Fin 2 × Fin 2 => true :=
  ⟨1, fun _ => rfl⟩

/-- Its Edmonds matrix at `r` has determinant `r (0, 0) * r (1, 1) - r (0, 1) * r (1, 0)`. -/
example (r : Fin 2 × Fin 2 → ℤ) :
    (edmondsEval (fun _ => true) r).det = r (0, 0) * r (1, 1) - r (0, 1) * r (1, 0) := by
  simp [det_fin_two, edmondsEval_apply]

/-- Its Edmonds determinant is a nonzero polynomial. -/
example : (edmondsMatrix (R := ℤ) fun _ : Fin 2 × Fin 2 => true).det ≠ 0 :=
  det_edmondsMatrix_ne_zero_iff.2 complete_hasPerfectMatching

/-- Values from `{0, 1, 2}`, more than `|V| = 2` of them, detect the perfect matching. -/
example : ∃ r : Fin 2 × Fin 2 → ℤ, (∀ e, r e ∈ ({0, 1, 2} : Finset ℤ)) ∧
    (edmondsEval (fun _ => true) r).det ≠ 0 :=
  exists_det_edmondsEval_ne_zero complete_hasPerfectMatching (by decide)

/-- Over `{0, 1, 2}`, its Edmonds matrix is singular with probability at most `2 / 3`. -/
example : #{r ∈ Fintype.piFinset fun _ : Fin 2 × Fin 2 => ({0, 1, 2} : Finset ℤ) |
      (edmondsEval (fun _ => true) r).det = 0} / (3 ^ 4 : ℚ≥0) ≤ 2 / 3 := by
  have h := card_det_edmondsEval_eq_zero_div_le complete_hasPerfectMatching
    ({0, 1, 2} : Finset ℤ)
  have h3 : #({0, 1, 2} : Finset ℤ) = 3 := by decide
  simpa [h3] using h

/-! ### A graph without a perfect matching -/

/-- Both left vertices are adjacent only to the right vertex `0`. -/
def star (e : Fin 2 × Fin 2) : Bool := decide (e.2 = 0)

/-- The right vertex `1` is unmatched, so `star` has no perfect matching. -/
theorem not_hasPerfectMatching_star : ¬ HasPerfectMatching star :=
  fun ⟨σ, hσ⟩ => by simpa [star] using hσ (σ.symm 1)

/-- Its Edmonds determinant is the zero polynomial. -/
example : (edmondsMatrix (R := ℚ) star).det = 0 :=
  det_edmondsMatrix_eq_zero not_hasPerfectMatching_star

/-- The test has no false positives: the determinant vanishes at all values. -/
example (r : Fin 2 × Fin 2 → ℚ) : (edmondsEval star r).det = 0 :=
  det_edmondsEval_eq_zero not_hasPerfectMatching_star r

/-! ### Edge cases -/

/-- On the empty vertex type, the empty matching is perfect. -/
example : HasPerfectMatching fun _ : Fin 0 × Fin 0 => true := ⟨1, fun v => v.elim0⟩

/-- On the empty vertex type, the Edmonds matrix has determinant `1` at all values. -/
example (r : Fin 0 × Fin 0 → ℤ) : (edmondsEval (fun _ => true) r).det = 1 := det_isEmpty

/-- The bound `|V| < |S|` in `exists_det_edmondsEval_ne_zero` cannot be relaxed to `|V| ≤ |S|`:
for one vertex with its single edge, values from `{0}` never detect the perfect matching. -/
example (r : Fin 1 × Fin 1 → ℤ) (hr : ∀ e, r e ∈ ({0} : Finset ℤ)) :
    (edmondsEval (fun _ => true) r).det = 0 := by
  rw [det_unique, edmondsEval_apply]
  simpa using hr _

/-! ### Axiom guards -/

/-- info: 'Cslib.Algorithms.Matching.det_edmondsMatrix_ne_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms det_edmondsMatrix_ne_zero_iff

/-- info: 'Cslib.Algorithms.Matching.card_det_edmondsEval_eq_zero_div_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms card_det_edmondsEval_eq_zero_div_le

/-- info: 'Cslib.Algorithms.Matching.exists_det_edmondsEval_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_det_edmondsEval_ne_zero

end ComplexityTests.EdmondsMatching
