/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.LatticeReduction.LLL

/-!
# Tests for the LLL algorithm

* `lll` evaluates on small integer bases (compiled evaluation via `#guard`);
* the integer basis `B₀ = ((1, 0), (7, 1))` has linearly independent rows (by the Gram-determinant
  criterion `linearIndependent_realRows_iff`) and an integral Gram matrix, so the hypotheses of
  `isReduced_lll` and `dotProduct_lll_zero_le` are satisfiable;
* dependent rows fail the hypothesis;
* the exact Gram–Schmidt rows of a `3 × 3` basis.
-/

namespace ComplexityTests.Algorithms.LatticeReduction.LLL

open Cslib.Algorithms.LatticeReduction

set_option linter.hashCommand false

/-- The integer basis `(1, 0), (7, 1)` of `ℤ²`. -/
def B₀ : Vector (Vector ℤ 2) 2 := #v[#v[1, 0], #v[7, 1]]

/-! ### Evaluation -/

#guard lll B₀ == #v[#v[1, 0], #v[0, 1]]

-- One swap: `(2, 0), (1, 1)` reduces to `(-1, 1), (1, 1)`.
#guard lll #v[#v[(2 : ℤ), 0], #v[1, 1]] == #v[#v[-1, 1], #v[1, 1]]

#guard lll #v[#v[(1 : ℤ), 1, 1], #v[-1, 0, 2], #v[3, 5, 6]] ==
  #v[#v[0, 1, 0], #v[1, 0, 1], #v[-2, 0, 1]]

#guard lll #v[#v[(1 : ℤ), 0, 0, 1345], #v[0, 1, 0, 35], #v[0, 0, 1, 154]] ==
  #v[#v[0, 9, -2, 7], #v[1, 1, -9, -6], #v[1, -3, -8, 8]]

-- The exact Gram–Schmidt rows of `(1, 1, 1), (-1, 0, 2), (3, 5, 6)`.
#guard gramSchmidtRows #v[#v[(1 : ℤ), 1, 1], #v[-1, 0, 2], #v[3, 5, 6]] ==
  #v[#v[1, 1, 1], #v[-4 / 3, -1 / 3, 5 / 3], #v[-3 / 7, 9 / 14, -3 / 14]]

/-! ### The hypotheses are satisfiable -/

theorem linearIndependent_B₀ : LinearIndependent ℝ (realRows B₀) := by
  rw [linearIndependent_realRows_iff, Matrix.det_fin_two]
  simp [B₀, dotProduct, Fin.sum_univ_two]

/-- A concrete integral basis: integral Gram matrix and linearly independent rows. -/
example : HasIntegralGram (realRows B₀) ∧ LinearIndependent ℝ (realRows B₀) :=
  ⟨hasIntegralGram_realRows B₀, linearIndependent_B₀⟩

example : IsReduced (3 / 4) (realRows (lll B₀)) := (isReduced_lll B₀ linearIndependent_B₀).1

example : Submodule.span ℤ (Set.range (rows (lll B₀))) =
    Submodule.span ℤ (Set.range (rows B₀)) :=
  span_lll B₀

example {x : Fin 2 → ℤ} (hx : x ∈ Submodule.span ℤ (Set.range (rows B₀))) (hx0 : x ≠ 0) :
    dotProduct (rows (lll B₀) 0) (rows (lll B₀) 0) ≤ 2 ^ 1 * dotProduct x x :=
  dotProduct_lll_zero_le B₀ linearIndependent_B₀ hx hx0

/-- Dependent rows fail the hypothesis of `isReduced_lll`. -/
example : ¬ LinearIndependent ℝ (realRows (#v[#v[1, 2], #v[2, 4]] : Vector (Vector ℤ 2) 2)) := by
  rw [linearIndependent_realRows_iff, Matrix.det_fin_two]
  simp [dotProduct, Fin.sum_univ_two]

end ComplexityTests.Algorithms.LatticeReduction.LLL
