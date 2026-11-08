/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.LatticeReduction.Babai

/-!
# Tests for Babai's nearest-plane algorithm

* `nearestPlane` and `babai` evaluate on small integer bases (compiled evaluation via `#guard`);
  on the knapsack-style basis `K` the preliminary LLL reduction turns a far lattice point into a
  close one;
* the hypotheses of `babai_dotProduct_le` are satisfiable (linearly independent rows, checked by
  the Gram-determinant criterion);
* `isNearestPlane_nearestPlane` holds unconditionally, while a lattice point with a Gram–Schmidt
  coordinate of `x - y` outside `[-1/2, 1/2]` fails `IsNearestPlane`, and the approximation bound
  fails for it;
* with no rows the output is `0`.
-/

namespace ComplexityTests.Algorithms.LatticeReduction.Babai

open Cslib.Algorithms.LatticeReduction InnerProductSpace

set_option linter.hashCommand false

/-- The integer basis `(201, 37), (1648, 297)` of a lattice of determinant `-1279`. -/
def B₁ : Vector (Vector ℤ 2) 2 := #v[#v[201, 37], #v[1648, 297]]

/-- A knapsack-style basis of a rank-3 lattice in `ℤ⁴`. -/
def K : Vector (Vector ℤ 4) 3 := #v[#v[1, 0, 0, 1345], #v[0, 1, 0, 35], #v[0, 0, 1, 154]]

/-- The squared Euclidean distance between two integer vectors. -/
def sqDist {m : ℕ} (x y : Vector ℤ m) : ℤ := (List.ofFn fun l : Fin m => (x[l] - y[l]) ^ 2).sum

/-! ### Evaluation -/

-- On `2ℤ²`, the nearest-plane loop rounds each coordinate to the nearest even integer.
#guard nearestPlane #v[#v[(2 : ℤ), 0], #v[0, 2]] #v[3, 5] == #v[4, 6]

#guard babai B₁ #v[100, 100] == #v[83, 98]

-- Without reduction, the nearest-plane loop on `K` returns a point at squared distance
-- `4² + 0 + 0 + 494² = 244052` from the target.
#guard nearestPlane K #v[3, 7, 11, 100] == #v[-1, 7, 11, 594]
#guard sqDist (nearestPlane K #v[3, 7, 11, 100]) #v[3, 7, 11, 100] == 244052

-- After LLL reduction, Babai's algorithm returns a point at squared distance `16 + 1 + 9 + 9 = 35`.
#guard babai K #v[3, 7, 11, 100] == #v[-1, 6, 8, 97]
#guard sqDist (babai K #v[3, 7, 11, 100]) #v[3, 7, 11, 100] == 35

-- The output `(-1, 6, 8, 97) = -b₀ + 6 b₁ + 8 b₂` is a lattice point.
#guard (#v[-1, 6, 8, 97] : Vector ℤ 4) ==
  Vector.ofFn fun l => -K[0][l] + 6 * K[1][l] + 8 * K[2][l]

-- A target in the lattice is returned unchanged.
#guard babai K #v[1, 1, 1, 1534] == #v[1, 1, 1, 1534]

-- With no rows the lattice is `{0}`.
#guard babai (#v[] : Vector (Vector ℤ 3) 0) #v[10, -3, 7] == #v[0, 0, 0]

/-! ### The hypotheses are satisfiable -/

theorem linearIndependent_B₁ : LinearIndependent ℝ (realRows B₁) := by
  rw [linearIndependent_realRows_iff, Matrix.det_fin_two]
  simp [B₁, dotProduct, Fin.sum_univ_two]

example (t : Vector ℤ 2) {v : Fin 2 → ℤ} (hv : v ∈ Submodule.span ℤ (Set.range (rows B₁))) :
    dotProduct ((babai B₁ t).get - t.get) ((babai B₁ t).get - t.get) ≤
      2 ^ 2 * dotProduct (v - t.get) (v - t.get) :=
  babai_dotProduct_le B₁ linearIndependent_B₁ t hv

example (t : Vector ℤ 2) : (babai B₁ t).get ∈ Submodule.span ℤ (Set.range (rows B₁)) :=
  babai_mem_span B₁ t

/-! ### The nearest-plane condition -/

example (t : Vector ℤ 2) :
    IsNearestPlane (realRows B₁) (intToEuclidean t.get) (intToEuclidean (nearestPlane B₁ t).get) :=
  isNearestPlane_nearestPlane B₁ t

theorem gramSchmidt_one : gramSchmidt ℝ ![(1 : ℝ)] 0 = 1 := by
  have h := gramSchmidt_bot ℝ ![(1 : ℝ)]
  rw [bot_eq_zero] at h
  rw [h]
  rfl

/-- The basis `(1)` of `ℤ ⊂ ℝ` is `δ`-reduced for every `δ`: with one vector, both conditions are
vacuous. -/
theorem isReduced_one (δ : ℝ) : IsReduced δ ![(1 : ℝ)] := by
  refine ⟨fun i j hji => (lt_irrefl j (Subsingleton.elim i j ▸ hji)).elim, fun i j hij => ?_⟩
  have := i.isLt
  have := j.isLt
  omega

/-- In `ℝ` with the basis `(1)`, the lattice point `0` is a nearest-plane output for the
target `2/5`. -/
theorem isNearestPlane_zero : IsNearestPlane ![(1 : ℝ)] (2 / 5) 0 := by
  refine ⟨zero_mem _, fun j => ?_⟩
  rw [Subsingleton.elim j 0, gramSchmidt_one]
  norm_num

/-- In `ℝ` with the basis `(1)`, the lattice point `5` is not a nearest-plane output for the
target `0`. -/
theorem not_isNearestPlane : ¬ IsNearestPlane ![(1 : ℝ)] 0 5 := by
  intro h
  have := h.abs_inner_le 0
  rw [gramSchmidt_one] at this
  norm_num at this

/-- The general-`δ` bound at `δ = 1` for the nearest-plane output `0` of the target `2/5`. -/
example {v : ℝ} (hv : v ∈ Submodule.span ℤ (Set.range ![(1 : ℝ)])) :
    ‖(2 / 5 : ℝ) - 0‖ ^ 2 ≤
      (∑ i ∈ Finset.range 1, (4 / (4 * 1 - 1) : ℝ) ^ i) * ‖(2 / 5 : ℝ) - v‖ ^ 2 :=
  isNearestPlane_zero.norm_sq_le (isReduced_one 1) (by norm_num) le_rfl hv

/-- The approximation bound fails for that point, although the basis `(1)` is `3/4`-reduced and
`5` and `0` are lattice points: `‖0 - 5‖² > 2¹ ‖0 - 0‖²`. So the nearest-plane hypothesis of
`IsNearestPlane.norm_sq_le_two_pow_mul` cannot be dropped. -/
example : IsReduced (3 / 4) ![(1 : ℝ)] ∧ (5 : ℝ) ∈ Submodule.span ℤ (Set.range ![(1 : ℝ)]) ∧
    ¬ ‖(0 : ℝ) - 5‖ ^ 2 ≤ 2 ^ 1 * ‖(0 : ℝ) - 0‖ ^ 2 := by
  refine ⟨isReduced_one _, ?_, by norm_num⟩
  have h : (5 : ℝ) = (5 : ℤ) • ![(1 : ℝ)] 0 := by norm_num
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

end ComplexityTests.Algorithms.LatticeReduction.Babai
