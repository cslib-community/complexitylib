/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.Problems.TSP.Approximation

/-!
# Worked metric-TSP approximation examples

These kernel-checked examples (using no `native_decide`) exercise
`Cslib.Complexity.TSP.approxTour`, the minimum-spanning-tree tour:

1. Four cities on a line at positions `0, 1, 2, 3`: the matrix is metric, Kruskal's tree is the
   path, and the tour `[0, 1, 2, 3]` has length `6`, which is optimal.
2. A matrix violating the triangle inequality, with cheap edges `0 - 1`, `1 - 2`, `2 - 3`, `3 - 0`
   and diagonals of length `100`: Kruskal's tree is `0 - 1`, `0 - 3`, `1 - 2`, the tour is
   `[0, 3, 1, 2]` of length `202`, while the tour `[0, 1, 2, 3]` has length `4`. So the metric
   hypothesis of `tourLength_approxTour_le_two_mul` cannot be dropped.
3. Edge cases: no cities, and one city, whose tour costs its diagonal entry.

`List.mergeSort` does not reduce in the kernel, so each run first pins the sorted edge list with
`simp [sortEdges_cons_cons]`, as in `CslibFrontierTests/Kruskal.lean`; the remaining computation is
checked by `decide +kernel`.
-/

public section

namespace CslibFrontierTests.TSPApproximation

open Cslib.Complexity Cslib.Complexity.TSP Cslib.Algorithms.Lean.TSP Cslib.Algorithms.Lean.Kruskal

/-! ### 1. Four cities on a line -/

/-- Four cities on a line at positions `0, 1, 2, 3`. -/
def line4 : List (List ℕ) :=
  [[0, 1, 2, 3], [1, 0, 1, 2], [2, 1, 0, 1], [3, 2, 1, 0]]

theorem line4_isMetric : IsMetric line4 :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The distances of `line4` on `Fin 4`. -/
def δLine (i j : Fin 4) : ℕ := dist line4 i j

theorem sortEdges_line4 : sortEdges (completeEdges δLine) =
    [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨2, 2, 0⟩, ⟨3, 3, 0⟩, ⟨0, 1, 1⟩, ⟨1, 0, 1⟩, ⟨1, 2, 1⟩, ⟨2, 1, 1⟩,
      ⟨2, 3, 1⟩, ⟨3, 2, 1⟩, ⟨0, 2, 2⟩, ⟨1, 3, 2⟩, ⟨2, 0, 2⟩, ⟨3, 1, 2⟩, ⟨0, 3, 3⟩, ⟨3, 0, 3⟩] := by
  rw [show completeEdges δLine =
      [⟨0, 0, 0⟩, ⟨0, 1, 1⟩, ⟨0, 2, 2⟩, ⟨0, 3, 3⟩, ⟨1, 0, 1⟩, ⟨1, 1, 0⟩, ⟨1, 2, 1⟩, ⟨1, 3, 2⟩,
        ⟨2, 0, 2⟩, ⟨2, 1, 1⟩, ⟨2, 2, 0⟩, ⟨2, 3, 1⟩, ⟨3, 0, 3⟩, ⟨3, 1, 2⟩, ⟨3, 2, 1⟩, ⟨3, 3, 0⟩]
      by decide +kernel]
  simp [sortEdges_cons_cons]

theorem approxTour_line4 : approxTour line4 = [0, 1, 2, 3] := by
  change (mstTour δLine).map Fin.val = _
  rw [mstTour_of_pos _ (by decide), kruskalEdges, sortEdges_line4]
  decide +kernel

example : tourLength line4 (approxTour line4) = 6 := by
  rw [approxTour_line4]
  decide +kernel

/-- The guarantee applied to the tour `[0, 1, 2, 3]` of length `6`. -/
example : tourLength line4 (approxTour line4) ≤ 2 * 6 :=
  tourLength_approxTour_le_two_mul_of_mem (x := ⟨line4, 6⟩) line4_isMetric
    ⟨[0, 1, 2, 3], by decide +kernel, by decide +kernel⟩

/-! ### 2. The metric hypothesis is needed -/

/-- A cheap `4`-cycle `0 - 1 - 2 - 3 - 0` with diagonals of length `100`. -/
def nonMetric : List (List ℕ) :=
  [[0, 1, 100, 1], [1, 0, 1, 100], [100, 1, 0, 1], [1, 100, 1, 0]]

/-- The diagonal `0 - 2` is longer than the path `0 - 1 - 2`. -/
example : ¬IsMetric nonMetric := fun h => by
  have := h.triangle 0 (by decide) 1 (by decide) 2 (by decide)
  revert this
  decide +kernel

/-- The distances of `nonMetric` on `Fin 4`. -/
def δNonMetric (i j : Fin 4) : ℕ := dist nonMetric i j

theorem sortEdges_nonMetric : sortEdges (completeEdges δNonMetric) =
    [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨2, 2, 0⟩, ⟨3, 3, 0⟩, ⟨0, 1, 1⟩, ⟨0, 3, 1⟩, ⟨1, 0, 1⟩, ⟨1, 2, 1⟩,
      ⟨2, 1, 1⟩, ⟨2, 3, 1⟩, ⟨3, 0, 1⟩, ⟨3, 2, 1⟩, ⟨0, 2, 100⟩, ⟨1, 3, 100⟩, ⟨2, 0, 100⟩,
      ⟨3, 1, 100⟩] := by
  rw [show completeEdges δNonMetric =
      [⟨0, 0, 0⟩, ⟨0, 1, 1⟩, ⟨0, 2, 100⟩, ⟨0, 3, 1⟩, ⟨1, 0, 1⟩, ⟨1, 1, 0⟩, ⟨1, 2, 1⟩,
        ⟨1, 3, 100⟩, ⟨2, 0, 100⟩, ⟨2, 1, 1⟩, ⟨2, 2, 0⟩, ⟨2, 3, 1⟩, ⟨3, 0, 1⟩, ⟨3, 1, 100⟩,
        ⟨3, 2, 1⟩, ⟨3, 3, 0⟩]
      by decide +kernel]
  simp [sortEdges_cons_cons]

theorem approxTour_nonMetric : approxTour nonMetric = [0, 3, 1, 2] := by
  change (mstTour δNonMetric).map Fin.val = _
  rw [mstTour_of_pos _ (by decide), kruskalEdges, sortEdges_nonMetric]
  decide +kernel

/-- Without the triangle inequality the MST tour is more than twice an optimal tour. -/
example : 2 * tourLength nonMetric [0, 1, 2, 3] < tourLength nonMetric (approxTour nonMetric) := by
  rw [approxTour_nonMetric]
  decide +kernel

/-! ### 3. Edge cases -/

example : approxTour [] = [] := by decide +kernel

/-- One city: the tour is the city alone, and costs the diagonal entry. -/
example : approxTour [[5]] = [0] ∧ tourLength [[5]] (approxTour [[5]]) = 5 := by
  have h : approxTour [[5]] = [0] := by
    change (mstTour (finDist [[5]])).map Fin.val = _
    rw [mstTour_of_pos _ (by decide), kruskalEdges,
      show completeEdges (finDist [[5]]) = [⟨0, 0, 5⟩] by decide +kernel, sortEdges_singleton]
    decide +kernel
  rw [h]
  exact ⟨rfl, by decide +kernel⟩

end CslibFrontierTests.TSPApproximation
