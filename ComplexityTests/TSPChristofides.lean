/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Problems.TSP.Christofides

/-!
# Worked examples of Christofides' algorithm

These kernel-checked examples (using no `native_decide`) exercise
`Cslib.Algorithms.Lean.TSP.christofides` and `Cslib.Complexity.TSP.christofidesTour`:

1. An uneven star on four cities: centre `0` at distance `2` from the leaves `1, 2, 3`, with
   leaf distances `d(1, 2) = 3` and `d(1, 3) = d(2, 3) = 4`. Kruskal's tree is the star, all four
   cities have odd degree, and the three perfect matchings on them cost `5`, `6` and `6`; exhaustive
   search picks `{0 - 3, 1 - 2}`. The Euler circuit `[0, 1, 2, 0, 3, 0]` of the tree plus the
   matching visits `0` three times, and shortcutting yields the tour `[1, 2, 3, 0]` of length
   `11`, which is optimal (the three Hamiltonian cycles have lengths `11`, `11` and `12`).
2. Nonvacuity of `two_mul_cycleCost_shortcutTour_le_three_mul`: Kruskal's tree and the exhaustive
   matching satisfy its hypotheses.
3. Edge cases: no cities, and one city, whose tour costs its diagonal entry.

`List.mergeSort` does not reduce in the kernel, so the sorted edge list is pinned with
`simp [sortEdges_cons_cons]` first, as in `ComplexityTests/TSPApproximation.lean`.
-/

public section

namespace ComplexityTests.TSPChristofides

open Cslib.Complexity Cslib.Complexity.TSP Cslib.Algorithms.Lean.TSP Cslib.Algorithms.Lean.Kruskal
  Cslib.Algorithms.Lean.Euler Cslib.Algorithms.Lean.VertexCover

/-! ### 1. An uneven star -/

/-- A star with centre `0` and leaves `1, 2, 3` at distance `2`; the leaves are `3` or `4` apart. -/
def star : List (List ℕ) :=
  [[0, 2, 2, 2], [2, 0, 3, 4], [2, 3, 0, 4], [2, 4, 4, 0]]

theorem star_isMetric : IsMetric star :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The distances of `star` on `Fin 4`. -/
def δStar (i j : Fin 4) : ℕ := dist star i j

theorem sortEdges_star : sortEdges (completeEdges δStar) =
    [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨2, 2, 0⟩, ⟨3, 3, 0⟩, ⟨0, 1, 2⟩, ⟨0, 2, 2⟩, ⟨0, 3, 2⟩, ⟨1, 0, 2⟩,
      ⟨2, 0, 2⟩, ⟨3, 0, 2⟩, ⟨1, 2, 3⟩, ⟨2, 1, 3⟩, ⟨1, 3, 4⟩, ⟨2, 3, 4⟩, ⟨3, 1, 4⟩, ⟨3, 2, 4⟩] := by
  rw [show completeEdges δStar =
      [⟨0, 0, 0⟩, ⟨0, 1, 2⟩, ⟨0, 2, 2⟩, ⟨0, 3, 2⟩, ⟨1, 0, 2⟩, ⟨1, 1, 0⟩, ⟨1, 2, 3⟩, ⟨1, 3, 4⟩,
        ⟨2, 0, 2⟩, ⟨2, 1, 3⟩, ⟨2, 2, 0⟩, ⟨2, 3, 4⟩, ⟨3, 0, 2⟩, ⟨3, 1, 4⟩, ⟨3, 2, 4⟩, ⟨3, 3, 0⟩]
      by decide +kernel]
  simp [sortEdges_cons_cons]

/-- Kruskal's tree is the star. -/
theorem kruskalEdges_star :
    kruskalEdges (completeEdges δStar) = [⟨0, 1, 2⟩, ⟨0, 2, 2⟩, ⟨0, 3, 2⟩] := by
  rw [kruskalEdges, sortEdges_star]
  decide +kernel

/-- All four cities have odd degree in the star. -/
theorem oddVertices_star : oddVertices (kruskalEdges (completeEdges δStar)) = [0, 1, 2, 3] := by
  rw [kruskalEdges_star]
  decide +kernel

/-- The three perfect matchings on the four cities cost `5`, `6` and `6`. -/
example : ([[(0, 1), (2, 3)], [(0, 2), (1, 3)], [(0, 3), (1, 2)]] : List (List (Fin 4 × Fin 4))).map
    (fun M => (M.map fun e => δStar e.1 e.2).sum) = [6, 6, 5] := by
  decide +kernel

/-- Exhaustive search finds the cheapest perfect matching `{0 - 3, 1 - 2}`. -/
theorem minPerfectMatching_star :
    minPerfectMatching δStar 4 [0, 1, 2, 3] = [(0, 3), (1, 2)] := by
  decide +kernel

/-- Hierholzer's Euler circuit of the star plus the matching visits `0` three times. -/
example : eulerCircuit ([(0, 1), (0, 2), (0, 3)] ++ [(0, 3), (1, 2)] : List (Fin 4 × Fin 4)) 0 =
    [0, 1, 2, 0, 3, 0] := by
  decide +kernel

/-- Shortcutting keeps the last visit to each city. -/
theorem christofides_star : christofides δStar = [1, 2, 3, 0] := by
  rw [christofides, kruskalEdges_star]
  decide +kernel

theorem christofidesTour_star : christofidesTour star = [1, 2, 3, 0] := by
  change (christofides δStar).map Fin.val = _
  rw [christofides_star]
  decide +kernel

/-- The tour has length `11`. -/
example : tourLength star (christofidesTour star) = 11 := by
  rw [christofidesTour_star]
  decide +kernel

/-- The Hamiltonian cycles through `0, 1, 2, 3` have lengths `11`, `11` and `12`, so the tour is
optimal here. -/
example : [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3]].map (tourLength star) = [11, 12, 11] := by
  decide +kernel

/-- The guarantee applied to the tour `[0, 1, 2, 3]` of length `11`. -/
example : 2 * tourLength star (christofidesTour star) ≤ 3 * 11 :=
  two_mul_tourLength_christofidesTour_le_three_mul_of_mem star_isMetric
    ⟨[0, 1, 2, 3], by decide +kernel, by decide +kernel⟩

/-! ### 2. Nonvacuity of the bound for any tree and matching -/

/-- Kruskal's tree and the exhaustive matching meet the hypotheses of
`two_mul_cycleCost_shortcutTour_le_three_mul`, which then applies to the star. -/
example : 2 * cycleCost δStar (shortcutTour (kruskalEdges (completeEdges δStar))
      (minPerfectMatching δStar 4 (oddVertices (kruskalEdges (completeEdges δStar))))) ≤
    3 * cycleCost δStar [0, 1, 2, 3] := by
  have hsymm : ∀ x y, δStar x y = δStar y x := by decide +kernel
  have htri : ∀ x y z, δStar x z ≤ δStar x y + δStar y z := by decide +kernel
  have hk : (oddVertices (kruskalEdges (completeEdges δStar))).length ≤ 2 * 4 := by
    rw [oddVertices_star]
    decide
  exact two_mul_cycleCost_shortcutTour_le_three_mul hsymm htri
    (kruskalEdges_isMinSpanningTree (numComponents_edgePartition_completeEdges δStar (by decide)))
    (endpoints_minPerfectMatching_perm δStar hk (even_length_oddVertices _))
    (fun M' hM' => sum_minPerfectMatching_le hsymm hk hM') (by decide) (by decide)

/-! ### 3. Edge cases -/

example : christofidesTour [] = [] := by decide +kernel

/-- One city: the tour is the city alone, and costs the diagonal entry. -/
example : christofidesTour [[5]] = [0] ∧ tourLength [[5]] (christofidesTour [[5]]) = 5 := by
  have h : christofidesTour [[5]] = [0] := by
    change (christofides (finDist [[5]])).map Fin.val = _
    rw [christofides, kruskalEdges,
      show completeEdges (finDist [[5]]) = [⟨0, 0, 5⟩] by decide +kernel, sortEdges_singleton]
    decide +kernel
  rw [h]
  exact ⟨rfl, by decide +kernel⟩

end ComplexityTests.TSPChristofides
