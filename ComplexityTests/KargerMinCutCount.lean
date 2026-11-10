/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.Karger.MinCutCount

/-!
# The number of minimum cuts on small graphs

The unit-weight `4`-cycle is a connected multigraph with minimum cut weight `2` and exactly
`C(4, 2) = 6` minimum cuts, so `card_minCuts_le_choose_two` is tight there, and the tests
instantiate it and the per-cut bound `two_div_le_cutLaw`. The `5`-cycle, with minimum cut weight
`2`, has `C(5, 2) = 10` minimum cuts. The empty graph on four vertices, where `minCut = 0`, has
seven non-trivial minimum cuts; the filter, which then also contains `∅`, has `8 > C(4, 2)`
elements, so the hypothesis `0 < minCut W₀` cannot be dropped. Cuts are counted by their side
without vertex `0`, by brute force (`decide`).
-/

@[expose] public section

namespace ComplexityTests.KargerMinCutCount

open scoped ENNReal
open Cslib.WeightedCut Cslib.Algorithms.Lean.Karger

/-- The symmetric matrix with upper triangle `f` and zero diagonal. -/
def sym {n : ℕ} (f : Fin n → Fin n → ℕ) : Fin n → Fin n → ℕ :=
  fun i j => if i < j then f i j else if j < i then f j i else 0

/-- The `4`-cycle `0 - 1 - 2 - 3 - 0` with unit weights. -/
def C4 : Fin 4 → Fin 4 → ℕ := sym fun i j =>
  match i.val, j.val with
  | 0, 1 => 1 | 1, 2 => 1 | 2, 3 => 1 | 0, 3 => 1 | _, _ => 0

theorem isMultigraph_C4 : IsMultigraph C4 := by
  unfold IsMultigraph
  decide

/-- Every non-trivial cut of the `4`-cycle cuts at least two edges, and `{0}` cuts two. -/
theorem minCut_C4 : minCut C4 = 2 := by
  apply le_antisymm
  · exact (minCut_le_cutWeight C4 (C := {0}) ⟨by decide, by decide⟩).trans_eq (by decide)
  · obtain ⟨C, hC, hw⟩ := exists_minCut_achiever (by simp) C4
    rw [← hw]
    have : ∀ C : Finset (Fin 4), C.Nonempty → C ≠ Finset.univ → 2 ≤ cutWeight C4 C := by decide
    exact this C hC.1 hC.2

/-- The `4`-cycle has exactly `C(4, 2)` minimum cuts: the bound is tight. -/
example : (Finset.univ.filter fun C : Finset (Fin 4) =>
    (0 : Fin 4) ∉ C ∧ cutWeight C4 C = minCut C4).card = (4).choose 2 := by
  rw [minCut_C4]
  decide

/-- The count bound, instantiated on the `4`-cycle. -/
example : (Finset.univ.filter fun C : Finset (Fin 4) =>
    (0 : Fin 4) ∉ C ∧ cutWeight C4 C = minCut C4).card ≤ (4).choose 2 :=
  card_minCuts_le_choose_two isMultigraph_C4 (by rw [minCut_C4]; norm_num) 0

/-- The per-cut bound, instantiated on the minimum cut `{{1}, {0, 2, 3}}` of the `4`-cycle. -/
example : (2 : ℝ≥0∞) / ((4 * (4 - 1) : ℕ) : ℝ≥0∞) ≤
    (cutLaw C4).toOuterMeasure {{1}, Finset.univ \ {1}} :=
  two_div_le_cutLaw isMultigraph_C4 (by rw [minCut_C4]; norm_num)
    ⟨by decide, by decide⟩ (by rw [minCut_C4]; decide)

/-- The answer of `karger` on the `4`-cycle is the weight of the cut it outputs. -/
example : answerLaw ⟨4, C4⟩ = (cutLaw C4).map (cutWeight C4) :=
  answerLaw_eq_map_cutLaw (by norm_num) isMultigraph_C4

/-- The empty graph on four vertices. -/
def E4 : Fin 4 → Fin 4 → ℕ := fun _ _ => 0

theorem minCut_E4 : minCut E4 = 0 :=
  Nat.le_zero.mp ((minCut_le_cutWeight E4 (C := {0}) ⟨by decide, by decide⟩).trans_eq (by decide))

/-- Without `0 < minCut W₀` the count fails: the empty graph has seven non-trivial minimum cuts,
and the filter, which then also contains `∅`, has `8 > C(4, 2)` elements. -/
example : (4 : ℕ).choose 2 < (Finset.univ.filter fun C : Finset (Fin 4) =>
    (0 : Fin 4) ∉ C ∧ cutWeight E4 C = minCut E4).card := by
  rw [minCut_E4]
  decide

/-- The `5`-cycle `0 - 1 - 2 - 3 - 4 - 0` with unit weights. -/
def C5 : Fin 5 → Fin 5 → ℕ := sym fun i j =>
  match i.val, j.val with
  | 0, 1 => 1 | 1, 2 => 1 | 2, 3 => 1 | 3, 4 => 1 | 0, 4 => 1 | _, _ => 0

theorem isMultigraph_C5 : IsMultigraph C5 := by
  unfold IsMultigraph
  decide

/-- Every non-trivial cut of the `5`-cycle cuts at least two edges, and `{0}` cuts two. -/
theorem minCut_C5 : minCut C5 = 2 := by
  apply le_antisymm
  · exact (minCut_le_cutWeight C5 (C := {0}) ⟨by decide, by decide⟩).trans_eq (by decide)
  · obtain ⟨C, hC, hw⟩ := exists_minCut_achiever (by simp) C5
    rw [← hw]
    have : ∀ C : Finset (Fin 5), C.Nonempty → C ≠ Finset.univ → 2 ≤ cutWeight C5 C := by decide
    exact this C hC.1 hC.2

/-- The `5`-cycle has exactly `C(5, 2)` minimum cuts, one for each pair of cut edges. -/
example : (Finset.univ.filter fun C : Finset (Fin 5) =>
    (0 : Fin 5) ∉ C ∧ cutWeight C5 C = minCut C5).card = (5).choose 2 := by
  rw [minCut_C5]
  decide

end ComplexityTests.KargerMinCutCount
