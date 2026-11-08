/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.WeightedCut.Contraction

/-!
# Supervertex contraction tests

Exercise the contraction API of `Cslib.WeightedCut` on the 4-cycle `0 - 1 - 2 - 3 - 0` with
weights `3, 1, 4, 2`, importing only the probability-free contraction module:

* merging `3` into `0` (`v = Fin.last 3`, no compaction) keeps the slots `0, 1, 2`, drops the
  edge `0 - 3` between the merged vertices and redirects `2 - 3` to `0 - 2`;
* merging `1` into `0` moves the last vertex `3` into the freed slot `1`;
* the total doubled weight drops by `2 * W u v`;
* a cut that does not separate the merged pair keeps its weight (`cutWeight_contractCut`), and
  one that separates them need not.
-/

namespace ComplexityTests.WeightedCutContraction

open Cslib.WeightedCut

/-- The symmetric matrix with zero diagonal given by its entries above the diagonal. -/
private def sym {n : ℕ} (f : Fin n → Fin n → ℕ) : Fin n → Fin n → ℕ :=
  fun i j => if i < j then f i j else if j < i then f j i else 0

/-- The 4-cycle `0 - 1 - 2 - 3 - 0` with weights `3, 1, 4, 2`. -/
private def G4 : Fin 4 → Fin 4 → ℕ := sym fun i j =>
  match i.val, j.val with
  | 0, 1 => 3 | 1, 2 => 1 | 2, 3 => 4 | 0, 3 => 2 | _, _ => 0

private theorem isMultigraph_G4 : IsMultigraph G4 := by
  unfold IsMultigraph
  decide

/-! ### Merging the last vertex: no compaction -/

/-- Merging `3` into `0` gives the triangle `0 - 1 - 2` with weights `3, 1, 4`. -/
example : ∀ i j : Fin 3, contractMatrix G4 0 3 i j =
    sym (fun i j => match i.val, j.val with
      | 0, 1 => 3 | 1, 2 => 1 | 0, 2 => 4 | _, _ => 0) i j := by
  decide

example : ∀ x : Fin 4, contractPart id (0 : Fin 4) 3 (by decide) x =
    ![0, 1, 2, 0] x := by
  decide

/-! ### Merging an inner vertex: the last vertex moves into the freed slot -/

/-- Merging `1` into `0` puts vertex `3` in slot `1`: the edges are `0 - 1` of weight `2`,
`1 - 2` of weight `4` (the old `2 - 3`) and `0 - 2` of weight `1` (the old `1 - 2`). -/
example : ∀ i j : Fin 3, contractMatrix G4 0 1 i j =
    sym (fun i j => match i.val, j.val with
      | 0, 1 => 2 | 1, 2 => 4 | 0, 2 => 1 | _, _ => 0) i j := by
  decide

example : embedCompact (1 : Fin 4) 1 = 3 ∧ compactIdx (1 : Fin 4) 3 (by decide) = 1 := by
  decide

example : ∀ x : Fin 4, contractPart id (0 : Fin 4) 1 (by decide) x =
    ![0, 0, 2, 1] x := by
  decide

/-- The contracted matrix is again a multigraph. -/
example : IsMultigraph (contractMatrix G4 0 1) :=
  isMultigraph_contractMatrix isMultigraph_G4 0 1

/-- The total doubled weight drops from `2 * 10` to `2 * 7 = 2 * 10 - 2 * G4 0 1`. -/
example : totalDoubledWeight G4 = 20 ∧ totalDoubledWeight (contractMatrix G4 0 1) = 14 := by
  decide

example : totalDoubledWeight (contractMatrix G4 0 1) + 2 * G4 0 1 = totalDoubledWeight G4 :=
  totalDoubledWeight_contractMatrix isMultigraph_G4 (u := 0) (v := 1) (by decide)

/-! ### Cuts across a contraction -/

/-- The cut `{0, 1}` does not separate `0` and `1`; it becomes `{0}` (slot `1` holds vertex `3`,
which is not in the cut) and keeps its weight `1 + 2 = 3`. -/
example : contractCut (1 : Fin 4) {0, 1} = {0} ∧ cutWeight G4 {0, 1} = 3 ∧
    cutWeight (contractMatrix G4 0 1) {0} = 3 := by
  decide

example : cutWeight (contractMatrix G4 0 1) (contractCut 1 {0, 1}) = cutWeight G4 {0, 1} :=
  cutWeight_contractCut isMultigraph_G4 (by decide) (by decide)

/-- The hypothesis `s ∈ C ↔ t ∈ C` is needed: the cut `{0}` separates `0` and `1`, has weight
`3 + 2 = 5`, and its contracted image `{0}` has weight `2 + 1 = 3`. -/
example : cutWeight G4 {0} = 5 ∧ cutWeight (contractMatrix G4 0 1) (contractCut 1 {0}) = 3 := by
  decide

/-- Contracting the identity map yields a contraction of the original graph. -/
example : IsContractionOf G4 (contractPart id (0 : Fin 4) 1 (by decide)) (contractMatrix G4 0 1) :=
  isContractionOf_contract (isContractionOf_id isMultigraph_G4) (by decide)

end ComplexityTests.WeightedCutContraction
