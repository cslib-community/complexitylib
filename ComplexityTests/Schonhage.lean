/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.MatrixMultiplication.Schonhage.Identity
import Complexity.Algorithms.MatrixMultiplication.Schonhage.Pruned

/-! Concrete tensor evaluations, signed cancellation and pruning boundary cases. -/

open Cslib.Algorithms.MatrixMultiplication.Schonhage

namespace SchonhageTests

private def left : LeftStr 1 → ℤ := fun u =>
  match u 0 with
  | .x i => ![1, 2, 3] i
  | .p i j => !![4, 5; 6, 7] i j

private def right : RightStr 1 → ℤ := fun v =>
  match v 0 with
  | .y j => ![8, 9, 10] j
  | .q i j => !![11, 12; 13, 14] i j

-- The negative tenth term cancels the unwanted outer products in the inner output.
example : Full.multipliedAt 1 left right ![.P0] = (-6, 27) := by decide

example : Full.result 1 left right ![.z0] = 280 := by decide

example : Full.result 1 left right ![.z 0 0] = 95 := by decide

example : Full.result 1 left right ![.z 2 2] = 30 := by decide

-- Unrestricted outer outputs include error terms: 95 is not the wanted product 1 * 8.
example : Full.result 1 left right ![.z 0 0] ≠ 1 * 8 := by decide

example : coefficient (.x 0) (.y 0) .z0 = 0 := by decide

example : coefficient (.p 0 1) (.q 0 1) .z0 = 1 := by decide

example : coefficient (.p 0 1) (.q 1 0) .z0 = 0 := by decide

example : coefficient (.x 0) (.q 0 0) (.z 0 0) = 1 := by decide

private def outerQuery : Finset (OutStr 1) := {![.z 0 0]}

private def innerQuery : Finset (OutStr 1) := {![.z0]}

example : Pruned.result 1 (encodingL left) (encodingR right) outerQuery ![.z 0 0] = 95 := by
  decide

example : Pruned.result 1 (encodingL left) (encodingR right) outerQuery ![.z0] = 0 := by
  decide

example : (leaves outerQuery).card = 1 := by decide

example : (Pruned.calls 1 (encodingL left) (encodingR right) outerQuery).card = 2 := by
  decide

example : Pruned.totalSize (encodingL left) (encodingR right) outerQuery = 2 := by decide

example : (leaves innerQuery).card = 10 := by decide

example : Pruned.totalSize (encodingL left) (encodingR right) innerQuery = 11 := by decide

-- The shared contributing leaf of these two outputs is included only once.
private def mixedQuery : Finset (OutStr 1) := {![.z 0 0], ![.z0]}

example : (leaves mixedQuery).card = 10 := by decide

example : (Pruned.calls 1 (encodingL left) (encodingR right) mixedQuery).card = 11 := by
  decide

example : Pruned.totalSize (encodingL left) (encodingR right) mixedQuery = 12 := by decide

example : Pruned.result 1 (encodingL left) (encodingR right) ∅ ![.z0] = 0 := by decide

example : (Pruned.calls 1 (encodingL left) (encodingR right) ∅).card = 1 := by decide

example : Pruned.totalSize (encodingL left) (encodingR right) ∅ = 0 := by decide

-- Below a two-level query, the outer level keeps one child and the inner one keeps ten.
example : Pruned.result 2 (fun _ => 3) (fun _ => -4) {![.z 1 2, .z0]}
    ![.z 1 2, .z0] = -120 := by decide

example : Pruned.totalSize (fun _ : Leaf 2 => 3) (fun _ => -4) {![.z 1 2, .z0]} = 12 := by
  decide

example : Pruned.result 0 (fun _ => -3) (fun _ => 7) {Fin.elim0} Fin.elim0 = -21 := by
  decide

-- The unqualified visited-leaf equivalence fails at the empty, zero-depth root.
example : Pruned.Visits (fun _ : Leaf 0 => 1) (fun _ => 1) ∅ Fin.elim0 ∧
    Fin.elim0 ∉ leaves (∅ : Finset (OutStr 0)) := by
  constructor
  · exact (Pruned.visits_iff_root_or_mem_leaves _ _ ∅ Fin.elim0).mpr (.inl rfl)
  · simp [leaves]

end SchonhageTests
