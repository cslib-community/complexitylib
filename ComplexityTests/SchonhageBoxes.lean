/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxesFromLeaves

/-!
Finite box regressions: both order conditions, saturation/empty boundaries, exact box
counts, signed value recurrence, and a query whose low-order term cannot be omitted.
These tests assert no native program, lookup or preprocessing bound.
-/

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

namespace SchonhageBoxesTests

example : lowest 2 ({-7, 4, 1} : Finset ℤ) = {-7, 1} := by decide
example : lowest 10 ({-7, 4, 1} : Finset ℤ) = {-7, 1, 4} := by decide
example : lowest 0 ({-7, 4, 1} : Finset ℤ) = ∅ := by decide

example : IsBox 2 0 (![.star, .term .P0] : Cube 2) := by decide
example : ¬IsBox 2 0 (![.term .P0, .star] : Cube 2) := by decide
example : ¬IsBox 1 1 (![.star] : Cube 1) := by decide
example : IsBox 1 1 (![.term (.P 0 0)] : Cube 1) := by decide
example : IsBox 0 0 (Fin.elim0 : Cube 0) := by decide

example : (boxes 0 0 0).card = 1 := by decide +kernel
example : (boxes 1 1 0).card = 11 := by decide +kernel
example : (boxes 1 1 1).card = 9 := by decide +kernel
example : (Cube.leaves (![.star, .star] : Cube 2)).card = 100 := by decide +kernel

-- Real signed inputs with both x/y contributions and a nonzero p/q product.
private def a (u : LeftStr 1) : ℤ :=
  match u 0 with
  | .x i => ![1, 2, -1] i
  | .p i j => !![-3, 2; 0, 5] i j

private def b (v : RightStr 1) : ℤ :=
  match v 0 with
  | .y j => ![3, -2, 1] j
  | .q i j => !![2, -1; 4, 0] i j

private def inner : OutStr 1 := ![.z0]

example : encodeLeft (![.P0] : Leaf 1) a * encodeRight (![.P0] : Leaf 1) b = -4 := by
  decide +kernel

-- At threshold 1, omitting the low-order product changes -8 to -4.
example : ∑ τ ∈ lowLeaves 1 1 inner, encodeLeft τ a * encodeRight τ b = -4 := by
  decide +kernel
example : ∑ V ∈ boxLevelSets 1 1 inner, ∑ π ∈ boxesAt inner V, Cube.val a b π = -4 := by
  decide +kernel
example : boxQuery 1 1 a b inner = -8 := by decide +kernel

-- At threshold zero, the whole answer is the value of one starred box.
example : lowLeaves 1 0 inner = ∅ ∧
    ((boxLevelSets 1 0 inner).biUnion (boxesAt inner)).card = 1 := by decide +kernel
example : boxQuery 1 0 a b inner = -8 := by decide +kernel
example : Cube.val a b (![.star] : Cube 1) = -8 := by decide +kernel
example : boxValue (encodingL a) (encodingR b) 1 (![.star] : Cube 1) = -8 := by
  decide +kernel

example : boxQuery 1 1 a b inner = bilinearProduct a b inner :=
  (bilinearProduct_eq_boxQuery 1 1 (by decide) a b inner (by decide)).symm

-- Both signed inputs nonzero, while the full starred sum cancels exactly.
private def cancelA (u : LeftStr 1) : ℤ :=
  match u 0 with
  | .x i => ![1, 2, -1] i
  | .p _ _ => 0
private def cancelB (v : RightStr 1) : ℤ :=
  match v 0 with
  | .y j => ![3, -2, 1] j
  | .q _ _ => 0

example : Cube.val cancelA cancelB (![.star] : Cube 1) = 0 ∧
    encodeLeft (![.P0] : Leaf 1) cancelA * encodeRight (![.P0] : Leaf 1) cancelB = -4 := by
  decide +kernel

example : boxQuery 0 0 (fun _ : LeftStr 0 => 2) (fun _ : RightStr 0 => -3) Fin.elim0 = -6 := by
  decide +kernel

-- A concrete client of the cardinal bound and of the exact-threshold indexing bijection.
example : (boxes 2 1 1).card ≤ 2 * ∑ d ∈ Icc 1 1, beta 2 1 d :=
  card_boxes_le 2 1 1 (by decide) (by decide)

example : ∃! τ : Leaf 1, (Leaf.Contributes τ inner ∧ order 1 τ = 0) ∧
    starBelow inner τ = (![.star] : Cube 1) :=
  existsUnique_starBelow_eq (by decide) (by decide) (by decide +kernel)

end SchonhageBoxesTests
