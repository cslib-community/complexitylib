/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Selecting and restoring positions of a bit list

`readPositions` selects bits in a supplied order. `restorePositions` writes those selected bits
back into a full list, retaining a reference list at unselected positions. Both operations are
executable and total: out-of-range reads and missing selected bits are false, and restoring keeps
the reference list's length. A repeated position uses its first occurrence in the selected list.

## Main definitions

* `Cslib.BitString.readPositions`: read a list of positions, in order.
* `Cslib.BitString.restorePositions`: restore selected bits into a reference list.

## Main results

* `Cslib.BitString.getD_readPositions_idxOf`: a selected position reads its original bit.
* `Cslib.BitString.getD_restorePositions`: the bitwise restoration rule.
* `Cslib.BitString.restorePositions_readPositions`: selecting and restoring recovers any list
  that agrees with the reference outside the selected positions.
-/

public section

namespace Cslib.BitString

/-- Read bits at the supplied positions, using `false` outside the list. -/
@[expose] def readPositions (positions : List ℕ) (word : List Bool) : List Bool :=
  positions.map fun j => word.getD j false

/-- Restore selected bits, keeping the reference bits at all other positions. A repeated position
uses its first occurrence, and missing selected bits are false. -/
@[expose] def restorePositions (positions : List ℕ) (reference bits : List Bool) : List Bool :=
  (List.range reference.length).map fun j =>
    if j ∈ positions then bits.getD (positions.idxOf j) false else reference.getD j false

/-- Reading positions returns one bit per position. -/
@[simp] theorem length_readPositions (positions : List ℕ) (word : List Bool) :
    (readPositions positions word).length = positions.length := by
  simp [readPositions]

/-- Restoring positions preserves the reference list's length. -/
@[simp] theorem length_restorePositions (positions : List ℕ) (reference bits : List Bool) :
    (restorePositions positions reference bits).length = reference.length := by
  simp [restorePositions]

/-- The first occurrence of a selected position contains the original bit at that position. -/
theorem getD_readPositions_idxOf {positions : List ℕ} (word : List Bool) {j : ℕ}
    (hj : j ∈ positions) :
    (readPositions positions word).getD (positions.idxOf j) false = word.getD j false := by
  have hindex : positions.idxOf j < positions.length := List.idxOf_lt_length_iff.mpr hj
  rw [List.getD_eq_getElem _ _ (by simpa only [length_readPositions] using hindex)]
  simp [readPositions, List.getElem_idxOf]

/-- Restored bits come from the selected word at selected positions and the reference elsewhere. -/
theorem getD_restorePositions (positions : List ℕ) (reference bits : List Bool) {j : ℕ}
    (hj : j < reference.length) :
    (restorePositions positions reference bits).getD j false =
      if j ∈ positions then bits.getD (positions.idxOf j) false else reference.getD j false :=
  List.getD_map_range _ _ hj

/-- Reading and restoring selected positions recovers a list that agrees with the reference at
all unselected positions. Repeated or out-of-range selected positions do not affect the identity. -/
theorem restorePositions_readPositions (positions : List ℕ) (reference word : List Bool)
    (hlength : word.length = reference.length)
    (houtside : ∀ j, j < reference.length → j ∉ positions →
      word.getD j false = reference.getD j false) :
    restorePositions positions reference (readPositions positions word) = word := by
  apply List.ext_getElem (by simp [hlength])
  intro j hj hj'
  have hindex : j < reference.length := by simpa only [length_restorePositions] using hj
  have hread : (restorePositions positions reference (readPositions positions word)).getD j false =
      word.getD j false := by
    rw [getD_restorePositions _ _ _ hindex]
    split_ifs with hmem
    · exact getD_readPositions_idxOf word hmem
    · exact (houtside j hindex hmem).symm
  simpa only [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] using hread

end Cslib.BitString
