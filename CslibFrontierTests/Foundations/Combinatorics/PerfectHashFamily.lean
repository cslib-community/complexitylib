/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import CslibFrontier.Foundations.Combinatorics.PerfectHashFamily.Basic
public import CslibFrontier.Foundations.Combinatorics.PerfectHashFamily.LinearHash

public section

open Finset

namespace Cslib.Tests.PerfectHashFamily

/-! ### Linear hashing

The set `{2, 7}` of numbers below `9` has two ordered pairs of distinct elements, fewer than
the prime `3`. -/

/-- Some linear hash map with values below `3` separates `2` and `7`. -/
theorem exists_linearHash_separating : ∃ u ∈ linearHash 3 9, u 2 ≠ u 7 ∧ u 2 < 3 ∧ u 7 < 3 := by
  obtain ⟨u, hu, hinj⟩ := exists_injOn_linearHash (p := 3) (q := 9) (S := {2, 7})
    (by decide) (by decide)
  exact ⟨u, hu, fun h => absurd (hinj (by simp) (by simp) h) (by decide),
    linearHash_lt hu 2, linearHash_lt hu 7⟩

/-! ### The perfect hash family -/

/-- Some member of `perfectHashFamily 5 2` separates the points `1` and `3` of `Fin 5`. -/
theorem exists_perfectHashFamily_separating : ∃ h ∈ perfectHashFamily 5 2, h 1 ≠ h 3 := by
  obtain ⟨h, hh, hinj⟩ := isPerfectHashFamily_perfectHashFamily 5 2 (by decide) {1, 3} (by decide)
  exact ⟨h, hh, fun h' => absurd (hinj (by simp) (by simp) h') (by decide)⟩

/-- A family that separates two points is nonempty, and this one has at most `5 * 2 ^ 50`
members. -/
example : 0 < #(perfectHashFamily 5 2) ∧ #(perfectHashFamily 5 2) ≤ 5 * 2 ^ 50 :=
  let ⟨_, hh, _⟩ := exists_perfectHashFamily_separating
  ⟨card_pos.2 ⟨_, hh⟩, card_perfectHashFamily_le 5 2⟩

/-- The family is empty when there are no points to hash. -/
example (r : ℕ) : perfectHashFamily 0 r = ∅ :=
  card_eq_zero.1 (Nat.le_zero.1 ((card_perfectHashFamily_le 0 r).trans_eq (zero_mul _)))

end Cslib.Tests.PerfectHashFamily
