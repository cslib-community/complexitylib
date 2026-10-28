/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.MaskTable
public import Complexity.Foundations.Data.Nat.OfDigits
public import Complexity.Foundations.Data.Finset.OrderedFilter

/-!
# Splitting flat tensor digits into band indices

Outer digits `0,1,2` contribute to a base-three offset. Inner digits `3,4,5,6`
contribute to a base-four offset and set the corresponding binary mask bit. All positions
are least significant first, in the encoder's existing numbering.

## Main definitions

* `BandDigits.parts`: the three indices computed by the native digit loop.
* `BandDigits.sevenDigits`: exactly `L` digits, retaining leading zeros.

## Main results

* `BandDigits.parts_bounds`: component bounds derived from the original depth.
* `BandDigits.parts_lists`: the compressed digit-list interpretation of all three indices.
-/

@[expose] public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage.BandDigits

/-- Binary level mask and the two compressed offsets. -/
structure Parts where
  /-- Inner-level mask. -/
  mask : ℕ
  /-- Base-three outer offset. -/
  outer : ℕ
  /-- Base-four inner offset. -/
  inner : ℕ
  deriving DecidableEq, Repr

/-- Remove one base-seven digit, recursively interpreting the remaining higher levels. -/
def parts : ℕ → ℕ → Parts
  | 0, _ => ⟨0, 0, 0⟩
  | L + 1, a =>
    let tail := parts L (a / 7)
    if a % 7 < 3 then ⟨2 * tail.mask, a % 7 + 3 * tail.outer, tail.inner⟩
    else ⟨1 + 2 * tail.mask, tail.outer, (a % 7 - 3) + 4 * tail.inner⟩

/-- Component fits depend only on the input depth, even for an unbounded argument. -/
theorem parts_bounds (L a : ℕ) :
    (parts L a).mask < 2 ^ L ∧ (parts L a).outer < 3 ^ L ∧ (parts L a).inner < 4 ^ L := by
  induction L generalizing a with
  | zero => simp [parts]
  | succ L ih =>
    obtain ⟨hm, ho, hi⟩ := ih (a / 7)
    have hd : a % 7 < 7 := Nat.mod_lt _ (by decide)
    rw [parts]
    split <;> dsimp only
    · simp only [pow_succ]
      constructor
      · omega
      constructor <;> omega
    · simp only [pow_succ]
      constructor
      · omega
      constructor <;> omega

/-- A fixed number of digits, so that zero digits at the end are retained. -/
def sevenDigits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | L + 1, a => a % 7 :: sevenDigits L (a / 7)

/-- These are exactly the digits in Mathlib's finite-function numbering. -/
theorem sevenDigits_eq_ofFn (L a : ℕ) :
    sevenDigits L a = List.ofFn (fun i : Fin L => a / 7 ^ i.val % 7) := by
  induction L generalizing a with
  | zero => simp [sevenDigits]
  | succ L ih =>
    rw [sevenDigits, ih, List.ofFn_succ]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ, pow_succ',
      ← Nat.div_div_eq_div_mul]

/-- The native indices are precisely the binary mask and the two compressed digit lists. -/
theorem parts_lists (L a : ℕ) :
    (parts L a).mask = Nat.ofDigits 2 ((sevenDigits L a).map fun d => if d < 3 then 0 else 1) ∧
      (parts L a).outer = Nat.ofDigits 3 ((sevenDigits L a).filter fun d => d < 3) ∧
      (parts L a).inner = Nat.ofDigits 4
        (((sevenDigits L a).filter fun d => ¬d < 3).map fun d => d - 3) := by
  induction L generalizing a with
  | zero => simp [parts, sevenDigits]
  | succ L ih =>
    obtain ⟨hm, ho, hi⟩ := ih (a / 7)
    by_cases hd : a % 7 < 3
    · simp [parts, sevenDigits, hd, Nat.ofDigits, hm, ho, hi]
    · have hg : 3 ≤ a % 7 := by omega
      simp [parts, sevenDigits, hd, hg, Nat.ofDigits, hm, ho, hi]

end Cslib.Algorithms.MatrixMultiplication.Schonhage.BandDigits
