/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.ZipTransducer
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison

/-! Zip transducers: semantics on concrete words, the machine bound on a concrete input, and the
linear comparison certificate instantiated on concrete numbers. -/

@[expose] public section
namespace ComplexityTests.ZipTransducer
open Turing.MultiTapeTM

/-- Bitwise disjunction of two words, padding the shorter one with zeros. -/
def orZip : ZipTransducer Unit where
  q₀ := ()
  step _ x := ((), [x.1.getD false || x.2.getD false])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- Emits the number of digits by which the first word is longer, in unary, then a marker; it
exercises a state that changes when only one word has digits left. -/
def longerZip : ZipTransducer Bool where
  q₀ := false
  step _ x := (x.2.isNone, if x.2.isNone then [true] else [])
  final b := [b, false]
  length_step_le _ x := by cases x.2 <;> simp
  length_final_le _ := by simp

-- The semantics pads the shorter word and runs in lockstep, in both directions.
example : orZip.run () [true, false] [false, false, true] = [true, false, true] := by
  simp [orZip]

example : orZip.run () [false, false, true] [] = [false, false, true] := by
  simp [orZip]

example : longerZip.run false [true, true, true] [false] = [true, true, true, false] := by
  simp [longerZip]

example : longerZip.run false [] [false, true] = [false, false] := by
  simp [longerZip]

-- The machine on `frame [true, false] ++ [false, false, true]`: the input has length `8`, so the
-- run takes at most `25` steps, and the work head visits the four cells `-1, 0, 1, 2`.
example : orZip.toTM.ComputesInTimeAndSpace (frame [true, false] ++ [false, false, true])
    [true, false, true] 25 4 := by
  have h := orZip.computesInTimeAndSpace_toTM [true, false] [false, false, true]
  simp only [List.length_append, length_frame, List.length_cons, List.length_nil] at h
  simpa [orZip] using h

-- The linear comparison certificate on `(5, 6)`: `encPair encNat encNat (5, 6)` has length
-- `2 * 3 + 1 + 3 = 10`, so some machine outputs `[true]` within `31` steps and `5` cells.
example : ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (tm : Turing.MultiTapeTM k Bool Q),
    tm.ComputesInTimeAndSpace (encPair encNat encNat (5, 6)) [true] 31 5 := by
  obtain ⟨k, Q, hQ, tm, h⟩ := computableInTimeAndSpace_natLt
  have hb5 : Nat.bits 5 = [true, false, true] := by
    rw [show 5 = Nat.bit true 2 from rfl, Nat.bits_append_bit _ _ (by simp),
      show 2 = Nat.bit false 1 from rfl, Nat.bits_append_bit _ _ (by simp), Nat.one_bits]
  have hb6 : Nat.bits 6 = [false, true, true] := by
    rw [show 6 = Nat.bit false 3 from rfl, Nat.bits_append_bit _ _ (by simp),
      show 3 = Nat.bit true 1 from rfl, Nat.bits_append_bit _ _ (by simp), Nat.one_bits]
  refine ⟨k, Q, hQ, tm, ?_⟩
  simpa [encNat_apply, encBool_apply, hb5, hb6, length_frame] using h (5, 6)

-- The comparison is correct on both sides, including equal operands.
example : ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (tm : Turing.MultiTapeTM k Bool Q),
    tm.Computes (encPair encNat encNat (6, 5)) [false] ∧
      tm.Computes (encPair encNat encNat (6, 6)) [false] ∧
      tm.Computes (encPair encNat encNat (0, 1)) [true] := by
  obtain ⟨k, Q, hQ, tm, h⟩ := computableInTimeAndSpace_natLt
  exact ⟨k, Q, hQ, tm, (h (6, 5)).1, (h (6, 6)).1, (h (0, 1)).1⟩

end ComplexityTests.ZipTransducer
