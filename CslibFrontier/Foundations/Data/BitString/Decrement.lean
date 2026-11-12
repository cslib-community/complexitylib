/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Counter
import Mathlib.Data.List.Count

/-!
# Amortized prefix work for binary decrement

A fixed-width little-endian decrement flips the initial zero bits and the first one. Its
prefix-visit cost is bounded by a potential counting zero bits. Across `q` decrements the total
number of inspected digits is at most `2*q + width`, even when the word wraps around at zero.
For a selector that decrements its bit position at most twice per level, this is linear in the
number of levels plus the initial bit width.

These are word semantics and exact digit-visit counts, not yet a native Turing-machine runtime
certificate. In particular, they do not apply to a transducer that copies the entire word on
every decrement. A native implementation must stop at the first one and preserve the unvisited
suffix in place. Wraparound is allowed here; consumers requiring nonnegative counters must
separately guard against underflow.
-/

public section

namespace Cslib.BitString

/-- Fixed-width little-endian decrement, discarding the final borrow. -/
@[expose] def decrement : List Bool → List Bool
  | [] => []
  | true :: w => false :: w
  | false :: w => true :: decrement w

/-- The number of digits inspected until the first one, or the end of the word. -/
@[expose] def decrementVisits : List Bool → ℕ
  | [] => 0
  | true :: _ => 1
  | false :: w => 1 + decrementVisits w

/-- Decrement preserves the fixed word width. -/
@[simp] theorem length_decrement (w : List Bool) : (decrement w).length = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [decrement, ih]

/-- Without underflow the word operation is ordinary predecessor. -/
theorem lsbValue_decrement (w : List Bool) (h : 0 < lsbValue w) :
    lsbValue (decrement w) = lsbValue w - 1 := by
  induction w with
  | nil => simp [lsbValue] at h
  | cons b w ih =>
    cases b with
    | false =>
      have hw : 0 < lsbValue w := by simp only [lsbValue, Bool.toNat_false] at h; omega
      simp only [decrement, lsbValue, Bool.toNat_true, Bool.toNat_false, ih hw]
      omega
    | true => simp [decrement, lsbValue]

/-- A sequence of decrements that does not pass zero performs natural subtraction. -/
theorem lsbValue_iterate_decrement (q : ℕ) (w : List Bool) (h : q ≤ lsbValue w) :
    lsbValue (decrement^[q] w) = lsbValue w - q := by
  induction q generalizing w with
  | zero => simp
  | succ q ih =>
    have hd := lsbValue_decrement w (by omega)
    rw [Function.iterate_succ_apply, ih (decrement w) (by rw [hd]; omega), hd]
    omega

/-- Each visited zero pays for its own flip; the first one adds at most two units of charge. -/
theorem decrementVisits_add_count_false_le (w : List Bool) :
    decrementVisits w + (decrement w).count false ≤ 2 + w.count false := by
  induction w with
  | nil => simp [decrementVisits, decrement]
  | cons b w ih => cases b <;> simp [decrementVisits, decrement] <;> omega

/-- The sum of digit visits across successive decrements. -/
@[expose] def decrementCost : ℕ → List Bool → ℕ
  | 0, _ => 0
  | q + 1, w => decrementVisits w + decrementCost q (decrement w)

/-- The zero-bit potential telescopes through an arbitrary number of decrements. -/
theorem decrementCost_add_count_false_le (q : ℕ) (w : List Bool) :
    decrementCost q w + (decrement^[q] w).count false ≤ 2 * q + w.count false := by
  induction q generalizing w with
  | zero => simp [decrementCost]
  | succ q ih =>
    have hstep := decrementVisits_add_count_false_le w
    have hrest := ih (decrement w)
    simp only [decrementCost, Function.iterate_succ_apply]
    omega

/-- All initial potential fits in the initial word width. -/
theorem decrementCost_le (q : ℕ) (w : List Bool) :
    decrementCost q w ≤ 2 * q + w.length := by
  have h := decrementCost_add_count_false_le q w
  have hz : w.count false ≤ w.length := List.count_le_length
  omega

/-- At most two decrements per tree level incur linear total prefix work. -/
theorem decrementCost_le_of_le_two_mul {q levels : ℕ} (hq : q ≤ 2 * levels) (w : List Bool) :
    decrementCost q w ≤ 4 * levels + w.length := by
  have := decrementCost_le q w
  omega

/-- Scanning each visited digit in both directions, plus a fixed overhead per decrement, remains
linear. This converts digit visits to a prospective cursor-motion budget; it does not assert a
native machine implementation. -/
theorem decrement_roundTrip_budget_le (q overhead : ℕ) (w : List Bool) :
    2 * decrementCost q w + overhead * q ≤ (4 + overhead) * q + 2 * w.length := by
  have := decrementCost_le q w
  rw [Nat.add_mul]
  omega

end Cslib.BitString
