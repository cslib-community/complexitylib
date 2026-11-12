/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Decrement
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordUpdate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork

/-!
# In-place binary decrement with prefix-sensitive time

The borrow scanner flips initial zero digits on one work tape, flips the first one and stops.
It leaves the remaining suffix untouched. If it reaches the blank at the right end, it reports
underflow; thus the caller need not scan the word again to detect zero. One output bit reports
this result (`true` for underflow). The existing work-head rewinder restores the head to zero.

The complete native machine takes at most `2 * decrementVisits w + 3` steps. Its input head
and input tape are untouched. Combined with the zero-bit potential, repeated decrements have a
linear aggregate clock in the number of operations plus the original counter width.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.BitString

namespace BinaryDecrement

/-- The number of initial zeros, excluding the first one or the terminal blank. -/
@[expose] def zeros : List Bool → ℕ
  | [] => 0
  | true :: _ => 0
  | false :: w => zeros w + 1

/-- The scanner inspects all initial zeros and, when present, the first one. -/
theorem zeros_le_visits (w : List Bool) : zeros w ≤ decrementVisits w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [zeros, decrementVisits]; omega

/-- The cursor at which borrowing stops is inside the word or at its right blank. -/
theorem zeros_le_length (w : List Bool) : zeros w ≤ w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [zeros]; omega

/-- The scanner preserves the unvisited suffix and emits whether borrowing reached a blank. -/
@[expose] def borrow : MultiTapeTM 1 Bool Unit :=
  .ofTr () fun _ _ work => match work 0 with
    | some false => ⟨0, fun _ => (some (some true), 1), none, some ()⟩
    | some true => ⟨0, fun _ => (some (some false), 0), some false, none⟩
    | none => ⟨0, fun _ => (none, 0), some true, none⟩

private def cfg {S : Type} {input : List Bool} (q : Option S) (ip : Fin (input.length + 2))
    (out w : List Bool) (p : ℕ) : Cfg 1 Bool S input :=
  ⟨q, ip, fun _ => tapeOfList w, fun _ => (p : ℤ), out⟩

private theorem tape_update (pre suffix : List Bool) (b b' : Bool) :
    Function.update (tapeOfList (pre ++ b :: suffix)) (pre.length : ℤ) (some b') =
      tapeOfList (pre ++ b' :: suffix) := by
  rw [← tapeOfList_set _ (by simp), List.set_append_right _ _ le_rfl]
  simp

/-- The borrow scan never touches any digit after the first one. It also works after an already
processed prefix, which is what permits induction without copying that prefix. -/
private theorem runFrom_borrow {input : List Bool} (ip : Fin (input.length + 2))
    (out pre w : List Bool) :
    borrow.runFrom (cfg (some ()) ip out (pre ++ w) pre.length) (zeros w + 1) =
      cfg none ip (out ++ [!w.contains true]) (pre ++ decrement w) (pre.length + zeros w) := by
  induction w generalizing pre with
  | nil =>
    simp [zeros, decrement, runFrom, step_of_state, tr_ofTr,
      borrow, cfg, Action.apply, Cfg.workTapeSymbols]
  | cons b w ih =>
    cases b with
    | true =>
      simp [zeros, decrement, runFrom, step_of_state, tr_ofTr,
        borrow, cfg, Action.apply, Cfg.workTapeSymbols, tape_update]
    | false =>
      have hs : borrow.step (cfg (some ()) ip out (pre ++ false :: w) pre.length) =
          cfg (some ()) ip out ((pre ++ [true]) ++ w) (pre ++ [true]).length := by
        simp [step_of_state, tr_ofTr, borrow, cfg, Action.apply, Cfg.workTapeSymbols,
          tape_update, List.append_assoc]
      rw [show zeros (false :: w) + 1 = zeros w + 1 + 1 by simp [zeros],
        runFrom, Function.iterate_succ_apply, hs, ← runFrom, ih]
      simp [cfg, zeros, decrement, List.append_assoc, Nat.add_assoc, Int.add_comm]

end BinaryDecrement

/-- Decrement a fixed-width binary word in place, emit an underflow bit, and restore the work
head to zero. The input head is never moved. -/
@[expose] noncomputable def binaryDecrement := BinaryDecrement.borrow.seq (rewindWork Bool)

/-- The complete native decrement runs in twice the zero-prefix length plus three steps.
It emits `true` exactly when the initial word was zero, including the empty word. -/
theorem runFrom_binaryDecrement {input : List Bool} (ip : Fin (input.length + 2))
    (out w : List Bool) :
    binaryDecrement.runFrom
      ⟨some binaryDecrement.q₀, ip, fun _ => tapeOfList w, fun _ => 0, out⟩
      (2 * BinaryDecrement.zeros w + 3) =
      ⟨none, ip, fun _ => tapeOfList (decrement w), fun _ => 0, out ++ [!w.contains true]⟩ := by
  have h₀ := BinaryDecrement.runFrom_borrow ip out [] w
  have h₁ := runFrom_rewindWork_none ip (tapeOfList (decrement w))
    (out ++ [!w.contains true]) rfl
    (show BinaryDecrement.zeros w ≤ (decrement w).length by
      rw [length_decrement]; exact BinaryDecrement.zeros_le_length w)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h₀
  have h := runFrom_seq (tm₁ := rewindWork Bool) h₀ rfl
    (by simpa [BinaryDecrement.cfg, Cfg.withState] using h₁) rfl
  have ht : 2 * BinaryDecrement.zeros w + 3 =
      BinaryDecrement.zeros w + 1 + (BinaryDecrement.zeros w + 2) := by omega
  rw [ht]
  exact h

/-- The emitted flag detects underflow from the same scan that updates the digits. -/
theorem BinaryDecrement.underflow_eq (w : List Bool) :
    (!w.contains true) = decide (lsbValue w = 0) := by
  by_cases h : true ∈ w
  · have hp := lsbValue_pos_of_true_mem h
    simp [h, Nat.ne_of_gt hp]
  · have hz := lsbValue_eq_zero_of_true_not_mem h
    simp [h, hz]

/-- A prefix-visit bound for the same native machine, including rewinding and the underflow bit. -/
theorem runFrom_binaryDecrement_visits {input : List Bool} (ip : Fin (input.length + 2))
    (out w : List Bool) :
    binaryDecrement.runFrom
      ⟨some binaryDecrement.q₀, ip, fun _ => tapeOfList w, fun _ => 0, out⟩
      (2 * decrementVisits w + 3) =
      ⟨none, ip, fun _ => tapeOfList (decrement w), fun _ => 0, out ++ [!w.contains true]⟩ := by
  have h := runFrom_binaryDecrement ip out w
  rw [runFrom_eq_of_halt binaryDecrement _ (τ := 2 * BinaryDecrement.zeros w + 3)
    (by have := BinaryDecrement.zeros_le_visits w; omega) (by rw [h]), h]

/-- The sum of the exact native subroutine clocks along a sequence of decrements. -/
@[expose] def BinaryDecrement.totalClock : ℕ → List Bool → ℕ
  | 0, _ => 0
  | q + 1, w => 2 * zeros w + 3 + totalClock q (decrement w)

/-- Exact native clocks are bounded by twice the visited digits plus three steps per call. -/
theorem BinaryDecrement.totalClock_le_visits (q : ℕ) (w : List Bool) :
    totalClock q w ≤ 2 * decrementCost q w + 3 * q := by
  induction q generalizing w with
  | zero => simp [totalClock, decrementCost]
  | succ q ih =>
    have hs := zeros_le_visits w
    have hr := ih (decrement w)
    simp only [totalClock, decrementCost]
    omega

/-- The native subroutine clocks telescope to a linear budget; no normalization or full-word
copy is charged at every call. A surrounding loop must add its own dispatch time. -/
theorem BinaryDecrement.totalClock_le (q : ℕ) (w : List Bool) :
    totalClock q w ≤ 7 * q + 2 * w.length := by
  have hc := totalClock_le_visits q w
  have ha := decrementCost_le q w
  omega

/-- Two counter decrements per selector level still have linear aggregate native clocks. -/
theorem BinaryDecrement.totalClock_le_of_le_two_mul {q levels : ℕ}
    (hq : q ≤ 2 * levels) (w : List Bool) :
    totalClock q w ≤ 14 * levels + 2 * w.length := by
  have := totalClock_le q w
  omega

end Turing.MultiTapeTM
