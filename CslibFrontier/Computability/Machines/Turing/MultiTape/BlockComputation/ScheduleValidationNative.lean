/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleValidation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Mathlib.Tactic.DeriveFintype

/-!
# Native linear-time validation of movement schedules

A fixed finite controller checks aligned pairs and counts columns modulo the fixed row width.
The schedule and its length are runtime input. No work tape is needed; the final emitted bit
is the executable canonical-input check.
-/

public section

namespace Turing.MultiTapeTM.ScheduleValidation

/-- Pair alignment, column position, and an absorbing invalid-input state. -/
inductive State (k : ℕ)
  /-- Await the first bit of the next movement. -/
  | first : Fin (k + 1) → State k
  /-- Await its second bit, retaining the negative indicator. -/
  | second : Fin (k + 1) → Bool → State k
  /-- An invalid aligned pair was encountered. -/
  | reject : State k
  deriving Fintype

private def advance {k : ℕ} (c : Fin (k + 1)) : Fin (k + 1) :=
  if h : c.val < k then ⟨c.val + 1, by omega⟩ else 0

/-- Read once, with no intermediate output; emit the validity bit at the right blank. -/
def reader (k : ℕ) : Transducer Bool (State k) where
  q₀ := .first 0
  step s b := (match s with
    | .first c => .second c b
    | .second c a => if a && b then .reject else .first (advance c)
    | .reject => .reject, [])
  final s := [match s with | .first c => decide (c.val = 0) | _ => false]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem run_reject (k : ℕ) (word : List Bool) :
    (reader k).run .reject word = [false] := by
  induction word with
  | nil => rfl
  | cons b word ih => simpa only [Transducer.run_cons, reader, List.nil_append] using ih

private theorem advance_mod {k : ℕ} (c : Fin (k + 1)) (n : ℕ) :
    (2 * (advance c).val + n) % (2 * (k + 1)) =
      (2 * c.val + (n + 2)) % (2 * (k + 1)) := by
  unfold advance
  split_ifs with h
  · congr 1; simp only; omega
  · have hc : c.val = k := by omega
    simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, hc]
    rw [show 2 * k + (n + 2) = 2 * (k + 1) + n by omega, Nat.add_mod]
    simp

private theorem run_first (k : ℕ) : ∀ (word : List Bool) (c : Fin (k + 1)),
    (reader k).run (.first c) word =
      [ScheduleBits.validPairs word &&
        decide ((2 * c.val + word.length) % (2 * (k + 1)) = 0)]
  | [], c => by
    have hc : 2 * c.val < 2 * (k + 1) := by omega
    simp [Transducer.run, reader, ScheduleBits.validPairs, Nat.mod_eq_of_lt hc]
  | [a], c => by
    simp [Transducer.run, reader, ScheduleBits.validPairs]
  | a :: b :: rest, c => by
    have hm := advance_mod c rest.length
    have hr := run_first k rest (advance c)
    change (reader k).run (if a && b then .reject else .first (advance c)) rest = _
    cases a <;> cases b <;>
      simp [ScheduleBits.validPairs, ScheduleBits.decodePair, run_reject, hr, hm, Nat.add_assoc]

/-- The finite controller computes exactly the canonical raw-table checker. -/
theorem run_eq_validate (k : ℕ) (word : List Bool) :
    (reader k).run (reader k).q₀ word = [ScheduleBits.validate k word] := by
  simpa [reader, ScheduleBits.validate, Bool.and_comm] using run_first k word 0

/-- The actual native zero-work-tape machine checks the full raw input in linear time. -/
theorem computes_validate (k : ℕ) (word : List Bool) :
    (reader k).toTM.ComputesInTimeAndSpace word [ScheduleBits.validate k word]
      (2 * word.length + 3) 0 := by
  rw [← run_eq_validate]
  exact (reader k).computesInTimeAndSpace_toTM word

end Turing.MultiTapeTM.ScheduleValidation
