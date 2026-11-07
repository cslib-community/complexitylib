/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas
import Mathlib.Tactic.FinCases

/-!
# Counted transfer of a local tape block

`Turing.MultiTapeTM.copyBlock` copies a block from work tape `0` to work tape `1`, using a
unary counter on work tape `2`. Each nonblank counter cell authorizes one transfer, including
a blank source cell, and is erased. All three heads advance together. The first blank counter
cell halts the machine without moving a head. The optional erasure mode also clears the source.

The machine has one control state. Its contract allows arbitrary initial head positions and
preserves all cells outside the three transferred segments. The counter cell immediately after
its segment must be blank; all other exterior contents are arbitrary. Each head visits only its
segment and its right boundary. A block of length `n` takes exactly `n + 1` transitions and visits
at most `3 * (n + 1)` work-tape cells. These are native machine resources, independent of the total
stored data.

This is a local block primitive for buffered simulations. It does not by itself implement a
buffer layout, its refill schedule, or a logarithmic-overhead universal simulator.

## Main definitions

* `Turing.MultiTapeTM.copyBlock`: the counted copy or move machine.
* `Turing.MultiTapeTM.CopyBlock.writeBlock`: replacement of a finite interval of a tape.
* `Turing.MultiTapeTM.CopyBlock.finish`: the exact final configuration.

## Main results

* `Turing.MultiTapeTM.CopyBlock.runFrom_copyBlock`: the exact resulting configuration.
* `Turing.MultiTapeTM.CopyBlock.haltsAt_copyBlock`: the exact number of transitions.
* `Turing.MultiTapeTM.CopyBlock.space_copyBlock_le`: the visited-cell bound.
-/

public section

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- Copy from tape `0` to tape `1` while erasing a unary counter on tape `2`.
If `erase` is true, also erase each copied source cell. Physical blanks in the source are copied
as blanks; only the counter determines where the block ends. -/
@[expose] def copyBlock (erase : Bool) : MultiTapeTM 3 Symbol Unit :=
  ofTr () fun _ _ work =>
    match work 2 with
    | none =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }
    | some _ =>
      { inputTape := 0
        workTapes := fun i =>
          (if i = 0 then (if erase then some none else none)
            else if i = 1 then some (work 0) else some none, 1)
        output := none
        state := some () }

namespace CopyBlock

/-- Replace exactly the cells in `[start, start + count)` by `values`, indexed relative to
`start`, preserving the tape everywhere else. -/
@[expose] def writeBlock (tape : ℤ → Option Symbol) (start : ℤ)
    (values : ℤ → Option Symbol) (count : ℕ) : ℤ → Option Symbol :=
  fun z => if start ≤ z ∧ z < start + count then values (z - start) else tape z

@[simp] theorem writeBlock_zero (tape : ℤ → Option Symbol) (start : ℤ)
    (values : ℤ → Option Symbol) : writeBlock tape start values 0 = tape := by
  funext z
  simp only [writeBlock, Nat.cast_zero, add_zero]
  exact ite_eq_right (by omega)

/-- A cell inside the replacement interval contains its specified value. -/
theorem writeBlock_apply (tape : ℤ → Option Symbol) (start : ℤ)
    (values : ℤ → Option Symbol) {count j : ℕ} (hj : j < count) :
    writeBlock tape start values count (start + j) = values j := by
  rw [writeBlock, ite_eq_left (by omega)]
  congr 1
  omega

/-- Exterior cells are unchanged. -/
theorem writeBlock_apply_of_outside (tape : ℤ → Option Symbol) (start : ℤ)
    (values : ℤ → Option Symbol) (count : ℕ) {z : ℤ}
    (hz : z < start ∨ start + count ≤ z) : writeBlock tape start values count z = tape z :=
  ite_eq_right (by omega)

@[simp] theorem writeBlock_at_end (tape : ℤ → Option Symbol) (start : ℤ)
    (values : ℤ → Option Symbol) (count : ℕ) :
    writeBlock tape start values count (start + count) = tape (start + count) :=
  writeBlock_apply_of_outside tape start values count (Or.inr le_rfl)

private theorem writeBlock_succ (tape : ℤ → Option Symbol) (start : ℤ)
    (values : ℤ → Option Symbol) (count : ℕ) :
    Function.update (writeBlock tape start values count) (start + count) (values count) =
      writeBlock tape start values (count + 1) := by
  funext z
  by_cases hz : z = start + count
  · subst z
    rw [Function.update_self, writeBlock, ite_eq_left (by omega)]
    congr 1
    omega
  · rw [Function.update_of_ne hz]
    simp only [writeBlock]
    have hiff : (start ≤ z ∧ z < start + (count : ℤ)) ↔
        (start ≤ z ∧ z < start + ((count + 1 : ℕ) : ℤ)) := by omega
    simp only [hiff]

/-- The tapes after `count` transfers, before or after the final halting transition. -/
@[expose] def tapes (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ) :
    Fin 3 → ℤ → Option Symbol :=
  fun i => if i = 0 then
      if erase then writeBlock (cfg.workTapes 0) (cfg.workTapePos 0) (fun _ => none) count
      else cfg.workTapes 0
    else if i = 1 then
      writeBlock (cfg.workTapes 1) (cfg.workTapePos 1)
        (fun j => cfg.workTapes 0 (cfg.workTapePos 0 + j)) count
    else writeBlock (cfg.workTapes 2) (cfg.workTapePos 2) (fun _ => none) count

/-- The configuration after `count` transfers, still in the running state. -/
@[expose] def progress (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ) :
    Cfg 3 Symbol Unit input :=
  ⟨some (), cfg.inputPos, tapes erase cfg count, fun i => cfg.workTapePos i + count, cfg.output⟩

/-- The final configuration: the transferred segments, erased counter, shifted heads and
unchanged input position and output. -/
@[expose] def finish (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ) :
    Cfg 3 Symbol Unit input :=
  (progress erase cfg count).withState none

@[simp] theorem progress_zero (erase : Bool) (cfg : Cfg 3 Symbol Unit input)
    (hstate : cfg.state = some ()) : progress erase cfg 0 = cfg := by
  refine Cfg.ext hstate.symm rfl ?_ ?_ rfl
  · funext i
    fin_cases i <;> simp [progress, tapes]
  · funext i
    simp [progress]

private theorem source_at_progress (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ) :
    (progress erase cfg count).workTapeSymbols 0 =
      cfg.workTapes 0 (cfg.workTapePos 0 + count) := by
  cases erase <;> simp [progress, tapes, Cfg.workTapeSymbols]

private theorem counter_at_progress (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ) :
    (progress erase cfg count).workTapeSymbols 2 =
      cfg.workTapes 2 (cfg.workTapePos 2 + count) := by
  simp [progress, tapes, Cfg.workTapeSymbols]

private theorem step_progress (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ)
    (hcount : cfg.workTapes 2 (cfg.workTapePos 2 + count) ≠ none) :
    (copyBlock erase).step (progress erase cfg count) = progress erase cfg (count + 1) := by
  rw [step_of_state (by rfl)]
  simp only [copyBlock, tr_ofTr, counter_at_progress, source_at_progress]
  cases hc : cfg.workTapes 2 (cfg.workTapePos 2 + count) with
  | none => exact False.elim (hcount hc)
  | some a =>
    refine Cfg.ext rfl ?_ ?_ ?_ ?_
    · simp [Action.apply, progress]
    · funext i
      fin_cases i
      · cases erase <;> simp [Action.apply, progress, tapes, writeBlock_succ]
      · simp only [Action.apply, progress, tapes]
        simp [writeBlock_succ]
      · simp [Action.apply, progress, tapes, writeBlock_succ]
    · funext i
      simp [Action.apply, progress, Nat.cast_add, add_assoc]
    · simp [Action.apply, progress]

/-- Each nonblank counter cell permits one native transfer. -/
theorem runFrom_progress (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ)
    (hstate : cfg.state = some ())
    (hcount : ∀ j < count, cfg.workTapes 2 (cfg.workTapePos 2 + j) ≠ none) :
    (copyBlock erase).runFrom cfg count = progress erase cfg count := by
  induction count with
  | zero => simpa only [runFrom, Function.iterate_zero, id_eq] using
      (progress_zero erase cfg hstate).symm
  | succ count ih =>
    rw [runFrom_succ, ih (fun j hj => hcount j (by omega))]
    exact step_progress erase cfg count (hcount count (by omega))

/-- The exact result of transferring a counted block. Only the counter must be nonblank:
the copied block may contain any mixture of symbols and physical blanks. -/
theorem runFrom_copyBlock (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ)
    (hstate : cfg.state = some ())
    (hcount : ∀ j < count, cfg.workTapes 2 (cfg.workTapePos 2 + j) ≠ none)
    (hend : cfg.workTapes 2 (cfg.workTapePos 2 + count) = none) :
    (copyBlock erase).runFrom cfg (count + 1) = finish erase cfg count := by
  rw [runFrom_succ, runFrom_progress erase cfg count hstate hcount, step_of_state (by rfl)]
  simp only [copyBlock, tr_ofTr, counter_at_progress, hend]
  simp [Action.apply, finish, progress, Cfg.withState]

/-- The first blank counter cell is the halting step, so the running time is exactly
`count + 1`, including when the counter is initially blank. -/
theorem haltsAt_copyBlock (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ)
    (hstate : cfg.state = some ())
    (hcount : ∀ j < count, cfg.workTapes 2 (cfg.workTapePos 2 + j) ≠ none)
    (hend : cfg.workTapes 2 (cfg.workTapePos 2 + count) = none) :
    (copyBlock erase).HaltsAt cfg (count + 1) := by
  constructor
  · rw [runFrom_copyBlock erase cfg count hstate hcount hend]
    rfl
  · intro j hj
    rw [runFrom_progress erase cfg j hstate (fun i hi => hcount i (by omega))]
    simp [Cfg.Halted, progress]

/-- Every visited head position lies in the transferred interval together with its right
boundary. The final halting transition visits no additional cell. -/
theorem workTapePos_runFrom (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ)
    (hstate : cfg.state = some ())
    (hcount : ∀ j < count, cfg.workTapes 2 (cfg.workTapePos 2 + j) ≠ none)
    (hend : cfg.workTapes 2 (cfg.workTapePos 2 + count) = none) (time : ℕ) (i : Fin 3) :
    ((copyBlock erase).runFrom cfg time).workTapePos i = cfg.workTapePos i + min time count := by
  by_cases ht : time ≤ count
  · rw [runFrom_progress erase cfg time hstate (fun j hj => hcount j (by omega)),
      Nat.min_eq_left ht]
    rfl
  · have hhalt := haltsAt_copyBlock erase cfg count hstate hcount hend
    rw [hhalt.runFrom_eq (by omega), runFrom_copyBlock erase cfg count hstate hcount hend,
      Nat.min_eq_right (by omega)]
    rfl

/-- A native run path for a length-`count` block visits at most `3 * (count + 1)` work-tape
cells, independent of the initial heads and of data outside the three touched intervals. -/
theorem space_copyBlock_le (erase : Bool) (cfg : Cfg 3 Symbol Unit input) (count : ℕ)
    (hstate : cfg.state = some ())
    (hcount : ∀ j < count, cfg.workTapes 2 (cfg.workTapePos 2 + j) ≠ none)
    (hend : cfg.workTapes 2 (cfg.workTapePos 2 + count) = none) :
    (MultiTapeNTM.RunPath.ofDeterministic (copyBlock erase) cfg (count + 1)).space ≤
      3 * (count + 1) := by
  classical
  apply le_trans (MultiTapeNTM.RunPath.space_le_sum_card _
    (S := fun i => Finset.Icc (cfg.workTapePos i) (cfg.workTapePos i + count)) ?_)
  · simp [add_assoc]
  · rintro c ⟨t, rfl⟩ i
    change ((copyBlock erase).runFrom cfg t.val).workTapePos i ∈ _
    rw [workTapePos_runFrom erase cfg count hstate hcount hend]
    simp only [Finset.mem_Icc]
    constructor <;> omega

end CopyBlock

end Turing.MultiTapeTM
