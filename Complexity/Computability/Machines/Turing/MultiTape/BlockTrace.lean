/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Native time-block traces

These original native-model lemmas are prerequisites for the active-block construction in
[Williams2025], arXiv:2502.17779v1, §3.4. They use the actual
multitape machine and its stationary-after-halting run. They do not construct a computation
graph, simulate input access, or prove a space bound.

A finite work-tape window retains `Option Symbol`: blank and a written zero are different.
`blockEmitted` retains only the symbols emitted during a block, not the preceding output.
The radius-duration window below is deliberately a locality envelope, not a claim about the
optimal number of aligned active blocks or their encoded bit length.

The active-block route was proposed in worker-crei-dc679113’s M0 design for issue #888;
these local trace lemmas do not implement its pending graph/packing obligations.

## Main definitions

* `Turing.MultiTapeTM.blockStart`: the native configuration at a block boundary.
* `Turing.MultiTapeTM.blockDuration`: a block clipped to a finite time horizon.
* `Turing.Cfg.workWindow`: a finite window around each native work-tape head.
* `Turing.MultiTapeTM.blockEmitted`: output emitted during a run segment.

## Main results

* `Turing.MultiTapeTM.blockStart_succ`: exact composition of adjacent blocks.
* `Turing.MultiTapeTM.runFrom_blockDuration`: exact clipped-final-block composition.
* `Turing.MultiTapeTM.workTapePos_runFrom_abs_sub_le`: local head displacement.
* `Turing.MultiTapeTM.workTapes_runFrom_eq_of_outside_window`: unchanged exterior cells.
* `Turing.MultiTapeTM.output_eq_append_blockEmitted`: separate old output from new output.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A finite window of exactly `2 * radius + 1` cells per tape, centered at its starting head.
No previous output word is stored here. -/
def Cfg.workWindow (cfg : Cfg k Symbol State input) (radius : ℕ) :
    Fin k → Fin (2 * radius + 1) → Option Symbol :=
  fun tape j => cfg.workTapes tape (cfg.workTapePos tape - radius + j.val)

/-- The middle entry is the actual scanned cell, including its blank marker. -/
theorem Cfg.workWindow_center (cfg : Cfg k Symbol State input) (radius : ℕ) (tape : Fin k) :
    cfg.workWindow radius tape ⟨radius, by omega⟩ = cfg.workTapeSymbols tape := by
  simp [Cfg.workWindow, Cfg.workTapeSymbols]

namespace MultiTapeTM

variable (tm : MultiTapeTM k Symbol State)

/-- The native configuration at the start of zero-indexed time block `index`. -/
noncomputable def blockStart (cfg : Cfg k Symbol State input) (width index : ℕ) :
    Cfg k Symbol State input := tm.runFrom cfg (index * width)

/-- The number of steps left in a block before the finite horizon. A zero width is allowed
and gives an empty block; later aligned-block geometry requires positive width separately. -/
def blockDuration (horizon width index : ℕ) : ℕ := min width (horizon - index * width)

/-- Block zero starts at the supplied configuration, even at width zero. -/
@[simp] theorem blockStart_zero (cfg : Cfg k Symbol State input) (width : ℕ) :
    tm.blockStart cfg width 0 = cfg := by simp [blockStart, runFrom]

/-- Zero-width blocks contain no steps at any horizon. -/
@[simp] theorem blockDuration_zero_width (horizon index : ℕ) :
    blockDuration horizon 0 index = 0 := by simp [blockDuration]

/-- Clipping never increases the chosen block width. -/
theorem blockDuration_le_width (horizon width index : ℕ) :
    blockDuration horizon width index ≤ width := Nat.min_le_left _ _

/-- Adjacent full blocks use exactly the same native run, including halted suffixes. -/
theorem blockStart_succ (cfg : Cfg k Symbol State input) (width index : ℕ) :
    tm.blockStart cfg width (index + 1) = tm.runFrom (tm.blockStart cfg width index) width := by
  simp only [blockStart, Nat.add_mul, Nat.one_mul, runFrom_add]

/-- A block beginning before the horizon ends exactly at the next boundary or the horizon.
The hypothesis is essential: a block starting after the horizon is not rewound. -/
theorem runFrom_blockDuration (cfg : Cfg k Symbol State input) (horizon width index : ℕ)
    (hstart : index * width ≤ horizon) :
    tm.runFrom (tm.blockStart cfg width index) (blockDuration horizon width index) =
      tm.runFrom cfg (min ((index + 1) * width) horizon) := by
  rw [blockStart, ← runFrom_add]
  congr 1
  simp only [blockDuration, Nat.add_mul, Nat.one_mul]
  omega

/-- At or beyond the horizon there are no remaining steps. -/
theorem blockDuration_eq_zero_of_le (horizon width index : ℕ)
    (h : horizon ≤ index * width) : blockDuration horizon width index = 0 := by
  simp [blockDuration, Nat.sub_eq_zero_of_le h]

/-- The final configuration is included: in `duration` steps a head is within `duration`
cells of its starting position. This holds for negative tape positions and halted prefixes. -/
theorem workTapePos_runFrom_abs_sub_le (cfg : Cfg k Symbol State input)
    (duration : ℕ) (tape : Fin k) :
    |(tm.runFrom cfg duration).workTapePos tape - cfg.workTapePos tape| ≤ (duration : ℤ) := by
  induction duration with
  | zero => simp [runFrom]
  | succ duration ih =>
    rw [runFrom_succ]
    have hs := abs_le.mp (MultiTapeNTM.Step.workTapePos_le
      (step_iff.mpr rfl : tm.Step (tm.runFrom cfg duration) _) tape)
    have hi := abs_le.mp ih
    apply abs_le.mpr
    constructor <;> push_cast <;> omega

/-- A cell outside the closed radius-duration locality envelope is never visited and therefore
retains its contents. In particular, blank cells do not silently become written zeroes. -/
theorem workTapes_runFrom_eq_of_outside_window (cfg : Cfg k Symbol State input)
    (duration : ℕ) (tape : Fin k) (position : ℤ)
    (hout : (duration : ℤ) < |position - cfg.workTapePos tape|) :
    (tm.runFrom cfg duration).workTapes tape position = cfg.workTapes tape position := by
  apply workTapes_runFrom_eq_of_notMem_visitedByTapeHead
  intro hmem
  obtain ⟨j, hj, rfl⟩ := MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.mp hmem
  have hpos := tm.workTapePos_runFrom_abs_sub_le cfg j tape
  omega

/-- The output of a segment consists of the existing prefix and at most one new symbol per
native step. No assumption of halting is needed. -/
theorem exists_output_suffix (cfg : Cfg k Symbol State input) (duration : ℕ) :
    ∃ emitted : List Symbol, (tm.runFrom cfg duration).output = cfg.output ++ emitted ∧
      emitted.length ≤ duration := by
  induction duration with
  | zero => exact ⟨[], by simp [runFrom], by simp⟩
  | succ duration ih =>
    obtain ⟨emitted, heq, hlen⟩ := ih
    rw [runFrom_succ]
    cases hstate : (tm.runFrom cfg duration).state with
    | none => exact ⟨emitted, by rw [step_of_halt hstate, heq], by omega⟩
    | some q =>
      let action := tm.tr q (tm.runFrom cfg duration).inputSymbol
        (tm.runFrom cfg duration).workTapeSymbols
      refine ⟨emitted ++ action.output.toList, ?_, ?_⟩
      · rw [step_of_state hstate, Action.apply_output, heq, List.append_assoc]
      · have h := Option.length_toList_le (o := action.output)
        simp only [List.length_append]
        omega

/-- Only the output newly emitted by this segment. The old prefix is explicitly discarded. -/
noncomputable def blockEmitted (cfg : Cfg k Symbol State input) (duration : ℕ) : List Symbol :=
  (tm.runFrom cfg duration).output.drop cfg.output.length

/-- Reconstruct the native output from its existing prefix and the segment-only suffix. -/
theorem output_eq_append_blockEmitted (cfg : Cfg k Symbol State input) (duration : ℕ) :
    (tm.runFrom cfg duration).output = cfg.output ++ tm.blockEmitted cfg duration := by
  obtain ⟨emitted, heq, _⟩ := tm.exists_output_suffix cfg duration
  simp only [blockEmitted, heq, List.drop_left]

/-- The suffix payload is at most the segment duration, regardless of the old prefix length. -/
theorem length_blockEmitted_le (cfg : Cfg k Symbol State input) (duration : ℕ) :
    (tm.blockEmitted cfg duration).length ≤ duration := by
  have h := tm.length_output_runFrom_le cfg duration
  simp only [blockEmitted, List.length_drop]
  omega

/-- Halting is stationary, including all output and work-tape contents. -/
theorem blockStart_eq_of_halted (cfg : Cfg k Symbol State input) (hhalt : cfg.Halted)
    (width index : ℕ) : tm.blockStart cfg width index = cfg := by
  simpa only [blockStart, runFrom, Function.iterate_zero_apply] using
    tm.runFrom_eq_of_halt cfg (τ := 0) (t := index * width) (Nat.zero_le _) hhalt

end MultiTapeTM
end Turing
