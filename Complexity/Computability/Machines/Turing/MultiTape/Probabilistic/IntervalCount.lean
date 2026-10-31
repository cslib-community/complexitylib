/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalSimulation
public import Complexity.Foundations.Data.BitString.Enumeration

/-!
# Interval counts on list data

The interval tensor of the block-counting networks of #1833
(`Turing.MultiTapePTM.intervalCount`) takes a control record with offsets in `ZMod b` and window
contents indexed by `ZMod b`. This module restates it on plain data, the form in which a
polynomial-time construction of the networks computes it: a control record with offsets as
natural numbers (`Turing.MultiTapePTM.ControlData`, `Turing.MultiTapePTM.controlData`) and the
window of each work tape as the list of its `3 b` cells (`Turing.MultiTapePTM.windowCells`).

On such data, the finite storage of the embedded window is
`Turing.MultiTapePTM.localStartData`, and the interval condition
(`Turing.MultiTapePTM.LocalIntervalStepData`) compares the state and output track after the
replay, the coordinate of every head with its prescribed block start plus offset, and the cells
of every window with the given lists. Block indices and offsets need no division: a coordinate `z`
has block index `q` and offset `r` modulo `b` exactly when `r < b` and `z = b q + r`. The interval
count (`Turing.MultiTapePTM.localIntervalCount`) counts the coin strings of the enumeration
`Cslib.BitString.enumList b` satisfying the condition, and agrees with the interval tensor
(`Turing.MultiTapePTM.localIntervalCount_eq_intervalCount`).

## Main definitions

* `Turing.MultiTapePTM.ControlData`, `Turing.MultiTapePTM.controlData`: control records on
  plain data.
* `Turing.MultiTapePTM.localStartData`: the finite storage of an embedded window.
* `Turing.MultiTapePTM.LocalCfg.headCoord`, `Turing.MultiTapePTM.LocalCfg.windowCellsAt`: the
  coordinates of the heads and the cells of a window on finite storage.
* `Turing.MultiTapePTM.LocalIntervalStepData`, `Turing.MultiTapePTM.localIntervalCount`: the
  interval condition and the interval count on plain data.

## Main results

* `Turing.MultiTapePTM.localIntervalStepData_iff`: the condition on plain data is the interval
  condition on finite storage.
* `Turing.MultiTapePTM.localIntervalCount_eq_intervalCount`: the count on plain data is the
  interval tensor.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeNTM.ChoiceTable Cslib.Turing

variable {k : ℕ} {State : Type}

/-! ### Plain data -/

/-- A control record on plain data: the state, the offset of every head as a natural number, and
the output track. -/
abbrev ControlData (k : ℕ) (State : Type) := Option State × (Option (Fin k) → ℕ) × OutputTrack

/-- A control record as plain data: its offsets by their values. -/
@[expose] def controlData {b : ℕ} (c : BlockControl k State b) : ControlData k State :=
  (c.1, fun head => (c.2.1 head).val, c.2.2)

/-- The finite storage of the configuration embedded at block indices `J` with the control
record `cIn` and the window cells `wIn` (the `3 b` cells of each window, left to right): each
work tape holds the cells of its window with its head on cell `b + offset`. -/
@[expose] def localStartData (b : ℕ) (input : List Bool) (J : Option (Fin k) → ℤ)
    (cIn : ControlData k State) (wIn : Fin k → List (Option Bool)) : LocalCfg k State where
  state := cIn.1
  inputPos := (inputPosOfCoord input (b * J none + cIn.2.1 none)).val
  workTapes h := BiTape.ofCells (wIn h) (b + cIn.2.1 (some h))
  workTapePos h := b * J (some h) + cIn.2.1 (some h)
  track := cIn.2.2

/-- On the data of a control record and window contents, `localStartData` is `localStart`. -/
theorem localStartData_controlData (b : ℕ) (input : List Bool)
    (J : Option (Fin k) → ℤ) (cIn : BlockControl k State b)
    (wIn : Fin k → Fin 3 → ZMod b → Option Bool) :
    localStartData b input J (controlData cIn) (fun h => windowCells b (wIn h)) =
      localStart b input J cIn wIn := rfl

/-- The coordinate of every head of finite storage: the input position less one for the input
head, and the absolute position for a work head. -/
@[expose] def LocalCfg.headCoord (l : LocalCfg k State) : Option (Fin k) → ℤ
  | none => (l.inputPos : ℤ) - 1
  | some h => l.workTapePos h

/-- The `3 b` cells of the window of work tape `h` around block index `j`, left to right. -/
@[expose] def LocalCfg.windowCellsAt (b : ℕ) (j : ℤ) (l : LocalCfg k State) (h : Fin k) :
    List (Option Bool) :=
  (List.range (3 * b)).map fun c : ℕ =>
    (l.workTapes h).read (b * (j - 1) + (c : ℤ) - l.workTapePos h)

/-! ### Block indices and offsets without division -/

section Arithmetic

variable {b : ℕ} [NeZero b]

/-- A coordinate has block index `q` and offset `r` exactly when it is `b q + r`. -/
theorem intCast_eq_and_ediv_eq_iff (z q : ℤ) (r : ZMod b) :
    ((z : ZMod b) = r ∧ z / b = q) ↔ z = b * q + r.val := by
  have hb : (0 : ℤ) < b := by exact_mod_cast Nat.pos_of_neZero b
  have hr : (r.val : ℤ) < b := by exact_mod_cast ZMod.val_lt r
  constructor
  · rintro ⟨hz, hq⟩
    have hval : ((z : ZMod b).val : ℤ) = z % b := ZMod.val_intCast z
    rw [hz] at hval
    rw [hval, ← hq]
    exact (Int.mul_ediv_add_emod z b).symm
  · rintro rfl
    constructor
    · simp
    · rw [add_comm, Int.add_mul_ediv_left _ _ hb.ne']
      rw [Int.ediv_eq_zero_of_lt (by positivity) hr, zero_add]

/-- The offsets and block indices of finite storage, compared with a control record's offsets and
prescribed block indices, are its head coordinates. -/
theorem blockControl_eq_and_blockIndex_iff (l : LocalCfg k State) (c : BlockControl k State b)
    (J : Option (Fin k) → ℤ) :
    (l.blockControl b = c ∧ ∀ head, l.blockIndex b head = J head) ↔
      l.state = c.1 ∧ l.track = c.2.2 ∧
        ∀ head, l.headCoord head = b * J head + (c.2.1 head).val := by
  obtain ⟨s, off, tr⟩ := c
  have hcoord : ∀ head, ((l.blockControl b).2.1 head = off head ∧ l.blockIndex b head = J head) ↔
      l.headCoord head = b * J head + (off head).val := by
    intro head
    rw [← intCast_eq_and_ediv_eq_iff]
    cases head <;> rfl
  simp only [LocalCfg.blockControl, Prod.mk.injEq] at hcoord ⊢
  constructor
  · rintro ⟨⟨hs, hoff, htr⟩, hJ⟩
    exact ⟨hs, htr, fun head => (hcoord head).mp ⟨congrFun hoff head, hJ head⟩⟩
  · rintro ⟨hs, htr, hJ⟩
    exact ⟨⟨hs, funext fun head => ((hcoord head).mpr (hJ head)).1, htr⟩,
      fun head => ((hcoord head).mpr (hJ head)).2⟩

/-- The window contents of finite storage are `w` exactly when the cells of every window are the
window cells of `w`. -/
theorem windowContents_eq_iff (l : LocalCfg k State) (J : Option (Fin k) → ℤ)
    (w : Fin k → Fin 3 → ZMod b → Option Bool) :
    l.windowContents b J = w ↔ ∀ h, l.windowCellsAt b (J (some h)) h = windowCells b (w h) := by
  have hb : 0 < b := Nat.pos_of_neZero b
  constructor
  · rintro rfl h
    unfold LocalCfg.windowCellsAt windowCells
    refine List.map_congr_left fun c hc => ?_
    have hc3 : c / b < 3 := by
      rw [Nat.div_lt_iff_lt_mul hb]
      simpa [Nat.mul_comm] using List.mem_range.mp hc
    rw [dite_eq_left hc3]
    simp only [LocalCfg.windowContents, ZMod.val_natCast]
    congr 1
    have h := Nat.div_add_mod c b
    zify at h
    push_cast
    linear_combination (-1 : ℤ) * h
  · intro hw
    funext h d r
    have hwh := hw h
    unfold LocalCfg.windowCellsAt windowCells at hwh
    have hlt : b * (d : ℕ) + r.val < 3 * b := by
      have := d.isLt
      have := ZMod.val_lt r
      nlinarith
    have hcell := List.map_inj_left.mp hwh (b * d + r.val) (List.mem_range.mpr hlt)
    have hdiv : (b * d + r.val) / b = d := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (ZMod.val_lt r), zero_add]
    simp only [hdiv, d.isLt, dite_true] at hcell
    have hcast : ((b * d + r.val : ℕ) : ZMod b) = r := by
      push_cast
      simp
    rw [hcast] at hcell
    rw [← hcell]
    simp only [LocalCfg.windowContents]
    congr 1
    push_cast
    ring

end Arithmetic

/-! ### The interval condition and count on plain data -/

section Interval

variable (machine : MultiTapePTM k Bool State) (b : ℕ)

/-- **The interval condition on plain data**: replaying `coins` on the finite storage of the
embedded window leaves the state and the output track of `cOut`, puts every head at its
prescribed block start `b (J + δ)` plus its offset in `cOut`, which is below `b`, and leaves the
window cells `wOut`. -/
@[expose] def LocalIntervalStepData (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : ControlData k State)
    (wIn : Fin k → List (Option Bool)) (cOut : ControlData k State)
    (wOut : Fin k → List (Option Bool)) (coins : List Bool) : Prop :=
  (machine.localRun input coins (localStartData b input J cIn wIn)).state = cOut.1 ∧
    (machine.localRun input coins (localStartData b input J cIn wIn)).track = cOut.2.2 ∧
    (∀ head, cOut.2.1 head < b ∧
      (machine.localRun input coins (localStartData b input J cIn wIn)).headCoord head =
        b * (J head + δ head) + cOut.2.1 head) ∧
    ∀ h, (machine.localRun input coins (localStartData b input J cIn wIn)).windowCellsAt b
      (J (some h)) h = wOut h

instance [DecidableEq State] (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : ControlData k State)
    (wIn : Fin k → List (Option Bool)) (cOut : ControlData k State)
    (wOut : Fin k → List (Option Bool)) (coins : List Bool) :
    Decidable (machine.LocalIntervalStepData b input J δ cIn wIn cOut wOut coins) := by
  unfold LocalIntervalStepData
  infer_instance

/-- **The interval condition on plain data is the interval condition on finite storage.** -/
theorem localIntervalStepData_iff [NeZero b] (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : BlockControl k State b)
    (wIn : Fin k → Fin 3 → ZMod b → Option Bool) (cOut : BlockControl k State b)
    (wOut : Fin k → Fin 3 → ZMod b → Option Bool) (coins : List Bool) :
    machine.LocalIntervalStepData b input J δ (controlData cIn) (fun h => windowCells b (wIn h))
        (controlData cOut) (fun h => windowCells b (wOut h)) coins ↔
      machine.LocalIntervalStep b input J δ cIn wIn coins cOut wOut := by
  set l := machine.localRun input coins (localStart b input J cIn wIn)
  have hcontrol := blockControl_eq_and_blockIndex_iff l cOut (fun head => J head + δ head)
  have hwindow := windowContents_eq_iff l J wOut
  have hlt : ∀ head, (cOut.2.1 head).val < b := fun head => ZMod.val_lt _
  simp only [LocalIntervalStepData, LocalIntervalStep, controlData]
  change (l.state = cOut.1 ∧ l.track = cOut.2.2 ∧ (∀ head, (cOut.2.1 head).val < b ∧
      l.headCoord head = b * (J head + δ head) + (cOut.2.1 head).val) ∧
      ∀ h, l.windowCellsAt b (J (some h)) h = windowCells b (wOut h)) ↔
    l.blockControl b = cOut ∧ l.windowContents b J = wOut ∧
      ∀ head, l.blockIndex b head = J head + δ head
  rw [hwindow]
  constructor
  · rintro ⟨hs, htr, hcoord, hw⟩
    obtain ⟨hc, hJ⟩ := hcontrol.mpr ⟨hs, htr, fun head => (hcoord head).2⟩
    exact ⟨hc, hw, hJ⟩
  · rintro ⟨hc, hw, hJ⟩
    obtain ⟨hs, htr, hcoord⟩ := hcontrol.mp ⟨hc, hJ⟩
    exact ⟨hs, htr, fun head => ⟨hlt head, hcoord head⟩, hw⟩

/-- **The interval count on plain data**: the number of coin strings of `b` bits satisfying the
interval condition. -/
@[expose] def localIntervalCount [DecidableEq State] (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : ControlData k State)
    (wIn : Fin k → List (Option Bool)) (cOut : ControlData k State)
    (wOut : Fin k → List (Option Bool)) : ℕ :=
  (Cslib.BitString.enumList b).countP fun coins =>
    decide (machine.LocalIntervalStepData b input J δ cIn wIn cOut wOut coins)

/-- **The interval count on plain data is the interval tensor.** -/
theorem localIntervalCount_eq_intervalCount [DecidableEq State] [NeZero b] (input : List Bool)
    (J : Option (Fin k) → ℤ) (δ : Option (Fin k) → SignType) (cIn : BlockControl k State b)
    (wIn : Fin k → Fin 3 → ZMod b → Option Bool) (cOut : BlockControl k State b)
    (wOut : Fin k → Fin 3 → ZMod b → Option Bool) :
    machine.localIntervalCount b input J δ (controlData cIn) (fun h => windowCells b (wIn h))
        (controlData cOut) (fun h => windowCells b (wOut h)) =
      machine.intervalCount b input J δ cIn wIn cOut wOut := by
  classical
  rw [localIntervalCount, Cslib.BitString.countP_enumList,
    intervalCount_eq_card_localIntervalStep]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
    localIntervalStepData_iff]

end Interval

end Turing.MultiTapePTM
