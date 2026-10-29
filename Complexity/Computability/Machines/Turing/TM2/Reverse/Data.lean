/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.Reverse.Input
public import Complexity.Computability.Machines.Turing.TM2.Reverse.Tape
public import Complexity.Computability.Machines.Turing.TM2.Reverse.TapeSpace
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Raw configurations for the multi-tape to TM2 compiler

## Main definitions

* `Turing.MultiTapeTM.ToTM2.Data`: finite stacks representing a binary native configuration.
* `Turing.MultiTapeTM.ToTM2.Data.step`: apply one native action to the raw configuration.
* `Turing.MultiTapeTM.ToTM2.Data.run`: execute a native machine with raw stacks.
* `Turing.MultiTapeTM.ToTM2.Data.Represents`: agreement with a native configuration.

## Main results

* `Turing.MultiTapeTM.ToTM2.Data.represents_run`: raw execution agrees with native execution.
* `Turing.MultiTapeTM.ToTM2.Data.input_length_run`: input storage is exactly the input length.
* `Turing.MultiTapeTM.ToTM2.Data.output_prefix_run`: chronological output grows by extension.
* `Turing.MultiTapeTM.ToTM2.Data.sum_work_span_run_le`: native space bounds raw work storage.
-/

public section

namespace Turing.MultiTapeTM.ToTM2

/-- A native binary configuration stored as finite stacks, with chronological output. -/
@[ext]
structure Data (k : ℕ) (State : Type) where
  /-- The current state, or `none` after halting. -/
  state : Option State
  /-- The bounded read-only input zipper. -/
  input : Input Bool
  /-- The work tapes, retaining all visited cells. -/
  work : Fin k → RawTape Bool
  /-- Symbols emitted so far, in chronological order. -/
  output : List Bool

namespace Data

variable {k : ℕ} {State : Type}

/-- Initialize the input zipper and blank work tapes. -/
@[expose] def init (q₀ : State) (input : List Bool) : Data k State :=
  ⟨some q₀, Input.init input, fun _ => RawTape.init, []⟩

/-- Apply an action, including the output and movement of its final halting step. -/
@[expose] def step (d : Data k State) (a : Action k Bool State) : Data k State where
  state := a.state
  input := d.input.move a.inputTape
  work i := (d.work i).step (a.workTapes i)
  output := d.output ++ a.output.toList

/-- Select and apply the native transition, staying put once halted. -/
noncomputable def totalStep (tm : MultiTapeTM k Bool State) (d : Data k State) : Data k State :=
  match d.state with
  | none => d
  | some q => d.step (tm.tr q d.input.read (fun i => (d.work i).head))

/-- Execute a fixed number of total steps from an arbitrary raw configuration. -/
noncomputable def runFrom (tm : MultiTapeTM k Bool State) (d : Data k State) (t : ℕ) :
    Data k State :=
  (totalStep tm)^[t] d

/-- Execute a fixed number of total steps from the initial raw configuration. -/
noncomputable def run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    Data k State :=
  runFrom tm (init tm.q₀ input) t

/-- Raw fields agree with the corresponding native state, heads, tapes and output. -/
structure Represents (d : Data k State) {sourceInput : List Bool}
    (cfg : Cfg k Bool State sourceInput) : Prop where
  /-- The control states agree. -/
  state : d.state = cfg.state
  /-- The input zipper represents the native bounded head. -/
  input : d.input.Represents sourceInput cfg.inputPos
  /-- Each work tape represents its native integer-indexed tape and head. -/
  work : ∀ i, (d.work i).Represents (cfg.workTapes i) (cfg.workTapePos i)
  /-- Output is chronological in both representations. -/
  output : d.output = cfg.output

@[simp]
theorem runFrom_zero (tm : MultiTapeTM k Bool State) (d : Data k State) :
    runFrom tm d 0 = d := by rfl

/-- The next raw configuration is one total step from the preceding configuration. -/
theorem runFrom_succ (tm : MultiTapeTM k Bool State) (d : Data k State) (t : ℕ) :
    runFrom tm d (t + 1) = totalStep tm (runFrom tm d t) := by
  exact Function.iterate_succ_apply' _ _ _

@[simp]
theorem run_zero (tm : MultiTapeTM k Bool State) (input : List Bool) :
    run tm input 0 = init tm.q₀ input := by rfl

/-- The next raw configuration on an input is obtained by one total step. -/
theorem run_succ (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    run tm input (t + 1) = totalStep tm (run tm input t) := by
  exact runFrom_succ _ _ _

/-- Halted raw configurations are fixed by the total step. -/
theorem totalStep_of_halt (tm : MultiTapeTM k Bool State) {d : Data k State}
    (h : d.state = none) : totalStep tm d = d := by
  rw [totalStep, h]

/-- A live raw configuration applies the transition selected from its current reads. -/
theorem totalStep_of_state (tm : MultiTapeTM k Bool State) {d : Data k State} {q : State}
    (h : d.state = some q) :
    totalStep tm d = d.step (tm.tr q d.input.read (fun i => (d.work i).head)) := by
  rw [totalStep, h]

namespace Represents

variable {d : Data k State} {sourceInput : List Bool} {cfg : Cfg k Bool State sourceInput}

/-- Initialization represents the native initial configuration. -/
theorem init (q₀ : State) (input : List Bool) :
    (Data.init (k := k) q₀ input).Represents (Cfg.init q₀ input) :=
  ⟨rfl, Input.represents_init input, fun _ => RawTape.Represents.init, rfl⟩

/-- Applying the same action preserves every field of the representation. -/
theorem step (h : d.Represents cfg) (a : Action k Bool State) :
    (d.step a).Represents (a.apply cfg) :=
  ⟨rfl, h.input.move a.inputTape, fun i => (h.work i).step (a.workTapes i),
    congrArg (· ++ a.output.toList) h.output⟩

/-- Raw and native configurations select the same action and take corresponding total steps. -/
theorem totalStep (h : d.Represents cfg) (tm : MultiTapeTM k Bool State) :
    (Data.totalStep tm d).Represents (tm.step cfg) := by
  cases hs : d.state with
  | none =>
    rw [Data.totalStep_of_halt tm hs, tm.step_of_halt (h.state.symm.trans hs)]
    exact h
  | some q =>
    rw [Data.totalStep_of_state tm hs, tm.step_of_state (h.state.symm.trans hs)]
    have hi : d.input.read = cfg.inputSymbol := h.input.read_eq_inputSymbol
    have hw : (fun i => (d.work i).head) = cfg.workTapeSymbols :=
      funext fun i => (h.work i).head
    rw [hi, hw]
    exact h.step _

/-- Any number of raw total steps represents the same number of native total steps. -/
theorem runFrom (h : d.Represents cfg) (tm : MultiTapeTM k Bool State) (t : ℕ) :
    (Data.runFrom tm d t).Represents (tm.runFrom cfg t) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [Data.runFrom_succ, MultiTapeTM.runFrom, Function.iterate_succ_apply',
      ← MultiTapeTM.runFrom]
    exact ih.totalStep tm

end Represents

/-- Raw execution from initialization agrees with the native execution, even after halting. -/
theorem represents_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).Represents (tm.runFrom (tm.initCfg input) t) :=
  (Represents.init tm.q₀ input).runFrom tm t

/-- At every time, the raw input stacks retain exactly the original input length. -/
theorem input_length_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).input.left.length + (run tm input t).input.right.length = input.length :=
  (represents_run tm input t).input.length_eq

/-- The raw output is exactly the native chronological output. -/
theorem output_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).output = (tm.runFrom (tm.initCfg input) t).output :=
  (represents_run tm input t).output

/-- The raw control state agrees with the native state at every time. -/
theorem state_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).state = (tm.runFrom (tm.initCfg input) t).state :=
  (represents_run tm input t).state

/-- Each action only appends to the output. -/
theorem output_prefix_step (d : Data k State) (a : Action k Bool State) :
    d.output <+: (d.step a).output :=
  ⟨a.output.toList, rfl⟩

/-- Total steps only append to the output, including a step which halts. -/
theorem output_prefix_totalStep (tm : MultiTapeTM k Bool State) (d : Data k State) :
    d.output <+: (totalStep tm d).output := by
  cases hs : d.state with
  | none => rw [totalStep_of_halt tm hs]
  | some q => rw [totalStep_of_state tm hs]; exact output_prefix_step _ _

/-- Earlier raw outputs are prefixes of all later raw outputs. -/
theorem output_prefix_run (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t u : ℕ} (h : t ≤ u) : (run tm input t).output <+: (run tm input u).output := by
  induction u, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ u _ ih =>
    rw [run_succ]
    exact ih.trans (output_prefix_totalStep tm _)

/-- The amount of output never decreases. -/
theorem output_length_run_mono (tm : MultiTapeTM k Bool State) (input : List Bool) :
    Monotone (fun t => (run tm input t).output.length) :=
  fun _ _ h => (output_prefix_run tm input h).length_le

/-- Raw execution stays at its final configuration after halting. -/
theorem run_eq_of_halt (tm : MultiTapeTM k Bool State) (input : List Bool) {t u : ℕ}
    (hle : t ≤ u) (hhalt : (run tm input t).state = none) :
    run tm input u = run tm input t := by
  induction u, hle using Nat.le_induction with
  | base => rfl
  | succ u _ ih => rw [run_succ, ih, totalStep_of_halt tm hhalt]

/-- Every intermediate output is bounded by the output of a terminating run. -/
theorem output_length_run_le_of_halt (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t : ℕ} (hhalt : (run tm input t).state = none) (u : ℕ) :
    (run tm input u).output.length ≤ (run tm input t).output.length := by
  rcases le_total u t with h | h
  · exact output_length_run_mono tm input h
  · rw [run_eq_of_halt tm input h hhalt]

/-- Every raw output is a prefix of the complete output of a terminating native computation. -/
theorem output_prefix_run_of_computes {tm : MultiTapeTM k Bool State}
    {input output : List Bool} (h : tm.Computes input output) (t : ℕ) :
    (run tm input t).output <+: output := by
  obtain ⟨u, hhalt, hout⟩ := h
  have hraw : (run tm input u).output = output := (output_run tm input u).trans hout
  rcases le_total t u with h | h
  · exact hraw ▸ output_prefix_run tm input h
  · rw [run_eq_of_halt tm input h ((state_run tm input u).trans hhalt), hraw]

/-- A terminating native output bounds every intermediate raw output, without a time term. -/
theorem output_length_run_le_of_computes {tm : MultiTapeTM k Bool State}
    {input output : List Bool} (h : tm.Computes input output) (t : ℕ) :
    (run tm input t).output.length ≤ output.length :=
  (output_prefix_run_of_computes h t).length_le

/-- Each raw total step uses precisely the tape action along the represented native step. -/
theorem Represents.work_totalStep {d : Data k State} {sourceInput : List Bool}
    {cfg : Cfg k Bool State sourceInput} (h : d.Represents cfg)
    (tm : MultiTapeTM k Bool State) (i : Fin k) :
    (Data.totalStep tm d).work i = (d.work i).step (RawTape.nativeAction tm cfg i) := by
  cases hs : d.state with
  | none =>
    rw [totalStep_of_halt tm hs, RawTape.nativeAction, h.state.symm.trans hs]
    rfl
  | some q =>
    rw [totalStep_of_state tm hs, RawTape.nativeAction, h.state.symm.trans hs]
    change (d.work i).step _ = (d.work i).step _
    have hi : d.input.read = cfg.inputSymbol := h.input.read_eq_inputSymbol
    have hw : (fun i => (d.work i).head) = cfg.workTapeSymbols :=
      funext fun i => (h.work i).head
    rw [hi, hw]

/-- The work tapes coincide with the raw tapes used by the exact visited-space theorem. -/
theorem work_run_eq_tape_run (tm : MultiTapeTM k Bool State) (input : List Bool)
    (t : ℕ) (i : Fin k) : (run tm input t).work i = RawTape.run tm input t i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, (represents_run tm input t).work_totalStep tm i, RawTape.run, ih]

/-- Summed raw work-tape storage is exactly native visited space. -/
theorem sum_work_span_run_eq_space (tm : MultiTapeTM k Bool State) (input : List Bool)
    (t : ℕ) :
    ∑ i, ((run tm input t).work i).span =
      (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) t).space := by
  simp only [work_run_eq_tape_run]
  exact RawTape.sum_span_run_eq_space tm input t

/-- Side-stack storage omits exactly the one current cell held in control for each work tape. -/
theorem sum_work_sides_run_add_eq_space (tm : MultiTapeTM k Bool State) (input : List Bool)
    (t : ℕ) :
    (∑ i, (((run tm input t).work i).left.length +
      ((run tm input t).work i).right.length)) + k =
      (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) t).space := by
  simpa [RawTape.span, Finset.sum_add_distrib] using sum_work_span_run_eq_space tm input t

/-- A native space certificate bounds all raw work storage, independently of runtime. -/
theorem sum_work_span_run_le {tm : MultiTapeTM k Bool State} {input : List Bool} {s : ℕ}
    (hs : tm.RunsInSpace input s) (t : ℕ) : ∑ i, ((run tm input t).work i).span ≤ s := by
  simp only [work_run_eq_tape_run]
  exact RawTape.sum_span_run_le hs t

/-- The sum of raw side-stack lengths is bounded by native space. -/
theorem sum_work_sides_run_le {tm : MultiTapeTM k Bool State} {input : List Bool} {s : ℕ}
    (hs : tm.RunsInSpace input s) (t : ℕ) :
    ∑ i, (((run tm input t).work i).left.length +
      ((run tm input t).work i).right.length) ≤ s :=
  (Finset.sum_le_sum fun _ _ => Nat.le_succ _).trans (sum_work_span_run_le hs t)

end Data
end Turing.MultiTapeTM.ToTM2
