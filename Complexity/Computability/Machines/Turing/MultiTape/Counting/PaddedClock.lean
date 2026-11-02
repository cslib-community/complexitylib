/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.AcceptCount
import Complexity.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic

/-!
# Padded coin counts as terminal-path counts

A closed fair-coin table counts the coin strings of a fixed length `τ` on which it outputs
`[true]` (`Turing.MultiTapePTM.acceptCount`). A run that halts early ignores its remaining coins,
so an accepting run of length `ℓ` contributes `2 ^ (τ - ℓ)` strings. A native counting machine
counts each terminal branch once (`Turing.MultiTapeCTM.acceptCount`).

`Turing.MultiTapeCTM.PaddedClock.machine` turns the first count into the second. It keeps the
source tapes on its first `k` work tapes and a unary clock on its last work tape. While the
clock head reads `true`, it takes one of two transition occurrences, one per coin: it performs
the source action selected by that coin and advances the clock head. After the source halts, the
two occurrences only advance the clock. On the first cell that does not hold `true`, it halts
with a single occurrence and emits nothing. Thus a clock of `τ` cells has exactly one terminal
branch for each coin string of length `τ`, and that branch ends with the output of the coin
replay.

`Turing.MultiTapeCTM.PaddedClock.compile` precedes this machine by a deterministic phase that
writes `τ` true cells on the clock tape and leaves every other tape blank. The time and
correctness of that phase are hypotheses here; the clock is prepared from a time-constructible
bound in `Complexity.Computability.Complexity.Classes.Constructible.UnaryClock`.

## Main definitions

* `Turing.MultiTapeCTM.PaddedClock.machine`: count coin strings under a prepared unary clock.
* `Turing.MultiTapeCTM.PaddedClock.compile`: prepare the clock, then count.

## Main results

* `Turing.MultiTapeCTM.PaddedClock.haltsWithin_acceptCount_machine`: a clock of `n` cells halts
  every branch within `n + 1` steps and counts the coin strings of length `n`.
* `Turing.MultiTapeCTM.PaddedClock.haltsWithin_acceptCount_compile`: after a preparation of
  `time` steps writing `τ` cells, every branch halts within `time + (τ + 1)` steps and the
  terminal accepting count is the padded accepting count at `τ`.

## References

The unary clock tape follows `MultiTape.Machine.Clock`, whose controller does not pad halted
runs with branching choices.
-/

public section

namespace Turing.MultiTapeCTM.PaddedClock

open Cslib MultiTapeMachine

variable {k r : ℕ} {State : Type} {input : List Bool}

/-- The source action selected by a coin at a running source state. -/
def coinAction (M : MultiTapePTM k Bool State) (state : State) (symbol : Option Bool)
    (work : Fin k → Option Bool) (bit : Bool) : Turing.Action k Bool State :=
  Action.emptyOracleEquiv (M.tr state symbol work Empty.elim bit)

/-- A source action on the first `k` work tapes, advancing the clock head on the last one. -/
def lift (action : Turing.Action k Bool State) :
    Turing.Action (k + r + 1) Bool (Option State) where
  inputTape := action.inputTape
  workTapes := Fin.lastCases (none, 1) (Fin.addCases action.workTapes fun _ => (none, 0))
  output := action.output
  state := some action.state

/-- After the source halts: advance the clock head and change nothing else. -/
def tick : Turing.Action (k + r + 1) Bool (Option State) where
  inputTape := 0
  workTapes := Fin.lastCases (none, 1) fun _ => (none, 0)
  output := none
  state := some none

/-- Halt once the clock is exhausted, emitting nothing. -/
def stop : Turing.Action (k + r + 1) Bool (Option State) where
  inputTape := 0
  workTapes := fun _ => (none, 0)
  output := none
  state := none

/-- The transition occurrences: one per coin while the clock head reads `true`, and a single halt
afterwards. A halted source keeps two occurrences per clock cell. -/
def choices (M : MultiTapePTM k Bool State) (r : ℕ) (state : Option State)
    (symbol : Option Bool) (work : Fin (k + r + 1) → Option Bool) :
    List (Turing.Action (k + r + 1) Bool (Option State)) :=
  if work (Fin.last (k + r)) = some true then
    match state with
    | some state => [false, true].map fun bit =>
        lift (coinAction M state symbol (fun i => work (Fin.castAdd r i).castSucc) bit)
    | none => [tick, tick]
  else [stop]

/-- **Padded coin counting.** Run a fair-coin table on the first `k` work tapes under the unary
clock on the last work tape, branching once per coin until the clock is exhausted. The control
state is the source state, `none` once the source has halted. -/
def machine (M : MultiTapePTM k Bool State) (r : ℕ) :
    MultiTapeCTM (k + r + 1) Bool (Option State) where
  initial := some M.initial
  tr state symbol work _ := (choices M r state symbol work).map Action.emptyOracleEquiv.symm

/-- A source configuration on the first `k` work tapes, blank middle tapes, and the clock tape
`clock` with its head at `pos`. -/
def config (r : ℕ) (c : Cfg k Bool State input) (clock : ℤ → Option Bool) (pos : ℤ) :
    Cfg (k + r + 1) Bool (Option State) input where
  state := some c.state
  inputPos := c.inputPos
  workTapes := Fin.lastCases clock (Fin.addCases c.workTapes fun _ _ => none)
  workTapePos := Fin.lastCases pos (Fin.addCases c.workTapePos fun _ => 0)
  output := c.output

/-- No local view is stuck: some occurrence is always available. -/
theorem nonblocking_machine (M : MultiTapePTM k Bool State) (r : ℕ) :
    (machine M r).Nonblocking := by
  intro state symbol work
  simp only [machine, choices, ne_eq, List.map_eq_nil_iff]
  split_ifs
  · cases state <;> simp
  · simp

/-- The occurrences at a simulated configuration are the coin choices of its source state. -/
theorem actions_config (M : MultiTapePTM k Bool State) (c : Cfg k Bool State input)
    (clock : ℤ → Option Bool) (pos : ℤ) :
    (machine M r).actions (config r c clock pos) =
      choices M r c.state c.inputSymbol (config r c clock pos).workTapeSymbols := by
  simp only [actions, config, machine, List.map_map]
  rw [Equiv.self_comp_symm, List.map_id]
  rfl

@[simp] theorem workTapeSymbols_config_last (c : Cfg k Bool State input)
    (clock : ℤ → Option Bool) (pos : ℤ) :
    (config r c clock pos).workTapeSymbols (Fin.last (k + r)) = clock pos := by
  simp [config, Cfg.workTapeSymbols]

@[simp] theorem workTapeSymbols_config_source (c : Cfg k Bool State input)
    (clock : ℤ → Option Bool) (pos : ℤ) (i : Fin k) :
    (config r c clock pos).workTapeSymbols (Fin.castAdd r i).castSucc = c.workTapeSymbols i := by
  simp [config, Cfg.workTapeSymbols]

/-- A lifted source action acts on the source data and advances the clock head. -/
theorem apply_lift (action : Turing.Action k Bool State) (c : Cfg k Bool State input)
    (clock : ℤ → Option Bool) (pos : ℤ) :
    (lift (r := r) action).apply (config r c clock pos) =
      config r (action.apply c) clock (pos + 1) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;> induction j using Fin.lastCases with
  | last => simp [lift, config, Action.apply]
  | cast j =>
    induction j using Fin.addCases with
    | left i =>
      simp only [lift, config, Action.apply, Fin.lastCases_castSucc, Fin.addCases_left]
    | right i =>
      simp only [lift, config, Action.apply, Fin.lastCases_castSucc, Fin.addCases_right,
        SignType.coe_zero, add_zero]

/-- After the source halts, a tick only advances the clock head. -/
theorem apply_tick {c : Cfg k Bool State input} (hc : c.state = none)
    (clock : ℤ → Option Bool) (pos : ℤ) :
    (tick (k := k) (r := r) (State := State)).apply (config r c clock pos) =
      config r c clock (pos + 1) := by
  refine Cfg.ext (by simp [tick, config, hc]) (by simp [tick, config])
    ?_ ?_ (by simp [tick, config, Action.apply]) <;>
    funext j <;> induction j using Fin.lastCases with
  | last => simp [tick, config, Action.apply]
  | cast j =>
    induction j using Fin.addCases with
    | left i =>
      simp only [tick, config, Action.apply, Fin.lastCases_castSucc, Fin.addCases_left,
        SignType.coe_zero, add_zero]
    | right i =>
      simp only [tick, config, Action.apply, Fin.lastCases_castSucc, Fin.addCases_right,
        SignType.coe_zero, add_zero]

/-- The fixed-coin step of the source, in the notation of the coin replay. -/
private theorem step_withCoin_of_state (M : MultiTapePTM k Bool State)
    {c : Cfg k Bool State input} {state : State} (hc : c.state = some state) (bit : Bool) :
    (M.withCoin bit).toTM.step c =
      (coinAction M state c.inputSymbol c.workTapeSymbols bit).apply c := by
  rw [MultiTapeTM.step_of_state hc, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
  rfl

/-- While the clock lasts, the occurrences are the two coins, each followed by the simulated
configuration after the corresponding coin step. -/
private theorem actions_config_of_clock (M : MultiTapePTM k Bool State)
    (c : Cfg k Bool State input) (clock : ℤ → Option Bool) (pos : ℤ)
    (hpos : clock pos = some true) :
    ∃ g : Bool → Turing.Action (k + r + 1) Bool (Option State),
      (machine M r).actions (config r c clock pos) = [false, true].map g ∧
        ∀ bit, (g bit).apply (config r c clock pos) =
          config r ((M.withCoin bit).toTM.step c) clock (pos + 1) := by
  rw [actions_config]
  cases hc : c.state with
  | none =>
    refine ⟨fun _ => tick, ?_, fun bit => ?_⟩
    · simp [choices, hpos]
    · rw [apply_tick hc, MultiTapeTM.step_of_halt hc]
  | some state =>
    refine ⟨fun bit => lift (coinAction M state c.inputSymbol c.workTapeSymbols bit), ?_,
      fun bit => ?_⟩
    · simp [choices, hpos]
    · rw [apply_lift, step_withCoin_of_state M hc]

/-- The padded count splits over the first coin. -/
theorem acceptCount_stepCoins_succ (M : MultiTapePTM k Bool State) (c : Cfg k Bool State input)
    (n : ℕ) :
    Complexity.acceptCount (fun p : Cfg k Bool State input × List Bool =>
        decide ((M.stepCoins p.2 p.1).output = [true])) c (n + 1) =
      Complexity.acceptCount (fun p : Cfg k Bool State input × List Bool =>
          decide ((M.stepCoins p.2 p.1).output = [true])) ((M.withCoin false).toTM.step c) n +
        Complexity.acceptCount (fun p : Cfg k Bool State input × List Bool =>
          decide ((M.stepCoins p.2 p.1).output = [true])) ((M.withCoin true).toTM.step c) n := by
  rw [show n + 1 = 1 + n from Nat.add_comm n 1, Complexity.acceptCount_add,
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) _
      (fun bit => Complexity.acceptCount (fun x : Cfg k Bool State input × List Bool =>
        decide ((M.stepCoins (bit :: x.2) x.1).output = [true])) c n)
      (fun u => by simp [List.ofFn_succ]),
    Fintype.sum_bool]
  simp only [Complexity.acceptCount, MultiTapePTM.stepCoins_cons]
  exact Nat.add_comm _ _

/-- **The counting phase.** With `n` true cells from the clock head on, every branch halts within
`n + 1` steps, and the accepting terminal branches are counted exactly by the coin strings of
length `n` whose replay outputs `[true]`. -/
theorem haltsWithin_acceptCount_machine (M : MultiTapePTM k Bool State) (r n : ℕ)
    (c : Cfg k Bool State input) (clock : ℤ → Option Bool) (pos : ℤ)
    (hclock : ∀ i : ℕ, i < n → clock (pos + i) = some true)
    (hstop : clock (pos + n) ≠ some true) :
    (machine M r).HaltsWithin (n + 1) (config r c clock pos) ∧
      (machine M r).acceptCount (n + 1) (config r c clock pos) =
        Complexity.acceptCount (fun p : Cfg k Bool State input × List Bool =>
          decide ((M.stepCoins p.2 p.1).output = [true])) c n := by
  induction n generalizing c pos with
  | zero =>
    have hpos : clock pos ≠ some true := by simpa using hstop
    have hact : (machine M r).actions (config r c clock pos) = [stop] := by
      rw [actions_config]
      simp [choices, hpos]
    have hhalt : (stop (k := k) (r := r) (State := State)).apply (config r c clock pos)
        |>.Halted := rfl
    refine ⟨.step (by simp [hact]) fun index => ?_, ?_⟩
    · have hindex : ((machine M r).actions (config r c clock pos))[index] = stop :=
        List.mem_singleton.mp (hact ▸ List.getElem_mem index.isLt)
      exact .halt (by rw [hindex]; exact hhalt)
    · rw [acceptCount, ← countP_runList, runList_succ _ _ _ _ rfl, hact,
        Complexity.acceptCount_zero]
      by_cases hout : c.output = [true] <;> simp [stop, config, Action.apply, hout]
  | succ n ih =>
    have hpos : clock pos = some true := by simpa using hclock 0 (Nat.succ_pos n)
    have hnext (bit : Bool) := ih ((M.withCoin bit).toTM.step c) (pos + 1)
      (fun i hi => by
        have := hclock (i + 1) (by omega)
        rwa [Nat.cast_add, Nat.cast_one, add_comm (i : ℤ) 1, ← add_assoc] at this)
      (by
        have := hstop
        rwa [Nat.cast_add, Nat.cast_one, add_comm (n : ℤ) 1, ← add_assoc] at this)
    obtain ⟨g, hact, hg⟩ := actions_config_of_clock (r := r) M c clock pos hpos
    refine ⟨.step (by simp [hact]) fun index => ?_, ?_⟩
    · have hmem : ((machine M r).actions (config r c clock pos))[index] ∈
          [false, true].map g := by
        rw [← hact]
        exact List.getElem_mem index.isLt
      obtain ⟨bit, -, hbit⟩ := List.mem_map.mp hmem
      rw [← hbit, hg]
      exact (hnext bit).1
    · rw [acceptCount_stepCoins_succ, acceptCount, ← countP_runList,
        runList_succ _ _ _ _ rfl, hact, List.flatMap_map]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.countP_append, hg]
      rw [← (hnext false).2, ← (hnext true).2, acceptCount, acceptCount, ← countP_runList,
        ← countP_runList]

variable {P : Type}

/-- **Prepare, then count.** A deterministic phase on all tapes prepares the clock; the counting
phase then runs the source from its initial configuration. -/
noncomputable def compile (M : MultiTapePTM k Bool State)
    (prepare : MultiTapeTM (k + r + 1) Bool P) : MultiTapeCTM (k + r + 1) Bool (P ⊕ Option State) :=
  (ofDeterministic prepare).seq (machine M r)

theorem nonblocking_compile (M : MultiTapePTM k Bool State)
    (prepare : MultiTapeTM (k + r + 1) Bool P) : (compile M prepare).Nonblocking :=
  (nonblocking_ofDeterministic prepare).seq (nonblocking_machine M r)

/-- A prepared clock of `τ` cells is the initial source configuration under that clock. -/
private theorem start_eq (M : MultiTapePTM k Bool State) (input : List Bool) (τ : ℕ) :
    (wordsCfg input (none : Option P)
        (Function.update (fun _ => []) (Fin.last (k + r)) (List.replicate τ true)) []).withState
        (some (machine M r).initial) =
      config r (Cfg.init M.initial input) (tapeOfList (List.replicate τ true)) 0 := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;> induction j using Fin.lastCases with
  | last => simp [config, wordsCfg, Cfg.withState]
  | cast j =>
    induction j using Fin.addCases with
    | left i =>
      simp only [config, wordsCfg, Cfg.withState, Fin.lastCases_castSucc, Fin.addCases_left,
        Cfg.init, Function.update_of_ne (Fin.castSucc_ne_last _), tapeOfList_nil]
    | right i =>
      simp only [config, wordsCfg, Cfg.withState, Fin.lastCases_castSucc, Fin.addCases_right,
        Function.update_of_ne (Fin.castSucc_ne_last _), tapeOfList_nil]

/-- **Padded counts from a prepared clock.** If the preparation halts after `time` steps with
exactly `τ` true cells on the last work tape, every other tape blank and nothing emitted, then
every branch of the compiled machine halts within `time + (τ + 1)` steps, and its accepting
terminal count is the padded accepting count `M.acceptCount input τ`. -/
theorem haltsWithin_acceptCount_compile (M : MultiTapePTM k Bool State)
    (prepare : MultiTapeTM (k + r + 1) Bool P) (input : List Bool) (time τ : ℕ)
    (hprepare : prepare.runFrom (prepare.initCfg input) time =
      wordsCfg input none
        (Function.update (fun _ => []) (Fin.last (k + r)) (List.replicate τ true)) []) :
    (compile M prepare).HaltsWithin (time + (τ + 1)) (Cfg.init (compile M prepare).initial input) ∧
      (compile M prepare).acceptCount (time + (τ + 1))
        (Cfg.init (compile M prepare).initial input) = M.acceptCount input τ := by
  set first := ofDeterministic prepare with hfirst_def
  set cfg := first.initialConfig input with hcfg_def
  have hready : prepare.runFrom cfg.tapes time = wordsCfg input none
      (Function.update (fun _ => []) (Fin.last (k + r)) (List.replicate τ true)) [] := hprepare
  have hfirst : first.HaltsWithin time cfg.tapes := by
    rw [haltsWithin_ofDeterministic_iff, hready]
    rfl
  have hrun : first.runList time cfg.tapes = [wordsCfg input none
      (Function.update (fun _ => []) (Fin.last (k + r)) (List.replicate τ true)) []] := by
    rw [runList_ofDeterministic, hready]
  have hclock := haltsWithin_acceptCount_machine M r τ (Cfg.init M.initial input)
    (tapeOfList (List.replicate τ true)) 0 (fun i hi => by simp [hi]) (by simp)
  have hsecond : ∀ result ∈ first.runList time cfg.tapes,
      (machine M r).HaltsWithin (τ + 1) (result.withState (some (machine M r).initial)) := by
    intro result hresult
    rw [hrun, List.mem_singleton] at hresult
    rw [hresult, start_eq]
    exact hclock.1
  have hstart : Cfg.init (compile M prepare).initial input =
      (Sequential.left (machine M r) cfg).tapes := rfl
  refine ⟨hstart ▸ HaltsWithin.seq (nonblocking_ofDeterministic prepare) (nonblocking_machine M r)
    cfg time (τ + 1) hfirst hsecond, ?_⟩
  rw [hstart, acceptCount, ← countP_runList,
    show compile M prepare = first.seq (machine M r) from rfl,
    runList_seq first (machine M r) cfg time (τ + 1) hfirst hsecond, hrun, List.flatMap_singleton,
    List.countP_map, start_eq]
  have hcount := hclock.2
  rw [acceptCount, ← countP_runList] at hcount
  simp only [Function.comp_def, Cfg.mapState, Option.isNone_map]
  rw [hcount, MultiTapePTM.acceptCount]
  simp only [Complexity.acceptCount, MultiTapePTM.runClosedCoins_eq_output_stepCoins]

end Turing.MultiTapeCTM.PaddedClock
