/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BiTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine

/-!
# Finite data for multi-tape configurations

`FiniteCfg` replaces the native integer-indexed work tapes by CSLib's `BiTape` data.
The input, control, output and action types retain their original meanings. Its simulation
relation allows the native heads to have any absolute positions; the finite tapes store their
contents relative to their current heads.

`MultiTapeMachine.FiniteConfig` adds finite query buffers and read-only answer tapes. It uses the
same named channels and the same local actions and query instructions as the shared machine core.
Each channel has finite storage; encoding all channels as finite data additionally requires the
channel type to be finite. The representation laws do not need that restriction.

## Main definitions

* `Turing.FiniteCfg`: finite input, work tapes, output and control.
* `Turing.MultiTapeMachine.FiniteConfig`: finite storage with oracle channels.
* `Turing.MultiTapeMachine.FiniteConfig.SpaceBound`: input, work, output, query and reply budgets.

## Main results

* `Turing.MultiTapeMachine.FiniteConfig.Represents.step`: preserve native observations.
* `Turing.MultiTapeMachine.FiniteConfig.Represents.receive`: preserve the channel reset semantics.
* `Turing.MultiTapeMachine.FiniteConfig.SpaceBound.step`: per-instruction storage growth.

## References

Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using
Bolton Bailey's upstream `BiTape` and the common native machine configurations.
-/

@[expose] public section

namespace Turing

open Cslib.Turing

/-- A configuration stored entirely as finite data. The input is included so the representation
has one fixed type across all runtime inputs. -/
@[ext] structure FiniteCfg (k : ℕ) (Symbol State : Type*) where
  /-- The immutable input word. -/
  input : List Symbol
  /-- The current control, or `none` when halted. -/
  state : Option State
  /-- The native input position, including the two boundary cells. -/
  inputPos : Fin (input.length + 2)
  /-- Work tapes centered at their current heads. -/
  workTapes : Fin k → BiTape Symbol
  /-- Symbols already written to the output. -/
  output : List Symbol

namespace FiniteCfg

variable {k : ℕ} {Symbol State : Type*}

/-- The integer-indexed view with each work head placed at zero. Absolute work-head positions
are irrelevant to observations, so the representation relation also admits translated views. -/
def toCfg (finite : FiniteCfg k Symbol State) : Cfg k Symbol State finite.input where
  state := finite.state
  inputPos := finite.inputPos
  workTapes := fun tape => (finite.workTapes tape).read
  workTapePos := fun _ => 0
  output := finite.output

/-- Observe the native read-only input geometry. -/
def inputSymbol (finite : FiniteCfg k Symbol State) : Option Symbol := finite.toCfg.inputSymbol

/-- Reading the native input is list lookup with an initial blank and a blank default. -/
theorem inputSymbol_eq_getD (finite : FiniteCfg k Symbol State) :
    finite.inputSymbol = ((none :: finite.input.map some)[finite.inputPos.val]?).getD none := by
  by_cases hzero : finite.inputPos.val = 0
  · rw [inputSymbol, inputSymbol_eq_none_of_boundary (Or.inl hzero)]
    simp [hzero]
  · have hpos : finite.inputPos.val = (finite.inputPos.val - 1) + 1 := by lia
    conv_rhs => rw [hpos]
    by_cases hlt : finite.inputPos.val - 1 < finite.input.length
    · rw [inputSymbol, inputSymbolInner (finite.inputPos.val - 1)
        (by simpa [toCfg, Nat.add_comm] using hpos) hlt]
      simp [List.getElem?_eq_getElem hlt]
    · have hright : finite.inputPos.val = finite.input.length + 1 := by
        have := finite.inputPos.isLt
        lia
      rw [inputSymbol, inputSymbol_eq_none_of_boundary (Or.inr hright)]
      simp [List.getElem?_eq_none (Nat.le_of_not_gt hlt)]

/-- Observe one symbol per work tape. -/
def workTapeSymbols (finite : FiniteCfg k Symbol State) : Fin k → Option Symbol :=
  fun tape => (finite.workTapes tape).head

/-- Apply a native action to finite storage. -/
def step (finite : FiniteCfg k Symbol State) (action : Action k Symbol State) :
    FiniteCfg k Symbol State where
  input := finite.input
  state := action.state
  inputPos := moveInputPos finite.inputPos action.inputTape
  workTapes := fun tape => (finite.workTapes tape).step (action.workTapes tape)
  output := finite.output ++ action.output.toList

/-- Initial finite storage uses the native input-head convention and blank work tapes. -/
def init (state : State) (input : List Symbol) : FiniteCfg k Symbol State where
  input := input
  state := some state
  inputPos := 1
  workTapes := fun _ => BiTape.nil
  output := []

/-- The finite data and native configuration have identical observations and corresponding
work-tape contents at every displacement from their heads. -/
structure Represents (finite : FiniteCfg k Symbol State)
    (cfg : Cfg k Symbol State finite.input) : Prop where
  /-- Control states agree. -/
  state : finite.state = cfg.state
  /-- Input positions agree. -/
  inputPos : finite.inputPos = cfg.inputPos
  /-- Each finite work tape represents the native tape at its native head position. -/
  workTapes : ∀ tape, (finite.workTapes tape).Represents
    (cfg.workTapes tape) (cfg.workTapePos tape)
  /-- Accumulated outputs agree. -/
  output : finite.output = cfg.output

theorem represents_init (state : State) (input : List Symbol) :
    (init (k := k) state input).Represents (Cfg.init state input) :=
  ⟨rfl, rfl, fun _ => BiTape.represents_nil _, rfl⟩

/-- Related configurations read the same input cell. -/
theorem Represents.inputSymbol {finite : FiniteCfg k Symbol State}
    {cfg : Cfg k Symbol State finite.input} (h : finite.Represents cfg) :
    finite.inputSymbol = cfg.inputSymbol := by
  simp only [FiniteCfg.inputSymbol, Cfg.inputSymbol, toCfg, h.inputPos]

/-- Related configurations read the same work cells. -/
theorem Represents.workTapeSymbols {finite : FiniteCfg k Symbol State}
    {cfg : Cfg k Symbol State finite.input} (h : finite.Represents cfg) :
    finite.workTapeSymbols = cfg.workTapeSymbols :=
  funext (fun tape => (h.workTapes tape).head)

/-- The same native action preserves the representation relation. -/
theorem Represents.step {finite : FiniteCfg k Symbol State}
    {cfg : Cfg k Symbol State finite.input} (h : finite.Represents cfg)
    (action : Action k Symbol State) : (finite.step action).Represents (action.apply cfg) := by
  refine ⟨rfl, congrArg (moveInputPos · action.inputTape) h.inputPos, ?_, ?_⟩
  · intro tape
    have hstep := (h.workTapes tape).step (action.workTapes tape)
    cases hw : (action.workTapes tape).1 <;> simpa [FiniteCfg.step, Action.apply, hw] using hstep
  · simp only [FiniteCfg.step, Action.apply, h.output]

end FiniteCfg

namespace MultiTapeMachine

/-- Finite tape storage for a shared-core configuration. Each channel stores its pending request
and an answer tape centered at its current head. A finite channel type makes the whole
configuration a finite collection of finite data. -/
@[ext] structure FiniteConfig (k : ℕ) (Symbol State Oracle : Type*) where
  /-- The ordinary input, work, control and output components. -/
  tapes : FiniteCfg k Symbol State
  /-- Per-channel pending requests and read-only answer tapes. -/
  channels : Oracle → List Symbol × BiTape Symbol

namespace FiniteConfig

variable {k : ℕ} {Symbol State Oracle : Type*}

/-- The current answer symbols supplied to the shared transition table. -/
def answerSymbols (finite : FiniteConfig k Symbol State Oracle) : Oracle → Option Symbol :=
  fun oracle => (finite.channels oracle).2.head

/-- An ordinary step applies the tape action and moves each answer head. -/
def step (finite : FiniteConfig k Symbol State Oracle) (action : Turing.Action k Symbol State)
    (symbol : Oracle → Option Symbol) (move : Oracle → SignType) :
    FiniteConfig k Symbol State Oracle where
  tapes := finite.tapes.step action
  channels oracle := ((finite.channels oracle).1 ++ (symbol oracle).toList,
    (finite.channels oracle).2.step (none, move oracle))

/-- A query clears just its selected buffer and installs the reply at position zero. -/
def receive [DecidableEq Oracle] (finite : FiniteConfig k Symbol State Oracle)
    (oracle : Oracle) (next : State) (answer : List Symbol) :
    FiniteConfig k Symbol State Oracle where
  tapes := { finite.tapes with state := some next }
  channels := Function.update finite.channels oracle ([], BiTape.mk₁ answer)

/-- Initial finite storage has empty buffers and blank answer tapes. -/
def init (state : State) (input : List Symbol) : FiniteConfig k Symbol State Oracle where
  tapes := FiniteCfg.init state input
  channels := fun _ => ([], BiTape.nil)

/-- Storage bounds after a number of native transitions. Replies can be longer than the clock;
their size is therefore tracked separately from the work tapes and pending query buffers. -/
structure SpaceBound (inputSize steps answerSize : ℕ)
    (finite : FiniteConfig k Symbol State Oracle) : Prop where
  /-- The input is stored once. -/
  input : finite.tapes.input.length ≤ inputSize
  /-- Work space grows by at most one cell per transition on each tape. -/
  work : ∀ tape, (finite.tapes.workTapes tape).spaceUsed ≤ steps + 1
  /-- At most one output symbol is written per transition. -/
  output : finite.tapes.output.length ≤ steps
  /-- At most one query symbol per channel is written per transition. -/
  query : ∀ channel, (finite.channels channel).1.length ≤ steps
  /-- Answer storage includes the installed reply and head movements since installation. -/
  answer : ∀ channel, (finite.channels channel).2.spaceUsed ≤ steps + answerSize + 1

/-- Storage bounds may be enlarged independently. -/
theorem SpaceBound.mono {inputSize steps answerSize inputSize' steps' answerSize' : ℕ}
    {finite : FiniteConfig k Symbol State Oracle} (h : SpaceBound inputSize steps answerSize finite)
    (hi : inputSize ≤ inputSize') (ht : steps ≤ steps') (ha : answerSize ≤ answerSize') :
    SpaceBound inputSize' steps' answerSize' finite :=
  ⟨h.input.trans hi, fun tape => (h.work tape).trans (by lia), h.output.trans ht,
    fun channel => (h.query channel).trans ht, fun channel => (h.answer channel).trans (by lia)⟩

/-- Initially only the input occupies nonblank storage. -/
theorem spaceBound_init (state : State) (input : List Symbol) (answerSize : ℕ) :
    SpaceBound input.length 0 answerSize (init (k := k) (Oracle := Oracle) state input) := by
  constructor <;> simp [init, FiniteCfg.init, BiTape.spaceUsed, BiTape.nil, StackTape.length_nil]

/-- A local native transition respects the per-step storage bounds. -/
theorem SpaceBound.step {inputSize steps answerSize : ℕ}
    {finite : FiniteConfig k Symbol State Oracle} (h : SpaceBound inputSize steps answerSize finite)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) :
    SpaceBound inputSize (steps + 1) answerSize (finite.step action symbol move) := by
  refine ⟨h.input, ?_, ?_, ?_, ?_⟩
  · intro tape
    exact (BiTape.spaceUsed_step_le _ _).trans (Nat.add_le_add_right (h.work tape) 1)
  · simpa only [FiniteConfig.step, FiniteCfg.step, List.length_append] using
      Nat.add_le_add (h.output) action.output.length_toList_le
  · intro channel
    simpa only [FiniteConfig.step, List.length_append] using
      Nat.add_le_add (h.query channel) (symbol channel).length_toList_le
  · intro channel
    have := (BiTape.spaceUsed_step_le (finite.channels channel).2 (none, move channel)).trans
      (Nat.add_le_add_right (h.answer channel) 1)
    simpa only [FiniteConfig.step, Nat.add_right_comm steps answerSize 1] using this

/-- Installing a bounded reply preserves the storage bounds and clears only its own query. -/
theorem SpaceBound.receive [DecidableEq Oracle] {inputSize steps answerSize : ℕ}
    {finite : FiniteConfig k Symbol State Oracle}
    (h : SpaceBound inputSize steps answerSize finite)
    (channel : Oracle) (next : State) (answer : List Symbol)
    (hanswer : answer.length ≤ answerSize) :
    SpaceBound inputSize (steps + 1) answerSize (finite.receive channel next answer) := by
  refine ⟨h.input, fun tape => (h.work tape).trans (by lia),
    h.output.trans (by lia), ?_, ?_⟩
  · intro other
    by_cases heq : other = channel
    · subst other
      simp [FiniteConfig.receive]
    · simpa [FiniteConfig.receive, heq] using (h.query other).trans (Nat.le_succ steps)
  · intro other
    by_cases heq : other = channel
    · subst other
      simp only [FiniteConfig.receive, Function.update_self, BiTape.spaceUsed_mk₁]
      lia
    · simpa [FiniteConfig.receive, heq] using (h.answer other).trans (by lia)

/-- The observation-preserving relation to the shared native configuration. -/
structure Represents (finite : FiniteConfig k Symbol State Oracle)
    (cfg : Config k Symbol State Oracle finite.tapes.input) : Prop where
  /-- Ordinary configurations correspond. -/
  tapes : finite.tapes.Represents cfg.tapes
  /-- Pending requests agree exactly, including requests not yet submitted. -/
  queries : ∀ oracle, (finite.channels oracle).1 = (cfg.channels oracle).queryBuffer
  /-- Answer tapes agree at every displacement from their heads. -/
  answers : ∀ oracle, (finite.channels oracle).2.Represents
    (fun position => if 0 ≤ position then (cfg.channels oracle).answer[position.toNat]? else none)
    (cfg.channels oracle).answerPos

/-- The finite and native initial configurations correspond. -/
theorem represents_init (state : State) (input : List Symbol) :
    (init (k := k) (Oracle := Oracle) state input).Represents
      { tapes := Cfg.init state input } := by
  refine ⟨FiniteCfg.represents_init _ _, fun _ => rfl, ?_⟩
  intro oracle position
  simp [init, BiTape.read_nil]

/-- The transition table sees the same answer symbols in both representations. -/
theorem Represents.answerSymbols {finite : FiniteConfig k Symbol State Oracle}
    {cfg : Config k Symbol State Oracle finite.tapes.input} (h : finite.Represents cfg) :
    finite.answerSymbols = cfg.answerSymbols :=
  funext (fun oracle => (h.answers oracle).head)

/-- An ordinary shared-core action preserves all finite representations. -/
theorem Represents.step {finite : FiniteConfig k Symbol State Oracle}
    {cfg : Config k Symbol State Oracle finite.tapes.input} (h : finite.Represents cfg)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) :
    (finite.step action symbol move).Represents (cfg.step action symbol move) := by
  refine ⟨h.tapes.step action, ?_, ?_⟩
  · intro oracle
    simp only [FiniteConfig.step, Config.step, h.queries]
  · intro oracle
    simpa only [FiniteConfig.step, Config.step, Option.elim_none] using
      (h.answers oracle).step (none, move oracle)

/-- Submission resets precisely the selected channel, retaining every other pending query and
answer head. The installed reply has the native position-zero geometry. -/
theorem Represents.receive [DecidableEq Oracle]
    {finite : FiniteConfig k Symbol State Oracle}
    {cfg : Config k Symbol State Oracle finite.tapes.input} (h : finite.Represents cfg)
    (oracle : Oracle) (next : State) (answer : List Symbol) :
    (finite.receive oracle next answer).Represents (cfg.receive oracle next answer) := by
  refine ⟨⟨rfl, h.tapes.inputPos, h.tapes.workTapes, h.tapes.output⟩, ?_, ?_⟩
  · intro channel
    by_cases heq : channel = oracle
    · subst channel
      simp [FiniteConfig.receive, Config.receive]
    · simpa [FiniteConfig.receive, Config.receive, heq] using h.queries channel
  · intro channel
    by_cases heq : channel = oracle
    · subst channel
      intro position
      simp [FiniteConfig.receive, Config.receive, BiTape.read_mk₁]
    · simpa [FiniteConfig.receive, Config.receive, heq] using h.answers channel

end FiniteConfig

end MultiTapeMachine

end Turing
