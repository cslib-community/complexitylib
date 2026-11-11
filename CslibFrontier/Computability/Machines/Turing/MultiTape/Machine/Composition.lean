/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Sequential
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.InputFromTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.OutputToTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput

/-!
# Shared tape layout for closed buffered composition

The source runs on its own work tapes and writes to a fresh output buffer. The consumer has
separate initially blank work tapes and reads that buffer through the existing virtual-input
compiler. A native deterministic handoff rewinds the buffer and marks its left boundary in
exactly the word length plus four transitions. Source scratch and the real input head remain
explicit in the configuration maps; no clearing or copying occurs outside machine instructions.

These maps and program laws are independent of the transition-choice mechanism. The complete
compiler must still supply its choice-preserving deterministic lift and prove halting/count laws.
The scope here is closed machines with no oracle channels.

## Main definitions

* `Turing.MultiTapeMachine.Composition.source`: reserve consumer tapes and buffer source output.
* `Turing.MultiTapeMachine.Composition.consumer`: read the buffer on separate work tapes.
* `Turing.MultiTapeMachine.Composition.consumerConfig`: the exact joint tape layout.

## Main results

* `Turing.MultiTapeMachine.Composition.runConfigFrom_source`: exact source program embedding.
* `Turing.MultiTapeMachine.Composition.runConfigFrom_consumer`: exact consumer program embedding.
* `Turing.MultiTapeMachine.Composition.runFrom_prepare`: the charged native buffer handoff.

## References

Extracted from `MultiTape.Probabilistic.Composition`, adapted from
MultiTape/Oracle/Composition.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. The native deterministic tape plumbing is by
Christian Reitwiessner and Samuel Schlesinger.
-/

@[expose] public section

namespace Turing.MultiTapeMachine.Composition

open Cslib

universe u v

variable {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type} {input : List Symbol}
  {Choose : Type → Type v}

/-- Reserve blank continuation tapes before the source's work tapes. -/
def reserve (k₁ : ℕ) (cfg : Config k₀ Symbol State₀ Empty input) :
    Config (k₁ + k₀) Symbol State₀ Empty input :=
  cfg.embed (Fin.natAddEmb k₁) (fun _ _ => none) (fun _ => 0)

/-- Buffer the source result and reserve a blank boundary-marker tape. -/
def buffer (k₁ : ℕ) (cfg : Config k₀ Symbol State₀ Empty input) :
    Config (k₁ + k₀ + 2) Symbol State₀ Empty input :=
  (OutputToTape.config (reserve k₁ cfg)).embed Fin.castSuccEmb (fun _ _ => none) (fun _ => 0)

/-- Run the source on its own tapes, redirecting its output to the virtual input buffer. -/
def source [Functor Choose] (machine : MultiTapeMachine k₀ Symbol State₀ Empty Choose) (k₁ : ℕ) :
    MultiTapeMachine (k₁ + k₀ + 2) Symbol State₀ Empty Choose :=
  ((machine.extendTapes (Fin.natAddEmb k₁)).outputToTape).extendTapes Fin.castSuccEmb

/-- Run the continuation on separate work tapes, reading the virtual input. -/
def consumer [Functor Choose] (machine : MultiTapeMachine k₁ Symbol State₁ Empty Choose) (k₀ : ℕ) :
    MultiTapeMachine (k₁ + k₀ + 2) Symbol State₁ Empty Choose :=
  (machine.extendTapes (Fin.castAddEmb k₀)).inputFromTape

/-- Retain the first machine's scratch tapes while the continuation runs on its output. -/
def consumerConfig (mark : Symbol) (cfg₀ : Config k₀ Symbol State₀ Empty input)
    (cfg₁ : Config k₁ Symbol State₁ Empty cfg₀.tapes.output) :
    Config (k₁ + k₀ + 2) Symbol State₁ Empty input :=
  InputFromTape.config mark
    (cfg₁.embed (Fin.castAddEmb k₀)
      (reserve k₁ cfg₀).tapes.workTapes (reserve k₁ cfg₀).tapes.workTapePos)
    input cfg₀.tapes.inputPos

/-- The prepared virtual input, with every source work tape retained. -/
def ready (mark : Symbol) (k₁ : ℕ) (cfg : Config k₀ Symbol State₀ Empty input) :
    Config (k₁ + k₀ + 2) Symbol (MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState)
      Empty input where
  tapes := ⟨none, cfg.tapes.inputPos,
    Fin.append (reserve k₁ cfg).tapes.workTapes
      ![tapeOfList cfg.tapes.output, Function.update (fun _ => none) (-1) (some mark)],
    Fin.append (reserve k₁ cfg).tapes.workTapePos (fun _ => 0), []⟩
  channels := cfg.channels

section Program

variable {Query : Type u} {spec : OracleSpec.{u, 0} Query} [Functor Choose]
  (choose : {α : Type} → Choose α → OracleComp spec α)
  (hchoose : ∀ {α β : Type} (f : α → β) (choices : Choose α),
    choose (f <$> choices) = f <$> choose choices)

include hchoose

/-- Buffering the source preserves its complete configuration program from initialized tapes. -/
theorem runConfigFrom_source (machine : MultiTapeMachine k₀ Symbol State₀ Empty Choose)
    (k₁ fuel : ℕ) (input : List Symbol) :
    (source machine k₁).runConfigFrom choose Empty.elim fuel
        ((source machine k₁).initialConfig input) =
      buffer k₁ <$> machine.runConfigFrom choose Empty.elim fuel (machine.initialConfig input) := by
  simp only [source, initialConfig_extendTapes, initialConfig_outputToTape,
    runConfigFrom_embed _ _ choose hchoose, runConfigFrom_outputToTape _ choose hchoose,
    Functor.map_map]
  rfl

/-- The consumer preserves its complete program and every reserved source scratch tape. -/
theorem runConfigFrom_consumer (machine : MultiTapeMachine k₁ Symbol State₁ Empty Choose)
    (mark : Symbol) (cfg₀ : Config k₀ Symbol State₀ Empty input)
    (cfg₁ : Config k₁ Symbol State₁ Empty cfg₀.tapes.output) (fuel : ℕ) :
    (consumer machine k₀).runConfigFrom choose Empty.elim fuel (consumerConfig mark cfg₀ cfg₁) =
      consumerConfig mark cfg₀ <$> machine.runConfigFrom choose Empty.elim fuel cfg₁ := by
  simp only [consumer, consumerConfig, runConfigFrom_inputFromTape _ choose hchoose,
    runConfigFrom_embed _ _ choose hchoose, Functor.map_map]
  rfl

end Program

/-- The two new tapes are the completed output buffer and a blank boundary tape. -/
theorem buffer_tapes (k₁ : ℕ) (cfg : Config k₀ Symbol State₀ Empty input) :
    (buffer k₁ cfg).tapes =
      ⟨cfg.tapes.state, cfg.tapes.inputPos,
        Fin.append (reserve k₁ cfg).tapes.workTapes ![tapeOfList cfg.tapes.output, fun _ => none],
        Fin.append (reserve k₁ cfg).tapes.workTapePos ![(cfg.tapes.output.length : ℤ), 0], []⟩ := by
  have happend {α : Type} (f : Fin (k₁ + k₀) → α) (a b : α) :
      Fin.lastCases b (Fin.lastCases a f) = Fin.append f ![a, b] := by
    have hsnoc {n : ℕ} (f : Fin n → α) (a : α) :
        (Fin.lastCases a f : Fin (n + 1) → α) = Fin.snoc f a := by
      funext i
      induction i using Fin.lastCases <;> simp
    change Fin.lastCases b (Fin.lastCases a f) = Fin.append f (Fin.cons a (Fin.cons b Fin.elim0))
    rw [hsnoc, hsnoc, Fin.append_right_cons, Fin.append_right_eq_snoc]
    rfl
  simp only [buffer, Config.embed, OutputToTape.config, MultiTapeTM.embed_castSucc,
    MultiTapeTM.outCfg, happend]
  rfl

/-- The handoff costs the buffered word length plus four, with no assumptions on source scratch. -/
theorem runFrom_prepare (mark : Symbol) (k₁ : ℕ) (cfg : Config k₀ Symbol State₀ Empty input) :
    (MultiTapeTM.prepareInput (k₁ + k₀) mark).runFrom
        ((buffer k₁ cfg).tapes.withState
          (some (MultiTapeTM.prepareInput (k₁ + k₀) mark).q₀)) (cfg.tapes.output.length + 4) =
      (ready mark k₁ cfg).tapes := by
  rw [MultiTapeTM.runFrom_prepareInput mark _ cfg.tapes.output
    (by rw [buffer_tapes]; simp) (by rw [buffer_tapes]; simp) (by rw [buffer_tapes]; simp)]
  rw [buffer_tapes]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases with
  | left i => simp [ready, Function.update_of_ne (Fin.castAdd_ne_natAdd i _)]
  | right i => fin_cases i <;> simp [ready]

/-- The prepared input starts the consumer with blank work tapes while retaining source scratch. -/
theorem start_ready [Functor Choose] (machine : MultiTapeMachine k₁ Symbol State₁ Empty Choose)
    (mark : Symbol) (cfg : Config k₀ Symbol State₀ Empty input) :
    Sequential.start (consumer machine k₀) (ready mark k₁ cfg) =
      consumerConfig mark cfg (machine.initialConfig cfg.tapes.output) := by
  refine Config.ext ?_ (Subsingleton.elim _ _)
  simp only [Sequential.start, ready, consumerConfig, InputFromTape.config, Config.embed,
    MultiTapeTM.embed_castAdd, MultiTapeTM.inCfg, initialConfig, Cfg.init, reserve,
    MultiTapeTM.embed_natAdd, Cfg.withState]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases with
  | left i => induction i using Fin.addCases <;> simp
  | right i => fin_cases i <;> simp

/-- The control-state embeddings of a completed buffered composition. -/
def finalConfig (mark : Symbol) (cfg₀ : Config k₀ Symbol State₀ Empty input)
    (cfg₁ : Config k₁ Symbol State₁ Empty cfg₀.tapes.output) :
    Config (k₁ + k₀ + 2) Symbol
      (State₀ ⊕ ((MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState) ⊕ State₁)) Empty input :=
  Sequential.right (Sequential.right (consumerConfig mark cfg₀ cfg₁))

@[simp] theorem finalConfig_output (mark : Symbol) (cfg₀ : Config k₀ Symbol State₀ Empty input)
    (cfg₁ : Config k₁ Symbol State₁ Empty cfg₀.tapes.output) :
    (finalConfig mark cfg₀ cfg₁).tapes.output = cfg₁.tapes.output := rfl

end Turing.MultiTapeMachine.Composition
