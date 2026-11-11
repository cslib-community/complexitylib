/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Closed
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.OutputToTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Composition
import CslibFrontier.Probability.PMF.Bind

/-!
# Composing closed probabilistic machines through a buffered word

The first machine writes to a fresh buffer. A deterministic handoff rewinds the buffer and
marks its left boundary. The second machine then reads this word as its input, starting with
separate blank work tapes. Preparation costs the intermediate word length plus four transitions.

## Main definitions

* `Turing.MultiTapePTM.comp`: feed one closed machine's output to another.

## Main results

* `Turing.MultiTapePTM.eval_runClosedConfigFrom_comp`: configuration distribution preservation and
  time bounds for composition.
* `Turing.MultiTapePTM.eval_comp`: the compiled output distribution is monadic composition.

## References

Adapted from MultiTape/Oracle/Composition.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine compilers. As for upstream
deterministic composition, `second.comp first mark` executes `first` and then `second`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeMachine.Composition

namespace Composition

variable {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type} {input : List Symbol}

/-- The shared output-buffer compiler, specialized to fair-coin machines. -/
abbrev source (machine : MultiTapePTM k₀ Symbol State₀) (k₁ : ℕ) :
    MultiTapePTM (k₁ + k₀ + 2) Symbol State₀ :=
  MultiTapeMachine.Composition.source machine k₁

/-- The shared virtual-input compiler, specialized to fair-coin machines. -/
abbrev consumer (machine : MultiTapePTM k₁ Symbol State₁) (k₀ : ℕ) :
    MultiTapePTM (k₁ + k₀ + 2) Symbol State₁ :=
  MultiTapeMachine.Composition.consumer machine k₀

/-- Rewind and mark the intermediate word before starting the continuation. -/
noncomputable def continuation (machine : MultiTapePTM k₁ Symbol State₁) (k₀ : ℕ)
    (mark : Symbol) : MultiTapePTM (k₁ + k₀ + 2) Symbol
      ((MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState) ⊕ State₁) :=
  (ofDeterministic (MultiTapeTM.prepareInput (k₁ + k₀) mark)).seq (consumer machine k₀)

/-- Buffering the source preserves its complete configuration program. -/
theorem runClosedConfigFrom_source (machine : MultiTapePTM k₀ Symbol State₀) (k₁ fuel : ℕ)
    (input : List Symbol) :
    (source machine k₁).runClosedConfigFrom fuel ((source machine k₁).initialConfig input) =
      buffer k₁ <$> machine.runClosedConfigFrom fuel (machine.initialConfig input) := by
  simp only [source, MultiTapeMachine.Composition.source, runClosedConfigFrom,
    MultiTapeMachine.initialConfig_extendTapes,
    MultiTapeMachine.initialConfig_outputToTape, runConfigFrom_embed,
    runConfigFrom_outputToTape, Functor.map_map]
  rfl

/-- The consumer preserves the continuation's complete configuration program. -/
theorem runClosedConfigFrom_consumer (machine : MultiTapePTM k₁ Symbol State₁) (mark : Symbol)
    (cfg₀ : Config k₀ Symbol State₀ Empty input)
    (cfg₁ : Config k₁ Symbol State₁ Empty cfg₀.tapes.output) (fuel : ℕ) :
    (consumer machine k₀).runClosedConfigFrom fuel (consumerConfig mark cfg₀ cfg₁) =
      consumerConfig mark cfg₀ <$> machine.runClosedConfigFrom fuel cfg₁ := by
  simp only [consumer, MultiTapeMachine.Composition.consumer, consumerConfig, runClosedConfigFrom,
    runConfigFrom_inputFromTape,
    runConfigFrom_embed, Functor.map_map]
  rfl

/-- Virtual-input redirection preserves a halting bound. -/
theorem consumer_halted (machine : MultiTapePTM k₁ Symbol State₁) (mark : Symbol)
    (cfg : Config k₀ Symbol State₀ Empty input) (fuel : ℕ)
    (hhalt : ∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom fuel (machine.initialConfig cfg.tapes.output))).support,
      final.tapes.state = none) :
    ∀ final ∈ (ProbComp.eval ((consumer machine k₀).runClosedConfigFrom fuel
      (consumerConfig mark cfg (machine.initialConfig cfg.tapes.output)))).support,
      final.tapes.state = none := by
  intro final hfinal
  rw [runClosedConfigFrom_consumer, ProbComp.eval_map] at hfinal
  obtain ⟨result, hresult, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  exact hhalt result hresult

/-- Once preparation and execution have been paid for, the continuation has its source law. -/
theorem eval_runClosedConfigFrom_continuation (machine : MultiTapePTM k₁ Symbol State₁)
    (mark : Symbol) (cfg : Config k₀ Symbol State₀ Empty input) (prepareTime runTime : ℕ)
    (hprepare : cfg.tapes.output.length + 4 ≤ prepareTime)
    (hrun : ∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom runTime (machine.initialConfig cfg.tapes.output))).support,
      final.tapes.state = none) :
    ProbComp.eval ((continuation machine k₀ mark).runClosedConfigFrom (prepareTime + runTime)
      (Sequential.start (continuation machine k₀ mark) (buffer k₁ cfg))) =
      (ProbComp.eval
        (machine.runClosedConfigFrom runTime (machine.initialConfig cfg.tapes.output))).map
        (fun final => Sequential.right (consumerConfig mark cfg final)) := by
  let prep := MultiTapeTM.prepareInput (k₁ + k₀) mark
  let initial := Sequential.start (ofDeterministic prep) (buffer k₁ cfg)
  have hdet := runFrom_prepare mark k₁ cfg
  change prep.runFrom initial.tapes (cfg.tapes.output.length + 4) = _ at hdet
  have hprep : prep.runFrom initial.tapes prepareTime = (ready mark k₁ cfg).tapes := by
    rw [prep.runFrom_eq_of_halt initial.tapes hprepare (by rw [hdet]; rfl), hdet]
  have hstate : ProbComp.eval ((ofDeterministic prep).runClosedConfigFrom prepareTime initial) =
      PMF.pure (ready mark k₁ cfg) := by
    rw [eval_runClosedConfigFrom_ofDeterministic, hprep]
    rfl
  change ProbComp.eval (((ofDeterministic prep).seq (consumer machine k₀)).runClosedConfigFrom
    _ (Sequential.left (consumer machine k₀) initial)) = _
  rw [eval_runClosedConfigFrom_seq _ _ _ prepareTime runTime
    (by simp [hstate, ready])
    (by simpa [hstate, start_ready] using consumer_halted machine mark cfg runTime hrun),
    Probability.PMF.monad_bind_eq_bind, hstate, PMF.pure_bind, start_ready,
    runClosedConfigFrom_consumer, ProbComp.eval_map, PMF.map_comp]
  rfl

/-- The handoff and continuation actually halt within the combined bound. -/
theorem continuation_halted (machine : MultiTapePTM k₁ Symbol State₁) (mark : Symbol)
    (cfg : Config k₀ Symbol State₀ Empty input) (prepareTime runTime : ℕ)
    (hprepare : cfg.tapes.output.length + 4 ≤ prepareTime)
    (hrun : ∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom runTime (machine.initialConfig cfg.tapes.output))).support,
      final.tapes.state = none) :
    ∀ final ∈ (ProbComp.eval ((continuation machine k₀ mark).runClosedConfigFrom
      (prepareTime + runTime)
      (Sequential.start (continuation machine k₀ mark) (buffer k₁ cfg)))).support,
      final.tapes.state = none := by
  intro final hfinal
  rw [eval_runClosedConfigFrom_continuation machine mark cfg prepareTime runTime hprepare hrun]
    at hfinal
  obtain ⟨result, hresult, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  change result.tapes.state.map Sum.inr = none
  rw [hrun result hresult]
  rfl

/-- A supported final configuration supplies a supported output word. -/
theorem output_mem (machine : MultiTapePTM k₀ Symbol State₀) (fuel : ℕ) (input : List Symbol)
    (final : Config k₀ Symbol State₀ Empty input)
    (hfinal : final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom fuel (machine.initialConfig input))).support) :
    final.tapes.output ∈ (ProbComp.eval (machine.runClosed fuel input)).support := by
  rw [runClosed_eq_map, ProbComp.eval_map]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, hfinal, rfl⟩

end Composition

/-- Feed `first`'s output to `second`, with separate work tapes and a charged input handoff. -/
noncomputable def comp {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type}
    (second : MultiTapePTM k₁ Symbol State₁) (first : MultiTapePTM k₀ Symbol State₀)
    (mark : Symbol) : MultiTapePTM (k₁ + k₀ + 2) Symbol
      (State₀ ⊕ ((MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState) ⊕ State₁)) :=
  (Composition.source first k₁).seq (Composition.continuation second k₀ mark)

variable {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type}
  (first : MultiTapePTM k₀ Symbol State₀) (second : MultiTapePTM k₁ Symbol State₁)
  (mark : Symbol) (input : List Symbol) (firstTime secondTime : ℕ)
  (hfirst : ∀ final ∈ (ProbComp.eval
    (first.runClosedConfigFrom firstTime (first.initialConfig input))).support,
    final.tapes.state = none)
  (hsecond : ∀ word ∈ (ProbComp.eval (first.runClosed firstTime input)).support,
    ∀ final ∈ (ProbComp.eval
      (second.runClosedConfigFrom secondTime (second.initialConfig word))).support,
      final.tapes.state = none)

include hfirst hsecond

/-- Composition preserves the full configuration distribution and charges the intermediate word.
The first phase takes `firstTime`, preparation at most `firstTime + 4`, and the second phase
`secondTime`. Both source bounds concern actual halting, including random stopping times. -/
theorem eval_runClosedConfigFrom_comp :
    ProbComp.eval ((second.comp first mark).runClosedConfigFrom
      (firstTime + (firstTime + 4 + secondTime)) ((second.comp first mark).initialConfig input)) =
      (do
        let sourceFinal ← ProbComp.eval (first.runClosedConfigFrom firstTime
          (first.initialConfig input))
        (ProbComp.eval (second.runClosedConfigFrom secondTime
          (second.initialConfig sourceFinal.tapes.output))).map
          (MultiTapeMachine.Composition.finalConfig mark sourceFinal)) := by
  have hlength (final : Config k₀ Symbol State₀ Empty input)
      (hfinal : final ∈ (ProbComp.eval
        (first.runClosedConfigFrom firstTime (first.initialConfig input))).support) :
      final.tapes.output.length ≤ firstTime :=
    first.length_output_eval_runClosed_le firstTime input final.tapes.output
      (Composition.output_mem first firstTime input final hfinal)
  change ProbComp.eval
    (((Composition.source first k₁).seq
      (Composition.continuation second k₀ mark)).runClosedConfigFrom
      _ (Sequential.left (Composition.continuation second k₀ mark)
        ((Composition.source first k₁).initialConfig input))) = _
  rw [eval_runClosedConfigFrom_seq _ _ _ firstTime (firstTime + 4 + secondTime)
    (by
      intro result hresult
      rw [Composition.runClosedConfigFrom_source, ProbComp.eval_map] at hresult
      obtain ⟨final, hfinal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      exact hfirst final hfinal)
    (by
      intro result hresult
      rw [Composition.runClosedConfigFrom_source, ProbComp.eval_map] at hresult
      obtain ⟨final, hfinal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      exact Composition.continuation_halted second mark final (firstTime + 4) secondTime
        (by have := hlength final hfinal; lia)
        (hsecond _ (Composition.output_mem first firstTime input final hfinal))),
    Composition.runClosedConfigFrom_source, ProbComp.eval_map]
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map]
  apply Probability.PMF.bind_congr_on_support
  intro final hfinal
  dsimp only [Function.comp_def]
  rw [Composition.eval_runClosedConfigFrom_continuation second mark final
    (firstTime + 4) secondTime (by have := hlength final hfinal; lia)
    (hsecond _ (Composition.output_mem first firstTime input final hfinal)), PMF.map_comp]
  rfl

/-- At the output level, the compiled machine realizes ordinary monadic composition. -/
theorem eval_comp :
    ProbComp.eval ((second.comp first mark).runClosed
      (firstTime + (firstTime + 4 + secondTime)) input) =
      (do
        let word ← ProbComp.eval (first.runClosed firstTime input)
        ProbComp.eval (second.runClosed secondTime word)) := by
  have h := congrArg (PMF.map (fun final => final.tapes.output))
    (eval_runClosedConfigFrom_comp first second mark input firstTime secondTime hfirst hsecond)
  simpa only [Probability.PMF.monad_bind_eq_bind, runClosed_eq_map, ProbComp.eval_map,
    PMF.map_bind, PMF.map_comp, PMF.bind_map,
    Function.comp_def, MultiTapeMachine.Composition.finalConfig_output] using h

/-- Every supported execution of the composed machine has halted within the combined bound. -/
theorem comp_halted :
    ∀ final ∈ (ProbComp.eval ((second.comp first mark).runClosedConfigFrom
      (firstTime + (firstTime + 4 + secondTime))
      ((second.comp first mark).initialConfig input))).support,
      final.tapes.state = none := by
  intro final hfinal
  rw [eval_runClosedConfigFrom_comp first second mark input firstTime secondTime hfirst hsecond]
    at hfinal
  obtain ⟨source, hsource, htarget⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
  obtain ⟨target, hmem, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htarget
  have hhalt := hsecond _ (Composition.output_mem first firstTime input source hsource)
    target hmem
  change (target.tapes.state.map Sum.inr).map Sum.inr = none
  rw [hhalt]
  rfl

end Turing.MultiTapePTM
