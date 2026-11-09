/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.NativeRetention.InitialContext
import ComplexityTests.NativeBatchMetadata
import Mathlib.Tactic

/-!
# Actual native stopping before the first query

A single machine, starting with blank work tapes on startup input, handles both
initial stopping and live correlated unbounded replies. True stop bits emit the
computed mask without calls; the live branch still has the old two-query limit.
-/

noncomputable section
open Cslib Cslib.Probability Turing Turing.MultiTapeTM NativeOpenExecution
open StochasticOracle NativeRetention InitialContext
namespace ComplexityTests.NativeStopGuard

/-- Stop dominates even arbitrary native consumer code. The frame is actually
read from tape, with no oracle state/event/resource change. -/
example {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit) (env : Environment Unit P)
    (input output payload : List Bool) (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal (Cslib.Probability.NativeStopGuard.machine consumer) env
      (NativeContextLoader.loadedStart (Cslib.Probability.NativeStopGuard.machine consumer)
        input (Cslib.Probability.NativeStopGuard.packet true output payload) memory)).map
          (Option.map fun world => (world.config.tapes.output, world.memory)) =
      PMF.pure (some (output, memory)) := by
  rw [Cslib.Probability.NativeStopGuard.terminal_stop, PMF.pure_map]
  rfl

private def firstReply (value : ℕ) : Reply := ⟨List.replicate (value + 1) true, value + 1, 2⟩
private def secondReply (request : List Bool) (value : ℕ) : Reply :=
  ⟨request.reverse, value + 3, 5⟩
private def initial : Memory Unit ℕ := ⟨0, []⟩
private def environment : Environment Unit ℕ := fun query memory =>
  if memory.events = [] then
    NativeBatchMetadata.metadata.map fun value => (firstReply value, value)
  else PMF.pure (secondReply query.2 memory.privateState, memory.privateState)

private def stoppedOutcome (data : Startup) : NativeRuntimeContext.Observation ℕ :=
  ⟨(header data).output,
    tapeOfList (Cslib.Probability.NativeStopGuard.packet true (header data).output (context data)),
    (1 + 2 * (header data).output.length + 1 : ℕ), fun _ => none, initial⟩

private def liveOutcome (data : Startup) (value : ℕ) : NativeRuntimeContext.Observation ℕ :=
  let first := firstReply value
  let selected := Cslib.Probability.NativeStopGuard.packet false (header data).output
    (context data) ++
    frame first.word
  let second := secondReply selected value
  ⟨selected ++ second.word, tapeOfList selected, 0, fun _ => none,
    (initial.record ((), encoding data) first value).record ((), selected) second value⟩

/-- The same code handles both branches for every startup datum. Stop flags are
computed by the initializer; the client provides no prepared context or machine law. -/
theorem one_machine_control :
    ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
      (code : MultiTapePTM (4 + scratch) Bool S Unit), ∀ data : Startup,
      (NativeUnboundedExecution.terminal code environment
        ⟨code.initialConfig (encoding data), initial⟩).map
          (Option.map NativeContextLoader.observe) =
        if (header data).stopped then PMF.pure (some (stoppedOutcome data))
        else NativeBatchMetadata.metadata.map fun value => some (liveOutcome data value) := by
  obtain ⟨scratch, S, hS, code, hc⟩ := exists_guarded_original_input
  refine ⟨scratch, S, hS, code, ?_⟩
  intro data
  rw [hc]
  by_cases hs : (header data).stopped = true
  · simp only [hs, ↓reduceIte]
    rfl
  · simp only [hs, ↓reduceIte, environment, initial, PMF.bind_map,
      Memory.record, List.cons_ne_self, PMF.pure_map]
    rfl

private def coverInput (turns opportunities : ℕ) : Startup :=
  ⟨⟨[[0], [1]], [1, 1], [1, 1], 1, [[0, 1]]⟩, turns, opportunities, [false, true]⟩

/-- Nonempty ground and a fabricated cover do not stop a live initialization. -/
private theorem cover_live : (header (coverInput 2 3)).stopped = false := by
  norm_num [header, initialDecision, Packets.decision, Packets.assemble, coverInput,
    complete, output, retain, ground, covered, population]
  exact ⟨0, by decide⟩

/-- Zero turns and zero opportunities actually prevent the calls now, rather than
merely setting an ignored header field. -/
example : ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
    (code : MultiTapePTM (4 + scratch) Bool S Unit),
    ∀ data ∈ [coverInput 0 3, coverInput 2 0],
    (NativeUnboundedExecution.terminal code environment
      ⟨code.initialConfig (encoding data), initial⟩).map
        (Option.map NativeContextLoader.observe) = PMF.pure (some (stoppedOutcome data)) := by
  obtain ⟨scratch, S, hS, code, hc⟩ := one_machine_control
  refine ⟨scratch, S, hS, code, fun data hd => ?_⟩
  rw [hc]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> simp [header, coverInput]

private def emptyGround : Startup := ⟨⟨[[0], [1]], [1, 1], [], 1, [[99]]⟩, 3, 2, [true]⟩
private theorem completed : (header emptyGround).stopped = true ∧
    (header emptyGround).output = [false, false] := by
  norm_num [header, initialDecision, Packets.decision, Packets.assemble, emptyGround,
    complete, output, retain, ground, covered, population]

/-- Completion emits the original two-candidate empty-family mask, not just an
empty word, without sampling a response. -/
example : ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
    (code : MultiTapePTM (4 + scratch) Bool S Unit),
    ((NativeUnboundedExecution.terminal code environment
      ⟨code.initialConfig (encoding emptyGround), initial⟩).map
        (Option.map NativeContextLoader.observe)).map
          (Option.map fun result => (result.output, result.memory)) =
      PMF.pure (some ([false, false], initial)) := by
  obtain ⟨scratch, S, hS, code, hc⟩ := one_machine_control
  refine ⟨scratch, S, hS, code, ?_⟩
  rw [hc, completed.1]
  simp [stoppedOutcome, completed.2]

/-- The live branch retains every positively supported unbounded response and the
same latent state for the second invoice; there is no finite response approximation. -/
example : ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
    (code : MultiTapePTM (4 + scratch) Bool S Unit), ∀ value : ℕ,
    some (liveOutcome (coverInput 2 3) value) ∈
      ((NativeUnboundedExecution.terminal code environment
        ⟨code.initialConfig (encoding (coverInput 2 3)), initial⟩).map
          (Option.map NativeContextLoader.observe)).support := by
  obtain ⟨scratch, S, hS, code, hc⟩ := one_machine_control
  refine ⟨scratch, S, hS, code, fun value => ?_⟩
  rw [hc, cover_live]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨value, NativeBatchMetadata.metadata_support value, rfl⟩

/-- Initial dispatch is not a post-response budget controller: a one-turn live
input still has two recorded calls. This is an explicit limit of the current code. -/
example : ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
    (code : MultiTapePTM (4 + scratch) Bool S Unit),
    ((NativeUnboundedExecution.terminal code environment
      ⟨code.initialConfig (encoding (coverInput 1 3)), initial⟩).map
        (Option.map NativeContextLoader.observe)).map
          (Option.map fun result => result.memory.events.length) = PMF.pure (some 2) := by
  obtain ⟨scratch, S, hS, code, hc⟩ := one_machine_control
  refine ⟨scratch, S, hS, code, ?_⟩
  have hs : (header (coverInput 1 3)).stopped = false := by
    norm_num [header, initialDecision, Packets.decision, Packets.assemble, coverInput,
      complete, output, retain, ground, covered, population]
    exact ⟨0, by decide⟩
  rw [hc, hs]
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.map_comp]
  have he : (Option.map (fun result => result.memory.events.length) ∘
      (fun value => some (liveOutcome (coverInput 1 3) value))) = fun _ => some 2 := by
    funext value
    rfl
  rw [he]
  exact PMF.map_const _ _

end ComplexityTests.NativeStopGuard
