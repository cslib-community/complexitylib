/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.NativeRetention.InitialContext
import ComplexityTests.NativeBatchMetadata
import Mathlib.Tactic

/-!
# Actual original-input initialization and correlated native execution

A single constructed machine starts on the encoded rational instance/startup
input, with every work tape blank. Its first actual reply is unbounded and its
second request carries the context computed from that original input. Nonempty
cover data with fabricated initial proposals, empty ground and zero allowances
check the initialization semantics. The raw carrier does not yet enforce its
stored stop bit; these tests do not assert a source-admitted cover selector.
-/

noncomputable section
open Cslib Cslib.Probability Turing Turing.MultiTapeTM NativeOpenExecution
open StochasticOracle NativeRetention InitialContext
namespace ComplexityTests.NativeContextLoader

private def firstReply (value : ℕ) : Reply := ⟨List.replicate (value + 1) true, value + 1, 2⟩
private def secondReply (request : List Bool) (value : ℕ) : Reply :=
  ⟨request.reverse, value + 3, 5⟩
private def initial : Memory Unit ℕ := ⟨0, []⟩

private def environment : Environment Unit ℕ := fun query memory =>
  if memory.events = [] then
    NativeBatchMetadata.metadata.map fun value => (firstReply value, value)
  else PMF.pure (secondReply query.2 memory.privateState, memory.privateState)

private def outcome (data : Startup) (value : ℕ) : NativeRuntimeContext.Observation ℕ :=
  let first := firstReply value
  let selected := context data ++ frame first.word
  let second := secondReply selected value
  ⟨selected ++ second.word, tapeOfList selected, 0, fun _ => none,
    (initial.record ((), encoding data) first value).record ((), selected) second value⟩

/-- One code witness, outside both input and latent-response quantifiers. No context
word or prepared native work tape is provided by this client. -/
theorem one_machine_all_original_inputs :
    ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
      (machine : MultiTapePTM (4 + scratch) Bool S Unit), ∀ data : Startup,
      (NativeUnboundedExecution.terminal machine environment
        ⟨machine.initialConfig (encoding data), initial⟩).map
          (Option.map Cslib.Probability.NativeContextLoader.observe) =
        NativeBatchMetadata.metadata.map fun value => some (outcome data value) := by
  obtain ⟨scratch, S, hS, machine, hm⟩ := exists_original_input_runtime
  refine ⟨scratch, S, hS, machine, ?_⟩
  intro data
  rw [hm]
  simp only [environment, initial, PMF.bind_map, Memory.record,
    List.cons_ne_self, ↓reduceIte, PMF.pure_map]
  rfl

/-- Every finite reply length really occurs for the same original-input native
machine. Context preparation is not a response-length or finite-alphabet premise. -/
example : ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
    (machine : MultiTapePTM (4 + scratch) Bool S Unit), ∀ (data : Startup) (value : ℕ),
    some (outcome data value) ∈
      ((NativeUnboundedExecution.terminal machine environment
        ⟨machine.initialConfig (encoding data), initial⟩).map
          (Option.map Cslib.Probability.NativeContextLoader.observe)).support := by
  obtain ⟨scratch, S, hS, machine, hm⟩ := one_machine_all_original_inputs
  refine ⟨scratch, S, hS, machine, fun data value => ?_⟩
  rw [hm]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨value, NativeBatchMetadata.metadata_support value, rfl⟩

/-- The actual second query contains the original instance bytes after native
loading and reply-dependent context update. -/
example (data : Startup) (value : ℕ) :
    ((outcome data value).memory.events.head?.map fun event =>
      unframe (unframe event.request)) = some (encInput data.system) := by
  simp [outcome, Memory.record, context, NativeRuntimeContext.Header.initialWord,
    NativeRuntimeContext.Header.encode, header]

private def nontrivial : Startup :=
  ⟨⟨[[0], [1]], [1, 1], [1, 1], 1, [[0, 1]]⟩, 2, 3, [false, true]⟩

/-- The nonempty original incidence instance has a feasible nonnegative dual. -/
example : Valid nontrivial.system := by
  constructor
  · intro j
    rcases j with _ | (_ | j) <;> norm_num [nontrivial, List.getD]
  · intro e
    rcases e with _ | (_ | e) <;> norm_num [nontrivial, List.getD]
  · intro j
    rcases j with _ | (_ | j) <;>
      norm_num [nontrivial, elements, ground, List.getD, List.range_succ]

/-- An input proposal list claiming a full cover is ignored at initialization.
The native header algorithm sees a nonempty original ground and no actual replies. -/
example : (header nontrivial).stopped = false ∧ (header nontrivial).output = [] := by
  norm_num [header, initialDecision, Packets.decision, Packets.assemble, nontrivial,
    complete, output, retain, ground, covered, population]
  exact ⟨0, by decide⟩

/-- Original rows and runtime private/control data remain in the computed header. -/
example : (header nontrivial).originalInstance = encInput nontrivial.system ∧
    (header nontrivial).privateSelector = [false, true] ∧
    (header nontrivial).remainingTurns = 2 ∧
    (header nontrivial).opportunities = [true, true, true] := by decide

private def empty : Startup := ⟨⟨[], [], [], 1, [[99]]⟩, 0, 0, []⟩
example : (header empty).stopped = true ∧ (header empty).output = [] := by
  norm_num [header, initialDecision, Packets.decision, Packets.assemble, empty,
    complete, output, retain, ground, covered, population]

/-- The transport carrier still issues two raw calls even when the initializer's
stop bit is true. This checked limitation prevents treating loading as a completed
source stopping/zero-ground upper-policy theorem. -/
example (value : ℕ) : (header empty).stopped = true ∧
    (outcome empty value).memory.events.length = 2 := by
  constructor
  · norm_num [header, empty]
  · rfl

/-- Both actual invoices and external durations survive the pure loader unchanged. -/
example (data : Startup) (value : ℕ) :
    ((outcome data value).memory.events.map fun event => event.reply.tokens).sum =
        (2 * value + 4 : ℕ) ∧
      ((outcome data value).memory.events.map fun event => event.reply.duration).sum = 7 := by
  simp [outcome, firstReply, secondReply, initial, Memory.record]
  norm_num
  ring

end ComplexityTests.NativeContextLoader
