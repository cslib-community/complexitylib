/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (native method answer-observation regressions)

public import Complexity.Computability.WordRAM.Realization.Module
public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueMethod

/-!
# Answer observations need not encode operation arguments

The queue's native regressions exercise both operations using a single two-word answer emitter.
These edge cases distinguish the faithful common result encoding from its operation-indexed
observation: Unit answers can collide, while `none` and `some 0` remain different native results.
The original whole-label adapter remains available with its original dependent interface.
-/

public section

namespace ComplexityTests.WordRAMRealizationObservation

open Cslib Cslib.DataStructure Cslib.WordRAM.Realization
open MemoryQueueMethod

/-- Discarding an enqueue argument cannot faithfully encode the whole operation/result label. -/
theorem result_only_not_label_embedding :
    ¬Function.Injective (fun a : (Queue.queue ℕ).Label =>
      match a with
      | ⟨.enqueue _, _⟩ => (none : Option ℕ)
      | ⟨.dequeue, result⟩ => result) := by
  intro hi
  have h := @hi ⟨.enqueue 3, ()⟩ ⟨.enqueue 4, ()⟩ rfl
  have he : (Queue.QueueOp.enqueue 3 : Queue.QueueOp ℕ) = .enqueue 4 := congrArg Sigma.fst h
  injection he with hn
  omega

-- Faithfulness is retained on the common result carrier, including this tag collision edge.
example : optionWords none ≠ optionWords (some 0) := by
  intro h
  have he := optionWords.injective h
  cases he

-- The known operation selects the observation; no enqueue argument appears in either result word.
example (v : ℕ) : answer (.enqueue v) none = () ∧ answer .dequeue none = none := ⟨rfl, rfl⟩

-- Every runtime enqueue payload returns the same common result, through the actual memory method.
example (front rear : Stack.Memory.Layout) (u v : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (method ((front, rear), .enqueue u)) =
      (Memory.spec 0).clientResult s (method ((front, rear), .enqueue v)) := by
  change ((Memory.spec 0).runClient s
    ((Queue.Memory.memMethods front rear 0 0 (.enqueue u)).bind (fun _ => .pure none))).1 =
    ((Memory.spec 0).runClient s
      ((Queue.Memory.memMethods front rear 0 0 (.enqueue v)).bind (fun _ => .pure none))).1
  simp only [StateTransitionSpec.runClient_bind, StateTransitionSpec.runClient_pure]

end ComplexityTests.WordRAMRealizationObservation
