/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueFrame

/-! A preallocated queue transfers its rear stack while preserving all outside memory. -/

namespace ComplexityTests.WordRAMRealizationMemoryQueueFrame

open Cslib.WordRAM Cslib.DataStructure Cslib.WordRAM.Realization

private def front : Stack.Memory.Layout := ⟨⟨0, 1⟩, ⟨1, 2⟩⟩
private def rear : Stack.Memory.Layout := ⟨⟨3, 1⟩, ⟨4, 2⟩⟩

private theorem front_valid : front.Valid 4 2 :=
  ⟨rfl, by simp [front, Block.Owns], rfl, by decide⟩

private theorem rear_valid : rear.Valid 4 2 :=
  ⟨rfl, by simp [rear, Block.Owns], rfl, by decide⟩

private theorem disjoint : Disjoint front.footprint rear.footprint := by decide

-- Rear items1,2 encode FIFO[1,2]; cell9 is an inaccessible but preserved sentinel.
private def initial : Memory.State :=
  ⟨fun a => if a = 3 then 2 else if a = 4 then 1 else if a = 5 then 2 else
    if a = 9 then 7 else 0, 6⟩

private theorem initial_inv :
    (Queue.Memory.memRefinement front_valid rear_valid disjoint).inv initial := by
  refine ⟨⟨⟨by change 0 + 1 ≤ 6; decide, by change 1 + 2 ≤ 6; decide, by decide⟩,
    ⟨by change 3 + 1 ≤ 6; decide, by change 4 + 2 ≤ 6; decide, by decide⟩⟩, ?_⟩
  change Queue.Memory.Inv 4 2 [1, 2]
  refine ⟨by decide, ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> decide

private def afterDequeue : Memory.State :=
  (Memory.spec 4).clientState initial (Queue.Memory.memMethods front rear 4 2 .dequeue)

example : Modifies (front.footprint ∪ rear.footprint) initial.mem afterDequeue.mem ∧
    afterDequeue.frontier = initial.frontier :=
  MemoryQueueFrame.modifies_methods front_valid rear_valid disjoint .dequeue initial_inv trivial

-- The theorem protects all outside cells, including unallocated addresses.
example : afterDequeue.mem 9 = 7 := by
  have h := (MemoryQueueFrame.modifies_methods front_valid rear_valid disjoint .dequeue
    initial_inv trivial).1 9 (by decide)
  exact h

example : (Memory.spec 4).clientResult initial
    (Queue.Memory.memMethods front rear 4 2 .dequeue) = some 1 := by decide

-- The frame is deliberately weaker than global memory equality: the front count really changes.
example : afterDequeue.mem 0 = 1 := by decide

example : afterDequeue.mem ≠ initial.mem := by
  intro h
  have hcount := congrFun h 0
  have hbad : 1 = 0 := hcount
  cases hbad

-- External writes and frontier growth preserve exactly the supported representation.
private def extended : Memory.State := ⟨Function.update initial.mem 9 11, 8⟩

private theorem supported : ∀ a ∈ front.footprint ∪ rear.footprint,
    extended.mem a = initial.mem a := by
  intro a ha
  exact Function.update_of_ne (ne_of_mem_of_not_mem ha (by decide)) _ _

example : (Queue.Memory.memRefinement front_valid rear_valid disjoint).abs extended =
    (Queue.Memory.memRefinement front_valid rear_valid disjoint).abs initial :=
  MemoryQueueFrame.abs_congr front_valid rear_valid disjoint initial_inv supported

example : (Queue.Memory.memRefinement front_valid rear_valid disjoint).inv extended :=
  MemoryQueueFrame.inv_congr front_valid rear_valid disjoint initial_inv supported (by decide)

end ComplexityTests.WordRAMRealizationMemoryQueueFrame
