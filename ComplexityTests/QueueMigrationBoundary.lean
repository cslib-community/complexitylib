/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Queue.WordRAM.Dynamic
public import Complexity.DataStructure.Queue.Memory

/-!
# Queue initialization boundaries that a migration must preserve

The legacy register-count queue accepts arbitrary bounded dirty memory, preserves it during
initialization, and reserves `2 * capacity` cells. The current memory allocator instead reserves
two count cells as well and clears them. Both existing APIs are sound on their own hypotheses;
these checked clients identify the source/representation obligations of replacing one by the
other. The native operation-client theorem retains its documented external-controller and
argument-delivery boundary; no whole-client compiler or new backend is asserted here.
-/

@[expose] public section

namespace ComplexityTests.QueueMigrationBoundary

open Cslib Cslib.WordRAM Cslib.DataStructure

-- This is the original initializer theorem applied at the small boundary, with no zero-memory,
-- installed-frontier or extra-room hypothesis added to the arbitrary bounded input.
theorem legacy_small_initialize (x : Data 11) (hx : x.Bounded 2) :
    ∃ ready, Exec 2 (Queue.WordRAM.initializeCode 1 1) x ready 6 ∧
      Queue.WordRAM.Rep 2 1 1 [] [] ready ∧ ready.mem = x.mem :=
  Queue.WordRAM.initialize_exec hx (by decide) (by decide)

private def dirtyNative : Data 11 := ⟨fun _ => 3, fun _ => 3⟩

private theorem dirtyNative_bounded : dirtyNative.Bounded 2 :=
  ⟨fun _ => (by decide : Fits 2 3), fun _ => (by decide : Fits 2 3)⟩

example : ∃ ready, Exec 2 (Queue.WordRAM.initializeCode 1 1) dirtyNative ready 6 ∧
    Queue.WordRAM.Rep 2 1 1 [] [] ready ∧ ready.mem = (fun _ => 3) :=
  legacy_small_initialize dirtyNative dirtyNative_bounded

/-- A valid queue client uses the largest two-bit word, then observes it through dequeue. -/
private def maxWordClient : (Queue.WordRAM.spec 2 1).Client (Option ℕ) := do
  (Queue.WordRAM.spec 2 1).call (.enqueue 3)
  (Queue.WordRAM.spec 2 1).call .dequeue

private theorem maxWordClient_valid :
    (Queue.WordRAM.spec 2 1).ValidHistory []
      ((Queue.WordRAM.spec 2 1).clientHistory [] maxWordClient) :=
  ⟨⟨by decide, by decide⟩, trivial, trivial⟩

-- Actual existing RAM executions, including the charged six-instruction initializer.
example : ∃ ready y traces, Exec 2 (Queue.WordRAM.initializeCode 1 1) dirtyNative ready 6 ∧
    DataStructure.Executes ((Queue.WordRAM.implementation 2 1).ExecOp 2)
      maxWordClient ready (some 3) y traces ∧
    Queue.WordRAM.QueueRep 2 1 1 [] y ∧
    6 + DataStructure.total DynamicProgram.OperationTrace.instructions traces +
      Queue.WordRAM.potential y ≤ 34 :=
  Queue.WordRAM.run_initialized (by decide) (by decide) maxWordClient
    dirtyNative_bounded maxWordClient_valid

-- End3 fits two bits, but adding the new two count cells gives end5, which does not.
example : Fits 2 1 ∧ Fits 2 (1 + 2 * 1) ∧
    ¬Fits 2 (1 + (Queue.Memory.allocator 2 1).room) := by decide

private def dirtyMemory : Memory.State := ⟨fun _ => 3, 1⟩
private noncomputable abbrev allocator := Queue.Memory.allocator 3 1
private noncomputable def allocated : Memory.State :=
  (Memory.spec 3).clientState dirtyMemory allocator.alloc

-- A separate width-three case meets ALL the new allocator's actual hypotheses on dirty memory.
example : Memory.WellFormed 3 dirtyMemory :=
  ⟨by decide, fun _ => (by decide : Fits 3 3)⟩

example : allocator.Pre dirtyMemory := Queue.Memory.pre_allocator dirtyMemory

private theorem allocator_room : Fits 3 (dirtyMemory.frontier + allocator.room) := by decide

-- At the same larger width, the legacy initializer still preserves the identical dirty image.
example : ∃ ready, Exec 3 (Queue.WordRAM.initializeCode 1 1) dirtyNative ready 6 ∧
    Queue.WordRAM.Rep 3 1 1 [] [] ready ∧ ready.mem = dirtyMemory.mem :=
  Queue.WordRAM.initialize_exec
    ⟨fun _ => (by decide : Fits 3 3), fun _ => (by decide : Fits 3 3)⟩ (by decide) (by decide)

example : (Memory.spec 3).ValidHistory dirtyMemory
    ((Memory.spec 3).clientHistory dirtyMemory allocator.alloc) :=
  (allocator.allocates dirtyMemory (Queue.Memory.pre_allocator dirtyMemory)
    allocator_room).validHistory

-- The actual allocator returns two distinct layouts, with separate count and item cells.
example : let (front, back) := (Memory.spec 3).clientResult dirtyMemory allocator.alloc
    front.count = ⟨1, 1⟩ ∧ front.items = ⟨2, 1⟩ ∧
      back.count = ⟨3, 1⟩ ∧ back.items = ⟨4, 1⟩ := ⟨rfl, rfl, rfl, rfl⟩

example : (Memory.spec 3).clientHistory dirtyMemory allocator.alloc =
    [.alloc 1, .allocDirty 1, .alloc 1, .allocDirty 1] := rfl

-- Count cells are cleared, dirty item cells are retained, and the real frontier is 5.
example : allocated.frontier = 5 ∧ allocated.mem 1 = 0 ∧ allocated.mem 3 = 0 ∧
    allocated.mem 2 = 3 ∧ allocated.mem 4 = 3 ∧ allocated.mem 0 = 3 := by decide

private theorem allocation_changes_dirty_memory : allocated.mem ≠ dirtyMemory.mem := by
  intro h
  have hcount : (0 : ℕ) = 3 := congrFun h 1
  exact (by decide : (0 : ℕ) ≠ 3) hcount

-- Capacity zero is also in the old domain at width one; the new two count cells do not fit.
example (x : Data 11) (hx : x.Bounded 1) :
    ∃ ready, Exec 1 (Queue.WordRAM.initializeCode 0 0) x ready 6 ∧
      Queue.WordRAM.Rep 1 0 0 [] [] ready ∧ ready.mem = x.mem :=
  Queue.WordRAM.initialize_exec hx (by decide) (by decide)

example : Fits 1 1 ∧ Fits 1 (0 + 2 * 0) ∧
    ¬Fits 1 (0 + (Queue.Memory.allocator 1 0).room) := by decide

-- Width zero was already outside the old initializer's domain.
example : ¬Fits 0 1 := by decide

end ComplexityTests.QueueMigrationBoundary
