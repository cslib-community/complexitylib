/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Queue.WordRAM.RegisterDynamic

/-!
The original adaptive FIFO client is consumed by the existing dynamic execution/resource
interfaces. Raw dirty initialization, its six actual instructions, final potential and the
free external-controller boundary are preserved. The native exchange factor is uniform;
the old hand-written program's literal14/28 instruction claims are not reused.
-/

@[expose] public section

namespace ComplexityTests.QueueRegisterDynamic

open Cslib Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Queue.WordRAM

/-- Enqueue two values, dequeue the first and reinsert that observed value before the final
dequeue. The client never inspects either physical stack or its count words. -/
def cycle {w capacity : ℕ} (a b : ℕ) :
    (spec w capacity).Client (Option ℕ × Option ℕ) := do
  let _ ← (spec w capacity).call (.enqueue a)
  let _ ← (spec w capacity).call (.enqueue b)
  let first ← (spec w capacity).call .dequeue
  let _ ← (spec w capacity).call (.enqueue (first.getD 0))
  let second ← (spec w capacity).call .dequeue
  pure (first, second)

theorem cycle_valid {w capacity a b : ℕ} (hc : 2 ≤ capacity)
    (ha : Fits w a) (hb : Fits w b) :
    (spec w capacity).ValidHistory [] ((spec w capacity).runClient [] (cycle a b)).2.2 := by
  exact ⟨⟨by simpa using (show 0 < capacity by omega), ha⟩,
    ⟨⟨by simpa using (show 1 < capacity by omega), hb⟩,
    trivial, ⟨by simpa using (show 1 < capacity by omega), ha⟩, trivial, trivial⟩⟩

example {w capacity a b : ℕ} : (spec w capacity).runClient [] (cycle a b) =
    ((some a, some b), [a], [.enqueue a, .enqueue b, .dequeue, .enqueue a, .dequeue]) := rfl

/-- All registers and all physical cells initially contain dirty maximum words. -/
def stale : Data registers := ⟨fun _ => 15, fun _ => 15⟩

theorem stale_bounded : stale.Bounded 4 :=
  ⟨fun _ => (by decide : Fits 4 15), fun _ => (by decide : Fits 4 15)⟩

/-- The five adaptive native calls retain the final queue and terminal rear credit. -/
theorem adaptive_from_dirty : ∃ ready y traces,
    Exec 4 (initializeCode 3 2) stale ready 6 ∧
      DataStructure.Executes ((implementation 4 2).ExecOp 4)
        (cycle 0 15) ready (some 0, some 15) y traces ∧
      QueueRep 4 3 2 [0] y ∧
      6 + DataStructure.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        6 + 5 * (4 * Backend.factor family + 6) := by
  exact run_initialized (w := 4) (base := 3) (capacity := 2)
    (by decide) (by decide) (cycle 0 15) stale_bounded
    (cycle_valid (by decide) (by decide) (by decide))

-- No unused physical cell is cleared by the raw initializer.
example : (initialized 3 2 stale).mem = stale.mem := rfl

-- The original zero-capacity domain and dirty memory need no extra metadata cells.
example {x : Data registers} (hx : x.Bounded 1) : ∃ ready y traces,
    Exec 1 (initializeCode 0 0) x ready 6 ∧
      DataStructure.Executes ((implementation 1 0).ExecOp 1)
        ((spec 1 0).call .dequeue) ready none y traces ∧
      QueueRep 1 0 0 [] y ∧
      6 + DataStructure.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        6 + (4 * Backend.factor family + 6) := by
  have hrun : (spec 1 0).runClient [] ((spec 1 0).call .dequeue) =
      (none, [], [Queue.QueueOp.dequeue]) := rfl
  have h := run_initialized (w := 1) (base := 0) (capacity := 0)
    (by decide) (by decide) ((spec 1 0).call .dequeue) hx ⟨trivial, trivial⟩
  rw [hrun] at h
  simpa only [List.length_singleton, Nat.one_mul] using h

end ComplexityTests.QueueRegisterDynamic
