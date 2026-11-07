/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Queue.WordRAM.RegisterDynamic

/-!
# A worked adaptive FIFO example

Enqueue `a`, enqueue `b`, dequeue the oldest value, then enqueue the observed value again.
The final dequeue must return `b`, leaving `[a]`. The reinsertion is adaptive: it uses the
observed word, rather than reading the hidden FIFO list. This exercises a rear-to-front transfer,
a nonempty-front dequeue, and an enqueue while both stack regions contain live values.
-/

@[expose] public section

open Cslib Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Queue

namespace WordRAMQueueTest

/-- An adaptive FIFO client, with no access to either stack representation. -/
def cycle {w capacity : ℕ} (a b : ℕ) :
    (Queue.WordRAM.spec w capacity).Client (Option ℕ × Option ℕ) :=
  .liftBind (.enqueue a) fun _ =>
  .liftBind (.enqueue b) fun _ =>
  .liftBind .dequeue fun first =>
  .liftBind (.enqueue (first.getD 0)) fun _ =>
  .liftBind .dequeue fun second => .pure (first, second)

example {w capacity a b : ℕ} :
    (Queue.WordRAM.spec w capacity).runClient [] (cycle a b) =
      ((some a, some b), [a], [.enqueue a, .enqueue b, .dequeue, .enqueue a, .dequeue]) := rfl

theorem cycle_valid {w capacity a b : ℕ} (hc : 2 ≤ capacity) (ha : Fits w a) (hb : Fits w b) :
    (Queue.WordRAM.spec w capacity).ValidHistory []
      ((Queue.WordRAM.spec w capacity).runClient [] (cycle a b)).2.2 := by
  exact ⟨⟨by simpa using (show 0 < capacity by omega), ha⟩,
    ⟨⟨by simpa using (show 1 < capacity by omega), hb⟩,
    trivial, ⟨by simpa using (show 1 < capacity by omega), ha⟩, trivial, trivial⟩⟩

/-- The backend-independent FIFO trace becomes actual queue-operation executions. -/
example {w base capacity a b : ℕ} (h1 : Fits w 1)
    (hsize : 2 ≤ capacity)
    (ha : Fits w a) (hb : Fits w b) {x : Data Queue.WordRAM.registers}
    (hr : Queue.WordRAM.QueueRep w base capacity [] x) :
    ∃ y traces,
      DataStructure.Executes ((Queue.WordRAM.implementation w capacity).ExecOp w)
        (cycle a b) x (some a, some b) y traces ∧
      Queue.WordRAM.QueueRep w base capacity [a] y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces +
        Queue.WordRAM.potential y ≤
          5 * (4 * Backend.factor Queue.WordRAM.family + 6) + Queue.WordRAM.potential x := by
  have hv : (Queue.WordRAM.spec w capacity).ValidHistory []
      ((Queue.WordRAM.spec w capacity).runClient [] (cycle a b)).2.2 :=
    ⟨⟨by simpa using (show 0 < capacity by omega), ha⟩,
      ⟨⟨by simpa using (show 1 < capacity by omega), hb⟩,
      trivial, ⟨by simpa using (show 1 < capacity by omega), ha⟩, trivial, trivial⟩⟩
  simpa only [cycle, DataStructure.StateTransitionSpec.runClient_liftBind,
    DataStructure.StateTransitionSpec.runClient_pure,
    Queue.WordRAM.spec, queue,
    List.nil_append, List.cons_append, List.tail_cons, List.head?_cons,
    Option.getD_some, List.length_cons, List.length_nil] using
    Queue.WordRAM.run_client h1 (cycle a b) hr hv

-- Nonzero unused memory is legitimate: only live prefixes carry queue contents.
private def stale : Data Queue.WordRAM.registers := ⟨fun _ => 15, fun _ => 15⟩

private theorem stale_bounded : stale.Bounded 4 :=
  ⟨fun _ => (by decide : Fits 4 15), fun _ => (by decide : Fits 4 15)⟩

example : ∃ ready, Exec 4 (Queue.WordRAM.initializeCode 3 2) stale ready 6 ∧
    Queue.WordRAM.Rep 4 3 2 [] [] ready ∧ ready.mem = stale.mem :=
  ⟨Queue.WordRAM.initialized 3 2 stale,
    (Queue.WordRAM.initialize_exec stale_bounded (by decide)).1,
    Queue.WordRAM.initialized_rep stale_bounded (by decide), rfl⟩

-- All five adaptive calls work from an initialized representation, including a zero word.
example : ∃ ready y traces, Exec 4 (Queue.WordRAM.initializeCode 3 2) stale ready 6 ∧
    DataStructure.Executes ((Queue.WordRAM.implementation 4 2).ExecOp 4)
      (cycle 0 15) ready (some 0, some 15) y traces ∧
    Queue.WordRAM.QueueRep 4 3 2 [0] y ∧
    6 + DataStructure.total DynamicProgram.OperationTrace.instructions traces +
      Queue.WordRAM.potential y ≤
        6 + 5 * (4 * Backend.factor Queue.WordRAM.family + 6) := by
  exact Queue.WordRAM.run_initialized (w := 4) (base := 3) (capacity := 2)
    (by decide) (by decide) (cycle 0 15)
    stale_bounded (cycle_valid (by decide) (by decide) (by decide))

-- Capacity zero allows an empty dequeue, but no enqueue (even of zero), and capacity/width bounds
-- are enforced.
example :
    ¬(Queue.WordRAM.spec 4 0).valid [] (.enqueue 0) ∧
    (Queue.WordRAM.spec 4 0).valid [] .dequeue ∧
    ¬(Queue.WordRAM.spec 4 2).valid [0, 15] (.enqueue 1) ∧
    ¬(Queue.WordRAM.spec 4 2).valid [] (.enqueue 16) :=
  ⟨by decide, trivial, by decide, by decide⟩

-- The realized program has one uniform factor rather than the removed hand-code's exact28
-- refill clock. Its actual trace still pays control, commit and halt with terminal credit.
example {x y : Data Queue.WordRAM.registers} {a : Option ℕ}
    {trace : DynamicProgram.OperationTrace}
    (hr : Queue.WordRAM.Rep 4 3 2 [] [15, 0] x)
    (he : (Queue.WordRAM.implementation 4 2).ExecOp 4 x .dequeue a y trace) :
    trace.instructions + Queue.WordRAM.potential y ≤
      4 * Backend.factor Queue.WordRAM.family + 6 + Queue.WordRAM.potential x := by
  obtain ⟨z, n, hz, _, _, _, hp⟩ := Queue.WordRAM.execute (by decide) hr .dequeue trivial
  obtain ⟨rfl, hn⟩ := he.eq_of_exec hz
  rw [hn]
  exact hp

-- Empty and zero-valued observations are semantically distinct, and the footprint size is `2 * c`.
example :
    (Queue.WordRAM.pairStep ([], []) .dequeue).2 = none ∧
    (Queue.WordRAM.pairStep ([], [0]) .dequeue).2 = some 0 ∧
    (Queue.WordRAM.footprint 3 2).card = 4 :=
  ⟨rfl, rfl, Queue.WordRAM.footprint_card _ _⟩

end WordRAMQueueTest
