/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.WordRAM.Queue.Dynamic

/-!
# A worked adaptive FIFO example

Enqueue `a`, enqueue `b`, dequeue the oldest value, then enqueue the observed value again.
The final dequeue must return `b`, leaving `[a]`. The reinsertion is adaptive: it uses the
observed word, rather than reading the hidden FIFO list. This exercises a rear-to-front transfer,
a nonempty-front dequeue, and an enqueue while both stack regions contain live values.
-/

@[expose] public section

open Cslib Cslib.WordRAM
open Cslib.Algorithms.Lean.Queue

namespace WordRAMQueueTest

/-- An adaptive FIFO client, with no access to either stack representation. -/
def cycle {w capacity : ℕ} (a b : ℕ) :
    (WordRAM.Queue.spec w capacity).Client (Option ℕ × Option ℕ) :=
  .liftBind (.enqueue a) fun _ =>
  .liftBind (.enqueue b) fun _ =>
  .liftBind .dequeue fun first =>
  .liftBind (.enqueue (first.getD 0)) fun _ =>
  .liftBind .dequeue fun second => .pure (first, second)

example {w capacity a b : ℕ} :
    (WordRAM.Queue.spec w capacity).runClient [] (cycle a b) =
      ((some a, some b), [a], [.enqueue a, .enqueue b, .dequeue, .enqueue a, .dequeue]) := rfl

theorem cycle_valid {w capacity a b : ℕ} (hc : 2 ≤ capacity) (ha : Fits w a) (hb : Fits w b) :
    (WordRAM.Queue.spec w capacity).ValidHistory []
      ((WordRAM.Queue.spec w capacity).runClient [] (cycle a b)).2.2 := by
  exact ⟨⟨by simpa using (show 0 < capacity by omega), ha⟩,
    ⟨⟨by simpa using (show 1 < capacity by omega), hb⟩,
    trivial, ⟨by simpa using (show 1 < capacity by omega), ha⟩, trivial, trivial⟩⟩

/-- The backend-independent FIFO trace becomes actual queue-operation executions. -/
example {w base capacity a b : ℕ} (h1 : Fits w 1)
    (hc : Fits w (base + 2 * capacity)) (hsize : 2 ≤ capacity)
    (ha : Fits w a) (hb : Fits w b) {x : Data 11}
    (hr : WordRAM.Queue.QueueRep w base capacity [] x) :
    ∃ y traces,
      Stateful.Executes ((WordRAM.Queue.implementation w capacity).ExecOp w)
        (cycle a b) x (some a, some b) y traces ∧
      WordRAM.Queue.QueueRep w base capacity [a] y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces +
        WordRAM.Queue.potential y ≤ 70 + WordRAM.Queue.potential x := by
  have hv : (WordRAM.Queue.spec w capacity).ValidHistory []
      ((WordRAM.Queue.spec w capacity).runClient [] (cycle a b)).2.2 :=
    ⟨⟨by simpa using (show 0 < capacity by omega), ha⟩,
      ⟨⟨by simpa using (show 1 < capacity by omega), hb⟩,
      trivial, ⟨by simpa using (show 1 < capacity by omega), ha⟩, trivial, trivial⟩⟩
  simpa only [cycle, Stateful.Spec.runClient_liftBind, Stateful.Spec.runClient_pure,
    WordRAM.Queue.spec, queue,
    List.nil_append, List.cons_append, List.tail_cons, List.head?_cons,
    Option.getD_some, List.length_cons, List.length_nil] using
    WordRAM.Queue.run_client h1 hc (cycle a b) hr hv

-- Nonzero unused memory is legitimate: only live prefixes carry queue contents.
private def stale : Data 11 := ⟨fun _ => 15, fun _ => 15⟩

private theorem stale_bounded : stale.Bounded 4 :=
  ⟨fun _ => (by decide : Fits 4 15), fun _ => (by decide : Fits 4 15)⟩

example : ∃ ready, Exec 4 (WordRAM.Queue.initializeCode 3 2) stale ready 6 ∧
    WordRAM.Queue.Rep 4 3 2 [] [] ready ∧ ready.mem = stale.mem :=
  WordRAM.Queue.initialize_exec stale_bounded (by decide) (by decide)

-- All five adaptive calls work from an initialized representation, including a zero word.
example : ∃ ready y traces, Exec 4 (WordRAM.Queue.initializeCode 3 2) stale ready 6 ∧
    Stateful.Executes ((WordRAM.Queue.implementation 4 2).ExecOp 4)
      (cycle 0 15) ready (some 0, some 15) y traces ∧
    WordRAM.Queue.QueueRep 4 3 2 [0] y ∧
    6 + Stateful.total DynamicProgram.OperationTrace.instructions traces +
      WordRAM.Queue.potential y ≤ 76 := by
  exact WordRAM.Queue.run_initialized (by decide) (by decide) (cycle 0 15)
    stale_bounded (cycle_valid (by decide) (by decide) (by decide))

-- Capacity zero allows an empty dequeue, but no enqueue (even of zero), and capacity/width bounds
-- are enforced.
example :
    ¬(WordRAM.Queue.spec 4 0).valid [] (.enqueue 0) ∧
    (WordRAM.Queue.spec 4 0).valid [] .dequeue ∧
    ¬(WordRAM.Queue.spec 4 2).valid [0, 15] (.enqueue 1) ∧
    ¬(WordRAM.Queue.spec 4 2).valid [] (.enqueue 16) :=
  ⟨by decide, trivial, by decide, by decide⟩

-- A refill of two rear words costs 28 including halt: a false 27 bound is rejected.
example {x y : Data 11} {a : Option ℕ} {trace : DynamicProgram.OperationTrace}
    (hr : WordRAM.Queue.Rep 4 3 2 [] [15, 0] x)
    (he : (WordRAM.Queue.implementation 4 2).ExecOp 4 x .dequeue a y trace) :
    trace.instructions = 28 ∧ ¬trace.instructions ≤ 27 := by
  have h := WordRAM.Queue.instructions_eq (by decide) hr trivial he
  change trace.instructions = 28 at h
  omega

-- Empty and zero-valued observations are semantically distinct, and the footprint size is `2 * c`.
example :
    (WordRAM.Queue.pairStep ([], []) .dequeue).2 = none ∧
    (WordRAM.Queue.pairStep ([], [0]) .dequeue).2 = some 0 ∧
    (WordRAM.Queue.footprint 3 2).card = 4 :=
  ⟨rfl, rfl, WordRAM.Queue.footprint_card _ _⟩

end WordRAMQueueTest
