/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.WordRAM.DynamicArray

/-!
# Doubling-array execution tests and axiom guards

Concrete symbolic executions trace the twelve-register doubling array across three capacity
doublings (`1 → 2 → 4 → 8`), checking exact register contents, live and historical memory
blocks, zeroed spare cells, frontier growth (`1 → 3 → 7 → 15`), and exact instruction counts
(`15` for initialization, `7` without growth, `34`, `49`, and `79` across the three doublings,
each attaining the exact `49`-instruction potential bound). An adaptive `Stateful` client also
interleaves appends with indexed reads.
-/

@[expose] public section

open Cslib Cslib.WordRAM
open Cslib.Algorithms.WordRAM

namespace DynamicArrayTest

/-- Initial blank state on 12 registers. -/
def blank : Data 12 := ⟨fun _ => 0, fun _ => 0⟩

theorem blank_bounded : blank.Bounded 8 :=
  ⟨fun _ => fits_zero 8, fun _ => fits_zero 8⟩

/-- Snapshot the persistent doubling-array registers `(ptr, len, cap, frontier)` and a list of
memory addresses, paired with the executed instruction count. -/
def snapshot (addrs : List ℕ) (yn : Data 12 × ℕ) : ℕ × (ℕ × ℕ × ℕ × ℕ) × List ℕ :=
  (yn.2,
   (yn.1.regs DynamicArray.ptr, yn.1.regs DynamicArray.len,
    yn.1.regs DynamicArray.cap, yn.1.regs DynamicArray.frontier),
   addrs.map yn.1.mem)

/-- Concrete state representing `vs` at `(ptrVal, capVal, frontierVal)`. -/
def mkState (ptrVal lenVal capVal frontierVal argVal : ℕ) (memList : List ℕ) : Data 12 where
  regs i :=
    if i = DynamicArray.ptr then ptrVal
    else if i = DynamicArray.len then lenVal
    else if i = DynamicArray.cap then capVal
    else if i = DynamicArray.frontier then frontierVal
    else if i = DynamicArray.arg then argVal
    else 0
  mem a := memList.getD a 0

/-- Concrete witness for the doubling-array representation invariant `Rep` after doubling `1 → 2`
on `[10, 20]`. -/
def repTwoState : Data 12 := mkState 1 2 2 3 0 [10, 10, 20]

theorem repTwo_rep : DynamicArray.Rep [10, 20] repTwoState where
  length_eq := rfl
  capacity_pos := by decide
  length_le := by decide
  capacity_le := by decide
  pointer_eq := rfl
  frontier_eq := rfl
  contents i := by fin_cases i <;> rfl

theorem repTwo_boundedRep : DynamicArray.BoundedRep 8 [10, 20] repTwoState :=
  ⟨⟨fun i => by fin_cases i <;> decide,
    fun a => by
      rcases a with _ | _ | _ | a <;> simp [repTwoState, mkState, Fits]⟩,
   repTwo_rep⟩

/-- Concrete execution trace across `initProgram`, five appends (`1 → 2 → 4 → 8` capacity
doublings), and `getProgram`, plus precondition rejections for out-of-range read and word overflow.
-/
example :
    -- Init allocates the one-word block at address 0, zeroes it and sets frontier = 1 in 15 steps.
    (DynamicArray.initProgram.eval 8 4 blank).map (snapshot [0, 1]) =
      some (15, (0, 0, 1, 1), [0, 0]) ∧
    -- First append: capacity 1 suffices; write 10 at address 0 in 7 steps.
    (DynamicArray.program.eval 8 4 (mkState 0 0 1 1 10 [0])).map (snapshot [0, 1]) =
      some (7, (0, 1, 1, 1), [10, 0]) ∧
    -- Second append doubles 1 → 2, allocates [1, 3), copies 10 and writes 20.
    -- Frontier becomes 3; amortized charge is 34 + 30 - 15 = 49.
    (DynamicArray.program.eval 8 4 (mkState 0 1 1 1 20 [10])).map (snapshot [0, 1, 2, 3]) =
      some (34, (1, 2, 2, 3), [10, 10, 20, 0]) ∧
    -- Third append doubles 2 → 4, copies to addresses 3..4, writes 30 at 5 and leaves cell 6 zero.
    -- Frontier becomes 7; amortized charge is 49 + 30 - 30 = 49.
    (DynamicArray.program.eval 8 8 (mkState 1 2 2 3 30 [10, 10, 20])).map
      (snapshot [3, 4, 5, 6]) =
      some (49, (3, 3, 4, 7), [10, 20, 30, 0]) ∧
    -- Fourth append uses spare capacity, writing 40 at address 6 in 7 steps.
    (DynamicArray.program.eval 8 8
      (mkState 3 3 4 7 40 [10, 10, 20, 10, 20, 30, 0])).map (snapshot [3, 4, 5, 6]) =
      some (7, (3, 4, 4, 7), [10, 20, 30, 40]) ∧
    -- Fifth append doubles 4 → 8, copies to 7..10, writes 50 at 11 and zeroes 12..14.
    -- Frontier becomes 15 < 4 * 5 = 20; amortized charge is 79 + 30 - 60 = 49.
    (DynamicArray.program.eval 8 10
      (mkState 3 4 4 7 50 [10, 10, 20, 10, 20, 30, 40])).map
      (snapshot [7, 8, 9, 10, 11, 12, 13, 14]) =
      some (79, (7, 5, 8, 15), [10, 20, 30, 40, 50, 0, 0, 0]) ∧
    -- Read index 4 from the block at address 7, returning 50 in 2 steps.
    (DynamicArray.getProgram.eval 8 0
      (mkState 7 5 8 15 4 [10, 10, 20, 10, 20, 30, 40, 10, 20, 30, 40, 50, 0, 0, 0])).map
      (fun yn => (yn.2, yn.1.regs DynamicArray.temp)) =
      some (2, 50) ∧
    -- Reject an out-of-range read and an append value that overflows the word width.
    ¬(DynamicArray.spec 8).valid [10, 20] (.get 2) ∧
    ¬(DynamicArray.spec 4).valid [10, 20] (.append 5) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- Adaptive client: append `11` and `22`, read index `0`, then append the observed value plus
`33` and read index `2`. -/
def adaptiveClient : (DynamicArray.spec 8).Client (ℕ × ℕ) :=
  .liftBind (.append 11) fun _ =>
  .liftBind (.append 22) fun _ =>
  .liftBind (.get 0) fun (first : ℕ) =>
  .liftBind (.append (first + 33)) fun _ =>
  .liftBind (.get 2) fun (third : ℕ) => .pure (first, third)

example : (DynamicArray.spec 8).runClient [] adaptiveClient =
    ((11, 44), [11, 22, 44],
     [.append 11, .append 22, .get 0, .append 44, .get 2]) := rfl

theorem adaptiveClient_valid :
    (DynamicArray.spec 8).ValidHistory []
      ((DynamicArray.spec 8).runClient [] adaptiveClient).2.2 := by
  change (Fits 8 11 ∧ Fits 8 4) ∧ (Fits 8 22 ∧ Fits 8 12) ∧
    (0 < 2 ∧ Fits 8 0) ∧ (Fits 8 44 ∧ Fits 8 20) ∧ (2 < 3 ∧ Fits 8 2) ∧ True
  decide

/-- End-to-end adaptive execution from `initProgram` satisfies the linear instruction bound
`15 + 5 * 52 = 275` and space bound `frontier < 4 * 3 = 12`. -/
example : ∃ ready y traces, Exec 8 DynamicArray.initProgram blank ready 15 ∧
    Stateful.Executes ((DynamicArray.implementation 8).ExecOp 8) adaptiveClient ready
      (11, 44) y traces ∧
    DynamicArray.BoundedRep 8 [11, 22, 44] y ∧
    15 + Stateful.total DynamicProgram.OperationTrace.instructions traces +
      DynamicArray.potential [11, 22, 44] y ≤ 275 ∧
    y.regs DynamicArray.frontier < 12 := by
  obtain ⟨ready, y, traces, hi, he, hy, hb, hspace⟩ :=
    DynamicArray.run_initialized (by decide : Fits 8 1) adaptiveClient
      blank_bounded adaptiveClient_valid
  exact ⟨ready, y, traces, hi, he, hy, hb, hspace (by decide)⟩

/-- `run_appendAll` across five elements (`1 → 2 → 4 → 8` doublings) guarantees total charged
instructions `≤ 15 + 5 * 52 = 275` and `frontier < 20`. -/
example : ∃ ready y traces, Exec 8 DynamicArray.initProgram blank ready 15 ∧
    Stateful.Executes ((DynamicArray.implementation 8).ExecOp 8)
      (DynamicArray.appendAll [10, 20, 30, 40, 50]) ready () y traces ∧
    DynamicArray.BoundedRep 8 [10, 20, 30, 40, 50] y ∧
    15 + Stateful.total DynamicProgram.OperationTrace.instructions traces +
      DynamicArray.potential [10, 20, 30, 40, 50] y ≤ 275 ∧
    y.regs DynamicArray.frontier < 20 := by
  obtain ⟨ready, y, traces, hi, he, hy, hb, hspace⟩ :=
    DynamicArray.run_appendAll (w := 8) (vs := [10, 20, 30, 40, 50])
      (by decide : Fits 8 1) blank_bounded (by decide) (by decide)
  exact ⟨ready, y, traces, hi, he, hy, hb, hspace (by decide)⟩

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.Rep.space' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.Rep.space

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.get_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.get_exec

end DynamicArrayTest
