/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalFold
import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalLocalDelivery
import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Program
import Complexity.Algorithms.WordRAM.ThreeSum.Host.Slow

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

private def localInput : Data 128 where
  regs i := if i = heap then 100 else if i = slot 2 then 2
    else if i = slot 4 then 3 else if i = slot 6 then 1
    else if i = groups then 8 else if i = selected then 4
    else if i = one then 1 else 255
  mem a := if a = 100 then 1 else if a = 103 then 2 else if a = 107 then 0 else 79

-- The unused table address and count would overflow if the old publication ran.
-- Local delivery reads actual dirty-memory counts and keeps both unrelated words intact.
/-- info: true -/
#guard_msgs in
#eval decide ((Code.eval 8 1 deliverLocal localInput).map (fun (y, steps) =>
  [steps, y.regs packed, y.regs heap] ++ List.ofFn (fun j => y.regs (heavyLength j)) ++
    List.ofFn (fun j => y.regs (heavyBase j)) ++
    [y.regs outputs, y.regs outputCount, y.mem 100, y.mem 255]) =
    some [21, 109, 151, 1, 2, 0, 101, 104, 108, 255, 255, 1, 79])

-- The same actual block fits eight bits but its endpoint arithmetic faults at seven bits.
/-- info: true -/
#guard_msgs in
#eval (Code.eval 7 1 deliverLocal localInput).isNone

-- The execution theorem is inhabited and preserves the complete memory function.
example : Exec 8 deliverLocal localInput (localDeliveryState localInput) 21 ∧
    (localDeliveryState localInput).mem = localInput.mem :=
  ⟨deliverLocal_exec localInput (by decide) (by decide), localDeliveryState_mem localInput⟩

-- A noncommutative collector retains the mathematical order, rather than only its set of nodes.
example (Q : Finset ℕ) (Λ : ℕ) (t : Math.Task) (ts : List Math.Task)
    (seen : List Cslib.Algorithms.ThreeSum.ChanHe.Node) :
    (Math.output Q Λ (t :: ts)).foldl (fun xs node => xs ++ [node]) seen =
      (Math.output Q Λ (Math.step Q Λ t ts).1).foldl (fun xs node => xs ++ [node])
        ((Math.step Q Λ t ts).2.toList.foldl (fun xs node => xs ++ [node]) seen) :=
  Math.foldl_step _ _ _ _ _ _

private def rootInput (f n : ℕ) (z : ℤ) : Data 128 where
  regs i := match i.val with
    | 64 => f
    | 65 => 1
    | 66 => n
    | 67 => 2
    | 68 => n
    | 69 => 3
    | 70 => n
    | 71 => 2
    | 72 => 1
    | 73 => 1
    | 74 => 8
    | 75 => 10
    | 76 => 1
    | 77 => 100
    | 78 => 60
    | 79 => 0
    | 80 => 20
    | 81 => 21
    | 116 => 32
    | _ => 79
  mem a := if a = 1 ∨ a = 2 ∨ a = 3 then Signed.encode z
    else if a = 10 ∨ a = 11 then 0 else if a = 12 then 1 else 79

open Cslib.Algorithms.WordRAM.ThreeSum

private def visitorInput (f n : ℕ) (z : ℤ) : Data (Decision.registerCount 17) where
  regs i := if hi : i.val < 128 then (rootInput f n z).regs ⟨i.val, hi⟩
    else if i = Decision.controllerRegisters 17 Decision.envelope then 100
    else if i = Decision.controllerRegisters 17 Decision.one then 1
    else if i = Decision.controllerRegisters 17 Decision.answer then 0 else 79
  mem := (rootInput f n z).mem

private def observeVisitor (f n : ℕ) (z : ℤ) :=
  (Code.eval 16 4096 (Decision.Visitor.oneRoot Host.Slow.callee.code)
    (visitorInput f n z)).map fun (y, _) =>
      [y.regs (Decision.controllerRegisters 17 Decision.answer),
        y.regs (Decision.preprocessingRegisters 17 heap), y.mem 60,
        y.mem 1, y.mem 2, y.mem 3,
        y.regs (Decision.preprocessingRegisters 17 (registers WordStack.len))]

-- Live native modulus/node kernels immediately call the actual certified exhaustive solver.
-- The old pointer-table cell is untouched, and all three aliased root inputs survive.
/-- info: true -/
#guard_msgs in
#eval decide (observeVisitor 1 1 0 = some [1, 145, 79, 0, 0, 0, 0])

/-- info: true -/
#guard_msgs in
#eval decide (observeVisitor 1 1 (-1) =
  some [0, 145, 79, Signed.encode (-1), Signed.encode (-1), Signed.encode (-1), 0])

-- Zero fuel and an empty column still execute their native pop/guard path, without a node call.
/-- info: true -/
#guard_msgs in
#eval decide (observeVisitor 0 1 0 = some [0, 100, 79, 0, 0, 0, 0])

/-- info: true -/
#guard_msgs in
#eval decide (observeVisitor 1 0 0 = some [0, 100, 79, 0, 0, 0, 0])

private def branchingVisitorInput : Data (Decision.registerCount 17) where
  regs i := if i = Decision.preprocessingRegisters 17 (slot 2) then 3
    else if i = Decision.preprocessingRegisters 17 (slot 3) then 4
    else if i = Decision.preprocessingRegisters 17 (slot 5) then 5
    else if i = Decision.preprocessingRegisters 17 digits then 4
    else if i = Decision.preprocessingRegisters 17 magnitude then 4
    else if i = Decision.preprocessingRegisters 17 stackCapacity then 35
    else if i = Decision.controllerRegisters 17 Decision.envelope then 1000
    else (visitorInput 2 1 0).regs i
  mem a := match a with
    | 1 => Signed.encode 0
    | 2 => Signed.encode 4
    | 3 => Signed.encode 1
    | 4 => Signed.encode 0
    | 5 => Signed.encode (-1)
    | _ => (visitorInput 2 1 0).mem a

-- A true parent followed by a false heavy child keeps the true accumulator. The second node
-- allocates into the previous host's dirty workspace, while pending siblings alias old columns.
/-- info: true -/
#guard_msgs in
#eval decide ((Code.eval 16 4096 (Decision.Visitor.oneRoot Host.Slow.callee.code)
  branchingVisitorInput).map (fun (y, _) =>
    (y.regs (Decision.controllerRegisters 17 Decision.answer),
      y.regs (Decision.preprocessingRegisters 17 heap), y.mem 60, y.mem 61,
      [y.mem 1, y.mem 2, y.mem 3, y.mem 4, y.mem 5],
      y.regs (Decision.preprocessingRegisters 17 (registers WordStack.len)))) =
    some (1, 196, 79, 79, [Signed.encode 0, Signed.encode 4, Signed.encode 1,
      Signed.encode 0, Signed.encode (-1)], 0))

-- The complete initialized program retains the distinct-position short-input path.
/-- info: true -/
#guard_msgs in
#eval decide (run 4 (Decision.flatProgram 1 Host.Slow.callee.code) 10
  (State.init ([] : List ℕ)) = some (0, 7))

/-- info: true -/
#guard_msgs in
#eval decide (run 4 (Decision.flatProgram 1 Host.Slow.callee.code) 10
  (State.init [Signed.encode 0]) = some (0, 7))

/-- info: true -/
#guard_msgs in
#eval decide (run 4 (Decision.flatProgram 1 Host.Slow.callee.code) 10
  (State.init [Signed.encode 0, Signed.encode 0]) = some (0, 7))
