/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the memory queue migration)

public import CslibFrontier.DataStructure.Queue.Memory.Transfer

@[expose] public section

namespace CslibFrontierTests.QueueMemoryTransfer

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

def front : Stack.Memory.Layout := ⟨⟨0, 1⟩, ⟨1, 2⟩⟩
def rear : Stack.Memory.Layout := ⟨⟨3, 1⟩, ⟨4, 2⟩⟩

def memory : Memory.State :=
  ⟨fun a => if a = 3 then 2 else if a = 4 then 3 else if a = 7 then 5 else 0, 6⟩

def source : Memory.Prog ℕ :=
  boundedWhile (fun _ r => 0 < r) Queue.Memory.transferBody (front, rear) 2 2

example : (Memory.spec 3).clientResult memory source = 0 := rfl
example : ((Memory.spec 3).clientState memory source).mem 0 = 2 := rfl
example : ((Memory.spec 3).clientState memory source).mem 3 = 0 := rfl
example : ((Memory.spec 3).clientState memory source).mem 7 = 5 := rfl
example : Stack.Memory.abs front ((Memory.spec 3).clientState memory source) = [3, 0] := rfl

-- The ghost cutoff may exceed the count without changing the linked source or its history.
example :
    link (Methods.prod (Stack.Memory.methods front 3 2) (Stack.Memory.methods rear 3 2))
        (Queue.transfer 2) =
      (boundedWhile (fun _ r => 0 < r) Queue.Memory.transferBody (front, rear) 9 2).bind
        (fun _ => pure ()) :=
  Queue.Memory.transfer_eq_boundedWhile front rear 3 2 9 2 (by omega)

-- A positive remaining count on an empty rear performs just the terminating count read.
example :
    (Memory.spec 3).clientHistory (⟨fun _ => 0, 6⟩ : Memory.State)
      (boundedWhile (fun _ r => 0 < r) Queue.Memory.transferBody (front, rear) 4 4) =
        [.read 3] := rfl

-- The existing invariants are satisfiable at the concrete nonempty transfer above.
example :
    let p := link (Methods.prod (Stack.Memory.methods front 3 2)
      (Stack.Memory.methods rear 3 2)) (Queue.transfer 2)
    let s' := (Memory.spec 3).clientState memory p
    (Memory.spec 3).ValidHistory memory ((Memory.spec 3).clientHistory memory p) ∧
      Memory.WellFormed 3 s' ∧ Stack.Memory.Inv front s' ∧ Stack.Memory.Inv rear s' ∧
      s'.mem rear.count.base = 0 ∧ s'.mem front.count.base = memory.mem front.count.base + 2 ∧
      Stack.Memory.abs front s' = (Stack.Memory.abs rear memory).reverse ++
        Stack.Memory.abs front memory := by
  apply Queue.Memory.transfer_invariant (w := 3) (C := 2)
  · exact ⟨rfl, by change ¬(1 ≤ 0 ∧ 0 < 1 + 2); decide, rfl, by decide⟩
  · exact ⟨rfl, by change ¬(4 ≤ 3 ∧ 3 < 4 + 2); decide, rfl, by decide⟩
  · decide
  · refine ⟨by decide, fun a => ?_⟩
    dsimp only [memory]
    split <;> (try split) <;> (try split) <;> decide
  · exact ⟨by change 0 + 1 ≤ 6; decide, by change 1 + 2 ≤ 6; decide, by decide⟩
  · exact ⟨by change 3 + 1 ≤ 6; decide, by change 4 + 2 ≤ 6; decide, by decide⟩
  · rfl
  · decide

end CslibFrontierTests.QueueMemoryTransfer
