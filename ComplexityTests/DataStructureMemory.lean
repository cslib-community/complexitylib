/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Memory.Field

/-!
# Memory-oracle programs: named fields, pointer chasing and block reuse

A singly linked list is stored as a struct of arrays with a `key` field and a `next` field;
pointers are indices, with `0` as null. The tests allocate the layout, build a two-node list,
chase pointers to sum the keys, and reuse one scratch block across two rounds. They check the
answers, the operation histories and charges, admissibility at an 8-bit word size, and two
rejected operations: a read above the frontier and a write of an oversized value.
-/

@[expose] public section

namespace ComplexityTests.DataStructureMemory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory

/-- A linked-list node store as a struct of arrays. -/
structure Nodes where
  /-- The key of each node. -/
  key : Block
  /-- The successor of each node, as an index; `0` is null. -/
  next : Block

/-- Allocate both fields for `n` nodes. -/
def Nodes.alloc (n : ℕ) : Prog Nodes := do
  let key ← allocBlock n
  let next ← allocBlock n
  pure ⟨key, next⟩

/-- Follow at most `fuel` successors from node `v`, summing keys. Every address is computed from
an answer: the next node is read from memory. -/
def Nodes.sumFrom (L : Nodes) : ℕ → ℕ → Prog ℕ
  | 0, _ => pure 0
  | fuel + 1, v => do
    let k ← L.key.get v
    let nxt ← L.next.get v
    if nxt = 0 then pure k else do
      let rest ← L.sumFrom fuel nxt
      pure (k + rest)

/-- Build the list `1 → 2` with keys `5` and `7` (node `0` is reserved as null), then sum it. -/
def linkedSum : Prog ℕ := do
  let L ← Nodes.alloc 3
  L.key.set 1 5
  L.key.set 2 7
  L.next.set 1 2
  L.sumFrom 3 1

/-- The empty memory with nothing allocated. -/
def empty : State := ⟨fun _ => 0, 0⟩

example : (spec 8).clientResult empty linkedSum = 12 := by decide

/-- The history: two zeroed allocations, three writes and four reads by pointer chasing. -/
example : (spec 8).clientHistory empty linkedSum =
    [.alloc 3, .alloc 3, .write 1 5, .write 2 7, .write 4 2,
      .read 1, .read 4, .read 2, .read 5] := by decide

/-- The two zeroed allocations of three cells cost four each; seven unit operations follow. -/
example : (spec 8).totalCost charge empty ((spec 8).clientHistory empty linkedSum) = 15 := by
  decide

/-- Every operation is admissible at an 8-bit word size. -/
example : (spec 8).ValidHistory empty ((spec 8).clientHistory empty linkedSum) := by decide

/-- One scratch block, allocated without clearing, is reused across two rounds. -/
def reuse : Prog (ℕ × ℕ) := do
  let scratch ← allocBlockDirty 1
  scratch.set 0 3
  let first ← scratch.get 0
  scratch.set 0 (first + 4)
  let second ← scratch.get 0
  pure (first, second)

example : (spec 8).clientResult empty reuse = (3, 7) := by decide

example : ((spec 8).clientState empty reuse).frontier = 1 := by decide

example : (spec 8).totalCost charge empty ((spec 8).clientHistory empty reuse) = 5 := by decide

/-- A read above the frontier is rejected. -/
example : ¬(spec 8).ValidHistory empty [.read 0] := by decide

/-- A write of a value wider than the word is rejected, even at an allocated address. -/
example : ¬(spec 8).ValidHistory ⟨fun _ => 0, 1⟩ [.write 0 256] := by decide

/-- An allocation whose end does not fit the word is rejected. -/
example : ¬(spec 8).ValidHistory empty [.alloc 256] := by decide

/-- Well-formedness survives the pointer-chasing program. -/
example : WellFormed 8 ((spec 8).clientState empty linkedSum) := by
  have h : WellFormed 8 empty := ⟨by decide, fun _ => fits_zero 8⟩
  rw [← (spec 8).run_runClient]
  exact h.run (by decide)

/-- The input convention: the length at address `0`, the words from address `1`, and the
frontier just past them. -/
example : (spec 8).clientResult (State.init [4, 9]) (do
    let n ← read 0
    let x ← read 2
    pure (n, x)) = (2, 9) := by decide

/-- The list view reads the live prefix of a field. -/
example : (Block.mk 1 3).entries 2 (fun a => a * 10) = [10, 20] := by decide

end ComplexityTests.DataStructureMemory
