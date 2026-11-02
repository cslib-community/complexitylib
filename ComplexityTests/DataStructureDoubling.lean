/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Queue.Memory
public import Complexity.DataStructure.Stack.Doubling

/-!
# Growing structures sharing one memory

Doubling stacks allocate inside their operations. The tests run them on concrete memory at word
size `8`:

* one doubling stack, which grows from capacity `1` to `8`;
* two doubling stacks in one memory, pushed alternately, so that each grows into memory beyond
  the other's latest array: the shared room budget of `Memory.Framed.prod` at work;
* the two-stack queue of `Queue.Memory`, unchanged, over two doubling stacks instead of two fixed
  arrays.

Each test checks the answers and the exact memory cost by evaluation, and applies the generic
theorems of `Memory.Allocator`, which need no setup proof.
-/

@[expose] public section

namespace ComplexityTests.DataStructureDoubling

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Queue

/-- Memory with nothing allocated. -/
def nothing : State := ⟨fun _ => 0, 0⟩

/-! ## One doubling stack -/

/-- A bounded stack of capacity `8` at word size `8`. -/
abbrev S : StateTransitionSpec := Stack.WordRAM.spec 8 8

/-- Push `1, …, 8`, pop three times, and read the size. -/
def client : S.Client (List (Option ℕ) × ℕ) := do
  for i in [1, 2, 3, 4, 5, 6, 7, 8] do
    let _ ← S.call (.push i)
  let a ← S.call .pop
  let b ← S.call .pop
  let c ← S.call .pop
  let n ← S.call .size
  pure ([a, b, c], n)

/-- The run answers last in, first out. -/
example : (spec 8).clientResult nothing ((Stack.Doubling.allocator 8 8).run client) =
    ([some 8, some 7, some 6], 5) := by
  decide

/-- Its exact cost: seven to allocate; pushes into arrays with room cost five, and the pushes into
full arrays of `1`, `2` and `4` items cost `11`, `13` and `17`; three pops cost four, and the
size one. -/
example : (spec 8).totalCost charge nothing ((spec 8).clientHistory nothing
    ((Stack.Doubling.allocator 8 8).run client)) = 7 + (5 * 5 + 11 + 13 + 17) + 3 * 4 + 1 := by
  decide

/-- The client is admissible for the bounded stack. -/
theorem client_valid : S.ValidHistory [] (S.clientHistory [] client) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, trivial, trivial, trivial, trivial, trivial⟩

/-- The generic theorems: the specification's answer, and at most `7 + 13 m` memory units. -/
example : (spec 8).clientResult nothing ((Stack.Doubling.allocator 8 8).run client) =
    S.clientResult [] client :=
  have ⟨_, hres, _⟩ :=
    (Stack.Doubling.allocator 8 8).run_correct client trivial (by decide) client_valid
  hres

example : (spec 8).totalCost charge nothing ((spec 8).clientHistory nothing
    ((Stack.Doubling.allocator 8 8).run client)) ≤ 7 + 0 + 13 * 12 :=
  Allocator.run_cost_le Stack.Doubling.amortized_allocator client trivial (by decide) client_valid

/-! ## Two doubling stacks in one memory -/

/-- Two bounded stacks of capacity `4`. -/
abbrev T : StateTransitionSpec := product (Stack.WordRAM.spec 8 4) (Stack.WordRAM.spec 8 4)

/-- Two doubling stacks, allocated one after the other. -/
abbrev twoStacks : Allocator T 8 :=
  (Stack.Doubling.allocator 8 4).prod (Stack.Doubling.allocator 8 4)

/-- Push `1, …, 4` on the left and `11, …, 14` on the right, alternately, then pop both. Each
stack grows twice, each time past the other's newest array. -/
def client₂ : T.Client (List (Option ℕ)) := do
  for i in [1, 2, 3, 4] do
    let _ ← T.call (.inl (.push i))
    let _ ← T.call (.inr (.push (i + 10)))
  let a ← T.call (.inl .pop)
  let b ← T.call (.inr .pop)
  let c ← T.call (.inl .pop)
  let d ← T.call (.inr .pop)
  pure [a, b, c, d]

/-- The two stacks keep their own items. -/
example : (spec 8).clientResult nothing (twoStacks.run client₂) =
    [some 4, some 14, some 3, some 13] := by
  decide

/-- The left stack's arrays sit at `3`, `8` and `12`, the right one's at `7`, `10` and `16`, and
the memory ends at `20`. -/
example : ((spec 8).clientState nothing (twoStacks.run client₂)).frontier = 20 ∧
    ((spec 8).clientState nothing (twoStacks.run client₂)).mem 2 = 12 ∧
    ((spec 8).clientState nothing (twoStacks.run client₂)).mem 6 = 16 := by
  decide

/-- The client is admissible for the two bounded stacks. -/
theorem client₂_valid :
    T.ValidHistory twoStacks.init (T.clientHistory twoStacks.init client₂) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, trivial, trivial, trivial, trivial, trivial⟩

/-- The certificates add across the product. -/
theorem amortized_twoStacks : twoStacks.Amortized (fun _ _ => 13) 0 := by
  have h := Allocator.Amortized.prod (Stack.Doubling.amortized_allocator (w := 8) (C := 4))
    (Stack.Doubling.amortized_allocator (w := 8) (C := 4))
  rwa [productCharge_const] at h

/-- The generic theorems apply to the two growing stacks in one memory. -/
example : (spec 8).clientResult nothing (twoStacks.run client₂) =
    T.clientResult twoStacks.init client₂ :=
  have ⟨_, hres, _⟩ :=
    twoStacks.run_correct client₂ ⟨trivial, trivial, Finset.disjoint_empty_left _⟩ (by decide)
      client₂_valid
  hres

example : (spec 8).totalCost charge nothing ((spec 8).clientHistory nothing
    (twoStacks.run client₂)) ≤ 14 + 0 + 13 * 12 :=
  Allocator.run_cost_le amortized_twoStacks client₂
    ⟨trivial, trivial, Finset.disjoint_empty_left _⟩ (by decide) client₂_valid

/-! ## The queue over two doubling stacks -/

/-- The two-stack queue of `Queue.Memory`, over two doubling stacks of capacity `3`. -/
abbrev growingQueue : Allocator (Queue.WordRAM.spec 8 3) 8 :=
  ((Stack.Doubling.allocator 8 3).prod (Stack.Doubling.allocator 8 3)).comp
    (Queue.Memory.refinement 8 3)
    (show Queue.Memory.Inv 8 3 [] from ⟨Nat.zero_le 3, fun _ h => absurd h List.not_mem_nil⟩)

/-- Enqueue `1, 2`, dequeue, enqueue `3`, then dequeue three times. -/
def queueClient : (Queue.WordRAM.spec 8 3).Client (List (Option ℕ)) := do
  (Queue.WordRAM.spec 8 3).call (.enqueue 1)
  (Queue.WordRAM.spec 8 3).call (.enqueue 2)
  let a ← (Queue.WordRAM.spec 8 3).call .dequeue
  (Queue.WordRAM.spec 8 3).call (.enqueue 3)
  let b ← (Queue.WordRAM.spec 8 3).call .dequeue
  let c ← (Queue.WordRAM.spec 8 3).call .dequeue
  let d ← (Queue.WordRAM.spec 8 3).call .dequeue
  pure [a, b, c, d]

/-- The queue answers first in, first out, as over fixed arrays. -/
example : (spec 8).clientResult nothing (growingQueue.run queueClient) =
    [some 1, some 2, some 3, none] := by
  decide

/-- The queue's certificate, three stack calls per operation, stacks over the doubling stacks'
thirteen units per call. -/
theorem amortized_growingQueue : growingQueue.Amortized (fun _ _ => 39) 0 := by
  have h := Allocator.Amortized.prod (Stack.Doubling.amortized_allocator (w := 8) (C := 3))
    (Stack.Doubling.amortized_allocator (w := 8) (C := 3))
  rw [productCharge_const] at h
  exact Allocator.Amortized.comp (Queue.Memory.amortized.mul_left 13) h

/-- The queue client is admissible. -/
theorem queueClient_valid : (Queue.WordRAM.spec 8 3).ValidHistory growingQueue.init
    ((Queue.WordRAM.spec 8 3).clientHistory growingQueue.init queueClient) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, trivial, ⟨by decide, by decide⟩, trivial,
    trivial, trivial, trivial⟩

/-- The generic cost theorem: at most `14 + 39 m` memory units. -/
example : (spec 8).totalCost charge nothing ((spec 8).clientHistory nothing
    (growingQueue.run queueClient)) ≤ 14 + 0 + 39 * 7 :=
  Allocator.run_cost_le amortized_growingQueue queueClient
    ⟨trivial, trivial, Finset.disjoint_empty_left _⟩ (by decide) queueClient_valid

end ComplexityTests.DataStructureDoubling
