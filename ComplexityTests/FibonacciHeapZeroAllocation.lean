/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Initialize

/-!
# Zero-above-input allocation and actual Fibonacci-heap clients

The zero-capacity case fits three-bit words with the final frontier at the maximum word. The
positive-capacity client inserts and extracts a maximum five-bit key, and the original input
cell remains unchanged. These check memory-oracle admissibility, answers and query counts;
the final test also executes the selected native reservation emitter on the zero-capacity
three-bit boundary, retaining the dirty input cell and establishing the empty-heap frame.
-/

public section

namespace ComplexityTests.FibonacciHeapZeroAllocation

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open FibonacciHeap

private def tiny : Memory.State := Memory.State.init [7]
private def input : Memory.State := Memory.State.init [31]

private def emptyAllocator : Memory.Allocator (indexedMinPQSpec 0 7) 3 :=
  zeroAllocator (by decide) (by decide)

private def heapAllocator : Memory.Allocator (indexedMinPQSpec 2 31) 5 :=
  zeroAllocator (by decide) (by decide)

private def emptyClient : (indexedMinPQSpec 0 7).Client (Bool × Option (Fin 0 × ℕ)) := do
  let e ← (indexedMinPQSpec 0 7).call .isEmpty
  let x ← (indexedMinPQSpec 0 7).call .extractMin
  pure (e, x)

/-- Insert a fitting maximum key and observe it through both optional-answer methods. -/
@[expose] def fullKeyClient :
    (indexedMinPQSpec 2 31).Client (Option ℕ × Bool × Option (Fin 2 × ℕ)) := do
  (indexedMinPQSpec 2 31).call (.insert 0 31)
  let k ← (indexedMinPQSpec 2 31).call (.getKey 0)
  let e ← (indexedMinPQSpec 2 31).call .isEmpty
  let x ← (indexedMinPQSpec 2 31).call .extractMin
  pure (k, e, x)

/-- The allocator's explicit zero-above precondition holds under the actual input convention. -/
example : Memory.ZeroAbove tiny ∧ Memory.ZeroAbove input :=
  ⟨Memory.zeroAbove_init _, Memory.zeroAbove_init _⟩

/-- Empty capacity needs five cells, not a fitting literal nine. -/
example : Cslib.WordRAM.Fits 3 (tiny.frontier + 9 * 0 + 5) ∧
    ¬Cslib.WordRAM.Fits 3 9 := by decide

/-- The empty frame is a genuine instance of the existing allocator certificate. -/
example :
    (emptyAllocator.framed tiny (Memory.zeroAbove_init _) (by decide)).inv
      ((Memory.spec 3).clientState tiny emptyAllocator.alloc) :=
  (emptyAllocator.allocates tiny (Memory.zeroAbove_init _) (by decide)).inv

/-- Allocation and both empty operations are admissible; the full frontier is still a word. -/
example :
    (Memory.spec 3).ValidHistory tiny
      ((Memory.spec 3).clientHistory tiny (emptyAllocator.run emptyClient)) ∧
    (Memory.spec 3).clientResult tiny (emptyAllocator.run emptyClient) = (true, none) ∧
    ((Memory.spec 3).clientState tiny (emptyAllocator.run emptyClient)).frontier = 7 ∧
    ((Memory.spec 3).clientState tiny (emptyAllocator.run emptyClient)).mem 1 = 7 ∧
    ((Memory.spec 3).clientHistory tiny (emptyAllocator.run emptyClient)).length = 3 := by decide

/-- Positive capacity, maximum key and the input's dirty lower cell are all retained. The one
allocation query replaces a linear clearing prefix; every method query is still counted. -/
example :
    (Memory.spec 5).ValidHistory input
      ((Memory.spec 5).clientHistory input (heapAllocator.run fullKeyClient)) ∧
    (Memory.spec 5).clientResult input (heapAllocator.run fullKeyClient) =
      (some 31, false, some (0, 31)) ∧
    ((Memory.spec 5).clientState input (heapAllocator.run fullKeyClient)).frontier = 25 ∧
    ((Memory.spec 5).clientState input (heapAllocator.run fullKeyClient)).mem 1 = 31 ∧
    ((Memory.spec 5).clientHistory input (heapAllocator.run fullKeyClient)).length = 30 := by decide

section Native

open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap.Native.Initialize

noncomputable section

private abbrev slots := 1 + realizes_reserve.scratchSize + 1
private abbrev regs := 2 + slots

private def frontier : Fin regs := ⟨0, by unfold regs; omega⟩
private def source (_ : Fin 1) : Fin regs := ⟨1, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨2 + i, by unfold regs; omega⟩

private def nativeInput : Data regs where
  regs i := if i = frontier then 2 else 0
  mem := tiny.mem

/-- The actual uniform emitter admits `n = 0`, three-bit words and a final frontier of seven.
The literal nine does not fit, and the dirty input cell remains unchanged. -/
example : ∃ y, ExecWithin 3 (realizes_reserve.code frontier source scratch) nativeInput y
      (2 * realizes_reserve.factor) ∧ y.mem 1 = 7 ∧ y.regs frontier = 7 ∧
    y.regs (scratch (Fin.castAdd (realizes_reserve.scratchSize + 1) 0)) = 2 ∧
    (framed (n := 0) (K := 7) (w := 3) (by decide) (by decide) 2).inv
      (memoryState frontier y) := by
  have hi : Function.Injective scratch := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simpa only [scratch, Nat.add_left_cancel_iff] using this
  have hd : ∀ i j, source i ≠ scratch j := by
    intro i j h
    have := congrArg Fin.val h
    simp only [source, scratch] at this
    omega
  have hf : ∀ j, scratch j ≠ frontier := by
    intro j h
    have := congrArg Fin.val h
    simp only [scratch, frontier] at this
    omega
  have hs : ∀ i, source i ≠ frontier := by
    intro i h
    have := congrArg Fin.val h
    simp only [source, frontier] at this
    omega
  have hb : nativeInput.Bounded 3 := by
    refine ⟨fun i => ?_, ?_⟩
    · dsimp only [nativeInput]
      split_ifs <;> decide
    · exact (Memory.wellFormed_init (w := 3) (input := [7]) (by decide) (by decide)).2
  have hin : nativeInput.regs ∘ source = WordEncoding.encode (α := ℕ) 0 := by
    funext i
    fin_cases i
    rfl
  obtain ⟨y, hy, _, hm, hfr, hout, _⟩ :=
    reserve_exec (n := 0) frontier source scratch hi hd hf hs nativeInput hb hin (by decide)
  have he := reserve_empty (n := 0) (K := 7) (w := 3) frontier (by decide) (by decide)
    hm hfr (show Memory.ZeroAbove (memoryState frontier nativeInput) from Memory.zeroAbove_init _)
  refine ⟨y, hy, ?_, hfr, hout, he.1⟩
  rw [hm]
  rfl

end

end Native

end ComplexityTests.FibonacciHeapZeroAllocation
