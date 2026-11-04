/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Absorb
public import Complexity.Computability.WordRAM.Realization.Witness
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Allocation
import Complexity.Tactic.Realize

/-!
# Native reservation of an empty indexed Fibonacci heap

One uniform exact-basis emitter reserves the original `9 n + 5` cells, returns their base and
preserves every memory cell. Address arithmetic and result copies are charged through the
existing `realize` rules. Repeated addition avoids materializing the literal nine: zero capacity
can be admitted with three-bit words even though nine does not fit.

Reservation alone does not initialize arbitrary dirty storage. The existing framed empty heap
follows under the explicit zero-above-input condition, through `zeroAllocator`; the method
implementations and representation are unchanged. These results certify initialization, not
the heap's other methods or either whole consumer migration.

## Main results

* `realizes_reserve`: uniform native realization of the original dirty reservation.
* `reserve_exec`: the same emitter's constant instruction bound, full memory and register frame.
* `reserve_empty`: its endpoint establishes the existing empty-heap frame in zero fresh memory.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native.Initialize

open Cslib.WordRAM Cslib.WordRAM.Realization

/-- Reserve the original layout without a fitting-literal-nine hypothesis. All intermediate
additions fit because the final frontier does; the one memory charge includes no clearing. -/
theorem realizes_reserve : Realizes .exact (fun n : ℕ => Memory.allocDirty (9 * n + 5))
    (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
    (fun w n s => Fits w (s.frontier + (9 * n + 5))) (fun _ _ => 0) := by
  have h : Realizes .exact
      (fun n : ℕ => Memory.allocDirty (n + n + n + n + n + n + n + n + n + 5))
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w n s => Fits w (s.frontier + (9 * n + 5))) (fun _ _ => 0) := by
    realize
    all_goals exact h.of_le (by omega)
  exact h.congr (fun n => congrArg Memory.allocDirty (by omega))

/-- One selected emitter returns the old frontier and reserves exactly the original span.
The fixed exchange factor precedes capacity, width, memory and register layout; all memory and
all registers outside the frontier and scratch bank are preserved. -/
theorem reserve_exec {r : ℕ} (frontier : Fin r) (src : Fin 1 → Fin r)
    (tmp : Fin (1 + realizes_reserve.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    {w n : ℕ} (x : Data r) (hx : x.Bounded w)
    (hin : x.regs ∘ src = WordEncoding.encode (α := ℕ) n)
    (hfit : Fits w (x.regs frontier + (9 * n + 5))) :
    ∃ y, ExecWithin w (realizes_reserve.code frontier src tmp) x y
        (2 * realizes_reserve.factor) ∧ y.Bounded w ∧
      y.mem = x.mem ∧ y.regs frontier = x.regs frontier + (9 * n + 5) ∧
      y.regs (tmp (Fin.castAdd (realizes_reserve.scratchSize + 1) 0)) = x.regs frontier ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  have hv : (Memory.spec w).ValidHistory (memoryState frontier x)
      ((Memory.spec w).clientHistory (memoryState frontier x) (Memory.allocDirty (9 * n + 5))) :=
    ⟨hfit, trivial⟩
  obtain ⟨y, hy, hm, ho, hframe⟩ :=
    (realizes_reserve.code_spec frontier src tmp hi hd hf hs).2 w n x hx hin hfit hv
  have hc : memoryCost (Memory.allocDirty (9 * n + 5)) (memoryState frontier x) = 1 := rfl
  refine ⟨y, ?_, hy.bounded hx, congrArg Memory.State.mem hm,
    congrArg Memory.State.frontier hm, ho 0, hframe⟩
  rw [hc] at hy
  simpa only [Nat.add_zero, Nat.mul_comm] using hy

/-- At the reservation endpoint, the existing zero-above precondition establishes the exact
empty indexed-queue abstraction. No fresh cells have been cleared or changed. -/
theorem reserve_empty {r n w K : ℕ} (frontier : Fin r) {x y : Data r}
    (hn : Fits w n) (hK : Fits w K)
    (hm : y.mem = x.mem) (hfr : y.regs frontier = x.regs frontier + (9 * n + 5))
    (hz : Memory.ZeroAbove (memoryState frontier x)) :
    (framed hn hK (x.regs frontier)).inv (memoryState frontier y) ∧
      (framed hn hK (x.regs frontier)).abs (memoryState frontier y) =
        IndexedMinPQ.empty n := by
  have he : memoryState frontier y =
      ⟨x.mem, x.regs frontier + (9 * n + 5)⟩ := Memory.State.ext hm hfr
  rw [he]
  exact framed_allocDirty hn hK hz

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native.Initialize
