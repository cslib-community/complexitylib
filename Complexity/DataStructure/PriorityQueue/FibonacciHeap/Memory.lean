/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.ExtractMin

/-!
# The Fibonacci heap as an amortized refinement over memory

The five operations of `Basic.lean`, `DecreaseKey.lean` and `ExtractMin.lean` implement the
indexed min-priority queue `indexedMinPQSpec n K` over the heap's record (`refinement`), with
amortized charges `O(1)` for every operation but `extractMin`, which is charged
`O(log m)` on a queue of `m` handles (`amortized`). The potential is
`credit * (numRoots + 2 * numMarked)` record operations.

Placing the record in memory at a base address (`layout`) and composing with
`Record.refinement` gives the heap over `Memory.spec w` (`memRefinement`). The potentials stack
across the composition (`Refinement.Amortized.comp`): every memory operation is one record
operation, so the charges are the same in memory units (`mem_amortized`).

The heap reads and writes only its `9 n + 5` cells (`footprint`). It is the record's framed
structure (`Record.framed`) with the heap's programs on top (`Memory.Framed.comp`), so it joins
products with other structures in one memory (`Memory.Framed.prod`), and its potential, read
through the record, is local to its footprint (`potential_local`). `allocator` allocates the
record in zeroed cells, which hold the empty queue, as a `Memory.Allocator`; its cost
certificate is `amortized_allocator`.

## Main definitions

* `methods`: the record programs of the five operations.
* `charge`: the amortized charges `1`, `2`, `43`, `104` and `extractCharge`.
* `refinement`: the heap over its record.
* `layout`: the record at `9 n + 5` consecutive cells from a base address.
* `memRefinement`: the heap over memory.
* `footprint`, `framed`: the heap as a framed structure over memory.
* `allocator`: allocation of an empty heap, as a `Memory.Allocator`.

## Main results

* `wp_methods`: every operation meets its specification, invariant and amortized charge.
* `amortized`, `mem_amortized`, `framed_amortized`: the amortized costs over the record and over
  memory.
* `potential_local`: the potential reads only the footprint.
* `amortized_allocator`: the allocated heap's charges, with no potential once allocated.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

variable {n w K : ℕ}

/-- The heap's operations as record programs. -/
def methods (n : ℕ) (w K : ℕ) :
    Methods (indexedMinPQSpec n K) (Record.spec (Cell.ok n) w)
  | .isEmpty => isEmpty
  | .getKey v => getKey v
  | .insert v k => insert v k
  | .decreaseKey v k => decreaseKey n v k
  | .extractMin => extractMin n

/-- The amortized charge of each operation, in record operations. -/
def charge (n : ℕ) (s : IndexedMinPQ.State n) : IndexedMinPQ.Op n → ℕ
  | .isEmpty => 1
  | .getKey _ => 2
  | .insert _ _ => 19 + credit
  | .decreaseKey _ _ => 104
  | .extractMin => extractCharge (IndexedMinPQ.dom s).card

/-- **Every operation** meets `IndexedMinPQ.step`, preserves the invariant, and costs at most its
charge, amortized. -/
theorem wp_methods (hn : Fits w n) (hK : Fits w K) {g : Cell → ℕ} (hI : Inv n K g)
    (o : IndexedMinPQ.Op n) (hv : IndexedMinPQ.valid K (abs n g) o) :
    Record.wp (Cell.ok n) w (methods n w K o) (fun a g' t =>
      IndexedMinPQ.step (abs n g) o = (abs n g', a) ∧ Inv n K g' ∧
        t + potential n g' ≤ charge n (abs n g) o + potential n g) g := by
  cases o with
  | isEmpty =>
    refine Record.wp_mono (fun a g' t ⟨ha, hg, ht⟩ => ?_) (wp_isEmpty (w := w) hI)
    subst hg ht
    exact ⟨by simp [IndexedMinPQ.step, ha], hI, by simp [charge]⟩
  | getKey v =>
    refine Record.wp_mono (fun a g' t ⟨ha, hg, ht⟩ => ?_) (wp_getKey (w := w) (g := g) v)
    subst hg
    exact ⟨by simp [IndexedMinPQ.step, ha], hI, by simp [charge]; omega⟩
  | insert v k =>
    obtain ⟨hvn, hk⟩ := hv
    refine Record.wp_mono (fun a g' t ⟨ha, hI', ht⟩ => ⟨?_, hI', ht⟩) (wp_insert hI hvn hk hn hK)
    simp [IndexedMinPQ.step, ha]
  | decreaseKey v k =>
    obtain ⟨⟨k₀, hv₀, hk₀⟩, hk⟩ := hv
    refine Record.wp_mono (fun a g' t ⟨ha, hI', ht⟩ => ⟨?_, hI', ht⟩)
      (wp_decreaseKey hI hv₀ hk₀ hk hn hK)
    simp [IndexedMinPQ.step, ha]
  | extractMin => exact wp_extractMin hI hn

/-- **The Fibonacci heap over its record.** -/
def refinement (hn : Fits w n) (hK : Fits w K) :
    Refinement (indexedMinPQSpec n K) (Record.spec (Cell.ok n) w) :=
  Refinement.ofFn (methods n w K) (Inv n K) (abs n)
    (fun o hI hv => ((Record.wp_iff _ _ _).mp (wp_methods hn hK hI o hv)).1)
    (fun o hI hv => by
      obtain ⟨-, hstep, hI', -⟩ := (Record.wp_iff _ _ _).mp (wp_methods hn hK hI o hv)
      exact ⟨hstep, hI'⟩)

/-- **Amortized costs over the record**: one unit per record operation, with potential
`credit * (numRoots + 2 * numMarked)`. -/
theorem amortized (hn : Fits w n) (hK : Fits w K) :
    (refinement hn hK).Amortized (fun _ _ => 1) (charge n) (potential n) := by
  refine Refinement.Amortized.ofFn fun o hI hv => ?_
  obtain ⟨-, -, -, hcost⟩ := (Record.wp_iff _ _ _).mp (wp_methods hn hK hI o hv)
  rw [StateTransitionSpec.totalCost_one]
  exact hcost

/-! ## In memory -/

/-- The record at `9 n + 5` consecutive cells from `base`: the eight arrays, the table, and the
four scalars. -/
def layout (n base : ℕ) : Record.Layout (Cell.ok n) where
  addr
    | .key v => base + v
    | .par v => base + n + v
    | .child v => base + 2 * n + v
    | .left v => base + 3 * n + v
    | .right v => base + 4 * n + v
    | .deg v => base + 5 * n + v
    | .mark v => base + 6 * n + v
    | .inHeap v => base + 7 * n + v
    | .cons d => base + 8 * n + d
    | .minRoot => base + 9 * n + 1
    | .numRoots => base + 9 * n + 2
    | .numMarked => base + 9 * n + 3
    | .sz => base + 9 * n + 4
  addr_injOn i j hi hj h := by
    cases i <;> cases j <;> simp only [Cell.ok, Cell.key.injEq, Cell.par.injEq,
      Cell.child.injEq, Cell.left.injEq, Cell.right.injEq, Cell.deg.injEq, Cell.mark.injEq,
      Cell.inHeap.injEq, Cell.cons.injEq, reduceCtorEq] at h hi hj ⊢ <;> omega

/-- **The Fibonacci heap over memory**, at base address `base`. -/
def memRefinement (hn : Fits w n) (hK : Fits w K) (base : ℕ) :
    Refinement (indexedMinPQSpec n K) (Memory.spec w) :=
  (refinement hn hK).comp (Record.refinement (layout n base) w)

/-- **Amortized costs over memory.** The potentials stack across the composition: every memory
unit is one record operation. -/
theorem mem_amortized (hn : Fits w n) (hK : Fits w K) (base : ℕ) :
    (memRefinement hn hK base).Amortized Memory.charge (charge n)
      (fun m => potential n ((layout n base).abs m) + 0) :=
  (amortized hn hK).comp (Record.amortized (layout n base) w)

/-! ## A framed structure in memory -/

/-- The heap's cells: `9 n + 5` consecutive addresses from `base`. -/
def footprint (n base : ℕ) : Finset ℕ := Finset.Ico base (base + 9 * n + 5)

/-- Every cell of the heap lies in its footprint. -/
theorem addr_mem_footprint {base : ℕ} {i : Cell} (hi : Cell.ok n i) :
    (layout n base).addr i ∈ footprint n base := by
  cases i <;> simp only [layout, footprint, Finset.mem_Ico, Cell.ok] at hi ⊢ <;> omega

/-- The heap's record is allocated once its last cell, the count `sz`, is. -/
theorem lt_frontier_of_inv {base : ℕ} {s : Memory.State} (hs : (layout n base).Inv s) {a : ℕ}
    (ha : a ∈ footprint n base) : a < s.frontier := by
  have hsz := hs .sz trivial
  simp only [footprint, Finset.mem_Ico] at ha
  simp only [layout] at hsz
  omega

/-- The heap's record at `base` as a framed structure over memory. -/
def recordFramed (n w base : ℕ) : Memory.Framed (Record.spec (Cell.ok n) w) w :=
  Record.framed (layout n base) w (footprint n base) (fun _ hi => addr_mem_footprint hi)
    fun hs ha => lt_frontier_of_inv hs ha

/-- **The Fibonacci heap as a framed structure over memory**: the heap's programs over its record,
framed by the record's footprint, so it composes with other structures in one memory
(`Memory.Framed.prod`). -/
def framed (hn : Fits w n) (hK : Fits w K) (base : ℕ) :
    Memory.Framed (indexedMinPQSpec n K) w :=
  Memory.Framed.comp (refinement hn hK) (recordFramed n w base)

/-- The framed heap's potential reads only its footprint, as `Memory.Framed.amortized_prod`
needs. -/
theorem potential_local (hn : Fits w n) (hK : Fits w K) (base : ℕ) :
    (framed hn hK base).Local fun m => potential n ((layout n base).abs m) + 0 :=
  Memory.Framed.Local.add
    (Memory.Framed.Local.comp (Memory.Framed.Local.comp_abs (recordFramed n w base) (potential n)))
    (Memory.Framed.Local.const _ 0)

/-- The framed heap's amortized costs are those of `mem_amortized`. -/
theorem framed_amortized (hn : Fits w n) (hK : Fits w K) (base : ℕ) :
    (framed hn hK base).Amortized Memory.charge (charge n)
      (fun m => potential n ((layout n base).abs m) + 0) :=
  Memory.Framed.amortized_comp (amortized hn hK) (Record.amortized (layout n base) w)

/-! ## Allocation -/

/-- The all-zero record is the empty heap. -/
theorem fibRawInv_zero : FibRawInv n K (IndexedMinPQ.empty n) (view n fun _ => 0) :=
  FibRawInv.empty (fun _ => rfl) (fun _ _ => rfl) rfl rfl rfl rfl

/-- Allocating the heap's record: `9 n + 5` zeroed cells at the frontier, the count `sz` last. -/
def recordAllocator (n w : ℕ) : Memory.Allocator (Record.spec (Cell.ok n) w) w :=
  Record.allocator (layout n) (9 * n + 5) w
    (fun _ i hi => by cases i <;> simp only [layout, Cell.ok] at hi ⊢ <;> omega)
    fun _ => ⟨.sz, trivial, by simp only [layout]; omega⟩

/-- **Allocating an empty heap**: its record in `9 n + 5` zeroed cells at the frontier, with the
heap's programs on top. -/
def allocator (hn : Fits w n) (hK : Fits w K) : Memory.Allocator (indexedMinPQSpec n K) w :=
  (recordAllocator n w).comp (refinement hn hK) (inv_of_fibRawInv fibRawInv_zero).1

/-- The allocated heap is empty. -/
theorem init_allocator (hn : Fits w n) (hK : Fits w K) :
    (allocator hn hK).init = IndexedMinPQ.empty n :=
  (inv_of_fibRawInv (K := K) fibRawInv_zero).2

/-- **The allocated heap's costs**: the charges of `charge` in memory units, with no potential
once allocated. -/
theorem amortized_allocator (hn : Fits w n) (hK : Fits w K) :
    (allocator hn hK).Amortized (charge n) 0 := by
  have h := Memory.Allocator.Amortized.comp (A := recordAllocator n w)
    (hinit := (inv_of_fibRawInv (K := K) fibRawInv_zero).1) (amortized hn hK)
    Record.amortized_allocator
  have h0 : potential n (recordAllocator n w).init + 0 = 0 := by
    simp [potential, view, recordAllocator, Record.allocator]
  rwa [h0] at h

end Cslib.DataStructure.PriorityQueue.FibonacciHeap
