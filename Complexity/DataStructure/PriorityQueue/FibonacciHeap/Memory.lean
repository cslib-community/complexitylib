/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Frame
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

The heap reads and writes only its `9 n + 5` cells (`footprint`), so it is a
`Memory.Framed` structure (`framed`) whose potential is local to its footprint
(`potential_local`), ready for `Memory.Framed.prod` and `amortized_prod` with other structures in
one memory. All arrays are allocated at once, zeroed, and hold the empty queue
(`framed_alloc`).

## Main definitions

* `methods`: the record programs of the five operations.
* `charge`: the amortized charges `1`, `2`, `43`, `104` and `extractCharge`.
* `refinement`: the heap over its record.
* `layout`: the record at `9 n + 5` consecutive cells from a base address.
* `memRefinement`: the heap over memory.
* `footprint`, `framed`: the heap as a framed structure over memory.

## Main results

* `wp_methods`: every operation meets its specification, invariant and amortized charge.
* `amortized`, `mem_amortized`, `framed_amortized`: the amortized costs over the record and over
  memory.
* `potential_local`: the potential reads only the footprint.
* `framed_alloc`: zeroed cells hold the empty heap.
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

/-- The record stored in memory depends only on the footprint. -/
theorem layout_abs_congr {base : ℕ} {s s' : Memory.State}
    (h : ∀ a ∈ footprint n base, s'.mem a = s.mem a) :
    (layout n base).abs s' = (layout n base).abs s := by
  funext i
  by_cases hi : Cell.ok n i
  · simp [Record.Layout.abs, hi, h _ (addr_mem_footprint hi)]
  · simp [Record.Layout.abs, hi]

/-- **The Fibonacci heap as a framed structure over memory**: it reads and writes only its
footprint, so it composes with other structures in one memory (`Memory.Framed.prod`). -/
def framed (hn : Fits w n) (hK : Fits w K) (base : ℕ) :
    Memory.Framed (indexedMinPQSpec n K) w :=
  Memory.Framed.ofStatic (memRefinement hn hK base) (footprint n base)
    (fun {s a} hs ha => by
      have hsz := hs.1 .sz trivial
      simp only [footprint, Finset.mem_Ico] at ha
      simp only [layout] at hsz
      omega)
    (fun {s s'} hs h hf => by
      have habs := layout_abs_congr h
      refine ⟨⟨fun i hi => (hs.1 i hi).trans_le hf, ?_⟩, ?_⟩
      · change Inv n K ((layout n base).abs s')
        rw [habs]; exact hs.2
      · change abs n ((layout n base).abs s') = abs n ((layout n base).abs s)
        rw [habs])
    (fun {s} o hs hv b _ hb => (layout n base).mem_clientState_link _ hs.1
      (wp_methods hn hK hs.2 o hv) b fun i hi e => hb (e ▸ addr_mem_footprint hi))

/-- The framed heap's potential reads only its footprint, as `Memory.Framed.amortized_prod`
needs. -/
theorem potential_local (hn : Fits w n) (hK : Fits w K) (base : ℕ) :
    (framed hn hK base).Local fun m => potential n ((layout n base).abs m) + 0 :=
  fun _ h _ => by dsimp only; rw [layout_abs_congr h]

/-- The framed heap's amortized costs are those of `mem_amortized`. -/
theorem framed_amortized (hn : Fits w n) (hK : Fits w K) (base : ℕ) :
    (framed hn hK base).Amortized Memory.charge (charge n)
      (fun m => potential n ((layout n base).abs m) + 0) :=
  mem_amortized hn hK base

/-- **Allocation of an empty heap**: `9 n + 5` zeroed cells at the frontier, all arrays at once.
The heap at the old frontier holds the empty queue. -/
theorem framed_alloc (hn : Fits w n) (hK : Fits w K) (s : Memory.State) :
    (framed hn hK s.frontier).inv
        ⟨clear s.mem s.frontier (9 * n + 5), s.frontier + (9 * n + 5)⟩ ∧
      (framed hn hK s.frontier).abs
        ⟨clear s.mem s.frontier (9 * n + 5), s.frontier + (9 * n + 5)⟩ = IndexedMinPQ.empty n := by
  set s' : Memory.State := ⟨clear s.mem s.frontier (9 * n + 5), s.frontier + (9 * n + 5)⟩
  have hzero : (layout n s.frontier).abs s' = fun _ => 0 := by
    funext i
    by_cases hi : Cell.ok n i
    · have hmem := addr_mem_footprint (base := s.frontier) hi
      simp only [footprint, Finset.mem_Ico] at hmem
      simp only [Record.Layout.abs, hi, ite_true, s']
      exact clear_of_owns (show Block.Owns ⟨s.frontier, 9 * n + 5⟩ _ from
        ⟨hmem.1, by dsimp only; omega⟩)
    · simp [Record.Layout.abs, hi]
  have hemp : FibRawInv n K (IndexedMinPQ.empty n) (view n fun _ => 0) :=
    FibRawInv.empty (fun _ => rfl) (fun _ _ => rfl) rfl rfl rfl rfl
  obtain ⟨hI, habs⟩ := inv_of_fibRawInv hemp
  refine ⟨⟨fun i hi => ?_, by
    change Inv n K ((layout n s.frontier).abs s'); rw [hzero]; exact hI⟩, ?_⟩
  · have hmem := addr_mem_footprint (base := s.frontier) hi
    simp only [footprint, Finset.mem_Ico] at hmem
    change _ < s.frontier + (9 * n + 5)
    omega
  · change abs n ((layout n s.frontier).abs s') = _
    rw [hzero, habs]

end Cslib.DataStructure.PriorityQueue.FibonacciHeap
