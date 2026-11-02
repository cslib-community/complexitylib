/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Frame
public import Complexity.DataStructure.Memory.Triple
public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Order
public import Complexity.DataStructure.StateTransition.Refinement
public import Mathlib.Data.Nat.Log

/-!
# An indexed binary heap over the memory oracle

The indexed min-priority queue `indexedMinPQSpec n K` is implemented as a binary heap by programs
over `Memory.spec w`. The storage is a `Layout`: a one-cell `size` field and three arrays from
`base`, exactly as in `BinaryHeap.Model`: the `key` of each handle, the `heap` of handles at
positions `1, …, size`, and the `pos`ition of each handle (`0` when absent). The abstraction
function is the model's `stateOfMem`, and the invariant is the model's `HeapInv` at the stored
size. Entries are ordered by `(key, handle)`, so `extractMin` returns exactly the spec's
`findMin`.

Sift-up and sift-down are recursive memory programs (`siftUp`, `siftDown`). Their proofs are
inductions on the recursion, one level per call: the order lemmas of `BinaryHeap.Order` move the
single order defect one level, and the memory steps are discharged by the rules of
`Memory.Triple`. A level costs at most `8` memory units on the way up and `10` on the way down, so
every operation costs at most `10 ⌊log₂ n⌋ + 14` memory units (`amortized`). No register, address
arithmetic beyond the layout, or instruction count appears; word fit enters only through the
admissibility of `Memory.spec w` and two static facts of the layout, that `n` and the largest key
fit a word.

The methods write only the layout's cells and never allocate (`methods_frame`), and the
abstraction and invariant read only those cells (`abs_congr`, `Inv.congr`), so the heap is framed
by its layout (`framed`) and composes with other structures in the same memory
(`Memory.Framed.prod`). Allocated in memory that is zero above the frontier, the heap starts empty
at a cost of two memory units (`allocLayout_bind`, `inv_allocated`).

The word-RAM counterpart is `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap`, a hand-stepped
dispatcher over the same memory layout.

## Main definitions

* `Layout`, `Layout.footprint`, `Layout.Valid`: the size cell and the three arrays, the cells they
  own, and their static well-formedness.
* `swap`, `siftUp`, `siftDown`: heap repair as memory programs.
* `isEmpty`, `getKey`, `insert`, `decreaseKey`, `extractMin`, `methods`: the operations.
* `abs`, `Inv`: the abstraction function and the implementation invariant.
* `opCost`: the memory cost of one operation, `10 ⌊log₂ n⌋ + 14`.
* `refinement`, `framed`: the binary heap as a `Refinement` of `indexedMinPQSpec n K`, framed by
  its layout.
* `allocLayout`, `allocated`: allocate an empty heap, and the layout it hands out.

## Main results

* `siftUp_triple`, `siftDown_triple`: sift-up and sift-down repair one order defect within
  `8 ⌊log₂ k⌋ + 4` and `10 (⌊log₂ S⌋ - ⌊log₂ k⌋) + 6` memory units.
* `methods_triple`: each operation realizes the specified step within `opCost n`.
* `amortized`: every operation costs at most `opCost n` memory units; `opCost_le` bounds it by
  `14 (⌊log₂ n⌋ + 1)`.
* `methods_frame`, `abs_congr`, `Inv.congr`: the frame of a heap.
* `allocLayout_bind`, `valid_allocated`, `inv_allocated`: allocation yields an empty heap.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 6][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Memory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap

/-- The storage of an indexed binary heap on the handles `Fin n`: a one-cell field holding the
number of entries, and three arrays from `base`, laid out as in `BinaryHeap.Model`. -/
structure Layout (n : ℕ) where
  /-- One cell holding the number of entries. -/
  size : Block
  /-- The start of the key, heap and position arrays. -/
  base : ℕ

namespace Layout

variable {n : ℕ} (L : Layout n)

/-- The key of each handle, from `base`. -/
abbrev key : Block := ⟨L.base, n⟩

/-- The handle at each heap position `1, …, size`, from `base + n`; position `0` is unused. -/
abbrev heap : Block := ⟨L.base + n, n + 1⟩

/-- The heap position of each handle, `0` when the handle is absent, from `base + 2 n + 1`. -/
abbrev pos : Block := ⟨L.base + 2 * n + 1, n⟩

/-- The cells of the three arrays. -/
abbrev arrays : Block := ⟨L.base, space n⟩

/-- The cells a heap owns. -/
def footprint : Finset ℕ := L.size.footprint ∪ L.arrays.footprint

/-- Static well-formedness at word size `w` for keys at most `K`: the size field is one cell
outside the arrays, and `n` and `K` fit a word. -/
structure Valid (L : Layout n) (w K : ℕ) : Prop where
  /-- The size field is one cell. -/
  size_length : L.size.length = 1
  /-- The size cell is not in the arrays. -/
  size_not_owns : ¬L.arrays.Owns L.size.base
  /-- The number of handles fits a word, hence so does every handle and position. -/
  n_fits : Fits w n
  /-- The largest key fits a word. -/
  key_fits : Fits w K

end Layout

variable {n : ℕ} (L : Layout n)

/-! ## The programs -/

/-- Swap the handles `va` at heap position `a` and `vb` at heap position `b`. -/
def swap (a b va vb : ℕ) : Prog Unit := do
  L.heap.set a vb
  L.heap.set b va
  L.pos.set vb a
  L.pos.set va b

/-- Sift-up from heap position `k`: while the entry at `k` has higher priority than its parent,
swap them and continue from the parent. -/
def siftUp (k : ℕ) : Prog Unit :=
  if 2 ≤ k then do
    let vk ← L.heap.get k
    let kk ← L.key.get vk
    let vp ← L.heap.get (k / 2)
    let kp ← L.key.get vp
    if IndexedMinPQ.RawPrioLT (vk, kk) (vp, kp) then do
      swap L k (k / 2) vk vp
      siftUp (k / 2)
    else pure ()
  else pure ()
termination_by k
decreasing_by omega

/-- One step of sift-down: if the child entry `(vc, kc)` at position `c` has higher priority than
the entry `(vk, kk)` at position `k`, swap them and continue with `next`. -/
def sink (k c vk kk vc kc : ℕ) (next : Prog Unit) : Prog Unit :=
  if IndexedMinPQ.RawPrioLT (vc, kc) (vk, kk) then do
    swap L k c vk vc
    next
  else pure ()

/-- Sift-down from heap position `k` in a heap of size `S`: while some child has higher priority
than the entry at `k`, swap the entry with its child of highest priority and continue from that
child. -/
def siftDown (S k : ℕ) : Prog Unit :=
  if 1 ≤ k ∧ 2 * k ≤ S then do
    let vk ← L.heap.get k
    let kk ← L.key.get vk
    let vl ← L.heap.get (2 * k)
    let kl ← L.key.get vl
    if 2 * k + 1 ≤ S then do
      let vr ← L.heap.get (2 * k + 1)
      let kr ← L.key.get vr
      if IndexedMinPQ.RawPrioLT (vr, kr) (vl, kl) then
        sink L k (2 * k + 1) vk kk vr kr (siftDown S (2 * k + 1))
      else sink L k (2 * k) vk kk vl kl (siftDown S (2 * k))
    else sink L k (2 * k) vk kk vl kl (siftDown S (2 * k))
  else pure ()
termination_by S + 1 - k
decreasing_by all_goals omega

/-- Test for emptiness: read the size. -/
def isEmpty : Prog Bool := do
  let S ← L.size.get 0
  pure (decide (S = 0))

/-- The key of handle `v`: absent when its position is `0`. -/
def getKey (v : Fin n) : Prog (Option ℕ) := do
  let p ← L.pos.get v
  if p = 0 then pure none else do
    let k ← L.key.get v
    pure (some k)

/-- Insert the absent handle `v` with key `k`: store the key, append `v` at the end of the heap,
and sift it up. -/
def insert (v : Fin n) (k : ℕ) : Prog Unit := do
  let S ← L.size.get 0
  L.size.set 0 (S + 1)
  L.key.set v k
  L.heap.set (S + 1) v
  L.pos.set v (S + 1)
  siftUp L (S + 1)

/-- Lower the key of the present handle `v` to `k`, and sift it up from its position. -/
def decreaseKey (v : Fin n) (k : ℕ) : Prog Unit := do
  let p ← L.pos.get v
  L.key.set v k
  siftUp L p

variable (n) in
/-- The answer of `extractMin` for the handle `u` with key `k`. -/
def entry (u k : ℕ) : Option (Fin n × ℕ) := if h : u < n then some (⟨u, h⟩, k) else none

/-- Remove the root and return it: move the last entry to the root, sift it down, and store the
new size. -/
def extractMin : Prog (Option (Fin n × ℕ)) := do
  let S ← L.size.get 0
  if S = 0 then pure none else do
    let u ← L.heap.get 1
    let k ← L.key.get u
    if S = 1 then do
      L.pos.set u 0
      L.size.set 0 0
      pure (entry n u k)
    else do
      let last ← L.heap.get S
      L.pos.set u 0
      L.heap.set 1 last
      L.pos.set last 1
      siftDown L (S - 1) 1
      L.size.set 0 (S - 1)
      pure (entry n u k)

/-- The operations of the indexed min-priority queue as memory programs. -/
def ops : (o : IndexedMinPQ.Op n) → Prog o.Result
  | .isEmpty => isEmpty L
  | .getKey v => getKey L v
  | .insert v k => insert L v k
  | .decreaseKey v k => decreaseKey L v k
  | .extractMin => extractMin L

/-- The operations as methods of `indexedMinPQSpec n K` over `Memory.spec w`. -/
abbrev methods (w K : ℕ) : Methods (indexedMinPQSpec n K) (Memory.spec w) := ops L

/-- The represented queue: the model's decoding of the key and position arrays. -/
def abs (s : Memory.State) : IndexedMinPQ.State n := stateOfMem n L.base s.mem

/-- The implementation invariant: the fields are allocated, and the arrays hold a binary heap of
the stored size. -/
structure Inv (s : Memory.State) : Prop where
  /-- The size cell is allocated. -/
  size_allocated : L.size.Allocated s
  /-- The arrays are allocated. -/
  arrays_allocated : L.arrays.Allocated s
  /-- The arrays hold a binary heap of the stored size. -/
  heap : HeapInv n L.base (s.mem L.size.base) s.mem

/-- The memory cost of one operation on `n` handles: `10 ⌊log₂ n⌋ + 14` units. -/
def opCost (n : ℕ) : ℕ := 10 * Nat.log 2 n + 14

/-! ## Layout facts -/

variable {L}

/-- A key cell is allocated. -/
theorem key_lt {s : Memory.State} (hA : L.arrays.Allocated s) {v : ℕ} (hv : v < n) :
    L.key.base + v < s.frontier := by
  simp only [Block.Allocated, space] at hA ⊢
  omega

/-- A heap cell is allocated. -/
theorem heap_lt {s : Memory.State} (hA : L.arrays.Allocated s) {i : ℕ} (hi : i ≤ n) :
    L.heap.base + i < s.frontier := by
  simp only [Block.Allocated, space] at hA ⊢
  omega

/-- A position cell is allocated. -/
theorem pos_lt {s : Memory.State} (hA : L.arrays.Allocated s) {v : ℕ} (hv : v < n) :
    L.pos.base + v < s.frontier := by
  simp only [Block.Allocated, space] at hA ⊢
  omega

/-! ## Rearranging the heap -/

variable (L) in
/-- `s'` is `s` with the heap and position arrays rearranged: the frontier, the keys, the presence
of each handle and every cell outside those two arrays are unchanged. -/
structure Rearranges (s s' : Memory.State) : Prop where
  /-- The frontier is unchanged. -/
  frontier_eq : s'.frontier = s.frontier
  /-- Each handle is present exactly when it was. -/
  pos_eq_zero : ∀ v < n, s'.mem (L.base + 2 * n + 1 + v) = 0 ↔ s.mem (L.base + 2 * n + 1 + v) = 0
  /-- Cells outside the heap and position arrays are unchanged. -/
  outside : ∀ a, a ≤ L.base + n ∨ L.base + 3 * n < a → s'.mem a = s.mem a

namespace Rearranges

/-- Every state is a rearrangement of itself. -/
theorem refl (s : Memory.State) : Rearranges L s s :=
  ⟨rfl, fun _ _ => Iff.rfl, fun _ _ => rfl⟩

/-- Rearrangements compose. -/
theorem trans {s₁ s₂ s₃ : Memory.State} (h₁ : Rearranges L s₁ s₂) (h₂ : Rearranges L s₂ s₃) :
    Rearranges L s₁ s₃ :=
  ⟨h₂.frontier_eq.trans h₁.frontier_eq,
    fun v hv => (h₂.pos_eq_zero v hv).trans (h₁.pos_eq_zero v hv),
    fun a ha => (h₂.outside a ha).trans (h₁.outside a ha)⟩

/-- A swap of two heap positions rearranges the heap. -/
theorem swap {s : Memory.State} {S a b : ℕ} (h : HeapShape n L.base S s.mem) (ha : 1 ≤ a)
    (haS : a ≤ S) (hb : 1 ≤ b) (hbS : b ≤ S) (hab : a ≠ b) :
    Rearranges L s ⟨swapMem n L.base s.mem a b (s.mem (L.base + n + a)) (s.mem (L.base + n + b)),
      s.frontier⟩ := by
  obtain ⟨-, -, -, -, hpos, hout⟩ := h.swap ha haS hb hbS hab
  exact ⟨rfl, hpos, hout⟩

end Rearranges

/-! ## Sift-up and sift-down -/

variable {w : ℕ}

/-- Swapping two heap positions writes four cells. -/
theorem swap_bind {α : Type} {s : Memory.State} {a b va vb c : ℕ} {k : Unit → Prog α}
    {Q : α → Memory.State → Prop} (hn : Fits w n) (hA : L.arrays.Allocated s) (ha : a ≤ n)
    (hb : b ≤ n) (hva : va < n) (hvb : vb < n)
    (h : Triple w ⟨swapMem n L.base s.mem a b va vb, s.frontier⟩ (k ()) c Q) :
    Triple w s (swap L a b va vb >>= k) (c + 4) Q := by
  simp only [swap, bind_assoc]
  exact Triple.write_bind (heap_lt hA ha) (hn.of_le hvb.le) <|
    Triple.write_bind (heap_lt hA hb) (hn.of_le hva.le) <|
    Triple.write_bind (pos_lt hA hvb) (hn.of_le ha) <|
    Triple.write_bind (pos_lt hA hva) (hn.of_le hb) h

/-- **Sift-up** repairs an upward defect at heap position `k` within `8 ⌊log₂ k⌋ + 4` memory
units. -/
theorem siftUp_triple (hn : Fits w n) {S : ℕ} {s : Memory.State} {k : ℕ}
    (hA : L.arrays.Allocated s) (hk : 1 ≤ k) (hkS : k ≤ S) (hshape : HeapShape n L.base S s.mem)
    (hord : UpOrdered (heapEntry n L.base s.mem) S k) :
    Triple w s (siftUp L k) (8 * Nat.log 2 k + 4)
      fun _ s' => HeapInv n L.base S s'.mem ∧ Rearranges L s s' := by
  rw [siftUp]
  split_ifs with h2
  · have hSn := hshape.size_le
    have hvk := hshape.vertex_lt k hk hkS
    have hvp := hshape.vertex_lt (k / 2) (by omega) (by omega)
    have hlog : Nat.log 2 k = Nat.log 2 (k / 2) + 1 := Nat.log_of_one_lt_of_le one_lt_two h2
    refine (?_ : Triple w s _ (8 * Nat.log 2 (k / 2) + 4 + 8) _).mono (by omega)
      fun _ _ h => h
    refine Triple.read_bind (heap_lt hA (by omega)) <| Triple.read_bind (key_lt hA hvk) <|
      Triple.read_bind (heap_lt hA (by omega)) <| Triple.read_bind (key_lt hA hvp) ?_
    split_ifs with hlt
    · obtain ⟨hs', hga, hgb, hgo, -, -⟩ :=
        hshape.swap (a := k) (b := k / 2) hk hkS (by omega) (by omega) (by omega)
      have hr := Rearranges.swap (L := L) hshape hk hkS (b := k / 2) (by omega) (by omega)
        (by omega)
      refine swap_bind hn hA (by omega) (by omega) hvk hvp <|
        (siftUp_triple hn (hr.frontier_eq ▸ hA) (by omega) (by omega) hs'
          (hord.swap h2 hkS hlt hga hgb hgo)).mono le_rfl fun _ _ h => ⟨h.1, hr.trans h.2⟩
    · exact Triple.pure ⟨⟨hshape, hord.ordered fun _ _ =>
        IndexedMinPQ.not_rawPrioLT_iff_rawPrioLE.mp hlt⟩, Rearranges.refl s⟩
  · exact Triple.pure ⟨⟨hshape, hord.ordered fun h => absurd h h2⟩, Rearranges.refl s⟩
termination_by k
decreasing_by omega

/-- One step of sift-down: a swap with the child when it has higher priority, then `next`. -/
theorem sink_triple {s : Memory.State} {k c vk kk vc kc cost : ℕ} {next : Prog Unit}
    {Q : Unit → Memory.State → Prop} (hn : Fits w n) (hA : L.arrays.Allocated s) (hk : k ≤ n)
    (hc : c ≤ n) (hvk : vk < n) (hvc : vc < n)
    (hswap : IndexedMinPQ.RawPrioLT (vc, kc) (vk, kk) →
      Triple w ⟨swapMem n L.base s.mem k c vk vc, s.frontier⟩ next cost Q)
    (hstop : ¬IndexedMinPQ.RawPrioLT (vc, kc) (vk, kk) → Q () s) :
    Triple w s (sink L k c vk kk vc kc next) (cost + 4) Q := by
  rw [sink]
  split_ifs with hlt
  · exact swap_bind hn hA hk hc hvk hvc (hswap hlt)
  · exact Triple.pure (hstop hlt)

/-- **Sift-down** repairs a downward defect at heap position `k` of a heap of size `S` within
`10 (⌊log₂ S⌋ - ⌊log₂ k⌋) + 6` memory units. -/
theorem siftDown_triple (hn : Fits w n) {S : ℕ} {s : Memory.State} {k : ℕ}
    (hA : L.arrays.Allocated s) (hk : 1 ≤ k) (hkS : k ≤ S) (hshape : HeapShape n L.base S s.mem)
    (hord : DownOrdered (heapEntry n L.base s.mem) S k) :
    Triple w s (siftDown L S k) (10 * (Nat.log 2 S - Nat.log 2 k) + 6)
      fun _ s' => HeapInv n L.base S s'.mem ∧ Rearranges L s s' := by
  rw [siftDown]
  split
  next h2 =>
    have hSn := hshape.size_le
    have hvk := hshape.vertex_lt k hk hkS
    have hvl := hshape.vertex_lt (2 * k) (by omega) h2.2
    have hlogS : Nat.log 2 (2 * k) ≤ Nat.log 2 S := Nat.log_mono_right h2.2
    have hlogc : ∀ c, c / 2 = k → Nat.log 2 c = Nat.log 2 k + 1 := fun c hc => by
      rw [Nat.log_of_one_lt_of_le one_lt_two (by omega), hc]
    have hlog2 := hlogc (2 * k) (by omega)
    -- The step to the child `c` of highest priority, whichever child it is.
    have step : ∀ c, c / 2 = k → c ≤ S → c = minChild (heapEntry n L.base s.mem) S k →
        Triple w s (sink L k c (s.mem (L.base + n + k)) (s.mem (L.base + s.mem (L.base + n + k)))
          (s.mem (L.base + n + c)) (s.mem (L.base + s.mem (L.base + n + c))) (siftDown L S c))
          (10 * (Nat.log 2 S - (Nat.log 2 k + 1)) + 6 + 4)
          fun _ s' => HeapInv n L.base S s'.mem ∧ Rearranges L s s' := by
      intro c hck hcS hcmin
      obtain ⟨-, -, hmin⟩ := minChild_spec (f := heapEntry n L.base s.mem) (S := S) (a := k) h2.2
      rw [← hcmin] at hmin
      refine sink_triple hn hA (by omega) (by omega) hvk (hshape.vertex_lt c (by omega) hcS)
        (fun hlt => ?_) fun hlt => ⟨⟨hshape, hord.ordered fun i _ hiS hia =>
          (IndexedMinPQ.not_rawPrioLT_iff_rawPrioLE.mp hlt).trans (hmin i hiS hia)⟩,
          Rearranges.refl s⟩
      obtain ⟨hs', hga, hgc, hgo, -, -⟩ :=
        hshape.swap (a := k) (b := c) hk hkS (by omega) hcS (by omega)
      have hr := Rearranges.swap (L := L) hshape hk hkS (b := c) (by omega) hcS (by omega)
      refine (siftDown_triple hn (hr.frontier_eq ▸ hA) (by omega) hcS hs'
        (hord.swap hck hcS (fun i _ hiS hia => hmin i hiS hia) hlt hga hgc hgo)).mono
        (by rw [hlogc c hck]) fun _ _ h => ⟨h.1, hr.trans h.2⟩
    refine (?_ : Triple w s _ (10 * (Nat.log 2 S - (Nat.log 2 k + 1)) + 6 + 10) _).mono
      (by omega) fun _ _ h => h
    refine Triple.read_bind (heap_lt hA (by omega)) <| Triple.read_bind (key_lt hA hvk) <|
      Triple.read_bind (heap_lt hA (by omega)) <| Triple.read_bind (key_lt hA hvl) ?_
    split
    next hr =>
      have hvr := hshape.vertex_lt (2 * k + 1) (by omega) hr
      refine Triple.read_bind (heap_lt hA (by omega)) <| Triple.read_bind (key_lt hA hvr) ?_
      split
      next hlr =>
        exact step (2 * k + 1) (by omega) hr (ite_eq_left (c := _ ∧ _) ⟨hr, hlr⟩).symm
      next hlr =>
        exact step (2 * k) (by omega) h2.2 (ite_eq_right (c := _ ∧ _) fun h => hlr h.2).symm
    next hr =>
      exact (step (2 * k) (by omega) h2.2 (ite_eq_right (c := _ ∧ _) fun h => hr h.1).symm).mono
        (by omega) fun _ _ h => h
  next h2 =>
    exact Triple.pure ⟨⟨hshape, hord.ordered fun i hi hiS hia => absurd hiS (by omega)⟩,
      Rearranges.refl s⟩
termination_by S + 1 - k
decreasing_by all_goals omega

/-! ## The abstraction -/

/-- A rearrangement represents the same queue. -/
theorem Rearranges.abs_eq {s s' : Memory.State} (h : Rearranges L s s') : abs L s' = abs L s := by
  funext ⟨v, hv⟩
  have hk := h.outside (L.base + v) (.inl (by omega))
  have hp := h.pos_eq_zero v hv
  simp only [abs, stateOfMem, hk]
  by_cases h0 : s.mem (L.base + 2 * n + 1 + v) = 0
  · simp [h0, hp.mpr h0]
  · simp [h0, mt hp.mp h0]

/-- A memory that keeps the key and the presence of every handle but `v` represents the queue
updated at `v`. -/
theorem abs_eq_update {s s' : Memory.State} {v : Fin n} {x : Option ℕ}
    (hother : ∀ u : Fin n, u ≠ v → s'.mem (L.base + u) = s.mem (L.base + u) ∧
      (s'.mem (L.base + 2 * n + 1 + u) = 0 ↔ s.mem (L.base + 2 * n + 1 + u) = 0))
    (hv : abs L s' v = x) : abs L s' = Function.update (abs L s) v x := by
  funext u
  by_cases huv : u = v
  · subst huv
    rw [Function.update_self, hv]
  · rw [Function.update_of_ne huv]
    obtain ⟨hk, hp⟩ := hother u huv
    simp only [abs, stateOfMem, hk]
    by_cases h0 : s.mem (L.base + 2 * n + 1 + u) = 0
    · simp [h0, hp.mpr h0]
    · simp [h0, mt hp.mp h0]

/-! ## The operations -/

variable {K : ℕ}

/-- The cells outside the layout: neither the size cell nor an array cell. -/
theorem not_mem_footprint (hL : L.Valid w K) {a : ℕ} (ha : a ∉ L.footprint) :
    a ≠ L.size.base ∧ (a < L.base ∨ L.base + 3 * n + 1 ≤ a) := by
  simp only [Layout.footprint, Finset.mem_union, Block.mem_footprint, Block.Owns, not_or,
    not_and_or, not_le, not_lt, hL.size_length, space] at ha
  omega

/-- The size cell lies outside the arrays. -/
theorem size_outside (hL : L.Valid w K) :
    L.size.base < L.base ∨ L.base + 3 * n + 1 ≤ L.size.base := by
  have h := hL.size_not_owns
  simp only [Block.Owns, not_and_or, not_le, not_lt, space] at h
  omega

/-- The size cell is allocated. -/
theorem Inv.size_lt (hL : L.Valid w K) {s : Memory.State} (hs : Inv L s) :
    L.size.base + 0 < s.frontier :=
  hs.size_allocated.lt_frontier (by rw [hL.size_length]; omega)

/-- A heap invariant survives a write to the size cell. -/
theorem heapInv_update_size (hL : L.Valid w K) {S : ℕ} {m : ℕ → ℕ}
    (h : HeapInv n L.base S m) (x : ℕ) :
    HeapInv n L.base S (Function.update m L.size.base x) :=
  h.congr_mem fun a ha => Function.update_of_ne (fun he => hL.size_not_owns
    (by rw [← he]; exact Block.mem_footprint.mp ha)) x m

variable (L) in
/-- What a run of the operation `o` from `s` establishes: the specified step from the represented
queue, the invariant, and the frame: the frontier and every cell outside the layout are
unchanged. -/
def Post (s : Memory.State) (o : IndexedMinPQ.Op n) (r : o.Result) (s' : Memory.State) : Prop :=
  IndexedMinPQ.step (abs L s) o = (abs L s', r) ∧ Inv L s' ∧ s'.frontier = s.frontier ∧
    ∀ a ∉ L.footprint, s'.mem a = s.mem a

/-- An operation that only reads realizes a step that leaves the queue unchanged. -/
theorem post_self {s : Memory.State} (hs : Inv L s) {o : IndexedMinPQ.Op n} {r : o.Result}
    (h : IndexedMinPQ.step (abs L s) o = (abs L s, r)) : Post L s o r s :=
  ⟨h, hs, rfl, fun _ _ => rfl⟩

/-- `isEmpty` reads the size. -/
theorem isEmpty_triple (hL : L.Valid w K) {s : Memory.State} (hs : Inv L s) :
    Triple w s (isEmpty L) 1 (Post L s .isEmpty) := by
  refine Triple.read_bind (hs.size_lt hL) (Triple.pure (post_self hs ?_))
  exact Prod.ext rfl (decide_eq_decide.mpr hs.heap.size_eq_zero_iff).symm

/-- `getKey` reads the position and, for a present handle, the key. -/
theorem getKey_triple {s : Memory.State} (hs : Inv L s) (v : Fin n) :
    Triple w s (getKey L v) 2 (Post L s (.getKey v)) := by
  refine Triple.read_bind (pos_lt hs.arrays_allocated v.isLt) ?_
  split
  next hp => exact Triple.pure (post_self hs (Prod.ext rfl (ite_eq_left hp)))
  next hp =>
    exact Triple.read_bind (key_lt hs.arrays_allocated v.isLt)
      (Triple.pure (post_self hs (Prod.ext rfl (ite_eq_right hp))))

/-- `insert` appends the handle and sifts it up, within `8 ⌊log₂ n⌋ + 9` memory units. -/
theorem insert_triple (hL : L.Valid w K) {s : Memory.State} (hs : Inv L s) {v : Fin n} {k : ℕ}
    (hv : IndexedMinPQ.valid K (abs L s) (.insert v k)) :
    Triple w s (insert L v k) (8 * Nat.log 2 n + 9) (Post L s (.insert v k)) := by
  obtain ⟨hnone, hk⟩ := hv
  have hA := hs.arrays_allocated
  have hp : s.mem (L.base + 2 * n + 1 + v) = 0 := by
    by_contra h
    simp [abs, stateOfMem, h] at hnone
  have hSn := hs.heap.size_lt v.isLt hp
  have hsz := size_outside hL
  have hlog := Nat.log_mono_right (b := 2) (show s.mem L.size.base + 1 ≤ n by omega)
  refine (?_ : Triple w s _ (8 * Nat.log 2 (s.mem L.size.base + 1) + 4 + 5) _).mono (by omega)
    fun _ _ h => h
  refine Triple.read_bind (hs.size_lt hL) ?_
  simp only [Nat.add_zero]
  refine Triple.write_bind (hs.size_lt hL) (hL.n_fits.of_le (by omega)) <|
    Triple.write_bind (key_lt hA v.isLt) (hL.key_fits.of_le hk) <|
    Triple.write_bind (heap_lt hA (by omega)) (hL.n_fits.of_le v.isLt.le) <|
    Triple.write_bind (pos_lt hA v.isLt) (hL.n_fits.of_le (by omega)) ?_
  obtain ⟨hshape, hord⟩ := (heapInv_update_size hL hs.heap (s.mem L.size.base + 1)).push v.isLt
    (c := k) (by rw [Function.update_of_ne (by omega)]; exact hp)
  refine Triple.mono (siftUp_triple hL.n_fits hA (by omega) le_rfl hshape hord) le_rfl ?_
  rintro _ s' ⟨hinv, hr⟩
  have hsize : s'.mem L.size.base = s.mem L.size.base + 1 := by
    rw [hr.outside _ (by omega)]
    simp only [Function.update_apply]
    split_ifs <;> omega
  refine ⟨?_, ⟨hs.size_allocated.mono (by rw [hr.frontier_eq]),
    hA.mono (by rw [hr.frontier_eq]), hsize ▸ hinv⟩, hr.frontier_eq, fun a ha => ?_⟩
  · rw [hr.abs_eq]
    refine Prod.ext (abs_eq_update (fun u hu => ?_) ?_).symm rfl
    · have hu' : (u : ℕ) ≠ v := Fin.val_ne_of_ne hu
      simp only [Function.update_apply]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
    · simp only [abs, stateOfMem, Function.update_apply]
      split_ifs <;> first | rfl | (exfalso; omega)
  · obtain ⟨ha₁, ha₂⟩ := not_mem_footprint hL ha
    rw [hr.outside a (by omega)]
    simp only [Function.update_apply]
    split_ifs <;> omega

/-- `decreaseKey` lowers the key and sifts the handle up, within `8 ⌊log₂ n⌋ + 6` memory units. -/
theorem decreaseKey_triple (hL : L.Valid w K) {s : Memory.State} (hs : Inv L s) {v : Fin n}
    {k : ℕ} (hv : IndexedMinPQ.valid K (abs L s) (.decreaseKey v k)) :
    Triple w s (decreaseKey L v k) (8 * Nat.log 2 n + 6) (Post L s (.decreaseKey v k)) := by
  obtain ⟨⟨k₀, hk₀, hle⟩, hk⟩ := hv
  have hA := hs.arrays_allocated
  have hp : s.mem (L.base + 2 * n + 1 + v) ≠ 0 := by
    intro h
    simp [abs, stateOfMem, h] at hk₀
  have hkey : s.mem (L.base + v) = k₀ := by simpa [abs, stateOfMem, hp] using hk₀
  have hsz := size_outside hL
  have hpS := hs.heap.pos_le v v.isLt
  have hSn := hs.heap.size_le
  have hlog := Nat.log_mono_right (b := 2) (show s.mem (L.base + 2 * n + 1 + v) ≤ n by omega)
  refine (?_ : Triple w s _ (8 * Nat.log 2 (s.mem (L.base + 2 * n + 1 + v)) + 4 + 2) _).mono
    (by omega) fun _ _ h => h
  refine Triple.read_bind (pos_lt hA v.isLt) <|
    Triple.write_bind (key_lt hA v.isLt) (hL.key_fits.of_le hk) ?_
  obtain ⟨hshape, hord⟩ := hs.heap.decrease v.isLt hp (c := k) (by omega)
  refine Triple.mono (siftUp_triple hL.n_fits hA (Nat.one_le_iff_ne_zero.mpr hp) hpS hshape hord)
    le_rfl ?_
  rintro _ s' ⟨hinv, hr⟩
  have hsize : s'.mem L.size.base = s.mem L.size.base := by
    rw [hr.outside _ (by omega)]
    exact Function.update_of_ne (show L.size.base ≠ L.base + v by omega) _ _
  refine ⟨?_, ⟨hs.size_allocated.mono (by rw [hr.frontier_eq]),
    hA.mono (by rw [hr.frontier_eq]), hsize ▸ hinv⟩, hr.frontier_eq, fun a ha => ?_⟩
  · rw [hr.abs_eq]
    refine Prod.ext (abs_eq_update (fun u hu => ?_) ?_).symm rfl
    · have hu' : (u : ℕ) ≠ v := Fin.val_ne_of_ne hu
      simp only [Function.update_apply]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
    · simp only [abs, stateOfMem, Function.update_apply]
      split_ifs <;> first | rfl | (exfalso; omega)
  · obtain ⟨ha₁, ha₂⟩ := not_mem_footprint hL ha
    rw [hr.outside a (by omega)]
    simp only [Function.update_apply]
    split_ifs <;> omega

/-- The answer for a handle. -/
theorem entry_of_lt {u : ℕ} (hu : u < n) (k : ℕ) : entry n u k = some (⟨u, hu⟩, k) :=
  dite_eq_left hu

/-- The postcondition of an extraction that removes the minimum `(u, k)`. -/
theorem post_extract {s s' : Memory.State} {u k : ℕ} (hu : u < n)
    (hfind : IndexedMinPQ.findMin (abs L s) = some (⟨u, hu⟩, k))
    (habs : abs L s' = Function.update (abs L s) ⟨u, hu⟩ none) (hinv : Inv L s')
    (hf : s'.frontier = s.frontier) (hframe : ∀ a ∉ L.footprint, s'.mem a = s.mem a) :
    Post L s .extractMin (entry n u k) s' :=
  ⟨by simp only [IndexedMinPQ.step, hfind, habs, entry_of_lt hu], hinv, hf, hframe⟩

/-- `extractMin` removes the root, moves the last entry up and sifts it down, within `opCost n`
memory units. -/
theorem extractMin_triple (hL : L.Valid w K) {s : Memory.State} (hs : Inv L s) :
    Triple w s (extractMin L) (opCost n) (Post L s .extractMin) := by
  have hA := hs.arrays_allocated
  have hsz := size_outside hL
  obtain ⟨S, hS⟩ : ∃ S, s.mem L.size.base = S := ⟨_, rfl⟩
  have hinv : HeapInv n L.base S s.mem := hS ▸ hs.heap
  have hSn := hinv.size_le
  have hlog := Nat.log_mono_right (b := 2) (show S - 1 ≤ n by omega)
  refine (?_ : Triple w s _ (10 * (Nat.log 2 (S - 1) - Nat.log 2 1) + 6 + 1 + 7) _).mono
    (by simp only [opCost, Nat.log_one_right]; omega) fun _ _ h => h
  refine Triple.read_bind (hs.size_lt hL) ?_
  simp only [Nat.add_zero, hS]
  split
  next h0 =>
    refine Triple.pure (post_self hs ?_)
    have hfind : IndexedMinPQ.findMin (abs L s) = none :=
      IndexedMinPQ.findMin_eq_none_iff.mpr (hinv.size_eq_zero_iff.mp h0)
    simp only [IndexedMinPQ.step, hfind]
  next h0 =>
    have hS1 : 1 ≤ S := Nat.one_le_iff_ne_zero.mpr h0
    have hroot := hinv.vertex_lt 1 le_rfl hS1
    have hfind := hinv.findMin_eq_root hS1
    refine Triple.read_bind (heap_lt hA (by omega)) <| Triple.read_bind (key_lt hA hroot) ?_
    split
    next h1 =>
      subst h1
      have hzero := hinv.extract_one
      refine Triple.write_bind (pos_lt hA hroot) (fits_zero w) <|
        Triple.write_bind (hs.size_lt hL) (fits_zero w) <| Triple.pure ?_
      refine post_extract (u := s.mem (L.base + n + 1)) hroot hfind ?_
        ⟨hs.size_allocated, hA, ?_⟩ rfl fun a ha => ?_
      · refine abs_eq_update (fun u hu => ?_) ?_
        · have hu' : (u : ℕ) ≠ s.mem (L.base + n + 1) := Fin.val_ne_of_ne hu
          simp only [Nat.add_zero, Function.update_apply]
          refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
        · simp only [abs, stateOfMem, Nat.add_zero,
            Function.update_apply]
          split_ifs <;> first | rfl | (exfalso; omega)
      · have h := heapInv_update_size hL hzero 0
        simp only [Nat.add_zero, Function.update_self]
        exact h
      · obtain ⟨ha₁, ha₂⟩ := not_mem_footprint hL ha
        simp only [Nat.add_zero, Function.update_apply]
        split_ifs <;> omega
    next h1 =>
      have hS2 : 2 ≤ S := by omega
      have hlast := hinv.vertex_lt S (by omega) le_rfl
      obtain ⟨hshape', hdown, hpos'⟩ := hinv.extract hS2
      refine Triple.read_bind (heap_lt hA (by omega)) <|
        Triple.write_bind (pos_lt hA hroot) (fits_zero w) <|
        Triple.write_bind (heap_lt hA (by omega)) (hL.n_fits.of_le hlast.le) <|
        Triple.write_bind (pos_lt hA hlast) (hL.n_fits.of_le (by omega)) ?_
      refine Triple.bind (c₁ := 10 * (Nat.log 2 (S - 1) - Nat.log 2 1) + 6) (c₂ := 1)
        (Triple.mono (siftDown_triple hL.n_fits hA le_rfl (by omega) hshape' hdown) le_rfl ?_)
      rintro _ s' ⟨hinv', hr⟩
      refine Triple.write_bind (hr.frontier_eq ▸ hs.size_lt hL) (hL.n_fits.of_le (by omega)) <|
        Triple.pure ?_
      refine post_extract (u := s.mem (L.base + n + 1)) hroot hfind ?_
        ⟨hs.size_allocated.mono (by rw [hr.frontier_eq]), hA.mono (by rw [hr.frontier_eq]), ?_⟩
        hr.frontier_eq fun a ha => ?_
      · have habs' := hr.abs_eq
        refine abs_eq_update (fun u hu => ?_) ?_
        · have hu' : (u : ℕ) ≠ s.mem (L.base + n + 1) := Fin.val_ne_of_ne hu
          have hp := hpos' u u.isLt
          have hk' := hr.outside (L.base + u) (.inl (by omega))
          have hp' := hr.pos_eq_zero u u.isLt
          simp only [Layout.heap, Layout.pos, Nat.add_zero, Function.update_apply]
            at hp hk' hp' ⊢
          refine ⟨?_, ?_⟩
          · split_ifs <;> first | omega | (rw [hk']; split_ifs <;> omega)
          · split_ifs <;> omega
        · have hp := (hr.pos_eq_zero _ hroot).mpr ((hpos' _ hroot).mpr (.inr rfl))
          simp only [abs, stateOfMem, Nat.add_zero, Function.update_apply]
          split_ifs <;> first | rfl | (exfalso; omega)
      · simp only [Nat.add_zero, Function.update_self]
        exact heapInv_update_size hL hinv' _
      · obtain ⟨ha₁, ha₂⟩ := not_mem_footprint hL ha
        have := hr.outside a (by omega)
        simp only [Layout.heap, Layout.pos, Nat.add_zero, Function.update_apply]
          at this ⊢
        split_ifs at this ⊢ <;> omega

/-- **Each operation realizes the specified step** within `opCost n` memory units, keeps the
invariant, and changes neither the frontier nor any cell outside the layout. -/
theorem methods_triple (hL : L.Valid w K) {s : Memory.State} (hs : Inv L s)
    (o : IndexedMinPQ.Op n) (hv : IndexedMinPQ.valid K (abs L s) o) :
    Triple w s (ops L o) (opCost n) (Post L s o) := by
  cases o with
  | isEmpty => exact (isEmpty_triple hL hs).mono (by unfold opCost; omega) fun _ _ h => h
  | getKey v => exact (getKey_triple hs v).mono (by unfold opCost; omega) fun _ _ h => h
  | insert v k => exact (insert_triple hL hs hv).mono (by unfold opCost; omega) fun _ _ h => h
  | decreaseKey v k =>
    exact (decreaseKey_triple hL hs hv).mono (by unfold opCost; omega) fun _ _ h => h
  | extractMin => exact extractMin_triple hL hs

/-- The run of an operation, by `methods_triple`. -/
theorem methods_run (hL : L.Valid w K) {s : Memory.State} (hs : Inv L s)
    (o : IndexedMinPQ.Op n) (hv : IndexedMinPQ.valid K (abs L s) o) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ops L o)) ∧
      (Memory.spec w).totalCost charge s ((Memory.spec w).clientHistory s (ops L o)) ≤ opCost n ∧
      Post L s o ((Memory.spec w).clientResult s (ops L o))
        ((Memory.spec w).clientState s (ops L o)) :=
  triple_iff.mp (methods_triple hL hs o hv)

/-- An operation changes no cell outside the layout. -/
theorem methods_frame (hL : L.Valid w K) {s : Memory.State} (hs : Inv L s)
    (o : IndexedMinPQ.Op n) (hv : IndexedMinPQ.valid K (abs L s) o) :
    ∀ a ∉ L.footprint, ((Memory.spec w).clientState s (ops L o)).mem a = s.mem a := by
  obtain ⟨-, -, -, -, -, h⟩ := methods_run hL hs o hv
  exact h

/-! ## The refinement and its frame -/

/-- The binary heap implements the indexed min-priority queue with keys at most `K`. -/
def refinement (hL : L.Valid w K) : Refinement (indexedMinPQSpec n K) (Memory.spec w) :=
  Refinement.ofFn (methods L w K) (Inv L) (abs L)
    (fun o hs hv => (methods_run hL hs o hv).1)
    (fun o hs hv => by
      obtain ⟨-, -, hstep, hinv, -⟩ := methods_run hL hs o hv
      exact ⟨hstep, hinv⟩)

/-- The layout's cells are allocated. -/
theorem Inv.lt_frontier (hL : L.Valid w K) {s : Memory.State} (hs : Inv L s) {a : ℕ}
    (ha : a ∈ L.footprint) : a < s.frontier := by
  have h₁ := hs.size_allocated
  have h₂ := hs.arrays_allocated
  simp only [Layout.footprint, Finset.mem_union, Block.mem_footprint, Block.Owns,
    hL.size_length, space] at ha
  simp only [Block.Allocated, hL.size_length, space] at h₁ h₂
  omega

/-- The abstraction reads only the arrays. -/
theorem abs_congr {s s' : Memory.State} (h : ∀ a ∈ L.footprint, s'.mem a = s.mem a) :
    abs L s' = abs L s :=
  stateOfMem_congr fun a ha => h a (Finset.mem_union_right _ ha)

/-- The invariant reads only the layout's cells and survives a growing frontier. -/
theorem Inv.congr (hL : L.Valid w K) {s s' : Memory.State} (hs : Inv L s)
    (h : ∀ a ∈ L.footprint, s'.mem a = s.mem a) (hf : s.frontier ≤ s'.frontier) :
    Inv L s' where
  size_allocated := hs.size_allocated.mono hf
  arrays_allocated := hs.arrays_allocated.mono hf
  heap := by
    rw [h _ (Finset.mem_union_left _ (Block.mem_footprint.mpr
      ⟨le_rfl, by rw [hL.size_length]; omega⟩))]
    exact hs.heap.congr_mem fun a ha => h a (Finset.mem_union_right _ ha)

/-- The binary heap, with its layout's cells as a constant footprint, so that it shares memory
with other structures (`Memory.Framed.prod`). -/
def framed (hL : L.Valid w K) : Memory.Framed (indexedMinPQSpec n K) w :=
  .ofStatic (refinement hL) L.footprint (fun hs ha => hs.lt_frontier hL ha)
    (fun hs h hf => ⟨hs.congr hL h hf, abs_congr h⟩)
    (fun o hs hv b _ hb => methods_frame hL hs o hv b hb)

/-- The footprint of a heap is its layout's cells. -/
@[simp] theorem framed_footprint (hL : L.Valid w K) (s : Memory.State) :
    (framed hL).footprint s = L.footprint := rfl

/-- **Every operation costs at most `opCost n = 10 ⌊log₂ n⌋ + 14` memory units**, with no
potential. -/
theorem amortized (hL : L.Valid w K) :
    (framed hL).Amortized charge (fun _ _ => opCost n) fun _ => 0 :=
  Refinement.Amortized.ofFn fun {_} o hs hv => by
    obtain ⟨-, hc, -⟩ := methods_run (w := w) hL hs o hv
    exact Nat.add_le_add_right hc 0

/-- The cost of one operation is `O(log n)`: at most `14 (⌊log₂ n⌋ + 1)`. -/
theorem opCost_le (n : ℕ) : opCost n ≤ 14 * (Nat.log 2 n + 1) := by
  unfold opCost
  omega

/-! ## Allocation -/

/-- Allocate a heap on `n` handles without clearing its storage: in memory that is zero above
the frontier, it starts empty. -/
def allocLayout (n : ℕ) : Prog (Layout n) := do
  let size ← allocBlockDirty 1
  let arrays ← allocBlockDirty (space n)
  pure ⟨size, arrays.base⟩

/-- The layout that `allocLayout n` hands out at the frontier `f`. -/
abbrev allocated (n f : ℕ) : Layout n := ⟨⟨f, 1⟩, f + 1⟩

/-- Allocation takes two memory units and hands out the layout at the frontier. -/
theorem allocLayout_bind {α : Type} {s : Memory.State} {c : ℕ} {next : Layout n → Prog α}
    {Q : α → Memory.State → Prop} (hfit : Fits w (s.frontier + 1 + space n))
    (h : Triple w ⟨s.mem, s.frontier + 1 + space n⟩ (next (allocated n s.frontier)) c Q) :
    Triple w s (allocLayout n >>= next) (c + 2) Q := by
  simp only [allocLayout, bind_assoc]
  exact Triple.allocBlockDirty_bind (hfit.of_le (by omega)) <|
    Triple.allocBlockDirty_bind hfit (by simpa only [pure_bind] using h)

/-- The allocated layout is well formed when `n` and the largest key fit a word. -/
theorem valid_allocated {f : ℕ} (hn : Fits w n) (hK : Fits w K) :
    (allocated n f).Valid w K where
  size_length := rfl
  size_not_owns := by simp [Block.Owns]
  n_fits := hn
  key_fits := hK

/-- The allocated layout lies at or above the frontier it was allocated from. -/
theorem le_of_mem_footprint_allocated {f a : ℕ} (ha : a ∈ (allocated n f).footprint) : f ≤ a := by
  simp only [Layout.footprint, Finset.mem_union, Block.mem_footprint, Block.Owns] at ha
  omega

/-- Allocated from memory that is zero above the frontier, the heap satisfies the invariant and
is empty. -/
theorem inv_allocated {s : Memory.State} (hz : ZeroAbove s) :
    Inv (allocated n s.frontier) ⟨s.mem, s.frontier + 1 + space n⟩ ∧
      abs (allocated n s.frontier) ⟨s.mem, s.frontier + 1 + space n⟩ = IndexedMinPQ.empty n := by
  have hpos : ∀ v < n, s.mem (s.frontier + 1 + 2 * n + 1 + v) = 0 := fun v _ => hz _ (by omega)
  have hshape : HeapShape n (s.frontier + 1) 0 s.mem :=
    ⟨Nat.zero_le _, fun _ h1 h2 => by omega, fun _ h1 h2 => by omega,
      fun v hv => (hpos v hv).le, fun v hv h0 => absurd (hpos v hv) h0⟩
  refine ⟨⟨le_rfl.trans (by simp only; omega), by simp only [Block.Allocated]; omega, ?_⟩,
    hshape.stateOfMem_zero⟩
  rw [hz s.frontier le_rfl]
  exact ⟨hshape, fun _ h1 h2 => by omega⟩

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Memory
