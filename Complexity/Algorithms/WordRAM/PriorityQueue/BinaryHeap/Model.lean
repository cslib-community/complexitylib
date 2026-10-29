/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.IndexedMinPQ
public import Complexity.Computability.WordRAM.Heap
import Mathlib.Order.Interval.Finset.Nat

/-!
# Indexed Binary Min-Heap: Memory Model and Invariant

This file defines the flat memory layout and structural/ordering invariants of the standalone
word-RAM indexed binary min-heap on `N` handles `0, …, N - 1` placed at base address `base`
with footprint `space N = 3 * N + 1`:

* `mem (base + v)` (`v < N`): current key of handle `v` (arbitrary word in `0 .. K_max`, including
  `0`).
* `mem (base + N + i)` (`1 ≤ i ≤ sz`): handle stored at 1-based heap position `i` (`base + N` is
  unused).
* `mem (base + 2 * N + 1 + v)` (`v < N`): 1-based heap position of handle `v`, or `0` when `v` is
  absent from the priority queue.

Heap entries are ordered by `Cslib.Algorithms.Lean.IndexedMinPQ.PrioLE` on `(handle, key)`,
breaking equal-key ties toward smaller handle indices so `extractMin` deterministically implements
`Cslib.Algorithms.Lean.IndexedMinPQ.findMin`.

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.space`: footprint size `3 * N + 1`.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.stateOfMem`: abstract `IndexedMinPQ.State N`
  represented in memory.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.HeapShape`,
  `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.HeapInv`: structural and lexicographic heap
  invariants.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.UpOrdered`,
  `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.DownOrdered`: single-defect invariants during
  `siftUp` and `siftDown`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap

open Cslib.WordRAM
open Cslib.Algorithms.Lean

/-- Memory footprint size (`3 * N + 1` words) of an indexed binary heap over `N` handles. -/
def space (N : ℕ) : ℕ := 3 * N + 1

/-- The binary-heap footprint on `N` handles is at least `N + 1` words. -/
theorem space_lower (N : ℕ) : N + 1 ≤ space N := by
  unfold space; omega

/-- Decreasing a handle's key improves its priority under `IndexedMinPQ.RawPrioLE`. -/
theorem entryLE_of_key_le {u k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    IndexedMinPQ.RawPrioLE (u, k₁) (u, k₂) := by
  dsimp only [IndexedMinPQ.RawPrioLE]; omega

/-- The `(handle, key)` pair stored at 1-based heap position `i`. -/
def heapEntry (N base : ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ × ℕ :=
  (mem (base + N + i), mem (base + mem (base + N + i)))

/-- Abstract `IndexedMinPQ.State N` decoded from the `key` and `pos` arrays at `base`. -/
def stateOfMem (N base : ℕ) (mem : ℕ → ℕ) : IndexedMinPQ.State N :=
  fun v => if mem (base + 2 * N + 1 + v.val) = 0 then none else some (mem (base + v.val))

/-- `stateOfMem` depends only on memory cells inside `(Block.mk base (space N)).footprint`. -/
theorem stateOfMem_congr {N base : ℕ} {m₁ m₂ : ℕ → ℕ}
    (h : ∀ a ∈ (Block.mk base (space N)).footprint, m₁ a = m₂ a) :
    stateOfMem N base m₁ = stateOfMem N base m₂ := by
  funext ⟨v, hv⟩
  simp only [stateOfMem]
  have hp : base + 2 * N + 1 + v ∈ (Block.mk base (space N)).footprint := by
    rw [Block.mem_footprint]; dsimp only [Block.Owns, space]; omega
  have hk : base + v ∈ (Block.mk base (space N)).footprint := by
    rw [Block.mem_footprint]; dsimp only [Block.Owns, space]; omega
  rw [h _ hp, h _ hk]

/-- **Structural binary-heap invariant**: positions `1, …, sz` store handles `< N`, and the `pos`
array at `base + 2 * N + 1` is the partial inverse of `heap` at `base + N`. -/
structure HeapShape (N base sz : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Heap size never exceeds `N`. -/
  size_le : sz ≤ N
  /-- Every occupied heap slot holds a valid handle `< N`. -/
  vertex_lt : ∀ i, 1 ≤ i → i ≤ sz → mem (base + N + i) < N
  /-- `pos[heap[i]] = i` for `1 ≤ i ≤ sz`. -/
  pos_vertex : ∀ i, 1 ≤ i → i ≤ sz → mem (base + 2 * N + 1 + mem (base + N + i)) = i
  /-- Every handle's position is at most `sz`. -/
  pos_le : ∀ v < N, mem (base + 2 * N + 1 + v) ≤ sz
  /-- Every handle with nonzero position `p` sits at `heap[p]`. -/
  vertex_pos : ∀ v < N, mem (base + 2 * N + 1 + v) ≠ 0 →
    mem (base + N + mem (base + 2 * N + 1 + v)) = v

/-- Heap order under `IndexedMinPQ.RawPrioLE`: every child `2 ≤ i ≤ sz` has priority at least that
of its parent `i / 2`. -/
def Ordered (f : ℕ → ℕ × ℕ) (sz : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ sz → IndexedMinPQ.RawPrioLE (f (i / 2)) (f i)

/-- Heap order except possibly between `k` and its parent `k / 2` (`siftUp` invariant). -/
def UpOrdered (f : ℕ → ℕ × ℕ) (sz k : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ sz →
    (i ≠ k → IndexedMinPQ.RawPrioLE (f (i / 2)) (f i)) ∧
    (i / 2 = k → 2 ≤ k → IndexedMinPQ.RawPrioLE (f (k / 2)) (f i))

/-- Heap order except possibly between `k` and its children (`siftDown` invariant). -/
def DownOrdered (f : ℕ → ℕ × ℕ) (sz k : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ sz →
    (i / 2 ≠ k → IndexedMinPQ.RawPrioLE (f (i / 2)) (f i)) ∧
    (i / 2 = k → 2 ≤ k → IndexedMinPQ.RawPrioLE (f (k / 2)) (f i))

/-- **Full binary-heap invariant**: structural bijection plus lexicographic heap order. -/
structure HeapInv (N base sz : ℕ) (mem : ℕ → ℕ) : Prop extends HeapShape N base sz mem where
  /-- Lexicographic min-heap order on `(handle, key)`. -/
  ordered : Ordered (heapEntry N base mem) sz

section InvariantLemmas

variable {N base S : ℕ} {mem : ℕ → ℕ}

/-- `HeapInv` depends only on memory cells inside `(Block.mk base (space N)).footprint`. -/
theorem HeapInv.congr_mem {m₂ : ℕ → ℕ} (h : HeapInv N base S mem)
    (hm : ∀ a ∈ (Block.mk base (space N)).footprint, m₂ a = mem a) :
    HeapInv N base S m₂ := by
  have hSN := h.size_le
  have hk (v : ℕ) (hv : v < N) : m₂ (base + v) = mem (base + v) :=
    hm _ (by rw [Block.mem_footprint]; dsimp only [Block.Owns, space]; omega)
  have hh (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ S) : m₂ (base + N + i) = mem (base + N + i) :=
    hm _ (by rw [Block.mem_footprint]; dsimp only [Block.Owns, space]; omega)
  have hp (v : ℕ) (hv : v < N) : m₂ (base + 2 * N + 1 + v) = mem (base + 2 * N + 1 + v) :=
    hm _ (by rw [Block.mem_footprint]; dsimp only [Block.Owns, space]; omega)
  have hent (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ S) :
      heapEntry N base m₂ i = heapEntry N base mem i := by
    have hv := h.vertex_lt i h1 h2
    simp only [heapEntry, hh i h1 h2, hk _ hv]
  refine ⟨⟨hSN, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun v hv => ?_, fun v hv hv0 => ?_⟩,
    fun i h1 h2 => ?_⟩
  · rw [hh i h1 h2]; exact h.vertex_lt i h1 h2
  · rw [hh i h1 h2, hp _ (h.vertex_lt i h1 h2)]; exact h.pos_vertex i h1 h2
  · rw [hp v hv]; exact h.pos_le v hv
  · rw [hp v hv] at hv0 ⊢
    rw [hh _ (Nat.one_le_iff_ne_zero.2 hv0) (h.pos_le v hv)]
    exact h.vertex_pos v hv hv0
  · rw [hent (i / 2) (by omega) (by omega), hent i (by omega) h2]
    exact h.ordered i h1 h2

/-- A heap missing handle `v < N` has size strictly below `N`. -/
theorem HeapShape.size_lt (h : HeapShape N base S mem) {v : ℕ} (hv : v < N)
    (hp : mem (base + 2 * N + 1 + v) = 0) : S < N := by
  have hcard := Finset.card_le_card_of_injOn (fun i => mem (base + N + i))
    (s := Finset.Icc 1 S) (t := (Finset.range N).erase v) (fun i hi => ?_)
    (fun i hi j hj he => ?_)
  · rw [Nat.card_Icc, Finset.card_erase_of_mem (Finset.mem_range.2 hv), Finset.card_range]
      at hcard
    omega
  · rw [Finset.mem_coe, Finset.mem_Icc] at hi
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_range]
    refine ⟨fun he => ?_, h.vertex_lt i hi.1 hi.2⟩
    have := h.pos_vertex i hi.1 hi.2
    simp only at he
    rw [he, hp] at this
    omega
  · rw [Finset.mem_coe, Finset.mem_Icc] at hi hj
    have h1 := h.pos_vertex i hi.1 hi.2
    have h2 := h.pos_vertex j hj.1 hj.2
    simp only at he
    rw [he] at h1
    omega

/-- When `sz = 0`, the represented `IndexedMinPQ.State N` is `empty N`. -/
theorem HeapShape.stateOfMem_zero (h : HeapShape N base 0 mem) :
    stateOfMem N base mem = IndexedMinPQ.empty N := by
  funext ⟨v, hv⟩
  have hp : mem (base + 2 * N + 1 + v) = 0 := Nat.eq_zero_of_le_zero (h.pos_le v hv)
  simp only [stateOfMem, hp, ↓reduceIte, IndexedMinPQ.empty]

/-- Size `S = 0` iff the represented `dom` is empty. -/
theorem HeapShape.size_eq_zero_iff (h : HeapShape N base S mem) :
    S = 0 ↔ IndexedMinPQ.dom (stateOfMem N base mem) = ∅ := by
  constructor
  · rintro rfl
    rw [h.stateOfMem_zero, IndexedMinPQ.dom_empty]
  · intro hdom
    by_contra hS
    have h1 : 1 ≤ S := Nat.one_le_iff_ne_zero.2 hS
    let u : Fin N := ⟨mem (base + N + 1), h.vertex_lt 1 le_rfl h1⟩
    have hpu : mem (base + 2 * N + 1 + u.val) = 1 := h.pos_vertex 1 le_rfl h1
    have hu_mem : u ∈ IndexedMinPQ.dom (stateOfMem N base mem) := by
      rw [IndexedMinPQ.mem_dom_iff]
      refine ⟨mem (base + u.val), ?_⟩
      simp only [stateOfMem, hpu, one_ne_zero, ↓reduceIte]
    rw [hdom] at hu_mem
    exact Finset.notMem_empty u hu_mem

/-- **Root optimality**: the root at position `1` has lexicographically minimum `(handle, key)`
among all handles present in the heap, so `IndexedMinPQ.findMin` equals the root entry. -/
theorem HeapInv.findMin_eq_root (h : HeapInv N base S mem) (hS : 1 ≤ S) :
    IndexedMinPQ.findMin (stateOfMem N base mem) =
      some (⟨mem (base + N + 1), h.vertex_lt 1 le_rfl hS⟩, mem (base + mem (base + N + 1))) := by
  have key : ∀ i, 1 ≤ i → i ≤ S →
      IndexedMinPQ.RawPrioLE (heapEntry N base mem 1) (heapEntry N base mem i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro h1 h2
      rcases Nat.lt_or_ge i 2 with hi | hi
      · obtain rfl : i = 1 := by omega
        exact IndexedMinPQ.RawPrioLE.refl _
      · exact (ih (i / 2) (by omega) (by omega) (by omega)).trans (h.ordered i hi h2)
  rw [IndexedMinPQ.findMin_eq_some_iff]
  refine ⟨?_, fun v k' hsv => ?_⟩
  · simp only [stateOfMem, h.pos_vertex 1 le_rfl hS, one_ne_zero, ↓reduceIte]
  · simp only [stateOfMem] at hsv
    by_cases hp : mem (base + 2 * N + 1 + v.val) = 0
    · simp only [hp, ↓reduceIte, reduceCtorEq] at hsv
    · simp only [hp, ↓reduceIte, Option.some.injEq] at hsv
      subst hsv
      have hle := key (mem (base + 2 * N + 1 + v.val)) (Nat.one_le_iff_ne_zero.2 hp)
        (h.pos_le v.val v.isLt)
      dsimp only [heapEntry] at hle ⊢
      rw [h.vertex_pos v.val v.isLt hp] at hle
      exact hle

/-- **Insertion**: storing key `c` for an absent handle `v < N` and appending `v` at `S + 1`
produces `HeapShape` and `UpOrdered` at `S + 1`. -/
theorem HeapInv.push (h : HeapInv N base S mem) {v c : ℕ} (hv : v < N)
    (hp : mem (base + 2 * N + 1 + v) = 0) :
    let m' := Function.update (Function.update (Function.update mem (base + v) c)
      (base + N + (S + 1)) v) (base + 2 * N + 1 + v) (S + 1)
    HeapShape N base (S + 1) m' ∧ UpOrdered (heapEntry N base m') (S + 1) (S + 1) := by
  intro m'
  have hSN := h.size_lt hv hp
  have hne : ∀ i, 1 ≤ i → i ≤ S → mem (base + N + i) ≠ v := fun i h1 h2 he => by
    have := h.pos_vertex i h1 h2
    rw [he, hp] at this
    omega
  have hent : ∀ i, 1 ≤ i → i ≤ S → heapEntry N base m' i = heapEntry N base mem i := by
    intro i h1 h2
    have := hne i h1 h2
    have := h.vertex_lt i h1 h2
    simp only [m', heapEntry, Function.update_apply]
    ext <;> (dsimp only; split_ifs <;> omega)
  refine ⟨⟨by omega, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun w hw => ?_,
    fun w hw hw0 => ?_⟩, fun i h1 h2 => ⟨fun hi => ?_, fun hi _ => by omega⟩⟩
  · rcases Nat.lt_or_ge i (S + 1) with hi | hi
    · have := h.vertex_lt i h1 (by omega)
      simp only [m', Function.update_apply]; split_ifs <;> omega
    · simp only [m', Function.update_apply]; split_ifs <;> omega
  · rcases Nat.lt_or_ge i (S + 1) with hi | hi
    · have := h.vertex_lt i h1 (by omega)
      have := hne i h1 (by omega)
      have := h.pos_vertex i h1 (by omega)
      simp only [m', Function.update_apply]; split_ifs <;> omega
    · simp only [m', Function.update_apply]; split_ifs <;> omega
  · have := h.pos_le w hw
    simp only [m', Function.update_apply]; split_ifs <;> omega
  · by_cases hwv : w = v
    · subst hwv
      simp only [m', Function.update_apply]; split_ifs <;> omega
    · have hP : m' (base + 2 * N + 1 + w) = mem (base + 2 * N + 1 + w) := by
        simp only [m', Function.update_apply]; split_ifs <;> omega
      rw [hP] at hw0 ⊢
      have := h.pos_le w hw
      have := h.vertex_pos w hw hw0
      simp only [m', Function.update_apply]; split_ifs <;> omega
  · rw [hent i (by omega) (by omega), hent (i / 2) (by omega) (by omega)]
    exact h.ordered i h1 (by omega)

/-- **Decrease-key**: lowering the key of a present handle `v < N` from `mem (base + v)` to `c`
produces `HeapShape` and `UpOrdered` at `pos[v]`. -/
theorem HeapInv.decrease (h : HeapInv N base S mem) {v c : ℕ} (hv : v < N)
    (_hp : mem (base + 2 * N + 1 + v) ≠ 0) (hle : c ≤ mem (base + v)) :
    let m' := Function.update mem (base + v) c
    HeapShape N base S m' ∧
      UpOrdered (heapEntry N base m') S (mem (base + 2 * N + 1 + v)) := by
  intro m'
  have hkS := h.pos_le v hv
  have hval : ∀ j, heapEntry N base m' j =
      if mem (base + N + j) = v then (v, c) else heapEntry N base mem j := by
    intro j
    have hin : m' (base + N + j) = mem (base + N + j) :=
      Function.update_of_ne (by omega) _ _
    by_cases he : mem (base + N + j) = v
    · simp only [heapEntry, hin, he, ↓reduceIte, m', Function.update_self]
    · have hne : base + mem (base + N + j) ≠ base + v := by omega
      simp only [heapEntry, hin, he, ↓reduceIte, m', Function.update_of_ne hne]
  have hle' : ∀ j, IndexedMinPQ.RawPrioLE (heapEntry N base m' j) (heapEntry N base mem j) := by
    intro j
    rw [hval]
    split_ifs with h1
    · simp only [heapEntry, h1]; exact entryLE_of_key_le hle
    · exact IndexedMinPQ.RawPrioLE.refl _
  have heq : ∀ j, 1 ≤ j → j ≤ S → j ≠ mem (base + 2 * N + 1 + v) →
      heapEntry N base m' j = heapEntry N base mem j := by
    intro j h1 h2 hj
    rw [hval]
    split_ifs with he
    · have := h.pos_vertex j h1 h2
      rw [he] at this; omega
    · rfl
  refine ⟨⟨h.size_le, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun w hw => ?_,
    fun w hw hw0 => ?_⟩, fun i h1 h2 => ⟨fun hi => ?_, fun hi h2k => ?_⟩⟩
  · dsimp only [m']; rw [Function.update_of_ne (by omega)]; exact h.vertex_lt i h1 h2
  · have := h.vertex_lt i h1 h2
    dsimp only [m']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact h.pos_vertex i h1 h2
  · dsimp only [m']; rw [Function.update_of_ne (by omega)]; exact h.pos_le w hw
  · dsimp only [m'] at hw0 ⊢
    rw [Function.update_of_ne (by omega)] at hw0 ⊢
    have := h.pos_le w hw
    rw [Function.update_of_ne (by omega)]; exact h.vertex_pos w hw hw0
  · rw [heq i (by omega) h2 hi]
    exact (hle' _).trans (h.ordered i h1 h2)
  · rw [heq i (by omega) h2 (by omega)]
    exact (hle' _).trans ((h.ordered _ h2k hkS).trans (hi ▸ h.ordered i h1 h2))

/-- **Root removal** (`2 ≤ S`): clearing the root's position and moving the last entry to `1`
produces `HeapShape` of size `S - 1` and `DownOrdered` at `1`. -/
theorem HeapInv.extract (h : HeapInv N base S mem) (hS : 2 ≤ S) :
    let m' := Function.update (Function.update
      (Function.update mem (base + 2 * N + 1 + mem (base + N + 1)) 0)
      (base + N + 1) (mem (base + N + S))) (base + 2 * N + 1 + mem (base + N + S)) 1
    HeapShape N base (S - 1) m' ∧ DownOrdered (heapEntry N base m') (S - 1) 1 ∧
      ∀ v < N, (m' (base + 2 * N + 1 + v) = 0 ↔
        mem (base + 2 * N + 1 + v) = 0 ∨ v = mem (base + N + 1)) := by
  intro m'
  have hSN := h.size_le
  have hU := h.vertex_lt 1 le_rfl (by omega)
  have hL := h.vertex_lt S (by omega) le_rfl
  have hPU := h.pos_vertex 1 le_rfl (by omega)
  have hPL := h.pos_vertex S (by omega) le_rfl
  have hUL : mem (base + N + 1) ≠ mem (base + N + S) := fun e => by
    rw [e, hPL] at hPU; omega
  have hmid : ∀ j, 2 ≤ j → j ≤ S - 1 → mem (base + N + j) ≠ mem (base + N + 1) ∧
      mem (base + N + j) ≠ mem (base + N + S) ∧ mem (base + N + j) < N ∧
      mem (base + 2 * N + 1 + mem (base + N + j)) = j := by
    intro j h1 h2
    have hj := h.pos_vertex j (by omega) (by omega)
    refine ⟨fun e => ?_, fun e => ?_, h.vertex_lt j (by omega) (by omega), hj⟩
    · rw [e, hPU] at hj; omega
    · rw [e, hPL] at hj; omega
  have hother : ∀ w < N, w ≠ mem (base + N + 1) → w ≠ mem (base + N + S) →
      mem (base + 2 * N + 1 + w) ≤ S - 1 ∧ mem (base + 2 * N + 1 + w) ≠ 1 := by
    intro w hw h1 h2
    have := h.pos_le w hw
    by_cases h0 : mem (base + 2 * N + 1 + w) = 0
    · omega
    have hv := h.vertex_pos w hw h0
    refine ⟨?_, fun e => h1 (by rw [e] at hv; exact hv.symm)⟩
    by_contra hc
    exact h2 (by rw [show mem (base + 2 * N + 1 + w) = S by omega] at hv; exact hv.symm)
  have hpos : ∀ w < N, m' (base + 2 * N + 1 + w) = if w = mem (base + N + S) then 1
      else if w = mem (base + N + 1) then 0 else mem (base + 2 * N + 1 + w) := by
    intro w hw
    simp only [m', Function.update_apply]; split_ifs <;> omega
  have hent : ∀ j, 2 ≤ j → j ≤ S - 1 → heapEntry N base m' j = heapEntry N base mem j := by
    intro j h1 h2
    have := hmid j h1 h2
    simp only [m', heapEntry, Function.update_apply]
    ext <;> (dsimp only; split_ifs <;> omega)
  refine ⟨⟨by omega, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun w hw => ?_,
    fun w hw hw0 => ?_⟩, fun i h1 h2 => ⟨fun _ => ?_, fun _ h => by omega⟩, fun w hw => ?_⟩
  · have := h.vertex_lt i h1 (by omega)
    simp only [m', Function.update_apply]; split_ifs <;> omega
  · rcases Nat.lt_or_ge i 2 with hi | hi
    · obtain rfl : i = 1 := by omega
      simp only [m', Function.update_apply]; split_ifs <;> omega
    · have := hmid i hi h2
      simp only [m', Function.update_apply]; split_ifs <;> omega
  · rw [hpos w hw]
    split_ifs with h1 h2
    · omega
    · omega
    · exact (hother w hw h2 h1).1
  · rw [hpos w hw] at hw0 ⊢
    split_ifs at hw0 ⊢ with h1 h2
    · simp only [m', Function.update_apply]; split_ifs <;> omega
    · exact absurd rfl hw0
    · have := hother w hw h2 h1
      have := h.vertex_pos w hw hw0
      simp only [m', Function.update_apply]; split_ifs <;> omega
  · rw [hent i h1 h2, hent (i / 2) (by omega) (by omega)]
    exact h.ordered i h1 (by omega)
  · rw [hpos w hw]
    split_ifs with h1 h2
    · subst h1
      refine iff_of_false id ?_
      rintro (h0 | h0)
      · omega
      · exact hUL h0.symm
    · omega
    · omega

/-- **Singleton root removal**: clearing the root's position on a 1-element heap leaves the empty
heap invariant. -/
theorem HeapInv.extract_one (h : HeapInv N base 1 mem) :
    HeapInv N base 0 (Function.update mem (base + 2 * N + 1 + mem (base + N + 1)) 0) := by
  have hz : ∀ w < N, Function.update mem (base + 2 * N + 1 + mem (base + N + 1)) 0
      (base + 2 * N + 1 + w) = 0 := by
    intro w hw
    rw [Function.update_apply]
    split_ifs with he
    · rfl
    · have := h.pos_le w hw
      by_contra h0
      have hv := h.vertex_pos w hw h0
      rw [show mem (base + 2 * N + 1 + w) = 1 by omega] at hv
      omega
  exact ⟨⟨Nat.zero_le _, fun _ h1 h2 => by omega, fun _ h1 h2 => by omega,
    fun w hw => (hz w hw).le, fun w hw hw0 => absurd (hz w hw) hw0⟩, fun _ h1 h2 => by omega⟩

end InvariantLemmas

end Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap
