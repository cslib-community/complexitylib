/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapProgram

/-!
# Dijkstra's algorithm with a binary heap: the heap

This file states the invariant of the binary min-heap of
`Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra` and proves how its operations change it. The heap
lives in a memory `mem` with three arrays past a base `Db`, for `N` vertices: the keys
`mem (Db + v)`, the heap entries `mem (Db + N + i)` for the positions `1 ≤ i ≤ sz`, and the
positions `mem (Db + 2 N + 1 + v)`, with `0` for a vertex not in the heap. The key of a position
is the key of the vertex there (`Cslib.Algorithms.WordRAM.Dijkstra.heapKey`).

The invariant (`Cslib.Algorithms.WordRAM.Dijkstra.HeapInv`) has a shape part
(`Cslib.Algorithms.WordRAM.Dijkstra.HeapShape`: the positions array is the inverse of the heap,
and vertices in the heap have nonzero keys) and an order part: the key of every position is at
least the key of its parent. A sift-up from position `k` repairs a heap ordered except between `k`
and its parent (`Cslib.Algorithms.WordRAM.Dijkstra.UpOrdered`), and a sift-down from `k` repairs a
heap ordered except between `k` and its children (`Cslib.Algorithms.WordRAM.Dijkstra.DownOrdered`).
Insertion and decrease-key leave the first kind of defect, and removal of the root the second.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.HeapShape`, `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv`: the
  heap invariant.
* `Cslib.Algorithms.WordRAM.Dijkstra.UpOrdered`, `Cslib.Algorithms.WordRAM.Dijkstra.DownOrdered`:
  heap order with one defect.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.push`,
  `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.decrease`,
  `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.extract`: insertion, decrease-key and removal of the
  root leave a heap with one defect.
* `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv.root_le`: the root has the least key.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM HeapReg

/-- The key of heap position `i`: the key of the vertex at position `i`. -/
def heapKey (N Db : ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ := mem (Db + mem (Db + N + i))

/-- **The shape of the heap.** The positions `1, …, sz` hold vertices below `N`, the positions
array is the inverse of the heap and is `0` off the heap, and vertices in the heap have nonzero
keys. -/
structure HeapShape (N Db sz : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- The heap holds at most `N` entries. -/
  size_le : sz ≤ N
  /-- The heap holds vertices. -/
  vertex_lt : ∀ i, 1 ≤ i → i ≤ sz → mem (Db + N + i) < N
  /-- The position of the vertex at position `i` is `i`. -/
  pos_vertex : ∀ i, 1 ≤ i → i ≤ sz → mem (Db + 2 * N + 1 + mem (Db + N + i)) = i
  /-- Positions are at most the size. -/
  pos_le : ∀ v < N, mem (Db + 2 * N + 1 + v) ≤ sz
  /-- A vertex with a nonzero position is at that position. -/
  vertex_pos : ∀ v < N, mem (Db + 2 * N + 1 + v) ≠ 0 →
    mem (Db + N + mem (Db + 2 * N + 1 + v)) = v
  /-- Vertices in the heap have nonzero keys. -/
  key_ne : ∀ v < N, mem (Db + 2 * N + 1 + v) ≠ 0 → mem (Db + v) ≠ 0

/-- **Heap order**: the key of every position `2 ≤ i ≤ sz` is at least that of its parent. -/
def Ordered (f : ℕ → ℕ) (sz : ℕ) : Prop := ∀ i, 2 ≤ i → i ≤ sz → f (i / 2) ≤ f i

/-- Heap order except between position `k` and its parent, where the parent of `k` is at most
the children of `k`: the state of a sift-up at `k`. -/
def UpOrdered (f : ℕ → ℕ) (sz k : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ sz → (i ≠ k → f (i / 2) ≤ f i) ∧ (i / 2 = k → 2 ≤ k → f (k / 2) ≤ f i)

/-- Heap order except between position `k` and its children, where the parent of `k` is at most
the children of `k`: the state of a sift-down at `k`. -/
def DownOrdered (f : ℕ → ℕ) (sz k : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ sz → (i / 2 ≠ k → f (i / 2) ≤ f i) ∧ (i / 2 = k → 2 ≤ k → f (k / 2) ≤ f i)

/-- **The heap invariant**: the shape and the heap order. -/
structure HeapInv (N Db sz : ℕ) (mem : ℕ → ℕ) : Prop extends HeapShape N Db sz mem where
  /-- Heap order. -/
  ordered : Ordered (heapKey N Db mem) sz

variable {N Db S : ℕ} {mem : ℕ → ℕ}

/-- A heap that misses a vertex has room for it. -/
theorem HeapShape.size_lt (h : HeapShape N Db S mem) {v : ℕ} (hv : v < N)
    (hp : mem (Db + 2 * N + 1 + v) = 0) : S < N := by
  have hcard := Finset.card_le_card_of_injOn (fun i => mem (Db + N + i))
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

/-- **The root has the least key** among the vertices in the heap. -/
theorem HeapInv.root_le (h : HeapInv N Db S mem) {v : ℕ} (hv : v < N)
    (hp : mem (Db + 2 * N + 1 + v) ≠ 0) : mem (Db + mem (Db + N + 1)) ≤ mem (Db + v) := by
  have key : ∀ i, 1 ≤ i → i ≤ S → heapKey N Db mem 1 ≤ heapKey N Db mem i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro h1 h2
      rcases Nat.lt_or_ge i 2 with hi | hi
      · obtain rfl : i = 1 := by omega
        exact le_rfl
      · exact (ih (i / 2) (by omega) (by omega) (by omega)).trans (h.ordered i hi h2)
  have := key _ (Nat.one_le_iff_ne_zero.2 hp) (h.pos_le v hv)
  simpa only [heapKey, h.vertex_pos v hv hp] using this

/-- **Insertion.** Giving a vertex `v` out of the heap the nonzero key `c` and appending it at
position `S + 1` leaves a heap ordered except at `S + 1`, which holds `v`. -/
theorem HeapInv.push (h : HeapInv N Db S mem) {v c : ℕ} (hv : v < N)
    (hp : mem (Db + 2 * N + 1 + v) = 0) (hc : c ≠ 0) :
    HeapShape N Db (S + 1) (Function.update (Function.update (Function.update mem (Db + v) c)
      (Db + N + (S + 1)) v) (Db + 2 * N + 1 + v) (S + 1)) ∧
    UpOrdered (heapKey N Db (Function.update (Function.update (Function.update mem (Db + v) c)
      (Db + N + (S + 1)) v) (Db + 2 * N + 1 + v) (S + 1))) (S + 1) (S + 1) := by
  have hSN := h.size_lt hv hp
  have hne : ∀ i, 1 ≤ i → i ≤ S → mem (Db + N + i) ≠ v := fun i h1 h2 he => by
    have := h.pos_vertex i h1 h2
    rw [he, hp] at this
    omega
  set m' := Function.update (Function.update (Function.update mem (Db + v) c)
    (Db + N + (S + 1)) v) (Db + 2 * N + 1 + v) (S + 1) with hm'
  have hkey : ∀ i, 1 ≤ i → i ≤ S → heapKey N Db m' i = heapKey N Db mem i := by
    intro i h1 h2
    have := hne i h1 h2
    have := h.vertex_lt i h1 h2
    simp only [hm', heapKey, Function.update_apply]
    split_ifs <;> omega
  refine ⟨⟨by omega, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun w hw => ?_, fun w hw hw0 => ?_,
    fun w hw hw0 => ?_⟩, fun i h1 h2 => ⟨fun hi => ?_, fun hi _ => by omega⟩⟩
  · rcases Nat.lt_or_ge i (S + 1) with hi | hi
    · have := h.vertex_lt i h1 (by omega)
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
    · simp only [hm', Function.update_apply]
      split_ifs <;> omega
  · rcases Nat.lt_or_ge i (S + 1) with hi | hi
    · have := h.vertex_lt i h1 (by omega)
      have := hne i h1 (by omega)
      have := h.pos_vertex i h1 (by omega)
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
    · simp only [hm', Function.update_apply]
      split_ifs <;> omega
  · have := h.pos_le w hw
    simp only [hm', Function.update_apply]
    split_ifs <;> omega
  · by_cases hwv : w = v
    · subst hwv
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
    · have hP : m' (Db + 2 * N + 1 + w) = mem (Db + 2 * N + 1 + w) := by
        simp only [hm', Function.update_apply]
        split_ifs <;> omega
      rw [hP] at hw0 ⊢
      have := h.pos_le w hw
      have := h.vertex_pos w hw hw0
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
  · by_cases hwv : w = v
    · subst hwv
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
    · have hP : m' (Db + 2 * N + 1 + w) = mem (Db + 2 * N + 1 + w) := by
        simp only [hm', Function.update_apply]
        split_ifs <;> omega
      rw [hP] at hw0
      have := h.key_ne w hw hw0
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
  · rw [hkey i (by omega) (by omega), hkey (i / 2) (by omega) (by omega)]
    exact h.ordered i h1 (by omega)

/-- **Decrease-key.** Lowering the key of a vertex `v` in the heap to the nonzero `c` leaves a
heap ordered except at the position of `v`. -/
theorem HeapInv.decrease (h : HeapInv N Db S mem) {v c : ℕ} (hv : v < N)
    (hp : mem (Db + 2 * N + 1 + v) ≠ 0) (hc : c ≠ 0) (hle : c ≤ mem (Db + v)) :
    HeapShape N Db S (Function.update mem (Db + v) c) ∧
    UpOrdered (heapKey N Db (Function.update mem (Db + v) c)) S (mem (Db + 2 * N + 1 + v)) := by
  have hk1 : 1 ≤ mem (Db + 2 * N + 1 + v) := Nat.one_le_iff_ne_zero.2 hp
  have hkS := h.pos_le v hv
  have hHk := h.vertex_pos v hv hp
  have hval : ∀ j, heapKey N Db (Function.update mem (Db + v) c) j =
      if mem (Db + N + j) = v then c else heapKey N Db mem j := by
    intro j
    have hin : Function.update mem (Db + v) c (Db + N + j) = mem (Db + N + j) :=
      Function.update_of_ne (by omega) _ _
    simp only [heapKey, hin, Function.update_apply]
    split_ifs <;> first | rfl | omega
  have hle' : ∀ j, heapKey N Db (Function.update mem (Db + v) c) j ≤ heapKey N Db mem j := by
    intro j
    rw [hval]
    split_ifs with h1
    · simp only [heapKey, h1]; exact hle
    · exact le_rfl
  have heq : ∀ j, 1 ≤ j → j ≤ S → j ≠ mem (Db + 2 * N + 1 + v) →
      heapKey N Db (Function.update mem (Db + v) c) j = heapKey N Db mem j := by
    intro j h1 h2 hj
    rw [hval]
    split_ifs with he
    · have := h.pos_vertex j h1 h2
      rw [he] at this
      omega
    · rfl
  refine ⟨⟨h.size_le, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun w hw => ?_, fun w hw hw0 => ?_,
    fun w hw hw0 => ?_⟩, fun i h1 h2 => ⟨fun hi => ?_, fun hi h2k => ?_⟩⟩
  · rw [Function.update_of_ne (by omega)]
    exact h.vertex_lt i h1 h2
  · have := h.vertex_lt i h1 h2
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact h.pos_vertex i h1 h2
  · rw [Function.update_of_ne (by omega)]
    exact h.pos_le w hw
  · rw [Function.update_of_ne (by omega)] at hw0 ⊢
    have := h.pos_le w hw
    rw [Function.update_of_ne (by omega)]
    exact h.vertex_pos w hw hw0
  · rw [Function.update_of_ne (by omega)] at hw0
    rw [Function.update_apply]
    split_ifs
    · exact hc
    · exact h.key_ne w hw hw0
  · rw [heq i (by omega) h2 hi]
    exact (hle' _).trans (h.ordered i h1 h2)
  · rw [heq i (by omega) h2 (by omega)]
    exact (hle' _).trans ((h.ordered _ h2k hkS).trans (hi ▸ h.ordered i h1 h2))

/-- **Removal of the root**, from a heap of at least two entries: clearing the position of the
root `U` and moving the last entry `L` to the root leaves a heap of `S - 1` entries ordered except
between the root and its children, which holds exactly the vertices of the old heap but `U`. -/
theorem HeapInv.extract (h : HeapInv N Db S mem) (hS : 2 ≤ S) :
    HeapShape N Db (S - 1) (Function.update (Function.update
      (Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0) (Db + N + 1)
        (mem (Db + N + S))) (Db + 2 * N + 1 + mem (Db + N + S)) 1) ∧
    DownOrdered (heapKey N Db (Function.update (Function.update
      (Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0) (Db + N + 1)
        (mem (Db + N + S))) (Db + 2 * N + 1 + mem (Db + N + S)) 1)) (S - 1) 1 ∧
    ∀ v < N, (Function.update (Function.update
      (Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0) (Db + N + 1)
        (mem (Db + N + S))) (Db + 2 * N + 1 + mem (Db + N + S)) 1 (Db + 2 * N + 1 + v) = 0 ↔
      mem (Db + 2 * N + 1 + v) = 0 ∨ v = mem (Db + N + 1)) := by
  have hSN := h.size_le
  have hU := h.vertex_lt 1 le_rfl (by omega)
  have hL := h.vertex_lt S (by omega) le_rfl
  have hPU := h.pos_vertex 1 le_rfl (by omega)
  have hPL := h.pos_vertex S (by omega) le_rfl
  have hUL : mem (Db + N + 1) ≠ mem (Db + N + S) := fun e => by
    rw [e, hPL] at hPU
    omega
  -- The middle positions `2, …, S - 1` hold neither the root nor the last vertex.
  have hmid : ∀ j, 2 ≤ j → j ≤ S - 1 → mem (Db + N + j) ≠ mem (Db + N + 1) ∧
      mem (Db + N + j) ≠ mem (Db + N + S) ∧ mem (Db + N + j) < N ∧
      mem (Db + 2 * N + 1 + mem (Db + N + j)) = j := by
    intro j h1 h2
    have hj := h.pos_vertex j (by omega) (by omega)
    refine ⟨fun e => ?_, fun e => ?_, h.vertex_lt j (by omega) (by omega), hj⟩
    · rw [e, hPU] at hj
      omega
    · rw [e, hPL] at hj
      omega
  -- Any other vertex has its position among the middle positions or is out of the heap.
  have hother : ∀ w < N, w ≠ mem (Db + N + 1) → w ≠ mem (Db + N + S) →
      mem (Db + 2 * N + 1 + w) ≤ S - 1 ∧ mem (Db + 2 * N + 1 + w) ≠ 1 := by
    intro w hw h1 h2
    have := h.pos_le w hw
    by_cases h0 : mem (Db + 2 * N + 1 + w) = 0
    · omega
    have hv := h.vertex_pos w hw h0
    refine ⟨?_, fun e => h1 (by rw [e] at hv; exact hv.symm)⟩
    by_contra hc
    exact h2 (by rw [show mem (Db + 2 * N + 1 + w) = S by omega] at hv; exact hv.symm)
  set m' := Function.update (Function.update
    (Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0) (Db + N + 1)
      (mem (Db + N + S))) (Db + 2 * N + 1 + mem (Db + N + S)) 1 with hm'
  -- The position of a vertex in the new heap.
  have hpos : ∀ w < N, m' (Db + 2 * N + 1 + w) = if w = mem (Db + N + S) then 1
      else if w = mem (Db + N + 1) then 0 else mem (Db + 2 * N + 1 + w) := by
    intro w hw
    simp only [hm', Function.update_apply]
    split_ifs <;> omega
  have hkey : ∀ j, 2 ≤ j → j ≤ S - 1 → heapKey N Db m' j = heapKey N Db mem j := by
    intro j h1 h2
    have := hmid j h1 h2
    simp only [hm', heapKey, Function.update_apply]
    split_ifs <;> omega
  refine ⟨⟨by omega, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun w hw => ?_, fun w hw hw0 => ?_,
    fun w hw hw0 => ?_⟩, fun i h1 h2 => ⟨fun hi => ?_, fun _ h => by omega⟩, fun w hw => ?_⟩
  · have := h.vertex_lt i h1 (by omega)
    simp only [hm', Function.update_apply]
    split_ifs <;> omega
  · rcases Nat.lt_or_ge i 2 with hi | hi
    · obtain rfl : i = 1 := by omega
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
    · have := hmid i hi h2
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
  · rw [hpos w hw]
    split_ifs with h1 h2
    · omega
    · omega
    · exact (hother w hw h2 h1).1
  · rw [hpos w hw] at hw0 ⊢
    split_ifs at hw0 ⊢ with h1 h2
    · simp only [hm', Function.update_apply]
      split_ifs <;> omega
    · exact absurd rfl hw0
    · have := hother w hw h2 h1
      have := h.vertex_pos w hw hw0
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
  · rw [hpos w hw] at hw0
    have hk : m' (Db + w) = mem (Db + w) := by
      simp only [hm', Function.update_apply]
      split_ifs <;> omega
    rw [hk]
    split_ifs at hw0 with h1 h2
    · subst h1
      exact h.key_ne _ hw (by omega)
    · exact absurd rfl hw0
    · exact h.key_ne w hw hw0
  · rw [hkey i h1 h2, hkey (i / 2) (by omega) (by omega)]
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

/-- **Removal of the only entry**: clearing the position of the root of a heap of one entry
leaves the empty heap. -/
theorem HeapInv.extract_one (h : HeapInv N Db 1 mem) :
    HeapInv N Db 0 (Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0) := by
  have hU := h.vertex_lt 1 le_rfl le_rfl
  have hz : ∀ w < N, Function.update mem (Db + 2 * N + 1 + mem (Db + N + 1)) 0
      (Db + 2 * N + 1 + w) = 0 := by
    intro w hw
    rw [Function.update_apply]
    split_ifs with he
    · rfl
    · have := h.pos_le w hw
      by_contra h0
      have hv := h.vertex_pos w hw h0
      rw [show mem (Db + 2 * N + 1 + w) = 1 by omega] at hv
      omega
  exact ⟨⟨Nat.zero_le _, fun i h1 h2 => by omega, fun i h1 h2 => by omega,
    fun w hw => (hz w hw).le, fun w hw hw0 => absurd (hz w hw) hw0,
    fun w hw hw0 => absurd (hz w hw) hw0⟩, fun i h1 h2 => by omega⟩

end Cslib.Algorithms.WordRAM.Dijkstra

end
