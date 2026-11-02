/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.WordRAM.BinaryHeap.Model

/-!
# Indexed binary min-heap: the order lemmas of sift-up and sift-down

These are the machine-free steps of sift-up and sift-down on the indexed binary heap of
`Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.Model`: swapping two heap positions keeps the
heap shape (`HeapShape.swap`), and a swap with the parent or with the child of highest priority
moves a single order defect one level (`UpOrdered.swap`, `DownOrdered.swap`) until it disappears
(`UpOrdered.ordered`, `DownOrdered.ordered`).

They are the private order lemmas of
`Complexity/DataStructure/PriorityQueue/WordRAM/BinaryHeap/Sift.lean`, copied unchanged apart from
docstrings so that implementations over the memory oracle can use them without importing word-RAM
code. They extend the namespace of `BinaryHeap.Model`, whose definitions they are about. The
private originals go when the word-RAM heap is migrated (#2205).

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.swapMem`: memory after swapping two heap
  positions.
* `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.minChild`: the child of highest priority.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.HeapShape.swap`: a swap keeps the shape.
* `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.UpOrdered.swap`,
  `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.UpOrdered.ordered`,
  `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.Ordered.upOrdered_one`: sift-up.
* `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.DownOrdered.swap`,
  `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.DownOrdered.ordered`,
  `Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap.minChild_spec`: sift-down.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue

section Order

variable {f g : ℕ → ℕ × ℕ} {S a c : ℕ}

/-- A heap with one upward defect at `a` is ordered once `a` is ordered with its parent. -/
theorem UpOrdered.ordered (h : UpOrdered f S a)
    (hle : 2 ≤ a → a ≤ S → IndexedMinPQ.RawPrioLE (f (a / 2)) (f a)) : Ordered f S := by
  intro i hi hiS
  by_cases hia : i = a
  · subst hia; exact hle hi hiS
  · exact (h i hi hiS).1 hia

/-- An ordered heap has at most an upward defect at the root. -/
theorem Ordered.upOrdered_one (h : Ordered f S) : UpOrdered f S 1 :=
  fun i hi hiS => ⟨fun _ => h i hi hiS, fun _ h2 => absurd h2 (by omega)⟩

/-- **One step of sift-up.** Swapping an entry `a` with its parent when it has higher priority
moves the upward defect to the parent. -/
theorem UpOrdered.swap (h : UpOrdered f S a) (ha : 2 ≤ a) (haS : a ≤ S)
    (hlt : IndexedMinPQ.RawPrioLT (f a) (f (a / 2))) (hga : g a = f (a / 2)) (hgp : g (a / 2) = f a)
    (hgo : ∀ i, 1 ≤ i → i ≤ S → i ≠ a → i ≠ a / 2 → g i = f i) :
    UpOrdered g S (a / 2) := by
  intro i hi hiS
  obtain ⟨h₁, h₂⟩ := h i hi hiS
  constructor
  · intro hne
    rcases eq_or_ne i a with rfl | hia
    · rw [hga, hgp]; exact hlt.le
    rw [hgo i (by omega) hiS hia hne]
    rcases eq_or_ne (i / 2) a with hia2 | hia2
    · rw [hia2, hga]; exact h₂ hia2 ha
    rcases eq_or_ne (i / 2) (a / 2) with hip | hip
    · have hp := h₁ hia
      rw [hip] at hp
      rw [hip, hgp]
      exact hlt.le.trans hp
    · rw [hgo (i / 2) (by omega) (by omega) hia2 hip]
      exact h₁ hia
  · intro hip hp2
    have hpa := (h (a / 2) hp2 (by omega)).1 (by omega)
    rw [hgo (a / 2 / 2) (by omega) (by omega) (by omega) (by omega)]
    rcases eq_or_ne i a with rfl | hia
    · rw [hga]; exact hpa
    · have hp := h₁ hia
      rw [hip] at hp
      rw [hgo i (by omega) hiS hia (by omega)]
      exact hpa.trans hp

/-- A heap with one downward defect at `a` is ordered once `a` is ordered with its children. -/
theorem DownOrdered.ordered (h : DownOrdered f S a)
    (hle : ∀ i, 2 ≤ i → i ≤ S → i / 2 = a → IndexedMinPQ.RawPrioLE (f a) (f i)) : Ordered f S := by
  intro i hi hiS
  by_cases hia : i / 2 = a
  · rw [hia]; exact hle i hi hiS hia
  · exact (h i hi hiS).1 hia

/-- **One step of sift-down.** Swapping an entry `a` with its child `c` of highest priority,
when `c` has higher priority than `a`, moves the downward defect to `c`. -/
theorem DownOrdered.swap (h : DownOrdered f S a) (hc : c / 2 = a) (hcS : c ≤ S)
    (hmin : ∀ i, 2 ≤ i → i ≤ S → i / 2 = a → IndexedMinPQ.RawPrioLE (f c) (f i))
    (hlt : IndexedMinPQ.RawPrioLT (f c) (f a)) (hga : g a = f c) (hgc : g c = f a)
    (hgo : ∀ i, 1 ≤ i → i ≤ S → i ≠ a → i ≠ c → g i = f i) :
    DownOrdered g S c := by
  intro i hi hiS
  obtain ⟨h₁, -⟩ := h i hi hiS
  constructor
  · intro hic
    rcases eq_or_ne i c with rfl | hic'
    · rw [hc, hga, hgc]; exact hlt.le
    rcases eq_or_ne (i / 2) a with hia | hia
    · rw [hia, hga, hgo i (by omega) hiS (by omega) hic']
      exact hmin i hi hiS hia
    rcases eq_or_ne i a with rfl | hia'
    · rw [hga, hgo (i / 2) (by omega) (by omega) (by omega) hic]
      exact (h c (by omega) hcS).2 hc hi
    · rw [hgo i (by omega) hiS hia' hic', hgo (i / 2) (by omega) (by omega) hia hic]
      exact h₁ hia
  · intro hic _
    have hp := h₁ (by omega)
    rw [hic] at hp
    rw [hc, hga, hgo i (by omega) hiS (by omega) (by omega)]
    exact hp

end Order

section Swap

variable {N base S : ℕ}

/-- Memory after swapping heap positions `a` and `b`, which hold the handles `va` and `vb`: the
heap array exchanges the two handles and the position array records their new positions. -/
def swapMem (N base : ℕ) (mem : ℕ → ℕ) (a b va vb : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update mem (base + N + a) vb)
    (base + N + b) va) (base + 2 * N + 1 + vb) a) (base + 2 * N + 1 + va) b

/-- **Swapping two heap positions** keeps the heap shape, exchanges the two entries, leaves the
other entries, the presence of every handle, and every cell outside the heap and position arrays
unchanged. -/
theorem HeapShape.swap {mem : ℕ → ℕ} {a b : ℕ} (h : HeapShape N base S mem)
    (ha : 1 ≤ a) (haS : a ≤ S) (hb : 1 ≤ b) (hbS : b ≤ S) (hab : a ≠ b) :
    let m' := swapMem N base mem a b (mem (base + N + a)) (mem (base + N + b))
    HeapShape N base S m' ∧ heapEntry N base m' a = heapEntry N base mem b ∧
      heapEntry N base m' b = heapEntry N base mem a ∧
      (∀ i, 1 ≤ i → i ≤ S → i ≠ a → i ≠ b → heapEntry N base m' i = heapEntry N base mem i) ∧
      (∀ v < N, m' (base + 2 * N + 1 + v) = 0 ↔ mem (base + 2 * N + 1 + v) = 0) ∧
      (∀ c, c ≤ base + N ∨ base + 3 * N < c → m' c = mem c) := by
  intro m'
  have hSN := h.size_le
  have hva : mem (base + N + a) < N := h.vertex_lt a ha haS
  have hvb : mem (base + N + b) < N := h.vertex_lt b hb hbS
  have hpa := h.pos_vertex a ha haS
  have hpb := h.pos_vertex b hb hbS
  have hne : mem (base + N + a) ≠ mem (base + N + b) := fun he => hab (by rw [← hpa, ← hpb, he])
  have hH : ∀ i, 1 ≤ i → i ≤ S → m' (base + N + i) = if i = b then mem (base + N + a)
      else if i = a then mem (base + N + b) else mem (base + N + i) := by
    intro i hi hiS
    simp only [m', swapMem, Function.update_apply]; split_ifs <;> omega
  have hP : ∀ v < N, m' (base + 2 * N + 1 + v) = if v = mem (base + N + a) then b
      else if v = mem (base + N + b) then a else mem (base + 2 * N + 1 + v) := by
    intro v hv
    simp only [m', swapMem, Function.update_apply]; split_ifs <;> omega
  have hD : ∀ c, c ≤ base + N ∨ base + 3 * N < c → m' c = mem c := by
    intro c hc
    simp only [m', swapMem, Function.update_apply]; split_ifs <;> omega
  have hK : ∀ v < N, m' (base + v) = mem (base + v) := fun _ hv => hD _ (Or.inl (by omega))
  refine ⟨⟨hSN, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hD⟩
  · intro i hi hiS
    rw [hH i hi hiS]; split_ifs; exacts [hva, hvb, h.vertex_lt i hi hiS]
  · intro i hi hiS
    rw [hH i hi hiS]
    split_ifs with h1 h2
    · rw [hP _ hva, ite_eq_left rfl, h1]
    · rw [hP _ hvb, ite_eq_right hne.symm, ite_eq_left rfl, h2]
    · have hpi := h.pos_vertex i hi hiS
      have h1' : mem (base + N + i) ≠ mem (base + N + a) := fun he => h2 (by rw [← hpi, he, hpa])
      have h2' : mem (base + N + i) ≠ mem (base + N + b) := fun he => h1 (by rw [← hpi, he, hpb])
      rw [hP _ (h.vertex_lt i hi hiS), ite_eq_right h1', ite_eq_right h2', hpi]
  · intro v hv
    rw [hP v hv]; split_ifs; exacts [hbS, haS, h.pos_le v hv]
  · intro v hv hv0
    rw [hP v hv] at hv0 ⊢
    split_ifs at hv0 ⊢ with h1 h2
    · rw [hH b hb hbS, ite_eq_left rfl, h1]
    · rw [hH a ha haS, ite_eq_right hab, ite_eq_left rfl, h2]
    · have hvp := h.vertex_pos v hv hv0
      have hle := h.pos_le v hv
      have h1' : mem (base + 2 * N + 1 + v) ≠ b := fun he => h2 (by rw [← hvp, he])
      have h2' : mem (base + 2 * N + 1 + v) ≠ a := fun he => h1 (by rw [← hvp, he])
      rw [hH _ (by omega) hle, ite_eq_right h1', ite_eq_right h2', hvp]
  · simp only [heapEntry]
    rw [hH a ha haS, ite_eq_right hab, ite_eq_left rfl, hK _ hvb]
  · simp only [heapEntry]
    rw [hH b hb hbS, ite_eq_left rfl, hK _ hva]
  · intro i hi hiS hia hib
    simp only [heapEntry]
    rw [hH i hi hiS, ite_eq_right hib, ite_eq_right hia, hK _ (h.vertex_lt i hi hiS)]
  · intro v hv
    rw [hP v hv]
    split_ifs with h1 h2
    · subst h1; rw [hpa]; omega
    · subst h2; rw [hpb]; omega
    · rfl

/-- The child of `a` with the highest priority in a heap of size `S`: the right child when it
exists and has strictly higher priority than the left child, and the left child otherwise. -/
def minChild (f : ℕ → ℕ × ℕ) (S a : ℕ) : ℕ :=
  if 2 * a + 1 ≤ S ∧ IndexedMinPQ.RawPrioLT (f (2 * a + 1)) (f (2 * a)) then 2 * a + 1 else 2 * a

/-- `minChild` is a child of `a` within the heap, of priority at least that of every child. -/
theorem minChild_spec {f : ℕ → ℕ × ℕ} {a : ℕ} (ha : 2 * a ≤ S) :
    (minChild f S a = 2 * a ∨ minChild f S a = 2 * a + 1) ∧ minChild f S a ≤ S ∧
      ∀ i, i ≤ S → i / 2 = a → IndexedMinPQ.RawPrioLE (f (minChild f S a)) (f i) := by
  unfold minChild
  split_ifs with h
  · refine ⟨Or.inr rfl, h.1, fun i hiS hia => ?_⟩
    rcases (by omega : i = 2 * a ∨ i = 2 * a + 1) with rfl | rfl
    · exact h.2.le
    · exact IndexedMinPQ.RawPrioLE.refl _
  · refine ⟨Or.inl rfl, ha, fun i hiS hia => ?_⟩
    rcases (by omega : i = 2 * a ∨ i = 2 * a + 1) with rfl | rfl
    · exact IndexedMinPQ.RawPrioLE.refl _
    · exact IndexedMinPQ.not_rawPrioLT_iff_rawPrioLE.mp fun hlt => h ⟨hiS, hlt⟩

end Swap

end Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap
