/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.BinaryHeap.Program

/-!
# Indexed Binary Min-Heap: Sift-Up, Sift-Down, and Root Extraction Proofs

This file proves functional correctness, framing, and `O(⌊log₂ n⌋ + 1)` exact-basis instruction
bounds for `siftUp`, `siftDown`, and `doExtractNonEmpty` under the lexicographic priority order
`IndexedMinPQ.PrioLE`.

## Main results

* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.siftUp_spec`: upward restoration from index `K`
  in at most `28 * ⌊log₂ K⌋ + 2` instructions.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.siftDown_spec`: downward restoration at heap
  size `S` in at most `46 * ⌊log₂ (S + 1)⌋ + 4` instructions.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.doExtractNonEmpty_spec`: non-empty root
  extraction at heap size `S ≥ 1` in at most `46 * ⌊log₂ S⌋ + 20` instructions.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Reg

section Order

variable {f g : ℕ → ℕ × ℕ} {S a c : ℕ}

private theorem UpOrdered.ordered (h : UpOrdered f S a)
    (hle : 2 ≤ a → a ≤ S → IndexedMinPQ.RawPrioLE (f (a / 2)) (f a)) : Ordered f S := by
  intro i hi hiS
  by_cases hia : i = a
  · subst hia; exact hle hi hiS
  · exact (h i hi hiS).1 hia

private theorem Ordered.upOrdered_one (h : Ordered f S) : UpOrdered f S 1 :=
  fun i hi hiS => ⟨fun _ => h i hi hiS, fun _ h2 => absurd h2 (by omega)⟩

private theorem UpOrdered.swap (h : UpOrdered f S a) (ha : 2 ≤ a) (haS : a ≤ S)
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

private theorem DownOrdered.ordered (h : DownOrdered f S a)
    (hle : ∀ i, 2 ≤ i → i ≤ S → i / 2 = a → IndexedMinPQ.RawPrioLE (f a) (f i)) : Ordered f S := by
  intro i hi hiS
  by_cases hia : i / 2 = a
  · rw [hia]; exact hle i hi hiS hia
  · exact (h i hi hiS).1 hia

private theorem DownOrdered.swap (h : DownOrdered f S a) (hc : c / 2 = a) (hcS : c ≤ S)
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

section SwapAndCompare

variable {N base S w : ℕ}

private def swapMem (N base : ℕ) (mem : ℕ → ℕ) (a b va vb : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update mem (base + N + a) vb)
    (base + N + b) va) (base + 2 * N + 1 + vb) a) (base + 2 * N + 1 + va) b

private theorem HeapShape.swap {mem : ℕ → ℕ} {a b : ℕ} (h : HeapShape N base S mem)
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

private theorem cmpEntries_spec (vA dA vB dB : Fin rBin) {y : Data rBin}
    (hzero : y.regs zero = 0) (hone : y.regs one = 1) :
    ExecWithin w (cmpEntries vA dA vB dB) y
      (y.set t (if IndexedMinPQ.RawPrioLT (y.regs vA, y.regs dA) (y.regs vB, y.regs dB)
        then 1 else 0)) 6 := by
  by_cases h1 : y.regs dA < y.regs dB
  · have hp : IndexedMinPQ.RawPrioLT (y.regs vA, y.regs dA) (y.regs vB, y.regs dB) := Or.inl h1
    simp only [hp, ↓reduceIte]
    ram_exact_eval [cmpEntries, hzero, hone, h1]
  · by_cases h2 : y.regs dA = y.regs dB
    · by_cases h3 : y.regs vA < y.regs vB
      · have hp : IndexedMinPQ.RawPrioLT (y.regs vA, y.regs dA) (y.regs vB, y.regs dB) :=
          Or.inr ⟨h2, h3⟩
        simp only [hp, ↓reduceIte]
        ram_exact_eval [cmpEntries, hzero, hone, h2, h3, lt_irrefl]
      · have hp : ¬IndexedMinPQ.RawPrioLT (y.regs vA, y.regs dA) (y.regs vB, y.regs dB) := by
          dsimp only [IndexedMinPQ.RawPrioLT]; omega
        simp only [hp, ↓reduceIte]
        ram_exact_eval [cmpEntries, hzero, hone, h2, h3, lt_irrefl]
    · have hp : ¬IndexedMinPQ.RawPrioLT (y.regs vA, y.regs dA) (y.regs vB, y.regs dB) := by
        dsimp only [IndexedMinPQ.RawPrioLT]; omega
      simp only [hp, ↓reduceIte]
      ram_exact_eval [cmpEntries, hzero, hone, h1, h2]

private theorem cmpKP_spec {y : Data rBin} (hzero : y.regs zero = 0) (hone : y.regs one = 1) :
    ExecWithin w cmpKP y
      (y.set t (if IndexedMinPQ.RawPrioLT (y.regs vk, y.regs dk) (y.regs vp, y.regs dp)
        then 1 else 0)) 6 :=
  cmpEntries_spec vk dk vp dp hzero hone

private theorem cmpPK_spec {y : Data rBin} (hzero : y.regs zero = 0) (hone : y.regs one = 1) :
    ExecWithin w cmpPK y
      (y.set t (if IndexedMinPQ.RawPrioLT (y.regs vp, y.regs dp) (y.regs vk, y.regs dk)
        then 1 else 0)) 6 :=
  cmpEntries_spec vp dp vk dk hzero hone

end SwapAndCompare

/-! ### Sift-up -/

section SiftUp

variable {N base S w : ℕ}

private def upLoad : Code .exact rBin := ram_exact[
  p ← k >>> one;
  t ← hb + k; vk ← *t; t ← baseReg + vk; dk ← *t;
  t ← hb + p; vp ← *t; t ← baseReg + vp; dp ← *t ]

private def upSwap : Code .exact rBin := ram_exact[ ⟪swapCode⟫; k ← p ]

private theorem siftUpBody_eq : siftUpBody = appendCode upLoad
    (.seq cmpKP (.branch (.lt zero t) upSwap ram_exact[ k ← one ])) := rfl

private theorem shiftRight_one (K : ℕ) : K >>> 1 = K / 2 := by
  rw [Nat.shiftRight_eq_div_pow]

private theorem siftUpBody_spec {K : ℕ} {y : Data rBin}
    (hzero : y.regs zero = 0) (hone : y.regs one = 1)
    (hbase : y.regs baseReg = base) (hhb : y.regs hb = base + N)
    (hpb : y.regs pb = base + 2 * N + 1) (hk : y.regs k = K)
    (hK : 2 ≤ K) (hKS : K ≤ S) (hfit : Fits w (base + space N))
    (hshape : HeapShape N base S y.mem) :
    ∃ z, ExecWithin w siftUpBody y z 26 ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t], z.regs i = y.regs i) ∧
      (IndexedMinPQ.RawPrioLT (heapEntry N base y.mem K) (heapEntry N base y.mem (K / 2)) ∧
        z.regs k = K / 2 ∧
        z.mem = swapMem N base y.mem K (K / 2) (y.mem (base + N + K))
          (y.mem (base + N + K / 2)) ∨
       ¬IndexedMinPQ.RawPrioLT (heapEntry N base y.mem K) (heapEntry N base y.mem (K / 2)) ∧
        z.regs k = 1 ∧ z.mem = y.mem) := by
  have hSN := hshape.size_le
  have hsp : space N = 3 * N + 1 := rfl
  obtain ⟨VK, hvk⟩ : ∃ v, y.mem (base + N + K) = v := ⟨_, rfl⟩
  obtain ⟨VP, hvp⟩ : ∃ v, y.mem (base + N + K / 2) = v := ⟨_, rfl⟩
  have hVK : VK < N := hvk ▸ hshape.vertex_lt K (by omega) hKS
  have hVP : VP < N := hvp ▸ hshape.vertex_lt (K / 2) (by omega) (by omega)
  have f₁ : Fits w (K / 2) := hfit.of_le (by omega)
  have f₂ : Fits w (base + N + K) := hfit.of_le (by omega)
  have f₃ : Fits w (base + N + K / 2) := hfit.of_le (by omega)
  have f₄ : Fits w (base + VK) := hfit.of_le (by omega)
  have f₅ : Fits w (base + VP) := hfit.of_le (by omega)
  have f₆ : Fits w (base + 2 * N + 1 + VK) := hfit.of_le (by omega)
  have f₇ : Fits w (base + 2 * N + 1 + VP) := hfit.of_le (by omega)
  have hframe : ∀ z T, ExecWithin w siftUpBody y z T →
      ∀ i ∉ [k, p, vk, vp, dk, dp, t], z.regs i = y.regs i := by
    intro z T he i hi
    apply he.regs_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [siftUpBody, cmpKP, swapCode, Code.Preserves, Op.dest, Op.exactBin, eq_comm,
      hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2]
  let y₁ := ((((((((y.set p (K / 2)).set t (base + N + K)).set vk VK).set t
    (base + VK)).set dk (y.mem (base + VK))).set t (base + N + K / 2)).set vp VP).set t
    (base + VP)).set dp (y.mem (base + VP))
  have e₁ : ExecWithin w upLoad y y₁ 9 := by
    ram_exact_eval [upLoad, y₁, hone, hbase, hhb, hk, hvk, hvp, shiftRight_one, f₁, f₂, f₃, f₄, f₅]
  have ecmp : ExecWithin w cmpKP y₁
      (y₁.set t (if IndexedMinPQ.RawPrioLT (VK, y.mem (base + VK)) (VP, y.mem (base + VP))
        then 1 else 0)) 6 := by
    simpa +decide [y₁] using cmpKP_spec (w := w) (y := y₁)
      (by simp +decide [y₁, hzero]) (by simp +decide [y₁, hone])
  have hentK : heapEntry N base y.mem K = (VK, y.mem (base + VK)) := by simp [heapEntry, hvk]
  have hentP : heapEntry N base y.mem (K / 2) = (VP, y.mem (base + VP)) := by simp [heapEntry, hvp]
  rw [hentK, hentP, hvk, hvp]
  by_cases hlt : IndexedMinPQ.RawPrioLT (VK, y.mem (base + VK)) (VP, y.mem (base + VP))
  · simp only [hlt, ↓reduceIte] at ecmp
    let y₂ := y₁.set t 1
    obtain ⟨z, e₂, hzk, hzm⟩ : ∃ z, ExecWithin w upSwap y₂ z 9 ∧ z.regs k = K / 2 ∧
        z.mem = swapMem N base y.mem K (K / 2) VK VP := by
      refine ⟨?z₁, ?es, ?_, ?_⟩
      case es =>
        ram_exact_eval [upSwap, swapCode, y₂, y₁, hhb, hpb, hk, f₂, f₃, f₆, f₇]
      · simp +decide
      · simp [swapMem]
    have hc : (Cond.lt zero t).Holds y₂ := by simp +decide [Cond.holds_lt, y₂, y₁, hzero]
    have etot : ExecWithin w siftUpBody y z 26 := by
      rw [siftUpBody_eq]
      exact (execWithin_append e₁ (ecmp.seq (ExecWithin.branch_pos hc e₂))).mono (by omega)
    exact ⟨z, etot, hframe z _ etot, Or.inl ⟨hlt, hzk, hzm⟩⟩
  · simp only [hlt, ↓reduceIte] at ecmp
    let y₂ := y₁.set t 0
    have e₂ : ExecWithin (B := .exact) w ram_exact[ k ← one ] y₂ (y₂.set k 1) 1 := by
      ram_exact_eval [y₂, y₁, hone]
    have hc : ¬(Cond.lt zero t).Holds y₂ := by simp +decide [Cond.holds_lt, y₂, y₁, hzero]
    have etot : ExecWithin w siftUpBody y (y₂.set k 1) 26 := by
      rw [siftUpBody_eq]
      exact (execWithin_append e₁ (ecmp.seq (ExecWithin.branch_neg hc e₂))).mono (by omega)
    exact ⟨y₂.set k 1, etot, hframe _ _ etot, Or.inr ⟨hlt, by simp +decide [y₂, y₁], rfl⟩⟩

private structure UpInv (N base S : ℕ) (x y : Data rBin) : Prop where
  frame : ∀ i ∉ [k, p, vk, vp, dk, dp, t], y.regs i = x.regs i
  one_le : 1 ≤ y.regs k
  le_size : y.regs k ≤ S
  shape : HeapShape N base S y.mem
  ordered : UpOrdered (heapEntry N base y.mem) S (y.regs k)
  pos : ∀ v < N, y.mem (base + 2 * N + 1 + v) = 0 ↔ x.mem (base + 2 * N + 1 + v) = 0
  outside : ∀ a, a ≤ base + N ∨ base + 3 * N < a → y.mem a = x.mem a

/-- **Sift-up** repairs a single upward defect at `K` in `28 ⌊log₂ K⌋ + 2` instructions. -/
theorem siftUp_spec {K : ℕ} {x : Data rBin}
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hbase : x.regs baseReg = base) (hhb : x.regs hb = base + N)
    (hpb : x.regs pb = base + 2 * N + 1) (hk : x.regs k = K)
    (hK : 1 ≤ K) (hKS : K ≤ S) (hfit : Fits w (base + space N))
    (hshape : HeapShape N base S x.mem) (hord : UpOrdered (heapEntry N base x.mem) S K) :
    ∃ y, ExecWithin w siftUp x y (28 * Nat.log 2 K + 2) ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t], y.regs i = x.regs i) ∧
      HeapInv N base S y.mem ∧
      (∀ v < N, y.mem (base + 2 * N + 1 + v) = 0 ↔ x.mem (base + 2 * N + 1 + v) = 0) ∧
      (∀ a, a ≤ base + N ∨ base + 3 * N < a → y.mem a = x.mem a) := by
  have hinit : UpInv N base S x x :=
    ⟨fun _ _ => rfl, hk ▸ hK, hk ▸ hKS, hshape, hk ▸ hord, fun _ _ => Iff.rfl, fun _ _ => rfl⟩
  have hbody : ∀ y, UpInv N base S x y → (Cond.lt one k).Holds y →
      ∃ z, ExecWithin w siftUpBody y z 26 ∧ UpInv N base S x z ∧
        Nat.log 2 (z.regs k) < Nat.log 2 (y.regs k) := by
    intro y hy hc
    have hz0 : y.regs zero = 0 := (hy.frame zero (by decide)).trans hzero
    have ho : y.regs one = 1 := (hy.frame one (by decide)).trans hone
    have hkS : y.regs k ≤ S := hy.le_size
    have hK2 : 2 ≤ y.regs k := by simp only [Cond.holds_lt, ho] at hc; omega
    have hlog : 0 < Nat.log 2 (y.regs k) := Nat.log_pos (by norm_num) hK2
    obtain ⟨z, he, hfr, hz⟩ := siftUpBody_spec hz0 ho
      ((hy.frame baseReg (by decide)).trans hbase) ((hy.frame hb (by decide)).trans hhb)
      ((hy.frame pb (by decide)).trans hpb) rfl hK2 hkS hfit hy.shape
    have hfr' : ∀ i ∉ [k, p, vk, vp, dk, dp, t], z.regs i = x.regs i :=
      fun i hi => (hfr i hi).trans (hy.frame i hi)
    rcases hz with ⟨hlt, hzk, hzm⟩ | ⟨hlt, hzk, hzm⟩
    · obtain ⟨hs, hga, hgb, hgo, hpos, hout⟩ := HeapShape.swap hy.shape (a := y.regs k)
        (b := y.regs k / 2) (by omega) hkS (by omega) (by omega) (by omega)
      rw [← hzm] at hs hga hgb hgo hpos hout
      refine ⟨z, he, ⟨hfr', by omega, by omega, hs, ?_, ?_, ?_⟩, ?_⟩
      · rw [hzk]; exact hy.ordered.swap hK2 hy.le_size hlt hga hgb hgo
      · intro v hv; rw [hpos v hv]; exact hy.pos v hv
      · intro a ha; rw [hout a ha]; exact hy.outside a ha
      · rw [hzk, Nat.log_div_base]; omega
    · refine ⟨z, he, ⟨hfr', by omega, by omega, hzm ▸ hy.shape, ?_, ?_, ?_⟩, ?_⟩
      · rw [hzk, hzm]
        exact (hy.ordered.ordered
          (fun _ _ => IndexedMinPQ.not_rawPrioLT_iff_rawPrioLE.mp hlt)).upOrdered_one
      · intro v hv; rw [hzm]; exact hy.pos v hv
      · intro a ha; rw [hzm]; exact hy.outside a ha
      · rw [hzk, Nat.log_one_right]; exact hlog
  obtain ⟨y, he, hy, hexit⟩ := ExecWithin.loop_invariant (cond := .lt one k)
    (body := siftUpBody) (UpInv N base S x) (fun y => Nat.log 2 (y.regs k)) hbody hinit
  have ho : y.regs one = 1 := (hy.frame one (by decide)).trans hone
  have hk1 : y.regs k = 1 := by
    have := hy.one_le
    simp only [Cond.holds_lt, ho] at hexit; omega
  refine ⟨y, he.mono (by rw [hk]; omega), hy.frame, ⟨hy.shape, ?_⟩, hy.pos, hy.outside⟩
  have hord' := hy.ordered
  rw [hk1] at hord'
  exact hord'.ordered (fun h => absurd h (by omega))

end SiftUp

/-! ### Sift-down and Root Extraction -/

section SiftDown

variable {N base S w : ℕ}

private def minChild (f : ℕ → ℕ × ℕ) (S a : ℕ) : ℕ :=
  if 2 * a + 1 ≤ S ∧ IndexedMinPQ.RawPrioLT (f (2 * a + 1)) (f (2 * a)) then 2 * a + 1 else 2 * a

private theorem minChild_spec {f : ℕ → ℕ × ℕ} {a : ℕ} (ha : 2 * a ≤ S) :
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

private def chooseLeft : Code .exact rBin := ram_exact[
  p ← l;
  t ← hb + l; vp ← *t; t ← baseReg + vp; dp ← *t;
  t ← l + one ]

private def chooseRightLoad : Code .exact rBin := ram_exact[
  t ← hb + t; vk ← *t; t ← baseReg + vk; dk ← *t ]

private def chooseRightTake : Code .exact rBin := ram_exact[
  p ← l + one; vp ← vk; dp ← dk ]

private theorem siftDownChoose_eq : siftDownChoose = appendCode chooseLeft
    (.branch (.lt t szp) (appendCode chooseRightLoad
      (.seq cmpKP (.branch (.lt zero t) chooseRightTake ram_exact[ p ← p ])))
      ram_exact[ p ← p ]) := rfl

private theorem siftDownChoose_spec {K : ℕ} {y : Data rBin}
    (hzero : y.regs zero = 0) (hone : y.regs one = 1)
    (hbase : y.regs baseReg = base) (hhb : y.regs hb = base + N)
    (hl : y.regs l = 2 * K) (hszp : y.regs szp = S + 1)
    (hK : 1 ≤ K) (hKS : 2 * K ≤ S) (hfit : Fits w (base + space N))
    (hshape : HeapShape N base S y.mem) :
    ∃ z, ExecWithin w siftDownChoose y z 22 ∧
      (∀ i ∉ [p, t, vp, dp, vk, dk], z.regs i = y.regs i) ∧ z.mem = y.mem ∧
      z.regs p = minChild (heapEntry N base y.mem) S K ∧
      z.regs vp = y.mem (base + N + minChild (heapEntry N base y.mem) S K) ∧
      z.regs dp = (heapEntry N base y.mem (minChild (heapEntry N base y.mem) S K)).2 := by
  have hSN := hshape.size_le
  have hsp : space N = 3 * N + 1 := rfl
  obtain ⟨VL, hvl⟩ : ∃ v, y.mem (base + N + 2 * K) = v := ⟨_, rfl⟩
  have hVL : VL < N := hvl ▸ hshape.vertex_lt (2 * K) (by omega) hKS
  have f₁ : Fits w (base + N + 2 * K) := hfit.of_le (by omega)
  have f₂ : Fits w (base + VL) := hfit.of_le (by omega)
  have f₃ : Fits w (2 * K + 1) := hfit.of_le (by omega)
  have hframe : ∀ z T, ExecWithin w siftDownChoose y z T →
      ∀ i ∉ [p, t, vp, dp, vk, dk], z.regs i = y.regs i := by
    intro z T he i hi
    apply he.regs_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [siftDownChoose, cmpKP, Code.Preserves, Op.dest, Op.exactBin, eq_comm,
      hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2]
  let y₁ := (((((y.set p (2 * K)).set t (base + N + 2 * K)).set vp VL).set t
    (base + VL)).set dp (y.mem (base + VL))).set t (2 * K + 1)
  have e₁ : ExecWithin w chooseLeft y y₁ 6 := by
    ram_exact_eval [chooseLeft, y₁, hone, hbase, hhb, hl, hvl, f₁, f₂, f₃]
  by_cases h₁ : 2 * K + 1 < S + 1
  · have hc₁ : (Cond.lt t szp).Holds y₁ := by simp +decide [Cond.holds_lt, y₁, hszp, h₁]
    obtain ⟨VR, hvr⟩ : ∃ v, y.mem (base + N + (2 * K + 1)) = v := ⟨_, rfl⟩
    have hVR : VR < N := hvr ▸ hshape.vertex_lt (2 * K + 1) (by omega) (by omega)
    have f₄ : Fits w (base + N + (2 * K + 1)) := hfit.of_le (by omega)
    have f₅ : Fits w (base + VR) := hfit.of_le (by omega)
    let y₂ := (((y₁.set t (base + N + (2 * K + 1))).set vk VR).set t (base + VR)).set dk
      (y.mem (base + VR))
    have e₂ : ExecWithin w chooseRightLoad y₁ y₂ 4 := by
      ram_exact_eval [chooseRightLoad, y₂, y₁, hbase, hhb, hvr, f₄, f₅]
    have ecmp : ExecWithin w cmpKP y₂
        (y₂.set t (if IndexedMinPQ.RawPrioLT (VR, y.mem (base + VR)) (VL, y.mem (base + VL))
          then 1 else 0)) 6 := by
      simpa +decide [y₂, y₁] using cmpKP_spec (w := w) (y := y₂)
        (by simp +decide [y₂, y₁, hzero]) (by simp +decide [y₂, y₁, hone])
    have hentL : heapEntry N base y.mem (2 * K) = (VL, y.mem (base + VL)) := by
      simp [heapEntry, hvl]
    have hentR : heapEntry N base y.mem (2 * K + 1) = (VR, y.mem (base + VR)) := by
      simp [heapEntry, hvr]
    by_cases h₂ : IndexedMinPQ.RawPrioLT (VR, y.mem (base + VR)) (VL, y.mem (base + VL))
    · simp only [h₂, ↓reduceIte] at ecmp
      have hC : minChild (heapEntry N base y.mem) S K = 2 * K + 1 := by
        unfold minChild; exact ite_eq_left ⟨by omega, by rw [hentR, hentL]; exact h₂⟩
      let y₃ := y₂.set t 1
      have hc₂ : (Cond.lt zero t).Holds y₃ := by simp +decide [Cond.holds_lt, y₃, y₂, y₁, hzero]
      obtain ⟨z, e₃, hzm, hzp, hzvp, hzdp⟩ : ∃ z, ExecWithin w chooseRightTake y₃ z 3 ∧
          z.mem = y.mem ∧ z.regs p = 2 * K + 1 ∧ z.regs vp = VR ∧
          z.regs dp = y.mem (base + VR) := by
        refine ⟨?z₁, ?es, ?_, ?_, ?_, ?_⟩
        case es => ram_exact_eval [chooseRightTake, y₃, y₂, y₁, hone, hl, f₃]
        all_goals simp +decide
      have etot : ExecWithin w siftDownChoose y z 22 := by
        rw [siftDownChoose_eq]
        exact (execWithin_append e₁ (ExecWithin.branch_pos hc₁
          (execWithin_append e₂ (ecmp.seq (ExecWithin.branch_pos hc₂ e₃))))).mono (by omega)
      rw [hC, hentR, hvr]
      exact ⟨z, etot, hframe z _ etot, hzm, hzp, hzvp, hzdp⟩
    · simp only [h₂, ↓reduceIte] at ecmp
      have hC : minChild (heapEntry N base y.mem) S K = 2 * K := by
        unfold minChild; exact ite_eq_right fun h => h₂ (by rw [hentR, hentL] at h; exact h.2)
      let y₃ := y₂.set t 0
      have hc₂ : ¬(Cond.lt zero t).Holds y₃ := by simp +decide [Cond.holds_lt, y₃, y₂, y₁, hzero]
      have e₃ : ExecWithin (B := .exact) w ram_exact[ p ← p ] y₃ (y₃.set p (2 * K)) 1 := by
        ram_exact_eval [y₃, y₂, y₁]
      have etot : ExecWithin w siftDownChoose y (y₃.set p (2 * K)) 22 := by
        rw [siftDownChoose_eq]
        exact (execWithin_append e₁ (ExecWithin.branch_pos hc₁
          (execWithin_append e₂ (ecmp.seq (ExecWithin.branch_neg hc₂ e₃))))).mono (by omega)
      rw [hC, hentL, hvl]
      exact ⟨y₃.set p (2 * K), etot, hframe _ _ etot, rfl, by simp +decide [y₃, y₂, y₁],
        by simp +decide [y₃, y₂, y₁], by simp +decide [y₃, y₂, y₁]⟩
  · have hc₁ : ¬(Cond.lt t szp).Holds y₁ := by simp +decide [Cond.holds_lt, y₁, hszp, h₁]
    have hC : minChild (heapEntry N base y.mem) S K = 2 * K := by
      unfold minChild; exact ite_eq_right fun h => h₁ (by omega)
    have e₂ : ExecWithin (B := .exact) w ram_exact[ p ← p ] y₁ (y₁.set p (2 * K)) 1 := by
      ram_exact_eval [y₁]
    have etot : ExecWithin w siftDownChoose y (y₁.set p (2 * K)) 22 := by
      rw [siftDownChoose_eq]
      exact (execWithin_append e₁ (ExecWithin.branch_neg hc₁ e₂)).mono (by omega)
    rw [hC, show (heapEntry N base y.mem (2 * K)).2 = y.mem (base + VL) by simp [heapEntry, hvl],
      hvl]
    exact ⟨y₁.set p (2 * K), etot, hframe _ _ etot, rfl, by simp +decide [y₁],
      by simp +decide [y₁], by simp +decide [y₁]⟩

private def sinkLoad : Code .exact rBin := ram_exact[
  t ← hb + k; vk ← *t; t ← baseReg + vk; dk ← *t ]

private def sinkSwap : Code .exact rBin := ram_exact[
  ⟪swapCode⟫; k ← p; l ← k + k ]

private theorem siftDownSink_eq : siftDownSink = appendCode sinkLoad
    (.seq cmpPK (.branch (.lt zero t) sinkSwap ram_exact[ l ← szp ])) := rfl

private theorem siftDownSink_spec {K C : ℕ} {y : Data rBin}
    (hzero : y.regs zero = 0) (hone : y.regs one = 1)
    (hbase : y.regs baseReg = base) (hhb : y.regs hb = base + N)
    (hpb : y.regs pb = base + 2 * N + 1) (hk : y.regs k = K)
    (hp : y.regs p = C) (hvp : y.regs vp = y.mem (base + N + C))
    (hdp : y.regs dp = (heapEntry N base y.mem C).2)
    (hszp : y.regs szp = S + 1) (hK : 1 ≤ K) (hKS : K ≤ S)
    (hC : 1 ≤ C) (hCS : C ≤ S) (hfit : Fits w (base + space N))
    (hshape : HeapShape N base S y.mem) :
    ∃ z, ExecWithin w siftDownSink y z 22 ∧
      (∀ i ∉ [t, vk, dk, k, l], z.regs i = y.regs i) ∧
      (IndexedMinPQ.RawPrioLT (heapEntry N base y.mem C) (heapEntry N base y.mem K) ∧
        z.regs k = C ∧ z.regs l = 2 * C ∧
        z.mem = swapMem N base y.mem K C (y.mem (base + N + K)) (y.mem (base + N + C)) ∨
       ¬IndexedMinPQ.RawPrioLT (heapEntry N base y.mem C) (heapEntry N base y.mem K) ∧
        z.regs k = K ∧ z.regs l = S + 1 ∧ z.mem = y.mem) := by
  have hSN := hshape.size_le
  have hsp : space N = 3 * N + 1 := rfl
  obtain ⟨VK, hvk⟩ : ∃ v, y.mem (base + N + K) = v := ⟨_, rfl⟩
  obtain ⟨VC, hvc⟩ : ∃ v, y.mem (base + N + C) = v := ⟨_, rfl⟩
  rw [hvc] at hvp
  have hVK : VK < N := hvk ▸ hshape.vertex_lt K hK hKS
  have hVC : VC < N := hvc ▸ hshape.vertex_lt C hC hCS
  have f₁ : Fits w (base + N + K) := hfit.of_le (by omega)
  have f₂ : Fits w (base + VK) := hfit.of_le (by omega)
  have f₃ : Fits w (base + N + C) := hfit.of_le (by omega)
  have f₄ : Fits w (base + 2 * N + 1 + VK) := hfit.of_le (by omega)
  have f₅ : Fits w (base + 2 * N + 1 + VC) := hfit.of_le (by omega)
  have f₆ : Fits w (C + C) := hfit.of_le (by omega)
  have hframe : ∀ z T, ExecWithin w siftDownSink y z T →
      ∀ i ∉ [t, vk, dk, k, l], z.regs i = y.regs i := by
    intro z T he i hi
    apply he.regs_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [siftDownSink, cmpPK, swapCode, Code.Preserves, Op.dest, Op.exactBin, eq_comm,
      hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2]
  let y₁ := (((y.set t (base + N + K)).set vk VK).set t (base + VK)).set dk (y.mem (base + VK))
  have e₁ : ExecWithin w sinkLoad y y₁ 4 := by
    ram_exact_eval [sinkLoad, y₁, hbase, hhb, hk, hvk, f₁, f₂]
  have hentK : heapEntry N base y.mem K = (VK, y.mem (base + VK)) := by simp [heapEntry, hvk]
  have hentC : heapEntry N base y.mem C = (VC, y.mem (base + VC)) := by simp [heapEntry, hvc]
  rw [hentC] at hdp
  have ecmp : ExecWithin w cmpPK y₁
      (y₁.set t (if IndexedMinPQ.RawPrioLT (VC, y.mem (base + VC)) (VK, y.mem (base + VK))
        then 1 else 0)) 6 := by
    simpa +decide [y₁, hvp, hdp] using cmpPK_spec (w := w) (y := y₁)
      (by simp +decide [y₁, hzero]) (by simp +decide [y₁, hone])
  rw [hentC, hentK, hvk, hvc]
  by_cases hlt : IndexedMinPQ.RawPrioLT (VC, y.mem (base + VC)) (VK, y.mem (base + VK))
  · simp only [hlt, ↓reduceIte] at ecmp
    let y₂ := y₁.set t 1
    have hc : (Cond.lt zero t).Holds y₂ := by simp +decide [Cond.holds_lt, y₂, y₁, hzero]
    obtain ⟨z, e₂, hzk, hzl, hzm⟩ : ∃ z, ExecWithin w sinkSwap y₂ z 10 ∧ z.regs k = C ∧
        z.regs l = 2 * C ∧ z.mem = swapMem N base y.mem K C VK VC := by
      refine ⟨?z₁, ?es, ?_, ?_, ?_⟩
      case es =>
        ram_exact_eval [sinkSwap, swapCode, y₂, y₁, hhb, hpb, hk, hp, hvp, f₁, f₃, f₄, f₅, f₆]
      · simp +decide
      · simp +decide only [Data.set_regs, Data.write_regs, Function.update_self]; omega
      · simp [swapMem]
    have etot : ExecWithin w siftDownSink y z 22 := by
      rw [siftDownSink_eq]
      exact (execWithin_append e₁ (ecmp.seq (ExecWithin.branch_pos hc e₂))).mono (by omega)
    exact ⟨z, etot, hframe z _ etot, Or.inl ⟨hlt, hzk, hzl, hzm⟩⟩
  · simp only [hlt, ↓reduceIte] at ecmp
    let y₂ := y₁.set t 0
    have hc : ¬(Cond.lt zero t).Holds y₂ := by simp +decide [Cond.holds_lt, y₂, y₁, hzero]
    have e₂ : ExecWithin (B := .exact) w ram_exact[ l ← szp ] y₂ (y₂.set l (S + 1)) 1 := by
      ram_exact_eval [y₂, y₁, hszp]
    have etot : ExecWithin w siftDownSink y (y₂.set l (S + 1)) 22 := by
      rw [siftDownSink_eq]
      exact (execWithin_append e₁ (ecmp.seq (ExecWithin.branch_neg hc e₂))).mono (by omega)
    exact ⟨y₂.set l (S + 1), etot, hframe _ _ etot,
      Or.inr ⟨hlt, by simp +decide [y₂, y₁, hk], by simp +decide [y₂, y₁], rfl⟩⟩

private theorem siftDownBody_spec {K C : ℕ} {y : Data rBin}
    (hzero : y.regs zero = 0) (hone : y.regs one = 1)
    (hbase : y.regs baseReg = base) (hhb : y.regs hb = base + N)
    (hpb : y.regs pb = base + 2 * N + 1) (hk : y.regs k = K)
    (hl : y.regs l = 2 * K) (hszp : y.regs szp = S + 1)
    (hK : 1 ≤ K) (hKS : 2 * K ≤ S) (hfit : Fits w (base + space N))
    (hshape : HeapShape N base S y.mem) (hC : C = minChild (heapEntry N base y.mem) S K) :
    ∃ z, ExecWithin w siftDownBody y z 44 ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t, l], z.regs i = y.regs i) ∧
      (IndexedMinPQ.RawPrioLT (heapEntry N base y.mem C) (heapEntry N base y.mem K) ∧
        z.regs k = C ∧ z.regs l = 2 * C ∧
        z.mem = swapMem N base y.mem K C (y.mem (base + N + K)) (y.mem (base + N + C)) ∨
       ¬IndexedMinPQ.RawPrioLT (heapEntry N base y.mem C) (heapEntry N base y.mem K) ∧
        z.regs k = K ∧ z.regs l = S + 1 ∧ z.mem = y.mem) := by
  obtain ⟨z₁, he₁, hfr₁, hm₁, hp₁, hvp₁, hdp₁⟩ :=
    siftDownChoose_spec hzero hone hbase hhb hl hszp hK hKS hfit hshape
  rw [← hC] at hp₁ hvp₁ hdp₁
  obtain ⟨hCc, hCS, -⟩ := minChild_spec (f := heapEntry N base y.mem) hKS
  rw [← hC] at hCc hCS
  obtain ⟨z, he₂, hfr₂, hz⟩ := siftDownSink_spec (y := z₁) (K := K) (C := C)
    ((hfr₁ zero (by decide)).trans hzero) ((hfr₁ one (by decide)).trans hone)
    ((hfr₁ baseReg (by decide)).trans hbase) ((hfr₁ hb (by decide)).trans hhb)
    ((hfr₁ pb (by decide)).trans hpb) ((hfr₁ k (by decide)).trans hk)
    hp₁ (hm₁ ▸ hvp₁) (hm₁ ▸ hdp₁) ((hfr₁ szp (by decide)).trans hszp)
    hK (by omega) (by omega) hCS hfit (hm₁ ▸ hshape)
  rw [hm₁] at hz
  refine ⟨z, (he₁.seq he₂).mono (by norm_num), fun i hi => ?_, hz⟩
  refine (hfr₂ i fun h => hi ?_).trans (hfr₁ i fun h => hi ?_)
  · exact (by decide : [t, vk, dk, k, l] ⊆ [k, p, vk, vp, dk, dp, t, l]) h
  · exact (by decide : [p, t, vp, dp, vk, dk] ⊆ [k, p, vk, vp, dk, dp, t, l]) h

private structure DownInv (N base S : ℕ) (x y : Data rBin) : Prop where
  frame : ∀ i ∉ [k, p, vk, vp, dk, dp, t, l, szp], y.regs i = x.regs i
  size_reg : y.regs szp = S + 1
  one_le : 1 ≤ y.regs k
  le_size : y.regs k ≤ S
  shape : HeapShape N base S y.mem
  order : y.regs l = 2 * y.regs k ∧ DownOrdered (heapEntry N base y.mem) S (y.regs k) ∨
    y.regs l = S + 1 ∧ Ordered (heapEntry N base y.mem) S
  pos : ∀ v < N, y.mem (base + 2 * N + 1 + v) = 0 ↔ x.mem (base + 2 * N + 1 + v) = 0
  outside : ∀ a, a ≤ base + N ∨ base + 3 * N < a → y.mem a = x.mem a

private def downSetup : Code .exact rBin := ram_exact[ l ← k + k; szp ← sz + one ]

private theorem siftDown_eq :
    siftDown = appendCode downSetup (.loop (.lt l szp) siftDownBody) := rfl

private def downMeasure (S : ℕ) (y : Data rBin) : ℕ :=
  if y.regs l < S + 1 then Nat.log 2 (S + 1) + 1 - Nat.log 2 (y.regs l) else 0

/-- **Sift-down** repairs a single downward defect at `K` in `46 ⌊log₂ (S + 1)⌋ + 4` instructions.
-/
theorem siftDown_spec {K : ℕ} {x : Data rBin}
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hbase : x.regs baseReg = base) (hhb : x.regs hb = base + N)
    (hpb : x.regs pb = base + 2 * N + 1) (hsz : x.regs sz = S)
    (hk : x.regs k = K) (hK : 1 ≤ K) (hKS : K ≤ S) (hfit : Fits w (base + space N))
    (hshape : HeapShape N base S x.mem) (hord : DownOrdered (heapEntry N base x.mem) S K) :
    ∃ y, ExecWithin w siftDown x y (46 * Nat.log 2 (S + 1) + 4) ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t, l, szp], y.regs i = x.regs i) ∧
      HeapInv N base S y.mem ∧
      (∀ v < N, y.mem (base + 2 * N + 1 + v) = 0 ↔ x.mem (base + 2 * N + 1 + v) = 0) ∧
      (∀ a, a ≤ base + N ∨ base + 3 * N < a → y.mem a = x.mem a) := by
  have hSN := hshape.size_le
  have hsp : space N = 3 * N + 1 := rfl
  have f₁ : Fits w (K + K) := hfit.of_le (by omega)
  have f₂ : Fits w (S + 1) := hfit.of_le (by omega)
  obtain ⟨x₁, he₁, hx₁l, hx₁s, hx₁m, hx₁r⟩ : ∃ x₁, ExecWithin w downSetup x x₁ 2 ∧
      x₁.regs l = 2 * K ∧ x₁.regs szp = S + 1 ∧ x₁.mem = x.mem ∧
      ∀ i, i ≠ l → i ≠ szp → x₁.regs i = x.regs i := by
    refine ⟨?z₀, ?e₀, ?_, ?_, ?_, ?_⟩
    case e₀ => ram_exact_eval [downSetup, hone, hk, hsz, f₁, f₂]
    · simp +decide only [Data.set_regs, ne_eq, Function.update_of_ne, Function.update_self]; omega
    · simp
    · rfl
    · intro i h₁ h₂; simp [h₁, h₂]
  have hx₁k : x₁.regs k = K := (hx₁r k (by decide) (by decide)).trans hk
  have hinit : DownInv N base S x x₁ := by
    refine ⟨fun i hi => hx₁r i ?_ ?_, hx₁s, hx₁k ▸ hK, hx₁k ▸ hKS, hx₁m ▸ hshape,
      Or.inl ⟨by rw [hx₁l, hx₁k], by rw [hx₁m, hx₁k]; exact hord⟩, fun _ _ => by rw [hx₁m],
      fun _ _ => by rw [hx₁m]⟩
    · rintro rfl; simp at hi
    · rintro rfl; simp at hi
  have hbody : ∀ y, DownInv N base S x y → (Cond.lt l szp).Holds y →
      ∃ z, ExecWithin w siftDownBody y z 44 ∧ DownInv N base S x z ∧
        downMeasure S z < downMeasure S y := by
    intro y hy hc
    have hr := hy.frame
    have hsz' := hy.size_reg
    have hk1 := hy.one_le
    have hkS := hy.le_size
    simp only [Cond.holds_lt, hsz'] at hc
    obtain ⟨hl', hdo⟩ := hy.order.resolve_right fun h => by omega
    obtain ⟨C, hC⟩ : ∃ C, C = minChild (heapEntry N base y.mem) S (y.regs k) := ⟨_, rfl⟩
    obtain ⟨hCc, hCS, hmin⟩ := minChild_spec (S := S) (f := heapEntry N base y.mem)
      (a := y.regs k) (by omega)
    rw [← hC] at hCc hCS hmin
    obtain ⟨z, he, hfr, hz⟩ := siftDownBody_spec
      ((hr zero (by decide)).trans hzero) ((hr one (by decide)).trans hone)
      ((hr baseReg (by decide)).trans hbase) ((hr hb (by decide)).trans hhb)
      ((hr pb (by decide)).trans hpb) rfl hl' hsz' hk1 (by omega) hfit hy.shape hC
    have hfr' : ∀ i ∉ [k, p, vk, vp, dk, dp, t, l, szp], z.regs i = x.regs i := by
      intro i hi
      refine (hfr i fun h => hi ?_).trans (hr i hi)
      exact List.mem_append_left [szp] h
    have hzs : z.regs szp = S + 1 := (hfr szp (by decide)).trans hsz'
    have hμ : downMeasure S y = Nat.log 2 (S + 1) + 1 - Nat.log 2 (y.regs l) := by
      simp only [downMeasure]; exact ite_eq_left hc
    rcases hz with ⟨hlt, hzk, hzl, hzm⟩ | ⟨hlt, hzk, hzl, hzm⟩
    · obtain ⟨hs, hga, hgb, hgo, hpos, hout⟩ := HeapShape.swap hy.shape (a := y.regs k)
        (b := C) hk1 hkS (by omega) hCS (by omega)
      rw [← hzm] at hs hga hgb hgo hpos hout
      refine ⟨z, he, ⟨hfr', hzs, by omega, by omega, hs, Or.inl ⟨by rw [hzl, hzk], ?_⟩, ?_, ?_⟩,
        ?_⟩
      · rw [hzk]; exact hdo.swap (by omega) hCS (fun i _ hiS hia => hmin i hiS hia) hlt hga hgb hgo
      · intro v hv; rw [hpos v hv]; exact hy.pos v hv
      · intro a ha; rw [hout a ha]; exact hy.outside a ha
      · have h₀ : Nat.log 2 (y.regs l) ≤ Nat.log 2 (S + 1) := Nat.log_mono_right (by omega)
        have h₁ : Nat.log 2 (y.regs l) ≤ Nat.log 2 C := Nat.log_mono_right (by omega)
        have h₂ : Nat.log 2 (z.regs l) = Nat.log 2 C + 1 := by
          rw [hzl, mul_comm]; exact Nat.log_mul_base (by norm_num) (by omega)
        rw [hμ]
        simp only [downMeasure]
        split_ifs with h₃
        · have : Nat.log 2 (z.regs l) ≤ Nat.log 2 (S + 1) := Nat.log_mono_right (by omega)
          omega
        · omega
    · refine ⟨z, he, ⟨hfr', hzs, by omega, by omega, hzm ▸ hy.shape, Or.inr ⟨hzl, ?_⟩, ?_, ?_⟩,
        ?_⟩
      · rw [hzm]
        exact hdo.ordered fun i _ hiS hia =>
          (IndexedMinPQ.not_rawPrioLT_iff_rawPrioLE.mp hlt).trans (hmin i hiS hia)
      · intro v hv; rw [hzm]; exact hy.pos v hv
      · intro a ha; rw [hzm]; exact hy.outside a ha
      · have : Nat.log 2 (y.regs l) ≤ Nat.log 2 (S + 1) := Nat.log_mono_right (by omega)
        rw [hμ]; simp only [downMeasure, hzl, lt_irrefl, ite_false]; omega
  obtain ⟨y, he, hy, hexit⟩ := ExecWithin.loop_invariant (cond := .lt l szp)
    (body := siftDownBody) (DownInv N base S x) (downMeasure S) hbody hinit
  have hμ : downMeasure S x₁ ≤ Nat.log 2 (S + 1) := by
    simp only [downMeasure, hx₁l]
    split_ifs with h
    · have : Nat.log 2 (2 * K) = Nat.log 2 K + 1 := by
        rw [mul_comm]; exact Nat.log_mul_base (by norm_num) (by omega)
      omega
    · omega
  refine ⟨y, ?_, hy.frame, ⟨hy.shape, ?_⟩, hy.pos, hy.outside⟩
  · rw [siftDown_eq]
    refine (execWithin_append he₁ he).mono ?_
    have := Nat.mul_le_mul_right 46 hμ; omega
  · have := hy.size_reg
    simp only [Cond.holds_lt, this] at hexit
    rcases hy.order with ⟨_, hdo⟩ | ⟨_, hord'⟩
    · exact hdo.ordered fun i _ hiS _ => absurd hiS (by omega)
    · exact hord'

private def extractHead : Code .exact rBin := ram_exact[
  outFlag ← one;
  t ← hb + one; outV ← *t;
  t ← baseReg + outV; outK ← *t;
  t ← pb + outV; *t ← zero;
  t ← hb + sz; vk ← *t;
  sz ← sz - one ]

private def extractMove : Code .exact rBin := ram_exact[
  t ← hb + one; *t ← vk;
  t ← pb + vk; *t ← one;
  k ← one ]

private theorem doExtractNonEmpty_eq : doExtractNonEmpty = appendCode extractHead
    (.branch (.lt zero sz) (appendCode extractMove siftDown) ram_exact[ k ← k ]) := rfl

/-- **Non-empty root extraction** runs in `46 ⌊log₂ S⌋ + 20` instructions, sets `(outFlag, outV,
outK) = (1, U, key[U])`, and removes `U` while preserving `HeapInv` and all keys. -/
theorem doExtractNonEmpty_spec {x : Data rBin}
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hbase : x.regs baseReg = base) (hhb : x.regs hb = base + N)
    (hpb : x.regs pb = base + 2 * N + 1) (hsz : x.regs sz = S)
    (hS : 1 ≤ S) (hfit : Fits w (base + space N)) (hheap : HeapInv N base S x.mem) :
    ∃ y, ExecWithin w doExtractNonEmpty x y (46 * Nat.log 2 S + 20) ∧
      (∀ i ∉ [outFlag, outV, outK, t, vk, sz, k, p, vp, dk, dp, l, szp], y.regs i = x.regs i) ∧
      y.regs outFlag = 1 ∧ y.regs outV = x.mem (base + N + 1) ∧
      y.regs outK = x.mem (base + x.mem (base + N + 1)) ∧
      y.regs sz = S - 1 ∧ HeapInv N base (S - 1) y.mem ∧
      (∀ v < N, y.mem (base + 2 * N + 1 + v) = 0 ↔
        x.mem (base + 2 * N + 1 + v) = 0 ∨ v = x.mem (base + N + 1)) ∧
      (∀ a, a ≤ base + N ∨ base + 3 * N < a → y.mem a = x.mem a) := by
  have hSN := hheap.size_le
  have hsp : space N = 3 * N + 1 := rfl
  obtain ⟨U, hU⟩ : ∃ v, x.mem (base + N + 1) = v := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ v, x.mem (base + N + S) = v := ⟨_, rfl⟩
  have hUN : U < N := hU ▸ hheap.vertex_lt 1 le_rfl hS
  have hLN : L < N := hL ▸ hheap.vertex_lt S hS le_rfl
  rw [hU]
  have f₁ : Fits w (base + N + 1) := hfit.of_le (by omega)
  have f₂ : Fits w (base + U) := hfit.of_le (by omega)
  have f₃ : Fits w (base + 2 * N + 1 + U) := hfit.of_le (by omega)
  have f₄ : Fits w (base + N + S) := hfit.of_le (by omega)
  have f₅ : Fits w (S - 1) := hfit.of_le (by omega)
  have hne : ¬base + N + S = base + 2 * N + 1 + U := by omega
  obtain ⟨x₁, he₁, hx₁f, hx₁u, hx₁b, hx₁v, hx₁s, hx₁m, hx₁r⟩ :
      ∃ x₁, ExecWithin w extractHead x x₁ 10 ∧
      x₁.regs outFlag = 1 ∧ x₁.regs outV = U ∧ x₁.regs outK = x.mem (base + U) ∧
      x₁.regs vk = L ∧ x₁.regs sz = S - 1 ∧
      x₁.mem = Function.update x.mem (base + 2 * N + 1 + U) 0 ∧
      ∀ i ∉ [outFlag, outV, outK, t, vk, sz], x₁.regs i = x.regs i := by
    refine ⟨?z₀, ?e₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case e₀ =>
      ram_exact_eval [extractHead, hzero, hone, hbase, hhb, hpb, hsz, hU, hL, hne, hS,
        f₁, f₂, f₃, f₄, f₅]
    · simp +decide
    · simp +decide
    · simp +decide
    · simp +decide
    · simp +decide
    · simp
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp [hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2]
  have hout₁ : ∀ a, a ≤ base + N ∨ base + 3 * N < a → x₁.mem a = x.mem a := by
    intro a ha; rw [hx₁m, Function.update_of_ne (by omega)]
  have hsub : ∀ (L₁ L₂ : List (Fin rBin)), (∀ i ∈ L₁, i ∈ L₂) → ∀ i ∉ L₂, i ∉ L₁ :=
    fun _ _ h i hi hi' => hi (h i hi')
  by_cases hS2 : 2 ≤ S
  · obtain ⟨hs, hdo, hpos⟩ := hheap.extract hS2
    rw [hU, hL] at hs hdo hpos
    have f₆ : Fits w (base + 2 * N + 1 + L) := hfit.of_le (by omega)
    obtain ⟨x₂, he₂, hx₂k, hx₂m, hx₂r⟩ : ∃ x₂, ExecWithin w extractMove x₁ x₂ 5 ∧
        x₂.regs k = 1 ∧ x₂.mem = Function.update (Function.update
          (Function.update x.mem (base + 2 * N + 1 + U) 0) (base + N + 1) L)
          (base + 2 * N + 1 + L) 1 ∧
        ∀ i ∉ [t, k], x₂.regs i = x₁.regs i := by
      refine ⟨?z₁, ?e₁, ?_, ?_, ?_⟩
      case e₁ =>
        ram_exact_eval [extractMove, hx₁r one (by decide) ▸ hone, hx₁r hb (by decide) ▸ hhb,
          hx₁r pb (by decide) ▸ hpb, hx₁v, hx₁m, f₁, f₆]
      · simp +decide
      · simp [hx₁m]
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp [hi.1, hi.2]
    have hr₂₁ : ∀ i ∉ [outFlag, outV, outK, t, vk, sz, k], x₂.regs i = x.regs i := fun i hi =>
      (hx₂r i (hsub _ _ (by simp) i hi)).trans (hx₁r i (hsub _ _ (by simp) i hi))
    obtain ⟨y, he₃, hfr₃, hheap', hpos₃, hout₃⟩ := siftDown_spec (S := S - 1) (K := 1)
      (hr₂₁ zero (by decide) ▸ hzero) (hr₂₁ one (by decide) ▸ hone)
      (hr₂₁ baseReg (by decide) ▸ hbase) (hr₂₁ hb (by decide) ▸ hhb)
      (hr₂₁ pb (by decide) ▸ hpb) ((hx₂r sz (by decide)).trans hx₁s)
      hx₂k le_rfl (by omega) hfit (hx₂m ▸ hs) (hx₂m ▸ hdo)
    rw [Nat.sub_add_cancel hS] at he₃
    have hc : (Cond.lt zero sz).Holds x₁ := by
      simp only [Cond.holds_lt, hx₁r zero (by decide) ▸ hzero, hx₁s]; omega
    refine ⟨y, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, hheap', fun v hv => ?_, fun a ha => ?_⟩
    · rw [doExtractNonEmpty_eq]
      exact (execWithin_append he₁ (ExecWithin.branch_pos hc
        (execWithin_append he₂ he₃))).mono (by omega)
    · exact (hfr₃ i (hsub _ _ (by simp) i hi)).trans (hr₂₁ i (hsub _ _ (by simp) i hi))
    · rw [hfr₃ outFlag (by decide), hx₂r outFlag (by decide), hx₁f]
    · rw [hfr₃ outV (by decide), hx₂r outV (by decide), hx₁u]
    · rw [hfr₃ outK (by decide), hx₂r outK (by decide), hx₁b]
    · rw [hfr₃ sz (by decide), hx₂r sz (by decide), hx₁s]
    · rw [hpos₃ v hv, hx₂m]; exact hpos v hv
    · rw [hout₃ a ha, hx₂m, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
  · obtain rfl : S = 1 := by omega
    have hc : ¬(Cond.lt zero sz).Holds x₁ := by
      simp only [Cond.holds_lt, hx₁r zero (by decide) ▸ hzero, hx₁s]; omega
    have he₂ : ExecWithin (B := .exact) w ram_exact[ k ← k ] x₁ (x₁.set k (x₁.regs k)) 1 := by
      ram_exact_eval
    have hset : x₁.set k (x₁.regs k) = x₁ := by ext i <;> simp [Data.set]
    rw [hset] at he₂
    have hheap' := hheap.extract_one
    rw [hU] at hheap'
    refine ⟨x₁, ?_, fun i hi => hx₁r i (hsub _ _ (by simp) i hi), hx₁f, hx₁u, hx₁b, hx₁s,
      hx₁m ▸ hheap', fun v hv => ?_, hout₁⟩
    · rw [doExtractNonEmpty_eq]
      exact (execWithin_append he₁ (ExecWithin.branch_neg hc he₂)).mono (by omega)
    · rw [hx₁m, Function.update_apply]
      split_ifs with h
      · exact iff_of_true rfl (Or.inr (by omega))
      · exact ⟨Or.inl, fun h' => h'.resolve_right (by omega)⟩

end SiftDown

end Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap
