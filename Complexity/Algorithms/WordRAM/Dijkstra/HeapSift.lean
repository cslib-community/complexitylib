/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.BinaryHeap

/-!
# Dijkstra's algorithm with a binary heap: the heap operations

This file proves what the heap operations of `Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra`
do on a heap with the invariant `Cslib.Algorithms.WordRAM.Dijkstra.HeapInv`, and how long they
take. A sift-up or a sift-down halves or doubles the repaired position at every step, so each
takes `O(⌊log₂ sz⌋ + 1)` instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.appendCode`: one code block after another, nested as
  `ram_exact[…]` nests sequences, so that a program splits into blocks proved one at a time.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.siftUp_spec`,
  `Cslib.Algorithms.WordRAM.Dijkstra.siftDown_spec`: the two repairs.
* `Cslib.Algorithms.WordRAM.Dijkstra.extractMin_spec`: removal of the root.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM HeapReg

variable {N Db S : ℕ}

/-! ### Sequencing -/

/-- `appendCode c d` runs `c` and then `d`, as a sequence nested to the right, as the notation
`ram_exact[…]` nests it. -/
def appendCode {B : Basis} {r : ℕ} : Code B r → Code B r → Code B r
  | .seq c₁ c₂, d => .seq c₁ (appendCode c₂ d)
  | c, d => .seq c d

/-- Running `c` and then `d`. -/
theorem execWithin_append {B : Basis} {r w T₁ T₂ : ℕ} {c d : Code B r} {x y z : Data r}
    (h₁ : ExecWithin w c x y T₁) (h₂ : ExecWithin w d y z T₂) :
    ExecWithin w (appendCode c d) x z (T₁ + T₂) := by
  induction c generalizing x T₁ with
  | seq c₁ c₂ _ ih =>
    obtain ⟨n, hn, he⟩ := h₁
    cases he with
    | seq he₁ he₂ => exact (he₁.within.seq (ih he₂.within)).mono (by omega)
  | op o => exact h₁.seq h₂
  | branch c pos neg _ _ => exact h₁.seq h₂
  | loop c body _ => exact h₁.seq h₂

/-! ### Heap order with one defect -/

section Order

variable {f g : ℕ → ℕ} {a c : ℕ}

/-- A heap ordered except above `a`, where the parent of `a` is at most `a`, is ordered. -/
private theorem UpOrdered.ordered (h : UpOrdered f S a)
    (hle : 2 ≤ a → a ≤ S → f (a / 2) ≤ f a) : Ordered f S := by
  intro i hi hiS
  by_cases hia : i = a
  · subst hia
    exact hle hi hiS
  · exact (h i hi hiS).1 hia

/-- An ordered heap is ordered except above the root. -/
private theorem Ordered.upOrdered_one (h : Ordered f S) : UpOrdered f S 1 :=
  fun i hi hiS => ⟨fun _ => h i hi hiS, fun _ h2 => absurd h2 (by omega)⟩

/-- **A sift-up step.** Swapping position `a ≥ 2` with its parent of larger key moves the defect
of a sift-up from `a` to its parent. Here `g` is `f` with the values at `a` and `a / 2`
exchanged. -/
private theorem UpOrdered.swap (h : UpOrdered f S a) (ha : 2 ≤ a) (haS : a ≤ S)
    (hlt : f a < f (a / 2)) (hga : g a = f (a / 2)) (hgp : g (a / 2) = f a)
    (hgo : ∀ i, 1 ≤ i → i ≤ S → i ≠ a → i ≠ a / 2 → g i = f i) :
    UpOrdered g S (a / 2) := by
  intro i hi hiS
  obtain ⟨h₁, h₂⟩ := h i hi hiS
  constructor
  · intro hne
    rcases eq_or_ne i a with rfl | hia
    · rw [hga, hgp]
      exact hlt.le
    rw [hgo i (by omega) hiS hia hne]
    rcases eq_or_ne (i / 2) a with hia2 | hia2
    · rw [hia2, hga]
      exact h₂ hia2 ha
    rcases eq_or_ne (i / 2) (a / 2) with hip | hip
    · have := h₁ hia
      rw [hip] at this
      rw [hip, hgp]
      omega
    · rw [hgo (i / 2) (by omega) (by omega) hia2 hip]
      exact h₁ hia
  · intro hip hp2
    have hpa := (h (a / 2) hp2 (by omega)).1 (by omega)
    rw [hgo (a / 2 / 2) (by omega) (by omega) (by omega) (by omega)]
    rcases eq_or_ne i a with rfl | hia
    · rw [hga]
      exact hpa
    · have := h₁ hia
      rw [hip] at this
      rw [hgo i (by omega) hiS hia (by omega)]
      omega

/-- A heap ordered except below `a`, where `a` is at most its children, is ordered. -/
private theorem DownOrdered.ordered (h : DownOrdered f S a)
    (hle : ∀ i, 2 ≤ i → i ≤ S → i / 2 = a → f a ≤ f i) : Ordered f S := by
  intro i hi hiS
  by_cases hia : i / 2 = a
  · rw [hia]
    exact hle i hi hiS hia
  · exact (h i hi hiS).1 hia

/-- **A sift-down step.** Swapping position `a` with its child `c` of least key, when that key is
smaller than the key of `a`, moves the defect of a sift-down from `a` to `c`. Here `g` is `f` with
the values at `a` and `c` exchanged. -/
private theorem DownOrdered.swap (h : DownOrdered f S a) (hc : c / 2 = a) (hcS : c ≤ S)
    (hmin : ∀ i, 2 ≤ i → i ≤ S → i / 2 = a → f c ≤ f i) (hlt : f c < f a)
    (hga : g a = f c) (hgc : g c = f a)
    (hgo : ∀ i, 1 ≤ i → i ≤ S → i ≠ a → i ≠ c → g i = f i) :
    DownOrdered g S c := by
  intro i hi hiS
  obtain ⟨h₁, -⟩ := h i hi hiS
  constructor
  · intro hic
    rcases eq_or_ne i c with rfl | hic'
    · rw [hc, hga, hgc]
      exact hlt.le
    rcases eq_or_ne (i / 2) a with hia | hia
    · rw [hia, hga, hgo i (by omega) hiS (by omega) hic']
      exact hmin i hi hiS hia
    rcases eq_or_ne i a with rfl | hia'
    · rw [hga, hgo (i / 2) (by omega) (by omega) (by omega) hic]
      exact (h c (by omega) hcS).2 hc hi
    · rw [hgo i (by omega) hiS hia' hic', hgo (i / 2) (by omega) (by omega) hia hic]
      exact h₁ hia
  · intro hic _
    have := h₁ (by omega)
    rw [hic] at this
    rw [hc, hga, hgo i (by omega) hiS (by omega) (by omega)]
    exact this

end Order

/-! ### Swapping two heap entries -/

/-- The memory after `swapCode` exchanges the vertices `va` at position `a` and `vb` at position
`b` and updates their positions. -/
private def swapMem (N Db : ℕ) (mem : ℕ → ℕ) (a b va vb : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update mem (Db + N + a) vb)
    (Db + N + b) va) (Db + 2 * N + 1 + vb) a) (Db + 2 * N + 1 + va) b

/-- **Swapping two heap entries** keeps the shape of the heap and the set of vertices in it,
exchanges the keys of the two positions, and changes no memory outside the heap and positions
arrays. -/
private theorem HeapShape.swap {mem : ℕ → ℕ} {a b : ℕ} (h : HeapShape N Db S mem)
    (ha : 1 ≤ a) (haS : a ≤ S) (hb : 1 ≤ b) (hbS : b ≤ S) (hab : a ≠ b) :
    let m' := swapMem N Db mem a b (mem (Db + N + a)) (mem (Db + N + b))
    HeapShape N Db S m' ∧ heapKey N Db m' a = heapKey N Db mem b ∧
      heapKey N Db m' b = heapKey N Db mem a ∧
      (∀ i, 1 ≤ i → i ≤ S → i ≠ a → i ≠ b → heapKey N Db m' i = heapKey N Db mem i) ∧
      (∀ v < N, m' (Db + 2 * N + 1 + v) = 0 ↔ mem (Db + 2 * N + 1 + v) = 0) ∧
      (∀ c, c ≤ Db + N ∨ Db + 3 * N < c → m' c = mem c) := by
  intro m'
  have hSN := h.size_le
  have hva : mem (Db + N + a) < N := h.vertex_lt a ha haS
  have hvb : mem (Db + N + b) < N := h.vertex_lt b hb hbS
  have hpa := h.pos_vertex a ha haS
  have hpb := h.pos_vertex b hb hbS
  have hne : mem (Db + N + a) ≠ mem (Db + N + b) := fun he => hab (by rw [← hpa, ← hpb, he])
  have hH : ∀ i, 1 ≤ i → i ≤ S → m' (Db + N + i) = if i = b then mem (Db + N + a)
      else if i = a then mem (Db + N + b) else mem (Db + N + i) := by
    intro i hi hiS
    simp only [m', swapMem, Function.update_apply]
    split_ifs <;> omega
  have hP : ∀ v < N, m' (Db + 2 * N + 1 + v) = if v = mem (Db + N + a) then b
      else if v = mem (Db + N + b) then a else mem (Db + 2 * N + 1 + v) := by
    intro v hv
    simp only [m', swapMem, Function.update_apply]
    split_ifs <;> omega
  have hD : ∀ c, c ≤ Db + N ∨ Db + 3 * N < c → m' c = mem c := by
    intro c hc
    simp only [m', swapMem, Function.update_apply]
    split_ifs <;> omega
  have hK : ∀ v < N, m' (Db + v) = mem (Db + v) := fun v hv => hD _ (Or.inl (by omega))
  refine ⟨⟨hSN, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hD⟩
  · intro i hi hiS
    rw [hH i hi hiS]
    split_ifs
    exacts [hva, hvb, h.vertex_lt i hi hiS]
  · intro i hi hiS
    rw [hH i hi hiS]
    split_ifs with h1 h2
    · rw [hP _ hva, ite_eq_left rfl, h1]
    · rw [hP _ hvb, ite_eq_right hne.symm, ite_eq_left rfl, h2]
    · have hpi := h.pos_vertex i hi hiS
      have h1' : mem (Db + N + i) ≠ mem (Db + N + a) := fun he => h2 (by rw [← hpi, he, hpa])
      have h2' : mem (Db + N + i) ≠ mem (Db + N + b) := fun he => h1 (by rw [← hpi, he, hpb])
      rw [hP _ (h.vertex_lt i hi hiS), ite_eq_right h1', ite_eq_right h2', hpi]
  · intro v hv
    rw [hP v hv]
    split_ifs
    exacts [hbS, haS, h.pos_le v hv]
  · intro v hv hv0
    rw [hP v hv] at hv0 ⊢
    split_ifs at hv0 ⊢ with h1 h2
    · rw [hH b hb hbS, ite_eq_left rfl, h1]
    · rw [hH a ha haS, ite_eq_right hab, ite_eq_left rfl, h2]
    · have hvp := h.vertex_pos v hv hv0
      have hle := h.pos_le v hv
      have h1' : mem (Db + 2 * N + 1 + v) ≠ b := fun he => h2 (by rw [← hvp, he])
      have h2' : mem (Db + 2 * N + 1 + v) ≠ a := fun he => h1 (by rw [← hvp, he])
      rw [hH _ (by omega) hle, ite_eq_right h1', ite_eq_right h2', hvp]
  · intro v hv hv0
    rw [hK v hv]
    rw [hP v hv] at hv0
    split_ifs at hv0 with h1 h2
    · subst h1
      exact h.key_ne _ hva (by omega)
    · subst h2
      exact h.key_ne _ hvb (by omega)
    · exact h.key_ne v hv hv0
  · simp only [heapKey]
    rw [hH a ha haS, ite_eq_right hab, ite_eq_left rfl, hK _ hvb]
  · simp only [heapKey]
    rw [hH b hb hbS, ite_eq_left rfl, hK _ hva]
  · intro i hi hiS hia hib
    simp only [heapKey]
    rw [hH i hi hiS, ite_eq_right hib, ite_eq_right hia, hK _ (h.vertex_lt i hi hiS)]
  · intro v hv
    rw [hP v hv]
    split_ifs with h1 h2
    · subst h1
      rw [hpa]
      omega
    · subst h2
      rw [hpb]
      omega
    · rfl


/-! ### Sift-up -/

/-- **One sift-up step** from position `K ≥ 2`: if the key at `K` is smaller than the key of its
parent, it swaps the two entries and moves to the parent; otherwise it moves to the root. -/
private theorem siftUpBody_spec {w K : ℕ} {y : Data 27} (hone : y.regs one = 1)
    (htwo : y.regs two = 2) (hdb : y.regs db = Db) (hhb : y.regs hb = Db + N)
    (hpb : y.regs pb = Db + 2 * N + 1) (hk : y.regs k = K) (hK : 2 ≤ K) (hKS : K ≤ S)
    (hfit : Fits w (Db + 3 * N + 1)) (hshape : HeapShape N Db S y.mem) :
    ∃ z, ExecWithin w siftUpBody y z 28 ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t], z.regs i = y.regs i) ∧
      (heapKey N Db y.mem K < heapKey N Db y.mem (K / 2) ∧ z.regs k = K / 2 ∧
        z.mem = swapMem N Db y.mem K (K / 2) (y.mem (Db + N + K)) (y.mem (Db + N + K / 2)) ∨
      ¬heapKey N Db y.mem K < heapKey N Db y.mem (K / 2) ∧ z.regs k = 1 ∧ z.mem = y.mem) := by
  have hSN := hshape.size_le
  obtain ⟨VK, hvk⟩ : ∃ v, y.mem (Db + N + K) = v := ⟨_, rfl⟩
  obtain ⟨VP, hvp⟩ : ∃ v, y.mem (Db + N + K / 2) = v := ⟨_, rfl⟩
  have hVK : VK < N := hvk ▸ hshape.vertex_lt K (by omega) hKS
  have hVP : VP < N := hvp ▸ hshape.vertex_lt (K / 2) (by omega) (by omega)
  have f₁ : Fits w (K / 2) := hfit.of_le (by omega)
  have f₂ : Fits w (Db + N + K) := hfit.of_le (by omega)
  have f₃ : Fits w (Db + N + K / 2) := hfit.of_le (by omega)
  have f₄ : Fits w (Db + VK) := hfit.of_le (by omega)
  have f₅ : Fits w (Db + VP) := hfit.of_le (by omega)
  have f₆ : Fits w (Db + 2 * N + 1 + VK) := hfit.of_le (by omega)
  have f₇ : Fits w (Db + 2 * N + 1 + VP) := hfit.of_le (by omega)
  have hframe : ∀ z T, ExecWithin w siftUpBody y z T →
      ∀ i ∉ [k, p, vk, vp, dk, dp, t], z.regs i = y.regs i := by
    intro z T he i hi
    apply he.regs_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [siftUpBody, swapCode, Code.Preserves, Op.dest, Op.exactBin, eq_comm, hi.1, hi.2.1,
      hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2]
  have hkey : ∀ a, heapKey N Db y.mem a = y.mem (Db + y.mem (Db + N + a)) := fun _ => rfl
  rw [hkey, hkey, hvk, hvp]
  by_cases hlt : y.mem (Db + VK) < y.mem (Db + VP)
  · obtain ⟨z, he, hz⟩ : ∃ z, ExecWithin w siftUpBody y z 28 ∧ z.regs k = K / 2 ∧
        z.mem = swapMem N Db y.mem K (K / 2) VK VP := by
      refine ⟨?z₁, ?e₁, ?_, ?_⟩
      case e₁ =>
        ram_exact_eval [siftUpBody, swapCode, hone, htwo, hdb, hhb, hpb, hk, hvk, hvp, f₁, f₂, f₃,
          f₄, f₅, f₆, f₇, hlt]
      · simp
      · simp [swapMem]
    exact ⟨z, he, hframe z _ he, Or.inl ⟨hlt, hz⟩⟩
  · obtain ⟨z, he, hz⟩ : ∃ z, ExecWithin w siftUpBody y z 28 ∧ z.regs k = 1 ∧
        z.mem = y.mem := by
      refine ⟨?z₂, ?e₂, ?_, ?_⟩
      case e₂ =>
        ram_exact_eval [siftUpBody, swapCode, hone, htwo, hdb, hhb, hpb, hk, hvk, hvp, f₁, f₂, f₃,
          f₄, f₅, f₆, f₇, hlt]
      · simp
      · simp
    exact ⟨z, he, hframe z _ he, Or.inr ⟨hlt, hz⟩⟩

/-- The invariant of the sift-up loop started from the data `x`. -/
private structure UpInv (N Db S : ℕ) (x y : Data 27) : Prop where
  /-- Only the registers of the sift-up change. -/
  frame : ∀ i ∉ [k, p, vk, vp, dk, dp, t], y.regs i = x.regs i
  /-- The position is in the heap. -/
  one_le : 1 ≤ y.regs k
  /-- The position is in the heap. -/
  le_size : y.regs k ≤ S
  /-- The heap keeps its shape. -/
  shape : HeapShape N Db S y.mem
  /-- The heap is ordered except above the position. -/
  ordered : UpOrdered (heapKey N Db y.mem) S (y.regs k)
  /-- The heap keeps its vertices. -/
  pos : ∀ v < N, y.mem (Db + 2 * N + 1 + v) = 0 ↔ x.mem (Db + 2 * N + 1 + v) = 0
  /-- Memory outside the heap and positions arrays is unchanged. -/
  outside : ∀ a, a ≤ Db + N ∨ Db + 3 * N < a → y.mem a = x.mem a

/-- **Sift-up.** From a heap ordered except between position `K` and its parent, the sift-up
runs within `30 ⌊log₂ K⌋ + 2` instructions, writes only the registers `k`, `p`, `vk`, `vp`, `dk`,
`dp`, `t` and the heap and positions arrays, and leaves a heap with the same vertices. -/
theorem siftUp_spec {w K : ℕ} {x : Data 27} (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hdb : x.regs db = Db) (hhb : x.regs hb = Db + N) (hpb : x.regs pb = Db + 2 * N + 1)
    (hk : x.regs k = K) (hK : 1 ≤ K) (hKS : K ≤ S) (hfit : Fits w (Db + 3 * N + 1))
    (hshape : HeapShape N Db S x.mem) (hord : UpOrdered (heapKey N Db x.mem) S K) :
    ∃ y, ExecWithin w siftUp x y (30 * Nat.log 2 K + 2) ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t], y.regs i = x.regs i) ∧
      HeapInv N Db S y.mem ∧
      (∀ v < N, y.mem (Db + 2 * N + 1 + v) = 0 ↔ x.mem (Db + 2 * N + 1 + v) = 0) ∧
      (∀ a, a ≤ Db + N ∨ Db + 3 * N < a → y.mem a = x.mem a) := by
  have hinit : UpInv N Db S x x :=
    ⟨fun _ _ => rfl, hk ▸ hK, hk ▸ hKS, hshape, hk ▸ hord, fun _ _ => Iff.rfl, fun _ _ => rfl⟩
  have hbody : ∀ y, UpInv N Db S x y → (Cond.lt one k).Holds y →
      ∃ z, ExecWithin w siftUpBody y z 28 ∧ UpInv N Db S x z ∧
        Nat.log 2 (z.regs k) < Nat.log 2 (y.regs k) := by
    intro y hy hc
    have ho : y.regs one = 1 := (hy.frame one (by decide)).trans hone
    have hK2 : 2 ≤ y.regs k := by
      simp only [Cond.holds_lt, ho] at hc
      omega
    have hlog : 0 < Nat.log 2 (y.regs k) := Nat.log_pos (by norm_num) hK2
    have hle := hy.le_size
    obtain ⟨z, he, hfr, hz⟩ := siftUpBody_spec ho ((hy.frame two (by decide)).trans htwo)
      ((hy.frame db (by decide)).trans hdb) ((hy.frame hb (by decide)).trans hhb)
      ((hy.frame pb (by decide)).trans hpb) rfl hK2 hy.le_size hfit hy.shape
    have hfr' : ∀ i ∉ [k, p, vk, vp, dk, dp, t], z.regs i = x.regs i :=
      fun i hi => (hfr i hi).trans (hy.frame i hi)
    rcases hz with ⟨hlt, hzk, hzm⟩ | ⟨hlt, hzk, hzm⟩
    · obtain ⟨hs, hga, hgb, hgo, hpos, hout⟩ := HeapShape.swap hy.shape (a := y.regs k)
        (b := y.regs k / 2) (by omega) hy.le_size (by omega) (by omega) (by omega)
      rw [← hzm] at hs hga hgb hgo hpos hout
      refine ⟨z, he, ⟨hfr', by omega, by omega, hs, ?_, ?_, ?_⟩, ?_⟩
      · rw [hzk]
        exact hy.ordered.swap hK2 hy.le_size hlt hga hgb hgo
      · intro v hv
        rw [hpos v hv]
        exact hy.pos v hv
      · intro a ha
        rw [hout a ha]
        exact hy.outside a ha
      · rw [hzk, Nat.log_div_base]
        omega
    · refine ⟨z, he, ⟨hfr', by omega, by omega, hzm ▸ hy.shape, ?_, ?_, ?_⟩, ?_⟩
      · rw [hzk, hzm]
        exact (hy.ordered.ordered (fun _ _ => not_lt.1 hlt)).upOrdered_one
      · intro v hv
        rw [hzm]
        exact hy.pos v hv
      · intro a ha
        rw [hzm]
        exact hy.outside a ha
      · rw [hzk, Nat.log_one_right]
        exact hlog
  obtain ⟨y, he, hy, hexit⟩ := ExecWithin.loop_invariant (cond := .lt one k)
    (body := siftUpBody) (UpInv N Db S x) (fun y => Nat.log 2 (y.regs k)) hbody hinit
  have ho : y.regs one = 1 := (hy.frame one (by decide)).trans hone
  have hk1 : y.regs k = 1 := by
    have := hy.one_le
    simp only [Cond.holds_lt, ho] at hexit
    omega
  refine ⟨y, he.mono (by rw [hk]; omega), hy.frame, ⟨hy.shape, ?_⟩, hy.pos, hy.outside⟩
  have hord' := hy.ordered
  rw [hk1] at hord'
  exact hord'.ordered (fun h => absurd h (by omega))

/-! ### Sift-down -/

/-- The child of position `a` of least key, for a position `a` with a child in a heap of `S`
entries with keys `f`: the right child `2 a + 1` if it is in the heap and has the smaller key,
and otherwise the left child `2 a`. -/
private def minChild (f : ℕ → ℕ) (S a : ℕ) : ℕ :=
  if 2 * a + 1 ≤ S ∧ f (2 * a + 1) < f (2 * a) then 2 * a + 1 else 2 * a

/-- The child of least key is a child in the heap, and its key is at most the keys of the
children of `a`. -/
private theorem minChild_spec {f : ℕ → ℕ} {a : ℕ} (ha : 2 * a ≤ S) :
    (minChild f S a = 2 * a ∨ minChild f S a = 2 * a + 1) ∧ minChild f S a ≤ S ∧
      ∀ i, i ≤ S → i / 2 = a → f (minChild f S a) ≤ f i := by
  unfold minChild
  split_ifs with h
  · refine ⟨Or.inr rfl, h.1, fun i hiS hia => ?_⟩
    rcases (by omega : i = 2 * a ∨ i = 2 * a + 1) with rfl | rfl
    · exact h.2.le
    · exact le_rfl
  · refine ⟨Or.inl rfl, ha, fun i hiS hia => ?_⟩
    rcases (by omega : i = 2 * a ∨ i = 2 * a + 1) with rfl | rfl
    · exact le_rfl
    · exact not_lt.1 fun hlt => h ⟨hiS, hlt⟩

/-- The first half of `siftDownBody`: it picks the child of least key. -/
private def chooseCode : Code .exact 27 := ram_exact[
  p ← l;
  t ← hb + l; vp ← *t; t ← db + vp; dp ← *t;
  t ← l + one;
  if t < szp then [
    t ← hb + t; vk ← *t; t ← db + vk; dk ← *t;
    if dk < dp then [ p ← l + one; vp ← vk; dp ← dk ] else [ p ← p ] ] else [ p ← p ] ]

/-- The second half of `siftDownBody`: it swaps with the chosen child if that has the smaller
key, and stops otherwise. -/
private def sinkCode : Code .exact 27 := ram_exact[
  t ← hb + k; vk ← *t; t ← db + vk; dk ← *t;
  if dp < dk then [ ⟪swapCode⟫; k ← p; l ← k + k ] else [ l ← szp ] ]

/-- `siftDownBody` is `chooseCode` followed by `sinkCode`. -/
private theorem siftDownBody_eq : siftDownBody = appendCode chooseCode sinkCode := rfl

/-- `chooseCode` leaves the child of least key of position `K` in `p`, its vertex in `vp` and
its key in `dp`. -/
private theorem chooseCode_spec {w K : ℕ} {y : Data 27} (hone : y.regs one = 1)
    (hdb : y.regs db = Db) (hhb : y.regs hb = Db + N) (hl : y.regs l = 2 * K)
    (hszp : y.regs szp = S + 1) (hK : 1 ≤ K) (hKS : 2 * K ≤ S) (hfit : Fits w (Db + 3 * N + 1))
    (hshape : HeapShape N Db S y.mem) :
    ∃ z, ExecWithin w chooseCode y z 15 ∧
      (∀ i ∉ [p, t, vp, dp, vk, dk], z.regs i = y.regs i) ∧ z.mem = y.mem ∧
      z.regs p = minChild (heapKey N Db y.mem) S K ∧
      z.regs vp = y.mem (Db + N + minChild (heapKey N Db y.mem) S K) ∧
      z.regs dp = heapKey N Db y.mem (minChild (heapKey N Db y.mem) S K) := by
  have hSN := hshape.size_le
  obtain ⟨VL, hvl⟩ : ∃ v, y.mem (Db + N + 2 * K) = v := ⟨_, rfl⟩
  have hVL : VL < N := hvl ▸ hshape.vertex_lt (2 * K) (by omega) hKS
  have f₁ : Fits w (Db + N + 2 * K) := hfit.of_le (by omega)
  have f₂ : Fits w (Db + VL) := hfit.of_le (by omega)
  have f₃ : Fits w (2 * K + 1) := hfit.of_le (by omega)
  have hframe : ∀ z T, ExecWithin w chooseCode y z T →
      ∀ i ∉ [p, t, vp, dp, vk, dk], z.regs i = y.regs i := by
    intro z T he i hi
    apply he.regs_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [chooseCode, Code.Preserves, Op.dest, Op.exactBin, eq_comm, hi.1, hi.2.1,
      hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2]
  have hkey : ∀ a, heapKey N Db y.mem a = y.mem (Db + y.mem (Db + N + a)) := fun _ => rfl
  by_cases h₁ : 2 * K + 1 < S + 1
  · obtain ⟨VR, hvr⟩ : ∃ v, y.mem (Db + N + (2 * K + 1)) = v := ⟨_, rfl⟩
    have hVR : VR < N := hvr ▸ hshape.vertex_lt (2 * K + 1) (by omega) (by omega)
    have f₄ : Fits w (Db + N + (2 * K + 1)) := hfit.of_le (by omega)
    have f₅ : Fits w (Db + VR) := hfit.of_le (by omega)
    by_cases h₂ : y.mem (Db + VR) < y.mem (Db + VL)
    · have hC : minChild (heapKey N Db y.mem) S K = 2 * K + 1 := by
        unfold minChild
        exact ite_eq_left ⟨by omega, by rw [hkey, hkey, hvl, hvr]; exact h₂⟩
      rw [hC, hkey, hvr]
      obtain ⟨z, he, hz⟩ : ∃ z, ExecWithin w chooseCode y z 15 ∧ z.mem = y.mem ∧
          z.regs p = 2 * K + 1 ∧ z.regs vp = VR ∧ z.regs dp = y.mem (Db + VR) := by
        refine ⟨?z₁, ?e₁, ?_, ?_, ?_, ?_⟩
        case e₁ =>
          ram_exact_eval [chooseCode, hone, hdb, hhb, hl, hszp, hvl, hvr, f₁, f₂, f₃, f₄, f₅, h₁,
            h₂]
        all_goals simp +decide
      exact ⟨z, he, hframe z _ he, hz⟩
    · have hC : minChild (heapKey N Db y.mem) S K = 2 * K := by
        unfold minChild
        exact ite_eq_right fun h => h₂ (by rw [hkey, hkey, hvl, hvr] at h; exact h.2)
      rw [hC, hkey, hvl]
      obtain ⟨z, he, hz⟩ : ∃ z, ExecWithin w chooseCode y z 15 ∧ z.mem = y.mem ∧
          z.regs p = 2 * K ∧ z.regs vp = VL ∧ z.regs dp = y.mem (Db + VL) := by
        refine ⟨?z₂, ?e₂, ?_, ?_, ?_, ?_⟩
        case e₂ =>
          ram_exact_eval [chooseCode, hone, hdb, hhb, hl, hszp, hvl, hvr, f₁, f₂, f₃, f₄, f₅, h₁,
            h₂]
        all_goals simp +decide
      exact ⟨z, he, hframe z _ he, hz⟩
  · have hC : minChild (heapKey N Db y.mem) S K = 2 * K := by
      unfold minChild
      exact ite_eq_right fun h => h₁ (by omega)
    rw [hC, hkey, hvl]
    obtain ⟨z, he, hz⟩ : ∃ z, ExecWithin w chooseCode y z 15 ∧ z.mem = y.mem ∧
        z.regs p = 2 * K ∧ z.regs vp = VL ∧ z.regs dp = y.mem (Db + VL) := by
      refine ⟨?z₃, ?e₃, ?_, ?_, ?_, ?_⟩
      case e₃ =>
        ram_exact_eval [chooseCode, hone, hdb, hhb, hl, hszp, hvl, f₁, f₂, f₃, h₁]
      all_goals simp +decide
    exact ⟨z, he, hframe z _ he, hz⟩

/-- `sinkCode` swaps position `K` with the position `C` in `p` if the key in `dp` is smaller
than the key at `K`, and moves to `C`; otherwise it stops the sift-down. -/
private theorem sinkCode_spec {w K C : ℕ} {y : Data 27} (hdb : y.regs db = Db)
    (hhb : y.regs hb = Db + N) (hpb : y.regs pb = Db + 2 * N + 1) (hk : y.regs k = K)
    (hp : y.regs p = C) (hvp : y.regs vp = y.mem (Db + N + C)) (hszp : y.regs szp = S + 1)
    (hK : 1 ≤ K) (hKS : K ≤ S) (hC : 1 ≤ C) (hCS : C ≤ S) (hfit : Fits w (Db + 3 * N + 1))
    (hshape : HeapShape N Db S y.mem) :
    ∃ z, ExecWithin w sinkCode y z 15 ∧ (∀ i ∉ [t, vk, dk, k, l], z.regs i = y.regs i) ∧
      (y.regs dp < heapKey N Db y.mem K ∧ z.regs k = C ∧ z.regs l = 2 * C ∧
        z.mem = swapMem N Db y.mem K C (y.mem (Db + N + K)) (y.mem (Db + N + C)) ∨
      ¬y.regs dp < heapKey N Db y.mem K ∧ z.regs k = K ∧ z.regs l = S + 1 ∧
        z.mem = y.mem) := by
  have hSN := hshape.size_le
  obtain ⟨VK, hvk⟩ : ∃ v, y.mem (Db + N + K) = v := ⟨_, rfl⟩
  obtain ⟨VC, hvc⟩ : ∃ v, y.mem (Db + N + C) = v := ⟨_, rfl⟩
  rw [hvc] at hvp
  have hVK : VK < N := hvk ▸ hshape.vertex_lt K hK hKS
  have hVC : VC < N := hvc ▸ hshape.vertex_lt C hC hCS
  have f₁ : Fits w (Db + N + K) := hfit.of_le (by omega)
  have f₂ : Fits w (Db + VK) := hfit.of_le (by omega)
  have f₃ : Fits w (Db + N + C) := hfit.of_le (by omega)
  have f₄ : Fits w (Db + 2 * N + 1 + VK) := hfit.of_le (by omega)
  have f₅ : Fits w (Db + 2 * N + 1 + VC) := hfit.of_le (by omega)
  have f₆ : Fits w (C + C) := hfit.of_le (by omega)
  have hframe : ∀ z T, ExecWithin w sinkCode y z T →
      ∀ i ∉ [t, vk, dk, k, l], z.regs i = y.regs i := by
    intro z T he i hi
    apply he.regs_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [sinkCode, swapCode, Code.Preserves, Op.dest, Op.exactBin, eq_comm, hi.1, hi.2.1,
      hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2]
  have hkey : heapKey N Db y.mem K = y.mem (Db + VK) := by simp only [heapKey, hvk]
  rw [hkey, hvk, hvc]
  by_cases hlt : y.regs dp < y.mem (Db + VK)
  · obtain ⟨z, he, hz⟩ : ∃ z, ExecWithin w sinkCode y z 15 ∧ z.regs k = C ∧
        z.regs l = 2 * C ∧ z.mem = swapMem N Db y.mem K C VK VC := by
      refine ⟨?z₁, ?e₁, ?_, ?_, ?_⟩
      case e₁ =>
        ram_exact_eval [sinkCode, swapCode, hdb, hhb, hpb, hk, hp, hvp, hszp, hvk, f₁, f₂, f₃, f₄,
          f₅, f₆, hlt]
      · simp +decide
      · simp only [Data.set_regs, Data.write_regs, Function.update_idem, Function.update_self]
        omega
      · simp [swapMem]
    exact ⟨z, he, hframe z _ he, Or.inl ⟨hlt, hz⟩⟩
  · obtain ⟨z, he, hz⟩ : ∃ z, ExecWithin w sinkCode y z 15 ∧ z.regs k = K ∧
        z.regs l = S + 1 ∧ z.mem = y.mem := by
      refine ⟨?z₂, ?e₂, ?_, ?_, ?_⟩
      case e₂ =>
        ram_exact_eval [sinkCode, swapCode, hdb, hhb, hpb, hk, hp, hvp, hszp, hvk, f₁, f₂, hlt]
      · simp +decide [hk]
      · simp +decide
      · simp
    exact ⟨z, he, hframe z _ he, Or.inr ⟨hlt, hz⟩⟩

/-- One round of the sift-down at position `K` with a child in the heap: with `C` the child of
least key, it swaps `K` with `C` and moves to `C` if `C` has the smaller key, and otherwise it
stops the sift-down. -/
private theorem siftDownBody_spec {w K C : ℕ} {y : Data 27} (hone : y.regs one = 1)
    (hdb : y.regs db = Db) (hhb : y.regs hb = Db + N) (hpb : y.regs pb = Db + 2 * N + 1)
    (hk : y.regs k = K) (hl : y.regs l = 2 * K) (hszp : y.regs szp = S + 1) (hK : 1 ≤ K)
    (hKS : 2 * K ≤ S) (hfit : Fits w (Db + 3 * N + 1)) (hshape : HeapShape N Db S y.mem)
    (hC : C = minChild (heapKey N Db y.mem) S K) :
    ∃ z, ExecWithin w siftDownBody y z 30 ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t, l], z.regs i = y.regs i) ∧
      (heapKey N Db y.mem C < heapKey N Db y.mem K ∧ z.regs k = C ∧ z.regs l = 2 * C ∧
        z.mem = swapMem N Db y.mem K C (y.mem (Db + N + K)) (y.mem (Db + N + C)) ∨
      ¬heapKey N Db y.mem C < heapKey N Db y.mem K ∧ z.regs k = K ∧ z.regs l = S + 1 ∧
        z.mem = y.mem) := by
  obtain ⟨z₁, he₁, hfr₁, hm₁, hp₁, hvp₁, hdp₁⟩ :=
    chooseCode_spec hone hdb hhb hl hszp hK hKS hfit hshape
  rw [← hC] at hp₁ hvp₁ hdp₁
  obtain ⟨hCc, hCS, -⟩ := minChild_spec (f := heapKey N Db y.mem) hKS
  rw [← hC] at hCc hCS
  have hr : ∀ i ∉ [p, t, vp, dp, vk, dk], z₁.regs i = y.regs i := hfr₁
  obtain ⟨z, he₂, hfr₂, hz⟩ := sinkCode_spec (y := z₁) (K := K) (C := C)
    ((hr db (by decide)).trans hdb) ((hr hb (by decide)).trans hhb)
    ((hr pb (by decide)).trans hpb) ((hr k (by decide)).trans hk) hp₁ (hm₁ ▸ hvp₁)
    ((hr szp (by decide)).trans hszp) hK (by omega) (by omega) hCS hfit (hm₁ ▸ hshape)
  rw [hdp₁, hm₁] at hz
  refine ⟨z, ?_, fun i hi => ?_, hz⟩
  · rw [siftDownBody_eq]
    exact (execWithin_append he₁ he₂).mono (by norm_num)
  · refine (hfr₂ i fun h => hi ?_).trans (hr i fun h => hi ?_) <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto

/-- The invariant of the sift-down loop started from the data `x`. -/
private structure DownInv (N Db S : ℕ) (x y : Data 27) : Prop where
  /-- Only the registers of the sift-down change. -/
  frame : ∀ i ∉ [k, p, vk, vp, dk, dp, t, l, szp], y.regs i = x.regs i
  /-- The register `szp` holds `S + 1`. -/
  size_reg : y.regs szp = S + 1
  /-- The position is in the heap. -/
  one_le : 1 ≤ y.regs k
  /-- The position is in the heap. -/
  le_size : y.regs k ≤ S
  /-- The heap keeps its shape. -/
  shape : HeapShape N Db S y.mem
  /-- Either the sift-down goes on at `k`, with `l = 2 k`, and the heap is ordered except below
  `k`, or it has stopped, with `l = S + 1`, and the heap is ordered. -/
  order : y.regs l = 2 * y.regs k ∧ DownOrdered (heapKey N Db y.mem) S (y.regs k) ∨
    y.regs l = S + 1 ∧ Ordered (heapKey N Db y.mem) S
  /-- The heap keeps its vertices. -/
  pos : ∀ v < N, y.mem (Db + 2 * N + 1 + v) = 0 ↔ x.mem (Db + 2 * N + 1 + v) = 0
  /-- Memory outside the heap and positions arrays is unchanged. -/
  outside : ∀ a, a ≤ Db + N ∨ Db + 3 * N < a → y.mem a = x.mem a

/-- The set-up of the sift-down loop. -/
private def downSetup : Code .exact 27 := ram_exact[ l ← k + k; szp ← sz + one ]

/-- `siftDown` is `downSetup` followed by the loop. -/
private theorem siftDown_eq :
    siftDown = appendCode downSetup (.loop (.lt l szp) siftDownBody) := rfl

/-- The measure of the sift-down loop: the number of rounds left is at most this. -/
private def downMeasure (S : ℕ) (y : Data 27) : ℕ :=
  if y.regs l < S + 1 then Nat.log 2 (S + 1) + 1 - Nat.log 2 (y.regs l) else 0

/-- **Sift-down.** From a heap of `S` entries ordered except between position `K` and its
children, the sift-down runs within `45 ⌊log₂ (S + 1)⌋ + 4` instructions, writes only the
registers `k`, `p`, `vk`, `vp`, `dk`, `dp`, `t`, `l`, `szp` and the heap and positions arrays, and
leaves a heap with the same vertices. -/
theorem siftDown_spec {w K : ℕ} {x : Data 27} (hone : x.regs one = 1)
    (hdb : x.regs db = Db) (hhb : x.regs hb = Db + N) (hpb : x.regs pb = Db + 2 * N + 1)
    (hsz : x.regs sz = S) (hk : x.regs k = K) (hK : 1 ≤ K) (hKS : K ≤ S)
    (hfit : Fits w (Db + 3 * N + 1))
    (hshape : HeapShape N Db S x.mem) (hord : DownOrdered (heapKey N Db x.mem) S K) :
    ∃ y, ExecWithin w siftDown x y (45 * Nat.log 2 (S + 1) + 4) ∧
      (∀ i ∉ [k, p, vk, vp, dk, dp, t, l, szp], y.regs i = x.regs i) ∧
      HeapInv N Db S y.mem ∧
      (∀ v < N, y.mem (Db + 2 * N + 1 + v) = 0 ↔ x.mem (Db + 2 * N + 1 + v) = 0) ∧
      (∀ a, a ≤ Db + N ∨ Db + 3 * N < a → y.mem a = x.mem a) := by
  have hSN := hshape.size_le
  have f₁ : Fits w (K + K) := hfit.of_le (by omega)
  have f₂ : Fits w (S + 1) := hfit.of_le (by omega)
  obtain ⟨x₁, he₁, hx₁l, hx₁s, hx₁m, hx₁r⟩ : ∃ x₁, ExecWithin w downSetup x x₁ 2 ∧
      x₁.regs l = 2 * K ∧ x₁.regs szp = S + 1 ∧ x₁.mem = x.mem ∧
      ∀ i, i ≠ l → i ≠ szp → x₁.regs i = x.regs i := by
    refine ⟨?z₀, ?e₀, ?_, ?_, ?_, ?_⟩
    case e₀ => ram_exact_eval [downSetup, hone, hk, hsz, f₁, f₂]
    · simp +decide only [Data.set_regs, ne_eq, Function.update_of_ne, Function.update_self]
      omega
    · simp
    · rfl
    · intro i h₁ h₂
      simp [h₁, h₂]
  have hx₁k : x₁.regs k = K := (hx₁r k (by decide) (by decide)).trans hk
  have hinit : DownInv N Db S x x₁ := by
    refine ⟨fun i hi => hx₁r i ?_ ?_, hx₁s, hx₁k ▸ hK, hx₁k ▸ hKS, hx₁m ▸ hshape,
      Or.inl ⟨by rw [hx₁l, hx₁k], by rw [hx₁m, hx₁k]; exact hord⟩, fun _ _ => by rw [hx₁m],
      fun _ _ => by rw [hx₁m]⟩
    · rintro rfl
      simp at hi
    · rintro rfl
      simp at hi
  have hbody : ∀ y, DownInv N Db S x y → (Cond.lt l szp).Holds y →
      ∃ z, ExecWithin w siftDownBody y z 30 ∧ DownInv N Db S x z ∧
        downMeasure S z < downMeasure S y := by
    intro y hy hc
    have hr : ∀ i ∉ [k, p, vk, vp, dk, dp, t, l, szp], y.regs i = x.regs i := hy.frame
    have hsz' := hy.size_reg
    have hk1 := hy.one_le
    have hkS := hy.le_size
    simp only [Cond.holds_lt, hsz'] at hc
    obtain ⟨hl, hdo⟩ : y.regs l = 2 * y.regs k ∧ DownOrdered (heapKey N Db y.mem) S (y.regs k) :=
      hy.order.resolve_right fun h => by omega
    obtain ⟨C, hC⟩ : ∃ C, C = minChild (heapKey N Db y.mem) S (y.regs k) := ⟨_, rfl⟩
    obtain ⟨hCc, hCS, hmin⟩ := minChild_spec (S := S) (f := heapKey N Db y.mem)
      (a := y.regs k) (by omega)
    rw [← hC] at hCc hCS hmin
    obtain ⟨z, he, hfr, hz⟩ := siftDownBody_spec (hr one (by decide) ▸ hone)
      (hr db (by decide) ▸ hdb) (hr hb (by decide) ▸ hhb) (hr pb (by decide) ▸ hpb) rfl hl hsz'
      hk1 (by omega) hfit hy.shape hC
    have hfr' : ∀ i ∉ [k, p, vk, vp, dk, dp, t, l, szp], z.regs i = x.regs i := by
      intro i hi
      refine (hfr i fun h => hi ?_).trans (hr i hi)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto
    have hzs : z.regs szp = S + 1 := (hfr szp (by decide)).trans hsz'
    have hlog : Nat.log 2 (y.regs l) ≤ Nat.log 2 (S + 1) := Nat.log_mono_right (by omega)
    have hμ : downMeasure S y = Nat.log 2 (S + 1) + 1 - Nat.log 2 (y.regs l) := by
      simp only [downMeasure]
      exact ite_eq_left hc
    rcases hz with ⟨hlt, hzk, hzl, hzm⟩ | ⟨hlt, hzk, hzl, hzm⟩
    · obtain ⟨hs, hga, hgb, hgo, hpos, hout⟩ := HeapShape.swap hy.shape (a := y.regs k)
        (b := C) hk1 hkS (by omega) hCS (by omega)
      rw [← hzm] at hs hga hgb hgo hpos hout
      refine ⟨z, he, ⟨hfr', hzs, by omega, by omega, hs, Or.inl ⟨by rw [hzl, hzk], ?_⟩, ?_, ?_⟩,
        ?_⟩
      · rw [hzk]
        exact hdo.swap (by omega) hCS (fun i _ hiS hia => hmin i hiS hia) hlt hga hgb hgo
      · intro v hv
        rw [hpos v hv]
        exact hy.pos v hv
      · intro a ha
        rw [hout a ha]
        exact hy.outside a ha
      · have h₁ : Nat.log 2 (y.regs l) ≤ Nat.log 2 C := Nat.log_mono_right (by omega)
        have h₂ : Nat.log 2 (z.regs l) = Nat.log 2 C + 1 := by
          rw [hzl, mul_comm]
          exact Nat.log_mul_base (by norm_num) (by omega)
        rw [hμ]
        simp only [downMeasure]
        split_ifs with h₃
        · have : Nat.log 2 (z.regs l) ≤ Nat.log 2 (S + 1) := Nat.log_mono_right (by omega)
          omega
        · omega
    · refine ⟨z, he, ⟨hfr', hzs, by omega, by omega, hzm ▸ hy.shape, Or.inr ⟨hzl, ?_⟩, ?_, ?_⟩,
        ?_⟩
      · rw [hzm]
        exact hdo.ordered fun i _ hiS hia => (not_lt.1 hlt).trans (hmin i hiS hia)
      · intro v hv
        rw [hzm]
        exact hy.pos v hv
      · intro a ha
        rw [hzm]
        exact hy.outside a ha
      · rw [hμ]
        simp only [downMeasure, hzl, lt_irrefl, ite_false]
        omega
  obtain ⟨y, he, hy, hexit⟩ := ExecWithin.loop_invariant (cond := .lt l szp)
    (body := siftDownBody) (DownInv N Db S x) (downMeasure S) hbody hinit
  have hμ : downMeasure S x₁ ≤ Nat.log 2 (S + 1) := by
    simp only [downMeasure, hx₁l]
    split_ifs with h
    · have : Nat.log 2 (2 * K) = Nat.log 2 K + 1 := by
        rw [mul_comm]
        exact Nat.log_mul_base (by norm_num) (by omega)
      omega
    · omega
  refine ⟨y, ?_, hy.frame, ⟨hy.shape, ?_⟩, hy.pos, hy.outside⟩
  · rw [siftDown_eq]
    refine (execWithin_append he₁ he).mono ?_
    have := Nat.mul_le_mul_right 32 hμ
    omega
  · have := hy.size_reg
    simp only [Cond.holds_lt, this] at hexit
    rcases hy.order with ⟨hl, hdo⟩ | ⟨-, hord'⟩
    · exact hdo.ordered fun i _ hiS hia => absurd hiS (by omega)
    · exact hord'

/-! ### Extract-min -/

/-- The part of `extractMin` before its test: it reads the root and removes it from the
positions array, reads the last entry and shrinks the heap. -/
private def extractHead : Code .exact 27 := ram_exact[
  t ← hb + one; u ← *t; t ← db + u; best ← *t;
  t ← pb + u; *t ← zero;
  t ← hb + sz; vk ← *t; sz ← sz - one ]

/-- The part of `extractMin` that moves the last entry to the root, before the sift-down. -/
private def extractMove : Code .exact 27 := ram_exact[
  t ← hb + one; *t ← vk; t ← pb + vk; *t ← one; k ← one ]

/-- The part of `extractMin` run when the heap becomes empty. -/
private def extractStop : Code .exact 27 := ram_exact[ k ← k ]

/-- `extractMin` is `extractHead` followed by the test on the new size. -/
private theorem extractMin_eq : extractMin = appendCode extractHead
    (.branch (.lt zero sz) (appendCode extractMove siftDown) extractStop) := rfl

/-- **Extract-min.** From a heap of `S ≥ 1` entries, the removal of the root runs within
`45 ⌊log₂ S⌋ + 20` instructions. It leaves the root vertex in `u` and its key in `best`, and a
heap of `S - 1` entries that holds the vertices of the old heap but the root. -/
theorem extractMin_spec {w : ℕ} {x : Data 27} (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hdb : x.regs db = Db) (hhb : x.regs hb = Db + N) (hpb : x.regs pb = Db + 2 * N + 1)
    (hsz : x.regs sz = S) (hS : 1 ≤ S) (hfit : Fits w (Db + 3 * N + 1))
    (hheap : HeapInv N Db S x.mem) :
    ∃ y, ExecWithin w extractMin x y (45 * Nat.log 2 S + 20) ∧
      (∀ i ∉ [t, u, best, vk, sz, k, p, vp, dk, dp, l, szp], y.regs i = x.regs i) ∧
      y.regs u = x.mem (Db + N + 1) ∧ y.regs best = x.mem (Db + x.mem (Db + N + 1)) ∧
      y.regs sz = S - 1 ∧ HeapInv N Db (S - 1) y.mem ∧
      (∀ v < N, y.mem (Db + 2 * N + 1 + v) = 0 ↔
        x.mem (Db + 2 * N + 1 + v) = 0 ∨ v = x.mem (Db + N + 1)) ∧
      (∀ a, a ≤ Db + N ∨ Db + 3 * N < a → y.mem a = x.mem a) := by
  have hSN := hheap.size_le
  obtain ⟨U, hU⟩ : ∃ v, x.mem (Db + N + 1) = v := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ v, x.mem (Db + N + S) = v := ⟨_, rfl⟩
  have hUN : U < N := hU ▸ hheap.vertex_lt 1 le_rfl hS
  have hLN : L < N := hL ▸ hheap.vertex_lt S hS le_rfl
  rw [hU]
  have f₁ : Fits w (Db + N + 1) := hfit.of_le (by omega)
  have f₂ : Fits w (Db + U) := hfit.of_le (by omega)
  have f₃ : Fits w (Db + 2 * N + 1 + U) := hfit.of_le (by omega)
  have f₄ : Fits w (Db + N + S) := hfit.of_le (by omega)
  have f₅ : Fits w (S - 1) := hfit.of_le (by omega)
  have hne : ¬Db + N + S = Db + 2 * N + 1 + U := by omega
  obtain ⟨x₁, he₁, hx₁u, hx₁b, hx₁v, hx₁s, hx₁m, hx₁r⟩ : ∃ x₁, ExecWithin w extractHead x x₁ 9 ∧
      x₁.regs u = U ∧ x₁.regs best = x.mem (Db + U) ∧ x₁.regs vk = L ∧ x₁.regs sz = S - 1 ∧
      x₁.mem = Function.update x.mem (Db + 2 * N + 1 + U) 0 ∧
      ∀ i ∉ [t, u, best, vk, sz], x₁.regs i = x.regs i := by
    refine ⟨?z₀, ?e₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case e₀ =>
      ram_exact_eval [extractHead, hzero, hone, hdb, hhb, hpb, hsz, hU, hL, hne, hS, f₁, f₂, f₃,
        f₄, f₅]
    · simp +decide
    · simp +decide
    · simp +decide
    · simp +decide
    · simp
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp [hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2]
  have hr₁ : ∀ i ∉ [t, u, best, vk, sz], x₁.regs i = x.regs i := hx₁r
  have hU₀ : Function.update x.mem (Db + 2 * N + 1 + U) 0 (Db + N + 1) = U := by
    rw [Function.update_of_ne (by omega), hU]
  have hout₁ : ∀ a, a ≤ Db + N ∨ Db + 3 * N < a → x₁.mem a = x.mem a := by
    intro a ha
    rw [hx₁m, Function.update_of_ne (by omega)]
  have hframe : ∀ (L₁ L₂ : List (Fin 27)), (∀ i ∈ L₁, i ∈ L₂) → ∀ i ∉ L₂, i ∉ L₁ :=
    fun _ _ h i hi hi' => hi (h i hi')
  by_cases hS2 : 2 ≤ S
  · obtain ⟨hs, hdo, hpos⟩ := hheap.extract hS2
    rw [hU, hL] at hs hdo hpos
    have f₆ : Fits w (Db + 2 * N + 1 + L) := hfit.of_le (by omega)
    obtain ⟨x₂, he₂, hx₂k, hx₂m, hx₂r⟩ : ∃ x₂, ExecWithin w extractMove x₁ x₂ 5 ∧
        x₂.regs k = 1 ∧ x₂.mem = Function.update (Function.update
          (Function.update x.mem (Db + 2 * N + 1 + U) 0) (Db + N + 1) L) (Db + 2 * N + 1 + L) 1 ∧
        ∀ i ∉ [t, k], x₂.regs i = x₁.regs i := by
      refine ⟨?z₁, ?e₁, ?_, ?_, ?_⟩
      case e₁ =>
        ram_exact_eval [extractMove, hr₁ one (by decide) ▸ hone, hr₁ hb (by decide) ▸ hhb,
          hr₁ pb (by decide) ▸ hpb, hx₁v, hx₁m, f₁, f₆]
      · simp +decide
      · simp [hx₁m]
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp [hi.1, hi.2]
    have hr₂ : ∀ i ∉ [t, k], x₂.regs i = x₁.regs i := hx₂r
    have hr₂₁ : ∀ i ∉ [t, u, best, vk, sz, k], x₂.regs i = x.regs i := fun i hi =>
      (hr₂ i (hframe _ _ (by simp) i hi)).trans (hr₁ i (hframe _ _ (by simp) i hi))
    obtain ⟨y, he₃, hfr₃, hheap', hpos₃, hout₃⟩ := siftDown_spec (S := S - 1) (K := 1)
      (hr₂₁ one (by decide) ▸ hone) (hr₂₁ db (by decide) ▸ hdb) (hr₂₁ hb (by decide) ▸ hhb)
      (hr₂₁ pb (by decide) ▸ hpb) ((hr₂ sz (by decide)).trans hx₁s) hx₂k le_rfl (by omega)
      hfit (hx₂m ▸ hs) (hx₂m ▸ hdo)
    rw [Nat.sub_add_cancel hS] at he₃
    have hr₃ : ∀ i ∉ [k, p, vk, vp, dk, dp, t, l, szp], y.regs i = x₂.regs i := hfr₃
    have hc : (Cond.lt zero sz).Holds x₁ := by
      simp only [Cond.holds_lt, hr₁ zero (by decide) ▸ hzero, hx₁s]
      omega
    refine ⟨y, ?_, fun i hi => ?_, ?_, ?_, ?_, hheap', fun v hv => ?_, fun a ha => ?_⟩
    · rw [extractMin_eq]
      refine (execWithin_append he₁ (ExecWithin.branch_pos hc
        (execWithin_append he₂ he₃))).mono ?_
      omega
    · exact (hr₃ i (hframe _ _ (by simp) i hi)).trans (hr₂₁ i (hframe _ _ (by simp) i hi))
    · rw [hr₃ u (by decide), hr₂ u (by decide), hx₁u]
    · rw [hr₃ best (by decide), hr₂ best (by decide), hx₁b]
    · rw [hr₃ sz (by decide), hr₂ sz (by decide), hx₁s]
    · rw [hpos₃ v hv, hx₂m]
      exact hpos v hv
    · rw [hout₃ a ha, hx₂m, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
  · obtain rfl : S = 1 := by omega
    have hc : ¬(Cond.lt zero sz).Holds x₁ := by
      simp only [Cond.holds_lt, hr₁ zero (by decide) ▸ hzero, hx₁s]
      omega
    obtain ⟨x₂, he₂, hx₂⟩ : ∃ x₂, ExecWithin w extractStop x₁ x₂ 1 ∧ x₂ = x₁ := by
      refine ⟨?z₂, ?e₂, ?_⟩
      case e₂ => ram_exact_eval [extractStop]
      simp [Data.set]
    subst hx₂
    have hheap' := hheap.extract_one
    rw [hU] at hheap'
    refine ⟨x₂, ?_, fun i hi => hr₁ i (hframe _ _ (by simp) i hi), hx₁u, hx₁b, hx₁s,
      hx₁m ▸ hheap', fun v hv => ?_, hout₁⟩
    · rw [extractMin_eq]
      exact (execWithin_append he₁ (ExecWithin.branch_neg hc he₂)).mono (by omega)
    · rw [hx₁m, Function.update_apply]
      split_ifs with h
      · exact iff_of_true rfl (Or.inr (by omega))
      · exact ⟨Or.inl, fun h' => h'.resolve_right (by omega)⟩

end Cslib.Algorithms.WordRAM.Dijkstra

end
