/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapSift
public import Complexity.Algorithms.WordRAM.Dijkstra.ListEncode

/-!
# Dijkstra's algorithm with a binary heap: the scan of the edges

This file proves what one run of `Cslib.Algorithms.WordRAM.Dijkstra.relaxEdges` does on the
edges out of a vertex `U` of an adjacency-list instance: within `O(deg U · (⌊log₂ n⌋ + 1) + 1)`
instructions it applies `Cslib.Algorithms.WordRAM.Dijkstra.edgesWord` to every distance word, and
keeps the heap invariant, with the heap holding the discovered vertices that are not visited.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.relaxEdges_spec`: the scan of the edges out of a vertex.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM HeapReg

/-- The straight-line start of `edgeBody`: read the edge and the distance word of its target. -/
private def edgePrefix : Code .exact 27 := ram_exact[
  t ← j + j; t ← t + eb; tv ← *t; t ← t + one; tc ← *t; j ← j + one;
  cand ← best + tc;
  t ← db + tv; dv ← *t ]

/-- The straight-line start of an insertion: store the key and append the vertex to the heap. -/
private def insPrefix : Code .exact 27 := ram_exact[
  *t ← cand; sz ← sz + one; t ← hb + sz; *t ← tv; t ← pb + tv; *t ← sz; k ← sz ]

/-- The straight-line start of a decrease-key: store the key and read the position. -/
private def decPrefix : Code .exact 27 := ram_exact[ *t ← cand; t ← pb + tv; k ← *t ]

/-- `edgeBody` split into its straight-line parts and the sift-ups. -/
private theorem edgeBody_eq : edgeBody = appendCode edgePrefix (.branch (.eq dv zero)
    (appendCode insPrefix siftUp)
    (.branch (.lt cand dv) (appendCode decPrefix siftUp) ram_exact[ t ← t ])) := rfl

/-- `edgeBody` writes only its scratch registers and `sz`. -/
private theorem edgeBody_preserves :
    ∀ i : Fin 27, i ∉ [j, tv, tc, cand, dv, t, k, p, vk, vp, dk, dp, sz] →
      edgeBody.Preserves i := by
  decide

/-- Relaxing through the first `i + 1` edges is relaxing through the first `i` and then
through edge `i`. -/
private theorem edgesWord_take_succ {N b d i : ℕ} {es : List (Fin N × ℕ)} (v : Fin N)
    (hi : i < es.length) :
    edgesWord b (es.take (i + 1)) v d = if es[i].1 = v then
      edgeWord b es[i].2 (edgesWord b (es.take i) v d) else edgesWord b (es.take i) v d := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [edgesWord, List.foldl_append, Option.toList_some, List.foldl_cons, List.foldl_nil]

/-- A nonzero distance word that no edge of the list improves stays. -/
private theorem edgesWord_of_le {N b d : ℕ} {es : List (Fin N × ℕ)} {v : Fin N} (hd : d ≠ 0)
    (hle : ∀ c, (v, c) ∈ es → d ≤ b + c) : edgesWord b es v d = d := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have h' : (if e.1 = v then edgeWord b e.2 d else d) = d := by
      split_ifs with he
      · have := hle e.2 (by rw [← he]; simp)
        simp [edgeWord, hd, Nat.not_lt.2 this]
      · rfl
    simp only [edgesWord, List.foldl_cons] at ih ⊢
    rw [h']
    exact ih fun c hc => hle c (List.mem_cons_of_mem _ hc)

/-- **One edge.** The relaxation of an edge to `V` of weight `C`, with `B ≠ 0` the distance word
of its tail, from a heap that holds every discovered vertex whose word the edge could improve:
it advances `j`, relaxes the word of `V` and keeps the heap invariant and the visited vertices.
-/
private theorem edgeBody_spec {G : ListInstance} {w B J S C : ℕ} {V : Fin G.n} {y : Data 27}
    (hzero : y.regs zero = 0) (hone : y.regs one = 1) (htwo : y.regs two = 2)
    (heb : y.regs eb = G.n + 4) (hdb : y.regs db = G.dbase) (hhb : y.regs hb = G.dbase + G.n)
    (hpb : y.regs pb = G.dbase + 2 * G.n + 1) (hsz : y.regs sz = S) (hbest : y.regs best = B)
    (hB : B ≠ 0) (hj : y.regs j = J) (hJ : J < G.m)
    (hfit : Fits w (G.dbase + 3 * G.n + 1)) (hfitC : Fits w (B + C))
    (hT : y.mem (J + J + (G.n + 4)) = V) (hW : y.mem (J + J + (G.n + 4) + 1) = C)
    (hheap : HeapInv G.n G.dbase S y.mem)
    (hvis : y.mem (G.dbase + V) ≠ 0 → y.mem (G.dbase + 2 * G.n + 1 + V) = 0 →
      y.mem (G.dbase + V) ≤ B + C) :
    ∃ z, ExecWithin w edgeBody y z (30 * Nat.log 2 G.n + 30) ∧
      z.regs j = J + 1 ∧ z.regs sz ≤ S + 1 ∧ HeapInv G.n G.dbase (z.regs sz) z.mem ∧
      (∀ v : Fin G.n, z.mem (G.dbase + v) =
        if V = v then edgeWord B C (y.mem (G.dbase + v)) else y.mem (G.dbase + v)) ∧
      (∀ v : Fin G.n, (z.mem (G.dbase + v) ≠ 0 ∧ z.mem (G.dbase + 2 * G.n + 1 + v) = 0) ↔
        (y.mem (G.dbase + v) ≠ 0 ∧ y.mem (G.dbase + 2 * G.n + 1 + v) = 0)) ∧
      (∀ a < G.dbase, z.mem a = y.mem a) := by
  have hDb : G.dbase = G.n + 2 * G.m + 4 := rfl
  have hV := V.isLt
  have f1 : Fits w (J + J) := hfit.of_le (by omega)
  have f2 : Fits w (J + J + (G.n + 4)) := hfit.of_le (by omega)
  have f3 : Fits w (J + J + (G.n + 4) + 1) := hfit.of_le (by omega)
  have f4 : Fits w (J + 1) := hfit.of_le (by omega)
  have f5 : Fits w (G.dbase + V) := hfit.of_le (by omega)
  have f8 : Fits w (G.dbase + 2 * G.n + 1 + V) := hfit.of_le (by omega)
  let y₁ := ((((((((y.set t (J + J)).set t (J + J + (G.n + 4))).set tv V).set t
    (J + J + (G.n + 4) + 1)).set tc C).set j (J + 1)).set cand (B + C)).set t
    (G.dbase + V)).set dv (y.mem (G.dbase + V))
  have e₁ : ExecWithin w edgePrefix y y₁ 9 := by
    ram_exact_eval [edgePrefix, y₁, hone, heb, hdb, hbest, hj, hT, hW, hfitC, f1, f2, f3, f4, f5]
  have hlog {K : ℕ} (hK : K ≤ G.n) : Nat.log 2 K ≤ Nat.log 2 G.n := Nat.log_mono_right hK
  by_cases hD0 : y.mem (G.dbase + V) = 0
  · -- `V` is undiscovered: insert it
    have hP : y.mem (G.dbase + 2 * G.n + 1 + V) = 0 := by
      by_contra hP
      exact hheap.key_ne V hV hP hD0
    have hSN : S < G.n := hheap.size_lt hV hP
    have f6 : Fits w (S + 1) := hfit.of_le (by omega)
    have f7 : Fits w (G.dbase + G.n + (S + 1)) := hfit.of_le (by omega)
    let y₂ := ((((((y₁.write (G.dbase + V) (B + C)).set sz (S + 1)).set t
      (G.dbase + G.n + (S + 1))).write (G.dbase + G.n + (S + 1)) V).set t
      (G.dbase + 2 * G.n + 1 + V)).write (G.dbase + 2 * G.n + 1 + V) (S + 1)).set k (S + 1)
    have e₂ : ExecWithin w insPrefix y₁ y₂ 7 := by
      ram_exact_eval [insPrefix, y₁, y₂, hone, hhb, hpb, hsz, f6, f7, f8]
    have hm₂ : y₂.mem = Function.update (Function.update (Function.update y.mem
        (G.dbase + V) (B + C)) (G.dbase + G.n + (S + 1)) V)
        (G.dbase + 2 * G.n + 1 + V) (S + 1) := rfl
    obtain ⟨hsh, hord⟩ := hheap.push (c := B + C) hV hP (by omega)
    rw [← hm₂] at hsh hord
    obtain ⟨z, e₃, hzr, hzh, hzp, hzm⟩ := siftUp_spec (S := S + 1) (K := S + 1) (x := y₂)
      (by simp +decide [y₂, y₁, hone]) (by simp +decide [y₂, y₁, htwo])
      (by simp +decide [y₂, y₁, hdb]) (by simp +decide [y₂, y₁, hhb])
      (by simp +decide [y₂, y₁, hpb]) (by simp +decide [y₂]) (by omega) le_rfl hfit hsh hord
    have hzj : z.regs j = J + 1 := by rw [hzr j (by decide)]; simp +decide [y₂, y₁]
    have hzsz : z.regs sz = S + 1 := by rw [hzr sz (by decide)]; simp +decide [y₂]
    have hzw (v : Fin G.n) (hv : V ≠ v) : z.mem (G.dbase + v) = y.mem (G.dbase + v) := by
      have hvv : (V : ℕ) ≠ v := fun h => hv (Fin.ext h)
      have := v.isLt
      rw [hzm _ (Or.inl (by omega)), hm₂, Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    refine ⟨z, ?_, hzj, by omega, hzsz ▸ hzh, ?_, ?_, ?_⟩
    · rw [edgeBody_eq]
      refine (execWithin_append e₁
        (ExecWithin.branch_pos ?_ (execWithin_append e₂ e₃))).mono ?_
      · simp +decide [Cond.holds_eq, y₁, hzero, hD0]
      · have := hlog (K := S + 1) (by omega)
        omega
    · intro v
      by_cases hv : V = v
      · subst hv
        simp only [↓reduceIte]
        rw [hzm _ (Or.inl (by omega)), hm₂, Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self, hD0]
        simp [edgeWord]
      · simp only [hv, ↓reduceIte]
        rw [hzw v hv]
    · intro v
      by_cases hv : V = v
      · subst hv
        have h₁ : z.mem (G.dbase + 2 * G.n + 1 + V) ≠ 0 := by
          rw [Ne, hzp V hV, hm₂, Function.update_self]
          omega
        exact ⟨fun h => absurd h.2 h₁, fun h => absurd hD0 h.1⟩
      · have hvv : (V : ℕ) ≠ v := fun h => hv (Fin.ext h)
        have := v.isLt
        rw [hzw v hv, hzp v v.isLt, hm₂, Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · intro a ha
      rw [hzm _ (Or.inl (by omega)), hm₂, Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  by_cases hlt : B + C < y.mem (G.dbase + V)
  · -- `V` is in the heap and its key decreases
    have hP : y.mem (G.dbase + 2 * G.n + 1 + V) ≠ 0 := fun hP => by
      have := hvis hD0 hP
      omega
    have hPS : y.mem (G.dbase + 2 * G.n + 1 + V) ≤ S := hheap.pos_le V hV
    have hne : G.dbase + 2 * G.n + 1 + V ≠ G.dbase + V := by omega
    let y₂ := ((y₁.write (G.dbase + V) (B + C)).set t (G.dbase + 2 * G.n + 1 + V)).set k
      (y.mem (G.dbase + 2 * G.n + 1 + V))
    have e₂ : ExecWithin w decPrefix y₁ y₂ 3 := by
      ram_exact_eval [decPrefix, y₁, y₂, hpb, f8, hne]
    have hm₂ : y₂.mem = Function.update y.mem (G.dbase + V) (B + C) := rfl
    obtain ⟨hsh, hord⟩ := hheap.decrease (c := B + C) hV hP (by omega) hlt.le
    rw [← hm₂] at hsh hord
    obtain ⟨z, e₃, hzr, hzh, hzp, hzm⟩ := siftUp_spec (S := S)
      (K := y.mem (G.dbase + 2 * G.n + 1 + V)) (x := y₂)
      (by simp +decide [y₂, y₁, hone]) (by simp +decide [y₂, y₁, htwo])
      (by simp +decide [y₂, y₁, hdb]) (by simp +decide [y₂, y₁, hhb])
      (by simp +decide [y₂, y₁, hpb]) (by simp +decide [y₂]) (by omega) hPS hfit hsh hord
    have hzj : z.regs j = J + 1 := by rw [hzr j (by decide)]; simp +decide [y₂, y₁]
    have hzsz : z.regs sz = S := by rw [hzr sz (by decide)]; simp +decide [y₂, y₁, hsz]
    have hzw (v : Fin G.n) (hv : V ≠ v) : z.mem (G.dbase + v) = y.mem (G.dbase + v) := by
      have hvv : (V : ℕ) ≠ v := fun h => hv (Fin.ext h)
      have := v.isLt
      rw [hzm _ (Or.inl (by omega)), hm₂, Function.update_of_ne (by omega)]
    refine ⟨z, ?_, hzj, hzsz.le.trans (Nat.le_succ S), hzsz ▸ hzh, ?_, ?_, ?_⟩
    · rw [edgeBody_eq]
      refine (execWithin_append e₁ (ExecWithin.branch_neg ?_ (ExecWithin.branch_pos ?_
        (execWithin_append e₂ e₃)))).mono ?_
      · simp +decide [Cond.holds_eq, y₁, hzero, hD0]
      · simp +decide [Cond.holds_lt, y₁, hlt]
      · have := hlog (K := y.mem (G.dbase + 2 * G.n + 1 + V)) (hPS.trans hheap.size_le)
        omega
    · intro v
      by_cases hv : V = v
      · subst hv
        simp only [↓reduceIte]
        rw [hzm _ (Or.inl (by omega)), hm₂, Function.update_self]
        simp [edgeWord, hD0, hlt]
      · simp only [hv, ↓reduceIte]
        rw [hzw v hv]
    · intro v
      by_cases hv : V = v
      · subst hv
        have h₁ : z.mem (G.dbase + 2 * G.n + 1 + V) ≠ 0 := by
          rw [Ne, hzp V hV, hm₂, Function.update_of_ne hne]
          exact hP
        exact ⟨fun h => absurd h.2 h₁, fun h => absurd h.2 hP⟩
      · have hvv : (V : ℕ) ≠ v := fun h => hv (Fin.ext h)
        have := v.isLt
        rw [hzw v hv, hzp v v.isLt, hm₂, Function.update_of_ne (by omega)]
    · intro a ha
      rw [hzm _ (Or.inl (by omega)), hm₂, Function.update_of_ne (by omega)]
  · -- no change
    have e₂ : ExecWithin (B := .exact) w ram_exact[ t ← t ] y₁ (y₁.set t (G.dbase + V)) 1 := by
      ram_exact_eval [y₁]
    refine ⟨y₁.set t (G.dbase + V), ?_, by simp +decide [y₁], by simp +decide [y₁, hsz],
      by simpa +decide [y₁, hsz] using hheap, ?_, fun v => Iff.rfl, fun a _ => rfl⟩
    · rw [edgeBody_eq]
      refine (execWithin_append e₁
        (ExecWithin.branch_neg ?_ (ExecWithin.branch_neg ?_ e₂))).mono ?_
      · simp +decide [Cond.holds_eq, y₁, hzero, hD0]
      · simp +decide [Cond.holds_lt, y₁, hlt]
      · omega
    · intro v
      by_cases hv : V = v
      · subst hv
        simp [y₁, edgeWord, hD0, hlt]
      · simp [y₁, hv]

/-- The invariant of the scan of the edges out of `U`, started from `x`: the edges before `j`
have been relaxed. -/
private structure ScanInv (G : ListInstance) (U : Fin G.n) (B S₀ : ℕ) (x y : Data 27) :
    Prop where
  /-- The registers other than the scratch registers and `sz` keep their contents. -/
  frame : ∀ i ∉ [j, tv, tc, cand, dv, t, k, p, vk, vp, dk, dp, sz], y.regs i = x.regs i
  /-- The index is at least the offset of `U`. -/
  j_ge : G.offset U ≤ y.regs j
  /-- The index is at most the offset of `U + 1`. -/
  j_le : y.regs j ≤ G.offset ((U : ℕ) + 1)
  /-- Each relaxed edge inserts at most one vertex. -/
  sz_le : y.regs sz ≤ S₀ + (y.regs j - G.offset U)
  /-- The heap invariant. -/
  heap : HeapInv G.n G.dbase (y.regs sz) y.mem
  /-- The distance words are relaxed through the edges before `j`. -/
  word : ∀ v : Fin G.n, y.mem (G.dbase + v) =
    edgesWord B ((G.adj U).take (y.regs j - G.offset U)) v (x.mem (G.dbase + v))
  /-- The visited vertices stay. -/
  visited : ∀ v : Fin G.n,
    (y.mem (G.dbase + v) ≠ 0 ∧ y.mem (G.dbase + 2 * G.n + 1 + v) = 0) ↔
      (x.mem (G.dbase + v) ≠ 0 ∧ x.mem (G.dbase + 2 * G.n + 1 + v) = 0)
  /-- The input stays. -/
  input : ∀ a < G.dbase, y.mem a = x.mem a

/-- **The scan of the edges out of `U`.** Started with the index `j` and the end `jend` at the
offsets of `U` and `U + 1`, the distance word `B ≠ 0` of `U` in `best`, the input intact below
`Db = G.dbase` and a heap that holds the discovered vertices other than the visited ones, the
scan runs within `deg U · (30 ⌊log₂ n⌋ + 32) + 2` instructions. It replaces every distance word
by its relaxation through the edges out of `U`, inserts at most `deg U` vertices into the heap and
keeps the heap invariant, the visited vertices, the input and the registers other than its
scratch registers and `sz`.

A vertex is visited when it is discovered (its distance word is nonzero) but not in the heap (its
position is `0`). The scan assumes that no edge out of `U` improves a visited vertex. -/
theorem relaxEdges_spec {G : ListInstance} {w S₀ B : ℕ} (U : Fin G.n) {x : Data 27}
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (heb : x.regs eb = G.n + 4) (hdb : x.regs db = G.dbase) (hhb : x.regs hb = G.dbase + G.n)
    (hpb : x.regs pb = G.dbase + 2 * G.n + 1) (hsz : x.regs sz = S₀) (hbest : x.regs best = B)
    (hB : B ≠ 0) (hj : x.regs j = G.offset U) (hjend : x.regs jend = G.offset ((U : ℕ) + 1))
    (hfit : Fits w (G.dbase + 3 * G.n + 1)) (hfitC : ∀ e ∈ G.adj U, Fits w (B + e.2))
    (hinput : ∀ a < G.dbase, x.mem a = (Data.init G.encode : Data 27).mem a)
    (hheap : HeapInv G.n G.dbase S₀ x.mem)
    (hvis : ∀ v : Fin G.n, x.mem (G.dbase + v) ≠ 0 → x.mem (G.dbase + 2 * G.n + 1 + v) = 0 →
      ∀ c, (v, c) ∈ G.adj U → x.mem (G.dbase + v) ≤ B + c) :
    ∃ y, ExecWithin w relaxEdges x y ((G.adj U).length * (30 * Nat.log 2 G.n + 32) + 2) ∧
      (∀ i ∉ [j, tv, tc, cand, dv, t, k, p, vk, vp, dk, dp, sz], y.regs i = x.regs i) ∧
      y.regs sz ≤ S₀ + (G.adj U).length ∧
      HeapInv G.n G.dbase (y.regs sz) y.mem ∧
      (∀ v : Fin G.n, y.mem (G.dbase + v) = edgesWord B (G.adj U) v (x.mem (G.dbase + v))) ∧
      (∀ v : Fin G.n, (y.mem (G.dbase + v) ≠ 0 ∧ y.mem (G.dbase + 2 * G.n + 1 + v) = 0) ↔
        (x.mem (G.dbase + v) ≠ 0 ∧ x.mem (G.dbase + 2 * G.n + 1 + v) = 0)) ∧
      (∀ a < G.dbase, y.mem a = x.mem a) := by
  have hDb : G.dbase = G.n + 2 * G.m + 4 := rfl
  have hdeg : G.offset ((U : ℕ) + 1) = G.offset U + (G.adj U).length := G.offset_succ U.isLt
  have hm : G.offset ((U : ℕ) + 1) ≤ G.m := G.offset_n ▸ G.offset_mono (by omega)
  have hI₀ : ScanInv G U B S₀ x x := by
    refine ⟨fun _ _ => rfl, hj.ge, hj ▸ G.offset_mono (by omega), by omega, hsz ▸ hheap,
      fun v => ?_, fun v => Iff.rfl, fun _ _ => rfl⟩
    rw [hj, Nat.sub_self, List.take_zero]
    rfl
  have hbody : ∀ y, ScanInv G U B S₀ x y → (Cond.lt j jend).Holds y →
      ∃ z, ExecWithin w edgeBody y z (30 * Nat.log 2 G.n + 30) ∧ ScanInv G U B S₀ x z ∧
        G.offset ((U : ℕ) + 1) - z.regs j < G.offset ((U : ℕ) + 1) - y.regs j := by
    intro y hy hc
    have hjend' : y.regs jend = G.offset ((U : ℕ) + 1) := (hy.frame jend (by decide)).trans hjend
    have hlt : y.regs j < G.offset ((U : ℕ) + 1) := by
      simpa only [Cond.holds_lt, hjend'] using hc
    obtain ⟨i, hji⟩ : ∃ i, y.regs j = G.offset U + i :=
      ⟨y.regs j - G.offset U, by have := hy.j_ge; omega⟩
    have hi : i < (G.adj U).length := by omega
    have hword (v : Fin G.n) : y.mem (G.dbase + v) =
        edgesWord B ((G.adj U).take i) v (x.mem (G.dbase + v)) := by
      rw [hy.word v, hji, Nat.add_sub_cancel_left]
    have haddr : y.regs j + y.regs j + (G.n + 4) = 2 * (G.offset U + i) + G.n + 4 := by omega
    have hT : y.mem (y.regs j + y.regs j + (G.n + 4)) = ((G.adj U)[i].1 : ℕ) := by
      rw [hy.input _ (by omega), hinput _ (by omega), haddr, G.init_target U hi]
    have hW : y.mem (y.regs j + y.regs j + (G.n + 4) + 1) = (G.adj U)[i].2 := by
      rw [hy.input _ (by omega), hinput _ (by omega), haddr, G.init_weight U hi]
    have hmem := List.getElem_mem hi
    have hvisy : y.mem (G.dbase + (G.adj U)[i].1) ≠ 0 →
        y.mem (G.dbase + 2 * G.n + 1 + (G.adj U)[i].1) = 0 →
        y.mem (G.dbase + (G.adj U)[i].1) ≤ B + (G.adj U)[i].2 := by
      intro h₁ h₂
      obtain ⟨hx₁, hx₂⟩ := (hy.visited _).1 ⟨h₁, h₂⟩
      rw [hword, edgesWord_of_le hx₁ fun c hc => hvis _ hx₁ hx₂ c (List.mem_of_mem_take hc)]
      exact hvis _ hx₁ hx₂ _ hmem
    obtain ⟨z, he, hzj, hzsz, hzh, hzw, hzv, hzi⟩ := edgeBody_spec
      ((hy.frame zero (by decide)).trans hzero) ((hy.frame one (by decide)).trans hone)
      ((hy.frame two (by decide)).trans htwo) ((hy.frame eb (by decide)).trans heb)
      ((hy.frame db (by decide)).trans hdb) ((hy.frame hb (by decide)).trans hhb)
      ((hy.frame pb (by decide)).trans hpb) rfl ((hy.frame best (by decide)).trans hbest) hB
      rfl (by omega) hfit (hfitC _ hmem) hT hW hy.heap hvisy
    refine ⟨z, he, ⟨?_, by omega, by omega, by have := hy.sz_le; omega, hzh, fun v => ?_,
      fun v => (hzv v).trans (hy.visited v), fun a ha => (hzi a ha).trans (hy.input a ha)⟩,
      by omega⟩
    · intro r hr
      rw [he.regs_eq (edgeBody_preserves r hr), hy.frame r hr]
    · rw [hzw v, hword v, hzj, hji, Nat.add_assoc, Nat.add_sub_cancel_left,
        edgesWord_take_succ v hi]
  obtain ⟨y, he, hy, hexit⟩ := ExecWithin.loop_invariant (cond := .lt j jend) (body := edgeBody)
    (ScanInv G U B S₀ x) (fun y => G.offset ((U : ℕ) + 1) - y.regs j) hbody hI₀
  have hjend' : y.regs jend = G.offset ((U : ℕ) + 1) := (hy.frame jend (by decide)).trans hjend
  have hlen : y.regs j - G.offset U = (G.adj U).length := by
    have := hy.j_le
    simp only [Cond.holds_lt, hjend'] at hexit
    omega
  refine ⟨y, he.mono ?_, hy.frame, hlen ▸ hy.sz_le, hy.heap, fun v => ?_, hy.visited, hy.input⟩
  · rw [hj, show G.offset ((U : ℕ) + 1) - G.offset U = (G.adj U).length by omega]
  · rw [hy.word v, hlen, List.take_length]

end Cslib.Algorithms.WordRAM.Dijkstra

end
