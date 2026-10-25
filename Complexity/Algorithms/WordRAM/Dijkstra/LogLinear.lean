/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapRelax
public import Complexity.Computability.WordRAM.Compile

/-!
# Dijkstra's algorithm with a binary heap in `O((m + 1) (⌊log₂ n⌋ + 1))` time

This file proves that `Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra` computes the distances
from the source of an adjacency-list instance within `O((m + 1) (⌊log₂ n⌋ + 1))` instructions,
and so proves `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearStatement`.

The rounds keep the invariant of Dijkstra's algorithm
(`Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv`) of the weight-matrix instance, for the visited
vertices (discovered and out of the heap) and the tentative distances in the output cells, along
with the heap invariant. A round costs `O((deg u + 1) (⌊log₂ n⌋ + 1))` for its vertex `u`, which
is paid by a potential that counts twice the edges out of the unvisited vertices plus the heap
size: the round visits `u`, so it removes `deg u` edges from the count and one entry from the
heap, and it inserts at most `deg u` entries.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.distOf`,
  `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.visitedOf`: the tentative distances and the
  visited vertices that a machine state holds.
* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.remaining`: the number of edges out of the
  unvisited vertices.
* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.OuterInv`: the invariant of the rounds.
* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.potential`: the potential that pays for them.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.heapSetup_spec`: the setup establishes the invariant of the
  rounds within `25` instructions, with potential at most `100 (⌊log₂ n⌋ + 1) (2 m + 1)`.
* `Cslib.Algorithms.WordRAM.Dijkstra.heapRound_spec`: one round keeps the invariant of the
  rounds, and the drop of the potential pays for its running time.
* `Cslib.Algorithms.WordRAM.Dijkstra.heapExit_spec`: when the rounds stop, with an empty heap,
  the output cells hold the encoded distances.
* `Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra_spec`: the structured program leaves the
  encoded distances in the output cells within `200 (m + 1) (⌊log₂ n⌋ + 1) + 27` instructions.
* `Cslib.Algorithms.WordRAM.Dijkstra.logLinearSpec`: its compiled program meets
  `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec` with `K = 230`.
* `Cslib.Algorithms.WordRAM.Dijkstra.logLinearStatement`: the log-linear main theorem.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM HeapReg

namespace ListInstance

variable (G : ListInstance)

/-- The tentative distances held in the distance words of `y`. -/
noncomputable def distOf (y : Data 27) (v : Fin G.n) : ℕ∞ :=
  decodeDist (y.mem (G.dbase + v))

/-- The visited vertices of `y`: those that are discovered, with a nonzero distance word, but
not in the heap, with position `0`. -/
def visitedOf (y : Data 27) : Finset (Fin G.n) :=
  Finset.univ.filter fun v => y.mem (G.dbase + v) ≠ 0 ∧ y.mem (G.dbase + 2 * G.n + 1 + v) = 0

/-- The number of edges out of the unvisited vertices of `y`. -/
def remaining (y : Data 27) : ℕ :=
  ∑ v ∈ Finset.univ.filter (· ∉ G.visitedOf y), (G.adj v).length

/-- **The potential** of `y`, which pays for the remaining rounds: `100 (⌊log₂ n⌋ + 1)` times
twice the number of edges out of the unvisited vertices plus the heap size. -/
def potential (y : Data 27) : ℕ :=
  100 * (Nat.log 2 G.n + 1) * (2 * G.remaining y + y.regs sz)

/-- **The invariant of the rounds.** The constant registers hold their values, the input is
intact, the heap invariant holds, and the memory satisfies the invariant of Dijkstra's algorithm
for the weight-matrix instance. -/
structure OuterInv (y : Data 27) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  two_eq : y.regs two = 2
  three_eq : y.regs three = 3
  eb_eq : y.regs eb = G.n + 4
  db_eq : y.regs db = G.dbase
  hb_eq : y.regs hb = G.dbase + G.n
  pb_eq : y.regs pb = G.dbase + 2 * G.n + 1
  input : ∀ a < G.dbase, y.mem a = (Data.init G.encode : Data 27).mem a
  heap : HeapInv G.n G.dbase (y.regs sz) y.mem
  inv : G.toInstance.Inv (G.visitedOf y) (G.distOf y)

end ListInstance

variable {G : ListInstance} {w : ℕ}

/-- The allowed word size holds every address of the three arrays. -/
private theorem fits_arrays (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    Fits w (G.dbase + 3 * G.n + 1) :=
  hw.of_le (by unfold ListInstance.dbase; nlinarith [Nat.zero_le G.maxWeight])

/-- The setup establishes the invariant of the rounds, with the source as the only heap entry. -/
theorem heapSetup_spec (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    ∃ y, ExecWithin w heapSetup (.init G.encode) y 25 ∧ G.OuterInv y ∧
      G.potential y ≤ 100 * (Nat.log 2 G.n + 1) * (2 * G.m + 1) := by
  classical
  have hf := fits_arrays hw
  have hs := G.source.isLt
  have hDb' : G.m + G.m + G.n + 3 + 1 = G.dbase := by unfold ListInstance.dbase; omega
  have hpb' : G.dbase + G.n + G.n + 1 = G.dbase + 2 * G.n + 1 := by omega
  have hoff : (Data.init G.encode : Data 27).mem (G.n + 3) = G.m := by
    rw [G.init_offset le_rfl, G.offset_n]
  have h1 : Fits w 1 := hf.of_le (by omega)
  have h2 : Fits w 2 := hf.of_le (by omega)
  have h3 : Fits w 3 := hf.of_le (by omega)
  have hn : Fits w G.n := hf.of_le (by omega)
  have hn3 : Fits w (G.n + 3) := hf.of_le (by unfold ListInstance.dbase; omega)
  have hn4 : Fits w (G.n + 3 + 1) := hf.of_le (by unfold ListInstance.dbase; omega)
  have hm2 : Fits w (G.m + G.m) := hf.of_le (by unfold ListInstance.dbase; omega)
  have hm2n : Fits w (G.m + G.m + G.n) := hf.of_le (by unfold ListInstance.dbase; omega)
  have hm2n3 : Fits w (G.m + G.m + G.n + 3) := hf.of_le (by unfold ListInstance.dbase; omega)
  have hDb : Fits w G.dbase := hf.of_le (by omega)
  have hhb : Fits w (G.dbase + G.n) := hf.of_le (by omega)
  have hpb₁ : Fits w (G.dbase + G.n + G.n) := hf.of_le (by omega)
  have hpb : Fits w (G.dbase + 2 * G.n + 1) := hf.of_le (by omega)
  have hds : Fits w (G.dbase + G.source) := hf.of_le (by omega)
  have hh1 : Fits w (G.dbase + G.n + 1) := hf.of_le (by omega)
  have hps : Fits w (G.dbase + 2 * G.n + 1 + G.source) := hf.of_le (by omega)
  let y := (((((((((((((((((((((((((Data.init G.encode : Data 27).set one 1).set two 2).set
    three 3).set t 1).set n G.n).set t 2).set u G.source).set t (G.n + 3)).set t G.m).set db
    (G.m + G.m)).set db (G.m + G.m + G.n)).set db (G.m + G.m + G.n + 3)).set db G.dbase).set eb
    (G.n + 3)).set eb (G.n + 3 + 1)).set hb (G.dbase + G.n)).set pb (G.dbase + G.n + G.n)).set pb
    (G.dbase + 2 * G.n + 1)).set t (G.dbase + G.source)).write (G.dbase + G.source) 1).set t
    (G.dbase + G.n + 1)).write (G.dbase + G.n + 1) G.source).set t
    (G.dbase + 2 * G.n + 1 + G.source)).write (G.dbase + 2 * G.n + 1 + G.source) 1).set sz 1
  have he : ExecWithin w heapSetup (.init G.encode) y 25 := by
    ram_exact_eval [heapSetup, y, Data.init_regs, G.init_n, G.init_source, hoff, h1, h2, h3, hn,
      hn3, hn4, hm2, hm2n, hm2n3, hDb', hDb, hhb, hpb₁, hpb', hpb, hds, hh1, hps]
  have hm (a : ℕ) : y.mem a = Function.update (Function.update (Function.update
      (Data.init G.encode : Data 27).mem (G.dbase + G.source) 1) (G.dbase + G.n + 1) G.source)
      (G.dbase + 2 * G.n + 1 + G.source) 1 a := rfl
  have hD (v : ℕ) (hv : v < G.n) :
      y.mem (G.dbase + v) = if v = G.source then 1 else 0 := by
    simp only [hm, Function.update_apply]
    split_ifs <;> first | rfl | omega | exact G.init_past (by omega)
  have hP (v : ℕ) (hv : v < G.n) :
      y.mem (G.dbase + 2 * G.n + 1 + v) = if v = G.source then 1 else 0 := by
    simp only [hm, Function.update_apply]
    split_ifs <;> first | rfl | omega | exact G.init_past (by omega)
  have hH : y.mem (G.dbase + G.n + 1) = G.source := by
    simp only [hm, Function.update_apply]
    split_ifs <;> first | rfl | omega
  have hsz : y.regs sz = 1 := by simp [y]
  have hvis : G.visitedOf y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v
    simp only [ListInstance.visitedOf, Finset.mem_filter, Finset.mem_univ, true_and,
      hD v v.isLt, hP v v.isLt]
    split_ifs <;> simp
  have hdist : G.distOf y = Function.update (fun _ => ⊤) G.source 0 := by
    funext v
    simp only [ListInstance.distOf, hD v v.isLt, Fin.val_eq_val]
    by_cases h : v = G.source
    · subst v
      simp [decodeDist]
    · simp [h, decodeDist]
  have hheap : HeapInv G.n G.dbase 1 y.mem := by
    refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i hi hi'
      rw [show i = 1 by omega, hH]
      exact hs
    · intro i hi hi'
      rw [show i = 1 by omega, hH, hP _ hs]
      simp
    · intro v hv
      rw [hP v hv]
      split_ifs <;> omega
    · intro v hv hne
      rw [hP v hv] at hne
      split_ifs at hne with h
      · subst h
        simp [hP _ hv, hH]
      · exact absurd rfl hne
    · intro v hv hne
      rw [hP v hv] at hne
      split_ifs at hne with h
      · subst h
        simp [hD _ hv]
      · exact absurd rfl hne
    · intro i hi hi'
      omega
  refine ⟨y, he, ⟨by simp +decide [y], by simp +decide [y], by simp +decide [y],
    by simp +decide [y], by simp +decide [y], by simp +decide [y], by simp +decide [y],
    by simp +decide [y], ?_, hsz ▸ hheap, ?_⟩, ?_⟩
  · intro a ha
    rw [hm, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  · rw [hvis, hdist]
    exact Instance.Inv.init G.toInstance
  · have hrem : G.remaining y = G.m := by
      simp [ListInstance.remaining, hvis, ListInstance.m]
    simp [ListInstance.potential, hrem, hsz]

/-- **One round** keeps the invariant of the rounds, and its running time and two more
instructions are paid by the drop of the potential. -/
theorem heapRound_spec (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) {y : Data 27}
    (hy : G.OuterInv y) (hsz : (Cond.lt zero sz).Holds y) :
    ∃ y' T, ExecWithin w heapRound y y' T ∧ G.OuterInv y' ∧
      T + 2 + G.potential y' ≤ G.potential y := by
  classical
  have hf := fits_arrays hw
  have hS1 : 1 ≤ y.regs sz := by
    simp only [Cond.holds_lt, hy.zero_eq] at hsz
    omega
  obtain ⟨x, ex, xr, xu, xbest, xsz, xheap, xpos, xmem⟩ :=
    extractMin_spec hy.zero_eq hy.one_eq hy.db_eq hy.hb_eq hy.pb_eq rfl hS1 hf hy.heap
  have hU : y.mem (G.dbase + G.n + 1) < G.n := hy.heap.vertex_lt 1 le_rfl hS1
  have hPU : y.mem (G.dbase + 2 * G.n + 1 + y.mem (G.dbase + G.n + 1)) = 1 :=
    hy.heap.pos_vertex 1 le_rfl hS1
  have hB : y.mem (G.dbase + y.mem (G.dbase + G.n + 1)) ≠ 0 :=
    hy.heap.key_ne _ hU (by rw [hPU]; omega)
  have hroot : ∀ v < G.n, y.mem (G.dbase + 2 * G.n + 1 + v) ≠ 0 →
      y.mem (G.dbase + y.mem (G.dbase + G.n + 1)) ≤ y.mem (G.dbase + v) :=
    fun v hv hp => hy.heap.root_le hv hp
  generalize hU0 : y.mem (G.dbase + G.n + 1) = U0 at xu xbest xpos hU hPU hB hroot
  generalize hB0 : y.mem (G.dbase + U0) = B at xbest hB hroot
  let U : Fin G.n := ⟨U0, hU⟩
  -- The four instructions that load the bounds of the edges out of `U`.
  have xthree : x.regs three = 3 := (xr three (by decide)).trans hy.three_eq
  have xone : x.regs one = 1 := (xr one (by decide)).trans hy.one_eq
  have hlt : U0 + 3 + 1 < G.dbase := by unfold ListInstance.dbase; omega
  have hf3 : Fits w (U0 + 3) := hf.of_le (by omega)
  have hf4 : Fits w (U0 + 3 + 1) := hf.of_le (by omega)
  have hx (a : ℕ) (ha : a < G.dbase) : x.mem a = (Data.init G.encode : Data 27).mem a := by
    rw [xmem a (Or.inl (by omega)), hy.input a ha]
  have hoff₀ : x.mem (U0 + 3) = G.offset U0 := by
    rw [hx _ (by omega), G.init_offset (by omega)]
  have hoff₁ : x.mem (U0 + 3 + 1) = G.offset (U0 + 1) := by
    rw [hx _ (by omega), show U0 + 3 + 1 = U0 + 1 + 3 by omega, G.init_offset (by omega)]
  let x₁ := x.set t (U0 + 3)
  let x₂ := x₁.set j (G.offset U0)
  let x₃ := x₂.set t (U0 + 3 + 1)
  let x₄ := x₃.set jend (G.offset (U0 + 1))
  have e₁ : ExecWithin w ram_exact[t ← u + three] x x₁ 1 := by ram_exact_eval [x₁, xu, xthree, hf3]
  have e₂ : ExecWithin (B := .exact) w ram_exact[j ← *t] x₁ x₂ 1 := by
    ram_exact_eval [x₁, x₂, hoff₀]
  have e₃ : ExecWithin w ram_exact[t ← t + one] x₂ x₃ 1 := by ram_exact_eval [x₁, x₂, x₃, xone, hf4]
  have e₄ : ExecWithin (B := .exact) w ram_exact[jend ← *t] x₃ x₄ 1 := by
    ram_exact_eval [x₁, x₂, x₃, x₄, hoff₁]
  have r₄ (i : Fin 27) (hi : i ∉ [t, j, jend]) : x₄.regs i = x.regs i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [x₄, x₃, x₂, x₁, hi.1, hi.2.1, hi.2.2]
  have reg (i : Fin 27) (h₁ : i ∉ [t, j, jend])
      (h₂ : i ∉ [t, u, best, vk, sz, k, p, vp, dk, dp, l, szp]) : x₄.regs i = y.regs i :=
    (r₄ i h₁).trans (xr i h₂)
  have hxD (v : Fin G.n) : x₄.mem (G.dbase + v) = y.mem (G.dbase + v) :=
    xmem _ (Or.inl (by have := v.isLt; omega))
  -- Dijkstra's step for the vertex `U`.
  have hdu : G.distOf y U = decodeDist B := by
    change decodeDist (y.mem (G.dbase + U0)) = _
    rw [hB0]
  have hfin : G.distOf y U ≠ ⊤ := hdu ▸ decodeDist_ne_top hB
  have hu : U ∉ G.visitedOf y := by simp [ListInstance.visitedOf, U, hPU]
  have hmin : ∀ v ∉ G.visitedOf y, G.distOf y U ≤ G.distOf y v := by
    intro v hv
    simp only [ListInstance.visitedOf, Finset.mem_filter, Finset.mem_univ, true_and,
      not_and] at hv
    rw [hdu]
    by_cases hd : y.mem (G.dbase + v) = 0
    · simp [ListInstance.distOf, hd, decodeDist]
    · exact decodeDist_le hB hd (hroot v v.isLt (hv hd))
  have hstep := Instance.Inv.step G.toInstance hy.inv hu hmin hfin
  have hfitC : ∀ e ∈ G.adj U, Fits w (B + e.2) := by
    intro e he
    have hb := hy.inv.bound U hfin
    rw [hdu] at hb
    simp only [decodeDist, hB, ite_false] at hb
    have hb' : B - 1 ≤ (G.visitedOf y).card * G.toInstance.maxWeight := by exact_mod_cast hb
    have hc : (G.visitedOf y).card ≤ G.n := by simpa using Finset.card_le_univ (G.visitedOf y)
    have hW := G.toInstance_maxWeight_le
    have he2 := G.le_maxWeight he
    have := Nat.mul_le_mul hc hW
    have hB' : B ≤ G.n * G.maxWeight + 1 := by omega
    have hle : G.n * G.maxWeight + G.maxWeight + 1 ≤
        8 * (G.n + G.m + 2) * (G.maxWeight + 2) := by nlinarith
    exact hw.of_le (by omega)
  have hvis : ∀ v : Fin G.n, x₄.mem (G.dbase + v) ≠ 0 →
      x₄.mem (G.dbase + 2 * G.n + 1 + v) = 0 → ∀ c, (v, c) ∈ G.adj U →
        x₄.mem (G.dbase + v) ≤ B + c := by
    intro v hd hp c hc
    rw [hxD] at hd ⊢
    rcases (xpos v v.isLt).mp hp with hp | hv
    · have hvV : v ∈ G.visitedOf y := by simp [ListInstance.visitedOf, hd, hp]
      have h₁ := hstep.eq_of_mem v (Finset.mem_insert_of_mem hvV)
      have h₂ := hy.inv.eq_of_mem v hvV
      obtain ⟨c', hc'⟩ : ∃ c', G.lightest U v = some c' := by
        cases h : G.lightest U v with
        | none => exact absurd hc ((G.lightest_eq_none_iff.mp h) c)
        | some c' => exact ⟨c', rfl⟩
      have hle := (G.lightest_eq_some_iff.mp hc').2 c hc
      have hrel : G.toInstance.relax (G.distOf y) U v =
          min (G.distOf y v) (G.distOf y U + c') := by
        simp only [Instance.relax, show G.toInstance.weight U v = some c' from hc']
      have hmin' : G.distOf y v ≤ G.distOf y U + c' := by
        rw [← min_eq_left_iff, ← hrel, h₁, h₂]
      rw [hdu] at hmin'
      simp only [ListInstance.distOf, decodeDist, hd, hB, ite_false] at hmin'
      have : y.mem (G.dbase + v) - 1 ≤ B - 1 + c' := by exact_mod_cast hmin'
      omega
    · have : y.mem (G.dbase + v) = B := by rw [hv, hB0]
      omega
  obtain ⟨z, ez, zr, zsz, zheap, zD, zvis, zin⟩ := relaxEdges_spec (G := G) (w := w) U (x := x₄)
    ((reg zero (by decide) (by decide)).trans hy.zero_eq)
    ((reg one (by decide) (by decide)).trans hy.one_eq)
    ((reg two (by decide) (by decide)).trans hy.two_eq)
    ((reg eb (by decide) (by decide)).trans hy.eb_eq)
    ((reg db (by decide) (by decide)).trans hy.db_eq)
    ((reg hb (by decide) (by decide)).trans hy.hb_eq)
    ((reg pb (by decide) (by decide)).trans hy.pb_eq)
    ((r₄ sz (by decide)).trans xsz) ((r₄ best (by decide)).trans xbest) hB
    (by simp +decide [x₄, x₃, x₂, U]) (by simp +decide [x₄, U]) hf hfitC hx xheap hvis
  -- The invariant after the round.
  have zreg (i : Fin 27) (h₁ : i ∉ [j, tv, tc, cand, dv, t, k, p, vk, vp, dk, dp, sz])
      (h₂ : i ∉ [t, j, jend]) (h₃ : i ∉ [t, u, best, vk, sz, k, p, vp, dk, dp, l, szp]) :
      z.regs i = y.regs i := (zr i h₁).trans (reg i h₂ h₃)
  have hvz : G.visitedOf z = insert U (G.visitedOf y) := by
    ext v
    simp only [ListInstance.visitedOf, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    rw [zvis v, hxD]
    change (_ ∧ x.mem _ = 0) ↔ _
    rw [xpos v v.isLt]
    by_cases hv : (v : ℕ) = U0
    · have hvU : v = U := Fin.ext hv
      have hd : y.mem (G.dbase + v) ≠ 0 := by rw [hv, hB0]; exact hB
      exact ⟨fun _ => Or.inl hvU, fun _ => ⟨hd, Or.inr hv⟩⟩
    · have hvU : v ≠ U := fun h => hv (by rw [h])
      simp [hv, hvU]
  have hdz : G.distOf z = G.toInstance.relax (G.distOf y) U := by
    funext v
    change decodeDist (z.mem (G.dbase + v)) = _
    rw [zD v]
    exact decode_edgesWord G hB hdu (by rw [hxD v]; rfl)
  have hz : G.OuterInv z := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, zheap, ?_⟩
    · exact (zreg zero (by decide) (by decide) (by decide)).trans hy.zero_eq
    · exact (zreg one (by decide) (by decide) (by decide)).trans hy.one_eq
    · exact (zreg two (by decide) (by decide) (by decide)).trans hy.two_eq
    · exact (zreg three (by decide) (by decide) (by decide)).trans hy.three_eq
    · exact (zreg eb (by decide) (by decide) (by decide)).trans hy.eb_eq
    · exact (zreg db (by decide) (by decide) (by decide)).trans hy.db_eq
    · exact (zreg hb (by decide) (by decide) (by decide)).trans hy.hb_eq
    · exact (zreg pb (by decide) (by decide) (by decide)).trans hy.pb_eq
    · intro a ha
      rw [zin a ha]
      exact hx a ha
    · rw [hvz, hdz]
      exact hstep
  -- The potential pays for the round.
  have hrem : G.remaining y = G.remaining z + (G.adj U).length := by
    have hs : Finset.univ.filter (· ∉ G.visitedOf y) =
        insert U (Finset.univ.filter (· ∉ insert U (G.visitedOf y))) := by
      ext v
      by_cases hv : v = U
      · subst hv
        simp [hu]
      · simp [hv]
    unfold ListInstance.remaining
    rw [hvz, hs, Finset.sum_insert (by simp), add_comm]
  have hlog : Nat.log 2 (y.regs sz) ≤ Nat.log 2 G.n := Nat.log_mono_right hy.heap.size_le
  refine ⟨z, _, ex.seq (e₁.seq (e₂.seq (e₃.seq (e₄.seq ez)))), hz, ?_⟩
  unfold ListInstance.potential
  rw [hrem]
  generalize Nat.log 2 G.n = L at hlog ⊢
  generalize (G.adj U).length = d at zsz ⊢
  generalize G.remaining z = R
  have h₁ : 100 * (L + 1) * (2 * R + z.regs sz) + 100 * (L + 1) * (d + 1) ≤
      100 * (L + 1) * (2 * (R + d) + y.regs sz) := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  have h₂ : d * (30 * L + 32) ≤ 100 * (L + 1) * d := by nlinarith
  have h₃ : 100 * (L + 1) * (d + 1) = 100 * (L + 1) * d + 100 * L + 100 := by ring
  omega

/-- When the rounds stop, with an empty heap, the output cells hold the encoded distances. -/
theorem heapExit_spec {y : Data 27} (hy : G.OuterInv y) (hsz : ¬(Cond.lt zero sz).Holds y)
    (v : Fin G.n) : y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  have hs : y.regs sz = 0 := by
    simp only [Cond.holds_lt, hy.zero_eq] at hsz
    omega
  have hd : ∀ v ∉ G.visitedOf y, G.distOf y v = ⊤ := by
    intro v hv
    have hp : y.mem (G.dbase + 2 * G.n + 1 + v) = 0 := by
      have := hy.heap.pos_le v v.isLt
      omega
    have h0 : y.mem (G.dbase + v) = 0 := by
      simpa [ListInstance.visitedOf, hp] using hv
    simp [ListInstance.distOf, h0, decodeDist]
  rw [show G.dist G.source v = G.distOf y v from
    (Instance.Inv.eq_dist G.toInstance hy.inv hd v).symm]
  exact (encodeDist_decodeDist _).symm

/-- **Correctness and running time of the structured program.** -/
theorem heapDijkstra_spec (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    ∃ y, ExecWithin w heapDijkstra (.init G.encode) y
        (200 * (G.m + 1) * (Nat.log 2 G.n + 1) + 27) ∧
      ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨x, hx, hix, hΦ⟩ := heapSetup_spec hw
  obtain ⟨y, he, hi, hc⟩ := ExecWithin.loop_potential G.OuterInv G.potential
    (fun _ h hc => heapRound_spec hw h hc) hix
  refine ⟨y, (hx.seq he).mono ?_, fun v => heapExit_spec hi hc v⟩
  nlinarith

/-- **Dijkstra's algorithm with a binary heap in `O((m + 1) (⌊log₂ n⌋ + 1))` time.** The
compiled program meets the specification `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec` with
`K = 230`. -/
theorem logLinearSpec : LogLinearSpec (heapDijkstra.program zero) 230 := by
  intro G w hw
  obtain ⟨y, ⟨m, hm, he⟩, hd⟩ := heapDijkstra_spec hw
  have hr := he.runs (pc := 0) (p := heapDijkstra.program zero)
    (Program.Contains.self _).append_left
  refine ⟨⟨heapDijkstra.size, y⟩, m, hr, ⟨y.regs zero, ?_⟩, ?_, hd⟩
  · exact step_halt (by simp [Code.program])
  · have : 1 ≤ (G.m + 1) * (Nat.log 2 G.n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith

/-- **Log-linear main theorem.** Some word-RAM program over the exact basis computes all
shortest-path distances from the source of a weighted directed graph with `n` vertices and `m`
edges, given by adjacency lists, within `O((m + 1) (⌊log₂ n⌋ + 1))` instructions. -/
theorem logLinearStatement : LogLinearStatement :=
  ⟨27, _, 230, logLinearSpec⟩

end Cslib.Algorithms.WordRAM.Dijkstra

end
