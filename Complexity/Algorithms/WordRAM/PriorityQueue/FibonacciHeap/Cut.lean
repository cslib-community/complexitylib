/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.BasicOps

/-!
# Fibonacci Heap: `decreaseKey` and Cascading Cuts

This file proves the exact-Word-RAM specification `decreaseKeyCode_exec` (`O(1)` amortized time
under `potential = 80 * (numRoots + 2 * numMarked)`):

* **No-cut key decrease (`ValidSubtree.lower_key_no_cut`):** When `v` is already a root or lowering
  `key[v]` to `k ≤ key[v]` preserves `IndexedMinPQ.PrioLT (p, key[p]) (v, k)`, `FibRawInv` holds
  without cutting any edges.
* **Single-edge cut (`cutNodeCode_raw`, `cutNode_forest`):** Executes `cutNodeCode` in at most `36`
  instructions, splicing `cur` into the circular root list, updating parent degree/child pointers,
  clearing `par[cur]` and `mark[cur]`, and adjusting `potential` by `-80` when `cur` was marked or
  `+80` when `cur` was unmarked.
* **Cascading cuts (`decreaseKeyCode_exec`):** Applies `ExecWithin.loop_potential_retain` to pay
  every cascading-cut iteration (`≤ 50` instructions including loop step) out of the `-80` drop in
  `potential`, marks the stopping non-root ancestor (`+160`), updates `minRootReg`, and restores
  `FibInv` within amortized charge `330` (`335 ≤ tDec n` including dispatch).

## Main definitions

* `cutNodeCode` and `decreaseKeyCode` are defined in
  `Complexity/Algorithms/WordRAM/PriorityQueue/FibonacciHeap/Program.lean` and verified here
  against `CutInv` and `FibInv`.

## Main results

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.cutNodeCode_raw`, `cutNode_forest`:
  single-edge pointer and forest cut specifications.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.decreaseKeyCode_exec`: `O(1)` amortized
  `decreaseKey` specification with cascading cuts.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

open Cslib.WordRAM
open Cslib.Algorithms.Lean

/-! ## Pure forest lemmas for `decreaseKey` -/

/-- Inside a valid root tree `T` with `Nodup` nodes, `st.par u = 0` holds iff `u = T.root`. -/
theorem ValidRoot.par_eq_zero_iff_root {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidRoot st pending T) {u : Fin n} (hu : u ∈ T.nodes) :
    st.par u = 0 ↔ u = T.root := by
  constructor
  · intro hp0
    rw [T.nodes_eq] at hu
    rcases List.mem_cons.mp hu with rfl | hdesc
    · rfl
    · obtain ⟨q, _, hpq⟩ := hT.1.par_of_mem_children u hdesc
      omega
  · rintro rfl
    exact hT.2.1

/-- Lowering `key[v]` to `k ≤ st.key v` preserves `ValidSubtree st' none T` whenever `v = T.root` or
`v` has parent `p` (`st.par v = p.val + 1`) with `¬IndexedMinPQ.PrioLT (v, k) (p, st.key p)`. -/
theorem ValidSubtree.lower_key_no_cut {n : ℕ} {st st' : RawState n} {T : FHTree n}
    (hT : ValidSubtree st none T) (hnd : T.nodes.Nodup) {v : Fin n} {k : ℕ}
    (hv : v ∈ T.nodes) (hle : k ≤ st.key v)
    (hk_v : st'.key v = k) (hk_other : ∀ x ∈ T.nodes, x ≠ v → st'.key x = st.key x)
    (hunch : ∀ x ∈ T.nodes,
      st'.inHeap x = st.inHeap x ∧ st'.mark x = st.mark x ∧ st'.deg x = st.deg x ∧
      st'.child x = st.child x)
    (hptr : ∀ x ∈ forestNodes T.children,
      st'.par x = st.par x ∧ st'.left x = st.left x ∧ st'.right x = st.right x)
    (hord : v = T.root ∨ ∃ p : Fin n, st.par v = p.val + 1 ∧
      ¬IndexedMinPQ.PrioLT (v, k) (p, st.key p)) :
    ValidSubtree st' none T := by
  induction hT with
  | @mk u cs hin hmark hdeg hchild hpar hprio hrank hsub ih =>
    have hu_in : u ∈ (FHTree.node u cs).nodes := List.mem_cons_self
    have hu := hunch u hu_in
    have hnd_u : u ∉ forestNodes cs := (List.nodup_cons.mp hnd).1
    have hnd_cs : (forestNodes cs).Nodup := (List.nodup_cons.mp hnd).2
    have hc_desc : ∀ c ∈ cs, c.root ∈ forestNodes cs := fun c hc =>
      mem_forestNodes_iff.mpr ⟨c, hc, c.root_mem_nodes⟩
    refine ⟨hu.1.trans_ne hin, hu.2.1 ▸ hmark, hu.2.2.1.trans hdeg, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hchild with ⟨rfl, hc0⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
      · exact Or.inl ⟨rfl, hu.2.2.2.trans hc0⟩
      · refine Or.inr ⟨h, tail, hu.2.2.2.trans hcu, hcirc.frame fun x hx => ?_, hperm⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (hperm.subset hx)
        have hp := hptr c.root (hc_desc c hc)
        exact ⟨hp.2.1, hp.2.2⟩
    · intro c hc
      exact (hptr c.root (hc_desc c hc)).1.trans (hpar c hc)
    · intro c hc
      have hcr_in : c.root ∈ (FHTree.node u cs).nodes := List.mem_cons_of_mem u (hc_desc c hc)
      have hu_ne_cr : u ≠ c.root := fun e => hnd_u (e ▸ hc_desc c hc)
      by_cases hvu : v = u
      · subst hvu
        rw [hk_v, hk_other c.root hcr_in hu_ne_cr.symm]
        exact IndexedMinPQ.PrioLT.of_le_of_lt
          (by dsimp only [IndexedMinPQ.PrioLE]; omega) (hprio c hc)
      · rw [hk_other u hu_in (Ne.symm hvu)]
        by_cases hv_cr : c.root = v
        · rw [hv_cr, hk_v]
          rcases hord with hroot | ⟨p, hpv, hnlt⟩
          · exact absurd hroot hvu
          · have hp_c := hpar c hc
            rw [hv_cr, hpv] at hp_c
            have hup : u = p := Fin.ext (by omega)
            subst hup
            have hu_ne_v : u ≠ v := hv_cr ▸ hu_ne_cr
            exact (IndexedMinPQ.prioLT_or_prioLT_of_ne hu_ne_v (st.key u) k).resolve_right hnlt
        · rw [hk_other c.root hcr_in hv_cr]
          exact hprio c hc
    · intro i hi
      have hmem : cs[i] ∈ cs := List.getElem_mem hi
      have hci := hunch (cs[i]).root (List.mem_cons_of_mem u (hc_desc cs[i] hmem))
      rw [hci.2.2.1, hci.2.1]
      exact hrank i hi
    · intro c hc
      have hnd_c : c.nodes.Nodup := forestNodes_nodup_tree hnd_cs hc
      have sub_in : ∀ x ∈ c.nodes, x ∈ (FHTree.node u cs).nodes := fun x hx =>
        List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c, hc, hx⟩)
      by_cases hvc : v ∈ c.nodes
      · refine ih c hc hnd_c hvc (fun x hx => hk_other x (sub_in x hx))
          (fun x hx => hunch x (sub_in x hx))
          (fun x hx => hptr x
            (mem_forestNodes_iff.mpr ⟨c, hc, c.nodes_eq ▸ List.mem_cons_of_mem c.root hx⟩)) ?_
        by_cases hvr : v = c.root
        · exact Or.inl hvr
        · rcases hord with hroot | hp_ord
          · rw [FHTree.root_node] at hroot
            subst hroot
            exact absurd hvc (fun hm => hnd_u (mem_forestNodes_iff.mpr ⟨c, hc, hm⟩))
          · exact Or.inr hp_ord
      · refine (hsub c hc).frame (fun x hx => ?_) (fun x hx => ?_)
        · have hx_ne : x ≠ v := fun e => hvc (e ▸ hx)
          have hxn := hunch x (sub_in x hx)
          exact ⟨hxn.1, hxn.2.1, hxn.2.2.1, hxn.2.2.2, hk_other x (sub_in x hx) hx_ne⟩
        · have hxp := hptr x
            (mem_forestNodes_iff.mpr ⟨c, hc, c.nodes_eq ▸ List.mem_cons_of_mem c.root hx⟩)
          exact ⟨hxp.1, hxp.2.1, hxp.2.2, Iff.rfl⟩

/-- Scalar counter bounds under `CutInv`. -/
theorem CutInv.bounds {n K_max : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    {v m : Fin n} {pending : Option (Fin n)} (h : CutInv n K_max s st v m pending) :
    st.sz ≤ n ∧ st.numRoots ≤ n ∧ st.numMarked ≤ n ∧ st.minRoot ≤ n := by
  obtain ⟨ts, _, hnd, _, _, _, hsz, hnr, hnm, _, ⟨_, hm, _, _⟩, _, _⟩ := h
  have hfn_le : (forestNodes ts).length ≤ n := by simpa using hnd.length_le_card
  have hts_le : ts.length ≤ n := (forestNodes_length_ge ts).trans hfn_le
  have hdom_le : (IndexedMinPQ.dom s).card ≤ n :=
    (Finset.card_le_univ _).trans (by simp only [Fintype.card_fin, le_rfl])
  have hm_le : markedCount st ≤ n := markedCount_le_n st
  have := m.isLt
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Once cascading cuts finish (`pending = none`) and `minRoot` is updated against `(v, st.key v)`,
`CutInv` upgrades back to `FibRawInv`. -/
theorem CutInv.to_fibRawInv {n K_max : ℕ} {s : IndexedMinPQ.State n} {st st' : RawState n}
    {v m : Fin n} (h : CutInv n K_max s st v m none)
    (heq : st'.key = st.key ∧ st'.par = st.par ∧ st'.child = st.child ∧
      st'.left = st.left ∧ st'.right = st.right ∧ st'.deg = st.deg ∧
      st'.mark = st.mark ∧ st'.inHeap = st.inHeap ∧ st'.cons = st.cons ∧
      st'.numRoots = st.numRoots ∧ st'.numMarked = st.numMarked ∧ st'.sz = st.sz)
    (hmin : (IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m) ∧ st'.minRoot = v.val + 1) ∨
      (¬IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m) ∧ st'.minRoot = m.val + 1)) :
    FibRawInv n K_max s st' := by
  obtain ⟨ts, hts, hnd, hdom, hin, hkeys, hsz, hnr, hnm, hcons,
    ⟨rtail, _, hcirc, hperm⟩, ⟨T_v, hTv, hTv_r⟩, hmin_other⟩ := h
  rcases heq with ⟨hk, hp, hch, hl, hr, hd, hmk, hinh, hco, hnrr, hnmr, hszr⟩
  have hts' : ∀ T ∈ ts, ValidRoot st' none T := fun T hT => by
    have hT0 := hts T hT
    exact ⟨hT0.1.frame
      (fun x _ => ⟨by rw [hinh], by rw [hmk], by rw [hd], by rw [hch], by rw [hk]⟩)
      (fun x _ => ⟨by rw [hp], by rw [hl], by rw [hr], Iff.rfl⟩),
      by rw [hp]; exact hT0.2.1, by rw [hmk]; exact hT0.2.2⟩
  have hm_cnt : markedCount st' = markedCount st :=
    markedCount_congr fun u => by rw [hinh, hmk]
  refine ⟨ts, hts', hnd, hdom,
    fun x => by rw [hinh]; exact hin x,
    fun x kx hsx => by rw [hk]; exact hkeys x kx hsx,
    hszr.trans hsz, hnrr.trans hnr, hnmr.trans (hnm.trans hm_cnt.symm),
    fun d hdn => by rw [hco]; exact hcons d hdn, ?_⟩
  rw [hl, hr]
  rcases hmin with ⟨hlt, hmin_v⟩ | ⟨hnlt, hmin_m⟩
  · have hv_map : v ∈ ts.map FHTree.root := hTv_r ▸ List.mem_map_of_mem hTv
    have hv_mr : v ∈ m :: rtail := hperm.symm.subset hv_map
    obtain ⟨vtail, hcirc_v, hperm_v⟩ := hcirc.exists_head hv_mr
    refine Or.inr ⟨v, vtail, hmin_v, hcirc_v, hperm_v.trans hperm, fun T hT => ?_⟩
    rw [hk]
    by_cases hTr : T.root = v
    · rw [hTr]; exact IndexedMinPQ.PrioLE.refl _
    · exact (IndexedMinPQ.PrioLT.le hlt).trans (hmin_other T hT hTr)
  · refine Or.inr ⟨m, rtail, hmin_m, hcirc, hperm, fun T hT => ?_⟩
    rw [hk]
    by_cases hTr : T.root = v
    · rw [hTr]; exact IndexedMinPQ.not_prioLT_iff_prioLE.mp hnlt
    · exact hmin_other T hT hTr

/-! ## `evalCascGuard` specification -/

/-- `evalCascGuard` sets `iterCur ← 1` iff `par[cur] ≠ 0 ∧ mark[cur] ≠ 0`, and `0` otherwise, in
at most `8` instructions while preserving `BaseRegs`, `RawState.ofData`, and all registers other
than `s0, s1, s2, iterCur`. -/
theorem evalCascGuard_exec {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x) {cur : Fin n} (hz_reg : x.regs zReg = cur.val) :
    let st := RawState.ofData n base x
    let gval := if st.par cur ≠ 0 ∧ st.mark cur ≠ 0 then 1 else 0
    ∃ y, ExecWithin w evalCascGuard x y 8 ∧
      BaseRegs n base y ∧
      RawState.ofData n base y = st ∧
      y.mem = x.mem ∧
      y.regs iterCur = gval ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ iterCur → y.regs r = x.regs r) := by
  intro st gval
  have hfit_stop := hbr.fits_stop hb
  have hp_b : x.regs parBase = base + n := hbr.2.2.2.1
  have hm_b : x.regs markBase = base + 6 * n := hbr.2.2.2.2.2.2.2.2.1
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  have hcur_lt := cur.isLt
  let x1 := (x.set s0 (base + n + cur.val)).set s1 (st.par cur)
  have ea1 : ExecWithin w (.op (.exactBin .add s0 parBase zReg)) x
      (x.set s0 (base + n + cur.val)) 1 := by
    simpa only [hp_b, hz_reg] using
      execWithin_exactAdd (x := x) (d := s0) (i := parBase) (j := zReg)
        (by rw [hp_b, hz_reg]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have el1 : ExecWithin (B := .exact) w (.op (.load s1 s0))
      (x.set s0 (base + n + cur.val)) x1 1 := by
    have hmem_p : x.mem (base + n + cur.val) = st.par cur := rfl
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hmem_p] using
      (ExecWithin.load (B := .exact) (w := w) (x := x.set s0 (base + n + cur.val))
        (d := s1) (a := s0))
  have hx1_z : x1.regs zeroP = 0 := by
    simp only [x1, Data.set_regs, Function.update_of_ne (by decide : zeroP ≠ s1),
      Function.update_of_ne (by decide : zeroP ≠ s0), hz0]
  have hx1_o : x1.regs oneP = 1 := by
    simp only [x1, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ s1),
      Function.update_of_ne (by decide : oneP ≠ s0), ho1]
  by_cases hpar0 : st.par cur = 0
  · have hc1 : ¬(Cond.lt zeroP s1).Holds x1 := by
      rw [Cond.Holds, hx1_z]
      simp only [x1, Data.set_regs, Function.update_self, hpar0,
        lt_self_iff_false, not_false_eq_true]
    let y := x1.set iterCur 0
    have he : ExecWithin w evalCascGuard x y 8 := by
      unfold evalCascGuard
      exact (ea1.seq <| el1.seq <| ExecWithin.branch_neg hc1
        (by simpa only [hx1_z] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x1) (d := iterCur) (s := zeroP)))).mono
        (by omega)
    have hg : gval = 0 := by
      simp only [gval, hpar0, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    refine ⟨y, he,
      ((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _,
      by simp only [y, x1, ofData_set_scratch _ (by decide : 17 ≤ iterCur.val),
        ofData_set_scratch _ (by decide : 17 ≤ s1.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val)]; rfl,
      rfl,
      by simp only [y, Data.set_regs, Function.update_self, hg],
      fun r h0 h1 _ hi => by
        simp only [y, x1, Data.set_regs, Function.update_of_ne hi, Function.update_of_ne h1,
          Function.update_of_ne h0]⟩
  · have hc1 : (Cond.lt zeroP s1).Holds x1 := by
      rw [Cond.Holds, hx1_z]
      simp only [x1, Data.set_regs, Function.update_self]
      omega
    have hx1_mb : x1.regs markBase = base + 6 * n := by
      simp only [x1, Data.set_regs, Function.update_of_ne (by decide : markBase ≠ s1),
        Function.update_of_ne (by decide : markBase ≠ s0), hm_b]
    have hx1_zr : x1.regs zReg = cur.val := by
      simp only [x1, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ s1),
        Function.update_of_ne (by decide : zReg ≠ s0), hz_reg]
    let x2 := (x1.set s0 (base + 6 * n + cur.val)).set s2 (st.mark cur)
    have ea2 : ExecWithin w (.op (.exactBin .add s0 markBase zReg)) x1
        (x1.set s0 (base + 6 * n + cur.val)) 1 := by
      simpa only [hx1_mb, hx1_zr] using
        execWithin_exactAdd (x := x1) (d := s0) (i := markBase) (j := zReg)
          (by rw [hx1_mb, hx1_zr]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
    have el2 : ExecWithin (B := .exact) w (.op (.load s2 s0))
        (x1.set s0 (base + 6 * n + cur.val)) x2 1 := by
      have hmem_m : x1.mem (base + 6 * n + cur.val) = st.mark cur := rfl
      simpa only [Data.set_mem, Data.set_regs, Function.update_self, hmem_m] using
        (ExecWithin.load (B := .exact) (w := w) (x := x1.set s0 (base + 6 * n + cur.val))
          (d := s2) (a := s0))
    have hx2_z : x2.regs zeroP = 0 := by
      simp only [x2, Data.set_regs, Function.update_of_ne (by decide : zeroP ≠ s2),
        Function.update_of_ne (by decide : zeroP ≠ s0), hx1_z]
    have hx2_o : x2.regs oneP = 1 := by
      simp only [x2, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ s2),
        Function.update_of_ne (by decide : oneP ≠ s0), hx1_o]
    by_cases hmk0 : st.mark cur = 0
    · have hc2 : ¬(Cond.lt zeroP s2).Holds x2 := by
        rw [Cond.Holds, hx2_z]
        simp only [x2, Data.set_regs, Function.update_self, hmk0,
          lt_self_iff_false, not_false_eq_true]
      let y := x2.set iterCur 0
      have he : ExecWithin w evalCascGuard x y 8 := by
        unfold evalCascGuard
        exact (ea1.seq <| el1.seq <| ExecWithin.branch_pos hc1
          (ea2.seq <| el2.seq <| ExecWithin.branch_neg hc2
            (by simpa only [hx2_z] using
              (ExecWithin.copy (B := .exact) (w := w) (x := x2) (d := iterCur) (s := zeroP))))).mono
          (by omega)
      have hg : gval = 0 := by
        simp only [gval, hmk0, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
      refine ⟨y, he,
        ((((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
          (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _,
        by simp only [y, x2, x1, ofData_set_scratch _ (by decide : 17 ≤ iterCur.val),
          ofData_set_scratch _ (by decide : 17 ≤ s2.val),
          ofData_set_scratch _ (by decide : 17 ≤ s1.val),
          ofData_set_scratch _ (by decide : 17 ≤ s0.val)]; rfl,
        rfl,
        by simp only [y, Data.set_regs, Function.update_self, hg],
        fun r h0 h1 h2 hi => by
          simp only [y, x2, x1, Data.set_regs, Function.update_of_ne hi,
            Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]⟩
    · have hc2 : (Cond.lt zeroP s2).Holds x2 := by
        rw [Cond.Holds, hx2_z]
        simp only [x2, Data.set_regs, Function.update_self]
        omega
      let y := x2.set iterCur 1
      have he : ExecWithin w evalCascGuard x y 8 := by
        unfold evalCascGuard
        exact (ea1.seq <| el1.seq <| ExecWithin.branch_pos hc1
          (ea2.seq <| el2.seq <| ExecWithin.branch_pos hc2
            (by simpa only [hx2_o] using
              (ExecWithin.copy (B := .exact) (w := w) (x := x2) (d := iterCur) (s := oneP))))).mono
          (by omega)
      have hg : gval = 1 := by
        simp only [gval, ne_eq, hpar0, hmk0, not_false_eq_true, and_self, ↓reduceIte]
      refine ⟨y, he,
        ((((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
          (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _,
        by simp only [y, x2, x1, ofData_set_scratch _ (by decide : 17 ≤ iterCur.val),
          ofData_set_scratch _ (by decide : 17 ≤ s2.val),
          ofData_set_scratch _ (by decide : 17 ≤ s1.val),
          ofData_set_scratch _ (by decide : 17 ≤ s0.val)]; rfl,
        rfl,
        by simp only [y, Data.set_regs, Function.update_self, hg],
        fun r h0 h1 h2 hi => by
          simp only [y, x2, x1, Data.set_regs, Function.update_of_ne hi,
            Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]⟩

/-! ## `cutNodeCode` machine execution -/

/-- Raw machine specification of `cutNodeCode`: cuts `cur` (`zReg`) from `p` (`pReg`) and splices
`cur` after `m` (`minRootReg = m.val + 1`) in at most `36` instructions. -/
theorem cutNodeCode_raw {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {cur p m : Fin n} {rtail : List (Fin n)}
    (hz_reg : x.regs zReg = cur.val) (hp_reg : x.regs pReg = p.val)
    (hdp_pos : 1 ≤ (RawState.ofData n base x).deg p)
    (hdp_le : (RawState.ofData n base x).deg p ≤ n)
    (hdp2 : 2 ≤ (RawState.ofData n base x).deg p →
      ∃ (h : Fin n) (tail : List (Fin n)),
        (RawState.ofData n base x).child p = h.val + 1 ∧
        IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right (h :: tail) ∧
        cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧
        ∀ u ∈ h :: tail, (RawState.ofData n base x).par u = p.val + 1)
    (hmin : (RawState.ofData n base x).minRoot = m.val + 1)
    (hcirc_r : IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right
      (m :: rtail))
    (hroots_par0 : ∀ u ∈ m :: rtail, (RawState.ofData n base x).par u = 0)
    (hpar_cur : (RawState.ofData n base x).par cur = p.val + 1)
    (hin_cur : (RawState.ofData n base x).inHeap cur ≠ 0)
    (hnm : (RawState.ofData n base x).numMarked = markedCount (RawState.ofData n base x))
    (hnr_le : (RawState.ofData n base x).numRoots + 1 ≤ n) :
    ∃ y, ExecWithin w cutNodeCode x y 36 ∧
      BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 →
        r ≠ numMarkedReg → r ≠ numRootsReg → y.regs r = x.regs r) ∧
      (let st := RawState.ofData n base x
       let st' := RawState.ofData n base y
       st'.key = st.key ∧ st'.inHeap = st.inHeap ∧ st'.cons = st.cons ∧
       st'.minRoot = st.minRoot ∧ st'.sz = st.sz ∧
       st'.numRoots = st.numRoots + 1 ∧
       st'.numMarked = markedCount st' ∧
       ((st.mark cur ≠ 0 → potential y + unitCredit = potential x) ∧
        (st.mark cur = 0 → potential y = potential x + unitCredit)) ∧
       (st'.mark cur = 0 ∧ ∀ u, u ≠ cur → st'.mark u = st.mark u) ∧
       (st'.deg p + 1 = st.deg p ∧ ∀ u, u ≠ p → st'.deg u = st.deg u) ∧
       (st'.par cur = 0 ∧ ∀ u, u ≠ cur → st'.par u = st.par u) ∧
       (∀ u, u ≠ p → st'.child u = st.child u) ∧
       (st.deg p = 1 → st'.child p = 0) ∧
       (∀ (h : Fin n) (tail : List (Fin n)),
         2 ≤ st.deg p → st.child p = h.val + 1 →
         IsCircList st.left st.right (h :: tail) → cur ∈ h :: tail →
         ∃ (r_c : Fin n) (rest : List (Fin n)),
           st'.child p = r_c.val + 1 ∧
           IsCircList st'.left st'.right (r_c :: rest) ∧
           (r_c :: rest).Perm ((h :: tail).erase cur)) ∧
       IsCircList st'.left st'.right (m :: cur :: rtail) ∧
       (∀ u, st.par u ≠ p.val + 1 → st.par u ≠ 0 →
         st'.left u = st.left u ∧ st'.right u = st.right u)) := by
  have hfit_stop := hbr.fits_stop hb
  set st := RawState.ofData n base x with hst_def
  have hp_lt := p.isLt
  have hcur_lt := cur.isLt
  have hm_lt := m.isLt
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  have hd_b : x.regs degBase = base + 5 * n := hbr.2.2.2.2.2.2.2.1
  -- Step 1: decrement deg[p] (`x → x1` in 4 steps)
  let dp' := st.deg p - 1
  have ho_dp := owns_arr_addr (base := base) (k := 5) (by decide) hp_lt
  let x1 := (((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)).set s1 dp').write
    (base + 5 * n + p.val) dp'
  have e_deg1 : ExecWithin w (.op (.exactBin .add s0 degBase pReg)) x
      (x.set s0 (base + 5 * n + p.val)) 1 := by
    simpa only [hd_b, hp_reg] using
      execWithin_exactAdd (x := x) (d := s0) (i := degBase) (j := pReg)
        (by rw [hd_b, hp_reg]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have e_deg2 : ExecWithin (B := .exact) w (.op (.load s1 s0))
      (x.set s0 (base + 5 * n + p.val))
      ((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)) 1 := by
    have hmem_dp : x.mem (base + 5 * n + p.val) = st.deg p := rfl
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hmem_dp] using
      (ExecWithin.load (B := .exact) (w := w) (x := x.set s0 (base + 5 * n + p.val))
        (d := s1) (a := s0))
  have e_deg3 : ExecWithin w (.op (.exactBin .sub s1 s1 oneP))
      ((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p))
      (((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)).set s1 dp') 1 := by
    have hs1_v : ((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)).regs s1 = st.deg p := by
      simp only [Data.set_regs, Function.update_self]
    have ho1_v : ((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)).regs oneP = 1 := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : oneP ≠ s1),
        Function.update_of_ne (by decide : oneP ≠ s0), ho1]
    simpa only [hs1_v, ho1_v] using
      execWithin_exactSub (x := (x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p))
        (d := s1) (i := s1) (j := oneP) (by rw [hs1_v, ho1_v]; omega)
        (by rw [hs1_v, ho1_v]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have e_deg4 : ExecWithin (B := .exact) w (.op (.store s0 s1))
      (((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)).set s1 dp') x1 1 := by
    have hs0_v : (((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)).set s1 dp').regs s0 =
        base + 5 * n + p.val := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : s0 ≠ s1), Function.update_self]
    have hs1_v : (((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)).set s1 dp').regs s1 =
        dp' := by
      simp only [Data.set_regs, Function.update_self]
    simpa only [hs0_v, hs1_v] using
      (ExecWithin.store (B := .exact) (w := w)
        (x := ((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)).set s1 dp')
        (a := s0) (s := s1))
  have hbr1 : BaseRegs n base x1 :=
    (((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
      (by decide) _).write_eq _ _
  have hb1 : x1.Bounded w :=
    e_deg4.bounded (e_deg3.bounded (e_deg2.bounded (e_deg1.bounded hb)))
  have hmod1 : Modifies (Block.mk base (space n)).footprint x.mem x1.mem :=
    Modifies.write_of_owns ho_dp dp'
  have hst1 : RawState.ofData n base x1 = { st with deg := Function.update st.deg p dp' } := by
    simp only [x1, ofData_write_deg, ofData_set_scratch _ (by decide : 17 ≤ s1.val),
      ofData_set_scratch _ (by decide : 17 ≤ s0.val), ← hst_def]
  have hx1_reg : ∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → x1.regs r = x.regs r := fun r h0 h1 => by
    simp only [x1, Data.write_regs, Data.set_regs, Function.update_of_ne h1,
      Function.update_of_ne h0]
  -- Step 2: branch on `s1 = zeroP` (`x1 → x2` in at most 13 steps)
  let cBranch : Code .exact rFib :=
    .branch (.eq s1 zeroP)
      (.seq (.op (.exactBin .add s0 childBase pReg)) (.op (.store s0 zeroP)))
      (.seq (.op (.exactBin .add s0 rightBase zReg)) <|
       .seq (.op (.load s2 s0)) <|
       .seq (.op (.exactBin .add s0 leftBase zReg)) <|
       .seq (.op (.load s3 s0)) <|
       .seq (.op (.exactBin .add s0 leftBase s2)) <|
       .seq (.op (.store s0 s3)) <|
       .seq (.op (.exactBin .add s0 rightBase s3)) <|
       .seq (.op (.store s0 s2)) <|
       .seq (.op (.exactBin .add s4 s2 oneP)) <|
       .seq (.op (.exactBin .add s0 childBase pReg)) <|
            (.op (.store s0 s4)))
  have hstep2 : ∃ x2, ExecWithin w cBranch x1 x2 13 ∧
      BaseRegs n base x2 ∧ x2.Bounded w ∧
      Modifies (Block.mk base (space n)).footprint x1.mem x2.mem ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s2 → r ≠ s3 → r ≠ s4 → x2.regs r = x1.regs r) ∧
      (let st2 := RawState.ofData n base x2
       st2.key = st.key ∧ st2.par = st.par ∧ st2.deg = Function.update st.deg p dp' ∧
       st2.mark = st.mark ∧ st2.inHeap = st.inHeap ∧ st2.cons = st.cons ∧
       st2.minRoot = st.minRoot ∧ st2.numRoots = st.numRoots ∧
       st2.numMarked = st.numMarked ∧ st2.sz = st.sz ∧
       (∀ u, u ≠ p → st2.child u = st.child u) ∧
       (st.deg p = 1 → st2.child p = 0) ∧
       (∀ (h : Fin n) (tail : List (Fin n)),
         2 ≤ st.deg p → st.child p = h.val + 1 →
         IsCircList st.left st.right (h :: tail) → cur ∈ h :: tail →
         ∃ (r_c : Fin n) (rest : List (Fin n)),
           st2.child p = r_c.val + 1 ∧
           IsCircList st2.left st2.right (r_c :: rest) ∧
           (r_c :: rest).Perm ((h :: tail).erase cur)) ∧
       IsCircList st2.left st2.right (m :: rtail) ∧
       (∀ u, st.par u ≠ p.val + 1 → st2.left u = st.left u ∧ st2.right u = st.right u)) := by
    have hx1_s1 : x1.regs s1 = dp' := by
      simp only [x1, Data.write_regs, Data.set_regs, Function.update_self]
    have hx1_z0 : x1.regs zeroP = 0 := hbr1.2.2.2.2.2.2.2.2.2.2.2.1
    have hx1_o1 : x1.regs oneP = 1 := hbr1.2.2.2.2.2.2.2.2.2.2.2.2
    have hx1_cb : x1.regs childBase = base + 2 * n := hbr1.2.2.2.2.1
    have hx1_p : x1.regs pReg = p.val := (hx1_reg pReg (by decide) (by decide)).trans hp_reg
    have hx1_z : x1.regs zReg = cur.val := (hx1_reg zReg (by decide) (by decide)).trans hz_reg
    have ho_cp := owns_arr_addr (base := base) (k := 2) (by decide) hp_lt
    by_cases hdp1 : dp' = 0
    · have hc : (Cond.eq s1 zeroP).Holds x1 := by simp only [Cond.Holds, hx1_s1, hx1_z0, hdp1]
      let x2 := (x1.set s0 (base + 2 * n + p.val)).write (base + 2 * n + p.val) 0
      have ea : ExecWithin w (.op (.exactBin .add s0 childBase pReg)) x1
          (x1.set s0 (base + 2 * n + p.val)) 1 := by
        simpa only [hx1_cb, hx1_p] using
          execWithin_exactAdd (x := x1) (d := s0) (i := childBase) (j := pReg)
            (by rw [hx1_cb, hx1_p]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
      have es : ExecWithin (B := .exact) w (.op (.store s0 zeroP))
          (x1.set s0 (base + 2 * n + p.val)) x2 1 := by
        have hs0 : (x1.set s0 (base + 2 * n + p.val)).regs s0 = base + 2 * n + p.val := by
          simp only [Data.set_regs, Function.update_self]
        have hz : (x1.set s0 (base + 2 * n + p.val)).regs zeroP = 0 := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : zeroP ≠ s0), hx1_z0]
        simpa only [hs0, hz] using
          (ExecWithin.store (B := .exact) (w := w) (x := x1.set s0 (base + 2 * n + p.val))
            (a := s0) (s := zeroP))
      have he2 : ExecWithin w cBranch x1 x2 13 :=
        (ExecWithin.branch_pos hc (ea.seq es)).mono (by omega)
      have hst2 : RawState.ofData n base x2 =
          { RawState.ofData n base x1 with child := Function.update st.child p 0 } := by
        simp only [x2, ofData_write_child, ofData_set_scratch _ (by decide : 17 ≤ s0.val), hst1]
      refine ⟨x2, he2, (hbr1.set_non_base (by decide) _).write_eq _ _, he2.bounded hb1,
        Modifies.write_of_owns ho_cp 0,
        fun r h0 _ _ _ => by
          simp only [x2, Data.write_regs, Data.set_regs, Function.update_of_ne h0],
        ?_⟩
      dsimp only
      rw [hst2, hst1]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun u hu => Function.update_of_ne hu 0 st.child,
        fun _ => Function.update_self p 0 st.child,
        fun _ _ hge2 => absurd hge2 (by omega),
        hcirc_r, fun _ _ => ⟨rfl, rfl⟩⟩
    · have hc : ¬(Cond.eq s1 zeroP).Holds x1 := by
        simp only [Cond.Holds, hx1_s1, hx1_z0]; exact hdp1
      have hge2 : 2 ≤ st.deg p := by omega
      obtain ⟨h_w, tail_w, hcp_w, hcirc_w, hcur_w, hlen_w, hpar_w⟩ := hdp2 hge2
      obtain ⟨r_nb, l_nb, rest_w, hr_cur, hl_cur, hr_mem_w, hl_mem_w, _, hcirc_rem_w, _⟩ :=
        hcirc_w.remove hcur_w hlen_w
      have hx1_lb : x1.regs leftBase = base + 3 * n := hbr1.2.2.2.2.2.1
      have hx1_rb : x1.regs rightBase = base + 4 * n := hbr1.2.2.2.2.2.2.1
      have hr_lt := r_nb.isLt
      have hl_lt := l_nb.isLt
      have ho_lr := owns_arr_addr (base := base) (k := 3) (by decide) hr_lt
      have ho_rl := owns_arr_addr (base := base) (k := 4) (by decide) hl_lt
      let sA := ((x1.set s0 (base + 4 * n + cur.val)).set s2 r_nb.val)
      let sB := ((sA.set s0 (base + 3 * n + cur.val)).set s3 l_nb.val)
      let sC := (sB.set s0 (base + 3 * n + r_nb.val)).write (base + 3 * n + r_nb.val) l_nb.val
      let sD := (sC.set s0 (base + 4 * n + l_nb.val)).write (base + 4 * n + l_nb.val) r_nb.val
      let sE := sD.set s4 (r_nb.val + 1)
      let x2 := (sE.set s0 (base + 2 * n + p.val)).write (base + 2 * n + p.val) (r_nb.val + 1)
      have ea1 : ExecWithin w (.op (.exactBin .add s0 rightBase zReg)) x1
          (x1.set s0 (base + 4 * n + cur.val)) 1 := by
        simpa only [hx1_rb, hx1_z] using
          execWithin_exactAdd (x := x1) (d := s0) (i := rightBase) (j := zReg)
            (by rw [hx1_rb, hx1_z]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
      have el1 : ExecWithin (B := .exact) w (.op (.load s2 s0))
          (x1.set s0 (base + 4 * n + cur.val)) sA 1 := by
        have hmem_r : x1.mem (base + 4 * n + cur.val) = r_nb.val := by
          have : (RawState.ofData n base x1).right cur = r_nb.val := by rw [hst1]; exact hr_cur
          exact this
        simpa only [Data.set_mem, Data.set_regs, Function.update_self, hmem_r] using
          (ExecWithin.load (B := .exact) (w := w) (x := x1.set s0 (base + 4 * n + cur.val))
            (d := s2) (a := s0))
      have ea2 : ExecWithin w (.op (.exactBin .add s0 leftBase zReg)) sA
          (sA.set s0 (base + 3 * n + cur.val)) 1 := by
        have hlb : sA.regs leftBase = base + 3 * n := by
          simp only [sA, Data.set_regs, Function.update_of_ne (by decide : leftBase ≠ s2),
            Function.update_of_ne (by decide : leftBase ≠ s0), hx1_lb]
        have hz : sA.regs zReg = cur.val := by
          simp only [sA, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ s2),
            Function.update_of_ne (by decide : zReg ≠ s0), hx1_z]
        simpa only [hlb, hz] using
          execWithin_exactAdd (x := sA) (d := s0) (i := leftBase) (j := zReg)
            (by rw [hlb, hz]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
      have el2 : ExecWithin (B := .exact) w (.op (.load s3 s0))
          (sA.set s0 (base + 3 * n + cur.val)) sB 1 := by
        have hmem_l : sA.mem (base + 3 * n + cur.val) = l_nb.val := by
          have : (RawState.ofData n base x1).left cur = l_nb.val := by rw [hst1]; exact hl_cur
          exact this
        simpa only [Data.set_mem, Data.set_regs, Function.update_self, hmem_l] using
          (ExecWithin.load (B := .exact) (w := w) (x := sA.set s0 (base + 3 * n + cur.val))
            (d := s3) (a := s0))
      have ea3 : ExecWithin w (.op (.exactBin .add s0 leftBase s2)) sB
          (sB.set s0 (base + 3 * n + r_nb.val)) 1 := by
        have hlb : sB.regs leftBase = base + 3 * n := by
          simp only [sB, sA, Data.set_regs, Function.update_of_ne (by decide : leftBase ≠ s3),
            Function.update_of_ne (by decide : leftBase ≠ s2),
            Function.update_of_ne (by decide : leftBase ≠ s0), hx1_lb]
        have hs2 : sB.regs s2 = r_nb.val := by
          simp only [sB, sA, Data.set_regs, Function.update_of_ne (by decide : s2 ≠ s3),
            Function.update_of_ne (by decide : s2 ≠ s0), Function.update_self]
        simpa only [hlb, hs2] using
          execWithin_exactAdd (x := sB) (d := s0) (i := leftBase) (j := s2)
            (by rw [hlb, hs2]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
      have es3 : ExecWithin (B := .exact) w (.op (.store s0 s3))
          (sB.set s0 (base + 3 * n + r_nb.val)) sC 1 := by
        have hs0 : (sB.set s0 (base + 3 * n + r_nb.val)).regs s0 = base + 3 * n + r_nb.val := by
          simp only [Data.set_regs, Function.update_self]
        have hs3 : (sB.set s0 (base + 3 * n + r_nb.val)).regs s3 = l_nb.val := by
          simp only [sB, Data.set_regs, Function.update_of_ne (by decide : s3 ≠ s0),
            Function.update_self]
        simpa only [hs0, hs3] using
          (ExecWithin.store (B := .exact) (w := w) (x := sB.set s0 (base + 3 * n + r_nb.val))
            (a := s0) (s := s3))
      have ea4 : ExecWithin w (.op (.exactBin .add s0 rightBase s3)) sC
          (sC.set s0 (base + 4 * n + l_nb.val)) 1 := by
        have hrb : sC.regs rightBase = base + 4 * n := by
          simp only [sC, sB, sA, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : rightBase ≠ s3),
            Function.update_of_ne (by decide : rightBase ≠ s2),
            Function.update_of_ne (by decide : rightBase ≠ s0), hx1_rb]
        have hs3 : sC.regs s3 = l_nb.val := by
          simp only [sC, sB, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s3 ≠ s0), Function.update_self]
        simpa only [hrb, hs3] using
          execWithin_exactAdd (x := sC) (d := s0) (i := rightBase) (j := s3)
            (by rw [hrb, hs3]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
      have es4 : ExecWithin (B := .exact) w (.op (.store s0 s2))
          (sC.set s0 (base + 4 * n + l_nb.val)) sD 1 := by
        have hs0 : (sC.set s0 (base + 4 * n + l_nb.val)).regs s0 = base + 4 * n + l_nb.val := by
          simp only [Data.set_regs, Function.update_self]
        have hs2 : (sC.set s0 (base + 4 * n + l_nb.val)).regs s2 = r_nb.val := by
          simp only [sC, sB, sA, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s2 ≠ s3),
            Function.update_of_ne (by decide : s2 ≠ s0), Function.update_self]
        simpa only [hs0, hs2] using
          (ExecWithin.store (B := .exact) (w := w) (x := sC.set s0 (base + 4 * n + l_nb.val))
            (a := s0) (s := s2))
      have ea5 : ExecWithin w (.op (.exactBin .add s4 s2 oneP)) sD sE 1 := by
        have hs2 : sD.regs s2 = r_nb.val := by
          simp only [sD, sC, sB, sA, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s2 ≠ s3),
            Function.update_of_ne (by decide : s2 ≠ s0), Function.update_self]
        have ho : sD.regs oneP = 1 := by
          simp only [sD, sC, sB, sA, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : oneP ≠ s3),
            Function.update_of_ne (by decide : oneP ≠ s2),
            Function.update_of_ne (by decide : oneP ≠ s0), hx1_o1]
        simpa only [hs2, ho] using
          execWithin_exactAdd (x := sD) (d := s4) (i := s2) (j := oneP)
            (by rw [hs2, ho]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
      have ea6 : ExecWithin w (.op (.exactBin .add s0 childBase pReg)) sE
          (sE.set s0 (base + 2 * n + p.val)) 1 := by
        have hcb : sE.regs childBase = base + 2 * n := by
          simp only [sE, sD, sC, sB, sA, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : childBase ≠ s4),
            Function.update_of_ne (by decide : childBase ≠ s3),
            Function.update_of_ne (by decide : childBase ≠ s2),
            Function.update_of_ne (by decide : childBase ≠ s0), hx1_cb]
        have hpv : sE.regs pReg = p.val := by
          simp only [sE, sD, sC, sB, sA, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : pReg ≠ s4),
            Function.update_of_ne (by decide : pReg ≠ s3),
            Function.update_of_ne (by decide : pReg ≠ s2),
            Function.update_of_ne (by decide : pReg ≠ s0), hx1_p]
        simpa only [hcb, hpv] using
          execWithin_exactAdd (x := sE) (d := s0) (i := childBase) (j := pReg)
            (by rw [hcb, hpv]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
      have es6 : ExecWithin (B := .exact) w (.op (.store s0 s4))
          (sE.set s0 (base + 2 * n + p.val)) x2 1 := by
        have hs0 : (sE.set s0 (base + 2 * n + p.val)).regs s0 = base + 2 * n + p.val := by
          simp only [Data.set_regs, Function.update_self]
        have hs4 : (sE.set s0 (base + 2 * n + p.val)).regs s4 = r_nb.val + 1 := by
          simp only [sE, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s0),
            Function.update_self]
        simpa only [hs0, hs4] using
          (ExecWithin.store (B := .exact) (w := w) (x := sE.set s0 (base + 2 * n + p.val))
            (a := s0) (s := s4))
      have he2 : ExecWithin w cBranch x1 x2 13 :=
        (ExecWithin.branch_neg hc
          (ea1.seq <| el1.seq <| ea2.seq <| el2.seq <| ea3.seq <| es3.seq <|
           ea4.seq <| es4.seq <| ea5.seq <| ea6.seq es6)).mono (by omega)
      have hbr2 : BaseRegs n base x2 := by
        have hbA : BaseRegs n base sA :=
          (hbr1.set_non_base (d := s0) (by decide) _).set_non_base (d := s2) (by decide) _
        have hbB : BaseRegs n base sB :=
          (hbA.set_non_base (d := s0) (by decide) _).set_non_base (d := s3) (by decide) _
        have hbC : BaseRegs n base sC :=
          (hbB.set_non_base (d := s0) (by decide) _).write_eq _ _
        have hbD : BaseRegs n base sD :=
          (hbC.set_non_base (d := s0) (by decide) _).write_eq _ _
        have hbE : BaseRegs n base sE := hbD.set_non_base (d := s4) (by decide) _
        exact (hbE.set_non_base (d := s0) (by decide) _).write_eq _ _
      have hmod2 : Modifies (Block.mk base (space n)).footprint x1.mem x2.mem :=
        modifies_block_trans (Modifies.write_of_owns ho_lr l_nb.val) <|
          modifies_block_trans (Modifies.write_of_owns ho_rl r_nb.val)
            (Modifies.write_of_owns ho_cp (r_nb.val + 1))
      have hst2 : RawState.ofData n base x2 =
          { st with
            deg := Function.update st.deg p dp'
            child := Function.update st.child p (r_nb.val + 1)
            left := Function.update st.left r_nb l_nb.val
            right := Function.update st.right l_nb r_nb.val } := by
        simp only [x2, sE, sD, sC, sB, sA, ofData_write_child, ofData_write_right,
          ofData_write_left, ofData_set_scratch _ (by decide : 17 ≤ s4.val),
          ofData_set_scratch _ (by decide : 17 ≤ s3.val),
          ofData_set_scratch _ (by decide : 17 ≤ s2.val),
          ofData_set_scratch _ (by decide : 17 ≤ s0.val), hst1]
      have hpar_rnb : st.par r_nb = p.val + 1 := hpar_w r_nb hr_mem_w
      have hpar_lnb : st.par l_nb = p.val + 1 := hpar_w l_nb hl_mem_w
      refine ⟨x2, he2, hbr2, he2.bounded hb1, hmod2,
        fun r h0 h2 h3 h4 => by
          simp only [x2, sE, sD, sC, sB, sA, Data.write_regs, Data.set_regs,
            Function.update_of_ne h0, Function.update_of_ne h4, Function.update_of_ne h3,
            Function.update_of_ne h2],
        ?_⟩
      dsimp only
      rw [hst2]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun u hu => Function.update_of_ne hu _ _,
        fun hd1 => absurd hd1 (by omega),
        ?_, ?_, ?_⟩
      · intro h tail _ _ hcirc_ht hcur_ht
        have hlen_ht : 2 ≤ (h :: tail).length := by
          obtain ⟨r', l', _, hr', _, _, _, hne_rc, _, _⟩ :=
            hcirc_w.remove hcur_w hlen_w
          cases tail with
          | nil =>
            have hcur_eq : cur = h := List.mem_singleton.mp hcur_ht
            subst hcur_eq
            have hrh : st.right cur = cur.val := hcirc_ht.2.1
            have hrc_eq : r'.val = cur.val := hr'.symm.trans hrh
            exact absurd (Fin.ext hrc_eq) hne_rc
          | cons _ _ => simp only [List.length_cons]; omega
        obtain ⟨r', l', rest', hr', hl', _, _, _, hcirc_rem', hperm_rem'⟩ :=
          hcirc_ht.remove hcur_ht hlen_ht
        have hrr : r' = r_nb := Fin.ext (hr'.symm.trans hr_cur)
        have hll : l' = l_nb := Fin.ext (hl'.symm.trans hl_cur)
        subst hrr; subst hll
        exact ⟨r', rest', Function.update_self p _ _, hcirc_rem', hperm_rem'⟩
      · refine hcirc_r.frame fun u hu => ?_
        have hpu0 : st.par u = 0 := hroots_par0 u hu
        have hur : u ≠ r_nb := fun e => by rw [e, hpar_rnb] at hpu0; omega
        have hul : u ≠ l_nb := fun e => by rw [e, hpar_lnb] at hpu0; omega
        exact ⟨Function.update_of_ne hur _ _, Function.update_of_ne hul _ _⟩
      · intro u hpu
        have hur : u ≠ r_nb := fun e => hpu (e ▸ hpar_rnb)
        have hul : u ≠ l_nb := fun e => hpu (e ▸ hpar_lnb)
        exact ⟨Function.update_of_ne hur _ _, Function.update_of_ne hul _ _⟩
  obtain ⟨x2, he2, hbr2, hb2, hmod2, hx2_reg, hst2_props⟩ := hstep2
  dsimp only at hst2_props
  rcases hst2_props with ⟨hk2, hp2, hd2_eq, hmk2, hin2, hco2, hmin2, hnr2, hnm2, hsz2,
    hch2_ne, hch2_1, hch2_2, hcirc2_r, hlr2_other⟩
  -- Step 3: `s1 ← minRootReg - oneP; ⟪insertIntoNonEmptyList s1 zReg⟫` (`x2 → x4` in 11 steps)
  let x3 := x2.set s1 m.val
  have he3 : ExecWithin w (.op (.exactBin .sub s1 minRootReg oneP)) x2 x3 1 := by
    have hmin_x2 : x2.regs minRootReg = m.val + 1 := hmin2.trans hmin
    have ho1_x2 : x2.regs oneP = 1 := hbr2.2.2.2.2.2.2.2.2.2.2.2.2
    simpa only [hmin_x2, ho1_x2, Nat.add_sub_cancel] using
      execWithin_exactSub (x := x2) (d := s1) (i := minRootReg) (j := oneP)
        (by rw [hmin_x2, ho1_x2]; omega)
        (by rw [hmin_x2, ho1_x2]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have hb3 : x3.Bounded w := he3.bounded hb2
  have hbr3 : BaseRegs n base x3 := hbr2.set_non_base (by decide) m.val
  have hst3 : RawState.ofData n base x3 = RawState.ofData n base x2 :=
    ofData_set_scratch x2 (by decide : 17 ≤ s1.val) m.val
  have hx3_s1 : x3.regs s1 = m.val := by simp only [x3, Data.set_regs, Function.update_self]
  have hx3_z : x3.regs zReg = cur.val := by
    simp only [x3, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ s1)]
    exact (hx2_reg zReg (by decide) (by decide) (by decide) (by decide)).trans
      ((hx1_reg zReg (by decide) (by decide)).trans hz_reg)
  have hcur_not_roots : cur ∉ m :: rtail := fun hm_in => by
    have hp0 := hroots_par0 cur hm_in
    omega
  obtain ⟨x4, he4, hbr4, hmod4, ⟨r_rt, hr_rt_eq, hr_rt_mem, hst4⟩, hcirc4_r⟩ :=
    insertIntoNonEmptyList_exec hb3 hbr3 (by decide) (by decide) (by decide) (by decide)
      hx3_s1 hx3_z (hst3 ▸ hcirc2_r) hcur_not_roots
  rw [hst3] at hr_rt_eq hst4
  have hb4 : x4.Bounded w := he4.bounded hb3
  have hx4_reg : ∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 →
      x4.regs r = x.regs r := fun r h0 h1 h2 h3 h4 => by
    have h43 : x4.regs r = x3.regs r := he4.regs_eq (insertIntoNonEmptyList_preserves h0 h2)
    have h32 : x3.regs r = x2.regs r := by simp only [x3, Data.set_regs, Function.update_of_ne h1]
    exact h43.trans (h32.trans ((hx2_reg r h0 h2 h3 h4).trans (hx1_reg r h0 h1)))
  -- Step 4: clear `par[cur]` and `mark[cur]`, update `numMarkedReg` and `numRootsReg` (8 steps)
  have ho_pcur := owns_arr_addr (base := base) (k := 1) (by decide) hcur_lt
  have ho_mcur := owns_arr_addr (base := base) (k := 6) (by decide) hcur_lt
  have hx4_pb : x4.regs parBase = base + n := hbr4.2.2.2.1
  have hx4_mb : x4.regs markBase = base + 6 * n := hbr4.2.2.2.2.2.2.2.2.1
  have hx4_z0 : x4.regs zeroP = 0 := hbr4.2.2.2.2.2.2.2.2.2.2.2.1
  have hx4_o1 : x4.regs oneP = 1 := hbr4.2.2.2.2.2.2.2.2.2.2.2.2
  have hx4_zr : x4.regs zReg = cur.val :=
    hx4_reg zReg (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans hz_reg
  let x5 := (x4.set s0 (base + n + cur.val)).write (base + n + cur.val) 0
  have ep1 : ExecWithin w (.op (.exactBin .add s0 parBase zReg)) x4
      (x4.set s0 (base + n + cur.val)) 1 := by
    simpa only [hx4_pb, hx4_zr] using
      execWithin_exactAdd (x := x4) (d := s0) (i := parBase) (j := zReg)
        (by rw [hx4_pb, hx4_zr]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have ep2 : ExecWithin (B := .exact) w (.op (.store s0 zeroP))
      (x4.set s0 (base + n + cur.val)) x5 1 := by
    have hs0 : (x4.set s0 (base + n + cur.val)).regs s0 = base + n + cur.val := by
      simp only [Data.set_regs, Function.update_self]
    have hz : (x4.set s0 (base + n + cur.val)).regs zeroP = 0 := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : zeroP ≠ s0), hx4_z0]
    simpa only [hs0, hz] using
      (ExecWithin.store (B := .exact) (w := w) (x := x4.set s0 (base + n + cur.val))
        (a := s0) (s := zeroP))
  let x6 := (x5.set s0 (base + 6 * n + cur.val)).set s1 (st.mark cur)
  have em1 : ExecWithin w (.op (.exactBin .add s0 markBase zReg)) x5
      (x5.set s0 (base + 6 * n + cur.val)) 1 := by
    have hmb : x5.regs markBase = base + 6 * n := by
      simp only [x5, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : markBase ≠ s0), hx4_mb]
    have hzr : x5.regs zReg = cur.val := by
      simp only [x5, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : zReg ≠ s0), hx4_zr]
    simpa only [hmb, hzr] using
      execWithin_exactAdd (x := x5) (d := s0) (i := markBase) (j := zReg)
        (by rw [hmb, hzr]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have em2 : ExecWithin (B := .exact) w (.op (.load s1 s0))
      (x5.set s0 (base + 6 * n + cur.val)) x6 1 := by
    have hmem_mk : x5.mem (base + 6 * n + cur.val) = st.mark cur := by
      have h54 : (RawState.ofData n base x5).mark cur = (RawState.ofData n base x4).mark cur := by
        simp only [x5, ofData_write_par, ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
      have h42 : (RawState.ofData n base x4).mark cur = st.mark cur := by
        rw [hst4]; exact congrFun hmk2 cur
      exact h54.trans h42
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hmem_mk] using
      (ExecWithin.load (B := .exact) (w := w) (x := x5.set s0 (base + 6 * n + cur.val))
        (d := s1) (a := s0))
  have hbr6 : BaseRegs n base x6 :=
    (((hbr4.set_non_base (by decide) _).write_eq _ _).set_non_base (by decide) _).set_non_base
      (by decide) _
  have hb6 : x6.Bounded w := em2.bounded (em1.bounded (ep2.bounded (ep1.bounded hb4)))
  have hx6_s0 : x6.regs s0 = base + 6 * n + cur.val := by
    simp only [x6, Data.set_regs, Function.update_of_ne (by decide : s0 ≠ s1), Function.update_self]
  have hx6_s1 : x6.regs s1 = st.mark cur := by
    simp only [x6, Data.set_regs, Function.update_self]
  have hx6_z0 : x6.regs zeroP = 0 := hbr6.2.2.2.2.2.2.2.2.2.2.2.1
  have hx6_o1 : x6.regs oneP = 1 := hbr6.2.2.2.2.2.2.2.2.2.2.2.2
  have hx6_nm : x6.regs numMarkedReg = st.numMarked := by
    simp only [x6, x5, Data.write_regs, Data.set_regs,
      Function.update_of_ne (by decide : numMarkedReg ≠ s1),
      Function.update_of_ne (by decide : numMarkedReg ≠ s0)]
    exact hx4_reg numMarkedReg (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx6_nr : x6.regs numRootsReg = st.numRoots := by
    simp only [x6, x5, Data.write_regs, Data.set_regs,
      Function.update_of_ne (by decide : numRootsReg ≠ s1),
      Function.update_of_ne (by decide : numRootsReg ≠ s0)]
    exact hx4_reg numRootsReg (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Helper: circular list uniqueness from identical head and pointers
  have circ_tail_eq : ∀ {first : Fin n} (h0 : Fin n) (t1 t2 : List (Fin n)),
      (first :: t1).Nodup → (first :: t2).Nodup →
      ChainLinks st.left st.right first h0 t1 →
      ChainLinks st.left st.right first h0 t2 → t1 = t2 := by
    intro first h0 t1
    induction t1 generalizing h0 with
    | nil =>
      intro t2 _ hnd_f2 hc1 hc2
      cases t2 with
      | nil => rfl
      | cons b _ =>
        have hr1 : st.right h0 = first.val := hc1.1
        have hr2 : st.right h0 = b.val := hc2.1
        have hbf : b = first := Fin.ext (by omega)
        subst hbf
        exact absurd List.mem_cons_self (List.nodup_cons.mp hnd_f2).1
    | cons a1 rest1 ih =>
      intro t2 hnd_f1 hnd_f2 hc1 hc2
      cases t2 with
      | nil =>
        have hr1 : st.right h0 = a1.val := hc1.1
        have hr2 : st.right h0 = first.val := hc2.1
        have haf : a1 = first := Fin.ext (by omega)
        subst haf
        exact absurd List.mem_cons_self (List.nodup_cons.mp hnd_f1).1
      | cons a2 rest2 =>
        have hr1 : st.right h0 = a1.val := hc1.1
        have hr2 : st.right h0 = a2.val := hc2.1
        have ha : a1 = a2 := Fin.ext (by omega)
        subst ha
        have hnd_f1' : (first :: rest1).Nodup := by
          rw [List.nodup_cons] at hnd_f1 ⊢
          exact ⟨fun hm => hnd_f1.1 (List.mem_cons_of_mem a1 hm), (List.nodup_cons.mp hnd_f1.2).2⟩
        have hnd_f2' : (first :: rest2).Nodup := by
          rw [List.nodup_cons] at hnd_f2 ⊢
          exact ⟨fun hm => hnd_f2.1 (List.mem_cons_of_mem a1 hm), (List.nodup_cons.mp hnd_f2.2).2⟩
        congr 1
        exact ih a1 rest2 hnd_f1' hnd_f2' hc1.2.2 hc2.2.2
  -- Branch on `zeroP < s1` (`st.mark cur ≠ 0` vs `st.mark cur = 0`)
  let nm' := if st.mark cur = 0 then st.numMarked else st.numMarked - 1
  have hstep_mk : ∃ x7, ExecWithin (B := .exact) w
      (.branch (.lt zeroP s1)
        (.seq (.op (.store s0 zeroP)) (.op (.exactBin .sub numMarkedReg numMarkedReg oneP)))
        (.op (.store s0 zeroP))) x6 x7 3 ∧
      BaseRegs n base x7 ∧ x7.Bounded w ∧
      Modifies (Block.mk base (space n)).footprint x6.mem x7.mem ∧
      x7.regs numRootsReg = st.numRoots ∧ x7.regs oneP = 1 ∧
      x7.regs numMarkedReg = nm' ∧
      (∀ r : Fin rFib, r ≠ numMarkedReg → x7.regs r = x6.regs r) ∧
      RawState.ofData n base x7 =
        { RawState.ofData n base x5 with
          mark := Function.update (RawState.ofData n base x5).mark cur 0
          numMarked := nm' } := by
    by_cases hmk0 : st.mark cur = 0
    · have hc_m : ¬(Cond.lt zeroP s1).Holds x6 := by
        simp only [Cond.Holds, hx6_z0, hx6_s1, hmk0, lt_self_iff_false, not_false_eq_true]
      let x7 := x6.write (base + 6 * n + cur.val) 0
      have es_m : ExecWithin (B := .exact) w (.op (.store s0 zeroP)) x6 x7 1 := by
        simpa only [hx6_s0, hx6_z0] using
          (ExecWithin.store (B := .exact) (w := w) (x := x6) (a := s0) (s := zeroP))
      have he_m : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s1)
            (.seq (.op (.store s0 zeroP)) (.op (.exactBin .sub numMarkedReg numMarkedReg oneP)))
            (.op (.store s0 zeroP))) x6 x7 3 :=
        ExecWithin.branch_neg hc_m es_m
      have hnm_eq : nm' = st.numMarked := by simp only [nm', hmk0, ↓reduceIte]
      refine ⟨x7, he_m, hbr6.write_eq _ _, he_m.bounded hb6, Modifies.write_of_owns ho_mcur 0,
        hx6_nr, hx6_o1, by simp only [x7, Data.write_regs, hx6_nm, hnm_eq],
        fun _ _ => rfl, ?_⟩
      simp only [x7, x6, ofData_write_mark, ofData_set_scratch _ (by decide : 17 ≤ s1.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val), hnm_eq]
      have : (RawState.ofData n base x5).numMarked = st.numMarked := hx6_nm
      cases h5 : RawState.ofData n base x5
      simp only [h5] at this ⊢
      subst this; rfl
    · have hc_m : (Cond.lt zeroP s1).Holds x6 := by
        simp only [Cond.Holds, hx6_z0, hx6_s1]; omega
      have hnm_pos : 1 ≤ st.numMarked := by
        have hmem_ms : cur ∈ markedSet st := by
          simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hin_cur, hmk0⟩
        have hpos : 0 < markedCount st := Finset.card_pos.mpr ⟨cur, hmem_ms⟩
        omega
      have hnm_le : st.numMarked ≤ n := hnm ▸ markedCount_le_n st
      have hfit_n1 : Fits w (n + 1) := hfit_stop.of_le (by simp only [space]; omega)
      let x7 := (x6.write (base + 6 * n + cur.val) 0).set numMarkedReg (st.numMarked - 1)
      have es_m : ExecWithin (B := .exact) w (.op (.store s0 zeroP)) x6
          (x6.write (base + 6 * n + cur.val) 0) 1 := by
        simpa only [hx6_s0, hx6_z0] using
          (ExecWithin.store (B := .exact) (w := w) (x := x6) (a := s0) (s := zeroP))
      have esub_m : ExecWithin w (.op (.exactBin .sub numMarkedReg numMarkedReg oneP))
          (x6.write (base + 6 * n + cur.val) 0) x7 1 := by
        have hnm_w :
            (x6.write (base + 6 * n + cur.val) 0).regs numMarkedReg = st.numMarked := hx6_nm
        have ho1_w : (x6.write (base + 6 * n + cur.val) 0).regs oneP = 1 := hx6_o1
        simpa only [hnm_w, ho1_w] using
          execWithin_exactSub (x := x6.write (base + 6 * n + cur.val) 0)
            (d := numMarkedReg) (i := numMarkedReg) (j := oneP)
            (by rw [hnm_w, ho1_w]; omega)
            (by rw [hnm_w, ho1_w]; exact hfit_n1.of_le (by omega))
      have he_m : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s1)
            (.seq (.op (.store s0 zeroP)) (.op (.exactBin .sub numMarkedReg numMarkedReg oneP)))
            (.op (.store s0 zeroP))) x6 x7 3 :=
        ExecWithin.branch_pos hc_m (es_m.seq esub_m)
      have hnm_eq : nm' = st.numMarked - 1 := by simp only [nm', hmk0, ↓reduceIte]
      refine ⟨x7, he_m, (hbr6.write_eq _ _).set_non_base (by decide) _, he_m.bounded hb6,
        Modifies.write_of_owns ho_mcur 0,
        by
          simp only [x7, Data.set_regs,
            Function.update_of_ne (by decide : numRootsReg ≠ numMarkedReg),
            Data.write_regs, hx6_nr],
        by simp only [x7, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ numMarkedReg),
          Data.write_regs, hx6_o1],
        by simp only [x7, Data.set_regs, Function.update_self, hnm_eq],
        fun r hr => by simp only [x7, Data.set_regs, Function.update_of_ne hr, Data.write_regs],
        ?_⟩
      simp only [x7, x6, ofData_set_numMarked, ofData_write_mark,
        ofData_set_scratch _ (by decide : 17 ≤ s1.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val), hnm_eq]
  obtain ⟨x7, he7, hbr7, hb7, hmod7, hx7_nr, hx7_o1, hx7_nm, hx7_reg, hst7⟩ := hstep_mk
  let y := x7.set numRootsReg (st.numRoots + 1)
  have he8 : ExecWithin w (.op (.exactBin .add numRootsReg numRootsReg oneP)) x7 y 1 := by
    simpa only [hx7_nr, hx7_o1] using
      execWithin_exactAdd (x := x7) (d := numRootsReg) (i := numRootsReg) (j := oneP)
        (by rw [hx7_nr, hx7_o1]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have he_all : ExecWithin w cutNodeCode x y 36 := by
    unfold cutNodeCode
    exact (e_deg1.seq <| e_deg2.seq <| e_deg3.seq <| e_deg4.seq <|
      he2.seq <| he3.seq <| he4.seq <| ep1.seq <| ep2.seq <| em1.seq <| em2.seq <|
      he7.seq he8).mono (by omega)
  have hmod_all : Modifies (Block.mk base (space n)).footprint x.mem y.mem := by
    have hm12 := modifies_block_trans hmod1 hmod2
    have hm14 := modifies_block_trans hm12 hmod4
    have hm56 : Modifies (Block.mk base (space n)).footprint x4.mem x6.mem := by
      simpa only [x6, x5, Data.set_mem, Data.write_mem, Nat.one_mul] using
        Modifies.write_of_owns (m := x4.mem) ho_pcur 0
    have hm16 := modifies_block_trans hm14 hm56
    exact modifies_block_trans hm16 hmod7
  have hst5 : RawState.ofData n base x5 =
      { RawState.ofData n base x4 with par := Function.update st.par cur 0 } := by
    have hp4 : (RawState.ofData n base x4).par = st.par := by rw [hst4]; exact hp2
    simp only [x5, ofData_write_par, ofData_set_scratch _ (by decide : 17 ≤ s0.val), hp4]
  have hmk5 : (RawState.ofData n base x5).mark = st.mark := by
    rw [hst5, hst4]; exact hmk2
  have hsty : RawState.ofData n base y =
      { RawState.ofData n base x5 with
        mark := Function.update st.mark cur 0
        numMarked := nm'
        numRoots := st.numRoots + 1 } := by
    simp only [y, ofData_set_numRoots, hst7, hmk5]
  refine ⟨y, he_all, hbr7.set_non_base (by decide) _, hmod_all,
    fun r h0 h1 h2 h3 h4 hnm_ne hnr_ne => by
      simp only [y, Data.set_regs, Function.update_of_ne hnr_ne]
      rw [hx7_reg r hnm_ne]
      simp only [x6, x5, Data.write_regs, Data.set_regs, Function.update_of_ne h1,
        Function.update_of_ne h0]
      exact hx4_reg r h0 h1 h2 h3 h4,
    ?_⟩
  dsimp only
  have hkey_y : (RawState.ofData n base y).key = st.key := by rw [hsty, hst5, hst4]; exact hk2
  have hin_y : (RawState.ofData n base y).inHeap = st.inHeap := by rw [hsty, hst5, hst4]; exact hin2
  have hco_y : (RawState.ofData n base y).cons = st.cons := by rw [hsty, hst5, hst4]; exact hco2
  have hmin_y : (RawState.ofData n base y).minRoot = st.minRoot := by
    rw [hsty, hst5, hst4]; exact hmin2
  have hsz_y : (RawState.ofData n base y).sz = st.sz := by rw [hsty, hst5, hst4]; exact hsz2
  have hnr_y : (RawState.ofData n base y).numRoots = st.numRoots + 1 := by rw [hsty]
  have hmk_y : (RawState.ofData n base y).mark = Function.update st.mark cur 0 := by rw [hsty]
  have hd_y : (RawState.ofData n base y).deg = Function.update st.deg p dp' := by
    rw [hsty, hst5, hst4]; exact hd2_eq
  have hp_y : (RawState.ofData n base y).par = Function.update st.par cur 0 := by rw [hsty, hst5]
  have hch_y : (RawState.ofData n base y).child = (RawState.ofData n base x2).child := by
    rw [hsty, hst5, hst4]
  have hl_y : (RawState.ofData n base y).left = (RawState.ofData n base x4).left := by
    rw [hsty, hst5]
  have hr_y : (RawState.ofData n base y).right = (RawState.ofData n base x4).right := by
    rw [hsty, hst5]
  have hnm_cnt : (RawState.ofData n base y).numMarked = markedCount (RawState.ofData n base y) := by
    have hnm_val : (RawState.ofData n base y).numMarked = nm' := by rw [hsty]
    rw [hnm_val]
    by_cases hmk0 : st.mark cur = 0
    · simp only [nm', hmk0, ↓reduceIte]
      rw [hnm]
      exact (markedCount_congr fun u => by
        rw [hin_y, hmk_y]
        by_cases huc : u = cur
        · subst huc; simp only [Function.update_self, hmk0]
        · simp only [Function.update_of_ne huc]).symm
    · simp only [nm', hmk0, ↓reduceIte]
      have hclr := markedCount_clear_one (st := st) (st' := RawState.ofData n base y)
        hin_cur hmk0 (by rw [hmk_y, Function.update_self])
        (fun u huc => by rw [hin_y, hmk_y, Function.update_of_ne huc])
      omega
  have hpot : (st.mark cur ≠ 0 → potential y + unitCredit = potential x) ∧
      (st.mark cur = 0 → potential y = potential x + unitCredit) := by
    have hy_nr : y.regs numRootsReg = st.numRoots + 1 := by
      simp only [y, Data.set_regs, Function.update_self]
    have hy_nm : y.regs numMarkedReg = nm' := by
      simp only [y, Data.set_regs,
        Function.update_of_ne (by decide : numMarkedReg ≠ numRootsReg), hx7_nm]
    have hx_nr : x.regs numRootsReg = st.numRoots := rfl
    have hx_nm : x.regs numMarkedReg = st.numMarked := rfl
    constructor
    · intro hmk_ne
      have hnm_pos : 1 ≤ st.numMarked := by
        have hmem_ms : cur ∈ markedSet st := by
          simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hin_cur, hmk_ne⟩
        have hpos : 0 < markedCount st := Finset.card_pos.mpr ⟨cur, hmem_ms⟩
        omega
      simp only [potential, unitCredit, hy_nr, hy_nm, hx_nr, hx_nm, nm', hmk_ne, ↓reduceIte]
      omega
    · intro hmk0
      simp only [potential, unitCredit, hy_nr, hy_nm, hx_nr, hx_nm, nm', hmk0, ↓reduceIte]
      omega
  refine ⟨hkey_y, hin_y, hco_y, hmin_y, hsz_y, hnr_y, hnm_cnt, hpot,
    ⟨by rw [hmk_y, Function.update_self], fun u hu => by rw [hmk_y, Function.update_of_ne hu]⟩,
    ⟨by rw [hd_y, Function.update_self]; omega,
      fun u hu => by rw [hd_y, Function.update_of_ne hu]⟩,
    ⟨by rw [hp_y, Function.update_self], fun u hu => by rw [hp_y, Function.update_of_ne hu]⟩,
    fun u hu => by rw [hch_y]; exact hch2_ne u hu,
    fun hd1 => by rw [hch_y]; exact hch2_1 hd1,
    ?_, by rw [hl_y, hr_y]; exact hcirc4_r, ?_⟩
  · intro h tail hge2 hcp_ht hcirc_ht hcur_ht
    obtain ⟨r_c, rest, hcp2, hcirc_rc, hperm_rc⟩ := hch2_2 h tail hge2 hcp_ht hcirc_ht hcur_ht
    obtain ⟨h_w, tail_w, hcp_w, hcirc_w, _, _, hpar_w⟩ := hdp2 hge2
    have hhw : h = h_w := Fin.ext (by omega)
    subst hhw
    have ht_eq : tail = tail_w :=
      circ_tail_eq h tail tail_w hcirc_ht.1 hcirc_w.1 hcirc_ht.2 hcirc_w.2
    subst ht_eq
    refine ⟨r_c, rest, (congrFun hch_y p).trans hcp2, hcirc_rc.frame fun w hw => ?_, hperm_rc⟩
    have hw_er : w ∈ (h :: tail).erase cur := hperm_rc.subset hw
    have hw_ne_cur : w ≠ cur := fun e => by
      subst e
      exact hcirc_ht.1.not_mem_erase hw_er
    have hw_in : w ∈ h :: tail := List.mem_of_mem_erase hw_er
    have hpw : st.par w = p.val + 1 := hpar_w w hw_in
    have hw_ne_m : w ≠ m := fun e => by
      have hm0 := hroots_par0 m List.mem_cons_self
      rw [← e, hpw] at hm0; omega
    have hw_ne_rrt : w ≠ r_rt := fun e => by
      have hr0 := hroots_par0 r_rt hr_rt_mem
      rw [← e, hpw] at hr0; omega
    rw [hl_y, hr_y, hst4]
    exact ⟨by simp only [Function.update_of_ne hw_ne_rrt, Function.update_of_ne hw_ne_cur],
      by simp only [Function.update_of_ne hw_ne_m, Function.update_of_ne hw_ne_cur]⟩
  · intro u hpu1 hpu0
    have hu_ne_cur : u ≠ cur := fun e => hpu1 (e ▸ hpar_cur)
    have hu_ne_m : u ≠ m := fun e => hpu0 (e ▸ hroots_par0 m List.mem_cons_self)
    have hu_ne_rrt : u ≠ r_rt := fun e => hpu0 (e ▸ hroots_par0 r_rt hr_rt_mem)
    rw [hl_y, hr_y, hst4]
    simp only [Function.update_of_ne hu_ne_rrt, Function.update_of_ne hu_ne_m,
      Function.update_of_ne hu_ne_cur]
    exact hlr2_other u hpu1

/-! ## Forest-level cut transition (`cutNode_forest`) -/

/-- Unified forest transition for `cutNodeCode`: given a pre-key-decrease witness `st_pre` agreeing
with `st = RawState.ofData n base x` everywhere except possibly `st.key cur ≤ st_pre.key cur`,
cutting `cur` (`st.par cur = p.val + 1`) establishes `CutInv n K_max s' st' v m (some p)` and
preserves `∀ T ∈ ts', p ∈ T.nodes → T.root ≠ v`. -/
theorem cutNode_forest {n K_max base w : ℕ} {s' : IndexedMinPQ.State n} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {cur p v m : Fin n} {pending : Option (Fin n)} {st_pre : RawState n}
    {ts : List (FHTree n)} {rtail : List (Fin n)}
    (hz_reg : x.regs zReg = cur.val) (hp_reg : x.regs pReg = p.val)
    (hpend : pending = none ∨ pending = some cur)
    (hst_agree : let st := RawState.ofData n base x
      st.par = st_pre.par ∧ st.child = st_pre.child ∧ st.left = st_pre.left ∧
      st.right = st_pre.right ∧ st.deg = st_pre.deg ∧ st.mark = st_pre.mark ∧
      st.inHeap = st_pre.inHeap ∧ st.key cur ≤ st_pre.key cur ∧
      ∀ u, u ≠ cur → st.key u = st_pre.key u)
    (hts : ∀ T ∈ ts, ValidRoot st_pre pending T)
    (hnd : (forestNodes ts).Nodup)
    (hdom : ∀ u : Fin n, u ∈ forestNodes ts ↔ (s' u).isSome)
    (hin : ∀ u : Fin n,
      ((RawState.ofData n base x).inHeap u ≠ 0 ↔ (s' u).isSome) ∧
      (RawState.ofData n base x).inHeap u ≤ 1)
    (hkeys : ∀ u : Fin n, ∀ ku : ℕ, s' u = some ku →
      (RawState.ofData n base x).key u = ku ∧ ku ≤ K_max)
    (hsz : (RawState.ofData n base x).sz = (IndexedMinPQ.dom s').card)
    (hnr : (RawState.ofData n base x).numRoots = ts.length)
    (hnm : (RawState.ofData n base x).numMarked = markedCount (RawState.ofData n base x))
    (hcons : ∀ d ≤ n, (RawState.ofData n base x).cons d = 0)
    (hmin : (RawState.ofData n base x).minRoot = m.val + 1)
    (hcirc_r : IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right
      (m :: rtail))
    (hperm_r : (m :: rtail).Perm (ts.map FHTree.root))
    (hmin_other : ∀ T ∈ ts, T.root ≠ v →
      IndexedMinPQ.PrioLE (m, (RawState.ofData n base x).key m)
        (T.root, (RawState.ofData n base x).key T.root))
    (hv_root : cur = v ∨
      ((RawState.ofData n base x).key cur = st_pre.key cur ∧ ∃ T_v ∈ ts, T_v.root = v))
    (hcur_tree_ne_v : ∀ T ∈ ts, cur ∈ T.nodes → T.root ≠ v)
    (hcur_in_fn : cur ∈ forestNodes ts)
    (hpar_cur : (RawState.ofData n base x).par cur = p.val + 1) :
    ∃ y, ExecWithin w cutNodeCode x y 36 ∧
      y.Bounded w ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 →
        r ≠ numMarkedReg → r ≠ numRootsReg → y.regs r = x.regs r) ∧
      (((RawState.ofData n base x).mark cur ≠ 0 → potential y + unitCredit = potential x) ∧
       ((RawState.ofData n base x).mark cur = 0 → potential y = potential x + unitCredit)) ∧
      ∃ ts' : List (FHTree n),
        (∀ T ∈ ts', ValidRoot (RawState.ofData n base y) (some p) T) ∧
        (forestNodes ts').Nodup ∧
        (∀ u : Fin n, u ∈ forestNodes ts' ↔ (s' u).isSome) ∧
        (RawState.ofData n base y).numRoots = ts'.length ∧
        (∃ rtail' : List (Fin n),
          (RawState.ofData n base y).minRoot = m.val + 1 ∧
          IsCircList (RawState.ofData n base y).left (RawState.ofData n base y).right
            (m :: rtail') ∧
          (m :: rtail').Perm (ts'.map FHTree.root)) ∧
        (∃ T_v ∈ ts', T_v.root = v) ∧
        (∀ T ∈ ts', T.root ≠ v →
          IndexedMinPQ.PrioLE (m, (RawState.ofData n base y).key m)
            (T.root, (RawState.ofData n base y).key T.root)) ∧
        (∀ T ∈ ts', p ∈ T.nodes → T.root ≠ v) ∧
        CutInv n K_max s' (RawState.ofData n base y) v m (some p) := by
  let st := RawState.ofData n base x
  dsimp only at hst_agree
  rcases hst_agree with ⟨hp_ag, hch_ag, hl_ag, hr_ag, hd_ag, hmk_ag, hin_ag, hkle_cur, hk_other⟩
  obtain ⟨T_i, hTi_mem, hcur_Ti⟩ := mem_forestNodes_iff.mp hcur_in_fn
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hTi_mem
  have hi_mem : ts[i] ∈ ts := List.getElem_mem hi
  have hnd_Ti : (ts[i]).nodes.Nodup := forestNodes_nodup_tree hnd hi_mem
  have hTi_root_ne_v : (ts[i]).root ≠ v := hcur_tree_ne_v ts[i] hi_mem hcur_Ti
  have hpar_pre_cur : st_pre.par cur = p.val + 1 := hp_ag ▸ hpar_cur
  have hcur_ne_Ti_root : cur ≠ (ts[i]).root := fun e => by
    have hp0 := (hts ts[i] hi_mem).2.1
    rw [← e] at hp0
    omega
  have hcur_desc : cur ∈ forestNodes (ts[i]).children := by
    rw [(ts[i]).nodes_eq] at hcur_Ti
    exact (List.mem_cons.mp hcur_Ti).resolve_left hcur_ne_Ti_root
  obtain ⟨hp_in_Ti, _, _, hin_pre_cur, _, hdp_pos_pre, hdp2_pre⟩ :=
    exists_parent_info (hts ts[i] hi_mem).1 hcur_desc hpar_pre_cur
  have hdp_pos : 1 ≤ st.deg p := hd_ag ▸ hdp_pos_pre
  have hdp_le : st.deg p ≤ n := by
    let rec sub_deg_le (U : FHTree n) (hU : ValidSubtree st_pre pending U)
        (hnd_U : U.nodes.Nodup) (hp_U : p ∈ U.nodes) : st_pre.deg p ≤ n :=
      match U, hU with
      | .node u cs, .mk _ _ hdeg _ _ _ _ hsub => by
        rcases List.mem_cons.mp hp_U with rfl | hp_cs
        · have hcs_le : cs.length ≤ (forestNodes cs).length := forestNodes_length_ge cs
          have hfn_le : (FHTree.node p cs).nodes.length ≤ n := by simpa using hnd_U.length_le_card
          change (p :: forestNodes cs).length ≤ n at hfn_le
          simp only [List.length_cons] at hfn_le
          omega
        · obtain ⟨c, hc, hp_c⟩ := mem_forestNodes_iff.mp hp_cs
          exact sub_deg_le c (hsub c hc)
            (forestNodes_nodup_tree (List.nodup_cons.mp hnd_U).2 hc) hp_c
    exact hd_ag ▸ sub_deg_le ts[i] (hts ts[i] hi_mem).1 hnd_Ti hp_in_Ti
  have hdp2 : 2 ≤ st.deg p →
      ∃ (h : Fin n) (tail : List (Fin n)),
        st.child p = h.val + 1 ∧ IsCircList st.left st.right (h :: tail) ∧
        cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧ ∀ u ∈ h :: tail, st.par u = p.val + 1 := by
    intro hge2
    obtain ⟨h, tail, hcp, hcirc, hcur_ht, hlen, hpar_ht⟩ := hdp2_pre (hd_ag ▸ hge2)
    exact ⟨h, tail, hch_ag ▸ hcp, hl_ag ▸ hr_ag ▸ hcirc, hcur_ht, hlen,
      fun u hu => hp_ag ▸ hpar_ht u hu⟩
  have hroots_par0 : ∀ u ∈ m :: rtail, st.par u = 0 := fun u hu => by
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp (hperm_r.subset hu)
    exact hp_ag ▸ (hts R hR).2.1
  have hin_cur : st.inHeap cur ≠ 0 := hin_ag ▸ hin_pre_cur
  -- Also check `ts.length + 1 ≤ n` (`cur` becomes a new root while `ts[i]` keeps its root):
  have hnr_le : st.numRoots + 1 ≤ n := by
    rw [hnr]
    -- `cur :: ts.map FHTree.root` is Nodup!
    have hr_nd : (ts.map FHTree.root).Nodup := map_root_nodup hnd
    have hcur_not_map : cur ∉ ts.map FHTree.root := by
      intro hm_in
      obtain ⟨R, hR, hR_eq⟩ := List.mem_map.mp hm_in
      have hp0 := (hts R hR).2.1
      rw [hR_eq] at hp0
      omega
    have hnd_cons : (cur :: ts.map FHTree.root).Nodup := List.nodup_cons.mpr ⟨hcur_not_map, hr_nd⟩
    have hlen_le : (cur :: ts.map FHTree.root).length ≤ n := by simpa using hnd_cons.length_le_card
    simp only [List.length_cons, List.length_map] at hlen_le
    exact hlen_le
  obtain ⟨y, he, hbr_y, hmod_y, hy_reg, hy_props⟩ :=
    cutNodeCode_raw hb hbr hz_reg hp_reg hdp_pos hdp_le hdp2 hmin hcirc_r hroots_par0
      hpar_cur hin_cur hnm hnr_le
  dsimp only at hy_props
  rcases hy_props with ⟨hk_y, hin_y, hco_y, hmin_y, hsz_y, hnr_y, hnm_y, hpot_y,
    hmk_y, hd_y, hp_y, hch_y_ne, hch_y_1, hch_y_2, hcirc_y_r, hlr_y⟩
  let st' := RawState.ofData n base y
  -- Apply `ValidSubtree.exists_cut` between `st_pre` and `st_mid := { st' with key := st_pre.key }`
  let st_mid : RawState n := { st' with key := st_pre.key }
  obtain ⟨T_cut, T', hcut_r, hT'_r, hp_in_T', hperm_Ti, hvalid_cut_mid, hvalid_T'_mid⟩ :=
    (hts ts[i] hi_mem).1.exists_cut (st' := st_mid) hnd_Ti hcur_desc hpar_pre_cur hpend
      (fun u _ => ⟨by dsimp only [st_mid, st']; rw [hin_y, hin_ag], rfl⟩)
      ⟨hmk_y.1, fun u _ hu => (hmk_y.2 u hu).trans (congrFun hmk_ag u)⟩
      ⟨by dsimp only [st_mid, st']; rw [hd_y.1, ← hd_ag],
       fun u _ hu => (hd_y.2 u hu).trans (congrFun hd_ag u)⟩
      ⟨hp_y.1, fun u _ hu => (hp_y.2 u hu).trans (congrFun hp_ag u)⟩
      ⟨fun hd1 => hch_y_1 (hd_ag.symm ▸ hd1),
       fun h tail hge2 hcp hcirc hcur_ht =>
         hch_y_2 h tail (hd_ag.symm ▸ hge2) (hch_ag.symm ▸ hcp)
           (hl_ag.symm ▸ hr_ag.symm ▸ hcirc) hcur_ht⟩
      (fun u _ hu => (hch_y_ne u hu).trans (congrFun hch_ag u))
      (fun u _ hpu1 hpu0 => by
        have hlr := hlr_y u (hp_ag.symm ▸ hpu1) (hp_ag.symm ▸ hpu0)
        exact ⟨hlr.1.trans (congrFun hl_ag u), hlr.2.trans (congrFun hr_ag u)⟩)
  have hnd_cut_T' : (T_cut.nodes ++ T'.nodes).Nodup := hperm_Ti.nodup_iff.mpr hnd_Ti
  have hcur_not_T' : cur ∉ T'.nodes := fun hm_in =>
    (List.nodup_append.mp hnd_cut_T').2.2 cur (hcut_r ▸ T_cut.root_mem_nodes) cur hm_in rfl
  -- Upgrade `T_cut` and `T'` from `st_mid` (`key = st_pre.key`) to `st'` (`key = st.key`)
  have hvalid_cut : ValidRoot st' none T_cut := by
    refine ⟨hvalid_cut_mid.1.lower_key_no_cut (List.nodup_append.mp hnd_cut_T').1
      (hcut_r ▸ T_cut.root_mem_nodes) hkle_cur
      (by dsimp only [st']; rw [hk_y])
      (fun u _ hu => by dsimp only [st']; rw [hk_y]; exact hk_other u hu)
      (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩) (Or.inl hcut_r.symm),
      hvalid_cut_mid.2.1, hvalid_cut_mid.2.2⟩
  have hvalid_T' : ValidRoot st' (some p) T' := by
    have hT'_root_ne_cur : T'.root ≠ cur := by
      rw [hT'_r]; exact hcur_ne_Ti_root.symm
    refine ⟨hvalid_T'_mid.frame (fun u hu => ⟨rfl, rfl, rfl, rfl, ?_⟩)
      (fun _ _ => ⟨rfl, rfl, rfl, Iff.rfl⟩),
      by
        dsimp only [st']
        rw [hp_y.2 T'.root hT'_root_ne_cur, hT'_r, hp_ag]
        exact (hts ts[i] hi_mem).2.1,
      by
        dsimp only [st']
        rw [hmk_y.2 T'.root hT'_root_ne_cur, hT'_r, hmk_ag]
        exact (hts ts[i] hi_mem).2.2⟩
    have hu_ne : u ≠ cur := fun e => hcur_not_T' (e ▸ hu)
    dsimp only [st']; rw [hk_y]; exact hk_other u hu_ne
  let ts' : List (FHTree n) := T_cut :: ts.set i T'
  have hperm_fn : (forestNodes ts').Perm (forestNodes ts) :=
    forestNodes_set_perm ts i hi T_cut T' hperm_Ti
  have hnd_fn' : (forestNodes ts').Nodup := hperm_fn.nodup_iff.mpr hnd
  have hts'_valid : ∀ T ∈ ts', ValidRoot st' (some p) T := by
    intro T hT
    rcases List.mem_cons.mp hT with rfl | hT_set
    · exact ⟨hvalid_cut.1.weaken_pending (some p), hvalid_cut.2.1, hvalid_cut.2.2⟩
    · obtain ⟨j, hj_set, rfl⟩ := List.mem_iff_getElem.mp hT_set
      have hj : j < ts.length := by simpa only [List.length_set] using hj_set
      by_cases hji : j = i
      · subst j; simp only [List.getElem_set_self]; exact hvalid_T'
      · rw [List.getElem_set_ne (Ne.symm hji)]
        have hcur_not_j : cur ∉ (ts[j]).nodes := fun hm_in =>
          forestNodes_nodup_idx_disjoint hnd hi hj (Ne.symm hji) hcur_Ti hm_in
        have hp_not_j : p ∉ (ts[j]).nodes := fun hm_in =>
          forestNodes_nodup_idx_disjoint hnd hi hj (Ne.symm hji) hp_in_Ti hm_in
        have hsub_j_none : ValidSubtree st_pre none ts[j] := by
          rcases hpend with rfl | rfl
          · exact (hts ts[j] (List.getElem_mem hj)).1
          · exact (hts ts[j] (List.getElem_mem hj)).1.clear_pending fun hm_in =>
              hcur_not_j ((ts[j]).nodes_eq ▸ List.mem_cons_of_mem _ hm_in)
        have hr_ne_cur : (ts[j]).root ≠ cur := fun e =>
          hcur_not_j (e ▸ (ts[j]).root_mem_nodes)
        refine ⟨(hsub_j_none.frame (pending' := none) (fun u hu => ?_)
          (fun u hu => ?_)).weaken_pending (some p),
          by rw [hp_y.2 _ hr_ne_cur, hp_ag]; exact (hts ts[j] (List.getElem_mem hj)).2.1,
          by rw [hmk_y.2 _ hr_ne_cur, hmk_ag]; exact (hts ts[j] (List.getElem_mem hj)).2.2⟩
        · have hu_ne_cur : u ≠ cur := fun e => hcur_not_j (e ▸ hu)
          have hu_ne_p : u ≠ p := fun e => hp_not_j (e ▸ hu)
          exact ⟨by rw [hin_y, hin_ag], by rw [hmk_y.2 u hu_ne_cur, hmk_ag],
            by rw [hd_y.2 u hu_ne_p, hd_ag], by rw [hch_y_ne u hu_ne_p, hch_ag],
            by rw [hk_y]; exact hk_other u hu_ne_cur⟩
        · have hu_in_j : u ∈ (ts[j]).nodes :=
            (ts[j]).nodes_eq ▸ List.mem_cons_of_mem (ts[j]).root hu
          have hu_ne_cur : u ≠ cur := fun e => hcur_not_j (e ▸ hu_in_j)
          obtain ⟨q, hq_j, hpq⟩ := hsub_j_none.par_of_mem_children u hu
          have hq_ne_p : q ≠ p := fun e => hp_not_j (e ▸ hq_j)
          have hpu1 : st.par u ≠ p.val + 1 := by
            rw [hp_ag, hpq]; have := Fin.val_ne_of_ne hq_ne_p; omega
          have hpu0 : st.par u ≠ 0 := by rw [hp_ag, hpq]; omega
          have hlr := hlr_y u hpu1 hpu0
          exact ⟨by rw [hp_y.2 u hu_ne_cur, hp_ag], hlr.1.trans (congrFun hl_ag u),
            hlr.2.trans (congrFun hr_ag u), Iff.rfl⟩
  have hperm_roots' : (m :: cur :: rtail).Perm (ts'.map FHTree.root) := by
    simp only [ts', List.map_cons, hcut_r, map_root_set_eq ts i hi T' hT'_r]
    exact (List.Perm.swap cur m rtail).trans (List.Perm.cons cur hperm_r)
  have hTv' : ∃ T_v ∈ ts', T_v.root = v := by
    rcases hv_root with rfl | ⟨_, T_v, hTv_mem, hTv_r⟩
    · exact ⟨T_cut, List.mem_cons_self, hcut_r⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hTv_mem
      by_cases hji : j = i
      · subst hji; exact absurd hTv_r hTi_root_ne_v
      · refine ⟨ts[j], List.mem_cons_of_mem T_cut ?_, hTv_r⟩
        exact List.mem_iff_getElem.mpr
          ⟨j, by simp only [List.length_set]; exact hj,
            by simp only [List.getElem_set_ne (Ne.symm hji)]⟩
  have hmin_other' : ∀ T ∈ ts', T.root ≠ v →
      IndexedMinPQ.PrioLE (m, st'.key m) (T.root, st'.key T.root) := by
    intro T hT hTr_ne
    rw [hk_y]
    rcases List.mem_cons.mp hT with rfl | hT_set
    · rw [hcut_r] at hTr_ne ⊢
      rcases hv_root with rfl | ⟨hk_cur_eq, _⟩
      · exact absurd rfl hTr_ne
      · have hle_Ti : IndexedMinPQ.PrioLE (m, st.key m) ((ts[i]).root, st.key (ts[i]).root) :=
          hmin_other ts[i] hi_mem hTi_root_ne_v
        have hle_pre : IndexedMinPQ.PrioLE ((ts[i]).root, st_pre.key (ts[i]).root)
            (cur, st_pre.key cur) :=
          (hts ts[i] hi_mem).1.prioLE_of_mem hcur_Ti
        rw [← hk_other (ts[i]).root hcur_ne_Ti_root.symm, ← hk_cur_eq] at hle_pre
        exact hle_Ti.trans hle_pre
    · obtain ⟨j, hj_set, rfl⟩ := List.mem_iff_getElem.mp hT_set
      have hj : j < ts.length := by simpa only [List.length_set] using hj_set
      by_cases hji : j = i
      · subst j; simp only [List.getElem_set_self, hT'_r]
        exact hmin_other ts[i] hi_mem hTi_root_ne_v
      · rw [List.getElem_set_ne (Ne.symm hji)] at hTr_ne ⊢
        exact hmin_other ts[j] (List.getElem_mem hj) hTr_ne
  have hp_tree_ne_v : ∀ T ∈ ts', p ∈ T.nodes → T.root ≠ v := by
    have hT'_mem : T' ∈ ts' :=
      List.mem_cons_of_mem T_cut
        (List.mem_iff_getElem.mpr ⟨i, by simp only [List.length_set]; exact hi,
          by simp only [List.getElem_set_self]⟩)
    intro T hT hp_T
    by_cases hTT' : T = T'
    · subst hTT'; rw [hT'_r]; exact hTi_root_ne_v
    · exact False.elim (forestNodes_nodup_disjoint hnd_fn' hT hT'_mem hTT' hp_T hp_in_T')
  have hdom' : ∀ u : Fin n, u ∈ forestNodes ts' ↔ (s' u).isSome := fun u =>
    hperm_fn.mem_iff.trans (hdom u)
  have hlen_ts' : ts'.length = ts.length + 1 := by
    simp only [ts', List.length_cons, List.length_set]
  exact ⟨y, he, he.bounded hb, hbr_y, hmod_y, hy_reg, hpot_y, ts', hts'_valid, hnd_fn', hdom',
    hnr_y.trans (hnr ▸ hlen_ts'.symm),
    ⟨cur :: rtail, hmin_y.trans hmin, hcirc_y_r, hperm_roots'⟩, hTv', hmin_other', hp_tree_ne_v,
    ⟨ts', hts'_valid, hnd_fn', hdom',
      fun u => by rw [hin_y]; exact hin u,
      fun u ku hsu => by rw [hk_y]; exact hkeys u ku hsu,
      hsz_y.trans hsz, hnr_y.trans (hnr ▸ hlen_ts'.symm), hnm_y,
      fun d hdn => by rw [hco_y]; exact hcons d hdn,
      ⟨cur :: rtail, hmin_y.trans hmin, hcirc_y_r, hperm_roots'⟩,
      hTv', hmin_other'⟩⟩

/-! ## Final `minRootReg` update tail and `decreaseKeyCode_exec` -/

private def decreaseKeyTail : Code .exact rFib :=
  .seq (.op (.exactBin .sub s1 minRootReg oneP)) <|
  .seq (.op (.exactBin .add s0 baseReg s1)) <|
  .seq (.op (.load s2 s0)) <|
  .seq (prioLTFlag argV argK s1 s2 s3) <|
       (.branch (.lt zeroP s3)
         (.op (.exactBin .add minRootReg argV oneP))
         (.op (.copy s0 zeroP)))

private theorem decreaseKeyTail_exec {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {v m : Fin n} {k : ℕ}
    (hv_reg : x.regs argV = v.val) (hk_reg : x.regs argK = k)
    (hmin : (RawState.ofData n base x).minRoot = m.val + 1)
    (hkv : (RawState.ofData n base x).key v = k) :
    ∃ y, ExecWithin w decreaseKeyTail x y 12 ∧
      y.Bounded w ∧ BaseRegs n base y ∧ y.mem = x.mem ∧
      potential y = potential x ∧
      (let st := RawState.ofData n base x
       RawState.ofData n base y =
         { st with
           minRoot :=
             if IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m)
               then v.val + 1 else m.val + 1 }) := by
  have hfit_stop := hbr.fits_stop hb
  set st := RawState.ofData n base x with hst_def
  have hv_lt := v.isLt
  have hm_lt := m.isLt
  have hb_b : x.regs baseReg = base := hbr.2.2.1
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  let x1 := x.set s1 m.val
  have e1 : ExecWithin w (.op (.exactBin .sub s1 minRootReg oneP)) x x1 1 := by
    have hmin_x : x.regs minRootReg = m.val + 1 := hmin
    simpa only [hmin_x, ho1, Nat.add_sub_cancel] using
      execWithin_exactSub (x := x) (d := s1) (i := minRootReg) (j := oneP)
        (by rw [hmin_x, ho1]; omega)
        (by rw [hmin_x, ho1]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  let x2 := (x1.set s0 (base + m.val)).set s2 (st.key m)
  have e2 : ExecWithin w (.op (.exactBin .add s0 baseReg s1)) x1 (x1.set s0 (base + m.val)) 1 := by
    have hbb : x1.regs baseReg = base := by
      simp only [x1, Data.set_regs, Function.update_of_ne (by decide : baseReg ≠ s1), hb_b]
    have hs1 : x1.regs s1 = m.val := by simp only [x1, Data.set_regs, Function.update_self]
    simpa only [hbb, hs1] using
      execWithin_exactAdd (x := x1) (d := s0) (i := baseReg) (j := s1)
        (by rw [hbb, hs1]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have e3 : ExecWithin (B := .exact) w (.op (.load s2 s0)) (x1.set s0 (base + m.val)) x2 1 := by
    have hmem_m : x1.mem (base + m.val) = st.key m := rfl
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hmem_m] using
      (ExecWithin.load (B := .exact) (w := w) (x := x1.set s0 (base + m.val)) (d := s2) (a := s0))
  have hbr2 : BaseRegs n base x2 :=
    ((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _
  have hx2_v : x2.regs argV = v.val := by
    simp only [x2, x1, Data.set_regs, Function.update_of_ne (by decide : argV ≠ s2),
      Function.update_of_ne (by decide : argV ≠ s0),
      Function.update_of_ne (by decide : argV ≠ s1), hv_reg]
  have hx2_k : x2.regs argK = st.key v := by
    simp only [x2, x1, Data.set_regs, Function.update_of_ne (by decide : argK ≠ s2),
      Function.update_of_ne (by decide : argK ≠ s0),
      Function.update_of_ne (by decide : argK ≠ s1), hk_reg]
    exact hkv.symm
  have hx2_s1 : x2.regs s1 = m.val := by
    simp only [x2, x1, Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s2),
      Function.update_of_ne (by decide : s1 ≠ s0), Function.update_self]
  have hx2_s2 : x2.regs s2 = st.key m := by
    simp only [x2, Data.set_regs, Function.update_self]
  have he_plt := prioLTFlag_exec (w := w) hbr2 argV argK s1 s2 s3
  dsimp only at he_plt
  rw [hx2_k, hx2_s2, hx2_v, hx2_s1] at he_plt
  let bval := if IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m) then 1 else 0
  have e4 : ExecWithin w (prioLTFlag argV argK s1 s2 s3) x2 (x2.set s3 bval) 6 := he_plt
  let x3 := x2.set s3 bval
  have hbr3 : BaseRegs n base x3 := hbr2.set_non_base (by decide) bval
  have hst3 : RawState.ofData n base x3 = st := by
    simp only [x3, x2, x1, ofData_set_scratch _ (by decide : 17 ≤ s3.val),
      ofData_set_scratch _ (by decide : 17 ≤ s2.val),
      ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ s1.val), ← hst_def]
  have hx3_z0 : x3.regs zeroP = 0 := hbr3.2.2.2.2.2.2.2.2.2.2.2.1
  have hx3_o1 : x3.regs oneP = 1 := hbr3.2.2.2.2.2.2.2.2.2.2.2.2
  have hx3_v : x3.regs argV = v.val := by
    simp only [x3, Data.set_regs, Function.update_of_ne (by decide : argV ≠ s3), hx2_v]
  by_cases hlt : IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m)
  · have hc : (Cond.lt zeroP s3).Holds x3 := by
      rw [Cond.Holds, hx3_z0]
      simp only [x3, Data.set_regs, Function.update_self, bval, hlt, ↓reduceIte]
      exact Nat.zero_lt_one
    let y := x3.set minRootReg (v.val + 1)
    have e5 : ExecWithin (B := .exact) w
        (.branch (.lt zeroP s3) (.op (.exactBin .add minRootReg argV oneP))
          (.op (.copy s0 zeroP))) x3 y 2 :=
      ExecWithin.branch_pos hc (by
        simpa only [hx3_v, hx3_o1] using
          execWithin_exactAdd (x := x3) (d := minRootReg) (i := argV) (j := oneP)
            (by rw [hx3_v, hx3_o1]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega)))
    have he : ExecWithin w decreaseKeyTail x y 12 := by
      unfold decreaseKeyTail
      exact (e1.seq <| e2.seq <| e3.seq <| e4.seq e5).mono (by omega)
    have hpot : potential y = potential x := by
      simp only [potential, y, x3, x2, x1, Data.set_regs,
        Function.update_of_ne (by decide : numRootsReg ≠ minRootReg),
        Function.update_of_ne (by decide : numRootsReg ≠ s3),
        Function.update_of_ne (by decide : numRootsReg ≠ s2),
        Function.update_of_ne (by decide : numRootsReg ≠ s0),
        Function.update_of_ne (by decide : numRootsReg ≠ s1),
        Function.update_of_ne (by decide : numMarkedReg ≠ minRootReg),
        Function.update_of_ne (by decide : numMarkedReg ≠ s3),
        Function.update_of_ne (by decide : numMarkedReg ≠ s2),
        Function.update_of_ne (by decide : numMarkedReg ≠ s0),
        Function.update_of_ne (by decide : numMarkedReg ≠ s1)]
    refine ⟨y, he, he.bounded hb, hbr3.set_non_base (by decide) _, rfl, hpot, ?_⟩
    dsimp only
    simp only [y, ofData_set_minRoot, hst3, hlt, ↓reduceIte]
  · have hc : ¬(Cond.lt zeroP s3).Holds x3 := by
      rw [Cond.Holds, hx3_z0]
      simp only [x3, Data.set_regs, Function.update_self, bval, hlt,
        ↓reduceIte, lt_self_iff_false, not_false_eq_true]
    let y := x3.set s0 0
    have e5 : ExecWithin (B := .exact) w
        (.branch (.lt zeroP s3) (.op (.exactBin .add minRootReg argV oneP))
          (.op (.copy s0 zeroP))) x3 y 3 :=
      ExecWithin.branch_neg hc (by
        simpa only [hx3_z0] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x3) (d := s0) (s := zeroP)))
    have he : ExecWithin w decreaseKeyTail x y 12 := by
      unfold decreaseKeyTail
      exact (e1.seq <| e2.seq <| e3.seq <| e4.seq e5).mono (by omega)
    have hpot : potential y = potential x :=
      potential_supported fun i hi => by
        have h1 : i ≠ s0 := fun e => by subst e; cases hi
        have h2 : i ≠ s3 := fun e => by subst e; cases hi
        have h3 : i ≠ s2 := fun e => by subst e; cases hi
        have h5 : i ≠ s1 := fun e => by subst e; cases hi
        simp only [y, x3, x2, x1, Data.set_regs, Function.update_of_ne h1,
          Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h5]
    refine ⟨y, he, he.bounded hb, hbr3.set_non_base (by decide) _, rfl, hpot, ?_⟩
    dsimp only
    rw [ofData_set_scratch x3 (by decide : 17 ≤ s0.val) 0, hst3]
    simp only [hlt, ↓reduceIte, ← hmin]

/-- `decreaseKeyCode` lowers `key[v]` to `k ≤ k₀` (`s v = some k₀`), performs cascading cuts when
parent heap order is violated, updates `minRootReg`, and restores `FibInv` in amortized time
`t + potential y ≤ 330 + potential x`. -/
theorem decreaseKeyCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (v : Fin n) (k : ℕ) (hinv : FibInv n K_max w base s x)
    (hval : (∃ k₀, s v = some k₀ ∧ k ≤ k₀) ∧ k ≤ K_max)
    (hv_reg : x.regs argV = v.val) (hk_reg : x.regs argK = k) :
    ∃ y t, ExecWithin w decreaseKeyCode x y t ∧
      FibInv n K_max w base (Function.update s v (some k)) y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤ 330 + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  obtain ⟨⟨k₀, hsv₀, hkle₀⟩, hk_max⟩ := hval
  have hfit_stop := hbr.fits_stop hb
  set st₀ := RawState.ofData n base x with hst₀_def
  obtain ⟨ts₀, hts₀, hnd₀, hdom₀, hin₀, hkeys₀, hsz₀, hnr₀, hnm₀, hcons₀, hrl₀⟩ := hraw
  have hk_st₀ : st₀.key v = k₀ := (hkeys₀ v k₀ hsv₀).1
  have hkle_st₀ : k ≤ st₀.key v := hk_st₀ ▸ hkle₀
  have hv_in_fn₀ : v ∈ forestNodes ts₀ := (hdom₀ v).mpr (by simp only [hsv₀, Option.isSome_some])
  rcases hrl₀ with ⟨rfl, _⟩ | ⟨m, rtail₀, hmin₀, hcirc₀, hperm₀, hmin_le₀⟩
  · exact absurd hv_in_fn₀ List.not_mem_nil
  let s' := Function.update s v (some k)
  have hs'_isSome : ∀ u : Fin n, (s' u).isSome = (s u).isSome := fun u => by
    rcases eq_or_ne u v with rfl | huv
    · simp only [s', Function.update_self, hsv₀, Option.isSome_some]
    · simp only [s', Function.update_of_ne huv]
  have hdom_s' : IndexedMinPQ.dom s' = IndexedMinPQ.dom s := by
    rw [IndexedMinPQ.dom_insert]
    exact Finset.insert_eq_of_mem (IndexedMinPQ.mem_dom_iff.mpr ⟨k₀, hsv₀⟩)
  -- Step 1: write `key[v] ← k` and load `s1 ← par[v]` (`x → x2` in 4 steps)
  have hv_lt := v.isLt
  have ho_kv := owns_arr_addr (base := base) (k := 0) (by decide) hv_lt
  have hb_b : x.regs baseReg = base := hbr.2.2.1
  have hp_b : x.regs parBase = base + n := hbr.2.2.2.1
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  let x1 := (x.set s0 (base + v.val)).write (base + v.val) k
  have ek1 : ExecWithin w (.op (.exactBin .add s0 baseReg argV)) x (x.set s0 (base + v.val)) 1 := by
    simpa only [hb_b, hv_reg] using
      execWithin_exactAdd (x := x) (d := s0) (i := baseReg) (j := argV)
        (by rw [hb_b, hv_reg]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have ek2 : ExecWithin (B := .exact) w (.op (.store s0 argK)) (x.set s0 (base + v.val)) x1 1 := by
    have hs0 : (x.set s0 (base + v.val)).regs s0 = base + v.val := by
      simp only [Data.set_regs, Function.update_self]
    have hkr : (x.set s0 (base + v.val)).regs argK = k := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : argK ≠ s0), hk_reg]
    simpa only [hs0, hkr] using
      (ExecWithin.store (B := .exact) (w := w) (x := x.set s0 (base + v.val)) (a := s0) (s := argK))
  let x2 := (x1.set s0 (base + n + v.val)).set s1 (st₀.par v)
  have ek3 : ExecWithin w (.op (.exactBin .add s0 parBase argV)) x1
      (x1.set s0 (base + n + v.val)) 1 := by
    have hpb : x1.regs parBase = base + n := by
      simp only [x1, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : parBase ≠ s0), hp_b]
    have hvr : x1.regs argV = v.val := by
      simp only [x1, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : argV ≠ s0), hv_reg]
    simpa only [hpb, hvr] using
      execWithin_exactAdd (x := x1) (d := s0) (i := parBase) (j := argV)
        (by rw [hpb, hvr]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have ek4 : ExecWithin (B := .exact) w (.op (.load s1 s0))
      (x1.set s0 (base + n + v.val)) x2 1 := by
    have hmem_pv : x1.mem (base + n + v.val) = st₀.par v := by
      have : (RawState.ofData n base x1).par v = st₀.par v := by
        simp only [x1, ofData_write_key, ofData_set_scratch _ (by decide : 17 ≤ s0.val), ← hst₀_def]
      exact this
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hmem_pv] using
      (ExecWithin.load (B := .exact) (w := w) (x := x1.set s0 (base + n + v.val))
        (d := s1) (a := s0))
  have hb2 : x2.Bounded w := ek4.bounded (ek3.bounded (ek2.bounded (ek1.bounded hb)))
  have hbr2 : BaseRegs n base x2 :=
    (((hbr.set_non_base (by decide) _).write_eq _ _).set_non_base (by decide) _).set_non_base
      (by decide) _
  have hmod2 : Modifies (Block.mk base (space n)).footprint x.mem x2.mem := by
    simpa only [x2, x1, Data.set_mem, Data.write_mem, Nat.zero_mul, Nat.add_zero] using
      Modifies.write_of_owns (m := x.mem) ho_kv k
  have hst2 : RawState.ofData n base x2 = { st₀ with key := Function.update st₀.key v k } := by
    simp only [x2, x1, ofData_set_scratch _ (by decide : 17 ≤ s1.val),
      ofData_set_scratch _ (by decide : 17 ≤ s0.val), ofData_write_key, ← hst₀_def]
  have hpot2 : potential x2 = potential x :=
    potential_supported fun i hi => by
      have h1 : i ≠ s1 := fun e => by subst e; cases hi
      have h0 : i ≠ s0 := fun e => by subst e; cases hi
      simp only [x2, x1, Data.write_regs, Data.set_regs, Function.update_of_ne h1,
        Function.update_of_ne h0]
  have hx2_reg : ∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → x2.regs r = x.regs r := fun r h0 h1 => by
    simp only [x2, x1, Data.write_regs, Data.set_regs, Function.update_of_ne h1,
      Function.update_of_ne h0]
  have hs'_keys : ∀ u : Fin n, ∀ ku : ℕ, s' u = some ku →
      (Function.update st₀.key v k) u = ku ∧ ku ≤ K_max := by
    intro u ku hsu
    rcases eq_or_ne u v with rfl | huv
    · simp only [s', Function.update_self, Option.some.injEq] at hsu
      subst ku
      exact ⟨Function.update_self u k st₀.key, hk_max⟩
    · simp only [s', Function.update_of_ne huv] at hsu
      rw [Function.update_of_ne huv]
      exact hkeys₀ u ku hsu
  have hmin_other2 : ∀ T ∈ ts₀, T.root ≠ v →
      IndexedMinPQ.PrioLE (m, (Function.update st₀.key v k) m)
        (T.root, (Function.update st₀.key v k) T.root) := by
    intro T hT hTr
    rw [Function.update_of_ne hTr]
    have hle_m : IndexedMinPQ.PrioLE (m, (Function.update st₀.key v k) m) (m, st₀.key m) := by
      rcases eq_or_ne m v with rfl | hmv
      · rw [Function.update_self]; dsimp only [IndexedMinPQ.PrioLE]; omega
      · rw [Function.update_of_ne hmv]; exact IndexedMinPQ.PrioLE.refl _
    exact hle_m.trans (hmin_le₀ T hT)
  obtain ⟨T_rv, hTrv_mem, hv_in_Trv⟩ := mem_forestNodes_iff.mp hv_in_fn₀
  have hnd_Trv : T_rv.nodes.Nodup := forestNodes_nodup_tree hnd₀ hTrv_mem
  have hx2_z0 : x2.regs zeroP = 0 := hbr2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx2_s1 : x2.regs s1 = st₀.par v := by simp only [x2, Data.set_regs, Function.update_self]
  -- Case split on `st₀.par v = 0` (`v` is already a root) vs `st₀.par v ≠ 0`
  by_cases hpv0 : st₀.par v = 0
  · -- Case A: `v` is already a root (`T_rv.root = v`)
    have hv_eq_root : v = T_rv.root := ((hts₀ T_rv hTrv_mem).par_eq_zero_iff_root hv_in_Trv).mp hpv0
    have hc_outer : ¬(Cond.lt zeroP s1).Holds x2 := by
      simp only [Cond.Holds, hx2_z0, hx2_s1, hpv0, lt_self_iff_false, not_false_eq_true]
    let x3 := x2.set s0 0
    have he_outer_neg : ExecWithin (B := .exact) w (.op (.copy s0 zeroP)) x2 x3 1 := by
      simpa only [hx2_z0] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x2) (d := s0) (s := zeroP))
    have hbr3 : BaseRegs n base x3 := hbr2.set_non_base (by decide) 0
    have hb3 : x3.Bounded w := he_outer_neg.bounded hb2
    have hst3 : RawState.ofData n base x3 = { st₀ with key := Function.update st₀.key v k } :=
      (ofData_set_scratch x2 (by decide : 17 ≤ s0.val) 0).trans hst2
    have hpot3 : potential x3 = potential x :=
      (potential_supported fun i hi => by
        have h0 : i ≠ s0 := fun e => by subst e; cases hi
        simp only [x3, Data.set_regs, Function.update_of_ne h0]).trans hpot2
    have hx3_v : x3.regs argV = v.val := by
      simp only [x3, Data.set_regs, Function.update_of_ne (by decide : argV ≠ s0)]
      exact (hx2_reg argV (by decide) (by decide)).trans hv_reg
    have hx3_k : x3.regs argK = k := by
      simp only [x3, Data.set_regs, Function.update_of_ne (by decide : argK ≠ s0)]
      exact (hx2_reg argK (by decide) (by decide)).trans hk_reg
    obtain ⟨y, he_tail, hby, hbry, hmemy, hpoty, hsty⟩ :=
      decreaseKeyTail_exec hb3 hbr3 hx3_v hx3_k (by rw [hst3]; exact hmin₀)
        (by rw [hst3]; exact Function.update_self v k st₀.key)
    dsimp only at hsty
    have hcut_inv3 : CutInv n K_max s' (RawState.ofData n base x3) v m none := by
      rw [hst3]
      refine ⟨ts₀, fun T hT => ?_, hnd₀, fun u => (hdom₀ u).trans (hs'_isSome u ▸ Iff.rfl),
        fun u => by rw [hs'_isSome]; exact hin₀ u,
        hs'_keys, by rw [hdom_s']; exact hsz₀, hnr₀,
        hnm₀.trans (markedCount_congr fun _ => Iff.rfl).symm,
        hcons₀, ⟨rtail₀, hmin₀, hcirc₀, hperm₀⟩, ⟨T_rv, hTrv_mem, hv_eq_root.symm⟩, hmin_other2⟩
      by_cases hTT : T = T_rv
      · subst hTT
        exact ⟨(hts₀ T hT).1.lower_key_no_cut hnd_Trv hv_in_Trv hkle_st₀
          (Function.update_self v k st₀.key) (fun u _ hu => Function.update_of_ne hu k st₀.key)
          (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩) (Or.inl hv_eq_root),
          (hts₀ T hT).2.1, (hts₀ T hT).2.2⟩
      · have hv_not : v ∉ T.nodes := fun hm_in =>
          forestNodes_nodup_disjoint hnd₀ hTrv_mem hT (Ne.symm hTT) hv_in_Trv hm_in
        exact ⟨(hts₀ T hT).1.frame
          (fun u hu => ⟨rfl, rfl, rfl, rfl,
            Function.update_of_ne (fun (e : u = v) => hv_not (e ▸ hu)) k st₀.key⟩)
          (fun _ _ => ⟨rfl, rfl, rfl, Iff.rfl⟩),
          (hts₀ T hT).2.1, (hts₀ T hT).2.2⟩
    have hraw_y : FibRawInv n K_max s' (RawState.ofData n base y) := by
      refine hcut_inv3.to_fibRawInv ?_ ?_
      · rw [hsty]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · by_cases hlt : IndexedMinPQ.PrioLT (v, (RawState.ofData n base x3).key v)
            (m, (RawState.ofData n base x3).key m)
        · exact Or.inl ⟨hlt, by rw [hsty]; simp only [hlt, ↓reduceIte]⟩
        · exact Or.inr ⟨hlt, by rw [hsty]; simp only [hlt, ↓reduceIte]⟩
    have he_all : ExecWithin w decreaseKeyCode x y 330 := by
      unfold decreaseKeyCode
      exact (ek1.seq <| ek2.seq <| ek3.seq <| ek4.seq <|
        (ExecWithin.branch_neg hc_outer he_outer_neg).seq he_tail).mono (by omega)
    exact ⟨y, 330, he_all, ⟨hby, hbry, hraw_y⟩, hmemy ▸ hmod2,
      by rw [hpoty, hpot3]⟩
  · -- Case B: `st₀.par v ≠ 0`, so `v` has a parent `p₀ : Fin n` with `st₀.par v = p₀.val + 1`
    have hv_ne_root : v ≠ T_rv.root := fun e => hpv0 (((hts₀ T_rv hTrv_mem).par_eq_zero_iff_root
      hv_in_Trv).mpr e)
    have hv_desc : v ∈ forestNodes T_rv.children := by
      rw [T_rv.nodes_eq] at hv_in_Trv
      exact (List.mem_cons.mp hv_in_Trv).resolve_left hv_ne_root
    obtain ⟨p₀, hp₀_in_Trv, hpv_eq⟩ := (hts₀ T_rv hTrv_mem).1.par_of_mem_children v hv_desc
    have hp₀_lt := p₀.isLt
    have hc_outer : (Cond.lt zeroP s1).Holds x2 := by
      simp only [Cond.Holds, hx2_z0, hx2_s1, hpv_eq]; omega
    -- Compute `pReg ← s1 - oneP; s0 ← baseReg + pReg; s2 ← *s0; ⟪prioLTFlag argV argK pReg s2 s3⟫`
    have hx2_o1 : x2.regs oneP = 1 := hbr2.2.2.2.2.2.2.2.2.2.2.2.2
    have hx2_bb : x2.regs baseReg = base := hbr2.2.2.1
    have hp₀_ne_v : p₀ ≠ v := by
      -- If `p₀ = v`, `v` would have `v` as its own parent inside `T_rv` (`Nodup` impossible!):
      intro heq
      subst p₀
      let rec hnot_v (U : FHTree n) (hU : ValidSubtree st₀ none U) (hnd_U : U.nodes.Nodup)
          (hv_cs : v ∈ forestNodes U.children) : False :=
        match U, hU with
        | .node u cs, .mk _ _ _ _ hpar _ _ hsub => by
          have hu_not : u ∉ forestNodes cs := (List.nodup_cons.mp hnd_U).1
          obtain ⟨c, hc, hv_c⟩ := mem_forestNodes_iff.mp hv_cs
          rw [c.nodes_eq] at hv_c
          rcases List.mem_cons.mp hv_c with hvc_eq | hv_desc_c
          · have hpc := hpar c hc
            rw [← hvc_eq] at hpc
            have huv : u = v := Fin.ext (by omega)
            exact hu_not (huv ▸ hv_cs)
          · exact hnot_v c (hsub c hc)
              (forestNodes_nodup_tree (List.nodup_cons.mp hnd_U).2 hc) hv_desc_c
      exact hnot_v T_rv (hts₀ T_rv hTrv_mem).1 hnd_Trv hv_desc
    let x3 := x2.set pReg p₀.val
    have ep_sub : ExecWithin w (.op (.exactBin .sub pReg s1 oneP)) x2 x3 1 := by
      have hs1_p : x2.regs s1 = p₀.val + 1 := hx2_s1.trans hpv_eq
      simpa only [hs1_p, hx2_o1, Nat.add_sub_cancel] using
        execWithin_exactSub (x := x2) (d := pReg) (i := s1) (j := oneP)
          (by rw [hs1_p, hx2_o1]; omega)
          (by rw [hs1_p, hx2_o1]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
    let x4 := (x3.set s0 (base + p₀.val)).set s2 (st₀.key p₀)
    have ep_add : ExecWithin w (.op (.exactBin .add s0 baseReg pReg)) x3
        (x3.set s0 (base + p₀.val)) 1 := by
      have hbb : x3.regs baseReg = base := by
        simp only [x3, Data.set_regs, Function.update_of_ne (by decide : baseReg ≠ pReg), hx2_bb]
      have hpr : x3.regs pReg = p₀.val := by simp only [x3, Data.set_regs, Function.update_self]
      simpa only [hbb, hpr] using
        execWithin_exactAdd (x := x3) (d := s0) (i := baseReg) (j := pReg)
          (by rw [hbb, hpr]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
    have ep_ld : ExecWithin (B := .exact) w (.op (.load s2 s0))
        (x3.set s0 (base + p₀.val)) x4 1 := by
      have hmem_p : x3.mem (base + p₀.val) = st₀.key p₀ := by
        have : (RawState.ofData n base x2).key p₀ = st₀.key p₀ := by
          rw [hst2]; exact Function.update_of_ne hp₀_ne_v k st₀.key
        exact this
      simpa only [Data.set_mem, Data.set_regs, Function.update_self, hmem_p] using
        (ExecWithin.load (B := .exact) (w := w) (x := x3.set s0 (base + p₀.val))
          (d := s2) (a := s0))
    have hbr4 : BaseRegs n base x4 :=
      ((hbr2.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _
    have hx4_v : x4.regs argV = v.val := by
      simp only [x4, x3, Data.set_regs, Function.update_of_ne (by decide : argV ≠ s2),
        Function.update_of_ne (by decide : argV ≠ s0),
        Function.update_of_ne (by decide : argV ≠ pReg)]
      exact (hx2_reg argV (by decide) (by decide)).trans hv_reg
    have hx4_k : x4.regs argK = k := by
      simp only [x4, x3, Data.set_regs, Function.update_of_ne (by decide : argK ≠ s2),
        Function.update_of_ne (by decide : argK ≠ s0),
        Function.update_of_ne (by decide : argK ≠ pReg)]
      exact (hx2_reg argK (by decide) (by decide)).trans hk_reg
    have hx4_p : x4.regs pReg = p₀.val := by
      simp only [x4, x3, Data.set_regs, Function.update_of_ne (by decide : pReg ≠ s2),
        Function.update_of_ne (by decide : pReg ≠ s0), Function.update_self]
    have hx4_s2 : x4.regs s2 = st₀.key p₀ := by
      simp only [x4, Data.set_regs, Function.update_self]
    have he_plt_p := prioLTFlag_exec (w := w) hbr4 argV argK pReg s2 s3
    dsimp only at he_plt_p
    rw [hx4_k, hx4_s2, hx4_v, hx4_p] at he_plt_p
    let bval_p := if IndexedMinPQ.PrioLT (v, k) (p₀, st₀.key p₀) then 1 else 0
    have ep_plt : ExecWithin w (prioLTFlag argV argK pReg s2 s3) x4 (x4.set s3 bval_p) 6 :=
      he_plt_p
    let x5 := x4.set s3 bval_p
    have hb5 : x5.Bounded w := ep_plt.bounded (ep_ld.bounded (ep_add.bounded (ep_sub.bounded hb2)))
    have hbr5 : BaseRegs n base x5 := hbr4.set_non_base (by decide) bval_p
    have hst5 : RawState.ofData n base x5 = { st₀ with key := Function.update st₀.key v k } := by
      simp only [x5, x4, x3, ofData_set_scratch _ (by decide : 17 ≤ s3.val),
        ofData_set_scratch _ (by decide : 17 ≤ s2.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val),
        ofData_set_scratch _ (by decide : 17 ≤ pReg.val), hst2]
    have hpot5 : potential x5 = potential x :=
      (potential_supported fun i hi => by
        have h1 : i ≠ s3 := fun e => by subst e; cases hi
        have h2 : i ≠ s2 := fun e => by subst e; cases hi
        have h3 : i ≠ s0 := fun e => by subst e; cases hi
        have h4 : i ≠ pReg := fun e => by subst e; cases hi
        simp only [x5, x4, x3, Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne h3, Function.update_of_ne h4]).trans hpot2
    have hx5_z0 : x5.regs zeroP = 0 := hbr5.2.2.2.2.2.2.2.2.2.2.2.1
    have hx5_v : x5.regs argV = v.val := by
      simp only [x5, Data.set_regs, Function.update_of_ne (by decide : argV ≠ s3), hx4_v]
    have hx5_k : x5.regs argK = k := by
      simp only [x5, Data.set_regs, Function.update_of_ne (by decide : argK ≠ s3), hx4_k]
    have hx5_p : x5.regs pReg = p₀.val := by
      simp only [x5, Data.set_regs, Function.update_of_ne (by decide : pReg ≠ s3), hx4_p]
    by_cases hviol : IndexedMinPQ.PrioLT (v, k) (p₀, st₀.key p₀)
    · -- Case B2: parent heap order violated (`PrioLT (v, k) (p₀, st₀.key p₀)`) → cut + cascade!
      have hc_viol : (Cond.lt zeroP s3).Holds x5 := by
        rw [Cond.Holds, hx5_z0]
        simp only [x5, Data.set_regs, Function.update_self, bval_p, hviol, ↓reduceIte]
        exact Nat.zero_lt_one
      let x6 := x5.set zReg v.val
      have ez_init : ExecWithin (B := .exact) w (.op (.copy zReg argV)) x5 x6 1 := by
        simpa only [hx5_v] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x5) (d := zReg) (s := argV))
      have hb6 : x6.Bounded w := ez_init.bounded hb5
      have hbr6 : BaseRegs n base x6 := hbr5.set_non_base (by decide) v.val
      have hst6 : RawState.ofData n base x6 = { st₀ with key := Function.update st₀.key v k } :=
        (ofData_set_scratch x5 (by decide : 17 ≤ zReg.val) v.val).trans hst5
      have hpot6 : potential x6 = potential x :=
        (potential_supported fun i hi => by
          have h1 : i ≠ zReg := fun e => by subst e; cases hi
          simp only [x6, Data.set_regs, Function.update_of_ne h1]).trans hpot5
      have hx6_z : x6.regs zReg = v.val := by simp only [x6, Data.set_regs, Function.update_self]
      have hx6_p : x6.regs pReg = p₀.val := by
        simp only [x6, Data.set_regs, Function.update_of_ne (by decide : pReg ≠ zReg), hx5_p]
      have hx6_v : x6.regs argV = v.val := by
        simp only [x6, Data.set_regs, Function.update_of_ne (by decide : argV ≠ zReg), hx5_v]
      have hx6_k : x6.regs argK = k := by
        simp only [x6, Data.set_regs, Function.update_of_ne (by decide : argK ≠ zReg), hx5_k]
      -- Initial cut of `v` from `p₀` via `cutNode_forest`
      have hTrv_ne_v_all : ∀ T ∈ ts₀, v ∈ T.nodes → T.root ≠ v := fun T hT _ e =>
        hpv0 (e ▸ (hts₀ T hT).2.1)
      obtain ⟨x7, he_cut0, hb7, hbr7, hmod7, hx7_reg, hpot_cut0,
        ts₁, hts₁, hnd₁, hdom₁, hnr₁, hrl₁, hTv₁, hmin₁, hp₀_tree_ne_v, hcut₁⟩ :=
        cutNode_forest (K_max := K_max) (s' := s') (pending := none) (st_pre := st₀)
          hb6 hbr6 hx6_z hx6_p (Or.inl rfl)
          (by rw [hst6]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            by dsimp only; rw [Function.update_self]; exact hkle_st₀,
            fun u hu => Function.update_of_ne hu k st₀.key⟩)
          hts₀ hnd₀
          (fun u => (hdom₀ u).trans (hs'_isSome u ▸ Iff.rfl))
          (fun u => by rw [hst6, hs'_isSome]; exact hin₀ u)
          (by rw [hst6]; exact hs'_keys)
          (by rw [hst6, hdom_s']; exact hsz₀)
          (by rw [hst6]; exact hnr₀)
          (by rw [hst6]; exact hnm₀.trans (markedCount_congr fun _ => Iff.rfl).symm)
          (by rw [hst6]; exact hcons₀)
          (by rw [hst6]; exact hmin₀)
          (by rw [hst6]; exact hcirc₀)
          hperm₀
          (by rw [hst6]; exact hmin_other2)
          (Or.inl rfl)
          hTrv_ne_v_all
          hv_in_fn₀
          (by rw [hst6]; exact hpv_eq)
      have hpot7_le : potential x7 ≤ potential x + unitCredit := by
        by_cases hmk_v : (RawState.ofData n base x6).mark v = 0
        · rw [hpot_cut0.2 hmk_v, hpot6]
        · have h1 := hpot_cut0.1 hmk_v
          dsimp only [unitCredit] at h1 ⊢
          omega
      have hx7_p : x7.regs pReg = p₀.val :=
        (hx7_reg pReg (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hx6_p
      have hx7_v : x7.regs argV = v.val :=
        (hx7_reg argV (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hx6_v
      have hx7_k : x7.regs argK = k :=
        (hx7_reg argK (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hx6_k
      let x8 := x7.set zReg p₀.val
      have ez_p0 : ExecWithin (B := .exact) w (.op (.copy zReg pReg)) x7 x8 1 := by
        simpa only [hx7_p] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x7) (d := zReg) (s := pReg))
      have hb8 : x8.Bounded w := ez_p0.bounded hb7
      have hbr8 : BaseRegs n base x8 := hbr7.set_non_base (by decide) p₀.val
      have hst8 : RawState.ofData n base x8 = RawState.ofData n base x7 :=
        ofData_set_scratch x7 (by decide : 17 ≤ zReg.val) p₀.val
      have hpot8 : potential x8 = potential x7 :=
        potential_supported fun i hi => by
          have h1 : i ≠ zReg := fun e => by subst e; cases hi
          simp only [x8, Data.set_regs, Function.update_of_ne h1]
      have hx8_z : x8.regs zReg = p₀.val := by simp only [x8, Data.set_regs, Function.update_self]
      obtain ⟨x9, he_cg0, hbr9, hst9, hmem9, hx9_ic, hx9_reg⟩ := evalCascGuard_exec hb8 hbr8 hx8_z
      have hb9 : x9.Bounded w := he_cg0.bounded hb8
      have hpot9 : potential x9 = potential x7 :=
        (potential_supported fun i hi =>
          hx9_reg i (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)
            (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)).trans hpot8
      have hmod9 : Modifies (Block.mk base (space n)).footprint x.mem x9.mem :=
        hmem9 ▸ modifies_block_trans hmod2 hmod7
      -- Cascading cut `while` loop via `ExecWithin.loop_potential_retain`
      let loopBody : Code .exact rFib :=
        .seq (.op (.exactBin .add s0 parBase zReg)) <|
        .seq (.op (.load s1 s0)) <|
        .seq (.op (.exactBin .sub pReg s1 oneP)) <|
        .seq cutNodeCode <|
        .seq (.op (.copy zReg pReg)) evalCascGuard
      let loopInv (a : Data rFib) : Prop :=
        a.Bounded w ∧ BaseRegs n base a ∧
        Modifies (Block.mk base (space n)).footprint x.mem a.mem ∧
        a.regs argV = v.val ∧ a.regs argK = k ∧
        ∃ (cur : Fin n) (ts_c : List (FHTree n)),
          a.regs zReg = cur.val ∧
          cur ∈ forestNodes ts_c ∧
          (∀ T ∈ ts_c, cur ∈ T.nodes → T.root ≠ v) ∧
          (∀ T ∈ ts_c, ValidRoot (RawState.ofData n base a) (some cur) T) ∧
          (forestNodes ts_c).Nodup ∧
          (∀ u : Fin n, u ∈ forestNodes ts_c ↔ (s' u).isSome) ∧
          (RawState.ofData n base a).numRoots = ts_c.length ∧
          (∃ rtail_c : List (Fin n),
            (RawState.ofData n base a).minRoot = m.val + 1 ∧
            IsCircList (RawState.ofData n base a).left (RawState.ofData n base a).right
              (m :: rtail_c) ∧
            (m :: rtail_c).Perm (ts_c.map FHTree.root)) ∧
          (∃ T_v ∈ ts_c, T_v.root = v) ∧
          (∀ T ∈ ts_c, T.root ≠ v →
            IndexedMinPQ.PrioLE (m, (RawState.ofData n base a).key m)
              (T.root, (RawState.ofData n base a).key T.root)) ∧
          CutInv n K_max s' (RawState.ofData n base a) v m (some cur) ∧
          a.regs iterCur =
            if (RawState.ofData n base a).par cur ≠ 0 ∧ (RawState.ofData n base a).mark cur ≠ 0
            then 1 else 0
      have hp₀_in_fn1 : p₀ ∈ forestNodes ts₁ :=
        (hdom₁ p₀).mpr ((hdom₀ p₀).mp (mem_forestNodes_iff.mpr ⟨T_rv, hTrv_mem, hp₀_in_Trv⟩) |>
          fun h => by rw [hs'_isSome]; exact h)
      have hx9_inv : loopInv x9 := by
        have hx8_v : x8.regs argV = v.val := by
          simp only [x8, Data.set_regs, Function.update_of_ne (by decide : argV ≠ zReg), hx7_v]
        have hx8_k : x8.regs argK = k := by
          simp only [x8, Data.set_regs, Function.update_of_ne (by decide : argK ≠ zReg), hx7_k]
        have h9_v : x9.regs argV = v.val :=
          (hx9_reg argV (by decide) (by decide) (by decide) (by decide)).trans hx8_v
        have h9_k : x9.regs argK = k :=
          (hx9_reg argK (by decide) (by decide) (by decide) (by decide)).trans hx8_k
        have h9_z : x9.regs zReg = p₀.val :=
          (hx9_reg zReg (by decide) (by decide) (by decide) (by decide)).trans hx8_z
        have hst97 : RawState.ofData n base x9 = RawState.ofData n base x7 := hst9.trans hst8
        refine ⟨hb9, hbr9, hmod9, h9_v, h9_k, p₀, ts₁, h9_z, hp₀_in_fn1, hp₀_tree_ne_v, ?_⟩
        rw [hst97]
        rw [hst8] at hx9_ic
        exact ⟨hts₁, hnd₁, hdom₁, hnr₁, hrl₁, hTv₁, hmin₁, hcut₁, hx9_ic⟩
      obtain ⟨z_lp, t_lp, he_lp, hz_inv, hz_exit, hpot_lp⟩ :=
        ExecWithin.loop_potential_retain (B := .exact) (w := w)
          (cond := .lt zeroP iterCur) (body := loopBody) loopInv potential
          (fun a ha hc_a => by
            rcases ha with ⟨hba, hbra, hmoda, ha_v, ha_k,
              cur, ts_c, ha_z, hcur_fn, hcur_ne_v, hts_c, hnd_c, hdom_c, hnr_c,
              ⟨rtail_c, hmin_c, hcirc_c, hperm_c⟩, hTv_c, hmin_oth_c, hcut_a, ha_ic⟩
            set st_a := RawState.ofData n base a with hst_a_def
            have ha_z0 : a.regs zeroP = 0 := hbra.2.2.2.2.2.2.2.2.2.2.2.1
            have ha_o1 : a.regs oneP = 1 := hbra.2.2.2.2.2.2.2.2.2.2.2.2
            have ha_pb : a.regs parBase = base + n := hbra.2.2.2.1
            have hfit_a := hbra.fits_stop hba
            have hcond_true : st_a.par cur ≠ 0 ∧ st_a.mark cur ≠ 0 := by
              rw [Cond.Holds, ha_z0, ha_ic] at hc_a
              by_contra hnot
              simp only [hnot, ↓reduceIte, lt_self_iff_false] at hc_a
            obtain ⟨T_ci, hTci_mem, hcur_Tci⟩ := mem_forestNodes_iff.mp hcur_fn
            have hcur_ne_root : cur ≠ T_ci.root := fun e =>
              hcond_true.1 (((hts_c T_ci hTci_mem).par_eq_zero_iff_root hcur_Tci).mpr e)
            have hcur_desc_c : cur ∈ forestNodes T_ci.children := by
              rw [T_ci.nodes_eq] at hcur_Tci
              exact (List.mem_cons.mp hcur_Tci).resolve_left hcur_ne_root
            obtain ⟨p_c, hp_c_in, hpar_cur_c⟩ :=
              (hts_c T_ci hTci_mem).1.par_of_mem_children cur hcur_desc_c
            have hcur_lt_c := cur.isLt
            have hpc_lt := p_c.isLt
            -- `s0 ← parBase + zReg; s1 ← *s0; pReg ← s1 - oneP` (`a → a3` in 3 steps)
            let a1 := a.set s0 (base + n + cur.val)
            let a2 := a1.set s1 (st_a.par cur)
            let a3 := a2.set pReg p_c.val
            have b1 : ExecWithin w (.op (.exactBin .add s0 parBase zReg)) a a1 1 := by
              simpa only [ha_pb, ha_z] using
                execWithin_exactAdd (x := a) (d := s0) (i := parBase) (j := zReg)
                  (by rw [ha_pb, ha_z]; unfold space at hfit_a; exact hfit_a.of_le (by omega))
            have b2 : ExecWithin (B := .exact) w (.op (.load s1 s0)) a1 a2 1 := by
              have hs0_a1 : a1.regs s0 = base + n + cur.val := by
                simp only [a1, Data.set_regs, Function.update_self]
              have hm_p : a1.mem (base + n + cur.val) = st_a.par cur := rfl
              simpa only [hs0_a1, hm_p] using
                (ExecWithin.load (B := .exact) (w := w) (x := a1) (d := s1) (a := s0))
            have b3 : ExecWithin w (.op (.exactBin .sub pReg s1 oneP)) a2 a3 1 := by
              have hs1 : a2.regs s1 = p_c.val + 1 := by
                simp only [a2, Data.set_regs, Function.update_self, hpar_cur_c]
              have ho : a2.regs oneP = 1 := by
                simp only [a2, a1, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ s1),
                  Function.update_of_ne (by decide : oneP ≠ s0), ha_o1]
              simpa only [hs1, ho, Nat.add_sub_cancel] using
                execWithin_exactSub (x := a2) (d := pReg) (i := s1) (j := oneP)
                  (by rw [hs1, ho]; omega)
                  (by rw [hs1, ho]; unfold space at hfit_a; exact hfit_a.of_le (by omega))
            have hb_a3 : a3.Bounded w := b3.bounded (b2.bounded (b1.bounded hba))
            have hbr_a3 : BaseRegs n base a3 :=
              ((hbra.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
                (by decide) _
            have hst_a3 : RawState.ofData n base a3 = st_a := by
              simp only [a3, a2, a1, ofData_set_scratch _ (by decide : 17 ≤ pReg.val),
                ofData_set_scratch _ (by decide : 17 ≤ s1.val),
                ofData_set_scratch _ (by decide : 17 ≤ s0.val), ← hst_a_def]
            have hpot_a3 : potential a3 = potential a :=
              potential_supported fun i hi => by
                have h1 : i ≠ pReg := fun e => by subst e; cases hi
                have h2 : i ≠ s1 := fun e => by subst e; cases hi
                have h3 : i ≠ s0 := fun e => by subst e; cases hi
                simp only [a3, a2, a1, Data.set_regs, Function.update_of_ne h1,
                  Function.update_of_ne h2, Function.update_of_ne h3]
            have ha3_z : a3.regs zReg = cur.val := by
              simp only [a3, a2, a1, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ pReg),
                Function.update_of_ne (by decide : zReg ≠ s1),
                Function.update_of_ne (by decide : zReg ≠ s0), ha_z]
            have ha3_p : a3.regs pReg = p_c.val := by
              simp only [a3, Data.set_regs, Function.update_self]
            have ha3_v : a3.regs argV = v.val := by
              simp only [a3, a2, a1, Data.set_regs, Function.update_of_ne (by decide : argV ≠ pReg),
                Function.update_of_ne (by decide : argV ≠ s1),
                Function.update_of_ne (by decide : argV ≠ s0), ha_v]
            have ha3_k : a3.regs argK = k := by
              simp only [a3, a2, a1, Data.set_regs, Function.update_of_ne (by decide : argK ≠ pReg),
                Function.update_of_ne (by decide : argK ≠ s1),
                Function.update_of_ne (by decide : argK ≠ s0), ha_k]
            obtain ⟨_, _, _, _, hin_ca, hkeys_ca, hsz_ca, _, hnm_ca, hco_ca, _, _, _⟩ := hcut_a
            obtain ⟨a4, b4, hb_a4, hbr_a4, hmod_a4, ha4_reg, hpot_a4,
              ts_n, hts_n, hnd_n, hdom_n, hnr_n, hrl_n, hTv_n, hmin_n, hp_ne_v_n, hcut_n⟩ :=
              cutNode_forest (K_max := K_max) (s' := s') (pending := some cur) (st_pre := st_a)
                hb_a3 hbr_a3 ha3_z ha3_p (Or.inr rfl)
                (by rw [hst_a3]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, fun _ _ => rfl⟩)
                hts_c hnd_c hdom_c
                (by rw [hst_a3]; exact hin_ca)
                (by rw [hst_a3]; exact hkeys_ca)
                (by rw [hst_a3]; exact hsz_ca)
                (by rw [hst_a3]; exact hnr_c)
                (by rw [hst_a3]; exact hnm_ca)
                (by rw [hst_a3]; exact hco_ca)
                (by rw [hst_a3]; exact hmin_c)
                (by rw [hst_a3]; exact hcirc_c)
                hperm_c
                (by rw [hst_a3]; exact hmin_oth_c)
                (Or.inr ⟨by rw [hst_a3], hTv_c⟩)
                hcur_ne_v
                hcur_fn
                (by rw [hst_a3]; exact hpar_cur_c)
            have hpot_drop : potential a4 + unitCredit = potential a := by
              have hmk_a3 : (RawState.ofData n base a3).mark cur ≠ 0 := by
                rw [hst_a3]; exact hcond_true.2
              exact (hpot_a4.1 hmk_a3).trans hpot_a3
            have ha4_p : a4.regs pReg = p_c.val :=
              (ha4_reg pReg (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)).trans ha3_p
            have ha4_v : a4.regs argV = v.val :=
              (ha4_reg argV (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)).trans ha3_v
            have ha4_k : a4.regs argK = k :=
              (ha4_reg argK (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)).trans ha3_k
            let a5 := a4.set zReg p_c.val
            have b5 : ExecWithin (B := .exact) w (.op (.copy zReg pReg)) a4 a5 1 := by
              simpa only [ha4_p] using
                (ExecWithin.copy (B := .exact) (w := w) (x := a4) (d := zReg) (s := pReg))
            have hb_a5 : a5.Bounded w := b5.bounded hb_a4
            have hbr_a5 : BaseRegs n base a5 := hbr_a4.set_non_base (by decide) p_c.val
            have hst_a5 : RawState.ofData n base a5 = RawState.ofData n base a4 :=
              ofData_set_scratch a4 (by decide : 17 ≤ zReg.val) p_c.val
            have ha5_z : a5.regs zReg = p_c.val := by
              simp only [a5, Data.set_regs, Function.update_self]
            obtain ⟨a6, b6, hbr_a6, hst_a6, hmem_a6, ha6_ic, ha6_reg⟩ :=
              evalCascGuard_exec hb_a5 hbr_a5 ha5_z
            have hpot_a6 : potential a6 = potential a4 := by
              have hp65 : potential a6 = potential a5 :=
                potential_supported fun i hi =>
                  ha6_reg i (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)
                    (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)
              have hp54 : potential a5 = potential a4 :=
                potential_supported fun i hi => by
                  have h1 : i ≠ zReg := fun e => by subst e; cases hi
                  simp only [a5, Data.set_regs, Function.update_of_ne h1]
              exact hp65.trans hp54
            have he_body : ExecWithin w loopBody a a6 48 :=
              (b1.seq <| b2.seq <| b3.seq <| b4.seq <| b5.seq b6).mono (by omega)
            have hpc_in_fn : p_c ∈ forestNodes ts_n :=
              (hdom_n p_c).mpr ((hdom_c p_c).mp (mem_forestNodes_iff.mpr ⟨T_ci, hTci_mem, hp_c_in⟩))
            have ha5_v : a5.regs argV = v.val := by
              simp only [a5, Data.set_regs, Function.update_of_ne (by decide : argV ≠ zReg), ha4_v]
            have ha5_k : a5.regs argK = k := by
              simp only [a5, Data.set_regs, Function.update_of_ne (by decide : argK ≠ zReg), ha4_k]
            have ha6_v : a6.regs argV = v.val :=
              (ha6_reg argV (by decide) (by decide) (by decide) (by decide)).trans ha5_v
            have ha6_k : a6.regs argK = k :=
              (ha6_reg argK (by decide) (by decide) (by decide) (by decide)).trans ha5_k
            have ha6_z : a6.regs zReg = p_c.val :=
              (ha6_reg zReg (by decide) (by decide) (by decide) (by decide)).trans ha5_z
            have hst64 : RawState.ofData n base a6 = RawState.ofData n base a4 :=
              hst_a6.trans hst_a5
            refine ⟨a6, 48, he_body,
              ⟨b6.bounded hb_a5, hbr_a6, hmem_a6 ▸ modifies_block_trans hmoda hmod_a4,
                ha6_v, ha6_k, p_c, ts_n, ha6_z, hpc_in_fn, hp_ne_v_n, ?_⟩,
              by dsimp only [unitCredit] at hpot_drop ⊢; omega⟩
            rw [hst64]
            rw [hst_a5] at ha6_ic
            exact ⟨hts_n, hnd_n, hdom_n, hnr_n, hrl_n, hTv_n, hmin_n, hcut_n, ha6_ic⟩)
          hx9_inv
      -- Post-loop mark step (`z_lp → x_post` in at most 6 steps, restoring `CutInv ... none`)
      rcases hz_inv with ⟨hb_lp, hbr_lp, hmod_lp, hlp_v, hlp_k,
        cur_f, ts_f, hlp_z, hcurf_fn, _, hts_f, hnd_f, hdom_f, hnr_f,
        hrl_f, hTv_f, hmin_f, hcut_lp, hlp_ic⟩
      set st_lp := RawState.ofData n base z_lp with hst_lp_def
      have hlp_z0 : z_lp.regs zeroP = 0 := hbr_lp.2.2.2.2.2.2.2.2.2.2.2.1
      have hlp_o1 : z_lp.regs oneP = 1 := hbr_lp.2.2.2.2.2.2.2.2.2.2.2.2
      have hlp_pb : z_lp.regs parBase = base + n := hbr_lp.2.2.2.1
      have hlp_mb : z_lp.regs markBase = base + 6 * n := hbr_lp.2.2.2.2.2.2.2.2.1
      have hfit_lp := hbr_lp.fits_stop hb_lp
      have hcurf_lt := cur_f.isLt
      have hnot_both : ¬(st_lp.par cur_f ≠ 0 ∧ st_lp.mark cur_f ≠ 0) := by
        intro hboth
        apply hz_exit
        simp only [Cond.Holds, hlp_z0, hlp_ic, hboth.1, hboth.2, ne_eq, not_false_eq_true,
          and_self, ↓reduceIte]
        exact Nat.zero_lt_one
      let z1 := (z_lp.set s0 (base + n + cur_f.val)).set s1 (st_lp.par cur_f)
      have pm1 : ExecWithin w (.op (.exactBin .add s0 parBase zReg)) z_lp
          (z_lp.set s0 (base + n + cur_f.val)) 1 := by
        simpa only [hlp_pb, hlp_z] using
          execWithin_exactAdd (x := z_lp) (d := s0) (i := parBase) (j := zReg)
            (by rw [hlp_pb, hlp_z]; unfold space at hfit_lp; exact hfit_lp.of_le (by omega))
      have pm2 : ExecWithin (B := .exact) w (.op (.load s1 s0))
          (z_lp.set s0 (base + n + cur_f.val)) z1 1 := by
        have hm_pf : z_lp.mem (base + n + cur_f.val) = st_lp.par cur_f := rfl
        simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_pf] using
          (ExecWithin.load (B := .exact) (w := w) (x := z_lp.set s0 (base + n + cur_f.val))
            (d := s1) (a := s0))
      have hz1_z0 : z1.regs zeroP = 0 := by
        simp only [z1, Data.set_regs, Function.update_of_ne (by decide : zeroP ≠ s1),
          Function.update_of_ne (by decide : zeroP ≠ s0), hlp_z0]
      have hz1_o1 : z1.regs oneP = 1 := by
        simp only [z1, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ s1),
          Function.update_of_ne (by decide : oneP ≠ s0), hlp_o1]
      have hz1_s1 : z1.regs s1 = st_lp.par cur_f := by
        simp only [z1, Data.set_regs, Function.update_self]
      let postBranch : Code .exact rFib :=
        .branch (.lt zeroP s1)
          (.seq (.op (.exactBin .add s0 markBase zReg)) <|
           .seq (.op (.store s0 oneP)) <|
                (.op (.exactBin .add numMarkedReg numMarkedReg oneP)))
          (.op (.copy s0 zeroP))
      have hpost : ∃ x_post, ExecWithin w postBranch z1 x_post 4 ∧
          x_post.Bounded w ∧ BaseRegs n base x_post ∧
          Modifies (Block.mk base (space n)).footprint x.mem x_post.mem ∧
          x_post.regs argV = v.val ∧ x_post.regs argK = k ∧
          (RawState.ofData n base x_post).minRoot = m.val + 1 ∧
          (RawState.ofData n base x_post).key v = k ∧
          CutInv n K_max s' (RawState.ofData n base x_post) v m none ∧
          potential x_post ≤ potential z_lp + 2 * unitCredit := by
        obtain ⟨_, _, _, _, hin_f, hkeys_f, hsz_f, _, hnm_f, hco_f, _, _, _⟩ := hcut_lp
        have hkv_lp : st_lp.key v = k := (hkeys_f v k (Function.update_self v (some k) s)).1
        by_cases hpf0 : st_lp.par cur_f = 0
        · have hc_p : ¬(Cond.lt zeroP s1).Holds z1 := by
            simp only [Cond.Holds, hz1_z0, hz1_s1, hpf0, lt_self_iff_false, not_false_eq_true]
          let x_post := z1.set s0 0
          have he_p : ExecWithin w postBranch z1 x_post 4 :=
            (ExecWithin.branch_neg hc_p (by
              simpa only [hz1_z0] using
                (ExecWithin.copy (B := .exact) (w := w) (x := z1) (d := s0) (s := zeroP)))).mono
              (by omega)
          have hst_post : RawState.ofData n base x_post = st_lp := by
            simp only [x_post, z1, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
              ofData_set_scratch _ (by decide : 17 ≤ s1.val), ← hst_lp_def]
          have hpot_post : potential x_post = potential z_lp :=
            potential_supported fun i hi => by
              have h0 : i ≠ s0 := fun e => by subst e; cases hi
              have h1 : i ≠ s1 := fun e => by subst e; cases hi
              simp only [x_post, z1, Data.set_regs, Function.update_of_ne h0,
                Function.update_of_ne h1]
          obtain ⟨T_cf, hTcf_mem, hcurf_in_Tcf⟩ := mem_forestNodes_iff.mp hcurf_fn
          have hcurf_root : cur_f = T_cf.root :=
            ((hts_f T_cf hTcf_mem).par_eq_zero_iff_root hcurf_in_Tcf).mp hpf0
          have hts_none : ∀ T ∈ ts_f, ValidRoot st_lp none T := fun T hT => by
            have hnot_desc : cur_f ∉ forestNodes T.children := by
              by_cases hTT : T = T_cf
              · subst hTT
                have hnd_T := forestNodes_nodup_tree hnd_f hT
                rw [T.nodes_eq, ← hcurf_root] at hnd_T
                exact (List.nodup_cons.mp hnd_T).1
              · intro hm_in
                exact forestNodes_nodup_disjoint hnd_f hTcf_mem hT (Ne.symm hTT) hcurf_in_Tcf
                  (T.nodes_eq ▸ List.mem_cons_of_mem _ hm_in)
            exact ⟨(hts_f T hT).1.clear_pending hnot_desc, (hts_f T hT).2.1, (hts_f T hT).2.2⟩
          refine ⟨x_post, he_p, he_p.bounded (pm2.bounded (pm1.bounded hb_lp)),
            (((hbr_lp.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
              (by decide) _),
            hmod_lp,
            by simp only [x_post, z1, Data.set_regs, Function.update_of_ne (by decide : argV ≠ s0),
              Function.update_of_ne (by decide : argV ≠ s1), hlp_v],
            by simp only [x_post, z1, Data.set_regs, Function.update_of_ne (by decide : argK ≠ s0),
              Function.update_of_ne (by decide : argK ≠ s1), hlp_k],
            by rw [hst_post]; exact hrl_f.choose_spec.1,
            by rw [hst_post]; exact hkv_lp,
            by rw [hst_post]; exact ⟨ts_f, hts_none, hnd_f, hdom_f, hin_f, hkeys_f, hsz_f,
              hnr_f, hnm_f, hco_f, hrl_f, hTv_f, hmin_f⟩,
            by omega⟩
        · have hmf0 : st_lp.mark cur_f = 0 := by
            by_contra hmf_ne
            exact hnot_both ⟨hpf0, hmf_ne⟩
          have hc_p : (Cond.lt zeroP s1).Holds z1 := by
            simp only [Cond.Holds, hz1_z0, hz1_s1]; omega
          have ho_mf := owns_arr_addr (base := base) (k := 6) (by decide) hcurf_lt
          have hin_curf : st_lp.inHeap cur_f ≠ 0 :=
            (hin_f cur_f).1.mpr ((hdom_f cur_f).mp hcurf_fn)
          -- Bound `st_lp.numMarked + 1 ≤ n` via `markedCount_set_one`
          let st_mk : RawState n :=
            { st_lp with
              mark := Function.update st_lp.mark cur_f 1
              numMarked := st_lp.numMarked + 1 }
          have hmc_mk : markedCount st_mk = markedCount st_lp + 1 :=
            markedCount_set_one (st := st_lp) (st' := st_mk) (u := cur_f) hin_curf hmf0
              (by simp only [st_mk, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true])
              (fun u huc => by simp only [st_mk, Function.update_of_ne huc])
          have hnm_add_le : st_lp.numMarked + 1 ≤ n := by
            have := markedCount_le_n st_mk
            omega
          let z2 := (z1.set s0 (base + 6 * n + cur_f.val)).write (base + 6 * n + cur_f.val) 1
          let x_post := z2.set numMarkedReg (st_lp.numMarked + 1)
          have ma1 : ExecWithin w (.op (.exactBin .add s0 markBase zReg)) z1
              (z1.set s0 (base + 6 * n + cur_f.val)) 1 := by
            have hmb : z1.regs markBase = base + 6 * n := by
              simp only [z1, Data.set_regs, Function.update_of_ne (by decide : markBase ≠ s1),
                Function.update_of_ne (by decide : markBase ≠ s0), hlp_mb]
            have hzr : z1.regs zReg = cur_f.val := by
              simp only [z1, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ s1),
                Function.update_of_ne (by decide : zReg ≠ s0), hlp_z]
            simpa only [hmb, hzr] using
              execWithin_exactAdd (x := z1) (d := s0) (i := markBase) (j := zReg)
                (by rw [hmb, hzr]; unfold space at hfit_lp; exact hfit_lp.of_le (by omega))
          have ms1 : ExecWithin (B := .exact) w (.op (.store s0 oneP))
              (z1.set s0 (base + 6 * n + cur_f.val)) z2 1 := by
            have hs0 : (z1.set s0 (base + 6 * n + cur_f.val)).regs s0 =
                base + 6 * n + cur_f.val := by simp only [Data.set_regs, Function.update_self]
            have ho : (z1.set s0 (base + 6 * n + cur_f.val)).regs oneP = 1 := by
              simp only [Data.set_regs, Function.update_of_ne (by decide : oneP ≠ s0), hz1_o1]
            simpa only [hs0, ho] using
              (ExecWithin.store (B := .exact) (w := w) (x := z1.set s0 (base + 6 * n + cur_f.val))
                (a := s0) (s := oneP))
          have ma2 : ExecWithin w (.op (.exactBin .add numMarkedReg numMarkedReg oneP))
              z2 x_post 1 := by
            have hnm_z2 : z2.regs numMarkedReg = st_lp.numMarked := by
              simp only [z2, z1, Data.write_regs, Data.set_regs,
                Function.update_of_ne (by decide : numMarkedReg ≠ s0),
                Function.update_of_ne (by decide : numMarkedReg ≠ s1)]
              rfl
            have ho_z2 : z2.regs oneP = 1 := by
              simp only [z2, Data.write_regs, Data.set_regs,
                Function.update_of_ne (by decide : oneP ≠ s0), hz1_o1]
            simpa only [hnm_z2, ho_z2] using
              execWithin_exactAdd (x := z2) (d := numMarkedReg) (i := numMarkedReg) (j := oneP)
                (by rw [hnm_z2, ho_z2]; unfold space at hfit_lp; exact hfit_lp.of_le (by omega))
          have he_p : ExecWithin w postBranch z1 x_post 4 :=
            ExecWithin.branch_pos hc_p (ma1.seq <| ms1.seq ma2)
          have hst_post : RawState.ofData n base x_post = st_mk := by
            simp only [x_post, z2, z1, ofData_set_numMarked, ofData_write_mark,
              ofData_set_scratch _ (by decide : 17 ≤ s0.val),
              ofData_set_scratch _ (by decide : 17 ≤ s1.val), st_mk, ← hst_lp_def]
          have hts_none : ∀ T ∈ ts_f, ValidRoot st_mk none T := fun T hT => by
            have hr_ne_curf : T.root ≠ cur_f := fun e =>
              hpf0 (e ▸ (hts_f T hT).2.1)
            exact ⟨(hts_f T hT).1.mark_pending hmf0 (Function.update_self cur_f 1 st_lp.mark)
              (fun u _ huc => Function.update_of_ne huc 1 st_lp.mark)
              (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩),
              (hts_f T hT).2.1,
              (Function.update_of_ne hr_ne_curf 1 st_lp.mark).trans (hts_f T hT).2.2⟩
          have hpot_post : potential x_post = potential z_lp + 2 * unitCredit := by
            have hnr_post : x_post.regs numRootsReg = z_lp.regs numRootsReg := by
              simp only [x_post, z2, z1, Data.write_regs, Data.set_regs,
                Function.update_of_ne (by decide : numRootsReg ≠ numMarkedReg),
                Function.update_of_ne (by decide : numRootsReg ≠ s0),
                Function.update_of_ne (by decide : numRootsReg ≠ s1)]
            have hnm_post : x_post.regs numMarkedReg = z_lp.regs numMarkedReg + 1 := by
              simp only [x_post, Data.set_regs, Function.update_self]; rfl
            simp only [potential, unitCredit, hnr_post, hnm_post]
            omega
          refine ⟨x_post, he_p, he_p.bounded (pm2.bounded (pm1.bounded hb_lp)),
            ((((hbr_lp.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
              (by decide) _).write_eq _ _).set_non_base (by decide) _,
            modifies_block_trans hmod_lp (Modifies.write_of_owns ho_mf 1),
            by simp only [x_post, z2, z1, Data.write_regs, Data.set_regs,
              Function.update_of_ne (by decide : argV ≠ numMarkedReg),
              Function.update_of_ne (by decide : argV ≠ s0),
              Function.update_of_ne (by decide : argV ≠ s1), hlp_v],
            by simp only [x_post, z2, z1, Data.write_regs, Data.set_regs,
              Function.update_of_ne (by decide : argK ≠ numMarkedReg),
              Function.update_of_ne (by decide : argK ≠ s0),
              Function.update_of_ne (by decide : argK ≠ s1), hlp_k],
            by rw [hst_post]; exact hrl_f.choose_spec.1,
            by rw [hst_post]; exact hkv_lp,
            by rw [hst_post]; exact ⟨ts_f, hts_none, hnd_f, hdom_f, hin_f, hkeys_f, hsz_f,
              hnr_f, by change st_lp.numMarked + 1 = markedCount st_mk; rw [hmc_mk, hnm_f],
              hco_f, hrl_f, hTv_f, hmin_f⟩,
            by dsimp only [unitCredit] at hpot_post ⊢; omega⟩
      obtain ⟨x_post, he_post, hb_post, hbr_post, hmod_post, hp_v, hp_k, hp_min, hp_kv,
        hcut_post, hpot_post⟩ := hpost
      obtain ⟨y, he_tail, hby, hbry, hmemy, hpoty, hsty⟩ :=
        decreaseKeyTail_exec hb_post hbr_post hp_v hp_k hp_min hp_kv
      dsimp only at hsty
      have hraw_y : FibRawInv n K_max s' (RawState.ofData n base y) := by
        refine hcut_post.to_fibRawInv ?_ ?_
        · rw [hsty]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · by_cases hlt : IndexedMinPQ.PrioLT (v, (RawState.ofData n base x_post).key v)
              (m, (RawState.ofData n base x_post).key m)
          · exact Or.inl ⟨hlt, by rw [hsty]; simp only [hlt, ↓reduceIte]⟩
          · exact Or.inr ⟨hlt, by rw [hsty]; simp only [hlt, ↓reduceIte]⟩
      have he_all : ExecWithin w decreaseKeyCode x y (80 + t_lp) := by
        unfold decreaseKeyCode
        exact (ek1.seq <| ek2.seq <| ek3.seq <| ek4.seq <|
          (ExecWithin.branch_pos hc_outer
            (ep_sub.seq <| ep_add.seq <| ep_ld.seq <| ep_plt.seq <|
              ExecWithin.branch_pos hc_viol
                (ez_init.seq <| he_cut0.seq <| ez_p0.seq <| he_cg0.seq <|
                  he_lp.seq <| pm1.seq <| pm2.seq he_post))).seq he_tail).mono (by omega)
      exact ⟨y, 80 + t_lp, he_all, ⟨hby, hbry, hraw_y⟩, hmemy ▸ hmod_post, by
        dsimp only [unitCredit] at hpot7_le hpot_post ⊢
        omega⟩
    · -- Case B1: `¬PrioLT (v, k) (p₀, st₀.key p₀)` → no cuts needed, `minRoot` unchanged!
      have hc_viol : ¬(Cond.lt zeroP s3).Holds x5 := by
        rw [Cond.Holds, hx5_z0]
        simp only [x5, Data.set_regs, Function.update_self, bval_p, hviol,
          ↓reduceIte, lt_self_iff_false, not_false_eq_true]
      let x6 := x5.set s0 0
      have he_nop : ExecWithin (B := .exact) w (.op (.copy s0 zeroP)) x5 x6 1 := by
        simpa only [hx5_z0] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x5) (d := s0) (s := zeroP))
      have hb6 : x6.Bounded w := he_nop.bounded hb5
      have hbr6 : BaseRegs n base x6 := hbr5.set_non_base (by decide) 0
      have hst6 : RawState.ofData n base x6 = { st₀ with key := Function.update st₀.key v k } :=
        (ofData_set_scratch x5 (by decide : 17 ≤ s0.val) 0).trans hst5
      have hpot6 : potential x6 = potential x :=
        (potential_supported fun i hi => by
          have h0 : i ≠ s0 := fun e => by subst e; cases hi
          simp only [x6, Data.set_regs, Function.update_of_ne h0]).trans hpot5
      have hx6_v : x6.regs argV = v.val := by
        simp only [x6, Data.set_regs, Function.update_of_ne (by decide : argV ≠ s0), hx5_v]
      have hx6_k : x6.regs argK = k := by
        simp only [x6, Data.set_regs, Function.update_of_ne (by decide : argK ≠ s0), hx5_k]
      obtain ⟨y, he_tail, hby, hbry, hmemy, hpoty, hsty⟩ :=
        decreaseKeyTail_exec hb6 hbr6 hx6_v hx6_k (by rw [hst6]; exact hmin₀)
          (by rw [hst6]; exact Function.update_self v k st₀.key)
      dsimp only at hsty
      -- Prove `¬PrioLT (v, k) (m, (RawState.ofData n base x6).key m)` by transitivity!
      have hmv_ne : m ≠ v := fun e => hpv0 (e ▸ (by
        obtain ⟨R_m, hRm, hm_r⟩ := List.mem_map.mp (hperm₀.subset List.mem_cons_self)
        exact hm_r ▸ (hts₀ R_m hRm).2.1))
      have hnlt_m : ¬IndexedMinPQ.PrioLT (v, (RawState.ofData n base x6).key v)
          (m, (RawState.ofData n base x6).key m) := by
        rw [hst6]
        dsimp only
        rw [Function.update_self, Function.update_of_ne hmv_ne]
        rw [IndexedMinPQ.not_prioLT_iff_prioLE]
        have hle1 : IndexedMinPQ.PrioLE (m, st₀.key m) (T_rv.root, st₀.key T_rv.root) :=
          hmin_le₀ T_rv hTrv_mem
        have hle2 : IndexedMinPQ.PrioLE (T_rv.root, st₀.key T_rv.root) (p₀, st₀.key p₀) :=
          (hts₀ T_rv hTrv_mem).1.prioLE_of_mem hp₀_in_Trv
        have hle3 : IndexedMinPQ.PrioLE (p₀, st₀.key p₀) (v, k) :=
          IndexedMinPQ.not_prioLT_iff_prioLE.mp hviol
        exact (hle1.trans hle2).trans hle3
      have hsty_eq :
          RawState.ofData n base y = { st₀ with key := Function.update st₀.key v k } := by
        rw [hsty]
        simp only [hnlt_m, ↓reduceIte]
        rw [hst6, ← hmin₀]
      have hraw_y : FibRawInv n K_max s' (RawState.ofData n base y) := by
        rw [hsty_eq]
        refine ⟨ts₀, fun T hT => ?_, hnd₀, fun u => (hdom₀ u).trans (hs'_isSome u ▸ Iff.rfl),
          fun u => by rw [hs'_isSome]; exact hin₀ u,
          hs'_keys, by rw [hdom_s']; exact hsz₀, hnr₀,
          hnm₀.trans (markedCount_congr fun _ => Iff.rfl).symm,
          hcons₀, Or.inr ⟨m, rtail₀, hmin₀, hcirc₀, hperm₀, ?_⟩⟩
        · by_cases hTT : T = T_rv
          · subst hTT
            exact ⟨(hts₀ T hT).1.lower_key_no_cut hnd_Trv hv_in_Trv hkle_st₀
              (Function.update_self v k st₀.key) (fun u _ hu => Function.update_of_ne hu k st₀.key)
              (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩)
              (Or.inr ⟨p₀, hpv_eq, hviol⟩),
              (hts₀ T hT).2.1, (hts₀ T hT).2.2⟩
          · have hv_not : v ∉ T.nodes := fun hm_in =>
              forestNodes_nodup_disjoint hnd₀ hTrv_mem hT (Ne.symm hTT) hv_in_Trv hm_in
            exact ⟨(hts₀ T hT).1.frame
              (fun u hu => ⟨rfl, rfl, rfl, rfl,
                Function.update_of_ne (fun (e : u = v) => hv_not (e ▸ hu)) k st₀.key⟩)
              (fun _ _ => ⟨rfl, rfl, rfl, Iff.rfl⟩),
              (hts₀ T hT).2.1, (hts₀ T hT).2.2⟩
        · intro T hT
          have hTr_ne : T.root ≠ v := fun e => hpv0 (e ▸ (hts₀ T hT).2.1)
          exact hmin_other2 T hT hTr_ne
      have he_all : ExecWithin w decreaseKeyCode x y 330 := by
        unfold decreaseKeyCode
        exact (ek1.seq <| ek2.seq <| ek3.seq <| ek4.seq <|
          (ExecWithin.branch_pos hc_outer
            (ep_sub.seq <| ep_add.seq <| ep_ld.seq <| ep_plt.seq <|
              ExecWithin.branch_neg hc_viol he_nop)).seq he_tail).mono (by omega)
      exact ⟨y, 330, he_all, ⟨hby, hbry, hraw_y⟩, hmemy ▸ hmod2,
        by rw [hpoty, hpot6]⟩

end Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap
