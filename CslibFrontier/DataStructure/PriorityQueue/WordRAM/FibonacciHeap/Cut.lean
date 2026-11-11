/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.BasicOps
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.DecreaseKey

/-!
# Fibonacci Heap: `decreaseKey` and Cascading Cuts

This file proves the exact-Word-RAM specification `decreaseKeyCode_exec` (`O(1)` amortized time
under `potential = 80 * (numRoots + 2 * numMarked)`). The proofs step the machine code; the forest
reasoning is that of the record heap (`Cslib.DataStructure.PriorityQueue.FibonacciHeap`,
`DecreaseKey.lean`), applied to the machine state read as `RawState.ofData n base x`:

* **Single-edge cut (`cutNodeCode_raw`):** `cutNodeCode` runs in at most `36` instructions, and the
  state it leaves is `cutState`, so its effect is `CutsNode` (`cutsNode_cutState`). The potential
  drops by `80` when `cur` was marked and grows by `80` otherwise.
* **Cascading cuts (`decreaseKeyCode_exec`):** the machine writes the new key first, so the forest
  is read with the old keys as `Cascading`. Each cut is `CutsNode.cascading`, and the cascade ends
  with `Cascading.clear_root` or `Cascading.mark`. `Cascading.lowerRootKey` (after a cut) or
  `FibRawInv.lowerKey_noCut` (without one) then stores the key. `ExecWithin.loop_potential_retain`
  pays every cascading-cut iteration (`≤ 50` instructions including the loop step) out of the
  `-80` drop in `potential`; marking the stopping non-root ancestor costs `+160`, and `FibInv` is
  restored within amortized charge `330` (`335 ≤ tDec n` including dispatch).

## Main definitions

* `cutNodeCode` and `decreaseKeyCode` are defined in
  `CslibFrontier/DataStructure/PriorityQueue/WordRAM/FibonacciHeap/Program.lean`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.cutNodeCode_raw`: a single-edge cut, as
  `CutsNode`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.decreaseKeyCode_exec`: `O(1)` amortized
  `decreaseKey` specification with cascading cuts.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.FibonacciHeap hiding potential

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
  have hfit := hbr.fits_of_le hb
  have := cur.isLt
  unfold evalCascGuard
  wram_exec [hfit, hbr.regs_parBase, hbr.regs_markBase, hbr.regs_zeroP, hbr.regs_oneP, hz_reg]
  all_goals refine ⟨by wram_simp [BaseRegs.set_iff, hbr], by wram_simp [ofData_set_scratch]; rfl,
    rfl, ?_, fun r h0 h1 h2 h3 => by wram_simp⟩
  all_goals wram_simp [gval, st, RawState.ofData]; split_ifs <;> omega

/-! ## `cutNodeCode` machine execution -/

/-- Raw machine specification of `cutNodeCode`: cuts `cur` (`zReg`) from `p` (`pReg`) and splices
`cur` after `m` (`minRootReg = m.val + 1`) in at most `36` instructions. Its effect is `CutsNode`,
as for the record program `cut`: the machine state after the cut is `cutState`, and
`cutsNode_cutState` does the list reasoning. -/
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
    (hmk_cur : (RawState.ofData n base x).mark cur ≤ 1)
    (hnm : (RawState.ofData n base x).numMarked = markedCount (RawState.ofData n base x))
    (hnr_le : (RawState.ofData n base x).numRoots + 1 ≤ n) :
    ∃ y, ExecWithin w cutNodeCode x y 36 ∧
      BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 →
        r ≠ numMarkedReg → r ≠ numRootsReg → y.regs r = x.regs r) ∧
      (((RawState.ofData n base x).mark cur ≠ 0 → potential y + unitCredit = potential x) ∧
        ((RawState.ofData n base x).mark cur = 0 → potential y = potential x + unitCredit)) ∧
      CutsNode (RawState.ofData n base x) cur p m rtail (RawState.ofData n base y) := by
  have hfit := hbr.fits_of_le hb
  set st := RawState.ofData n base x with hst_def
  have hp_lt := p.isLt
  have hcur_lt := cur.isLt
  have hm_lt := m.isLt
  have hfp (a : ℕ) (ha : a < base ∨ base + space n ≤ a) : a < base ∨ base + 9 * n + 1 ≤ a := by
    unfold space at ha; omega
  have hdeg_p : x.mem (base + 5 * n + p.val) = st.deg p := rfl
  unfold cutNodeCode
  -- Step 1: decrement `deg[p]`, and stop at the branch on the new degree.
  wram_exec -split [hfit, hbr.regs_degBase, hbr.regs_oneP, hp_reg, hdeg_p]
  -- Step 2: unlink `cur` from the children of `p`; both alternatives are the two cases of
  -- `cutsNode_cutState`.
  refine WP.cut (fun y t => t ≤ 13 ∧ y.Bounded w ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 → y.regs r = x.regs r) ∧
      ∃ (left₁ right₁ : Fin n → ℕ) (child₁ : ℕ),
        ((st.deg p = 1 ∧ child₁ = 0 ∧ left₁ = st.left ∧ right₁ = st.right) ∨
          (2 ≤ st.deg p ∧ ∃ r l : Fin n, st.right cur = r.val ∧ st.left cur = l.val ∧
            child₁ = r.val + 1 ∧ left₁ = Function.update st.left r l.val ∧
            right₁ = Function.update st.right l r.val)) ∧
        RawState.ofData n base y = { st with
          deg := Function.update st.deg p (st.deg p - 1)
          child := Function.update st.child p child₁
          left := left₁
          right := right₁ })
    (WP.bounded (by wram_bounded <;> exact hfit _ (by omega)) ?_) ?_
  · by_cases hdp1 : st.deg p - 1 = 0
    · wram_exec [hfit, hbr.regs_childBase, hbr.regs_zeroP, hp_reg, hdp1]
      intro hb2
      refine ⟨by omega, hb2, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
        Modifies.block_iff.2 fun a ha => by have := hfp a ha; wram_simp,
        fun r h0 h1 h2 h3 h4 => by wram_simp, st.left, st.right, 0,
        Or.inl ⟨by omega, rfl, rfl, rfl⟩, ?_⟩
      wram_simp [ofData_write_child, ofData_write_deg, ofData_set_scratch, ← hst_def]
    · have hge2 : 2 ≤ st.deg p := by omega
      obtain ⟨h_w, tail_w, hcp_w, hcirc_w, hcur_w, hlen_w, hpar_w⟩ := hdp2 hge2
      obtain ⟨r_nb, l_nb, -, hr_cur, hl_cur, -⟩ := hcirc_w.remove hcur_w hlen_w
      have hr_lt := r_nb.isLt
      have hl_lt := l_nb.isLt
      have hr_cur' : x.mem (base + 4 * n + cur.val) = r_nb.val := hr_cur
      have hl_cur' : x.mem (base + 3 * n + cur.val) = l_nb.val := hl_cur
      wram_exec [hfit, hbr.regs_childBase, hbr.regs_leftBase, hbr.regs_rightBase, hbr.regs_zeroP,
        hbr.regs_oneP, hp_reg, hz_reg, hr_cur', hl_cur', hdp1]
      intro hb2
      refine ⟨by omega, hb2, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
        Modifies.block_iff.2 fun a ha => by have := hfp a ha; wram_simp,
        fun r h0 h1 h2 h3 h4 => by wram_simp, _, _, _,
        Or.inr ⟨hge2, r_nb, l_nb, hr_cur, hl_cur, rfl, rfl, rfl⟩, ?_⟩
      wram_simp [ofData_write_child, ofData_write_left, ofData_write_right,
        ofData_write_deg, ofData_set_scratch, ← hst_def]
  rintro x2 t2 ⟨ht2, hb2, hbr2, hmod2, hx2_reg, left₁, right₁, child₁, hunlink, hst2⟩
  have hx2_z : x2.regs zReg = cur.val :=
    (hx2_reg zReg (by decide) (by decide) (by decide) (by decide) (by decide)).trans hz_reg
  have hmin_x2 : x2.regs minRootReg = m.val + 1 := by
    change (RawState.ofData n base x2).minRoot = _
    rw [hst2]
    exact hmin
  -- Step 3: `s1 ← minRootReg - oneP`, and splice `cur` after `m`, whose right neighbour after
  -- the unlinking is `r'`.
  wram_exec [hfit, hbr2.regs_oneP, hmin_x2]
  obtain ⟨r', hr'⟩ := exists_right_min_of_unlink hdp2 hcirc_r hroots_par0 hunlink
  obtain ⟨x4, he4, hbr4, hmod4, hst4⟩ :=
    insertIntoNonEmptyList_exec (x := x2.set s1 m.val) (hReg := s1) (uReg := zReg) (h := m)
      (u := cur) (r := r') (hb2.set (hfit _ (by omega))) (hbr2.set_non_base (by decide) _)
      (by decide) (by decide) (by decide) (by decide) (by wram_simp) (by wram_simp [hx2_z])
      (by rw [ofData_set_scratch _ (by decide : 17 ≤ s1.val), hst2]; exact hr')
  rw [ofData_set_scratch _ (by decide : 17 ≤ s1.val)] at hst4
  refine WP.of_execWithin he4 ?_
  have hx4_reg (r : Fin rFib) (h0 : r ≠ s0) (h1 : r ≠ s1) (h2 : r ≠ s2) (h3 : r ≠ s3)
      (h4 : r ≠ s4) : x4.regs r = x.regs r := by
    rw [he4.regs_eq (insertIntoNonEmptyList_preserves h0 h2)]
    wram_simp [hx2_reg r h0 h1 h2 h3 h4]
  have hx4_z : x4.regs zReg = cur.val :=
    (hx4_reg zReg (by decide) (by decide) (by decide) (by decide) (by decide)).trans hz_reg
  have hp4 : (RawState.ofData n base x4).par = st.par := by rw [hst4, hst2]
  have hmk4 : (RawState.ofData n base x4).mark = st.mark := by rw [hst4, hst2]
  have hnm4 : (RawState.ofData n base x4).numMarked = st.numMarked := by rw [hst4, hst2]
  have hmk4_cur : x4.mem (base + 6 * n + cur.val) = st.mark cur := congrFun hmk4 cur
  -- Step 4: clear `par[cur]`, load `mark[cur]`, and stop at the branch on it.
  wram_exec -split [hfit, hbr4.regs_parBase, hbr4.regs_markBase, hbr4.regs_zeroP, hx4_z, hmk4_cur]
  have hnm_le : st.numMarked ≤ n := hnm ▸ markedCount_le_n st
  let nm' := if st.mark cur = 0 then st.numMarked else st.numMarked - 1
  -- Step 5: clear `mark[cur]`, and decrement `numMarkedReg` if it was set.
  refine WP.cut (fun y t => t ≤ 3 ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x4.mem y.mem ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 → r ≠ numMarkedReg →
        y.regs r = x.regs r) ∧
      RawState.ofData n base y =
        { RawState.ofData n base x4 with
          par := Function.update st.par cur 0
          mark := Function.update st.mark cur 0
          numMarked := nm' }) ?_ ?_
  · by_cases hmk0 : st.mark cur = 0
    · wram_exec [hfit, hbr4.regs_zeroP, hmk0]
      refine ⟨by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr4],
        Modifies.block_iff.2 fun a ha => by have := hfp a ha; wram_simp,
        fun r h0 h1 h2 h3 h4 _ => by wram_simp [hx4_reg r h0 h1 h2 h3 h4], ?_⟩
      wram_simp [ofData_write_mark, ofData_write_par, ofData_set_scratch, hp4, hmk4, hnm4, nm',
        hmk0]
    · have hnm_pos : 1 ≤ st.numMarked := by
        have hmem_ms : cur ∈ markedSet st := by
          simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hin_cur, hmk0⟩
        have hpos : 0 < markedCount st := Finset.card_pos.mpr ⟨cur, hmem_ms⟩
        omega
      have hx4_nm : x4.regs numMarkedReg = st.numMarked :=
        hx4_reg numMarkedReg (by decide) (by decide) (by decide) (by decide) (by decide)
      wram_exec [hfit, hbr4.regs_zeroP, hbr4.regs_oneP, hx4_nm, hmk0]
      refine ⟨by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr4],
        Modifies.block_iff.2 fun a ha => by have := hfp a ha; wram_simp,
        fun r h0 h1 h2 h3 h4 hnm => by wram_simp [hx4_reg r h0 h1 h2 h3 h4], ?_⟩
      wram_simp [ofData_set_numMarked, ofData_write_mark, ofData_write_par, ofData_set_scratch,
        hp4, hmk4, nm', hmk0]
  rintro x7 t7 ⟨ht7, hbr7, hmod7, hx7_reg, hst7⟩
  have hx7_nr : x7.regs numRootsReg = st.numRoots :=
    hx7_reg numRootsReg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Step 6: increment `numRootsReg`.
  wram_exec [hfit, hbr7.regs_oneP, hx7_nr]
  refine ⟨by wram_simp [BaseRegs.set_iff, hbr7],
    modifies_block_trans (modifies_block_trans hmod2 hmod4) hmod7,
    fun r h0 h1 h2 h3 h4 hnm_ne hnr_ne => by wram_simp [hx7_reg r h0 h1 h2 h3 h4 hnm_ne], ?_⟩
  set y := x7.set numRootsReg (st.numRoots + 1) with hy_def
  have hsty : RawState.ofData n base y =
      { RawState.ofData n base x4 with
        par := Function.update st.par cur 0
        mark := Function.update st.mark cur 0
        numMarked := nm'
        numRoots := st.numRoots + 1 } := by
    simp only [y, ofData_set_numRoots, hst7]
  -- The machine state after the cut is `cutState`.
  have hnm' : nm' = st.numMarked - st.mark cur := by
    by_cases hmk0 : st.mark cur = 0
    · simp only [nm', hmk0, ↓reduceIte, Nat.sub_zero]
    · simp only [nm', hmk0, ↓reduceIte]
      have : st.mark cur = 1 := by omega
      rw [this]
  have hcs : RawState.ofData n base y = cutState st cur p m r' left₁ right₁ child₁ := by
    rw [hsty, hst4, hst2, hnm']
    rfl
  have hx7_nm : x7.regs numMarkedReg = nm' := congrArg RawState.numMarked hst7
  have hpot : (st.mark cur ≠ 0 → potential y + unitCredit = potential x) ∧
      (st.mark cur = 0 → potential y = potential x + unitCredit) := by
    have hy_nr : y.regs numRootsReg = st.numRoots + 1 := by wram_simp [hy_def]
    have hy_nm : y.regs numMarkedReg = nm' := by wram_simp [hy_def, hx7_nm]
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
  rw [hcs]
  exact ⟨hpot, cutsNode_cutState hdp_pos hdp2 hcirc_r hroots_par0 hpar_cur hunlink hr'⟩

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
  have hfit := hbr.fits_of_le hb
  set st := RawState.ofData n base x with hst_def
  have := v.isLt
  have := m.isLt
  have hmin' : x.regs minRootReg = m.val + 1 := hmin
  have hkm : x.mem (base + m.val) = st.key m := rfl
  refine WP.exists_execWithin (WP.bounded hb ?_)
  unfold decreaseKeyTail
  wram_exec [hfit, hbr.regs_oneP, hbr.regs_baseReg, hmin', hkm]
  refine WP.of_execWithin (prioLTFlag_exec (n := n) (base := base)
    (by wram_simp [BaseRegs.set_iff, hbr]) argV argK s1 s2 s3) ?_
  have hlt_iff : IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m) ↔
      k < st.key m ∨ k = st.key m ∧ v.val < m.val := by
    rw [← hkv]; rfl
  by_cases hlt : IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m)
  · wram_exec [hfit, hv_reg, hk_reg, hbr.regs_zeroP, hbr.regs_oneP, hlt_iff.mp hlt]
    refine fun hby => ⟨by omega, hby, by wram_simp [BaseRegs.set_iff, hbr], rfl, ?_, ?_⟩
    · simp only [potential]; wram_simp
    · simp only [ofData_set_minRoot, ofData_set_scratch _ (by decide : 17 ≤ s3.val),
        ofData_set_scratch _ (by decide : 17 ≤ s2.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val),
        ofData_set_scratch _ (by decide : 17 ≤ s1.val), ← hst_def, hlt, ↓reduceIte]
  · wram_exec [hfit, hv_reg, hk_reg, hbr.regs_zeroP, hbr.regs_oneP, hlt_iff.not.mp hlt]
    refine fun hby => ⟨by omega, hby, by wram_simp [BaseRegs.set_iff, hbr], rfl, ?_, ?_⟩
    · simp only [potential]; wram_simp
    · simp only [ofData_set_scratch _ (by decide : 17 ≤ s0.val),
        ofData_set_scratch _ (by decide : 17 ≤ s3.val),
        ofData_set_scratch _ (by decide : 17 ≤ s2.val),
        ofData_set_scratch _ (by decide : 17 ≤ s1.val), ← hst_def, hlt, ↓reduceIte, ← hmin]

/-- `decreaseKeyCode` lowers `key[v]` to `k ≤ k₀` (`s v = some k₀`), performs cascading cuts when
parent heap order is violated, updates `minRootReg`, and restores `FibInv` in amortized time
`t + potential y ≤ 330 + potential x`. The forest reasoning is the record heap's: the machine writes
the new key first, so the forest is read with the old keys (`{ st with key := st₀.key }`) as
`Cascading`, each cut is `CutsNode.cascading`, the cascade ends with `Cascading.clear_root` or
`Cascading.mark`, and `Cascading.lowerRootKey` or `FibRawInv.lowerKey_noCut` stores the key. -/
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
  have hfit := hbr.fits_of_le hb
  set st₀ := RawState.ofData n base x with hst₀_def
  -- The record heap's view: `Cascading` from `v`, with nothing pending.
  obtain ⟨m, ts₀, hc₀⟩ := cascading_of_fibRawInv (v := v) hraw (by simp [hsv₀])
  have hv_in_fn₀ : v ∈ forestNodes ts₀ := (hc₀.dom v).mpr (by simp [hsv₀])
  let s' := Function.update s v (some k)
  obtain ⟨T_rv, hTrv_mem, hv_in_Trv⟩ := mem_forestNodes_iff.mp hv_in_fn₀
  have hv_lt := v.isLt
  have hfp (a : ℕ) (ha : a < base ∨ base + space n ≤ a) : a < base ∨ base + 9 * n + 1 ≤ a := by
    unfold space at ha; omega
  have hfit_k : Fits w k := hk_reg ▸ hb.1 argK
  have hfit_par : Fits w (st₀.par v) := hb.2 _
  have hpar_v : x.mem (base + n + v.val) = st₀.par v := rfl
  unfold decreaseKeyCode
  -- Step 1: write `key[v] ← k`, load `par[v]`, and stop at the branch on it.
  wram_exec -split [hfit, hbr.regs_baseReg, hbr.regs_parBase, hv_reg, hk_reg, hpar_v]
  by_cases hpv0 : st₀.par v = 0
  · -- Case A: `v` is already a root (`T_rv.root = v`)
    have hv_eq_root : v = T_rv.root :=
      ((hc₀.valid T_rv hTrv_mem).par_eq_zero_iff_root hv_in_Trv).mp hpv0
    refine WP.cut (fun y t => t ≤ 3 ∧ y.Bounded w ∧ BaseRegs n base y ∧ y.regs argV = v.val ∧
        y.regs argK = k ∧ Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
        RawState.ofData n base y = { st₀ with key := Function.update st₀.key v k } ∧
        potential y = potential x)
      (WP.bounded (by wram_bounded <;> exact hfit _ (by omega)) ?_) ?_
    · wram_exec [hbr.regs_zeroP, hpv0]
      intro hb3
      exact ⟨by omega, hb3, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
        by wram_simp [hv_reg], by wram_simp [hk_reg],
        Modifies.block_iff.2 fun a ha => by have := hfp a ha; wram_simp,
        by wram_simp [ofData_write_key, ofData_set_scratch, ← hst₀_def],
        by simp only [potential]; wram_simp⟩
    rintro x3 t3 ⟨ht3, hb3, hbr3, hx3_v, hx3_k, hmod3, hst3, hpot3⟩
    obtain ⟨y, he_tail, hby, hbry, hmemy, hpoty, hsty⟩ :=
      decreaseKeyTail_exec hb3 hbr3 hx3_v hx3_k (by rw [hst3]; exact hc₀.minRoot)
        (by rw [hst3]; exact Function.update_self v k st₀.key)
    refine WP.of_execWithin he_tail ⟨⟨hby, hbry, ?_⟩, hmemy ▸ hmod3, by omega⟩
    dsimp only at hsty
    have hcut_inv3 : CutInv n K_max s' (RawState.ofData n base x3) v m none := by
      rw [hst3]
      exact hc₀.lowerRootKey ⟨T_rv, hTrv_mem, hv_eq_root.symm⟩ hsv₀ hkle₀ hk_max
    have hraw_y : FibRawInv n K_max s' (RawState.ofData n base y) := by
      refine hcut_inv3.to_fibRawInv ?_ ?_
      · rw [hsty]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · by_cases hlt : IndexedMinPQ.PrioLT (v, (RawState.ofData n base x3).key v)
            (m, (RawState.ofData n base x3).key m)
        · exact Or.inl ⟨hlt, by rw [hsty]; simp only [hlt, ↓reduceIte]⟩
        · exact Or.inr ⟨hlt, by rw [hsty]; simp only [hlt, ↓reduceIte]⟩
    exact hraw_y
  · -- Case B: `st₀.par v ≠ 0`, so `v` has a parent `p₀ : Fin n` with `st₀.par v = p₀.val + 1`
    obtain ⟨T, hT, hv_desc⟩ := hc₀.desc_of_par hv_in_fn₀ hpv0
    obtain ⟨p₀, -, hpv_eq⟩ := (hc₀.valid T hT).1.par_of_mem_children v hv_desc
    have hp₀_lt := p₀.isLt
    have hp₀_ne_v : p₀ ≠ v := fun heq => (hc₀.valid T hT).1.par_ne_self
      (forestNodes_nodup_tree hc₀.nodup hT) hv_desc (heq ▸ hpv_eq)
    have hp₀_ne_v' : p₀.val ≠ v.val := fun e => hp₀_ne_v (Fin.ext e)
    have hkey_p₀ : x.mem (base + p₀.val) = st₀.key p₀ := rfl
    have hviol_iff : IndexedMinPQ.PrioLT (v, k) (p₀, st₀.key p₀) ↔
        k < st₀.key p₀ ∨ k = st₀.key p₀ ∧ v.val < p₀.val := Iff.rfl
    by_cases hviol : IndexedMinPQ.PrioLT (v, k) (p₀, st₀.key p₀)
    · -- Case B2: parent heap order violated (`PrioLT (v, k) (p₀, st₀.key p₀)`) → cut + cascade!
      refine WP.cut (fun y t => y.Bounded w ∧ BaseRegs n base y ∧ y.regs argV = v.val ∧
          y.regs argK = k ∧ Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
          (RawState.ofData n base y).minRoot = m.val + 1 ∧
          (RawState.ofData n base y).key = Function.update st₀.key v k ∧
          CutInv n K_max s' { RawState.ofData n base y with key := Function.update st₀.key v k } v
            m none ∧
          t + potential y ≤ 314 + potential x) ?_ ?_
      · -- `pReg ← par[v] - 1`, compare with `key[p₀]`, and cut `v` from `p₀`.
        wram_exec [hfit, hbr.regs_baseReg, hbr.regs_zeroP, hbr.regs_oneP, hpv_eq, hkey_p₀]
        refine WP.of_execWithin (prioLTFlag_exec (n := n) (base := base)
          (by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr]) argV argK pReg s2 s3) ?_
        wram_exec [hv_reg, hk_reg, hbr.regs_zeroP, hviol_iff.mp hviol]
        refine WP.name fun x6 hx6 => ?_
        have hb6 : x6.Bounded w := by
          rw [hx6]
          wram_bounded <;> first | exact hfit _ (by omega) | (split <;> exact hfit _ (by omega))
        have hbr6 : BaseRegs n base x6 := by
          rw [hx6]; wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr]
        have hst6 :
            RawState.ofData n base x6 = { st₀ with key := Function.update st₀.key v k } := by
          rw [hx6]; wram_simp [ofData_write_key, ofData_set_scratch, ← hst₀_def]
        have hpot6 : potential x6 = potential x := by rw [hx6]; simp only [potential]; wram_simp
        have hmod6 : Modifies (Block.mk base (space n)).footprint x.mem x6.mem :=
          Modifies.block_iff.2 fun a ha => by have := hfp a ha; rw [hx6]; wram_simp
        have hx6_z : x6.regs zReg = v.val := by rw [hx6]; wram_simp [hv_reg]
        have hx6_p : x6.regs pReg = p₀.val := by rw [hx6]; wram_simp
        have hx6_v : x6.regs argV = v.val := by rw [hx6]; wram_simp [hv_reg]
        have hx6_k : x6.regs argK = k := by rw [hx6]; wram_simp [hk_reg]
        -- The first cut is `CutsNode`; on the old keys it keeps the forest `Cascading`.
        obtain ⟨rtail, hcirc, hperm⟩ := hc₀.roots
        obtain ⟨hdp, hdp2, hdp_le, hroots0, hnr, -⟩ := hc₀.cut_pre hperm hv_in_fn₀ hpv_eq
        obtain ⟨-, -, -, hin_v, hmk_v, -⟩ := exists_parent_info (hc₀.valid T hT).1 hv_desc hpv_eq
        obtain ⟨x7, he_cut0, hbr7, hmod7, hx7_reg, hpot_cut0, hcut0⟩ :=
          cutNodeCode_raw hb6 hbr6 hx6_z hx6_p (by rw [hst6]; exact hdp)
            (by rw [hst6]; exact hdp_le) (by rw [hst6]; exact hdp2)
            (by rw [hst6]; exact hc₀.minRoot) (by rw [hst6]; exact hcirc)
            (by rw [hst6]; exact hroots0) (by rw [hst6]; exact hpv_eq)
            (by rw [hst6]; exact hin_v) (by rw [hst6]; exact hmk_v)
            (by rw [hst6]; exact hc₀.numMarked) (by rw [hst6]; exact hnr)
        have hb7 : x7.Bounded w := he_cut0.bounded hb6
        have hcut0' :
            CutsNode st₀ v p₀ m rtail { RawState.ofData n base x7 with key := st₀.key } := by
          have h := hcut0.withKey st₀.key
          rw [hst6] at h
          exact h
        have hv_ne : ∀ T ∈ ts₀, v ∈ T.nodes → T.root ≠ v := fun T hT _ e =>
          hpv0 (e ▸ (hc₀.valid T hT).2.1)
        obtain ⟨ts₁, hc₁, hv₁, hpv₁, hp₁⟩ :=
          hcut0'.cascading hc₀ hperm (Or.inl rfl) (Or.inl rfl) hv_ne hv_in_fn₀ hpv_eq
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
        refine WP.of_execWithin he_cut0 ?_
        wram_exec [hx7_p]
        refine WP.name fun x8 hx8 => ?_
        have hb8 : x8.Bounded w := by rw [hx8]; wram_bounded; exact hfit _ (by omega)
        have hbr8 : BaseRegs n base x8 := by rw [hx8]; wram_simp [BaseRegs.set_iff, hbr7]
        have hst8 : RawState.ofData n base x8 = RawState.ofData n base x7 := by
          rw [hx8]; wram_simp [ofData_set_scratch]
        have hpot8 : potential x8 = potential x7 := by rw [hx8]; simp only [potential]; wram_simp
        have hx8_z : x8.regs zReg = p₀.val := by rw [hx8]; wram_simp
        have hx8_v : x8.regs argV = v.val := by rw [hx8]; wram_simp [hx7_v]
        have hx8_k : x8.regs argK = k := by rw [hx8]; wram_simp [hx7_k]
        have hmod8 : Modifies (Block.mk base (space n)).footprint x.mem x8.mem := by
          rw [hx8]; exact modifies_block_trans hmod6 hmod7
        obtain ⟨x9, he_cg0, hbr9, hst9, hmem9, hx9_ic, hx9_reg⟩ := evalCascGuard_exec hb8 hbr8 hx8_z
        have hb9 : x9.Bounded w := he_cg0.bounded hb8
        have hpot9 : potential x9 = potential x7 :=
          (potential_supported fun i hi =>
            hx9_reg i (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)
              (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)).trans hpot8
        refine WP.of_execWithin he_cg0 ?_
        have hmod9 : Modifies (Block.mk base (space n)).footprint x.mem x9.mem := hmem9 ▸ hmod8
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
          (RawState.ofData n base a).key = Function.update st₀.key v k ∧
          ∃ (cur : Fin n) (ts_c : List (FHTree n)),
            a.regs zReg = cur.val ∧
            Cascading n K_max s { RawState.ofData n base a with key := st₀.key } v m (some cur)
              ts_c ∧
            (∃ T ∈ ts_c, T.root = v) ∧ (∀ T ∈ ts_c, cur ∈ T.nodes → T.root ≠ v) ∧
            cur ∈ forestNodes ts_c ∧
            a.regs iterCur =
              if (RawState.ofData n base a).par cur ≠ 0 ∧ (RawState.ofData n base a).mark cur ≠ 0
              then 1 else 0
        have hx9_inv : loopInv x9 := by
          have h9_v : x9.regs argV = v.val :=
            (hx9_reg argV (by decide) (by decide) (by decide) (by decide)).trans hx8_v
          have h9_k : x9.regs argK = k :=
            (hx9_reg argK (by decide) (by decide) (by decide) (by decide)).trans hx8_k
          have h9_z : x9.regs zReg = p₀.val :=
            (hx9_reg zReg (by decide) (by decide) (by decide) (by decide)).trans hx8_z
          have hst97 : RawState.ofData n base x9 = RawState.ofData n base x7 := hst9.trans hst8
          refine ⟨hb9, hbr9, hmod9, h9_v, h9_k, by rw [hst97, hcut0.key, hst6], p₀, ts₁, h9_z,
            by rw [hst97]; exact hc₁, hv₁, hpv₁, hp₁, ?_⟩
          rw [hst97]
          rw [hst8] at hx9_ic
          exact hx9_ic
        have hbody : ∀ a, loopInv a → (Cond.lt zeroP iterCur).Holds a →
            ∃ y T, ExecWithin w loopBody a y T ∧ loopInv y ∧ T + 2 + potential y ≤ potential a := by
          intro a ha hc_a
          rcases ha with ⟨hba, hbra, hmoda, ha_v, ha_k, ha_key, cur, ts_c, ha_z, hc, hTv_c,
            hcur_ne_v, hcur_fn, ha_ic⟩
          set st_a := RawState.ofData n base a with hst_a_def
          have ha_z0 : a.regs zeroP = 0 := hbra.regs_zeroP
          have hcond_true : st_a.par cur ≠ 0 ∧ st_a.mark cur ≠ 0 := by
            rw [Cond.Holds, ha_z0, ha_ic] at hc_a
            by_contra hnot
            simp only [hnot, ↓reduceIte, lt_self_iff_false] at hc_a
          -- The cut of `cur` is `CutsNode`, and `CutsNode.cascading` on the old keys.
          obtain ⟨T_ci, hTci, hdesc⟩ := hc.desc_of_par hcur_fn hcond_true.1
          obtain ⟨p_c, -, hpar_cur_c⟩ := (hc.valid T_ci hTci).1.par_of_mem_children cur hdesc
          obtain ⟨-, -, -, hin_c, hmk_c, -⟩ :=
            exists_parent_info (hc.valid T_ci hTci).1 hdesc hpar_cur_c
          obtain ⟨rtail_c, hcirc_c, hperm_c⟩ := hc.roots
          obtain ⟨hdp, hdp2, hdp_le, hroots0, hnr, -⟩ := hc.cut_pre hperm_c hcur_fn hpar_cur_c
          have hcur_lt_c := cur.isLt
          have hpc_lt := p_c.isLt
          have hpar_c' : a.mem (base + n + cur.val) = p_c.val + 1 := hpar_cur_c
          simp only [loopBody]
          -- `s0 ← parBase + zReg; s1 ← *s0; pReg ← s1 - oneP`, then cut `cur` from `p_c`.
          wram_exec [hfit, hbra.regs_parBase, hbra.regs_oneP, ha_z, hpar_c']
          refine WP.name fun a3 ha3 => ?_
          have hb_a3 : a3.Bounded w := by rw [ha3]; wram_bounded <;> exact hfit _ (by omega)
          have hbr_a3 : BaseRegs n base a3 := by rw [ha3]; wram_simp [BaseRegs.set_iff, hbra]
          have hst_a3 : RawState.ofData n base a3 = st_a := by
            rw [ha3]; wram_simp [ofData_set_scratch, ← hst_a_def]
          have hpot_a3 : potential a3 = potential a := by
            rw [ha3]; simp only [potential]; wram_simp
          have hmem_a3 : a3.mem = a.mem := by rw [ha3]; rfl
          have ha3_z : a3.regs zReg = cur.val := by rw [ha3]; wram_simp [ha_z]
          have ha3_p : a3.regs pReg = p_c.val := by rw [ha3]; wram_simp
          have ha3_v : a3.regs argV = v.val := by rw [ha3]; wram_simp [ha_v]
          have ha3_k : a3.regs argK = k := by rw [ha3]; wram_simp [ha_k]
          obtain ⟨a4, b4, hbr_a4, hmod_a4, ha4_reg, hpot_a4, hcut⟩ :=
            cutNodeCode_raw hb_a3 hbr_a3 ha3_z ha3_p (by rw [hst_a3]; exact hdp)
              (by rw [hst_a3]; exact hdp_le) (by rw [hst_a3]; exact hdp2)
              (by rw [hst_a3]; exact hc.minRoot) (by rw [hst_a3]; exact hcirc_c)
              (by rw [hst_a3]; exact hroots0) (by rw [hst_a3]; exact hpar_cur_c)
              (by rw [hst_a3]; exact hin_c) (by rw [hst_a3]; exact hmk_c)
              (by rw [hst_a3]; exact hc.numMarked) (by rw [hst_a3]; exact hnr)
          have hb_a4 : a4.Bounded w := b4.bounded hb_a3
          rw [hst_a3] at hcut
          obtain ⟨ts_n, hc_n, hv_n, hpv_n, hp_n⟩ := (hcut.withKey st₀.key).cascading hc hperm_c
            (Or.inr rfl) (Or.inr hTv_c) hcur_ne_v hcur_fn hpar_cur_c
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
          refine WP.of_execWithin b4 ?_
          -- `zReg ← pReg`, then the guard of the next iteration.
          wram_exec [ha4_p]
          refine WP.name fun a5 ha5 => ?_
          have hb_a5 : a5.Bounded w := by rw [ha5]; wram_bounded; exact hfit _ (by omega)
          have hbr_a5 : BaseRegs n base a5 := by rw [ha5]; wram_simp [BaseRegs.set_iff, hbr_a4]
          have hst_a5 : RawState.ofData n base a5 = RawState.ofData n base a4 := by
            rw [ha5]; wram_simp [ofData_set_scratch]
          have hpot_a5 : potential a5 = potential a4 := by
            rw [ha5]; simp only [potential]; wram_simp
          have hmem_a5 : a5.mem = a4.mem := by rw [ha5]; rfl
          have ha5_z : a5.regs zReg = p_c.val := by rw [ha5]; wram_simp
          have ha5_v : a5.regs argV = v.val := by rw [ha5]; wram_simp [ha4_v]
          have ha5_k : a5.regs argK = k := by rw [ha5]; wram_simp [ha4_k]
          obtain ⟨a6, b6, hbr_a6, hst_a6, hmem_a6, ha6_ic, ha6_reg⟩ :=
            evalCascGuard_exec hb_a5 hbr_a5 ha5_z
          refine WP.of_execWithin b6 ?_
          have hpot_a6 : potential a6 = potential a4 :=
            (potential_supported fun i hi =>
              ha6_reg i (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)
                (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)).trans hpot_a5
          have ha6_v : a6.regs argV = v.val :=
            (ha6_reg argV (by decide) (by decide) (by decide) (by decide)).trans ha5_v
          have ha6_k : a6.regs argK = k :=
            (ha6_reg argK (by decide) (by decide) (by decide) (by decide)).trans ha5_k
          have ha6_z : a6.regs zReg = p_c.val :=
            (ha6_reg zReg (by decide) (by decide) (by decide) (by decide)).trans ha5_z
          have hst64 : RawState.ofData n base a6 = RawState.ofData n base a4 :=
            hst_a6.trans hst_a5
          refine ⟨⟨b6.bounded hb_a5, hbr_a6,
            hmem_a6 ▸ hmem_a5 ▸ modifies_block_trans hmoda (hmem_a3 ▸ hmod_a4),
            ha6_v, ha6_k, by rw [hst64, hcut.key]; exact ha_key, p_c, ts_n, ha6_z,
            by rw [hst64]; exact hc_n, hv_n, hpv_n, hp_n, ?_⟩,
            by dsimp only [unitCredit] at hpot_drop ⊢; omega⟩
          rw [hst64]
          rw [hst_a5] at ha6_ic
          exact ha6_ic
        obtain ⟨z_lp, t_lp, he_lp, hz_inv, hz_exit, hpot_lp⟩ :=
          ExecWithin.loop_potential_retain (B := .exact) (w := w)
            (cond := .lt zeroP iterCur) (body := loopBody) loopInv potential hbody hx9_inv
        refine WP.seq (WP.of_execWithin he_lp ?_)
        -- Post-loop mark step, restoring `CutInv ... none`.
        rcases hz_inv with ⟨hb_lp, hbr_lp, hmod_lp, hlp_v, hlp_k, hlp_key, cur_f, ts_f, hlp_z,
          hc_f, hTv_f, -, hcurf_fn, hlp_ic⟩
        set st_lp := RawState.ofData n base z_lp with hst_lp_def
        have hlp_z0 : z_lp.regs zeroP = 0 := hbr_lp.regs_zeroP
        have hlp_o1 : z_lp.regs oneP = 1 := hbr_lp.regs_oneP
        have hlp_pb : z_lp.regs parBase = base + n := hbr_lp.regs_parBase
        have hlp_mb : z_lp.regs markBase = base + 6 * n := hbr_lp.regs_markBase
        have hfit_lp := hbr_lp.fits_stop hb_lp
        have hcurf_lt := cur_f.isLt
        have hnot_both : ¬(st_lp.par cur_f ≠ 0 ∧ st_lp.mark cur_f ≠ 0) := by
          intro hboth
          apply hz_exit
          simp only [Cond.Holds, hlp_z0, hlp_ic, hboth.1, hboth.2, ne_eq, not_false_eq_true,
            and_self, ↓reduceIte]
          exact Nat.zero_lt_one
        have hkv_lp : st_lp.key v = k := by rw [hlp_key, Function.update_self]
        have hlp_par : z_lp.mem (base + n + cur_f.val) = st_lp.par cur_f := rfl
        have hpot9 : potential x9 = potential x7 :=
          (potential_supported fun i hi =>
            hx9_reg i (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)
              (fun e => by subst e; cases hi) (fun e => by subst e; cases hi)).trans hpot8
        refine WP.bounded hb_lp ?_
        by_cases hpf0 : st_lp.par cur_f = 0
        · wram_exec [hfit, hbr_lp.regs_parBase, hbr_lp.regs_zeroP, hlp_z, hlp_par, hpf0]
          intro hb_post
          refine ⟨hb_post, by wram_simp [BaseRegs.set_iff, hbr_lp], by wram_simp [hlp_v],
            by wram_simp [hlp_k], hmod_lp, ?_, ?_, ?_, ?_⟩
          · wram_simp [ofData_set_scratch, ← hst_lp_def]; exact hc_f.minRoot
          · wram_simp [ofData_set_scratch, ← hst_lp_def]; exact hlp_key
          · -- `Cascading.clear_root`, then `Cascading.lowerRootKey`.
            wram_simp [ofData_set_scratch, ← hst_lp_def]
            exact (hc_f.clear_root hcurf_fn hpf0).lowerRootKey hTv_f hsv₀ hkle₀ hk_max
          · wram_simp [potential_set_scratch]
            dsimp only [unitCredit] at hpot7_le
            omega
        · have hmf0 : st_lp.mark cur_f = 0 := by
            by_contra hmf_ne
            exact hnot_both ⟨hpf0, hmf_ne⟩
          have hin_curf : st_lp.inHeap cur_f ≠ 0 :=
            (hc_f.inHeap cur_f).1.mpr ((hc_f.dom cur_f).mp hcurf_fn)
          have hnm_f : st_lp.numMarked = markedCount st_lp := hc_f.numMarked
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
          have hlp_nm : z_lp.regs numMarkedReg = st_lp.numMarked := rfl
          wram_exec [hfit, hbr_lp.regs_parBase, hbr_lp.regs_markBase, hbr_lp.regs_zeroP,
            hbr_lp.regs_oneP, hlp_z, hlp_par, hlp_nm, hpf0]
          intro hb_post
          have hcurf_mark := owns_arr_addr (base := base) (k := 6) (by decide) hcurf_lt
          refine ⟨hb_post, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr_lp],
            by wram_simp [hlp_v], by wram_simp [hlp_k],
            Modifies.block_iff.2 fun a ha => by
              have := hfp a ha
              rw [← Modifies.block_iff.1 hmod_lp a ha]
              unfold space at hcurf_mark
              wram_simp, ?_, ?_, ?_, ?_⟩
          · wram_simp [ofData_set_numMarked, ofData_write_mark, ofData_set_scratch, ← hst_lp_def]
            exact hc_f.minRoot
          · wram_simp [ofData_set_numMarked, ofData_write_mark, ofData_set_scratch, ← hst_lp_def]
            exact hlp_key
          · -- `Cascading.mark`, then `Cascading.lowerRootKey`.
            wram_simp [ofData_set_numMarked, ofData_write_mark, ofData_set_scratch, ← hst_lp_def]
            exact (hc_f.mark hcurf_fn hpf0 hmf0).lowerRootKey hTv_f hsv₀ hkle₀ hk_max
          · have hpot_z : potential z_lp =
                unitCredit * (z_lp.regs numRootsReg + 2 * st_lp.numMarked) := rfl
            wram_simp [potential_set_numMarked, potential_set_scratch]
            dsimp only [unitCredit] at hpot7_le hpot_z ⊢
            omega
      rintro x_post t_post ⟨hb_post, hbr_post, hp_v, hp_k, hmod_post, hp_min, hp_key, hcut_post,
        hpot_post⟩
      obtain ⟨y, he_tail, hby, hbry, hmemy, hpoty, hsty⟩ :=
        decreaseKeyTail_exec hb_post hbr_post hp_v hp_k hp_min
          (by rw [hp_key, Function.update_self])
      dsimp only at hsty
      have hraw_y : FibRawInv n K_max s' (RawState.ofData n base y) := by
        refine hcut_post.to_fibRawInv ?_ ?_
        · rw [hsty]; exact ⟨hp_key, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · by_cases hlt : IndexedMinPQ.PrioLT (v, (RawState.ofData n base x_post).key v)
              (m, (RawState.ofData n base x_post).key m)
          · exact Or.inl ⟨by rw [← hp_key]; exact hlt, by rw [hsty]; simp only [hlt, ↓reduceIte]⟩
          · exact Or.inr ⟨by rw [← hp_key]; exact hlt, by rw [hsty]; simp only [hlt, ↓reduceIte]⟩
      exact WP.of_execWithin he_tail ⟨⟨hby, hbry, hraw_y⟩, hmemy ▸ hmod_post, by omega⟩
    · -- Case B1: `¬PrioLT (v, k) (p₀, st₀.key p₀)` → no cuts needed, `minRoot` unchanged!
      refine WP.cut (fun y t => t ≤ 13 ∧ y.Bounded w ∧ BaseRegs n base y ∧ y.regs argV = v.val ∧
          y.regs argK = k ∧ Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
          RawState.ofData n base y = { st₀ with key := Function.update st₀.key v k } ∧
          potential y = potential x)
        (WP.bounded (by wram_bounded <;> exact hfit _ (by omega)) ?_) ?_
      · wram_exec [hfit, hbr.regs_baseReg, hbr.regs_zeroP, hbr.regs_oneP, hpv_eq, hkey_p₀]
        refine WP.of_execWithin (prioLTFlag_exec (n := n) (base := base)
          (by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr]) argV argK pReg s2 s3) ?_
        wram_exec [hv_reg, hk_reg, hbr.regs_zeroP, hviol_iff.not.mp hviol]
        intro hb6
        exact ⟨by omega, hb6, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
          by wram_simp [hv_reg], by wram_simp [hk_reg],
          Modifies.block_iff.2 fun a ha => by have := hfp a ha; wram_simp,
          by wram_simp [ofData_write_key, ofData_set_scratch, ← hst₀_def],
          by simp only [potential]; wram_simp⟩
      rintro x6 t6 ⟨ht6, hb6, hbr6, hx6_v, hx6_k, hmod6, hst6, hpot6⟩
      obtain ⟨y, he_tail, hby, hbry, hmemy, hpoty, hsty⟩ :=
        decreaseKeyTail_exec hb6 hbr6 hx6_v hx6_k (by rw [hst6]; exact hc₀.minRoot)
          (by rw [hst6]; exact Function.update_self v k st₀.key)
      dsimp only at hsty
      refine WP.of_execWithin he_tail ⟨⟨hby, hbry, ?_⟩, hmemy ▸ hmod6, by omega⟩
      -- `FibRawInv.lowerKey_noCut`: the heap stays valid, and `v` does not precede `m`.
      obtain ⟨hinv, hnot⟩ := FibRawInv.lowerKey_noCut hraw hsv₀ hkle₀ hk_max hpv_eq hviol
      have hnlt_m : ¬IndexedMinPQ.PrioLT (v, (RawState.ofData n base x6).key v)
          (m, (RawState.ofData n base x6).key m) := by
        rw [hst6]
        dsimp only
        rw [Function.update_self]
        exact hnot m hc₀.minRoot
      have hsty_eq :
          RawState.ofData n base y = { st₀ with key := Function.update st₀.key v k } := by
        rw [hsty]
        simp only [hnlt_m, ↓reduceIte]
        rw [hst6, ← hc₀.minRoot]
      rw [hsty_eq]
      exact hinv

end Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
