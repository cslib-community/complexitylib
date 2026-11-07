/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.BasicOps
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Consolidation

/-!
# Degree-indexed root consolidation and `extractMin` for a Fibonacci heap

This file proves the correctness, memory-safety, and `O(log |dom s| + 1)` amortized instruction
bound of `scatterRootCode` and `extractMinCode` in the current number of stored elements
`sz = (IndexedMinPQ.dom s).card` [Fredman and Tarjan][FredmanTarjan1987]
[Cormen et al., Section 19.2][CLRS2009].

The proofs step the machine code; the forest reasoning is that of the record heap
(`Cslib.DataStructure.PriorityQueue.FibonacciHeap`, `Consolidation.lean`), applied to the machine
state read as `RawState.ofData n base x`:

* **Root scattering (`scatterRootCode_exec`):** each collision step is `Placing.collide` followed
  by a link, which the machine performs as `LinksAs`; the final store into an empty slot is
  `Placing.place`. The result is `Consolidated`, and the step count satisfies
  `t + 50 * slotTrees'.length ≤ 63 + 50 * slotTrees.length`.
* **Minimum extraction (`extractMinCode_exec`):** `FibRawInv.detach` splits the heap at
  `z = minRoot - 1` (which agrees with `IndexedMinPQ.findMin`). The two scatter loops are driven by
  `Detached.scatterChildren`, `Scattering.unmark`/`step` and `Detached.scatterRoots`, the slot scan
  by `Detached.gathering` and `Gathering.take`, and `Detached.finish` rebuilds `FibRawInv`. The scan
  covers only `0 .. maxDeg`, at most `2 * Nat.log 2 (IndexedMinPQ.dom s).card + 2` slots, so
  `t + potential y ≤ 410 * (Nat.log 2 (IndexedMinPQ.dom s).card + 1) + potential x`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.scatterRootCode_exec`: amortized root
  scattering, as `Consolidated`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.extractMinCode_exec`:
  `O(log |dom s| + 1)` amortized `extractMin` specification in the current number of stored
  elements.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 19.2][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.FibonacciHeap hiding potential
open scoped Cslib.WordRAM

/-! ## Root scattering (`scatterBody_exec` and `scatterRootCode_exec`) -/

private abbrev scatterBody : Code .exact rFib :=
  ram_exact[
    s5 ← s3 - oneP;
    s0 ← consBase + curDReg;
    *s0 ← zeroP;
    s0 ← baseReg + s4;
    s1 ← *s0;
    s0 ← baseReg + s5;
    s2 ← *s0;
    ⟪prioLTFlag s5 s2 s4 s1 s6⟫;
    if zeroP < s6 then [
      s6 ← s4;
      s4 ← s5;
      s5 ← s6
    ] else [
      s0 ← zeroP
    ];
    s1 ← s4 + oneP;
    s0 ← parBase + s5;
    *s0 ← s1;
    s0 ← degBase + s4;
    s1 ← *s0;
    if s1 = zeroP then [
      s0 ← leftBase + s5;
      *s0 ← s5;
      s0 ← rightBase + s5;
      *s0 ← s5;
      s2 ← s5 + oneP;
      s0 ← childBase + s4;
      *s0 ← s2;
      s0 ← degBase + s4;
      *s0 ← oneP
    ] else [
      s0 ← childBase + s4;
      s6 ← *s0;
      s6 ← s6 - oneP;
      ⟪insertIntoNonEmptyList s6 s5⟫;
      s1 ← s1 + oneP;
      s0 ← degBase + s4;
      *s0 ← s1
    ];
    curDReg ← curDReg + oneP;
    s0 ← consBase + curDReg;
    s3 ← *s0
  ]

/-- The collision body writes only its degree counter and inner scratch registers. -/
private theorem scatterBody_preserves :
    ∀ r : Fin rFib, r.val < 34 → scatterBody.Preserves r := by
  decide +kernel


/-- Single collision step of `scatterRootCode`: clears `cons[curD]`, links the tree `T_cur` in
`s4` with the table's tree of the same degree (the one that precedes becomes the parent), and
advances `curD`, in `≤ 43` steps. The forest reasoning is `Placing.collide` and `LinksAs.linked`:
the machine state after the link is `LinksAs` of the state before it. -/
private theorem scatterBody_exec {n sz base w maxDeg curD : ℕ} {a : Data rFib}
    {T_cur : FHTree n} {slotTrees : List (FHTree n)} {z : Fin n}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (hP : Placing sz z (RawState.ofData n base a) T_cur slotTrees maxDeg)
    (hcur_deg : T_cur.deg = curD)
    (ha_s4 : a.regs s4 = T_cur.root.val)
    (ha_curD : a.regs curDReg = curD)
    (ha_s3 : a.regs s3 = (RawState.ofData n base a).cons curD)
    (hcond : (Cond.lt zeroP s3).Holds a) :
    ∃ a' T_next slotTrees',
      ExecWithin w scatterBody a a' 43 ∧
      a'.Bounded w ∧ BaseRegs n base a' ∧
      Modifies (Block.mk base (space n)).footprint a.mem a'.mem ∧
      (∀ r : Fin rFib, r.val < 34 → a'.regs r = a.regs r) ∧
      slotTrees'.length + 1 = slotTrees.length ∧
      T_next.deg = curD + 1 ∧
      a'.regs s4 = T_next.root.val ∧
      a'.regs curDReg = curD + 1 ∧
      a'.regs s3 = (RawState.ofData n base a').cons (curD + 1) ∧
      Placing sz z (RawState.ofData n base a') T_next slotTrees' maxDeg ∧
      ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
        Consolidated sz (RawState.ofData n base a') st' (forestNodes (T_next :: slotTrees'))
          slots' md' →
        Consolidated sz (RawState.ofData n base a) st' (forestNodes (T_cur :: slotTrees))
          slots' md' := by
  set st := RawState.ofData n base a with hst_def
  have hfit_stop := hbr.fits_stop hb
  have hfit_n1 : Fits w (n + 1) := hfit_stop.of_le (by simp only [space]; omega)
  have hz0 : a.regs zeroP = 0 := hbr.regs_zeroP
  have ho1 : a.regs oneP = 1 := hbr.regs_oneP
  have hbb : a.regs baseReg = base := hbr.regs_baseReg
  have hpb : a.regs parBase = base + n := hbr.regs_parBase
  have hcb : a.regs childBase = base + 2 * n := hbr.regs_childBase
  have hlb : a.regs leftBase = base + 3 * n := hbr.regs_leftBase
  have hrb : a.regs rightBase = base + 4 * n := hbr.regs_rightBase
  have hdb : a.regs degBase = base + 5 * n := hbr.regs_degBase
  have hconsb : a.regs consBase = base + 8 * n := hbr.regs_consBase
  have hdeg_bds := hP.deg_bounds
  rw [hcur_deg] at hdeg_bds
  have hd_le_n : curD ≤ n := by omega
  have hd1_le_n : curD + 1 ≤ n := by omega
  -- `0 < st.cons curD` extracts the colliding slot tree `T_slot = slotTrees[idx]`:
  have hcons_pos : 0 < st.cons curD := by
    rw [Cond.Holds, hz0, ha_s3] at hcond
    exact hcond
  rcases hP.table.lookup hd_le_n with ⟨hc0, _⟩ |
      ⟨idx, hidx, hslot_deg, hcons_eq, hlen_er, hno_other⟩
  · omega
  let T_slot := slotTrees[idx]
  let slotTrees' := slotTrees.eraseIdx idx
  let u4 := T_cur.root
  let u5 := T_slot.root
  have hu4_lt := u4.isLt
  have hu5_lt := u5.isLt
  -- Step 1 (`a → a1`, 3 steps): `s5 ← s3 - oneP; s0 ← consBase + curDReg; *s0 ← zeroP`
  have ho_cons_d := owns_cons_addr (base := base) hd_le_n
  let a1 := ((a.set s5 u5.val).set s0 (base + 8 * n + curD)).write (base + 8 * n + curD) 0
  have e1_1 : ExecWithin w (.op (.exactBin .sub s5 s3 oneP)) a (a.set s5 u5.val) 1 := by
    simpa only [ha_s3, hcons_eq, ho1, Nat.add_sub_cancel] using
      execWithin_exactSub (x := a) (d := s5) (i := s3) (j := oneP)
        (by rw [ha_s3, hcons_eq, ho1]; omega)
        (by rw [ha_s3, hcons_eq, ho1]; exact hfit_n1.of_le (by omega))
  have e1_2 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg)) (a.set s5 u5.val)
      ((a.set s5 u5.val).set s0 (base + 8 * n + curD)) 1 := by
    have hcb1 : (a.set s5 u5.val).regs consBase = base + 8 * n := hconsb
    have hcd1 : (a.set s5 u5.val).regs curDReg = curD := ha_curD
    simpa only [hcb1, hcd1] using
      execWithin_exactAdd (x := a.set s5 u5.val) (d := s0) (i := consBase) (j := curDReg)
        (by rw [hcb1, hcd1]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e1_3 : ExecWithin (B := .exact) w (.op (.store s0 zeroP))
      ((a.set s5 u5.val).set s0 (base + 8 * n + curD)) a1 1 := by
    have hs0_1 : ((a.set s5 u5.val).set s0 (base + 8 * n + curD)).regs s0 =
        base + 8 * n + curD := by simp only [Data.set_regs, Function.update_self]
    have hz_1 : ((a.set s5 u5.val).set s0 (base + 8 * n + curD)).regs zeroP = 0 := hz0
    simpa only [hs0_1, hz_1] using
      (ExecWithin.store (B := .exact) (w := w)
        (x := (a.set s5 u5.val).set s0 (base + 8 * n + curD)) (a := s0) (s := zeroP))
  have hb1 : a1.Bounded w := e1_3.bounded (e1_2.bounded (e1_1.bounded hb))
  have hbr1 : BaseRegs n base a1 :=
    ((hbr.set_non_base (by decide) _).set_non_base (by decide) _).write_eq _ _
  have hmod1 : Modifies (Block.mk base (space n)).footprint a.mem a1.mem :=
    Modifies.write_of_owns ho_cons_d 0
  have hst1 : RawState.ofData n base a1 = { st with cons := Function.update st.cons curD 0 } := by
    simp only [a1, ofData_write_cons hd_le_n, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ s5.val), ← hst_def]
  -- `Placing.collide`: both trees stay valid roots after the slot is cleared.
  obtain ⟨hT_cur1, hT_slot1, hnd_pair, hnext⟩ := hP.collide (st₁ := RawState.ofData n base a1)
    hidx (hslot_deg.trans hcur_deg.symm) (fun R hR => by rw [hcur_deg]; exact hno_other R hR)
    (by rw [hst1, hcur_deg])
  have hu4_ne_u5 : u4 ≠ u5 :=
    (List.nodup_append.mp hnd_pair).2.2 u4 T_cur.root_mem_nodes u5 T_slot.root_mem_nodes
  have hkey1 : (RawState.ofData n base a1).key = st.key := by rw [hst1]
  -- Step 2 (`a1 → a2`, 10 steps): load `key[s4]`, `key[s5]`, and run `prioLTFlag s5 s2 s4 s1 s6`
  let a2_pre := (((a1.set s0 (base + u4.val)).set s1 (st.key u4)).set s0
    (base + u5.val)).set s2 (st.key u5)
  have e2_1 : ExecWithin w (.op (.exactBin .add s0 baseReg s4)) a1
      (a1.set s0 (base + u4.val)) 1 := by
    have hb_1 : a1.regs baseReg = base := hbb
    have hs4_1 : a1.regs s4 = u4.val := ha_s4
    simpa only [hb_1, hs4_1] using
      execWithin_exactAdd (x := a1) (d := s0) (i := baseReg) (j := s4)
        (by rw [hb_1, hs4_1]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e2_2 : ExecWithin (B := .exact) w (.op (.load s1 s0)) (a1.set s0 (base + u4.val))
      ((a1.set s0 (base + u4.val)).set s1 (st.key u4)) 1 := by
    have hm_u4 : a1.mem (base + u4.val) = st.key u4 := by
      have : (RawState.ofData n base a1).key u4 = st.key u4 := by rw [hst1]
      exact this
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_u4] using
      (ExecWithin.load (B := .exact) (w := w) (x := a1.set s0 (base + u4.val)) (d := s1) (a := s0))
  have e2_3 : ExecWithin w (.op (.exactBin .add s0 baseReg s5))
      ((a1.set s0 (base + u4.val)).set s1 (st.key u4))
      (((a1.set s0 (base + u4.val)).set s1 (st.key u4)).set s0 (base + u5.val)) 1 := by
    have hb_2 : ((a1.set s0 (base + u4.val)).set s1 (st.key u4)).regs baseReg = base := hbb
    have hs5_2 : ((a1.set s0 (base + u4.val)).set s1 (st.key u4)).regs s5 = u5.val := by
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : s5 ≠ s1), Function.update_of_ne (by decide : s5 ≠ s0),
        Function.update_self]
    simpa only [hb_2, hs5_2] using
      execWithin_exactAdd (x := (a1.set s0 (base + u4.val)).set s1 (st.key u4))
        (d := s0) (i := baseReg) (j := s5)
        (by rw [hb_2, hs5_2]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e2_4 : ExecWithin (B := .exact) w (.op (.load s2 s0))
      (((a1.set s0 (base + u4.val)).set s1 (st.key u4)).set s0 (base + u5.val)) a2_pre 1 := by
    have hm_u5 : a1.mem (base + u5.val) = st.key u5 := by
      have : (RawState.ofData n base a1).key u5 = st.key u5 := by rw [hst1]
      exact this
    simpa only [a2_pre, Data.set_mem, Data.set_regs, Function.update_self, hm_u5] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := ((a1.set s0 (base + u4.val)).set s1 (st.key u4)).set s0 (base + u5.val))
        (d := s2) (a := s0))
  have hb2_pre : a2_pre.Bounded w := e2_4.bounded (e2_3.bounded (e2_2.bounded (e2_1.bounded hb1)))
  have hbr2_pre : BaseRegs n base a2_pre :=
    (((hbr1.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
      (by decide) _).set_non_base (by decide) _
  have ha2_s4 : a2_pre.regs s4 = u4.val := ha_s4
  have ha2_s5 : a2_pre.regs s5 = u5.val := by
    simp only [a2_pre, a1, Data.set_regs, Data.write_regs,
      Function.update_of_ne (by decide : s5 ≠ s2), Function.update_of_ne (by decide : s5 ≠ s0),
      Function.update_of_ne (by decide : s5 ≠ s1), Function.update_self]
  have ha2_s1 : a2_pre.regs s1 = st.key u4 := by
    simp only [a2_pre, Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s2),
      Function.update_of_ne (by decide : s1 ≠ s0), Function.update_self]
  have ha2_s2 : a2_pre.regs s2 = st.key u5 := by
    simp only [a2_pre, Data.set_regs, Function.update_self]
  have he_plt := prioLTFlag_exec (w := w) hbr2_pre s5 s2 s4 s1 s6
  dsimp only at he_plt
  rw [ha2_s2, ha2_s1, ha2_s5, ha2_s4] at he_plt
  let bflag := if IndexedMinPQ.PrioLT (u5, st.key u5) (u4, st.key u4) then 1 else 0
  let a2 := a2_pre.set s6 bflag
  have e2_5 : ExecWithin w (prioLTFlag s5 s2 s4 s1 s6) a2_pre a2 6 := he_plt
  have hb2 : a2.Bounded w := e2_5.bounded hb2_pre
  have hbr2 : BaseRegs n base a2 := hbr2_pre.set_non_base (by decide) bflag
  have hst2 : RawState.ofData n base a2 = RawState.ofData n base a1 := by
    simp only [a2, a2_pre, ofData_set_scratch _ (by decide : 17 ≤ s6.val),
      ofData_set_scratch _ (by decide : 17 ≤ s2.val),
      ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ s1.val)]
  -- Step 3 (`a2 → a3`, ≤ 4 steps): swap `(s4, s5)` if `PrioLT (u5, key u5) (u4, key u4)`; the
  -- tree `T₁` in `s4` then becomes the parent of the tree `T₂` in `s5`.
  have hswap_step : ∃ (T₁ T₂ : FHTree n) (a3 : Data rFib),
      ExecWithin (B := .exact) w
        (.branch (.lt zeroP s6)
          (.seq (.op (.copy s6 s4)) (.seq (.op (.copy s4 s5)) (.op (.copy s5 s6))))
          (.op (.copy s0 zeroP))) a2 a3 4 ∧
      a3.Bounded w ∧ BaseRegs n base a3 ∧ a3.mem = a1.mem ∧
      RawState.ofData n base a3 = RawState.ofData n base a1 ∧
      ValidRoot (RawState.ofData n base a1) none T₁ ∧ T₁.deg = curD ∧
      (T₁.nodes ++ T₂.nodes).Nodup ∧
      a3.regs s4 = T₁.root.val ∧ a3.regs s5 = T₂.root.val ∧
      ∀ {st₂ : RawState n}, LinksAs (RawState.ofData n base a1) T₁.root T₂.root st₂ →
        Linked (RawState.ofData n base a1) st₂ T_cur T_slot
          (.node T₁.root (T₁.children ++ [T₂])) := by
    have hz_a2 : a2.regs zeroP = 0 := hbr2.regs_zeroP
    have hs4_a2 : a2.regs s4 = u4.val := ha_s4
    have hs5_a2 : a2.regs s5 = u5.val := by
      simp only [a2, Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s6), ha2_s5]
    by_cases hlt54 : IndexedMinPQ.PrioLT (u5, st.key u5) (u4, st.key u4)
    · have hc_sw : (Cond.lt zeroP s6).Holds a2 := by
        rw [Cond.Holds, hz_a2]
        simp only [a2, Data.set_regs, Function.update_self, bflag, hlt54, ↓reduceIte]
        exact Nat.zero_lt_one
      let a3 := ((a2.set s6 u4.val).set s4 u5.val).set s5 u4.val
      have c1 : ExecWithin (B := .exact) w (.op (.copy s6 s4)) a2 (a2.set s6 u4.val) 1 := by
        simpa only [hs4_a2] using
          (ExecWithin.copy (B := .exact) (w := w) (x := a2) (d := s6) (s := s4))
      have c2 : ExecWithin (B := .exact) w (.op (.copy s4 s5)) (a2.set s6 u4.val)
          ((a2.set s6 u4.val).set s4 u5.val) 1 := by
        have hs5_c : (a2.set s6 u4.val).regs s5 = u5.val := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s6), hs5_a2]
        simpa only [hs5_c] using
          (ExecWithin.copy (B := .exact) (w := w) (x := a2.set s6 u4.val) (d := s4) (s := s5))
      have c3 : ExecWithin (B := .exact) w (.op (.copy s5 s6)) ((a2.set s6 u4.val).set s4 u5.val)
          a3 1 := by
        have hs6_c : ((a2.set s6 u4.val).set s4 u5.val).regs s6 = u4.val := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s6 ≠ s4),
            Function.update_self]
        simpa only [hs6_c] using
          (ExecWithin.copy (B := .exact) (w := w)
            (x := (a2.set s6 u4.val).set s4 u5.val) (d := s5) (s := s6))
      have he_sw : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s6)
            (.seq (.op (.copy s6 s4)) (.seq (.op (.copy s4 s5)) (.op (.copy s5 s6))))
            (.op (.copy s0 zeroP))) a2 a3 4 :=
        ExecWithin.branch_pos hc_sw (c1.seq (c2.seq c3))
      refine ⟨T_slot, T_cur, a3, he_sw, he_sw.bounded hb2,
        ((hbr2.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _,
        rfl, ?_, hT_slot1, hslot_deg, List.perm_append_comm.nodup_iff.mp hnd_pair, ?_, ?_,
        fun hl => (LinksAs.linked hT_slot1 hT_cur1 (List.perm_append_comm.nodup_iff.mp hnd_pair)
          (hslot_deg.trans hcur_deg.symm) (by rw [hkey1]; exact hlt54) hl).symm
          (hcur_deg.trans hslot_deg.symm)⟩
      · simp only [a3, ofData_set_scratch _ (by decide : 17 ≤ s5.val),
          ofData_set_scratch _ (by decide : 17 ≤ s4.val),
          ofData_set_scratch _ (by decide : 17 ≤ s6.val), hst2]
      · simp only [a3, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s5),
          Function.update_self, u5]
      · simp only [a3, Data.set_regs, Function.update_self, u4]
    · have hc_sw : ¬(Cond.lt zeroP s6).Holds a2 := by
        rw [Cond.Holds, hz_a2]
        simp only [a2, Data.set_regs, Function.update_self, bflag, hlt54, ↓reduceIte,
          lt_self_iff_false, not_false_eq_true]
      let a3 := a2.set s0 0
      have c0 : ExecWithin (B := .exact) w (.op (.copy s0 zeroP)) a2 a3 1 := by
        simpa only [hz_a2] using
          (ExecWithin.copy (B := .exact) (w := w) (x := a2) (d := s0) (s := zeroP))
      have he_sw : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s6)
            (.seq (.op (.copy s6 s4)) (.seq (.op (.copy s4 s5)) (.op (.copy s5 s6))))
            (.op (.copy s0 zeroP))) a2 a3 4 :=
        (ExecWithin.branch_neg hc_sw c0).mono (by omega)
      have hlt45 : IndexedMinPQ.PrioLT (u4, st.key u4) (u5, st.key u5) :=
        (IndexedMinPQ.prioLT_or_prioLT_of_ne hu4_ne_u5 (st.key u4) (st.key u5)).resolve_right hlt54
      refine ⟨T_cur, T_slot, a3, he_sw, he_sw.bounded hb2, hbr2.set_non_base (by decide) 0,
        rfl, (ofData_set_scratch a2 (by decide : 17 ≤ s0.val) 0).trans hst2,
        hT_cur1, hcur_deg, hnd_pair, ?_, ?_, fun hl => LinksAs.linked hT_cur1 hT_slot1 hnd_pair
          (hcur_deg.trans hslot_deg.symm) (by rw [hkey1]; exact hlt45) hl⟩
      · simp only [a3, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s0), hs4_a2, u4]
      · simp only [a3, Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s0), hs5_a2, u5]
  obtain ⟨T₁, T₂, a3, e3, hb3, hbr3, hmem3, hst3, hT₁, hd₁, hnd12, ha3_s4, ha3_s5,
    hlinked⟩ := hswap_step
  let w1 := T₁.root
  let w2 := T₂.root
  have hw1_lt := w1.isLt
  have hw2_lt := w2.isLt
  -- Step 4 (`a3 → a4`, 5 steps): `par[w2] ← w1 + 1` and `s1 ← deg[w1] = curD`
  have hdeg_w1 : st.deg w1 = curD := by
    have h := ValidSubtree.deg_root hT₁.1
    rw [hst1] at h
    exact h.trans hd₁
  have ho_pw2 : (Block.mk base (space n)).Owns (base + n + w2.val) := by
    have h := owns_arr_addr (base := base) (k := 1) (by decide) hw2_lt
    rw [Nat.one_mul] at h
    exact h
  let a4 := ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
    (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val)).set s1 curD
  have e4_1 : ExecWithin w (.op (.exactBin .add s1 s4 oneP)) a3 (a3.set s1 (w1.val + 1)) 1 := by
    have ho_3 : a3.regs oneP = 1 := hbr3.regs_oneP
    simpa only [ha3_s4, ho_3, w1] using
      execWithin_exactAdd (x := a3) (d := s1) (i := s4) (j := oneP)
        (by rw [ha3_s4, ho_3]; exact hfit_n1.of_le (by omega))
  have e4_2 : ExecWithin w (.op (.exactBin .add s0 parBase s5)) (a3.set s1 (w1.val + 1))
      ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)) 1 := by
    have hp_3 : (a3.set s1 (w1.val + 1)).regs parBase = base + n := hbr3.regs_parBase
    have hs5_3 : (a3.set s1 (w1.val + 1)).regs s5 = w2.val := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s1), ha3_s5, w2]
    simpa only [hp_3, hs5_3] using
      execWithin_exactAdd (x := a3.set s1 (w1.val + 1)) (d := s0) (i := parBase) (j := s5)
        (by rw [hp_3, hs5_3]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e4_3 : ExecWithin (B := .exact) w (.op (.store s0 s1))
      ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val))
      (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)) 1 := by
    have hs0_3 : ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).regs s0 =
        base + n + w2.val := by simp only [Data.set_regs, Function.update_self]
    have hs1_3 : ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).regs s1 = w1.val + 1 := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s0), Function.update_self]
    simpa only [hs0_3, hs1_3] using
      (ExecWithin.store (B := .exact) (w := w)
        (x := (a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)) (a := s0) (s := s1))
  have e4_4 : ExecWithin w (.op (.exactBin .add s0 degBase s4))
      (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1))
      ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val)) 1 := by
    have hd_3 : (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).regs degBase = base + 5 * n := hbr3.regs_degBase
    have hs4_3 : (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).regs s4 = w1.val := by
      simp only [Data.write_regs, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s0),
        Function.update_of_ne (by decide : s4 ≠ s1), ha3_s4, w1]
    simpa only [hd_3, hs4_3] using
      execWithin_exactAdd
        (x := ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
          (base + n + w2.val) (w1.val + 1))
        (d := s0) (i := degBase) (j := s4)
        (by rw [hd_3, hs4_3]; exact hfit_stop.of_le (by simp only [space]; omega))
  have hst4_pre : RawState.ofData n base
      ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val)) =
      { st with
        par := Function.update st.par w2 (w1.val + 1)
        cons := Function.update st.cons curD 0 } := by
    simp only [ofData_set_scratch _ (by decide : 17 ≤ s0.val), ofData_write_par,
      ofData_set_scratch _ (by decide : 17 ≤ s1.val), hst3, hst1]
  have e4_5 : ExecWithin (B := .exact) w (.op (.load s1 s0))
      ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val)) a4 1 := by
    have hm_dw1 : (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).mem (base + 5 * n + w1.val) = curD := by
      have : (RawState.ofData n base
          ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
            (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val))).deg w1 = curD := by
        rw [hst4_pre]; exact hdeg_w1
      exact this
    simpa only [a4, Data.set_mem, Data.set_regs, Function.update_self, hm_dw1] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
          (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val))
        (d := s1) (a := s0))
  have hb4 : a4.Bounded w :=
    e4_5.bounded (e4_4.bounded (e4_3.bounded (e4_2.bounded (e4_1.bounded hb3))))
  have e4 := e4_1.seq <| e4_2.seq <| e4_3.seq <| e4_4.seq e4_5
  have hbr4 : BaseRegs n base a4 :=
    ((((hbr3.set_non_base (by decide) _).set_non_base (by decide) _).write_eq _ _).set_non_base
      (by decide) _).set_non_base (by decide) _
  have hmod4 : Modifies (Block.mk base (space n)).footprint a.mem a4.mem := by
    have hm34 : Modifies (Block.mk base (space n)).footprint a1.mem a4.mem := by
      change Modifies (Block.mk base (space n)).footprint a1.mem
        (Function.update a3.mem (base + n + w2.val) (w1.val + 1))
      rw [hmem3]
      exact Modifies.write_of_owns ho_pw2 (w1.val + 1)
    exact modifies_block_trans hmod1 hm34
  have hst4 : RawState.ofData n base a4 =
      { st with
        par := Function.update st.par w2 (w1.val + 1)
        cons := Function.update st.cons curD 0 } :=
    (ofData_set_scratch _ (by decide : 17 ≤ s1.val) curD).trans hst4_pre
  have ha4_s4 : a4.regs s4 = w1.val := (e4.regs_eq (by decide)).trans ha3_s4
  have ha4_s5 : a4.regs s5 = w2.val := (e4.regs_eq (by decide)).trans ha3_s5
  have ha4_s1 : a4.regs s1 = curD := by
    simp only [a4, Data.set_regs, Function.update_self]
  -- Step 5 (`a4 → a5`, ≤ 18 steps): splice `w2` into `w1`'s child list and increment `deg[w1]`
  let T_next : FHTree n := FHTree.node w1 (T₁.children ++ [T₂])
  let cStep5 : Code .exact rFib :=
    ram_exact[
      if s1 = zeroP then [
        s0 ← leftBase + s5;
        *s0 ← s5;
        s0 ← rightBase + s5;
        *s0 ← s5;
        s2 ← s5 + oneP;
        s0 ← childBase + s4;
        *s0 ← s2;
        s0 ← degBase + s4;
        *s0 ← oneP
      ] else [
        s0 ← childBase + s4;
        s6 ← *s0;
        s6 ← s6 - oneP;
        ⟪insertIntoNonEmptyList s6 s5⟫;
        s1 ← s1 + oneP;
        s0 ← degBase + s4;
        *s0 ← s1
      ]
    ]
  have hstep5 : ∃ a5,
      ExecWithin w cStep5 a4 a5 18 ∧
      a5.Bounded w ∧ BaseRegs n base a5 ∧
      Modifies (Block.mk base (space n)).footprint a4.mem a5.mem ∧
      LinksAs (RawState.ofData n base a1) w1 w2 (RawState.ofData n base a5) := by
    have hz_4 : a4.regs zeroP = 0 := hbr4.regs_zeroP
    have ho_4 : a4.regs oneP = 1 := hbr4.regs_oneP
    have hcb_4 : a4.regs childBase = base + 2 * n := hbr4.regs_childBase
    have hlb_4 : a4.regs leftBase = base + 3 * n := hbr4.regs_leftBase
    have hrb_4 : a4.regs rightBase = base + 4 * n := hbr4.regs_rightBase
    have hdb_4 : a4.regs degBase = base + 5 * n := hbr4.regs_degBase
    have ho_cw1 := owns_arr_addr (base := base) (k := 2) (by decide) hw1_lt
    have ho_dw1 := owns_arr_addr (base := base) (k := 5) (by decide) hw1_lt
    by_cases hd0 : curD = 0
    · have hc5 : (Cond.eq s1 zeroP).Holds a4 := by simp only [Cond.Holds, ha4_s1, hz_4, hd0]
      have ho_lw2 := owns_arr_addr (base := base) (k := 3) (by decide) hw2_lt
      have ho_rw2 := owns_arr_addr (base := base) (k := 4) (by decide) hw2_lt
      let p1 := (a4.set s0 (base + 3 * n + w2.val)).write (base + 3 * n + w2.val) w2.val
      let p2 := (p1.set s0 (base + 4 * n + w2.val)).write (base + 4 * n + w2.val) w2.val
      let p3 := ((p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)).write
        (base + 2 * n + w1.val) (w2.val + 1)
      let a5 := (p3.set s0 (base + 5 * n + w1.val)).write (base + 5 * n + w1.val) 1
      have s1_a : ExecWithin w (.op (.exactBin .add s0 leftBase s5)) a4
          (a4.set s0 (base + 3 * n + w2.val)) 1 := by
        simpa only [hlb_4, ha4_s5] using
          execWithin_exactAdd (x := a4) (d := s0) (i := leftBase) (j := s5)
            (by rw [hlb_4, ha4_s5]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s1_b : ExecWithin (B := .exact) w (.op (.store s0 s5))
          (a4.set s0 (base + 3 * n + w2.val)) p1 1 := by
        simpa only [Data.set_regs, Function.update_self,
          Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5] using
          (ExecWithin.store (B := .exact) (w := w) (x := a4.set s0 (base + 3 * n + w2.val))
            (a := s0) (s := s5))
      have s2_a : ExecWithin w (.op (.exactBin .add s0 rightBase s5)) p1
          (p1.set s0 (base + 4 * n + w2.val)) 1 := by
        have hr_p1 : p1.regs rightBase = base + 4 * n := hrb_4
        have hs5_p1 : p1.regs s5 = w2.val := by
          simp only [p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5]
        simpa only [hr_p1, hs5_p1] using
          execWithin_exactAdd (x := p1) (d := s0) (i := rightBase) (j := s5)
            (by rw [hr_p1, hs5_p1]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s2_b : ExecWithin (B := .exact) w (.op (.store s0 s5))
          (p1.set s0 (base + 4 * n + w2.val)) p2 1 := by
        have hs5_p1 : (p1.set s0 (base + 4 * n + w2.val)).regs s5 = w2.val := by
          simp only [p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5]
        simpa only [Data.set_regs, Function.update_self, hs5_p1] using
          (ExecWithin.store (B := .exact) (w := w) (x := p1.set s0 (base + 4 * n + w2.val))
            (a := s0) (s := s5))
      have s3_a : ExecWithin w (.op (.exactBin .add s2 s5 oneP)) p2 (p2.set s2 (w2.val + 1)) 1 := by
        have hs5_p2 : p2.regs s5 = w2.val := by
          simp only [p2, p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5]
        have ho_p2 : p2.regs oneP = 1 := ho_4
        simpa only [hs5_p2, ho_p2] using
          execWithin_exactAdd (x := p2) (d := s2) (i := s5) (j := oneP)
            (by rw [hs5_p2, ho_p2]; exact hfit_n1.of_le (by omega))
      have s3_b : ExecWithin w (.op (.exactBin .add s0 childBase s4)) (p2.set s2 (w2.val + 1))
          ((p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)) 1 := by
        have hc_p2 : (p2.set s2 (w2.val + 1)).regs childBase = base + 2 * n := hcb_4
        have hs4_p2 : (p2.set s2 (w2.val + 1)).regs s4 = w1.val := by
          simp only [p2, p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s4 ≠ s2),
            Function.update_of_ne (by decide : s4 ≠ s0), ha4_s4]
        simpa only [hc_p2, hs4_p2] using
          execWithin_exactAdd (x := p2.set s2 (w2.val + 1)) (d := s0) (i := childBase) (j := s4)
            (by rw [hc_p2, hs4_p2]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s3_c : ExecWithin (B := .exact) w (.op (.store s0 s2))
          ((p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)) p3 1 := by
        have hs2_p2 : ((p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)).regs s2 =
            w2.val + 1 := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s2 ≠ s0),
            Function.update_self]
        simpa only [Data.set_regs, Function.update_self, hs2_p2] using
          (ExecWithin.store (B := .exact) (w := w)
            (x := (p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)) (a := s0) (s := s2))
      have s4_a : ExecWithin w (.op (.exactBin .add s0 degBase s4)) p3
          (p3.set s0 (base + 5 * n + w1.val)) 1 := by
        have hd_p3 : p3.regs degBase = base + 5 * n := hdb_4
        have hs4_p3 : p3.regs s4 = w1.val := by
          simp only [p3, p2, p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s4 ≠ s0),
            Function.update_of_ne (by decide : s4 ≠ s2), ha4_s4]
        simpa only [hd_p3, hs4_p3] using
          execWithin_exactAdd (x := p3) (d := s0) (i := degBase) (j := s4)
            (by rw [hd_p3, hs4_p3]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s4_b : ExecWithin (B := .exact) w (.op (.store s0 oneP))
          (p3.set s0 (base + 5 * n + w1.val)) a5 1 := by
        have ho_p3 : (p3.set s0 (base + 5 * n + w1.val)).regs oneP = 1 := ho_4
        simpa only [Data.set_regs, Function.update_self, ho_p3] using
          (ExecWithin.store (B := .exact) (w := w)
            (x := p3.set s0 (base + 5 * n + w1.val)) (a := s0) (s := oneP))
      have he_pos := s1_a.seq <| s1_b.seq <| s2_a.seq <| s2_b.seq <| s3_a.seq <|
        s3_b.seq <| s3_c.seq <| s4_a.seq s4_b
      have he5 : ExecWithin w cStep5 a4 a5 18 :=
        (ExecWithin.branch_pos hc5 he_pos).mono (by omega)
      have hbr5 : BaseRegs n base a5 :=
        ((((((((hbr4.set_non_base (by decide) _).write_eq _ _).set_non_base
          (by decide) _).write_eq _ _).set_non_base (by decide) _).set_non_base
          (by decide) _).write_eq _ _).set_non_base (by decide) _).write_eq _ _
      have hmod5 : Modifies (Block.mk base (space n)).footprint a4.mem a5.mem :=
        modifies_block_trans (Modifies.write_of_owns ho_lw2 w2.val) <|
        modifies_block_trans (Modifies.write_of_owns ho_rw2 w2.val) <|
        modifies_block_trans (Modifies.write_of_owns ho_cw1 (w2.val + 1))
          (Modifies.write_of_owns ho_dw1 1)
      have hst5 : RawState.ofData n base a5 =
          { st with
            par := Function.update st.par w2 (w1.val + 1)
            child := Function.update st.child w1 (w2.val + 1)
            left := Function.update st.left w2 w2.val
            right := Function.update st.right w2 w2.val
            deg := Function.update st.deg w1 1
            cons := Function.update st.cons curD 0 } := by
        simp only [a5, p3, p2, p1, ofData_write_deg, ofData_write_child, ofData_write_right,
          ofData_write_left, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
          ofData_set_scratch _ (by decide : 17 ≤ s2.val), hst4]
      refine ⟨a5, he5, he5.bounded hb4, hbr5, hmod5, Or.inl ⟨?_, ?_⟩⟩
      · rw [hst1]
        exact hdeg_w1.trans hd0
      · rw [hst5, hst1]
    · have hc5 : ¬(Cond.eq s1 zeroP).Holds a4 := by
        simp only [Cond.Holds, ha4_s1, hz_4, hd0, not_false_eq_true]
      -- The head child `h_c` of `w1` and its right neighbour `r_c`.
      obtain ⟨h_c, r_c, hcw1_eq, hr_c⟩ := ValidSubtree.exists_child hT₁.1
        (by rw [ValidSubtree.deg_root hT₁.1]; exact fun h => hd0 (hd₁.symm.trans h))
      rw [hst1] at hcw1_eq hr_c
      have hhc_lt := h_c.isLt
      let q1 := ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)).set s6 h_c.val
      have t1 : ExecWithin w (.op (.exactBin .add s0 childBase s4)) a4
          (a4.set s0 (base + 2 * n + w1.val)) 1 := by
        simpa only [hcb_4, ha4_s4] using
          execWithin_exactAdd (x := a4) (d := s0) (i := childBase) (j := s4)
            (by rw [hcb_4, ha4_s4]; exact hfit_stop.of_le (by simp only [space]; omega))
      have t2 : ExecWithin (B := .exact) w (.op (.load s6 s0)) (a4.set s0 (base + 2 * n + w1.val))
          ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)) 1 := by
        have hm_cw1 : a4.mem (base + 2 * n + w1.val) = h_c.val + 1 := by
          have : (RawState.ofData n base a4).child w1 = h_c.val + 1 := by rw [hst4]; exact hcw1_eq
          exact this
        simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_cw1] using
          (ExecWithin.load (B := .exact) (w := w) (x := a4.set s0 (base + 2 * n + w1.val))
            (d := s6) (a := s0))
      have t3 : ExecWithin w (.op (.exactBin .sub s6 s6 oneP))
          ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)) q1 1 := by
        have hs6_q : ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)).regs s6 =
            h_c.val + 1 := by simp only [Data.set_regs, Function.update_self]
        have ho_q : ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)).regs oneP = 1 :=
          ho_4
        simpa only [hs6_q, ho_q, Nat.add_sub_cancel] using
          execWithin_exactSub
            (x := (a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1))
            (d := s6) (i := s6) (j := oneP)
            (by rw [hs6_q, ho_q]; omega)
            (by rw [hs6_q, ho_q]; exact hfit_n1.of_le (by omega))
      have hb_q1 : q1.Bounded w := t3.bounded (t2.bounded (t1.bounded hb4))
      have hbr_q1 : BaseRegs n base q1 :=
        ((hbr4.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _
      have hst_q1 : RawState.ofData n base q1 = RawState.ofData n base a4 := by
        simp only [q1, ofData_set_scratch _ (by decide : 17 ≤ s6.val),
          ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
      have hq1_s6 : q1.regs s6 = h_c.val := by simp only [q1, Data.set_regs, Function.update_self]
      have hq1_s5 : q1.regs s5 = w2.val := by
        simp only [q1, Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s6),
          Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5]
      obtain ⟨q2, t4, hbr_q2, hmod_q2, hst_q2⟩ :=
        insertIntoNonEmptyList_exec hb_q1 hbr_q1 (by decide) (by decide) (by decide) (by decide)
          hq1_s6 hq1_s5 (r := r_c) (by rw [hst_q1, hst4]; exact hr_c)
      rw [hst_q1, hst4] at hst_q2
      have hb_q2 : q2.Bounded w := t4.bounded hb_q1
      have hq2_s1 : q2.regs s1 = curD := by
        have h42 := t4.regs_eq (insertIntoNonEmptyList_preserves
          (by decide : s1 ≠ s0) (by decide : s1 ≠ s2))
        simp only [h42, q1, Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s6),
          Function.update_of_ne (by decide : s1 ≠ s0), ha4_s1]
      have hq2_s4 : q2.regs s4 = w1.val := by
        have h42 := t4.regs_eq (insertIntoNonEmptyList_preserves
          (by decide : s4 ≠ s0) (by decide : s4 ≠ s2))
        simp only [h42, q1, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s6),
          Function.update_of_ne (by decide : s4 ≠ s0), ha4_s4]
      let a5 := ((q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)).write
        (base + 5 * n + w1.val) (curD + 1)
      have t5 : ExecWithin w (.op (.exactBin .add s1 s1 oneP)) q2 (q2.set s1 (curD + 1)) 1 := by
        have ho_q2 : q2.regs oneP = 1 := hbr_q2.regs_oneP
        simpa only [hq2_s1, ho_q2] using
          execWithin_exactAdd (x := q2) (d := s1) (i := s1) (j := oneP)
            (by rw [hq2_s1, ho_q2]; exact hfit_n1.of_le (by omega))
      have t6 : ExecWithin w (.op (.exactBin .add s0 degBase s4)) (q2.set s1 (curD + 1))
          ((q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)) 1 := by
        have hd_q2 : (q2.set s1 (curD + 1)).regs degBase = base + 5 * n :=
          hbr_q2.regs_degBase
        have hs4_q2 : (q2.set s1 (curD + 1)).regs s4 = w1.val := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s1), hq2_s4]
        simpa only [hd_q2, hs4_q2] using
          execWithin_exactAdd (x := q2.set s1 (curD + 1)) (d := s0) (i := degBase) (j := s4)
            (by rw [hd_q2, hs4_q2]; exact hfit_stop.of_le (by simp only [space]; omega))
      have t7 : ExecWithin (B := .exact) w (.op (.store s0 s1))
          ((q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)) a5 1 := by
        have hs1_q2 : ((q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)).regs s1 =
            curD + 1 := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s0),
            Function.update_self]
        simpa only [Data.set_regs, Function.update_self, hs1_q2] using
          (ExecWithin.store (B := .exact) (w := w)
            (x := (q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)) (a := s0) (s := s1))
      have he_neg := t1.seq <| t2.seq <| t3.seq <| t4.seq <| t5.seq <| t6.seq t7
      have he5 : ExecWithin w cStep5 a4 a5 18 :=
        (ExecWithin.branch_neg hc5 he_neg).mono (by omega)
      have hbr5 : BaseRegs n base a5 :=
        (((hbr_q2.set_non_base (by decide) _).set_non_base (by decide) _).write_eq _ _)
      have hmod5 : Modifies (Block.mk base (space n)).footprint a4.mem a5.mem := by
        have hm_q1_q2 : Modifies (Block.mk base (space n)).footprint a4.mem q2.mem := hmod_q2
        have hm_q2_a5 : Modifies (Block.mk base (space n)).footprint q2.mem a5.mem :=
          Modifies.write_of_owns ho_dw1 (curD + 1)
        exact modifies_block_trans hm_q1_q2 hm_q2_a5
      have hst5 : RawState.ofData n base a5 =
          { st with
            par := Function.update st.par w2 (w1.val + 1)
            left := Function.update (Function.update st.left w2 h_c.val) r_c w2.val
            right := Function.update (Function.update st.right w2 r_c.val) h_c w2.val
            deg := Function.update st.deg w1 (curD + 1)
            cons := Function.update st.cons curD 0 } := by
        simp only [a5, ofData_write_deg, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
          ofData_set_scratch _ (by decide : 17 ≤ s1.val), hst_q2]
      refine ⟨a5, he5, he5.bounded hb4, hbr5, hmod5, Or.inr ⟨h_c, r_c, ?_, ?_, ?_, ?_⟩⟩
      · rw [hst1]
        exact fun h => hd0 (hdeg_w1.symm.trans h)
      · rw [hst1]
        exact hcw1_eq
      · rw [hst1]
        exact hr_c
      · rw [hst5, hst1]
        simp only [hdeg_w1]
  obtain ⟨a5, e5, hb5, hbr5, hmod5, hlink5⟩ := hstep5
  have ha5_s4 : a5.regs s4 = w1.val := (e5.regs_eq (by decide)).trans ha4_s4
  have hL := hlinked hlink5
  obtain ⟨hP_next, hback⟩ := hnext hL
  -- Step 6 (`a5 → a6`, 3 steps): `curDReg ← curDReg + oneP; s0 ← consBase + curDReg; s3 ← *s0`
  -- The verified phases before the increment preserve the degree counter.
  have he_prefix := e1_1.seq <| e1_2.seq <| e1_3.seq <| e2_1.seq <| e2_2.seq <| e2_3.seq <|
    e2_4.seq <| e2_5.seq <| e3.seq <| e4_1.seq <| e4_2.seq <| e4_3.seq <| e4_4.seq <|
    e4_5.seq e5
  have ha5_curD : a5.regs curDReg = curD :=
    (he_prefix.regs_eq (by decide +kernel)).trans ha_curD
  let a6 := ((a5.set curDReg (curD + 1)).set s0 (base + 8 * n + (curD + 1))).set s3
    ((RawState.ofData n base a5).cons (curD + 1))
  have e6_1 : ExecWithin w (.op (.exactBin .add curDReg curDReg oneP)) a5
      (a5.set curDReg (curD + 1)) 1 := by
    have ho_5 : a5.regs oneP = 1 := hbr5.regs_oneP
    simpa only [ha5_curD, ho_5] using
      execWithin_exactAdd (x := a5) (d := curDReg) (i := curDReg) (j := oneP)
        (by rw [ha5_curD, ho_5]; exact hfit_n1.of_le (by omega))
  have e6_2 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg))
      (a5.set curDReg (curD + 1))
      ((a5.set curDReg (curD + 1)).set s0 (base + 8 * n + (curD + 1))) 1 := by
    have hcb_5 : (a5.set curDReg (curD + 1)).regs consBase = base + 8 * n :=
      hbr5.regs_consBase
    have hcd_5 : (a5.set curDReg (curD + 1)).regs curDReg = curD + 1 := by
      simp only [Data.set_regs, Function.update_self]
    simpa only [hcb_5, hcd_5] using
      execWithin_exactAdd (x := a5.set curDReg (curD + 1))
        (d := s0) (i := consBase) (j := curDReg)
        (by rw [hcb_5, hcd_5]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e6_3 : ExecWithin (B := .exact) w (.op (.load s3 s0))
      ((a5.set curDReg (curD + 1)).set s0 (base + 8 * n + (curD + 1))) a6 1 := by
    have hm_c1 : a5.mem (base + 8 * n + (curD + 1)) =
        (RawState.ofData n base a5).cons (curD + 1) := by
      simp only [RawState.ofData, hd1_le_n, ↓reduceIte]
    simpa only [a6, Data.set_mem, Data.set_regs, Function.update_self, hm_c1] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := (a5.set curDReg (curD + 1)).set s0 (base + 8 * n + (curD + 1)))
        (d := s3) (a := s0))
  have hb6 : a6.Bounded w := e6_3.bounded (e6_2.bounded (e6_1.bounded hb5))
  have hbr6 : BaseRegs n base a6 :=
    ((hbr5.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _
  have hst6 : RawState.ofData n base a6 = RawState.ofData n base a5 := by
    simp only [a6, ofData_set_scratch _ (by decide : 17 ≤ s3.val),
      ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ curDReg.val)]
  have he_all : ExecWithin w scatterBody a a6 43 := by
    unfold scatterBody
    exact (e1_1.seq <| e1_2.seq <| e1_3.seq <| e2_1.seq <| e2_2.seq <| e2_3.seq <|
      e2_4.seq <| e2_5.seq <| e3.seq <| e4_1.seq <| e4_2.seq <| e4_3.seq <| e4_4.seq <|
      e4_5.seq <| e5.seq <| e6_1.seq <| e6_2.seq e6_3).mono (by omega)
  refine ⟨a6, T_next, slotTrees', he_all, hb6, hbr6, modifies_block_trans hmod4 hmod5, ?_,
    hlen_er, hL.deg.trans (by rw [hcur_deg]), ?_, ?_, ?_, by rw [hst6]; exact hP_next,
    fun hc => hback (by rw [← hst6]; exact hc)⟩
  · exact fun r hr => he_all.regs_eq (scatterBody_preserves r hr)
  · simp only [a6, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s3),
      Function.update_of_ne (by decide : s4 ≠ s0),
      Function.update_of_ne (by decide : s4 ≠ curDReg), ha5_s4, T_next, FHTree.root_node]
  · simp only [a6, Data.set_regs, Function.update_of_ne (by decide : curDReg ≠ s3),
      Function.update_of_ne (by decide : curDReg ≠ s0), Function.update_self]
  · simp only [a6, Data.set_regs, Function.update_self, hst6]

/-- Full `while zeroP < s3 do scatterBody` loop by induction on `slotTrees.length`: it stops at an
empty slot `curD_f`, holding `Placing` for the final tree `T_f`, in
`t + 50 * slotTrees_f.length ≤ 2 + 50 * slotTrees.length` instructions. Placing `T_f` places
`T_cur`. -/
private theorem scatterLoop_exec {n sz base w maxDeg : ℕ} {z : Fin n} :
    ∀ (k : ℕ) {a : Data rFib} {T_cur : FHTree n} {slotTrees : List (FHTree n)} {curD : ℕ},
      slotTrees.length = k →
      a.Bounded w → BaseRegs n base a →
      Placing sz z (RawState.ofData n base a) T_cur slotTrees maxDeg →
      T_cur.deg = curD →
      a.regs s4 = T_cur.root.val →
      a.regs curDReg = curD →
      a.regs s3 = (RawState.ofData n base a).cons curD →
      ∃ z_lp T_f slotTrees_f curD_f t,
        ExecWithin w (.loop (.lt zeroP s3) scatterBody) a z_lp t ∧
        t + slotCredit * slotTrees_f.length ≤ 2 + slotCredit * slotTrees.length ∧
        ¬(Cond.lt zeroP s3).Holds z_lp ∧
        z_lp.Bounded w ∧ BaseRegs n base z_lp ∧
        Modifies (Block.mk base (space n)).footprint a.mem z_lp.mem ∧
        (∀ r : Fin rFib, r.val < 34 → z_lp.regs r = a.regs r) ∧
        T_f.deg = curD_f ∧
        z_lp.regs s4 = T_f.root.val ∧
        z_lp.regs curDReg = curD_f ∧
        z_lp.regs s3 = (RawState.ofData n base z_lp).cons curD_f ∧
        Placing sz z (RawState.ofData n base z_lp) T_f slotTrees_f maxDeg ∧
        ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
          Consolidated sz (RawState.ofData n base z_lp) st' (forestNodes (T_f :: slotTrees_f))
            slots' md' →
          Consolidated sz (RawState.ofData n base a) st' (forestNodes (T_cur :: slotTrees))
            slots' md'
  | 0, a, T_cur, slotTrees, curD, hk, hb, hbr, hP, hcd, hs4, hcd_r, hs3 => by
    by_cases hc : (Cond.lt zeroP s3).Holds a
    · obtain ⟨_, _, _, _, _, _, _, _, hlen_er, _⟩ := scatterBody_exec hb hbr hP hcd hs4 hcd_r hs3 hc
      omega
    · exact ⟨a, T_cur, slotTrees, curD, 2, ExecWithin.loop_exit hc, by omega, hc, hb, hbr,
        Modifies.refl _ _, fun _ _ => rfl, hcd, hs4, hcd_r, hs3, hP, fun h => h⟩
  | k + 1, a, T_cur, slotTrees, curD, hk, hb, hbr, hP, hcd, hs4, hcd_r, hs3 => by
    by_cases hc : (Cond.lt zeroP s3).Holds a
    · obtain ⟨a', T_next, slotTrees', he1, hb', hbr', hmod1, hlow1, hlen_er, hdeg1, hs4_1, hcd1,
        hs3_1, hP1, hback1⟩ := scatterBody_exec hb hbr hP hcd hs4 hcd_r hs3 hc
      obtain ⟨z_lp, T_f, slotTrees_f, curD_f, t₂, he2, ht2, hnc, hbz, hbrz, hmod2, hlow2, hdeg2,
        hs4_2, hcd2, hs3_2, hP2, hback2⟩ :=
        scatterLoop_exec k (by omega) hb' hbr' hP1 hdeg1 hs4_1 hcd1 hs3_1
      exact ⟨z_lp, T_f, slotTrees_f, curD_f, 43 + t₂ + 2, ExecWithin.loop_iter hc he1 he2,
        by dsimp only [slotCredit] at ht2 ⊢; omega, hnc, hbz, hbrz,
        modifies_block_trans hmod1 hmod2, fun r hr => (hlow2 r hr).trans (hlow1 r hr), hdeg2,
        hs4_2, hcd2, hs3_2, hP2, fun hc' => hback1 (hback2 hc')⟩
    · exact ⟨a, T_cur, slotTrees, curD, 2, ExecWithin.loop_exit hc, by omega, hc, hb, hbr,
        Modifies.refl _ _, fun _ _ => rfl, hcd, hs4, hcd_r, hs3, hP, fun h => h⟩

/-- `scatterRootCode` places the valid root tree `T₀` (`iterCur = T₀.root.val`) into the
consolidation table, linking equal-degree roots and updating `maxDegReg`: the result is
`Consolidated`, in `t + 50 * slotTrees'.length ≤ 63 + 50 * slotTrees₀.length` instructions, and
all registers `< 33` are preserved. -/
theorem scatterRootCode_exec {n sz base w maxDeg₀ : ℕ} {x : Data rFib}
    {T₀ : FHTree n} {slotTrees₀ : List (FHTree n)} {z : Fin n}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    (hP : Placing sz z (RawState.ofData n base x) T₀ slotTrees₀ maxDeg₀)
    (hx_ic : x.regs iterCur = T₀.root.val)
    (hx_md : x.regs maxDegReg = maxDeg₀) :
    ∃ y slotTrees' maxDeg' t,
      ExecWithin w scatterRootCode x y t ∧
      t + slotCredit * slotTrees'.length ≤ 63 + slotCredit * slotTrees₀.length ∧
      y.Bounded w ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∀ r : Fin rFib, r.val < 33 → y.regs r = x.regs r) ∧
      y.regs maxDegReg = maxDeg' ∧
      Consolidated sz (RawState.ofData n base x) (RawState.ofData n base y)
        (forestNodes (T₀ :: slotTrees₀)) slotTrees' maxDeg' := by
  set st := RawState.ofData n base x with hst_def
  have hfit_stop := hbr.fits_stop hb
  have hfit_n1 : Fits w (n + 1) := hfit_stop.of_le (by simp only [space]; omega)
  let u0 := T₀.root
  have hu0_lt := u0.isLt
  let d0 := T₀.deg
  have hd0_bds := hP.deg_bounds
  have hd0_le_n : d0 ≤ n := by omega
  have hdeg_u0 : st.deg u0 = d0 := ValidSubtree.deg_root hP.valid.1
  -- Preamble (`x → x1`, 5 steps): load `d0 ← deg[iterCur]` and `s3 ← cons[d0]`
  let x1 := ((((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).set s0
    (base + 8 * n + d0)).set s3 (st.cons d0)
  have p1 : ExecWithin (B := .exact) w (.op (.copy s4 iterCur)) x (x.set s4 u0.val) 1 := by
    simpa only [hx_ic] using
      (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := s4) (s := iterCur))
  have p2 : ExecWithin w (.op (.exactBin .add s0 degBase s4)) (x.set s4 u0.val)
      ((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)) 1 := by
    have hdb : (x.set s4 u0.val).regs degBase = base + 5 * n := hbr.regs_degBase
    have hs4 : (x.set s4 u0.val).regs s4 = u0.val := by
      simp only [Data.set_regs, Function.update_self]
    simpa only [hdb, hs4] using
      execWithin_exactAdd (x := x.set s4 u0.val) (d := s0) (i := degBase) (j := s4)
        (by rw [hdb, hs4]; exact hfit_stop.of_le (by simp only [space]; omega))
  have p3 : ExecWithin (B := .exact) w (.op (.load curDReg s0))
      ((x.set s4 u0.val).set s0 (base + 5 * n + u0.val))
      (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0) 1 := by
    have hm_du0 : x.mem (base + 5 * n + u0.val) = d0 := hdeg_u0
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_du0] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := (x.set s4 u0.val).set s0 (base + 5 * n + u0.val)) (d := curDReg) (a := s0))
  have p4 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg))
      (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0)
      ((((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).set s0
        (base + 8 * n + d0)) 1 := by
    have hcb : (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).regs
        consBase = base + 8 * n := hbr.regs_consBase
    have hcd : (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).regs
        curDReg = d0 := by simp only [Data.set_regs, Function.update_self]
    simpa only [hcb, hcd] using
      execWithin_exactAdd
        (x := ((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0)
        (d := s0) (i := consBase) (j := curDReg)
        (by rw [hcb, hcd]; exact hfit_stop.of_le (by simp only [space]; omega))
  have p5 : ExecWithin (B := .exact) w (.op (.load s3 s0))
      ((((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).set s0
        (base + 8 * n + d0)) x1 1 := by
    have hm_cd0 : x.mem (base + 8 * n + d0) = st.cons d0 := by
      simp only [st, RawState.ofData, hd0_le_n, ↓reduceIte]
    simpa only [x1, Data.set_mem, Data.set_regs, Function.update_self, hm_cd0] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).set s0
          (base + 8 * n + d0)) (d := s3) (a := s0))
  have hb1 : x1.Bounded w := p5.bounded (p4.bounded (p3.bounded (p2.bounded (p1.bounded hb))))
  have hbr1 : BaseRegs n base x1 :=
    ((((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
      (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _
  have hst1 : RawState.ofData n base x1 = st := by
    simp only [x1, ofData_set_scratch _ (by decide : 17 ≤ s3.val),
      ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ curDReg.val),
      ofData_set_scratch _ (by decide : 17 ≤ s4.val), ← hst_def]
  have hx1_s4 : x1.regs s4 = u0.val := by
    simp only [x1, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s3),
      Function.update_of_ne (by decide : s4 ≠ s0),
      Function.update_of_ne (by decide : s4 ≠ curDReg), Function.update_self]
  have hx1_cd : x1.regs curDReg = d0 := by
    simp only [x1, Data.set_regs, Function.update_of_ne (by decide : curDReg ≠ s3),
      Function.update_of_ne (by decide : curDReg ≠ s0), Function.update_self]
  have hx1_md : x1.regs maxDegReg = maxDeg₀ := by
    simp only [x1, Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ s3),
      Function.update_of_ne (by decide : maxDegReg ≠ s0),
      Function.update_of_ne (by decide : maxDegReg ≠ curDReg),
      Function.update_of_ne (by decide : maxDegReg ≠ s4), hx_md]
  have hx1_s3 : x1.regs s3 = (RawState.ofData n base x1).cons d0 := by
    simp only [x1, Data.set_regs, Function.update_self, hst1]
  -- Collision loop (`x1 → z_lp`, `t_lp` steps):
  obtain ⟨z_lp, T_f, slotTrees_f, curD_f, t_lp, he_lp, ht_lp, hnc_lp, hbz, hbrz, hmod_lp,
    hlow_lp, hdeg_f, hs4_lp, hcd_lp, hs3_lp, hP_f, hback⟩ :=
    scatterLoop_exec slotTrees₀.length rfl hb1 hbr1 (by rw [hst1]; exact hP) rfl hx1_s4 hx1_cd
      hx1_s3
  have hmd_lp : z_lp.regs maxDegReg = maxDeg₀ := (hlow_lp maxDegReg (by decide)).trans hx1_md
  set st_lp := RawState.ofData n base z_lp with hst_lp_def
  -- Post-loop (`z_lp → y`, 5 steps): store `uf + 1` in `cons[curD_f]` and update `maxDegReg`
  have hdf_bds := hP_f.deg_bounds
  rw [hdeg_f] at hdf_bds
  have hdf_le_n : curD_f ≤ n := by omega
  have hcons_f_zero : st_lp.cons curD_f = 0 := by
    have hz0_lp : z_lp.regs zeroP = 0 := hbrz.regs_zeroP
    rw [Cond.Holds, hz0_lp, hs3_lp] at hnc_lp
    omega
  have hnone_f : ∀ R ∈ slotTrees_f, R.deg ≠ curD_f := by
    rcases hP_f.table.lookup hdf_le_n with ⟨_, hnone⟩ | ⟨_, _, _, hce, _, _⟩
    · exact hnone
    · omega
  let uf := T_f.root
  have huf_lt := uf.isLt
  have ho_cons_f := owns_cons_addr (base := base) hdf_le_n
  let z2 := ((z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)).write
    (base + 8 * n + curD_f) (uf.val + 1)
  have q1 : ExecWithin w (.op (.exactBin .add s1 s4 oneP)) z_lp (z_lp.set s1 (uf.val + 1)) 1 := by
    have ho_z : z_lp.regs oneP = 1 := hbrz.regs_oneP
    simpa only [hs4_lp, ho_z] using
      execWithin_exactAdd (x := z_lp) (d := s1) (i := s4) (j := oneP)
        (by rw [hs4_lp, ho_z]; exact hfit_n1.of_le (by omega))
  have q2 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg)) (z_lp.set s1 (uf.val + 1))
      ((z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)) 1 := by
    have hcb_z : (z_lp.set s1 (uf.val + 1)).regs consBase = base + 8 * n :=
      hbrz.regs_consBase
    have hcd_z : (z_lp.set s1 (uf.val + 1)).regs curDReg = curD_f := hcd_lp
    simpa only [hcb_z, hcd_z] using
      execWithin_exactAdd (x := z_lp.set s1 (uf.val + 1)) (d := s0) (i := consBase) (j := curDReg)
        (by rw [hcb_z, hcd_z]; exact hfit_stop.of_le (by simp only [space]; omega))
  have q3 : ExecWithin (B := .exact) w (.op (.store s0 s1))
      ((z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)) z2 1 := by
    have hs1_z : ((z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)).regs s1 =
        uf.val + 1 := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s0), Function.update_self]
    simpa only [Data.set_regs, Function.update_self, hs1_z] using
      (ExecWithin.store (B := .exact) (w := w)
        (x := (z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)) (a := s0) (s := s1))
  have hb_z2 : z2.Bounded w := q3.bounded (q2.bounded (q1.bounded hbz))
  have hbr_z2 : BaseRegs n base z2 :=
    ((hbrz.set_non_base (by decide) _).set_non_base (by decide) _).write_eq _ _
  have hst_z2 : RawState.ofData n base z2 =
      { st_lp with cons := Function.update st_lp.cons curD_f (uf.val + 1) } := by
    simp only [z2, ofData_write_cons hdf_le_n, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ s1.val), ← hst_lp_def]
  have hz2_md : z2.regs maxDegReg = maxDeg₀ := hmd_lp
  have hz2_cd : z2.regs curDReg = curD_f := hcd_lp
  have hz2_z0 : z2.regs zeroP = 0 := hbr_z2.regs_zeroP
  have hmax_step : ∃ y,
      ExecWithin (B := .exact) w
        (.branch (.lt maxDegReg curDReg) (.op (.copy maxDegReg curDReg)) (.op (.copy s0 zeroP)))
        z2 y 3 ∧
      y.Bounded w ∧ BaseRegs n base y ∧ y.mem = z2.mem ∧
      RawState.ofData n base y = RawState.ofData n base z2 ∧
      y.regs maxDegReg = max maxDeg₀ curD_f ∧
      (∀ r : Fin rFib, r.val < 33 → y.regs r = z2.regs r) := by
    by_cases hlt_md : maxDeg₀ < curD_f
    · have hc_md : (Cond.lt maxDegReg curDReg).Holds z2 := by
        simp only [Cond.Holds, hz2_md, hz2_cd, hlt_md]
      let y := z2.set maxDegReg curD_f
      have ec : ExecWithin (B := .exact) w (.op (.copy maxDegReg curDReg)) z2 y 1 := by
        simpa only [hz2_cd] using
          (ExecWithin.copy (B := .exact) (w := w) (x := z2) (d := maxDegReg) (s := curDReg))
      have heb : ExecWithin (B := .exact) w
          (.branch (.lt maxDegReg curDReg) (.op (.copy maxDegReg curDReg)) (.op (.copy s0 zeroP)))
          z2 y 3 := (ExecWithin.branch_pos hc_md ec).mono (by omega)
      refine ⟨y, heb, heb.bounded hb_z2, hbr_z2.set_non_base (by decide) curD_f, rfl,
        ofData_set_scratch z2 (by decide : 17 ≤ maxDegReg.val) curD_f,
        by simp only [y, Data.set_regs, Function.update_self]; omega, ?_⟩
      intro r hr
      have ne_md : r ≠ maxDegReg := fun e => by subst e; change 33 < 33 at hr; omega
      simp only [y, Data.set_regs, Function.update_of_ne ne_md]
    · have hc_md : ¬(Cond.lt maxDegReg curDReg).Holds z2 := by
        simp only [Cond.Holds, hz2_md, hz2_cd]; omega
      let y := z2.set s0 0
      have ec : ExecWithin (B := .exact) w (.op (.copy s0 zeroP)) z2 y 1 := by
        simpa only [hz2_z0] using
          (ExecWithin.copy (B := .exact) (w := w) (x := z2) (d := s0) (s := zeroP))
      have heb : ExecWithin (B := .exact) w
          (.branch (.lt maxDegReg curDReg) (.op (.copy maxDegReg curDReg)) (.op (.copy s0 zeroP)))
          z2 y 3 := (ExecWithin.branch_neg hc_md ec).mono (by omega)
      refine ⟨y, heb, heb.bounded hb_z2, hbr_z2.set_non_base (by decide) 0, rfl,
        ofData_set_scratch z2 (by decide : 17 ≤ s0.val) 0,
        by simp only [y, Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ s0),
          hz2_md]; omega, ?_⟩
      intro r hr
      have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 33 at hr; omega
      simp only [y, Data.set_regs, Function.update_of_ne ne0]
  obtain ⟨y, q4, hby, hbry, hmemy, hsty, hymd, hy_low⟩ := hmax_step
  have he_all : ExecWithin w scatterRootCode x y (t_lp + 11) := by
    unfold scatterRootCode
    exact (p1.seq <| p2.seq <| p3.seq <| p4.seq <| p5.seq <| he_lp.seq <|
      q1.seq <| q2.seq <| q3.seq q4).mono (by omega)
  have hmod_all : Modifies (Block.mk base (space n)).footprint x.mem y.mem := by
    rw [hmemy]
    have hm_lp : Modifies (Block.mk base (space n)).footprint x.mem z_lp.mem := hmod_lp
    have hm_z2 : Modifies (Block.mk base (space n)).footprint z_lp.mem z2.mem :=
      Modifies.write_of_owns ho_cons_f (uf.val + 1)
    exact modifies_block_trans hm_lp hm_z2
  refine ⟨y, T_f :: slotTrees_f, max maxDeg₀ curD_f, t_lp + 11, he_all,
    by simp only [List.length_cons, slotCredit] at ht_lp ⊢; omega,
    hby, hbry, hmod_all, ?_, hymd, ?_⟩
  · intro r hr
    have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 33 at hr; omega
    have ne1 : r ≠ s1 := fun e => by subst e; change 36 < 33 at hr; omega
    have ne3 : r ≠ s3 := fun e => by subst e; change 38 < 33 at hr; omega
    have ne4 : r ≠ s4 := fun e => by subst e; change 39 < 33 at hr; omega
    have ne_cd : r ≠ curDReg := fun e => by subst e; change 34 < 33 at hr; omega
    rw [hy_low r hr]
    simp only [z2, Data.write_regs, Data.set_regs, Function.update_of_ne ne0,
      Function.update_of_ne ne1, hlow_lp r (by omega), x1, Function.update_of_ne ne3,
      Function.update_of_ne ne_cd, Function.update_of_ne ne4]
  · rw [hsty, hst_z2, ← hst1]
    refine hback ?_
    rw [← hdeg_f]
    exact hP_f.place (hdeg_f ▸ hnone_f)

/-! ## Consolidation scatter loops (`childScatterLoop` and `rootScatterLoop`) -/

private abbrev childScatterBody : Code .exact rFib :=
  ram_exact[
    s0 ← rightBase + iterCur;
    iterNxt ← *s0;
    s0 ← parBase + iterCur;
    *s0 ← zeroP;
    s0 ← markBase + iterCur;
    s1 ← *s0;
    if zeroP < s1 then [
      *s0 ← zeroP;
      numMarkedReg ← numMarkedReg - oneP
    ] else [
      s0 ← zeroP
    ];
    ⟪scatterRootCode⟫;
    iterCur ← iterNxt;
    remReg ← remReg - oneP
  ]

private abbrev childScatterLoop : Code .exact rFib :=
  .loop (.lt zeroP remReg) childScatterBody


/-- Phase A1 loop: walks the children `rest` along their `right` pointers, clears each one's `par`
and `mark` (decrementing `numMarkedReg` when it was marked), and scatters it into `cons`. The
result is `Consolidated`; the forest reasoning is `Scattering.unmark`, `Scattering.placing` and
`Scattering.step`. -/
private theorem scatterChildrenLoop_exec {n sz base w : ℕ} {z : Fin n} :
    ∀ (rest : List (FHTree n)) (a : Data rFib) (slotTrees : List (FHTree n)) (maxDeg : ℕ),
      a.Bounded w → BaseRegs n base a →
      Scattering sz z true (RawState.ofData n base a) slotTrees rest maxDeg →
      a.regs remReg = rest.length →
      a.regs maxDegReg = maxDeg →
      (∀ y ∈ (rest.map FHTree.root).head?, a.regs iterCur = y.val) →
      ∃ b slotTrees' maxDeg' t,
        ExecWithin w childScatterLoop a b t ∧
        t + slotCredit * slotTrees'.length ≤
          2 + 76 * rest.length + slotCredit * slotTrees.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        (∀ r : Fin rFib, r.val < 30 → r ≠ numMarkedReg → b.regs r = a.regs r) ∧
        b.regs maxDegReg = maxDeg' ∧
        Consolidated sz (RawState.ofData n base a) (RawState.ofData n base b)
          (forestNodes (slotTrees ++ rest)) slotTrees' maxDeg'
  | [], a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, _ => by
    have hc : ¬(Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hbr.regs_zeroP, hrem, List.length_nil, Nat.lt_irrefl,
        not_false_eq_true]
    exact ⟨a, slotTrees, maxDeg, 2, ExecWithin.loop_exit hc, by omega, hb, hbr,
      Modifies.refl _ _, fun _ _ _ => rfl, hmd, h.done⟩
  | T_u :: c_tl, a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, hic => by
    set st := RawState.ofData n base a with hst_def
    have hfit_stop := hbr.fits_stop hb
    have hz0 : a.regs zeroP = 0 := hbr.regs_zeroP
    have ho1 : a.regs oneP = 1 := hbr.regs_oneP
    have hpb : a.regs parBase = base + n := hbr.regs_parBase
    have hrb : a.regs rightBase = base + 4 * n := hbr.regs_rightBase
    have hmkb : a.regs markBase = base + 6 * n := hbr.regs_markBase
    have hc : (Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hz0, hrem, List.length_cons]; omega
    let u := T_u.root
    have hu_ic : a.regs iterCur = u.val := hic u rfl
    have hu_lt := u.isLt
    have hTu_sub : ValidSubtree st none T_u := h.valid T_u List.mem_cons_self
    have hu_bds : st.inHeap u ≠ 0 ∧ st.mark u ≤ 1 :=
      ⟨h.inHeap u (List.mem_append_left _ T_u.root_mem_nodes), ValidSubtree.mark_root_le hTu_sub⟩
    have hnm : st.numMarked = markedCount st := h.numMarked
    -- Step 1 (`a → a1`, 6 steps): load `iterNxt ← right[u]`, clear `par[u]`, load `s1 ← mark[u]`
    have ho_par_u := owns_arr_addr (base := base) (k := 1) (by decide) hu_lt
    have ho_mk_u := owns_arr_addr (base := base) (k := 6) (by decide) hu_lt
    let nxtVal := st.right u
    let a1 := (((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
      (base + n + u.val)).write (base + n + u.val) 0).set s0 (base + 6 * n + u.val)).set s1
      (st.mark u)
    have s1_1 : ExecWithin w (.op (.exactBin .add s0 rightBase iterCur)) a
        (a.set s0 (base + 4 * n + u.val)) 1 := by
      simpa only [hrb, hu_ic] using
        execWithin_exactAdd (x := a) (d := s0) (i := rightBase) (j := iterCur)
          (by rw [hrb, hu_ic]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s1_2 : ExecWithin (B := .exact) w (.op (.load iterNxt s0))
        (a.set s0 (base + 4 * n + u.val))
        ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal) 1 := by
      have hm_r : a.mem (base + 4 * n + u.val) = nxtVal := rfl
      simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_r] using
        (ExecWithin.load (B := .exact) (w := w) (x := a.set s0 (base + 4 * n + u.val))
          (d := iterNxt) (a := s0))
    have s1_3 : ExecWithin w (.op (.exactBin .add s0 parBase iterCur))
        ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal)
        (((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)) 1 := by
      have hp_1 : ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).regs parBase =
          base + n := hpb
      have hic_1 : ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).regs iterCur =
          u.val := hu_ic
      simpa only [hp_1, hic_1] using
        execWithin_exactAdd (x := (a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal)
          (d := s0) (i := parBase) (j := iterCur)
          (by rw [hp_1, hic_1]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s1_4 : ExecWithin (B := .exact) w (.op (.store s0 zeroP))
        (((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val))
        ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)).write
          (base + n + u.val) 0) 1 := by
      have hz_1 : (((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
          (base + n + u.val)).regs zeroP = 0 := hz0
      simpa only [Data.set_regs, Function.update_self, hz_1] using
        (ExecWithin.store (B := .exact) (w := w)
          (x := ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val))
          (a := s0) (s := zeroP))
    have s1_5 : ExecWithin w (.op (.exactBin .add s0 markBase iterCur))
        ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)).write
          (base + n + u.val) 0)
        (((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)).write
          (base + n + u.val) 0).set s0 (base + 6 * n + u.val)) 1 := by
      have hm_1 : ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
          (base + n + u.val)).write (base + n + u.val) 0).regs markBase = base + 6 * n := hmkb
      have hic_1 : ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
          (base + n + u.val)).write (base + n + u.val) 0).regs iterCur = u.val := hu_ic
      simpa only [hm_1, hic_1] using
        execWithin_exactAdd
          (x := (((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
            (base + n + u.val)).write (base + n + u.val) 0)
          (d := s0) (i := markBase) (j := iterCur)
          (by rw [hm_1, hic_1]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s1_6 : ExecWithin (B := .exact) w (.op (.load s1 s0))
        (((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)).write
          (base + n + u.val) 0).set s0 (base + 6 * n + u.val)) a1 1 := by
      have hm_mk : a.mem (base + 6 * n + u.val) = st.mark u := rfl
      simpa only [a1, Data.set_mem, Data.write_mem, Data.set_regs, Function.update_self,
        Function.update_of_ne (by omega : base + 6 * n + u.val ≠ base + n + u.val), hm_mk] using
        (ExecWithin.load (B := .exact) (w := w)
          (x := ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
            (base + n + u.val)).write (base + n + u.val) 0).set s0 (base + 6 * n + u.val))
          (d := s1) (a := s0))
    have he1 : ExecWithin w
        (.seq (.op (.exactBin .add s0 rightBase iterCur)) <|
         .seq (.op (.load iterNxt s0)) <|
         .seq (.op (.exactBin .add s0 parBase iterCur)) <|
         .seq (.op (.store s0 zeroP)) <|
         .seq (.op (.exactBin .add s0 markBase iterCur))
              (.op (.load s1 s0))) a a1 6 :=
      (s1_1.seq <| s1_2.seq <| s1_3.seq <| s1_4.seq <| s1_5.seq s1_6).mono (by omega)
    have hb1 : a1.Bounded w := he1.bounded hb
    have hbr1 : BaseRegs n base a1 :=
      (((((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
        (by decide) _).write_eq _ _).set_non_base (by decide) _).set_non_base (by decide) _
    have hmod1 : Modifies (Block.mk base (space n)).footprint a.mem a1.mem := by
      dsimp only [a1]
      simp only [Data.set_mem, Data.write_mem]
      simpa only [Nat.one_mul] using Modifies.write_of_owns ho_par_u 0
    have hst1 : RawState.ofData n base a1 = { st with par := Function.update st.par u 0 } := by
      have hp_wr : RawState.ofData n base (a.write (base + n + u.val) 0) =
          { st with par := Function.update st.par u 0 } := by
        simpa only [Nat.one_mul, ← hst_def] using ofData_write_par a u 0
      simp only [a1, ofData_set_scratch _ (by decide : 17 ≤ s1.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
      exact hp_wr
    have ha1_s0 : a1.regs s0 = base + 6 * n + u.val := by
      simp only [a1, Data.set_regs, Function.update_of_ne (by decide : s0 ≠ s1),
        Function.update_self]
    have ha1_s1 : a1.regs s1 = st.mark u := by
      simp only [a1, Data.set_regs, Function.update_self]
    have ha1_z0 : a1.regs zeroP = 0 := hbr1.regs_zeroP
    have ha1_o1 : a1.regs oneP = 1 := hbr1.regs_oneP
    have ha1_nm : a1.regs numMarkedReg = st.numMarked := rfl
    -- Step 2 (`a1 → a_mid`, 3 steps): clear `mark[u]` and decrement `numMarkedReg` if
    -- `0 < mark[u]`; the result is `unmarkState st u`.
    have hmark_step : ∃ a_mid,
        ExecWithin (B := .exact) w
          (.branch (.lt zeroP s1)
            (.seq (.op (.store s0 zeroP)) (.op (.exactBin .sub numMarkedReg numMarkedReg oneP)))
            (.op (.copy s0 zeroP))) a1 a_mid 3 ∧
        a_mid.Bounded w ∧ BaseRegs n base a_mid ∧
        Modifies (Block.mk base (space n)).footprint a1.mem a_mid.mem ∧
        (∀ r : Fin rFib, r ≠ s0 → r ≠ numMarkedReg → a_mid.regs r = a1.regs r) ∧
        RawState.ofData n base a_mid = unmarkState st u := by
      by_cases hmk_pos : 0 < st.mark u
      · have hc_mk : (Cond.lt zeroP s1).Holds a1 := by
          simp only [Cond.Holds, ha1_z0, ha1_s1, hmk_pos]
        have hu_in_mk : u ∈ markedSet st := by
          simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hu_bds.1, by omega⟩
        have hnm_pos : 1 ≤ st.numMarked := by
          rw [hnm]
          exact Finset.card_pos.mpr ⟨u, hu_in_mk⟩
        let a_mid := (a1.write (base + 6 * n + u.val) 0).set numMarkedReg (st.numMarked - 1)
        have m1 : ExecWithin (B := .exact) w (.op (.store s0 zeroP)) a1
            (a1.write (base + 6 * n + u.val) 0) 1 := by
          simpa only [ha1_s0, ha1_z0] using
            (ExecWithin.store (B := .exact) (w := w) (x := a1) (a := s0) (s := zeroP))
        have m2 : ExecWithin w (.op (.exactBin .sub numMarkedReg numMarkedReg oneP))
            (a1.write (base + 6 * n + u.val) 0) a_mid 1 := by
          have hnm_w : (a1.write (base + 6 * n + u.val) 0).regs numMarkedReg = st.numMarked :=
            ha1_nm
          have ho1_w : (a1.write (base + 6 * n + u.val) 0).regs oneP = 1 := ha1_o1
          simpa only [hnm_w, ho1_w] using
            execWithin_exactSub (x := a1.write (base + 6 * n + u.val) 0)
              (d := numMarkedReg) (i := numMarkedReg) (j := oneP)
              (by rw [hnm_w, ho1_w]; exact hnm_pos)
              (by rw [hnm_w, ho1_w]; exact (hb1.1 numMarkedReg).of_le (by omega))
        have heb : ExecWithin (B := .exact) w
            (.branch (.lt zeroP s1)
              (.seq (.op (.store s0 zeroP)) (.op (.exactBin .sub numMarkedReg numMarkedReg oneP)))
              (.op (.copy s0 zeroP))) a1 a_mid 3 :=
          (ExecWithin.branch_pos hc_mk (m1.seq m2)).mono (by omega)
        have hst_mid : RawState.ofData n base a_mid =
            { st with
              par := Function.update st.par u 0
              mark := Function.update st.mark u 0
              numMarked := st.numMarked - 1 } := by
          simp only [a_mid, ofData_set_numMarked, ofData_write_mark, hst1]
        refine ⟨a_mid, heb, heb.bounded hb1,
          (hbr1.write_eq _ _).set_non_base (by decide) _,
          Modifies.write_of_owns ho_mk_u 0, ?_, ?_⟩
        · intro r _ hne_nm
          simp only [a_mid, Data.set_regs, Data.write_regs, Function.update_of_ne hne_nm]
        · have hmk1 : st.mark u = 1 := by have := hu_bds.2; omega
          rw [hst_mid]
          simp only [unmarkState, hmk1]
      · have hc_mk : ¬(Cond.lt zeroP s1).Holds a1 := by
          simp only [Cond.Holds, ha1_z0, ha1_s1]; omega
        let a_mid := a1.set s0 0
        have m1 : ExecWithin (B := .exact) w (.op (.copy s0 zeroP)) a1 a_mid 1 := by
          simpa only [ha1_z0] using
            (ExecWithin.copy (B := .exact) (w := w) (x := a1) (d := s0) (s := zeroP))
        have heb : ExecWithin (B := .exact) w
            (.branch (.lt zeroP s1)
              (.seq (.op (.store s0 zeroP)) (.op (.exactBin .sub numMarkedReg numMarkedReg oneP)))
              (.op (.copy s0 zeroP))) a1 a_mid 3 :=
          (ExecWithin.branch_neg hc_mk m1).mono (by omega)
        have hst_mid : RawState.ofData n base a_mid =
            { st with par := Function.update st.par u 0 } := by
          rw [ofData_set_scratch a1 (by decide : 17 ≤ s0.val) 0, hst1]
        refine ⟨a_mid, heb, heb.bounded hb1, hbr1.set_non_base (by decide) 0,
          Modifies.refl _ _, ?_, ?_⟩
        · intro r hne0 _
          simp only [a_mid, Data.set_regs, Function.update_of_ne hne0]
        · have hmk0 : st.mark u = 0 := by omega
          have hupd : Function.update st.mark u 0 = st.mark := by
            rw [← hmk0, Function.update_eq_self]
          rw [hst_mid]
          simp only [unmarkState, hmk0, Nat.sub_zero, hupd]
    obtain ⟨a_mid, he2, hb_mid, hbr_mid, hmod2, hregs_mid, hst_mid⟩ := hmark_step
    -- Step 3 (`a_mid → a_sc`, `t_sc` steps): `Scattering.unmark` makes `T_u` a valid root, and
    -- `scatterRootCode` places it.
    obtain ⟨h₁, hT₁, hsc₁⟩ := h.unmark
    have hmid_ic : a_mid.regs iterCur = T_u.root.val := by
      rw [hregs_mid iterCur (by decide) (by decide)]
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : iterCur ≠ s1),
        Function.update_of_ne (by decide : iterCur ≠ s0),
        Function.update_of_ne (by decide : iterCur ≠ iterNxt), hu_ic, u]
    have hmid_md : a_mid.regs maxDegReg = maxDeg := by
      rw [hregs_mid maxDegReg (by decide) (by decide)]
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : maxDegReg ≠ s1),
        Function.update_of_ne (by decide : maxDegReg ≠ s0),
        Function.update_of_ne (by decide : maxDegReg ≠ iterNxt), hmd]
    obtain ⟨a_sc, slotTrees_1, maxDeg_1, t_sc, he3, ht_sc, hb_sc, hbr_sc, hmod3, hlow_sc,
      hmd_sc, hc₁⟩ :=
      scatterRootCode_exec hb_mid hbr_mid (by rw [hst_mid]; exact h₁.placing hT₁) hmid_ic hmid_md
    rw [hst_mid] at hc₁
    obtain ⟨h₂, hback₂⟩ := h₁.step hc₁
    -- Step 4 (`a_sc → a_next`, 2 steps): `iterCur ← iterNxt; remReg ← remReg - oneP`
    have hsc_nxt : a_sc.regs iterNxt = nxtVal := by
      rw [hlow_sc iterNxt (by decide), hregs_mid iterNxt (by decide) (by decide)]
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : iterNxt ≠ s1),
        Function.update_of_ne (by decide : iterNxt ≠ s0), Function.update_self]
    have hsc_rem : a_sc.regs remReg = c_tl.length + 1 := by
      rw [hlow_sc remReg (by decide), hregs_mid remReg (by decide) (by decide)]
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : remReg ≠ s1),
        Function.update_of_ne (by decide : remReg ≠ s0),
        Function.update_of_ne (by decide : remReg ≠ iterNxt), hrem, List.length_cons]
    let a_next := (a_sc.set iterCur nxtVal).set remReg c_tl.length
    have s4_1 : ExecWithin (B := .exact) w (.op (.copy iterCur iterNxt)) a_sc
        (a_sc.set iterCur nxtVal) 1 := by
      simpa only [hsc_nxt] using
        (ExecWithin.copy (B := .exact) (w := w) (x := a_sc) (d := iterCur) (s := iterNxt))
    have s4_2 : ExecWithin w (.op (.exactBin .sub remReg remReg oneP))
        (a_sc.set iterCur nxtVal) a_next 1 := by
      have hrem_w : (a_sc.set iterCur nxtVal).regs remReg = c_tl.length + 1 := hsc_rem
      have ho1_w : (a_sc.set iterCur nxtVal).regs oneP = 1 := hbr_sc.regs_oneP
      simpa only [hrem_w, ho1_w, Nat.add_sub_cancel] using
        execWithin_exactSub (x := a_sc.set iterCur nxtVal) (d := remReg) (i := remReg) (j := oneP)
          (by rw [hrem_w, ho1_w]; omega)
          (by rw [hrem_w, ho1_w]; exact (hb_sc.1 remReg).of_le (by omega))
    have he_body : ExecWithin w childScatterBody a a_next (t_sc + 11) := by
      unfold childScatterBody
      exact (s1_1.seq <| s1_2.seq <| s1_3.seq <| s1_4.seq <| s1_5.seq <| s1_6.seq <|
        he2.seq <| he3.seq <| s4_1.seq s4_2).mono (by omega)
    have hb_next : a_next.Bounded w := s4_2.bounded (s4_1.bounded hb_sc)
    have hbr_next : BaseRegs n base a_next :=
      (hbr_sc.set_non_base (by decide) _).set_non_base (by decide) _
    have hst_next : RawState.ofData n base a_next = RawState.ofData n base a_sc := by
      simp only [a_next, ofData_set_scratch _ (by decide : 17 ≤ remReg.val),
        ofData_set_scratch _ (by decide : 17 ≤ iterCur.val)]
    have hic_next : ∀ y ∈ (c_tl.map FHTree.root).head?, a_next.regs iterCur = y.val := by
      intro y hy
      simp only [a_next, Data.set_regs, Function.update_of_ne (by decide : iterCur ≠ remReg),
        Function.update_self]
      exact RightChain.right_head h.chain y hy
    obtain ⟨b, slotTrees', maxDeg', t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hregs_tl,
      hmd_b, hc'⟩ :=
      scatterChildrenLoop_exec c_tl a_next slotTrees_1 maxDeg_1 hb_next hbr_next
        (by rw [hst_next]; exact h₂)
        (by simp only [a_next, Data.set_regs, Function.update_self])
        (by simp only [a_next, Data.set_regs,
              Function.update_of_ne (by decide : maxDegReg ≠ remReg),
              Function.update_of_ne (by decide : maxDegReg ≠ iterCur), hmd_sc])
        hic_next
    rw [hst_next] at hc'
    have he_all : ExecWithin w childScatterLoop a b (t_sc + 13 + t_tl) :=
      (ExecWithin.loop_iter hc he_body he_tl).mono (by omega)
    have hmod_all : Modifies (Block.mk base (space n)).footprint a.mem b.mem :=
      modifies_block_trans (modifies_block_trans (modifies_block_trans hmod1 hmod2) hmod3) hmod_tl
    refine ⟨b, slotTrees', maxDeg', t_sc + 13 + t_tl, he_all,
      by simp only [List.length_cons] at ht_sc ht_tl ⊢; omega,
      hb_b, hbr_b, hmod_all, ?_, hmd_b, (hback₂ hc').pre hsc₁ (.refl _)⟩
    · intro r hr hne_nm
      have ne_rem : r ≠ remReg := fun e => by subst e; change 30 < 30 at hr; omega
      have ne_ic : r ≠ iterCur := fun e => by subst e; change 31 < 30 at hr; omega
      have ne_in : r ≠ iterNxt := fun e => by subst e; change 32 < 30 at hr; omega
      have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
      have ne1 : r ≠ s1 := fun e => by subst e; change 36 < 30 at hr; omega
      rw [hregs_tl r hr hne_nm]
      simp only [a_next, Data.set_regs, Function.update_of_ne ne_rem, Function.update_of_ne ne_ic]
      rw [hlow_sc r (by omega), hregs_mid r ne0 hne_nm]
      simp only [a1, Data.set_regs, Data.write_regs, Function.update_of_ne ne1,
        Function.update_of_ne ne0, Function.update_of_ne ne_in]

private abbrev rootScatterBody : Code .exact rFib :=
  ram_exact[
    s0 ← rightBase + iterCur;
    iterNxt ← *s0;
    ⟪scatterRootCode⟫;
    iterCur ← iterNxt;
    remReg ← remReg - oneP
  ]

private abbrev rootScatterLoop : Code .exact rFib :=
  .loop (.lt zeroP remReg) rootScatterBody

/-- Phase A2 loop: walks the root trees `rest` along their `right` pointers and scatters each
into `cons`. The result is `Consolidated`; the forest reasoning is `Scattering.validRoot`,
`Scattering.placing` and `Scattering.step`. -/
private theorem scatterRootsLoop_exec {n sz base w : ℕ} {z : Fin n} :
    ∀ (rest : List (FHTree n)) (a : Data rFib) (slotTrees : List (FHTree n)) (maxDeg : ℕ),
      a.Bounded w → BaseRegs n base a →
      Scattering sz z false (RawState.ofData n base a) slotTrees rest maxDeg →
      a.regs remReg = rest.length →
      a.regs maxDegReg = maxDeg →
      (∀ y ∈ (rest.map FHTree.root).head?, a.regs iterCur = y.val) →
      ∃ b slotTrees' maxDeg' t,
        ExecWithin w rootScatterLoop a b t ∧
        t + slotCredit * slotTrees'.length ≤
          2 + 69 * rest.length + slotCredit * slotTrees.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        (∀ r : Fin rFib, r.val < 30 → b.regs r = a.regs r) ∧
        b.regs maxDegReg = maxDeg' ∧
        Consolidated sz (RawState.ofData n base a) (RawState.ofData n base b)
          (forestNodes (slotTrees ++ rest)) slotTrees' maxDeg'
  | [], a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, _ => by
    have hc : ¬(Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hbr.regs_zeroP, hrem, List.length_nil, Nat.lt_irrefl,
        not_false_eq_true]
    exact ⟨a, slotTrees, maxDeg, 2, ExecWithin.loop_exit hc, by omega, hb, hbr,
      Modifies.refl _ _, fun _ _ => rfl, hmd, h.done⟩
  | T_u :: r_tl, a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, hic => by
    set st := RawState.ofData n base a with hst_def
    have hfit_stop := hbr.fits_stop hb
    have hz0 : a.regs zeroP = 0 := hbr.regs_zeroP
    have hrb : a.regs rightBase = base + 4 * n := hbr.regs_rightBase
    have hc : (Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hz0, hrem, List.length_cons]; omega
    let u := T_u.root
    have hu_ic : a.regs iterCur = u.val := hic u rfl
    -- Step 1 (`a → a1`, 2 steps): `s0 ← rightBase + iterCur; iterNxt ← *s0`
    let nxtVal := st.right u
    let a1 := (a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal
    have s1_1 : ExecWithin w (.op (.exactBin .add s0 rightBase iterCur)) a
        (a.set s0 (base + 4 * n + u.val)) 1 := by
      have := u.isLt
      simpa only [hrb, hu_ic] using
        execWithin_exactAdd (x := a) (d := s0) (i := rightBase) (j := iterCur)
          (by rw [hrb, hu_ic]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s1_2 : ExecWithin (B := .exact) w (.op (.load iterNxt s0))
        (a.set s0 (base + 4 * n + u.val)) a1 1 := by
      have hm_r : a.mem (base + 4 * n + u.val) = nxtVal := rfl
      simpa only [a1, Data.set_mem, Data.set_regs, Function.update_self, hm_r] using
        (ExecWithin.load (B := .exact) (w := w) (x := a.set s0 (base + 4 * n + u.val))
          (d := iterNxt) (a := s0))
    have hb1 : a1.Bounded w := s1_2.bounded (s1_1.bounded hb)
    have hbr1 : BaseRegs n base a1 :=
      (hbr.set_non_base (by decide) _).set_non_base (by decide) _
    have hst1 : RawState.ofData n base a1 = st := by
      simp only [a1, ofData_set_scratch _ (by decide : 17 ≤ iterNxt.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val), ← hst_def]
    -- Step 2 (`a1 → a_sc`, `t_sc` steps): `scatterRootCode` places the valid root `T_u`
    obtain ⟨a_sc, slotTrees_1, maxDeg_1, t_sc, he2, ht_sc, hb_sc, hbr_sc, hmod2, hlow_sc,
      hmd_sc, hc₁⟩ :=
      scatterRootCode_exec hb1 hbr1 (by rw [hst1]; exact h.placing h.validRoot)
        (by simp only [a1, Data.set_regs, Function.update_of_ne (by decide : iterCur ≠ iterNxt),
              Function.update_of_ne (by decide : iterCur ≠ s0), hu_ic, u])
        (by simp only [a1, Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ iterNxt),
              Function.update_of_ne (by decide : maxDegReg ≠ s0), hmd])
    rw [hst1] at hc₁
    obtain ⟨h₂, hback₂⟩ := h.step hc₁
    -- Step 3 (`a_sc → a_next`, 2 steps): `iterCur ← iterNxt; remReg ← remReg - oneP`
    have hsc_nxt : a_sc.regs iterNxt = nxtVal := by
      rw [hlow_sc iterNxt (by decide)]
      simp only [a1, Data.set_regs, Function.update_self]
    have hsc_rem : a_sc.regs remReg = r_tl.length + 1 := by
      rw [hlow_sc remReg (by decide)]
      simp only [a1, Data.set_regs, Function.update_of_ne (by decide : remReg ≠ iterNxt),
        Function.update_of_ne (by decide : remReg ≠ s0), hrem, List.length_cons]
    let a_next := (a_sc.set iterCur nxtVal).set remReg r_tl.length
    have s3_1 : ExecWithin (B := .exact) w (.op (.copy iterCur iterNxt)) a_sc
        (a_sc.set iterCur nxtVal) 1 := by
      simpa only [hsc_nxt] using
        (ExecWithin.copy (B := .exact) (w := w) (x := a_sc) (d := iterCur) (s := iterNxt))
    have s3_2 : ExecWithin w (.op (.exactBin .sub remReg remReg oneP))
        (a_sc.set iterCur nxtVal) a_next 1 := by
      have hrem_w : (a_sc.set iterCur nxtVal).regs remReg = r_tl.length + 1 := hsc_rem
      have ho1_w : (a_sc.set iterCur nxtVal).regs oneP = 1 := hbr_sc.regs_oneP
      simpa only [hrem_w, ho1_w, Nat.add_sub_cancel] using
        execWithin_exactSub (x := a_sc.set iterCur nxtVal) (d := remReg) (i := remReg) (j := oneP)
          (by rw [hrem_w, ho1_w]; omega)
          (by rw [hrem_w, ho1_w]; exact (hb_sc.1 remReg).of_le (by omega))
    have he_body : ExecWithin w rootScatterBody a a_next (t_sc + 4) := by
      unfold rootScatterBody
      exact (s1_1.seq <| s1_2.seq <| he2.seq <| s3_1.seq s3_2).mono (by omega)
    have hb_next : a_next.Bounded w := s3_2.bounded (s3_1.bounded hb_sc)
    have hbr_next : BaseRegs n base a_next :=
      (hbr_sc.set_non_base (by decide) _).set_non_base (by decide) _
    have hst_next : RawState.ofData n base a_next = RawState.ofData n base a_sc := by
      simp only [a_next, ofData_set_scratch _ (by decide : 17 ≤ remReg.val),
        ofData_set_scratch _ (by decide : 17 ≤ iterCur.val)]
    have hic_next : ∀ y ∈ (r_tl.map FHTree.root).head?, a_next.regs iterCur = y.val := by
      intro y hy
      simp only [a_next, Data.set_regs, Function.update_of_ne (by decide : iterCur ≠ remReg),
        Function.update_self]
      exact RightChain.right_head h.chain y hy
    obtain ⟨b, slotTrees', maxDeg', t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hregs_tl,
      hmd_b, hc'⟩ :=
      scatterRootsLoop_exec r_tl a_next slotTrees_1 maxDeg_1 hb_next hbr_next
        (by rw [hst_next]; exact h₂)
        (by simp only [a_next, Data.set_regs, Function.update_self])
        (by simp only [a_next, Data.set_regs,
              Function.update_of_ne (by decide : maxDegReg ≠ remReg),
              Function.update_of_ne (by decide : maxDegReg ≠ iterCur), hmd_sc])
        hic_next
    rw [hst_next] at hc'
    have he_all : ExecWithin w rootScatterLoop a b (t_sc + 6 + t_tl) :=
      (ExecWithin.loop_iter hc he_body he_tl).mono (by omega)
    have hmod_all : Modifies (Block.mk base (space n)).footprint a.mem b.mem :=
      modifies_block_trans hmod2 hmod_tl
    refine ⟨b, slotTrees', maxDeg', t_sc + 6 + t_tl, he_all,
      by simp only [List.length_cons] at ht_sc ht_tl ⊢; omega,
      hb_b, hbr_b, hmod_all, ?_, hmd_b, hback₂ hc'⟩
    · intro r hr
      have ne_rem : r ≠ remReg := fun e => by subst e; change 30 < 30 at hr; omega
      have ne_ic : r ≠ iterCur := fun e => by subst e; change 31 < 30 at hr; omega
      have ne_in : r ≠ iterNxt := fun e => by subst e; change 32 < 30 at hr; omega
      have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
      rw [hregs_tl r hr]
      simp only [a_next, Data.set_regs, Function.update_of_ne ne_rem, Function.update_of_ne ne_ic]
      rw [hlow_sc r (by omega)]
      simp only [a1, Data.set_regs, Function.update_of_ne ne_in, Function.update_of_ne ne0]

/-! ## Phase B slot gathering (`gatherSlotsLoop_exec`) -/

private abbrev gatherSlotBody : Code .exact rFib :=
  ram_exact[
    s0 ← consBase + curDReg;
    s3 ← *s0;
    if zeroP < s3 then [
      *s0 ← zeroP;
      iterCur ← s3 - oneP;
      ⟪addRootAndUpdateMin iterCur⟫
    ] else [
      s0 ← zeroP
    ];
    curDReg ← curDReg + oneP
  ]

private abbrev gatherSlotsLoop : Code .exact rFib :=
  .loop (.lt curDReg maxDegReg) gatherSlotBody

/-- Phase B loop: scans `curD` up to `maxDeg + 1` (`curD + rem = maxDeg + 1`), clearing every
occupied `cons[curD]` and adding its tree to the root list with `addRootAndUpdateMin iterCur`. The
result is `Gathered`; the forest reasoning is `Gathering.take` and `Gathering.done`. -/
private theorem gatherSlotsLoop_exec {n sz base w maxDeg : ℕ} (rem : ℕ) :
    ∀ (a : Data rFib) (curD : ℕ) (slotTrees accRoots : List (FHTree n)),
      curD + rem = maxDeg + 1 →
      a.Bounded w → BaseRegs n base a →
      a.regs curDReg = curD →
      a.regs maxDegReg = maxDeg + 1 →
      Gathering sz (RawState.ofData n base a) accRoots slotTrees maxDeg →
      (∀ T ∈ slotTrees, curD ≤ T.deg) →
      ∃ b finalRoots t,
        ExecWithin w gatherSlotsLoop a b t ∧
        t + unitCredit * finalRoots.length ≤
          2 + 116 * rem + unitCredit * accRoots.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        (∀ r : Fin rFib, r.val < 30 → r ≠ minRootReg → r ≠ numRootsReg → b.regs r = a.regs r) ∧
        Gathered (RawState.ofData n base a) (RawState.ofData n base b)
          (forestNodes (accRoots ++ slotTrees)) finalRoots := by
  induction rem with
  | zero =>
    intro a curD slotTrees accRoots hsum hb hbr hcurD hmaxD h hge
    have hcur_eq : curD = maxDeg + 1 := by omega
    subst hcur_eq
    have hc : ¬(Cond.lt curDReg maxDegReg).Holds a := by
      simp only [Cond.Holds, hcurD, hmaxD, Nat.lt_irrefl, not_false_eq_true]
    obtain ⟨rfl, hG⟩ := h.done hge
    exact ⟨a, accRoots, 2, ExecWithin.loop_exit hc, by omega, hb, hbr,
      Modifies.refl _ _, fun _ _ _ _ => rfl, by simpa only [List.append_nil] using hG⟩
  | succ rem' ih =>
    intro a curD slotTrees accRoots hsum hb hbr hcurD hmaxD h hge
    set st := RawState.ofData n base a with hst_def
    have hfit_stop := hbr.fits_stop hb
    have hz0 : a.regs zeroP = 0 := hbr.regs_zeroP
    have ho1 : a.regs oneP = 1 := hbr.regs_oneP
    have hconsb : a.regs consBase = base + 8 * n := hbr.regs_consBase
    have hd_le_n : curD ≤ n := SlotInv.le_n h.table (by omega)
    have hc_loop : (Cond.lt curDReg maxDegReg).Holds a := by
      simp only [Cond.Holds, hcurD, hmaxD]; omega
    -- Load `s0 ← consBase + curDReg; s3 ← *s0` (2 steps)
    let a1 := (a.set s0 (base + 8 * n + curD)).set s3 (st.cons curD)
    have s_add0 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg)) a
        (a.set s0 (base + 8 * n + curD)) 1 := by
      simpa only [hconsb, hcurD] using
        execWithin_exactAdd (x := a) (d := s0) (i := consBase) (j := curDReg)
          (by rw [hconsb, hcurD]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s_ld0 : ExecWithin (B := .exact) w (.op (.load s3 s0))
        (a.set s0 (base + 8 * n + curD)) a1 1 := by
      have hm_c : a.mem (base + 8 * n + curD) = st.cons curD := by
        change a.mem _ = if curD ≤ n then a.mem _ else 0
        simp only [hd_le_n, ↓reduceIte]
      simpa only [a1, Data.set_mem, Data.set_regs, Function.update_self, hm_c] using
        (ExecWithin.load (B := .exact) (w := w) (x := a.set s0 (base + 8 * n + curD))
          (d := s3) (a := s0))
    have hb1 : a1.Bounded w := s_ld0.bounded (s_add0.bounded hb)
    have hbr1 : BaseRegs n base a1 :=
      (hbr.set_non_base (by decide) _).set_non_base (by decide) _
    have hst1 : RawState.ofData n base a1 = st := by
      simp only [a1, ofData_set_scratch _ (by decide : 17 ≤ s3.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val), hst_def]
    have ha1_s0 : a1.regs s0 = base + 8 * n + curD := by
      simp only [a1, Data.set_regs, Function.update_of_ne (by decide : s0 ≠ s3),
        Function.update_self]
    have ha1_s3 : a1.regs s3 = st.cons curD := by
      simp only [a1, Data.set_regs, Function.update_self]
    rcases h.table.lookup hd_le_n with ⟨hc0, hnone⟩ |
        ⟨idx, hidx, hslot_deg, hcons_eq, _, hno_other⟩
    · -- Unoccupied slot (`st.cons curD = 0`)
      have hc_br : ¬(Cond.lt zeroP s3).Holds a1 := by
        simp only [Cond.Holds, hbr1.regs_zeroP, ha1_s3, hc0, Nat.lt_irrefl,
          not_false_eq_true]
      let a2 := a1.set s0 0
      let a3 := a2.set curDReg (curD + 1)
      have he_br : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s3)
            (.seq (.op (.store s0 zeroP)) <|
             .seq (.op (.exactBin .sub iterCur s3 oneP)) (addRootAndUpdateMin iterCur))
            (.op (.copy s0 zeroP))) a1 a2 3 :=
        ExecWithin.branch_neg hc_br (by
          simpa only [hbr1.regs_zeroP] using
            (ExecWithin.copy (B := .exact) (w := w) (x := a1) (d := s0) (s := zeroP)))
      have ha2_curD : a2.regs curDReg = curD := by
        simp only [a2, a1, Data.set_regs, Function.update_of_ne (by decide : curDReg ≠ s0),
          Function.update_of_ne (by decide : curDReg ≠ s3), hcurD]
      have ha2_o1 : a2.regs oneP = 1 := by
        simp only [a2, a1, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ s0),
          Function.update_of_ne (by decide : oneP ≠ s3), ho1]
      have he_inc : ExecWithin w (.op (.exactBin .add curDReg curDReg oneP)) a2 a3 1 := by
        simpa only [ha2_curD, ha2_o1] using
          execWithin_exactAdd (x := a2) (d := curDReg) (i := curDReg) (j := oneP)
            (by rw [ha2_curD, ha2_o1]; exact hfit_stop.of_le (by simp only [space]; omega))
      have he_body : ExecWithin w gatherSlotBody a a3 6 := by
        unfold gatherSlotBody
        exact (s_add0.seq <| s_ld0.seq <| he_br.seq he_inc).mono (by omega)
      have hb3 : a3.Bounded w := he_inc.bounded (he_br.bounded hb1)
      have hbr3 : BaseRegs n base a3 :=
        (hbr1.set_non_base (by decide) _).set_non_base (by decide) _
      have hst3 : RawState.ofData n base a3 = st := by
        simp only [a3, a2, ofData_set_scratch _ (by decide : 17 ≤ curDReg.val),
          ofData_set_scratch _ (by decide : 17 ≤ s0.val), hst1]
      obtain ⟨b, finalRoots, t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hregs_tl, hG⟩ :=
        ih a3 (curD + 1) slotTrees accRoots (by omega) hb3 hbr3
          (by simp only [a3, Data.set_regs, Function.update_self])
          (by simp only [a3, a2, a1, Data.set_regs,
                Function.update_of_ne (by decide : maxDegReg ≠ curDReg),
                Function.update_of_ne (by decide : maxDegReg ≠ s0),
                Function.update_of_ne (by decide : maxDegReg ≠ s3), hmaxD])
          (by rw [hst3]; exact h) fun T hT => by
            have := hge T hT
            have := hnone T hT
            omega
      rw [hst3] at hG
      refine ⟨b, finalRoots, 6 + t_tl + 2, ExecWithin.loop_iter hc_loop he_body he_tl,
        by omega, hb_b, hbr_b, hmod_tl, ?_, hG⟩
      intro r hr hrm hrnr
      have ne_cd : r ≠ curDReg := fun e => by subst e; change 34 < 30 at hr; omega
      have ne_s0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
      have ne_s3 : r ≠ s3 := fun e => by subst e; change 38 < 30 at hr; omega
      rw [hregs_tl r hr hrm hrnr]
      simp only [a3, a2, a1, Data.set_regs, Function.update_of_ne ne_cd,
        Function.update_of_ne ne_s0, Function.update_of_ne ne_s3]
    · -- Occupied slot (`T_hit = slotTrees[idx]`)
      let T_hit := slotTrees[idx]
      let u := T_hit.root
      let slotRest := slotTrees.eraseIdx idx
      have hc_br : (Cond.lt zeroP s3).Holds a1 := by
        simp only [Cond.Holds, hbr1.regs_zeroP, ha1_s3, hcons_eq]; omega
      have ho_cons := owns_cons_addr (base := base) hd_le_n
      let a2 := a1.write (base + 8 * n + curD) 0
      let a3 := a2.set iterCur u.val
      have s_st0 : ExecWithin (B := .exact) w (.op (.store s0 zeroP)) a1 a2 1 := by
        simpa only [ha1_s0, hbr1.regs_zeroP] using
          (ExecWithin.store (B := .exact) (w := w) (x := a1) (a := s0) (s := zeroP))
      have ha2_s3 : a2.regs s3 = u.val + 1 := by
        simp only [a2, Data.write_regs, ha1_s3, hcons_eq]; rfl
      have ha2_o1 : a2.regs oneP = 1 := hbr1.regs_oneP
      have s_sub0 : ExecWithin w (.op (.exactBin .sub iterCur s3 oneP)) a2 a3 1 := by
        have := u.isLt
        simpa only [ha2_s3, ha2_o1, Nat.add_sub_cancel] using
          execWithin_exactSub (x := a2) (d := iterCur) (i := s3) (j := oneP)
            (by rw [ha2_s3, ha2_o1]; omega)
            (by rw [ha2_s3, ha2_o1]; exact hfit_stop.of_le (by simp only [space]; omega))
      have hb3 : a3.Bounded w := s_sub0.bounded (s_st0.bounded hb1)
      have hbr3 : BaseRegs n base a3 := (hbr1.write_eq _ _).set_non_base (by decide) _
      have hst3 : RawState.ofData n base a3 =
          { st with cons := Function.update st.cons curD 0 } := by
        have hc_wr := ofData_write_cons (base := base) hd_le_n a1 0
        rw [hst1] at hc_wr
        exact (ofData_set_scratch a2 (by decide : 17 ≤ iterCur.val) u.val).trans hc_wr
      -- `Gathering.take`: the tree can be added to the root list.
      obtain ⟨hroot, hnr, hnext⟩ := h.take hidx hslot_deg hd_le_n hno_other hst3
      have ha3_ic : a3.regs iterCur = u.val := by
        simp only [a3, Data.set_regs, Function.update_self]
      obtain ⟨a4, he_add, hbr4, hmod_add, hadd⟩ :=
        addRootAndUpdateMin_exec hb3 hbr3
          ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
          ha3_ic hroot hnr
      obtain ⟨h₂, hback⟩ := hnext hadd
      have hb4 : a4.Bounded w := he_add.bounded hb3
      let a5 := a4.set curDReg (curD + 1)
      have ha4_cd : a4.regs curDReg = curD := by
        rw [he_add.regs_eq (addRootAndUpdateMin_preserves (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide))]
        simp only [a3, a2, a1, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : curDReg ≠ iterCur),
          Function.update_of_ne (by decide : curDReg ≠ s3),
          Function.update_of_ne (by decide : curDReg ≠ s0), hcurD]
      have ha4_o1 : a4.regs oneP = 1 := hbr4.regs_oneP
      have he_inc : ExecWithin w (.op (.exactBin .add curDReg curDReg oneP)) a4 a5 1 := by
        simpa only [ha4_cd, ha4_o1] using
          execWithin_exactAdd (x := a4) (d := curDReg) (i := curDReg) (j := oneP)
            (by rw [ha4_cd, ha4_o1]; exact hfit_stop.of_le (by simp only [space]; omega))
      have he_br : ExecWithin w
          (.branch (.lt zeroP s3)
            (.seq (.op (.store s0 zeroP)) <|
             .seq (.op (.exactBin .sub iterCur s3 oneP)) (addRootAndUpdateMin iterCur))
            (.op (.copy s0 zeroP))) a1 a4 31 :=
        (ExecWithin.branch_pos hc_br (s_st0.seq (s_sub0.seq he_add))).mono (by omega)
      have he_body : ExecWithin w gatherSlotBody a a5 34 := by
        unfold gatherSlotBody
        exact (s_add0.seq <| s_ld0.seq <| he_br.seq he_inc).mono (by omega)
      have hb5 : a5.Bounded w := he_inc.bounded hb4
      have hbr5 : BaseRegs n base a5 := hbr4.set_non_base (by decide) _
      have hst5 : RawState.ofData n base a5 = RawState.ofData n base a4 :=
        ofData_set_scratch a4 (by decide : 17 ≤ curDReg.val) (curD + 1)
      have hmod5 : Modifies (Block.mk base (space n)).footprint a.mem a5.mem :=
        modifies_block_trans (Modifies.write_of_owns ho_cons 0) hmod_add
      obtain ⟨b, finalRoots, t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hregs_tl, hG⟩ :=
        ih a5 (curD + 1) slotRest (T_hit :: accRoots) (by omega) hb5 hbr5
          (by simp only [a5, Data.set_regs, Function.update_self])
          (by
            simp only [a5, Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ curDReg)]
            rw [he_add.regs_eq (addRootAndUpdateMin_preserves (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide))]
            simp only [a3, a2, a1, Data.set_regs, Data.write_regs,
              Function.update_of_ne (by decide : maxDegReg ≠ iterCur),
              Function.update_of_ne (by decide : maxDegReg ≠ s3),
              Function.update_of_ne (by decide : maxDegReg ≠ s0), hmaxD])
          (by rw [hst5]; exact h₂) fun R hR => by
            have := hge R (List.mem_of_mem_eraseIdx hR)
            have := hno_other R hR
            omega
      rw [hst5] at hG
      have he_all : ExecWithin w gatherSlotsLoop a b (34 + t_tl + 2) :=
        ExecWithin.loop_iter hc_loop he_body he_tl
      refine ⟨b, finalRoots, 34 + t_tl + 2, he_all,
        by simp only [List.length_cons, unitCredit] at ht_tl ⊢; omega,
        hb_b, hbr_b, modifies_block_trans hmod5 hmod_tl, ?_, hback hG⟩
      intro r hr hrm hrnr
      have ne_cd : r ≠ curDReg := fun e => by subst e; change 34 < 30 at hr; omega
      have ne_ic : r ≠ iterCur := fun e => by subst e; change 31 < 30 at hr; omega
      have ne_s0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
      have ne_s1 : r ≠ s1 := fun e => by subst e; change 36 < 30 at hr; omega
      have ne_s2 : r ≠ s2 := fun e => by subst e; change 37 < 30 at hr; omega
      have ne_s3 : r ≠ s3 := fun e => by subst e; change 38 < 30 at hr; omega
      have ne_s4 : r ≠ s4 := fun e => by subst e; change 39 < 30 at hr; omega
      have ne_s5 : r ≠ s5 := fun e => by subst e; change 40 < 30 at hr; omega
      rw [hregs_tl r hr hrm hrnr]
      simp only [a5, Data.set_regs, Function.update_of_ne ne_cd]
      rw [he_add.regs_eq (addRootAndUpdateMin_preserves ne_s0 ne_s1 ne_s2 ne_s3 ne_s4 ne_s5
        hrm hrnr)]
      simp only [a3, a2, a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne ne_ic, Function.update_of_ne ne_s3, Function.update_of_ne ne_s0]

/-! ## `extractMinCode` correctness and `O(log n)` amortized bound -/


/-! ## `extractMinCode` correctness and `O(log n)` amortized bound -/

private theorem execWithin_seq₂ {B : Basis} {r w t₁ t₂ : ℕ} {a b c : Code B r}
    {x y z : Data r} (h₁ : ExecWithin w (a.seq b) x y t₁) (h₂ : ExecWithin w c y z t₂) :
    ExecWithin w (a.seq (b.seq c)) x z (t₁ + t₂) := by
  rcases h₁ with ⟨_, hm₁, ea⟩
  cases ea with | seq ha hb =>
  rcases h₂ with ⟨_, hm₂, hc⟩
  exact ⟨_, by omega, ha.seq (hb.seq hc)⟩

private theorem execWithin_seq₃ {B : Basis} {r w t₁ t₂ : ℕ} {a b c d : Code B r}
    {x y z : Data r} (h₁ : ExecWithin w (a.seq (b.seq c)) x y t₁) (h₂ : ExecWithin w d y z t₂) :
    ExecWithin w (a.seq (b.seq (c.seq d))) x z (t₁ + t₂) := by
  rcases h₁ with ⟨_, hm₁, ea⟩
  cases ea with | seq ha ebc =>
  cases ebc with | seq hb hc =>
  rcases h₂ with ⟨_, hm₂, hd⟩
  exact ⟨_, by omega, ha.seq (hb.seq (hc.seq hd))⟩

/-- `extractMinCode` implements `.extractMin` on `FibInv` within
`410 * (Nat.log 2 (IndexedMinPQ.dom s).card + 1)` amortized instructions
(`t + potential y ≤ 410 * (Nat.log 2 (IndexedMinPQ.dom s).card + 1) + potential x`). The forest
reasoning is that of the record heap: `FibRawInv.detach` splits the heap at its minimum root, the
three loops produce `Consolidated`, `Consolidated` and `Gathered`, and `Detached.finish`
reassembles `FibRawInv`. -/
theorem extractMinCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (hinv : FibInv n K_max w base s x) :
    ∃ y t, ExecWithin w extractMinCode x y t ∧
      code.decode (n := n) (K_max := K_max) .extractMin y.regs =
        some ((indexedMinPQSpec n K_max).stepFn s .extractMin).2 ∧
      FibInv n K_max w base ((indexedMinPQSpec n K_max).stepFn s .extractMin).1 y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤
        410 * (Nat.log 2 (IndexedMinPQ.dom s).card + 1) + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  set st := RawState.ofData n base x with hst_def
  have hfit_stop := hbr.fits_stop hb
  have hz0 : x.regs zeroP = 0 := hbr.regs_zeroP
  have ho1 : x.regs oneP = 1 := hbr.regs_oneP
  by_cases hm0 : st.minRoot = 0
  · -- Empty heap (`minRoot = 0`)
    have hc : (Cond.eq minRootReg zeroP).Holds x := by
      simp only [Cond.Holds, hz0]; exact hm0
    let y := x.set outFlag 0
    have he : ExecWithin w extractMinCode x y 2 := by
      unfold extractMinCode
      exact ExecWithin.branch_pos hc (by
        simpa only [hz0] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := outFlag) (s := zeroP)))
    obtain ⟨_, hfind⟩ := hraw.findMin_eq_none hm0
    have hpot : potential y = potential x :=
      potential_supported fun i hi => by
        have hne : i ≠ outFlag := fun e => by subst e; cases hi
        simp only [y, Data.set_regs, Function.update_of_ne hne]
    refine ⟨y, 2, he, ?_, ?_, Modifies.refl _ _, by omega⟩
    · simp only [PQCode.decode, code, indexedMinPQSpec, IndexedMinPQ.step,
        StateTransitionSpec.stepFn,
        hfind, y, Data.set_regs, Function.update_self, ↓reduceIte]
    · simp only [indexedMinPQSpec, IndexedMinPQ.step, StateTransitionSpec.stepFn, hfind]
      exact ⟨he.bounded hb, hbr.set_non_base (by decide) 0,
        (ofData_set_scratch x (by decide : 17 ≤ outFlag.val) 0).symm ▸ hraw⟩
  · -- Non-empty heap (`st.minRoot = z.val + 1`)
    have hc_top : ¬(Cond.eq minRootReg zeroP).Holds x := by
      simp only [Cond.Holds, hz0]; exact hm0
    rcases FibonacciHeap.minRoot_cases hraw with h0 | ⟨z, -, hmin_z, -⟩
    · exact absurd h0 hm0
    -- `FibRawInv.detach` splits the heap at its minimum root `z`.
    obtain ⟨cs, E, hD⟩ := FibonacciHeap.FibRawInv.detach hraw hmin_z
    have hz_lt := z.isLt
    have hfind := hD.findMin
    have hz_dom : z ∈ IndexedMinPQ.dom s := IndexedMinPQ.findMin_mem_dom hfind
    have hsz_pos : 1 ≤ st.sz := by
      have : 0 < (IndexedMinPQ.dom s).card := Finset.card_pos.mpr ⟨z, hz_dom⟩
      rw [hD.sz]
      omega
    -- Preamble (`x → x_pre`, 13 instructions)
    have hbb : x.regs baseReg = base := hbr.regs_baseReg
    have hcb : x.regs childBase = base + 2 * n := hbr.regs_childBase
    have hrb : x.regs rightBase = base + 4 * n := hbr.regs_rightBase
    have hdb : x.regs degBase = base + 5 * n := hbr.regs_degBase
    have hinb : x.regs inBase = base + 7 * n := hbr.regs_inBase
    have ho_in_z := owns_arr_addr (base := base) (k := 7) (by decide) hz_lt
    let p1 := x.set zReg z.val
    let p2 := (p1.set outFlag 1).set outV z.val
    let p3 := (p2.set s0 (base + z.val)).set outK (st.key z)
    let p4 := ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0).set szReg
      (st.sz - 1)
    let p5 := ((p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z)).set maxDegReg 0
    let x_pre := (p5.set s0 (base + 5 * n + z.val)).set remReg (st.deg z)
    have ep1 : ExecWithin w (.op (.exactBin .sub zReg minRootReg oneP)) x p1 1 := by
      have hm_x : x.regs minRootReg = z.val + 1 := hmin_z
      simpa only [hm_x, ho1, Nat.add_sub_cancel] using
        execWithin_exactSub (x := x) (d := zReg) (i := minRootReg) (j := oneP)
          (by rw [hm_x, ho1]; omega)
          (by rw [hm_x, ho1]; exact hfit_stop.of_le (by simp only [space]; omega))
    have ep2 : ExecWithin (B := .exact) w
        (.seq (.op (.copy outFlag oneP)) (.op (.copy outV zReg))) p1 p2 2 := by
      have s_of : ExecWithin (B := .exact) w (.op (.copy outFlag oneP)) p1 (p1.set outFlag 1) 1 :=
        by simpa only [p1, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ zReg), ho1]
             using (ExecWithin.copy (B := .exact) (w := w) (x := p1) (d := outFlag) (s := oneP))
      have s_ov : ExecWithin (B := .exact) w (.op (.copy outV zReg)) (p1.set outFlag 1) p2 1 := by
        simpa only [p2, p1, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ outFlag),
          Function.update_self] using
          (ExecWithin.copy (B := .exact) (w := w) (x := p1.set outFlag 1) (d := outV) (s := zReg))
      exact (s_of.seq s_ov).mono (by omega)
    have ep3 : ExecWithin w
        (.seq (.op (.exactBin .add s0 baseReg zReg)) (.op (.load outK s0))) p2 p3 2 := by
      have hb_p2 : p2.regs baseReg = base := hbb
      have hz_p2 : p2.regs zReg = z.val := by
        simp only [p2, p1, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ outV),
          Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
      have s_a : ExecWithin w (.op (.exactBin .add s0 baseReg zReg)) p2
          (p2.set s0 (base + z.val)) 1 := by
        simpa only [hb_p2, hz_p2] using
          execWithin_exactAdd (x := p2) (d := s0) (i := baseReg) (j := zReg)
            (by rw [hb_p2, hz_p2]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s_l : ExecWithin (B := .exact) w (.op (.load outK s0))
          (p2.set s0 (base + z.val)) p3 1 := by
        have hkz : x.mem (base + z.val) = st.key z := rfl
        simpa only [p3, p2, p1, Data.set_mem, Data.set_regs, Function.update_self, hkz] using
          (ExecWithin.load (B := .exact) (w := w) (x := p2.set s0 (base + z.val))
            (d := outK) (a := s0))
      exact (s_a.seq s_l).mono (by omega)
    have ep4 : ExecWithin w
        (.seq (.op (.exactBin .add s0 inBase zReg)) <|
         .seq (.op (.store s0 zeroP))
              (.op (.exactBin .sub szReg szReg oneP))) p3 p4 3 := by
      have hin_p3 : p3.regs inBase = base + 7 * n := hinb
      have hz_p3 : p3.regs zReg = z.val := by
        simp only [p3, p2, p1, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ outK),
          Function.update_of_ne (by decide : zReg ≠ s0),
          Function.update_of_ne (by decide : zReg ≠ outV),
          Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
      have s_a : ExecWithin w (.op (.exactBin .add s0 inBase zReg)) p3
          (p3.set s0 (base + 7 * n + z.val)) 1 := by
        simpa only [hin_p3, hz_p3] using
          execWithin_exactAdd (x := p3) (d := s0) (i := inBase) (j := zReg)
            (by rw [hin_p3, hz_p3]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s_st : ExecWithin (B := .exact) w (.op (.store s0 zeroP))
          (p3.set s0 (base + 7 * n + z.val))
          ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0) 1 := by
        have hz0_p3 : (p3.set s0 (base + 7 * n + z.val)).regs zeroP = 0 := hz0
        simpa only [Data.set_regs, Function.update_self, hz0_p3] using
          (ExecWithin.store (B := .exact) (w := w) (x := p3.set s0 (base + 7 * n + z.val))
            (a := s0) (s := zeroP))
      have hsz_w : ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0).regs
          szReg = st.sz := rfl
      have ho1_w : ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0).regs
          oneP = 1 := ho1
      have hsz_le_n : st.sz ≤ n := hraw.bounds.1
      have s_sub : ExecWithin w (.op (.exactBin .sub szReg szReg oneP))
          ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0) p4 1 := by
        simpa only [p4, hsz_w, ho1_w] using
          execWithin_exactSub
            (x := (p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0)
            (d := szReg) (i := szReg) (j := oneP)
            (by rw [hsz_w, ho1_w]; omega)
            (by rw [hsz_w, ho1_w]; exact hfit_stop.of_le (by simp only [space]; omega))
      exact (s_a.seq (s_st.seq s_sub)).mono (by omega)
    have ep5 : ExecWithin w
        (.seq (.op (.exactBin .add s0 rightBase zReg)) <|
         .seq (.op (.load pReg s0))
              (.op (.copy maxDegReg zeroP))) p4 p5 3 := by
      have hr_p4 : p4.regs rightBase = base + 4 * n := hrb
      have hz_p4 : p4.regs zReg = z.val := by
        simp only [p4, p3, p2, p1, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : zReg ≠ szReg),
          Function.update_of_ne (by decide : zReg ≠ outK),
          Function.update_of_ne (by decide : zReg ≠ s0),
          Function.update_of_ne (by decide : zReg ≠ outV),
          Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
      have s_a : ExecWithin w (.op (.exactBin .add s0 rightBase zReg)) p4
          (p4.set s0 (base + 4 * n + z.val)) 1 := by
        simpa only [hr_p4, hz_p4] using
          execWithin_exactAdd (x := p4) (d := s0) (i := rightBase) (j := zReg)
            (by rw [hr_p4, hz_p4]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s_l : ExecWithin (B := .exact) w (.op (.load pReg s0))
          (p4.set s0 (base + 4 * n + z.val))
          ((p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z)) 1 := by
        have hrz : (p4.set s0 (base + 4 * n + z.val)).mem (base + 4 * n + z.val) =
            st.right z := by
          simp only [p4, p3, p2, p1, Data.set_mem, Data.write_mem,
            Function.update_of_ne (by omega : base + 4 * n + z.val ≠ base + 7 * n + z.val)]
          rfl
        simpa only [Data.set_regs, Function.update_self, hrz] using
          (ExecWithin.load (B := .exact) (w := w) (x := p4.set s0 (base + 4 * n + z.val))
            (d := pReg) (a := s0))
      have s_c : ExecWithin (B := .exact) w (.op (.copy maxDegReg zeroP))
          ((p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z)) p5 1 := by
        have hz0_p4 : ((p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z)).regs zeroP =
            0 := hz0
        simpa only [p5, hz0_p4] using
          (ExecWithin.copy (B := .exact) (w := w)
            (x := (p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z))
            (d := maxDegReg) (s := zeroP))
      exact (s_a.seq (s_l.seq s_c)).mono (by omega)
    have ep6 : ExecWithin w
        (.seq (.op (.exactBin .add s0 degBase zReg)) (.op (.load remReg s0))) p5 x_pre 2 := by
      have hd_p5 : p5.regs degBase = base + 5 * n := hdb
      have hz_p5 : p5.regs zReg = z.val := by
        simp only [p5, p4, p3, p2, p1, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : zReg ≠ maxDegReg),
          Function.update_of_ne (by decide : zReg ≠ pReg),
          Function.update_of_ne (by decide : zReg ≠ szReg),
          Function.update_of_ne (by decide : zReg ≠ outK),
          Function.update_of_ne (by decide : zReg ≠ s0),
          Function.update_of_ne (by decide : zReg ≠ outV),
          Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
      have s_a : ExecWithin w (.op (.exactBin .add s0 degBase zReg)) p5
          (p5.set s0 (base + 5 * n + z.val)) 1 := by
        simpa only [hd_p5, hz_p5] using
          execWithin_exactAdd (x := p5) (d := s0) (i := degBase) (j := zReg)
            (by rw [hd_p5, hz_p5]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s_l : ExecWithin (B := .exact) w (.op (.load remReg s0))
          (p5.set s0 (base + 5 * n + z.val)) x_pre 1 := by
        have hdz : (p5.set s0 (base + 5 * n + z.val)).mem (base + 5 * n + z.val) =
            st.deg z := by
          simp only [p5, p4, p3, p2, p1, Data.set_mem, Data.write_mem,
            Function.update_of_ne (by omega : base + 5 * n + z.val ≠ base + 7 * n + z.val)]
          rfl
        simpa only [x_pre, Data.set_regs, Function.update_self, hdz] using
          (ExecWithin.load (B := .exact) (w := w) (x := p5.set s0 (base + 5 * n + z.val))
            (d := remReg) (a := s0))
      exact (s_a.seq s_l).mono (by omega)
    have hb_pre : x_pre.Bounded w :=
      ep6.bounded (ep5.bounded (ep4.bounded (ep3.bounded (ep2.bounded (ep1.bounded hb)))))
    have hbr_pre : BaseRegs n base x_pre :=
      (((((((((((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
        (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
        (by decide) _).write_eq _ _).set_non_base (by decide) _).set_non_base
        (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
        (by decide) _ |>.set_non_base (by decide) _
    have hmod_pre : Modifies (Block.mk base (space n)).footprint x.mem x_pre.mem :=
      Modifies.write_of_owns ho_in_z 0
    have hst_pre : RawState.ofData n base x_pre =
        { st with inHeap := Function.update st.inHeap z 0, sz := st.sz - 1 } := by
      have hin_wr : RawState.ofData n base
          ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0) =
          { st with inHeap := Function.update st.inHeap z 0 } := by
        have h := ofData_write_inHeap (base := base) (p3.set s0 (base + 7 * n + z.val)) z 0
        have hp3_eq : RawState.ofData n base (p3.set s0 (base + 7 * n + z.val)) = st := by
          simp only [p3, p2, p1, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
            ofData_set_scratch _ (by decide : 17 ≤ outK.val),
            ofData_set_scratch _ (by decide : 17 ≤ outV.val),
            ofData_set_scratch _ (by decide : 17 ≤ outFlag.val),
            ofData_set_scratch _ (by decide : 17 ≤ zReg.val), hst_def]
        rw [hp3_eq] at h
        exact h
      simp only [x_pre, p5, p4, ofData_set_scratch _ (by decide : 17 ≤ remReg.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val),
        ofData_set_scratch _ (by decide : 17 ≤ maxDegReg.val),
        ofData_set_scratch _ (by decide : 17 ≤ pReg.val),
        ofData_set_sz, hin_wr]
    -- Phase A1 (`x_pre → x_A1`): the children of `z`, from `Detached.scatterChildren`
    have hA1 : ∃ x_A1 slotTrees_1 maxDeg_1 t_A1,
        ExecWithin w
          (.branch (.lt zeroP remReg)
            (.seq (.op (.exactBin .add s0 childBase zReg)) <|
             .seq (.op (.load s1 s0)) <|
             .seq (.op (.exactBin .sub iterCur s1 oneP)) childScatterLoop)
            (.op (.copy s0 zeroP))) x_pre x_A1 t_A1 ∧
        t_A1 + slotCredit * slotTrees_1.length ≤ 7 + 76 * cs.length ∧
        x_A1.Bounded w ∧ BaseRegs n base x_A1 ∧
        Modifies (Block.mk base (space n)).footprint x_pre.mem x_A1.mem ∧
        (∀ r : Fin rFib, r.val < 30 → r ≠ numMarkedReg → x_A1.regs r = x_pre.regs r) ∧
        x_A1.regs maxDegReg = maxDeg_1 ∧
        Consolidated (forestNodes (cs ++ E)).length (detachState st z)
          (RawState.ofData n base x_A1) (forestNodes ([] ++ cs)) slotTrees_1 maxDeg_1 := by
      have hz_pre0 : x_pre.regs zeroP = 0 := hbr_pre.regs_zeroP
      have hrem_pre : x_pre.regs remReg = st.deg z := by
        simp only [x_pre, Data.set_regs, Function.update_self]
      cases cs with
      | nil =>
        have hc_rem : ¬(Cond.lt zeroP remReg).Holds x_pre := by
          simp only [Cond.Holds, hz_pre0, hrem_pre, hD.deg, List.length_nil, Nat.lt_irrefl,
            not_false_eq_true]
        let x_A1 := x_pre.set s0 0
        have he_br : ExecWithin (B := .exact) w
            (.branch (.lt zeroP remReg)
              (.seq (.op (.exactBin .add s0 childBase zReg)) <|
               .seq (.op (.load s1 s0)) <|
               .seq (.op (.exactBin .sub iterCur s1 oneP)) childScatterLoop)
              (.op (.copy s0 zeroP))) x_pre x_A1 3 :=
          ExecWithin.branch_neg hc_rem (by
            simpa only [hz_pre0] using
              (ExecWithin.copy (B := .exact) (w := w) (x := x_pre) (d := s0) (s := zeroP)))
        have hst_A1 : RawState.ofData n base x_A1 = RawState.ofData n base x_pre :=
          ofData_set_scratch x_pre (by decide : 17 ≤ s0.val) 0
        refine ⟨x_A1, [], 0, 3, he_br, by simp only [List.length_nil, Nat.mul_zero]; omega,
          he_br.bounded hb_pre,
          hbr_pre.set_non_base (by decide) 0, Modifies.refl _ _,
          fun r hr _ => by
            have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
            simp only [x_A1, Data.set_regs, Function.update_of_ne ne0],
          by simp only [x_A1, x_pre, p5, Data.set_regs,
               Function.update_of_ne (by decide : maxDegReg ≠ s0),
               Function.update_of_ne (by decide : maxDegReg ≠ remReg), Function.update_self], ?_⟩
        rw [hst_A1, hst_pre]
        exact hD.scatterChildren.done
      | cons C₀ cs₀ =>
        let h_c := C₀.root
        have hcz : st.child z = h_c.val + 1 := hD.child h_c rfl
        have hc_rem : (Cond.lt zeroP remReg).Holds x_pre := by
          simp only [Cond.Holds, hz_pre0, hrem_pre, hD.deg, List.length_cons]
          omega
        let x_c0 := ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)).set iterCur
          h_c.val
        have hz_pre : x_pre.regs zReg = z.val := by
          simp only [x_pre, p5, p4, p3, p2, p1, Data.set_regs, Data.write_regs,
            Function.update_of_ne (by decide : zReg ≠ remReg),
            Function.update_of_ne (by decide : zReg ≠ maxDegReg),
            Function.update_of_ne (by decide : zReg ≠ pReg),
            Function.update_of_ne (by decide : zReg ≠ szReg),
            Function.update_of_ne (by decide : zReg ≠ outK),
            Function.update_of_ne (by decide : zReg ≠ s0),
            Function.update_of_ne (by decide : zReg ≠ outV),
            Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
        have s_ca : ExecWithin w (.op (.exactBin .add s0 childBase zReg)) x_pre
            (x_pre.set s0 (base + 2 * n + z.val)) 1 := by
          simpa only [hbr_pre.regs_childBase, hz_pre] using
            execWithin_exactAdd (x := x_pre) (d := s0) (i := childBase) (j := zReg)
              (by rw [hbr_pre.regs_childBase, hz_pre]
                  exact hfit_stop.of_le (by simp only [space]; omega))
        have s_cl : ExecWithin (B := .exact) w (.op (.load s1 s0))
            (x_pre.set s0 (base + 2 * n + z.val))
            ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)) 1 := by
          have hcz_mem : (x_pre.set s0 (base + 2 * n + z.val)).mem (base + 2 * n + z.val) =
              h_c.val + 1 := by
            have : (RawState.ofData n base x_pre).child z = st.child z := by rw [hst_pre]
            exact this.trans hcz
          simpa only [Data.set_regs, Function.update_self, hcz_mem] using
            (ExecWithin.load (B := .exact) (w := w) (x := x_pre.set s0 (base + 2 * n + z.val))
              (d := s1) (a := s0))
        have s_cs : ExecWithin w (.op (.exactBin .sub iterCur s1 oneP))
            ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)) x_c0 1 := by
          have := h_c.isLt
          have hs1_v : ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)).regs s1 =
              h_c.val + 1 := by simp only [Data.set_regs, Function.update_self]
          have ho1_v : ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)).regs oneP =
              1 := ho1
          simpa only [x_c0, hs1_v, ho1_v, Nat.add_sub_cancel] using
            execWithin_exactSub
              (x := (x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1))
              (d := iterCur) (i := s1) (j := oneP)
              (by rw [hs1_v, ho1_v]; omega)
              (by rw [hs1_v, ho1_v]; exact hfit_stop.of_le (by simp only [space]; omega))
        have hb_c0 : x_c0.Bounded w := s_cs.bounded (s_cl.bounded (s_ca.bounded hb_pre))
        have hbr_c0 : BaseRegs n base x_c0 :=
          ((hbr_pre.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
            (by decide) _
        have hst_c0 : RawState.ofData n base x_c0 = RawState.ofData n base x_pre := by
          simp only [x_c0, ofData_set_scratch _ (by decide : 17 ≤ iterCur.val),
            ofData_set_scratch _ (by decide : 17 ≤ s1.val),
            ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
        obtain ⟨x_A1, slotTrees_1, maxDeg_1, t_sc1, he_sc1, ht_sc1, hb_A1, hbr_A1, hmod_sc1,
          hregs_sc1, hmd_sc1, hc_sc1⟩ :=
          scatterChildrenLoop_exec (C₀ :: cs₀) x_c0 [] 0 hb_c0 hbr_c0
            (by rw [hst_c0, hst_pre]; exact hD.scatterChildren)
            (by simp only [x_c0, x_pre, Data.set_regs,
                  Function.update_of_ne (by decide : remReg ≠ iterCur),
                  Function.update_of_ne (by decide : remReg ≠ s1),
                  Function.update_of_ne (by decide : remReg ≠ s0),
                  Function.update_self, hD.deg])
            (by simp only [x_c0, x_pre, p5, Data.set_regs,
                  Function.update_of_ne (by decide : maxDegReg ≠ iterCur),
                  Function.update_of_ne (by decide : maxDegReg ≠ s1),
                  Function.update_of_ne (by decide : maxDegReg ≠ remReg),
                  Function.update_of_ne (by decide : maxDegReg ≠ s0), Function.update_self])
            (fun y hy => by
              cases hy
              simp only [x_c0, Data.set_regs, Function.update_self, h_c])
        have he_br : ExecWithin w
            (.branch (.lt zeroP remReg)
              (.seq (.op (.exactBin .add s0 childBase zReg)) <|
               .seq (.op (.load s1 s0)) <|
               .seq (.op (.exactBin .sub iterCur s1 oneP)) childScatterLoop)
              (.op (.copy s0 zeroP))) x_pre x_A1 (t_sc1 + 4) :=
          (ExecWithin.branch_pos hc_rem (s_ca.seq (s_cl.seq (s_cs.seq he_sc1)))).mono (by omega)
        rw [hst_c0, hst_pre] at hc_sc1
        refine ⟨x_A1, slotTrees_1, maxDeg_1, t_sc1 + 4, he_br,
          by simp only [slotCredit, List.length_nil] at ht_sc1 ⊢; omega,
          hb_A1, hbr_A1, hmod_sc1, ?_, hmd_sc1, hc_sc1⟩
        intro r hr hrnm
        have ne_ic : r ≠ iterCur := fun e => by subst e; change 31 < 30 at hr; omega
        have ne_s1 : r ≠ s1 := fun e => by subst e; change 36 < 30 at hr; omega
        have ne_s0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
        rw [hregs_sc1 r hr hrnm]
        simp only [x_c0, Data.set_regs, Function.update_of_ne ne_ic,
          Function.update_of_ne ne_s1, Function.update_of_ne ne_s0]
    obtain ⟨x_A1, slotTrees_1, maxDeg_1, t_A1, he_A1, ht_A1, hb_A1, hbr_A1, hmod_A1,
      hregs_A1, hmd_A1, hc₁⟩ := hA1
    -- Transition (`x_A1 → x_tr`, 2 ops): `remReg ← numRootsReg - oneP; iterCur ← pReg`
    let x_tr := (x_A1.set remReg E.length).set iterCur (st.right z)
    have hnr_xA1 : x_A1.regs numRootsReg = E.length + 1 := by
      change (RawState.ofData n base x_A1).numRoots = E.length + 1
      rw [hc₁.scattered.numRoots]
      exact hD.numRoots
    have hpr_xA1 : x_A1.regs pReg = st.right z := by
      rw [hregs_A1 pReg (by decide) (by decide)]
      simp only [x_pre, p5, Data.set_regs, Function.update_of_ne (by decide : pReg ≠ remReg),
        Function.update_of_ne (by decide : pReg ≠ s0),
        Function.update_of_ne (by decide : pReg ≠ maxDegReg), Function.update_self]
    have etr1 : ExecWithin w (.op (.exactBin .sub remReg numRootsReg oneP)) x_A1
        (x_A1.set remReg E.length) 1 := by
      have hnr_le_n : st.numRoots ≤ n := hraw.bounds.2.1
      have hr_le : E.length + 1 ≤ n := by have := hD.numRoots; omega
      simpa only [hnr_xA1, hbr_A1.regs_oneP, Nat.add_sub_cancel] using
        execWithin_exactSub (x := x_A1) (d := remReg) (i := numRootsReg) (j := oneP)
          (by rw [hnr_xA1, hbr_A1.regs_oneP]; omega)
          (by rw [hnr_xA1, hbr_A1.regs_oneP]
              exact hfit_stop.of_le (by simp only [space]; omega))
    have etr2 : ExecWithin (B := .exact) w (.op (.copy iterCur pReg))
        (x_A1.set remReg E.length) x_tr 1 := by
      simpa only [x_tr, Data.set_regs, Function.update_of_ne (by decide : pReg ≠ remReg),
        hpr_xA1] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x_A1.set remReg E.length)
          (d := iterCur) (s := pReg))
    have hb_tr : x_tr.Bounded w := etr2.bounded (etr1.bounded hb_A1)
    have hbr_tr : BaseRegs n base x_tr :=
      (hbr_A1.set_non_base (by decide) _).set_non_base (by decide) _
    have hst_tr : RawState.ofData n base x_tr = RawState.ofData n base x_A1 := by
      simp only [x_tr, ofData_set_scratch _ (by decide : 17 ≤ iterCur.val),
        ofData_set_scratch _ (by decide : 17 ≤ remReg.val)]
    -- Phase A2 (`x_tr → x_A2`, `rootScatterLoop`): the other trees, from `Detached.scatterRoots`
    obtain ⟨x_A2, slotTrees_2, maxDeg_2, t_A2, he_A2, ht_A2, hb_A2, hbr_A2, hmod_A2,
      hregs_A2, hmd_A2, hc₂⟩ :=
      scatterRootsLoop_exec E x_tr slotTrees_1 maxDeg_1 hb_tr hbr_tr
        (by rw [hst_tr]; exact hD.scatterRoots hc₁)
        (by simp only [x_tr, Data.set_regs, Function.update_of_ne (by decide : remReg ≠ iterCur),
              Function.update_self])
        (by simp only [x_tr, Data.set_regs,
              Function.update_of_ne (by decide : maxDegReg ≠ iterCur),
              Function.update_of_ne (by decide : maxDegReg ≠ remReg), hmd_A1])
        fun y hy => by
          simp only [x_tr, Data.set_regs, Function.update_self]
          exact hD.right y hy
    rw [hst_tr] at hc₂
    -- Phase B preamble (`x_A2 → x_B0`, 4 ops)
    have hmd2_le_n : maxDeg_2 + 1 ≤ n := by
      rcases hc₂.table.2.2.2.2.2 with h0 | h2 <;> omega
    let x_B0 := (((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg
      (maxDeg_2 + 1)).set curDReg 0
    have eb1 : ExecWithin (B := .exact) w (.op (.copy minRootReg zeroP)) x_A2
        (x_A2.set minRootReg 0) 1 := by
      simpa only [hbr_A2.regs_zeroP] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x_A2) (d := minRootReg) (s := zeroP))
    have eb2 : ExecWithin (B := .exact) w (.op (.copy numRootsReg zeroP))
        (x_A2.set minRootReg 0) ((x_A2.set minRootReg 0).set numRootsReg 0) 1 := by
      have hz_b : (x_A2.set minRootReg 0).regs zeroP = 0 := hbr_A2.regs_zeroP
      simpa only [hz_b] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x_A2.set minRootReg 0)
          (d := numRootsReg) (s := zeroP))
    have eb3 : ExecWithin w (.op (.exactBin .add maxDegReg maxDegReg oneP))
        ((x_A2.set minRootReg 0).set numRootsReg 0)
        (((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg (maxDeg_2 + 1)) 1 := by
      have hmd_b : ((x_A2.set minRootReg 0).set numRootsReg 0).regs maxDegReg = maxDeg_2 := by
        simp only [Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ numRootsReg),
          Function.update_of_ne (by decide : maxDegReg ≠ minRootReg), hmd_A2]
      have ho1_b : ((x_A2.set minRootReg 0).set numRootsReg 0).regs oneP = 1 :=
        hbr_A2.regs_oneP
      simpa only [hmd_b, ho1_b] using
        execWithin_exactAdd (x := (x_A2.set minRootReg 0).set numRootsReg 0)
          (d := maxDegReg) (i := maxDegReg) (j := oneP)
          (by rw [hmd_b, ho1_b]; exact hfit_stop.of_le (by simp only [space]; omega))
    have eb4 : ExecWithin (B := .exact) w (.op (.copy curDReg zeroP))
        (((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg (maxDeg_2 + 1)) x_B0 1 := by
      have hz_b : (((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg
          (maxDeg_2 + 1)).regs zeroP = 0 := hbr_A2.regs_zeroP
      simpa only [x_B0, hz_b] using
        (ExecWithin.copy (B := .exact) (w := w)
          (x := ((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg (maxDeg_2 + 1))
          (d := curDReg) (s := zeroP))
    have hb_B0 : x_B0.Bounded w := eb4.bounded (eb3.bounded (eb2.bounded (eb1.bounded hb_A2)))
    have hbr_B0 : BaseRegs n base x_B0 :=
      (((hbr_A2.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
        (by decide) _).set_non_base (by decide) _
    have hst_B0 : RawState.ofData n base x_B0 =
        { RawState.ofData n base x_A2 with minRoot := 0, numRoots := 0 } := by
      simp only [x_B0, ofData_set_scratch _ (by decide : 17 ≤ curDReg.val),
        ofData_set_scratch _ (by decide : 17 ≤ maxDegReg.val),
        ofData_set_numRoots, ofData_set_minRoot]
    -- Phase B (`x_B0 → y`, `gatherSlotsLoop`): the table is ready by `Detached.gathering`
    obtain ⟨y, finalRoots, t_B, he_B, ht_B, hb_y, hbr_y, hmod_B, hregs_B, hG⟩ :=
      gatherSlotsLoop_exec (maxDeg := maxDeg_2) (maxDeg_2 + 1) x_B0 0 slotTrees_2 [] (by omega)
        hb_B0 hbr_B0
        (by simp only [x_B0, Data.set_regs, Function.update_self])
        (by simp only [x_B0, Data.set_regs,
              Function.update_of_ne (by decide : maxDegReg ≠ curDReg), Function.update_self])
        (by rw [hst_B0]; exact hD.gathering hc₁ hc₂) fun _ _ => Nat.zero_le _
    rw [hst_B0] at hG
    -- `Detached.finish` reassembles `FibRawInv`.
    obtain ⟨hfin, hnm_le, hmd2_log⟩ := hD.finish hc₁ hc₂ hG
    -- Assemble full `ExecWithin` and total amortized step bound
    let t_else := 13 + t_A1 + 2 + t_A2 + 4 + t_B
    have he_seq :=
      ep1.seq <| execWithin_seq₂ ep2 <| execWithin_seq₂ ep3 <|
        execWithin_seq₃ ep4 <| execWithin_seq₃ ep5 <| execWithin_seq₂ ep6 <|
        he_A1.seq <| etr1.seq <| etr2.seq <| he_A2.seq <|
        eb1.seq <| eb2.seq <| eb3.seq <| eb4.seq he_B
    have he_full : ExecWithin w extractMinCode x y (t_else + 2) := by
      unfold extractMinCode
      exact (ExecWithin.branch_neg hc_top he_seq).mono (by omega)
    have hmod_full : Modifies (Block.mk base (space n)).footprint x.mem y.mem :=
      modifies_block_trans hmod_pre <|
        modifies_block_trans hmod_A1 <|
          modifies_block_trans hmod_A2 hmod_B
    -- Output register values (`outFlag = 1`, `outV = z.val`, `outK = st.key z`)
    have hout_pres : ∀ r : Fin rFib, (r = outFlag ∨ r = outV ∨ r = outK) →
        y.regs r = x_pre.regs r := by
      intro r hr_mem
      have hr30 : r.val < 30 := by rcases hr_mem with rfl | rfl | rfl <;> decide
      have hrm : r ≠ minRootReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
      have hrnr : r ≠ numRootsReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
      have hrnm : r ≠ numMarkedReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
      have hrcd : r ≠ curDReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
      have hrmd : r ≠ maxDegReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
      have hric : r ≠ iterCur := by rcases hr_mem with rfl | rfl | rfl <;> decide
      have hrrem : r ≠ remReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
      rw [hregs_B r hr30 hrm hrnr]
      simp only [x_B0, Data.set_regs, Function.update_of_ne hrcd, Function.update_of_ne hrmd,
        Function.update_of_ne hrnr, Function.update_of_ne hrm]
      rw [hregs_A2 r hr30]
      simp only [x_tr, Data.set_regs, Function.update_of_ne hric, Function.update_of_ne hrrem]
      exact hregs_A1 r hr30 hrnm
    have hy_of : y.regs outFlag = 1 := by
      rw [hout_pres outFlag (Or.inl rfl)]
      simp only [x_pre, p5, p4, p3, p2, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : outFlag ≠ remReg),
        Function.update_of_ne (by decide : outFlag ≠ maxDegReg),
        Function.update_of_ne (by decide : outFlag ≠ pReg),
        Function.update_of_ne (by decide : outFlag ≠ szReg),
        Function.update_of_ne (by decide : outFlag ≠ outK),
        Function.update_of_ne (by decide : outFlag ≠ s0),
        Function.update_of_ne (by decide : outFlag ≠ outV), Function.update_self]
    have hy_ov : y.regs outV = z.val := by
      rw [hout_pres outV (Or.inr (Or.inl rfl))]
      simp only [x_pre, p5, p4, p3, p2, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : outV ≠ remReg),
        Function.update_of_ne (by decide : outV ≠ maxDegReg),
        Function.update_of_ne (by decide : outV ≠ pReg),
        Function.update_of_ne (by decide : outV ≠ szReg),
        Function.update_of_ne (by decide : outV ≠ outK),
        Function.update_of_ne (by decide : outV ≠ s0), Function.update_self]
    have hy_ok : y.regs outK = st.key z := by
      rw [hout_pres outK (Or.inr (Or.inr rfl))]
      simp only [x_pre, p5, p4, p3, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : outK ≠ remReg),
        Function.update_of_ne (by decide : outK ≠ maxDegReg),
        Function.update_of_ne (by decide : outK ≠ pReg),
        Function.update_of_ne (by decide : outK ≠ szReg),
        Function.update_of_ne (by decide : outK ≠ s0), Function.update_self]
    refine ⟨y, t_else + 2, he_full, ?_, ?_, hmod_full, ?_⟩
    · simp only [PQCode.decode, code, indexedMinPQSpec, IndexedMinPQ.step,
        StateTransitionSpec.stepFn,
        hfind, hy_of, hy_ov, hy_ok, one_ne_zero, ↓reduceIte, hz_lt, ↓reduceDIte, Fin.eta]
    · simp only [indexedMinPQSpec, IndexedMinPQ.step, StateTransitionSpec.stepFn, hfind]
      exact ⟨hb_y, hbr_y, hfin⟩
    · -- Amortized bound: links are paid by the trees they remove; what remains is logarithmic.
      have hnr_x : x.regs numRootsReg = E.length + 1 := hD.numRoots
      have hnm_x : x.regs numMarkedReg = st.numMarked := rfl
      have hnr_y : y.regs numRootsReg = finalRoots.length := hG.numRoots
      have hnm_y_le : y.regs numMarkedReg ≤ st.numMarked := hnm_le
      have hdz := hD.degBound
      simp only [potential, unitCredit, slotCredit, List.length_nil, t_else, hnr_x, hnm_x,
        hnr_y] at ht_A1 ht_A2 ht_B ⊢
      omega

end Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
