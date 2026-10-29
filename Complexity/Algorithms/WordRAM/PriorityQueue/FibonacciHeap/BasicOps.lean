/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.Program

/-!
# Fibonacci Heap: Shared Primitives, Initialization, Queries, and Insertion

This file proves the exact-Word-RAM specifications for:
* shared primitives (`prioLTFlag`, `insertIntoNonEmptyList`, `addRootAndUpdateMin`) reused across
  `insert`, `decreaseKey`, and `extractMin`;
* `allocSpan`, `initSetup`, and `incCur` (`O(1)` fresh initialization on zeroed memory);
* `isEmptyCode`, `getKeyCode`, and `insertCode`.

## Main definitions

* Shared code fragments are defined in
  `Complexity/Algorithms/WordRAM/PriorityQueue/FibonacciHeap/Program.lean` and verified here
  against `FibInv`.

## Main results

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.prioLTFlag_exec`,
  `insertIntoNonEmptyList_exec`, `addRootAndUpdateMin_exec`: shared list and priority primitives.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.allocSpan_exec`, `initSetup_exec`,
  `incCur_eval`: initialization specifications for `SubroutineDS`.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.isEmptyCode_exec`, `getKeyCode_exec`,
  `insertCode_exec`: `O(1)` query and amortized insertion specifications.

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

theorem owns_arr_addr {n base k idx : ℕ} (hk : k < 8) (hidx : idx < n) :
    base ≤ base + k * n + idx ∧ base + k * n + idx < base + space n := by
  have hkn : (k + 1) * n ≤ 8 * n := Nat.mul_le_mul_right n hk
  rw [Nat.add_mul, Nat.one_mul] at hkn
  unfold space
  omega

theorem owns_cons_addr {n base d : ℕ} (hd : d ≤ n) :
    base ≤ base + 8 * n + d ∧ base + 8 * n + d < base + space n := by
  unfold space
  omega

/-! ## Shared primitives: `prioLTFlag`, `insertIntoNonEmptyList`, `addRootAndUpdateMin` -/

/-- `prioLTFlag uReg kuReg vReg kvReg flagReg` sets `flagReg ← 1` iff `(u, ku)` strictly precedes
`(v, kv)` under `IndexedMinPQ.PrioLT`, and `0` otherwise, within `6` instructions. -/
theorem prioLTFlag_exec {n base w : ℕ} {x : Data rFib} (hbr : BaseRegs n base x)
    (uReg kuReg vReg kvReg flagReg : Fin rFib) :
    let ltProp := x.regs kuReg < x.regs kvReg ∨
      (x.regs kuReg = x.regs kvReg ∧ x.regs uReg < x.regs vReg)
    let bval := if ltProp then 1 else 0
    ExecWithin w (prioLTFlag uReg kuReg vReg kvReg flagReg) x (x.set flagReg bval) 6 := by
  intro ltProp bval
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  unfold prioLTFlag
  by_cases hku : x.regs kuReg < x.regs kvReg
  · have hc : (Cond.lt kuReg kvReg).Holds x := hku
    have hb : bval = 1 := by simp only [bval, ltProp, hku, true_or, ↓reduceIte]
    rw [hb, ← ho1]
    exact (ExecWithin.branch_pos hc ExecWithin.copy).mono (by omega)
  · have hc : ¬(Cond.lt kuReg kvReg).Holds x := hku
    by_cases heq : x.regs kuReg = x.regs kvReg
    · have hc2 : (Cond.eq kuReg kvReg).Holds x := heq
      by_cases huv : x.regs uReg < x.regs vReg
      · have hc3 : (Cond.lt uReg vReg).Holds x := huv
        have hb : bval = 1 := by simp only [bval, ltProp, heq, huv, and_self, or_true, ↓reduceIte]
        rw [hb, ← ho1]
        exact (ExecWithin.branch_neg hc
          (ExecWithin.branch_pos hc2 (ExecWithin.branch_pos hc3 ExecWithin.copy))).mono (by omega)
      · have hc3 : ¬(Cond.lt uReg vReg).Holds x := huv
        have hb : bval = 0 := by
          simp only [bval, ltProp, heq, lt_self_iff_false, huv, true_and, or_self, ↓reduceIte]
        rw [hb, ← hz0]
        exact (ExecWithin.branch_neg hc
          (ExecWithin.branch_pos hc2 (ExecWithin.branch_neg hc3 ExecWithin.copy))).mono (by omega)
    · have hc2 : ¬(Cond.eq kuReg kvReg).Holds x := heq
      have hb : bval = 0 := by simp only [bval, ltProp, hku, heq, false_and, or_self, ↓reduceIte]
      rw [hb, ← hz0]
      exact (ExecWithin.branch_neg hc (ExecWithin.branch_neg hc2 ExecWithin.copy)).mono (by omega)

theorem prioLTFlag_preserves {r uReg kuReg vReg kvReg flagReg : Fin rFib} (hf : r ≠ flagReg) :
    (prioLTFlag uReg kuReg vReg kvReg flagReg).Preserves r := by
  simp only [prioLTFlag, Code.Preserves, Op.dest, ne_eq, Option.some.injEq, hf.symm,
    not_false_eq_true, and_self]

theorem insertIntoNonEmptyList_preserves {r hReg uReg : Fin rFib}
    (h0 : r ≠ s0) (h2 : r ≠ s2) :
    (insertIntoNonEmptyList hReg uReg).Preserves r := by
  simp only [insertIntoNonEmptyList, Code.Preserves, Op.dest, Op.exactBin, ne_eq,
    Option.some.injEq, reduceCtorEq, not_false_eq_true, h0.symm, h2.symm, and_self]

/-- `insertIntoNonEmptyList hReg uReg` splices `u` immediately after `h` in a circular list
`h :: tail` (`u ∉ h :: tail`) in `10` instructions, modifying only `left[u], left[r], right[u],
right[h]` (`r = right[h]`) and scratch registers `s0, s2`. -/
theorem insertIntoNonEmptyList_exec {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {hReg uReg : Fin rFib} (hh0 : hReg ≠ s0) (hh2 : hReg ≠ s2) (hu0 : uReg ≠ s0) (hu2 : uReg ≠ s2)
    {h u : Fin n} {tail : List (Fin n)}
    (hh_val : x.regs hReg = h.val) (hu_val : x.regs uReg = u.val)
    (hcirc : IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right
      (h :: tail))
    (hu_not : u ∉ h :: tail) :
    ∃ y, ExecWithin w (insertIntoNonEmptyList hReg uReg) x y 10 ∧
      BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∃ r : Fin n, (RawState.ofData n base x).right h = r.val ∧ r ∈ h :: tail ∧
        RawState.ofData n base y =
          { RawState.ofData n base x with
            left := Function.update
              (Function.update (RawState.ofData n base x).left u h.val) r u.val
            right := Function.update
              (Function.update (RawState.ofData n base x).right u r.val) h u.val }) ∧
      IsCircList (RawState.ofData n base y).left (RawState.ofData n base y).right
        (h :: u :: tail) := by
  have hfit_stop := hbr.fits_stop hb
  have hl_base : x.regs leftBase = base + 3 * n := hbr.2.2.2.2.2.1
  have hr_base : x.regs rightBase = base + 4 * n := hbr.2.2.2.2.2.2.1
  let st := RawState.ofData n base x
  obtain ⟨r, hr_eq, hr_mem⟩ := hcirc.right_head
  have hr_mem_x : x.mem (base + 4 * n + h.val) = r.val := hr_eq
  have ho_rh := owns_arr_addr (base := base) (k := 4) (by decide) h.isLt
  have ho_lu := owns_arr_addr (base := base) (k := 3) (by decide) u.isLt
  have ho_lr := owns_arr_addr (base := base) (k := 3) (by decide) r.isLt
  have ho_ru := owns_arr_addr (base := base) (k := 4) (by decide) u.isLt
  let x1 := (x.set s0 (base + 4 * n + h.val)).set s2 r.val
  let x2 := (x1.set s0 (base + 3 * n + u.val)).write (base + 3 * n + u.val) h.val
  let x3 := (x2.set s0 (base + 3 * n + r.val)).write (base + 3 * n + r.val) u.val
  let x4 := (x3.set s0 (base + 4 * n + u.val)).write (base + 4 * n + u.val) r.val
  let x5 := (x4.set s0 (base + 4 * n + h.val)).write (base + 4 * n + h.val) u.val
  have he : ExecWithin w (insertIntoNonEmptyList hReg uReg) x x5 10 := by
    unfold insertIntoNonEmptyList
    have s1_add : ExecWithin w (.op (.exactBin .add s0 rightBase hReg)) x
        (x.set s0 (base + 4 * n + h.val)) 1 := by
      simpa only [hr_base, hh_val] using
        execWithin_exactAdd (x := x) (d := s0) (i := rightBase) (j := hReg)
          (by rw [hr_base, hh_val]; exact hfit_stop.of_le (by omega))
    have s2_ld : ExecWithin (B := .exact) w (.op (.load s2 s0))
        (x.set s0 (base + 4 * n + h.val)) x1 1 := by
      simpa only [Data.set_mem, Data.set_regs, Function.update_self, hr_mem_x] using
        (ExecWithin.load (B := .exact) (w := w) (x := x.set s0 (base + 4 * n + h.val))
          (d := s2) (a := s0))
    have hx1_l : x1.regs leftBase = base + 3 * n := by
      simp only [x1, Data.set_regs, Function.update_of_ne (by decide : leftBase ≠ s2),
        Function.update_of_ne (by decide : leftBase ≠ s0), hl_base]
    have hx1_r : x1.regs rightBase = base + 4 * n := by
      simp only [x1, Data.set_regs, Function.update_of_ne (by decide : rightBase ≠ s2),
        Function.update_of_ne (by decide : rightBase ≠ s0), hr_base]
    have hx1_u : x1.regs uReg = u.val := by
      simp only [x1, Data.set_regs, Function.update_of_ne hu2, Function.update_of_ne hu0, hu_val]
    have hx1_h : x1.regs hReg = h.val := by
      simp only [x1, Data.set_regs, Function.update_of_ne hh2, Function.update_of_ne hh0, hh_val]
    have hx1_s2 : x1.regs s2 = r.val := by simp only [x1, Data.set_regs, Function.update_self]
    have s3_add : ExecWithin w (.op (.exactBin .add s0 leftBase uReg)) x1
        (x1.set s0 (base + 3 * n + u.val)) 1 := by
      simpa only [hx1_l, hx1_u] using
        execWithin_exactAdd (x := x1) (d := s0) (i := leftBase) (j := uReg)
          (by rw [hx1_l, hx1_u]; exact hfit_stop.of_le (by omega))
    have s4_st : ExecWithin (B := .exact) w (.op (.store s0 hReg))
        (x1.set s0 (base + 3 * n + u.val)) x2 1 := by
      simpa only [Data.set_regs, Function.update_self, Function.update_of_ne hh0, hx1_h] using
        (ExecWithin.store (B := .exact) (w := w) (x := x1.set s0 (base + 3 * n + u.val))
          (a := s0) (s := hReg))
    have hx2_l : x2.regs leftBase = base + 3 * n := by
      simp only [x2, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : leftBase ≠ s0), hx1_l]
    have hx2_s2 : x2.regs s2 = r.val := by
      simp only [x2, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : s2 ≠ s0), hx1_s2]
    have hx2_u : x2.regs uReg = u.val := by
      simp only [x2, Data.write_regs, Data.set_regs, Function.update_of_ne hu0, hx1_u]
    have s5_add : ExecWithin w (.op (.exactBin .add s0 leftBase s2)) x2
        (x2.set s0 (base + 3 * n + r.val)) 1 := by
      simpa only [hx2_l, hx2_s2] using
        execWithin_exactAdd (x := x2) (d := s0) (i := leftBase) (j := s2)
          (by rw [hx2_l, hx2_s2]; exact hfit_stop.of_le (by omega))
    have s6_st : ExecWithin (B := .exact) w (.op (.store s0 uReg))
        (x2.set s0 (base + 3 * n + r.val)) x3 1 := by
      simpa only [Data.set_regs, Function.update_self, Function.update_of_ne hu0, hx2_u] using
        (ExecWithin.store (B := .exact) (w := w) (x := x2.set s0 (base + 3 * n + r.val))
          (a := s0) (s := uReg))
    have hx3_r : x3.regs rightBase = base + 4 * n := by
      simp only [x3, x2, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : rightBase ≠ s0), hx1_r]
    have hx3_u : x3.regs uReg = u.val := by
      simp only [x3, Data.write_regs, Data.set_regs, Function.update_of_ne hu0, hx2_u]
    have hx3_s2 : x3.regs s2 = r.val := by
      simp only [x3, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : s2 ≠ s0), hx2_s2]
    have s7_add : ExecWithin w (.op (.exactBin .add s0 rightBase uReg)) x3
        (x3.set s0 (base + 4 * n + u.val)) 1 := by
      simpa only [hx3_r, hx3_u] using
        execWithin_exactAdd (x := x3) (d := s0) (i := rightBase) (j := uReg)
          (by rw [hx3_r, hx3_u]; exact hfit_stop.of_le (by omega))
    have s8_st : ExecWithin (B := .exact) w (.op (.store s0 s2))
        (x3.set s0 (base + 4 * n + u.val)) x4 1 := by
      simpa only [Data.set_regs, Function.update_self,
        Function.update_of_ne (by decide : s2 ≠ s0), hx3_s2] using
        (ExecWithin.store (B := .exact) (w := w) (x := x3.set s0 (base + 4 * n + u.val))
          (a := s0) (s := s2))
    have hx4_r : x4.regs rightBase = base + 4 * n := by
      simp only [x4, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : rightBase ≠ s0), hx3_r]
    have hx4_h : x4.regs hReg = h.val := by
      simp only [x4, x3, x2, Data.write_regs, Data.set_regs, Function.update_of_ne hh0, hx1_h]
    have hx4_u : x4.regs uReg = u.val := by
      simp only [x4, Data.write_regs, Data.set_regs, Function.update_of_ne hu0, hx3_u]
    have s9_add : ExecWithin w (.op (.exactBin .add s0 rightBase hReg)) x4
        (x4.set s0 (base + 4 * n + h.val)) 1 := by
      simpa only [hx4_r, hx4_h] using
        execWithin_exactAdd (x := x4) (d := s0) (i := rightBase) (j := hReg)
          (by rw [hx4_r, hx4_h]; exact hfit_stop.of_le (by omega))
    have s10_st : ExecWithin (B := .exact) w (.op (.store s0 uReg))
        (x4.set s0 (base + 4 * n + h.val)) x5 1 := by
      simpa only [Data.set_regs, Function.update_self, Function.update_of_ne hu0, hx4_u] using
        (ExecWithin.store (B := .exact) (w := w) (x := x4.set s0 (base + 4 * n + h.val))
          (a := s0) (s := uReg))
    exact (s1_add.seq <| s2_ld.seq <| s3_add.seq <| s4_st.seq <| s5_add.seq <| s6_st.seq <|
      s7_add.seq <| s8_st.seq <| s9_add.seq s10_st).mono (by omega)
  have hpres : ∀ r : Fin rFib, r ≠ s0 → r ≠ s2 →
      (insertIntoNonEmptyList hReg uReg).Preserves r :=
    fun _ h0 h2 => insertIntoNonEmptyList_preserves h0 h2
  have hbr5 : BaseRegs n base x5 :=
    hbr.preserved he (hpres _ (by decide) (by decide)) (hpres _ (by decide) (by decide))
      (hpres _ (by decide) (by decide)) (hpres _ (by decide) (by decide))
      (hpres _ (by decide) (by decide)) (hpres _ (by decide) (by decide))
      (hpres _ (by decide) (by decide)) (hpres _ (by decide) (by decide))
      (hpres _ (by decide) (by decide)) (hpres _ (by decide) (by decide))
      (hpres _ (by decide) (by decide)) (hpres _ (by decide) (by decide))
      (hpres _ (by decide) (by decide))
  have hmod : Modifies (Block.mk base (space n)).footprint x.mem x5.mem :=
    modifies_block_trans (Modifies.write_of_owns ho_lu h.val) <|
    modifies_block_trans (Modifies.write_of_owns ho_lr u.val) <|
    modifies_block_trans (Modifies.write_of_owns ho_ru r.val)
      (Modifies.write_of_owns ho_rh u.val)
  have hst5 : RawState.ofData n base x5 =
      { st with
        left := Function.update (Function.update st.left u h.val) r u.val
        right := Function.update (Function.update st.right u r.val) h u.val } := by
    simp only [x5, x4, x3, x2, x1, ofData_write_right, ofData_write_left,
      ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ s2.val)]
    rfl
  refine ⟨x5, he, hbr5, hmod, ⟨r, hr_eq, hr_mem, hst5⟩, ?_⟩
  rw [hst5]
  exact hcirc.insertAfter hu_not hr_eq

/-- In any `Nodup` forest `ts`, no strict descendant `x ∈ forestNodes T.children` (`T ∈ ts`) can
equal the root of any tree `R ∈ ts`. -/
theorem descendant_ne_root_of_nodup {n : ℕ} {ts : List (FHTree n)} (hnd : (forestNodes ts).Nodup)
    {T R : FHTree n} (hT : T ∈ ts) (hR : R ∈ ts) {x : Fin n} (hx : x ∈ forestNodes T.children) :
    x ≠ R.root := by
  intro hxr
  by_cases hTR : T = R
  · subst hTR
    have hnd_T := forestNodes_nodup_tree hnd hT
    rw [T.nodes_eq] at hnd_T
    exact (List.nodup_cons.mp hnd_T).1 (hxr ▸ hx)
  · have hx_T : x ∈ T.nodes := T.nodes_eq ▸ List.mem_cons_of_mem T.root hx
    exact forestNodes_nodup_disjoint hnd hT hR hTR hx_T (hxr ▸ R.root_mem_nodes)

theorem addRootAndUpdateMin_preserves {r uReg : Fin rFib}
    (h0 : r ≠ s0) (h1 : r ≠ s1) (h2 : r ≠ s2) (h3 : r ≠ s3) (h4 : r ≠ s4) (h5 : r ≠ s5)
    (hm : r ≠ minRootReg) (hnr : r ≠ numRootsReg) :
    (addRootAndUpdateMin uReg).Preserves r := by
  unfold addRootAndUpdateMin
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Code.Preserves, Op.dest, Op.exactBin, ne_eq, Option.some.injEq, reduceCtorEq,
      not_false_eq_true, h0.symm, hm.symm, and_self]
  · refine ⟨by simp only [Code.Preserves, Op.dest, Op.exactBin, ne_eq, Option.some.injEq,
        h1.symm, not_false_eq_true],
      insertIntoNonEmptyList_preserves h0 h2, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, prioLTFlag_preserves h5, ?_⟩ <;>
      simp only [Code.Preserves, Op.dest, Op.exactBin, ne_eq, Option.some.injEq,
        h0.symm, h3.symm, h4.symm, hm.symm, not_false_eq_true, and_self]
  · simp only [Code.Preserves, Op.dest, Op.exactBin, ne_eq, Option.some.injEq,
      hnr.symm, not_false_eq_true]

/-- `addRootAndUpdateMin uReg` appends a new valid root tree `T_u` (`T_u.root = u`) to the root
circular list `ts`, updating `minRootReg` under `IndexedMinPQ.PrioLT` and incrementing
`numRootsReg` in `≤ 28`
instructions while preserving `ValidRoot` across `T_u :: ts`. -/
theorem addRootAndUpdateMin_exec {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {uReg : Fin rFib} (hu_sc : uReg ≠ s0 ∧ uReg ≠ s1 ∧ uReg ≠ s2 ∧ uReg ≠ s3 ∧ uReg ≠ s4 ∧
      uReg ≠ s5 ∧ uReg ≠ minRootReg ∧ uReg ≠ numRootsReg)
    {u : Fin n} (hu_val : x.regs uReg = u.val)
    {T_u : FHTree n} {ts : List (FHTree n)}
    (hu_root : T_u.root = u)
    (hnd : (forestNodes (T_u :: ts)).Nodup)
    (hTu : ValidRoot (RawState.ofData n base x) none T_u)
    (hts : ∀ T ∈ ts, ValidRoot (RawState.ofData n base x) none T)
    (hnr : (RawState.ofData n base x).numRoots = ts.length)
    (hrl : (ts = [] ∧ (RawState.ofData n base x).minRoot = 0) ∨
      ∃ (m : Fin n) (rtail : List (Fin n)),
        (RawState.ofData n base x).minRoot = m.val + 1 ∧
        IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right (m :: rtail) ∧
        (m :: rtail).Perm (ts.map FHTree.root) ∧
        ∀ T ∈ ts, IndexedMinPQ.PrioLE
          (m, (RawState.ofData n base x).key m)
          (T.root, (RawState.ofData n base x).key T.root)) :
    let st := RawState.ofData n base x
    ∃ y, ExecWithin w (addRootAndUpdateMin uReg) x y 28 ∧
      BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (let st' := RawState.ofData n base y
       st'.key = st.key ∧ st'.par = st.par ∧ st'.child = st.child ∧
       st'.deg = st.deg ∧ st'.mark = st.mark ∧ st'.inHeap = st.inHeap ∧ st'.cons = st.cons ∧
       st'.numMarked = st.numMarked ∧ st'.sz = st.sz ∧
       st'.numRoots = (T_u :: ts).length ∧
       (∀ T ∈ T_u :: ts, ValidRoot st' none T) ∧
       ∃ (m' : Fin n) (rtail' : List (Fin n)),
         st'.minRoot = m'.val + 1 ∧
         IsCircList st'.left st'.right (m' :: rtail') ∧
         (m' :: rtail').Perm ((T_u :: ts).map FHTree.root) ∧
         ∀ T ∈ T_u :: ts, IndexedMinPQ.PrioLE (m', st'.key m') (T.root, st'.key T.root)) := by
  intro st
  have hfit_stop := hbr.fits_stop hb
  have hfn_le : (T_u :: ts).length ≤ n :=
    (forestNodes_length_ge (T_u :: ts)).trans (by simpa using hnd.length_le_card)
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hu0, hu1, hu2, hu3, hu4, hu5, hum, hunr⟩ := hu_sc
  have hpres_add : ∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 → r ≠ s5 →
      r ≠ minRootReg → r ≠ numRootsReg → (addRootAndUpdateMin uReg).Preserves r :=
    fun _ => addRootAndUpdateMin_preserves
  rcases hrl with ⟨rfl, hmin0⟩ | ⟨m, rtail, hmin_m, hcirc, hperm, hmin_le⟩
  · -- Empty root list (`minRoot = 0`)
    have hc : (Cond.eq minRootReg zeroP).Holds x := by
      simp only [Cond.Holds, hz0]; exact hmin0
    have hl_base : x.regs leftBase = base + 3 * n := hbr.2.2.2.2.2.1
    have hr_base : x.regs rightBase = base + 4 * n := hbr.2.2.2.2.2.2.1
    have ho_lu := owns_arr_addr (base := base) (k := 3) (by decide) u.isLt
    have ho_ru := owns_arr_addr (base := base) (k := 4) (by decide) u.isLt
    let x1 := (x.set s0 (base + 3 * n + u.val)).write (base + 3 * n + u.val) u.val
    let x2 := (x1.set s0 (base + 4 * n + u.val)).write (base + 4 * n + u.val) u.val
    let x3 := x2.set minRootReg (u.val + 1)
    let x4 := x3.set numRootsReg 1
    have he_pos : ExecWithin (B := .exact) w
        (.seq (.op (.exactBin .add s0 leftBase uReg)) <|
         .seq (.op (.store s0 uReg)) <|
         .seq (.op (.exactBin .add s0 rightBase uReg)) <|
         .seq (.op (.store s0 uReg)) <|
              (.op (.exactBin .add minRootReg uReg oneP))) x x3 5 := by
      have s1_add : ExecWithin w (.op (.exactBin .add s0 leftBase uReg)) x
          (x.set s0 (base + 3 * n + u.val)) 1 := by
        simpa only [hl_base, hu_val] using
          execWithin_exactAdd (x := x) (d := s0) (i := leftBase) (j := uReg)
            (by rw [hl_base, hu_val]; exact hfit_stop.of_le (by omega))
      have s2_st : ExecWithin (B := .exact) w (.op (.store s0 uReg))
          (x.set s0 (base + 3 * n + u.val)) x1 1 := by
        simpa only [Data.set_regs, Function.update_self, Function.update_of_ne hu0, hu_val] using
          (ExecWithin.store (B := .exact) (w := w) (x := x.set s0 (base + 3 * n + u.val))
            (a := s0) (s := uReg))
      have hx1_r : x1.regs rightBase = base + 4 * n := by
        simp only [x1, Data.write_regs, Data.set_regs,
          Function.update_of_ne (by decide : rightBase ≠ s0), hr_base]
      have hx1_u : x1.regs uReg = u.val := by
        simp only [x1, Data.write_regs, Data.set_regs, Function.update_of_ne hu0, hu_val]
      have s3_add : ExecWithin w (.op (.exactBin .add s0 rightBase uReg)) x1
          (x1.set s0 (base + 4 * n + u.val)) 1 := by
        simpa only [hx1_r, hx1_u] using
          execWithin_exactAdd (x := x1) (d := s0) (i := rightBase) (j := uReg)
            (by rw [hx1_r, hx1_u]; exact hfit_stop.of_le (by omega))
      have s4_st : ExecWithin (B := .exact) w (.op (.store s0 uReg))
          (x1.set s0 (base + 4 * n + u.val)) x2 1 := by
        simpa only [Data.set_regs, Function.update_self, Function.update_of_ne hu0, hx1_u] using
          (ExecWithin.store (B := .exact) (w := w) (x := x1.set s0 (base + 4 * n + u.val))
            (a := s0) (s := uReg))
      have hx2_u : x2.regs uReg = u.val := by
        simp only [x2, Data.write_regs, Data.set_regs, Function.update_of_ne hu0, hx1_u]
      have hx2_one : x2.regs oneP = 1 := by
        simp only [x2, x1, Data.write_regs, Data.set_regs,
          Function.update_of_ne (by decide : oneP ≠ s0), ho1]
      have s5_add : ExecWithin w (.op (.exactBin .add minRootReg uReg oneP)) x2 x3 1 := by
        have := u.isLt
        simpa only [hx2_u, hx2_one] using
          execWithin_exactAdd (x := x2) (d := minRootReg) (i := uReg) (j := oneP)
            (by rw [hx2_u, hx2_one]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
      exact (s1_add.seq <| s2_st.seq <| s3_add.seq <| s4_st.seq s5_add).mono (by omega)
    have hx3_nr : x3.regs numRootsReg = 0 := by
      simp only [x3, x2, x1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : numRootsReg ≠ minRootReg),
        Function.update_of_ne (by decide : numRootsReg ≠ s0)]
      exact hnr
    have hx3_one : x3.regs oneP = 1 := by
      simp only [x3, x2, x1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : oneP ≠ minRootReg),
        Function.update_of_ne (by decide : oneP ≠ s0), ho1]
    have he_inc : ExecWithin w (.op (.exactBin .add numRootsReg numRootsReg oneP)) x3 x4 1 := by
      simpa only [hx3_nr, hx3_one, Nat.zero_add] using
        execWithin_exactAdd (x := x3) (d := numRootsReg) (i := numRootsReg) (j := oneP)
          (by rw [hx3_nr, hx3_one]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
    have he : ExecWithin w (addRootAndUpdateMin uReg) x x4 28 := by
      unfold addRootAndUpdateMin
      exact ((ExecWithin.branch_pos hc he_pos).seq he_inc).mono (by omega)
    have hbr4 : BaseRegs n base x4 :=
      hbr.preserved he
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        (hpres_add _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
    have hmod : Modifies (Block.mk base (space n)).footprint x.mem x4.mem :=
      modifies_block_trans (Modifies.write_of_owns ho_lu u.val)
        (Modifies.write_of_owns ho_ru u.val)
    have hst4 : RawState.ofData n base x4 =
        { st with
          left := Function.update st.left u u.val
          right := Function.update st.right u u.val
          minRoot := u.val + 1
          numRoots := 1 } := by
      simp only [x4, x3, x2, x1, ofData_set_numRoots, ofData_set_minRoot,
        ofData_write_right, ofData_write_left,
        ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
      rfl
    refine ⟨x4, he, hbr4, hmod, ?_⟩
    dsimp only
    rw [hst4]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, u, [], rfl,
      IsCircList.singleton st.left st.right u, by simp only [List.map, hu_root, List.Perm.refl], ?_⟩
    · intro T hT
      have hTeq : T = T_u := List.mem_singleton.mp hT
      subst hTeq
      refine ⟨hTu.1.frame (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) (fun w hw => ?_),
        hTu.2.1, hTu.2.2⟩
      have hwu : w ≠ u := hu_root ▸
        descendant_ne_root_of_nodup hnd List.mem_cons_self List.mem_cons_self hw
      exact ⟨rfl, Function.update_of_ne hwu _ _, Function.update_of_ne hwu _ _, Iff.rfl⟩
    · intro T hT
      rw [List.mem_singleton.mp hT, hu_root]
      exact IndexedMinPQ.PrioLE.refl _
  · -- Non-empty root list (`minRoot = m.val + 1`)
    have hc : ¬(Cond.eq minRootReg zeroP).Holds x := by
      simp only [Cond.Holds, hz0]
      change (RawState.ofData n base x).minRoot ≠ 0
      rw [hmin_m]
      exact Nat.succ_ne_zero m.val
    let x1 := x.set s1 m.val
    have he_sub : ExecWithin w (.op (.exactBin .sub s1 minRootReg oneP)) x x1 1 := by
      have hmin_x : x.regs minRootReg = m.val + 1 := hmin_m
      have hm_lt := m.isLt
      simpa only [hmin_x, ho1, Nat.add_sub_cancel] using
        execWithin_exactSub (x := x) (d := s1) (i := minRootReg) (j := oneP)
          (by rw [hmin_x, ho1]; omega)
          (by rw [hmin_x, ho1]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
    have hb1 : x1.Bounded w := he_sub.bounded hb
    have hbr1 : BaseRegs n base x1 := hbr.set_non_base (by decide) m.val
    have hst1 : RawState.ofData n base x1 = st :=
      ofData_set_scratch x (by decide : 17 ≤ s1.val) m.val
    have hu_not_roots : u ∉ m :: rtail := by
      intro hm_in
      obtain ⟨R, hR, hR_root⟩ := List.mem_map.mp (hperm.subset hm_in)
      have hnd_cons := List.nodup_append.mp hnd
      exact hnd_cons.2.2 u (hu_root ▸ T_u.root_mem_nodes) u
        (mem_forestNodes_iff.mpr ⟨R, hR, hR_root ▸ R.root_mem_nodes⟩) rfl
    have hx1_s1 : x1.regs s1 = m.val := by simp only [x1, Data.set_regs, Function.update_self]
    have hx1_u : x1.regs uReg = u.val := by
      simp only [x1, Data.set_regs, Function.update_of_ne hu1, hu_val]
    obtain ⟨x2, he_ins, hbr2, hmod2, ⟨r, hr_eq, hr_mem, hst2⟩, hcirc2⟩ :=
      insertIntoNonEmptyList_exec hb1 hbr1 (by decide) (by decide) hu0 hu2 hx1_s1 hx1_u
        (hst1 ▸ hcirc) hu_not_roots
    rw [hst1] at hr_eq hst2
    have hb2 : x2.Bounded w := he_ins.bounded hb1
    have hx2_u : x2.regs uReg = u.val :=
      (he_ins.regs_eq (insertIntoNonEmptyList_preserves hu0 hu2)).trans hx1_u
    have hx2_s1 : x2.regs s1 = m.val :=
      (he_ins.regs_eq (insertIntoNonEmptyList_preserves (by decide) (by decide))).trans hx1_s1
    have hbase2 : x2.regs baseReg = base := hbr2.2.2.1
    have hku_mem : x2.mem (base + u.val) = st.key u := by
      have : (RawState.ofData n base x2).key u = st.key u := by rw [hst2]
      exact this
    have hkm_mem : x2.mem (base + m.val) = st.key m := by
      have : (RawState.ofData n base x2).key m = st.key m := by rw [hst2]
      exact this
    let x3 := ((x2.set s0 (base + u.val)).set s3 (st.key u))
    let x4 := ((x3.set s0 (base + m.val)).set s4 (st.key m))
    have hu_lt := u.isLt
    have hm_lt := m.isLt
    have a1 : ExecWithin w (.op (.exactBin .add s0 baseReg uReg)) x2
        (x2.set s0 (base + u.val)) 1 := by
      simpa only [hbase2, hx2_u] using
        execWithin_exactAdd (x := x2) (d := s0) (i := baseReg) (j := uReg)
          (by rw [hbase2, hx2_u]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
    have l1 : ExecWithin (B := .exact) w (.op (.load s3 s0))
        (x2.set s0 (base + u.val)) x3 1 := by
      simpa only [Data.set_mem, Data.set_regs, Function.update_self, hku_mem] using
        (ExecWithin.load (B := .exact) (w := w) (x := x2.set s0 (base + u.val)) (d := s3) (a := s0))
    have hx3_b : x3.regs baseReg = base := by
      simp only [x3, Data.set_regs, Function.update_of_ne (by decide : baseReg ≠ s3),
        Function.update_of_ne (by decide : baseReg ≠ s0), hbase2]
    have hx3_s1 : x3.regs s1 = m.val := by
      simp only [x3, Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s3),
        Function.update_of_ne (by decide : s1 ≠ s0), hx2_s1]
    have a2 : ExecWithin w (.op (.exactBin .add s0 baseReg s1)) x3
        (x3.set s0 (base + m.val)) 1 := by
      simpa only [hx3_b, hx3_s1] using
        execWithin_exactAdd (x := x3) (d := s0) (i := baseReg) (j := s1)
          (by rw [hx3_b, hx3_s1]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
    have l2 : ExecWithin (B := .exact) w (.op (.load s4 s0))
        (x3.set s0 (base + m.val)) x4 1 := by
      simpa only [x3, Data.set_mem, Data.set_regs, Function.update_self, hkm_mem] using
        (ExecWithin.load (B := .exact) (w := w) (x := x3.set s0 (base + m.val)) (d := s4) (a := s0))
    have hbr4 : BaseRegs n base x4 :=
      ((hbr2.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
        (by decide) _ |>.set_non_base (by decide) _
    have hst4 : RawState.ofData n base x4 = RawState.ofData n base x2 := by
      simp only [x4, x3, ofData_set_scratch _ (by decide : 17 ≤ s4.val),
        ofData_set_scratch _ (by decide : 17 ≤ s3.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
    have hx4_u : x4.regs uReg = u.val := by
      simp only [x4, x3, Data.set_regs, Function.update_of_ne hu4, Function.update_of_ne hu3,
        Function.update_of_ne hu0, hx2_u]
    have hx4_s1 : x4.regs s1 = m.val := by
      simp only [x4, x3, Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s4),
        Function.update_of_ne (by decide : s1 ≠ s3), Function.update_of_ne (by decide : s1 ≠ s0),
        hx2_s1]
    have hx4_s3 : x4.regs s3 = st.key u := by
      simp only [x4, x3, Data.set_regs, Function.update_of_ne (by decide : s3 ≠ s4),
        Function.update_of_ne (by decide : s3 ≠ s0), Function.update_self]
    have hx4_s4 : x4.regs s4 = st.key m := by
      simp only [x4, Data.set_regs, Function.update_self]
    have he_plt := prioLTFlag_exec (w := w) hbr4 uReg s3 s1 s4 s5
    dsimp only at he_plt
    rw [hx4_s3, hx4_s4, hx4_u, hx4_s1] at he_plt
    let bval := if IndexedMinPQ.PrioLT (u, st.key u) (m, st.key m) then 1 else 0
    have he_plt' : ExecWithin w (prioLTFlag uReg s3 s1 s4 s5) x4 (x4.set s5 bval) 6 := he_plt
    let x5 := x4.set s5 bval
    have hbr5 : BaseRegs n base x5 := hbr4.set_non_base (by decide) bval
    have hst5 : RawState.ofData n base x5 = RawState.ofData n base x2 :=
      (ofData_set_scratch x4 (by decide : 17 ≤ s5.val) bval).trans hst4
    have hx5_u : x5.regs uReg = u.val := by
      simp only [x5, Data.set_regs, Function.update_of_ne hu5, hx4_u]
    have hx5_z : x5.regs zeroP = 0 := hbr5.2.2.2.2.2.2.2.2.2.2.2.1
    have hx5_o : x5.regs oneP = 1 := hbr5.2.2.2.2.2.2.2.2.2.2.2.2
    -- ValidRoot preservation across x2 (only left/right of roots u, m, r changed!)
    have hvalid_all : ∀ (st_f : RawState n),
        st_f.key = st.key → st_f.par = st.par → st_f.child = st.child →
        st_f.deg = st.deg → st_f.mark = st.mark → st_f.inHeap = st.inHeap →
        st_f.left = (RawState.ofData n base x2).left →
        st_f.right = (RawState.ofData n base x2).right →
        ∀ T ∈ T_u :: ts, ValidRoot st_f none T := by
      intro st_f hk hp hch hd hmk hin hl hr T hT
      have hT_old : ValidRoot st none T := by
        rcases List.mem_cons.mp hT with rfl | hT_ts
        · exact hTu
        · exact hts T hT_ts
      refine ⟨hT_old.1.frame
        (fun w _ => ⟨by rw [hin], by rw [hmk], by rw [hd], by rw [hch], by rw [hk]⟩)
        (fun w hw => ?_),
        by rw [hp]; exact hT_old.2.1, by rw [hmk]; exact hT_old.2.2⟩
      have hwu : w ≠ u := hu_root ▸ descendant_ne_root_of_nodup hnd hT List.mem_cons_self hw
      obtain ⟨Rm, hRm, hRm_root⟩ := List.mem_map.mp (hperm.subset List.mem_cons_self)
      have hwm : w ≠ m := hRm_root ▸
        descendant_ne_root_of_nodup hnd hT (List.mem_cons_of_mem T_u hRm) hw
      obtain ⟨Rr, hRr, hRr_root⟩ := List.mem_map.mp (hperm.subset hr_mem)
      have hwr : w ≠ r := hRr_root ▸
        descendant_ne_root_of_nodup hnd hT (List.mem_cons_of_mem T_u hRr) hw
      rw [hl, hr, hst2]
      simp only [Function.update_of_ne hwr, Function.update_of_ne hwu, Function.update_of_ne hwm]
      exact ⟨by rw [hp], trivial, trivial, trivial⟩
    have hperm_new : (m :: u :: rtail).Perm ((T_u :: ts).map FHTree.root) := by
      simp only [List.map, hu_root]
      exact (List.Perm.swap u m rtail).trans (List.Perm.cons u hperm)
    by_cases hlt : IndexedMinPQ.PrioLT (u, st.key u) (m, st.key m)
    · have hc_b : (Cond.lt zeroP s5).Holds x5 := by
        simp only [Cond.Holds]
        rw [hx5_z]
        simp only [x5, Data.set_regs, Function.update_self, bval, hlt, ↓reduceIte]
        exact Nat.zero_lt_one
      let x6 := x5.set minRootReg (u.val + 1)
      let x7 := x6.set numRootsReg (ts.length + 1)
      have he_upd : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s5) (.op (.exactBin .add minRootReg uReg oneP))
            (.op (.copy s0 zeroP))) x5 x6 2 := by
        have hu_lt := u.isLt
        have ha : ExecWithin w (.op (.exactBin .add minRootReg uReg oneP)) x5 x6 1 := by
          simpa only [hx5_u, hx5_o] using
            execWithin_exactAdd (x := x5) (d := minRootReg) (i := uReg) (j := oneP)
              (by rw [hx5_u, hx5_o]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
        exact (ExecWithin.branch_pos hc_b ha).mono (by omega)
      have hx6_nr : x6.regs numRootsReg = ts.length := by
        have : (RawState.ofData n base x5).numRoots = ts.length := by
          rw [hst5, hst2]; exact hnr
        simp only [x6, Data.set_regs,
          Function.update_of_ne (by decide : numRootsReg ≠ minRootReg)]
        exact this
      have hx6_o : x6.regs oneP = 1 := by
        simp only [x6, Data.set_regs,
          Function.update_of_ne (by decide : oneP ≠ minRootReg), hx5_o]
      have he_inc : ExecWithin w (.op (.exactBin .add numRootsReg numRootsReg oneP)) x6 x7 1 := by
        simpa only [hx6_nr, hx6_o] using
          execWithin_exactAdd (x := x6) (d := numRootsReg) (i := numRootsReg) (j := oneP)
            (by
              rw [hx6_nr, hx6_o]
              simp only [List.length_cons] at hfn_le
              unfold space at hfit_stop
              exact hfit_stop.of_le (by omega))
      have he : ExecWithin w (addRootAndUpdateMin uReg) x x7 28 := by
        unfold addRootAndUpdateMin
        exact ((ExecWithin.branch_neg hc
          (he_sub.seq <| he_ins.seq <| a1.seq <| l1.seq <| a2.seq <| l2.seq <|
            he_plt'.seq he_upd)).seq he_inc).mono (by omega)
      have hbr7 : BaseRegs n base x7 :=
        (hbr5.set_non_base (by decide) _).set_non_base (by decide) _
      have hst7 : RawState.ofData n base x7 =
          { RawState.ofData n base x2 with
            minRoot := u.val + 1
            numRoots := ts.length + 1 } := by
        simp only [x7, x6, ofData_set_numRoots, ofData_set_minRoot, hst5]
      refine ⟨x7, he, hbr7, hmod2, ?_⟩
      dsimp only
      have hk7 : (RawState.ofData n base x7).key = st.key := by rw [hst7, hst2]
      refine ⟨hk7, by rw [hst7, hst2], by rw [hst7, hst2], by rw [hst7, hst2], by rw [hst7, hst2],
        by rw [hst7, hst2], by rw [hst7, hst2], by rw [hst7, hst2], by rw [hst7, hst2],
        by rw [hst7]; rfl,
        hvalid_all _ hk7 (by rw [hst7, hst2]) (by rw [hst7, hst2]) (by rw [hst7, hst2])
          (by rw [hst7, hst2]) (by rw [hst7, hst2]) (by rw [hst7]) (by rw [hst7]),
        u, rtail ++ [m], by rw [hst7], ?_, ?_, ?_⟩
      · rw [hst7]
        exact hcirc2.rotate_one
      · have hrot_perm : (u :: (rtail ++ [m])).Perm (m :: u :: rtail) := by
          have h1 : (u :: (rtail ++ [m])).Perm ((u :: rtail) ++ [m]) := List.Perm.refl _
          exact h1.trans List.perm_append_comm
        exact hrot_perm.trans hperm_new
      · intro T hT
        rw [hk7]
        rcases List.mem_cons.mp hT with rfl | hT_ts
        · rw [hu_root]; exact IndexedMinPQ.PrioLE.refl _
        · exact (IndexedMinPQ.PrioLT.le hlt).trans (hmin_le T hT_ts)
    · have hc_b : ¬(Cond.lt zeroP s5).Holds x5 := by
        simp only [Cond.Holds]
        rw [hx5_z]
        simp only [x5, Data.set_regs, Function.update_self, bval, hlt, ↓reduceIte,
          lt_self_iff_false, not_false_eq_true]
      let x6 := x5.set s0 0
      let x7 := x6.set numRootsReg (ts.length + 1)
      have he_upd : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s5) (.op (.exactBin .add minRootReg uReg oneP))
            (.op (.copy s0 zeroP))) x5 x6 3 := by
        have hc0 : ExecWithin (B := .exact) w (.op (.copy s0 zeroP)) x5 x6 1 := by
          simpa only [hx5_z] using (ExecWithin.copy (B := .exact) (w := w) (x := x5)
            (d := s0) (s := zeroP))
        exact ExecWithin.branch_neg hc_b hc0
      have hx6_nr : x6.regs numRootsReg = ts.length := by
        have : (RawState.ofData n base x5).numRoots = ts.length := by
          rw [hst5, hst2]; exact hnr
        simp only [x6, Data.set_regs, Function.update_of_ne (by decide : numRootsReg ≠ s0)]
        exact this
      have hx6_o : x6.regs oneP = 1 := by
        simp only [x6, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ s0), hx5_o]
      have he_inc : ExecWithin w (.op (.exactBin .add numRootsReg numRootsReg oneP)) x6 x7 1 := by
        simpa only [hx6_nr, hx6_o] using
          execWithin_exactAdd (x := x6) (d := numRootsReg) (i := numRootsReg) (j := oneP)
            (by
              rw [hx6_nr, hx6_o]
              simp only [List.length_cons] at hfn_le
              unfold space at hfit_stop
              exact hfit_stop.of_le (by omega))
      have he : ExecWithin w (addRootAndUpdateMin uReg) x x7 28 := by
        unfold addRootAndUpdateMin
        exact ((ExecWithin.branch_neg hc
          (he_sub.seq <| he_ins.seq <| a1.seq <| l1.seq <| a2.seq <| l2.seq <|
            he_plt'.seq he_upd)).seq he_inc).mono (by omega)
      have hbr7 : BaseRegs n base x7 :=
        (hbr5.set_non_base (by decide) _).set_non_base (by decide) _
      have hst7 : RawState.ofData n base x7 =
          { RawState.ofData n base x2 with numRoots := ts.length + 1 } := by
        simp only [x7, x6, ofData_set_numRoots,
          ofData_set_scratch _ (by decide : 17 ≤ s0.val), hst5]
      refine ⟨x7, he, hbr7, hmod2, ?_⟩
      dsimp only
      have hk7 : (RawState.ofData n base x7).key = st.key := by rw [hst7, hst2]
      refine ⟨hk7, by rw [hst7, hst2], by rw [hst7, hst2], by rw [hst7, hst2], by rw [hst7, hst2],
        by rw [hst7, hst2], by rw [hst7, hst2], by rw [hst7, hst2], by rw [hst7, hst2],
        by rw [hst7]; rfl,
        hvalid_all _ hk7 (by rw [hst7, hst2]) (by rw [hst7, hst2]) (by rw [hst7, hst2])
          (by rw [hst7, hst2]) (by rw [hst7, hst2]) (by rw [hst7]) (by rw [hst7]),
        m, u :: rtail, by rw [hst7, hst2]; exact hmin_m, by rw [hst7]; exact hcirc2, hperm_new, ?_⟩
      intro T hT
      rw [hk7]
      rcases List.mem_cons.mp hT with rfl | hT_ts
      · rw [hu_root]; exact IndexedMinPQ.not_prioLT_iff_prioLE.mp hlt
      · exact hmin_le T hT_ts

/-! ## `allocSpan`, `initSetup`, and `incCur` -/

theorem incCur_eval {w : ℕ} {x : Data rFib} (hone : x.regs oneReg = 1)
    (hfit : Fits w (x.regs curReg + 1)) :
    (Op.exactBin .add curReg curReg oneReg).eval w x = some (x.set curReg (x.regs curReg + 1)) := by
  rw [Op.eval_exactBin]
  simp only [BinOp.evalExact, Option.bind_some, hone]
  exact Data.put_of_fits hfit

theorem allocSpan_exec {n w base : ℕ} (hS : Fits w (base + space n)) {x : Data rFib}
    (_hx : x.Bounded w) (hfr : x.regs frontierReg = base)
    (hpar : ∀ j : Fin 1, x.regs (![nReg] j) = ![n] j) :
    ∃ x₁, ExecWithin w allocSpan x x₁ 12 ∧ x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧ x₁.regs frontierReg = base + space n ∧
      (∀ j : Fin 1, x₁.regs (![nReg] j) = ![n] j) := by
  have hn : x.regs nReg = n := hpar 0
  unfold space at hS
  let fstep (a : Data rFib) (v : ℕ) := a.set frontierReg v
  let x0 := x.set baseReg base
  let x1 := fstep x0 (base + n)
  let x2 := fstep x1 (base + 2 * n)
  let x3 := fstep x2 (base + 3 * n)
  let x4 := fstep x3 (base + 4 * n)
  let x5 := fstep x4 (base + 5 * n)
  let x6 := fstep x5 (base + 6 * n)
  let x7 := fstep x6 (base + 7 * n)
  let x8 := fstep x7 (base + 8 * n)
  let x9 := fstep x8 (base + 9 * n)
  let x10 := x9.set s0 1
  let x11 := x10.set frontierReg (base + (9 * n + 1))
  have step_n : ∀ {a : Data rFib} {k : ℕ}, k < 9 →
      a.regs frontierReg = base + k * n → a.regs nReg = n →
      ExecWithin w (.op (.exactBin .add frontierReg frontierReg nReg)) a
        (a.set frontierReg (base + (k + 1) * n)) 1 := by
    intro a k hk ha_fr ha_n
    have heq : base + k * n + n = base + (k + 1) * n := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    have hle : base + (k + 1) * n ≤ base + (9 * n + 1) := by
      have : (k + 1) * n ≤ 9 * n := Nat.mul_le_mul_right n hk
      omega
    have h := execWithin_exactAdd (x := a) (d := frontierReg) (i := frontierReg) (j := nReg)
      (by rw [ha_fr, ha_n, heq]; exact hS.of_le hle)
    rw [ha_fr, ha_n, heq] at h
    exact h
  have e0 : ExecWithin (B := .exact) w (.op (.copy baseReg frontierReg)) x x0 1 := by
    simpa only [hfr] using (ExecWithin.copy (B := .exact) (w := w) (x := x)
      (d := baseReg) (s := frontierReg))
  have hn0 : x0.regs nReg = n := by
    simp only [x0, Data.set_regs, Function.update_of_ne (by decide : nReg ≠ baseReg), hn]
  have hf0 : x0.regs frontierReg = base + 0 * n := by
    simp only [x0, Data.set_regs, Function.update_of_ne (by decide : frontierReg ≠ baseReg),
      hfr, Nat.zero_mul, Nat.add_zero]
  have e1 := by
    simpa only [Nat.zero_add, Nat.one_mul] using step_n (k := 0) (by decide) hf0 hn0
  have hn_pres : ∀ (a : Data rFib) (v : ℕ), a.regs nReg = n → (fstep a v).regs nReg = n := by
    intro a v ha
    simp only [fstep, Data.set_regs, Function.update_of_ne (by decide : nReg ≠ frontierReg), ha]
  have hf_pres : ∀ (a : Data rFib) (v : ℕ), (fstep a v).regs frontierReg = v := by
    intro a v; simp only [fstep, Data.set_regs, Function.update_self]
  have e2 := step_n (k := 1) (by decide) (by simpa only [Nat.one_mul] using hf_pres x0 _)
    (hn_pres x0 _ hn0)
  have e3 := step_n (k := 2) (by decide) (hf_pres x1 _) (hn_pres x1 _ (hn_pres x0 _ hn0))
  have e4 := step_n (k := 3) (by decide) (hf_pres x2 _)
    (hn_pres x2 _ (hn_pres x1 _ (hn_pres x0 _ hn0)))
  have e5 := step_n (k := 4) (by decide) (hf_pres x3 _)
    (hn_pres x3 _ (hn_pres x2 _ (hn_pres x1 _ (hn_pres x0 _ hn0))))
  have e6 := step_n (k := 5) (by decide) (hf_pres x4 _)
    (hn_pres x4 _ (hn_pres x3 _ (hn_pres x2 _ (hn_pres x1 _ (hn_pres x0 _ hn0)))))
  have e7 := step_n (k := 6) (by decide) (hf_pres x5 _)
    (hn_pres x5 _ (hn_pres x4 _ (hn_pres x3 _ (hn_pres x2 _ (hn_pres x1 _ (hn_pres x0 _ hn0))))))
  have e8 := step_n (k := 7) (by decide) (hf_pres x6 _)
    (hn_pres x6 _ (hn_pres x5 _ (hn_pres x4 _ (hn_pres x3 _
      (hn_pres x2 _ (hn_pres x1 _ (hn_pres x0 _ hn0)))))))
  have e9 := step_n (k := 8) (by decide) (hf_pres x7 _)
    (hn_pres x7 _ (hn_pres x6 _ (hn_pres x5 _ (hn_pres x4 _ (hn_pres x3 _
      (hn_pres x2 _ (hn_pres x1 _ (hn_pres x0 _ hn0))))))))
  have e10 : ExecWithin (B := .exact) w (.op (.const s0 1)) x9 x10 1 :=
    ExecWithin.const (hS.of_le (by omega))
  have e11 : ExecWithin w (.op (.exactBin .add frontierReg frontierReg s0)) x10 x11 1 := by
    have hx10_fr : x10.regs frontierReg = base + 9 * n := by
      simp only [x10, x9, Data.set_regs, Function.update_of_ne (by decide : frontierReg ≠ s0),
        hf_pres x8 _]
    have hx10_s0 : x10.regs s0 = 1 := by simp only [x10, Data.set_regs, Function.update_self]
    have h := execWithin_exactAdd (x := x10) (d := frontierReg) (i := frontierReg) (j := s0)
      (by rw [hx10_fr, hx10_s0, Nat.add_assoc]; exact hS)
    rw [hx10_fr, hx10_s0, Nat.add_assoc] at h
    exact h
  have he : ExecWithin w allocSpan x x11 12 := by
    unfold allocSpan
    exact (e0.seq <| e1.seq <| e2.seq <| e3.seq <| e4.seq <| e5.seq <| e6.seq <| e7.seq <|
      e8.seq <| e9.seq <| e10.seq e11).mono (by omega)
  refine ⟨x11, he, rfl, ?_, ?_, ?_⟩
  · simp only [x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0, fstep, Data.set_regs,
      Function.update_of_ne (by decide : baseReg ≠ frontierReg),
      Function.update_of_ne (by decide : baseReg ≠ s0), Function.update_self]
  · simp only [x11, Data.set_regs, Function.update_self, space]
  · intro j
    fin_cases j
    exact (he.regs_eq (by decide)).trans hn

theorem initSetup_exec {n K_max w base : ℕ} {x₁ : Data rFib}
    (hx₁ : x₁.Bounded w) (hb₁ : x₁.regs baseReg = base)
    (hfr₁ : x₁.regs frontierReg = base + space n)
    (hpar₁ : ∀ j : Fin 1, x₁.regs (![nReg] j) = ![n] j)
    (hz : ∀ a ∈ (Block.mk base (space n)).footprint, x₁.mem a = 0) :
    ∃ y, ExecWithin w initSetup x₁ y 14 ∧ y.regs frontierReg = base + space n ∧
      FibInv n K_max w base (IndexedMinPQ.empty n) y ∧ potential y ≤ 0 ∧
      Modifies (Block.mk base (space n)).footprint x₁.mem y.mem := by
  have hn : x₁.regs nReg = n := hpar₁ 0
  have hS : Fits w (base + space n) := hfr₁ ▸ hx₁.1 frontierReg
  unfold space at hS
  have hfit0 : Fits w 0 := hS.of_le (Nat.zero_le _)
  have hfit1 : Fits w 1 := hS.of_le (by omega)
  let s1 := x₁.set parBase (base + n)
  let s2 := s1.set childBase (base + 2 * n)
  let s3 := s2.set leftBase (base + 3 * n)
  let s4 := s3.set rightBase (base + 4 * n)
  let s5 := s4.set degBase (base + 5 * n)
  let s6 := s5.set markBase (base + 6 * n)
  let s7 := s6.set inBase (base + 7 * n)
  let s8 := s7.set consBase (base + 8 * n)
  let s9 := s8.set zeroP 0
  let s10 := s9.set oneP 1
  let s11 := s10.set minRootReg 0
  let s12 := s11.set numRootsReg 0
  let s13 := s12.set numMarkedReg 0
  let y := s13.set szReg 0
  have mk_add : ∀ {a : Data rFib} {dst src : Fin rFib} {k : ℕ}, k < 8 →
      a.regs src = base + k * n → a.regs nReg = n →
      ExecWithin w (.op (.exactBin .add dst src nReg)) a (a.set dst (base + (k + 1) * n)) 1 := by
    intro a dst src k hk hsrc hn_a
    have heq : base + k * n + n = base + (k + 1) * n := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    have hle : base + (k + 1) * n ≤ base + (9 * n + 1) := by
      have : (k + 1) * n ≤ 8 * n := Nat.mul_le_mul_right n hk
      omega
    have h := execWithin_exactAdd (x := a) (d := dst) (i := src) (j := nReg)
      (by rw [hsrc, hn_a, heq]; exact hS.of_le hle)
    rw [hsrc, hn_a, heq] at h
    exact h
  have e1 := by
    simpa only [Nat.zero_add, Nat.one_mul] using
      mk_add (a := x₁) (dst := parBase) (src := baseReg) (k := 0) (by decide)
        (by simpa only [Nat.zero_mul, Nat.add_zero] using hb₁) hn
  have e2 :=
    mk_add (a := s1) (dst := childBase) (src := parBase) (k := 1) (by decide)
      (by simp only [s1, Data.set_regs, Function.update_self, Nat.one_mul])
      (by simp only [s1, Data.set_regs, Function.update_of_ne (by decide : nReg ≠ parBase), hn])
  have e3 :=
    mk_add (a := s2) (dst := leftBase) (src := childBase) (k := 2) (by decide)
      (by simp only [s2, Data.set_regs, Function.update_self])
      (by simp only [s2, s1, Data.set_regs,
        Function.update_of_ne (by decide : nReg ≠ childBase),
        Function.update_of_ne (by decide : nReg ≠ parBase), hn])
  have e4 :=
    mk_add (a := s3) (dst := rightBase) (src := leftBase) (k := 3) (by decide)
      (by simp only [s3, Data.set_regs, Function.update_self])
      (by simp only [s3, s2, s1, Data.set_regs,
        Function.update_of_ne (by decide : nReg ≠ leftBase),
        Function.update_of_ne (by decide : nReg ≠ childBase),
        Function.update_of_ne (by decide : nReg ≠ parBase), hn])
  have e5 :=
    mk_add (a := s4) (dst := degBase) (src := rightBase) (k := 4) (by decide)
      (by simp only [s4, Data.set_regs, Function.update_self])
      (by simp only [s4, s3, s2, s1, Data.set_regs,
        Function.update_of_ne (by decide : nReg ≠ rightBase),
        Function.update_of_ne (by decide : nReg ≠ leftBase),
        Function.update_of_ne (by decide : nReg ≠ childBase),
        Function.update_of_ne (by decide : nReg ≠ parBase), hn])
  have e6 :=
    mk_add (a := s5) (dst := markBase) (src := degBase) (k := 5) (by decide)
      (by simp only [s5, Data.set_regs, Function.update_self])
      (by simp only [s5, s4, s3, s2, s1, Data.set_regs,
        Function.update_of_ne (by decide : nReg ≠ degBase),
        Function.update_of_ne (by decide : nReg ≠ rightBase),
        Function.update_of_ne (by decide : nReg ≠ leftBase),
        Function.update_of_ne (by decide : nReg ≠ childBase),
        Function.update_of_ne (by decide : nReg ≠ parBase), hn])
  have e7 :=
    mk_add (a := s6) (dst := inBase) (src := markBase) (k := 6) (by decide)
      (by simp only [s6, Data.set_regs, Function.update_self])
      (by simp only [s6, s5, s4, s3, s2, s1, Data.set_regs,
        Function.update_of_ne (by decide : nReg ≠ markBase),
        Function.update_of_ne (by decide : nReg ≠ degBase),
        Function.update_of_ne (by decide : nReg ≠ rightBase),
        Function.update_of_ne (by decide : nReg ≠ leftBase),
        Function.update_of_ne (by decide : nReg ≠ childBase),
        Function.update_of_ne (by decide : nReg ≠ parBase), hn])
  have e8 :=
    mk_add (a := s7) (dst := consBase) (src := inBase) (k := 7) (by decide)
      (by simp only [s7, Data.set_regs, Function.update_self])
      (by simp only [s7, s6, s5, s4, s3, s2, s1, Data.set_regs,
        Function.update_of_ne (by decide : nReg ≠ inBase),
        Function.update_of_ne (by decide : nReg ≠ markBase),
        Function.update_of_ne (by decide : nReg ≠ degBase),
        Function.update_of_ne (by decide : nReg ≠ rightBase),
        Function.update_of_ne (by decide : nReg ≠ leftBase),
        Function.update_of_ne (by decide : nReg ≠ childBase),
        Function.update_of_ne (by decide : nReg ≠ parBase), hn])
  have he : ExecWithin w initSetup x₁ y 14 := by
    unfold initSetup
    exact (e1.seq <| e2.seq <| e3.seq <| e4.seq <| e5.seq <| e6.seq <| e7.seq <| e8.seq <|
      (ExecWithin.const (B := .exact) hfit0).seq <|
      (ExecWithin.const (B := .exact) hfit1).seq <|
      (ExecWithin.const (B := .exact) hfit0).seq <|
      (ExecWithin.const (B := .exact) hfit0).seq <|
      (ExecWithin.const (B := .exact) hfit0).seq
        (ExecWithin.const (B := .exact) hfit0)).mono (by omega)
  have hfr_y : y.regs frontierReg = base + space n :=
    (he.regs_eq (by decide)).trans hfr₁
  have hn_y : y.regs nReg = n := (he.regs_eq (by decide)).trans hn
  have hb_y : y.regs baseReg = base := (he.regs_eq (by decide)).trans hb₁
  have hmem_y : y.mem = x₁.mem := rfl
  have hbr_y : BaseRegs n base y := by
    refine ⟨hn_y, hfr_y, hb_y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [y, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        Data.set_regs, Function.update_apply] <;>
      rfl
  refine ⟨y, he, hfr_y, ⟨he.bounded hx₁, hbr_y, ?_⟩, ?_, Modifies.refl _ _⟩
  · apply FibRawInv.empty
    · intro v
      change x₁.mem (base + 7 * n + v.val) = 0
      exact hz _ (Block.mem_footprint.mpr (owns_arr_addr (by decide) v.isLt))
    · intro d hd
      change (if d ≤ n then x₁.mem (base + 8 * n + d) else 0) = 0
      simp only [hd, ↓reduceIte]
      exact hz _ (Block.mem_footprint.mpr (owns_cons_addr hd))
    · simp only [RawState.ofData, y, s13, s12, s11, Data.set_regs, Function.update_apply]
      rfl
    · simp only [RawState.ofData, y, s13, s12, Data.set_regs, Function.update_apply]
      rfl
    · simp only [RawState.ofData, y, s13, Data.set_regs, Function.update_apply]
      rfl
    · simp only [RawState.ofData, y, Data.set_regs, Function.update_apply]
      rfl
  · have hnr0 : y.regs numRootsReg = 0 := by
      simp only [y, s13, s12, Data.set_regs, Function.update_apply]; rfl
    have hnm0 : y.regs numMarkedReg = 0 := by
      simp only [y, s13, Data.set_regs, Function.update_apply]; rfl
    simp only [potential, hnr0, hnm0, Nat.mul_zero, Nat.add_zero, le_rfl]

/-! ## `isEmptyCode`, `getKeyCode`, and `insertCode` -/

theorem isEmptyCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (hinv : FibInv n K_max w base s x) :
    ∃ y t, ExecWithin w isEmptyCode x y t ∧
      code.decode (n := n) (K_max := K_max) .isEmpty y.regs =
        some (decide (IndexedMinPQ.dom s = ∅)) ∧
      FibInv n K_max w base s y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤ 3 + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  by_cases hm : x.regs minRootReg = 0
  · have hc : (Cond.eq minRootReg zeroP).Holds x := by simp only [Cond.Holds, hz0, hm]
    let y := x.set outFlag 1
    have he : ExecWithin w isEmptyCode x y 2 := by
      unfold isEmptyCode
      exact ExecWithin.branch_pos hc (by simpa only [ho1] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := outFlag) (s := oneP)))
    obtain ⟨hdom, _⟩ := hraw.findMin_eq_none hm
    refine ⟨y, 2, he, ?_, ⟨he.bounded hb, hbr.set_non_base (by decide) 1,
      (ofData_set_scratch x (by decide : 17 ≤ outFlag.val) 1).symm ▸ hraw⟩,
      Modifies.refl _ _, ?_⟩
    · simp only [PQCode.decode, code, y, Data.set_regs, Function.update_self, hdom,
        decide_true, ne_eq, one_ne_zero, not_false_eq_true]
      rfl
    · have hp : potential y = potential x :=
        potential_supported fun i hi => by
          have hne : i ≠ outFlag := fun e => by subst e; cases hi
          simp only [y, Data.set_regs, Function.update_of_ne hne]
      omega
  · have hc : ¬(Cond.eq minRootReg zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact hm
    let y := x.set outFlag 0
    have he : ExecWithin w isEmptyCode x y 3 := by
      unfold isEmptyCode
      exact ExecWithin.branch_neg hc (by simpa only [hz0] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := outFlag) (s := zeroP)))
    have hdom_ne : IndexedMinPQ.dom s ≠ ∅ := by
      have hm_le : x.regs minRootReg ≤ n := hraw.bounds.2.2.2
      let z : Fin n := ⟨x.regs minRootReg - 1, by omega⟩
      have hz_eq : (RawState.ofData n base x).minRoot = z.val + 1 := by
        change x.regs minRootReg = x.regs minRootReg - 1 + 1; omega
      obtain ⟨_, hsz, _⟩ := hraw.findMin_eq_some hz_eq
      intro hemp
      have hmem : z ∈ IndexedMinPQ.dom s := IndexedMinPQ.mem_dom_iff.mpr ⟨_, hsz⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty z hmem
    refine ⟨y, 3, he, ?_, ⟨he.bounded hb, hbr.set_non_base (by decide) 0,
      (ofData_set_scratch x (by decide : 17 ≤ outFlag.val) 0).symm ▸ hraw⟩,
      Modifies.refl _ _, ?_⟩
    · simp only [PQCode.decode, code, y, Data.set_regs, Function.update_self, hdom_ne,
        decide_false, ne_eq, not_true_eq_false]
      rfl
    · have hp : potential y = potential x :=
        potential_supported fun i hi => by
          have hne : i ≠ outFlag := fun e => by subst e; cases hi
          simp only [y, Data.set_regs, Function.update_of_ne hne]
      omega

theorem getKeyCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (v : Fin n) (hinv : FibInv n K_max w base s x) (hv_reg : x.regs argV = v.val) :
    ∃ y t, ExecWithin w getKeyCode x y t ∧
      code.decode (K_max := K_max) (.getKey v) y.regs = some (s v) ∧
      FibInv n K_max w base s y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤ 7 + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  have hfit_stop := hbr.fits_stop hb
  have hin_b : x.regs inBase = base + 7 * n := hbr.2.2.2.2.2.2.2.2.2.1
  have hb_b : x.regs baseReg = base := hbr.2.2.1
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  let st := RawState.ofData n base x
  have hraw' : FibRawInv n K_max s st := hraw
  rcases hraw with ⟨_, _, _, _, hin_spec, hkey_spec, _, _, _, _, _⟩
  have ho_in := owns_arr_addr (base := base) (k := 7) (by decide) v.isLt
  let x1 := (x.set s0 (base + 7 * n + v.val)).set outFlag (st.inHeap v)
  have ea1 : ExecWithin w (.op (.exactBin .add s0 inBase argV)) x
      (x.set s0 (base + 7 * n + v.val)) 1 := by
    simpa only [hin_b, hv_reg] using
      execWithin_exactAdd (x := x) (d := s0) (i := inBase) (j := argV)
        (by rw [hin_b, hv_reg]; exact hfit_stop.of_le (by omega))
  have el1 : ExecWithin (B := .exact) w (.op (.load outFlag s0))
      (x.set s0 (base + 7 * n + v.val)) x1 1 := by
    have hin_mem : x.mem (base + 7 * n + v.val) = st.inHeap v := rfl
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hin_mem] using
      (ExecWithin.load (B := .exact) (w := w) (x := x.set s0 (base + 7 * n + v.val))
        (d := outFlag) (a := s0))
  have hx1_z : x1.regs zeroP = 0 := by
    simp only [x1, Data.set_regs, Function.update_of_ne (by decide : zeroP ≠ outFlag),
      Function.update_of_ne (by decide : zeroP ≠ s0), hz0]
  cases hsv : s v with
  | none =>
    have hin0 : st.inHeap v = 0 := by
      by_contra hne
      have := (hin_spec v).1.mp hne
      simp only [hsv, Option.isSome_none, Bool.false_eq_true] at this
    have hc : (Cond.eq outFlag zeroP).Holds x1 := by
      simp only [Cond.Holds]
      rw [hx1_z]
      simp only [x1, Data.set_regs, Function.update_self, hin0]
    let y := x1.set s0 0
    have he2 : ExecWithin (B := .exact) w
        (.branch (.eq outFlag zeroP) (.op (.copy s0 zeroP))
          (.seq (.op (.exactBin .add s0 baseReg argV)) (.op (.load outK s0)))) x1 y 2 :=
      ExecWithin.branch_pos hc (by simpa only [hx1_z] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x1) (d := s0) (s := zeroP)))
    have he : ExecWithin w getKeyCode x y 4 := by
      unfold getKeyCode
      exact (ea1.seq (el1.seq he2)).mono (by omega)
    have hreg_pres : ∀ i : Fin rFib, inputReg i = false → y.regs i = x.regs i := fun i hi => by
      have h1 : i ≠ s0 := fun e => by subst e; cases hi
      have h2 : i ≠ outFlag := fun e => by subst e; cases hi
      simp only [y, x1, Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h2]
    refine ⟨y, 4, he, ?_,
      FibInv.supported hreg_pres (fun _ _ => rfl) (he.bounded hb) ⟨hb, hbr, hraw'⟩,
      Modifies.refl _ _, by rw [potential_supported hreg_pres]; omega⟩
    simp only [PQCode.decode, code, y, x1, Data.set_regs,
      Function.update_of_ne (by decide : outFlag ≠ s0), Function.update_self, hin0, ↓reduceIte]
    rfl
  | some kv =>
    have hin_ne : st.inHeap v ≠ 0 :=
      (hin_spec v).1.mpr (by simp only [hsv, Option.isSome_some])
    have hkv_eq : st.key v = kv := (hkey_spec v kv hsv).1
    have hc : ¬(Cond.eq outFlag zeroP).Holds x1 := by
      simp only [Cond.Holds]
      rw [hx1_z]
      simp only [x1, Data.set_regs, Function.update_self]
      exact hin_ne
    have hx1_b : x1.regs baseReg = base := by
      simp only [x1, Data.set_regs, Function.update_of_ne (by decide : baseReg ≠ outFlag),
        Function.update_of_ne (by decide : baseReg ≠ s0), hb_b]
    have hx1_v : x1.regs argV = v.val := by
      simp only [x1, Data.set_regs, Function.update_of_ne (by decide : argV ≠ outFlag),
        Function.update_of_ne (by decide : argV ≠ s0), hv_reg]
    let y := (x1.set s0 (base + v.val)).set outK kv
    have he2 : ExecWithin (B := .exact) w
        (.branch (.eq outFlag zeroP) (.op (.copy s0 zeroP))
          (.seq (.op (.exactBin .add s0 baseReg argV)) (.op (.load outK s0)))) x1 y 4 := by
      have hv_lt := v.isLt
      have a2 : ExecWithin w (.op (.exactBin .add s0 baseReg argV)) x1
          (x1.set s0 (base + v.val)) 1 := by
        simpa only [hx1_b, hx1_v] using
          execWithin_exactAdd (x := x1) (d := s0) (i := baseReg) (j := argV)
            (by rw [hx1_b, hx1_v]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
      have l2 : ExecWithin (B := .exact) w (.op (.load outK s0))
          (x1.set s0 (base + v.val)) y 1 := by
        have hmem_kv : x.mem (base + v.val) = kv := hkv_eq
        simpa only [x1, Data.set_mem, Data.set_regs, Function.update_self, hmem_kv] using
          (ExecWithin.load (B := .exact) (w := w) (x := x1.set s0 (base + v.val))
            (d := outK) (a := s0))
      exact ExecWithin.branch_neg hc (a2.seq l2)
    have he : ExecWithin w getKeyCode x y 6 := by
      unfold getKeyCode
      exact (ea1.seq (el1.seq he2)).mono (by omega)
    have hreg_pres : ∀ i : Fin rFib, inputReg i = false → y.regs i = x.regs i := fun i hi => by
      have h1 : i ≠ outK := fun e => by subst e; cases hi
      have h2 : i ≠ s0 := fun e => by subst e; cases hi
      have h3 : i ≠ outFlag := fun e => by subst e; cases hi
      simp only [y, x1, Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3]
    refine ⟨y, 6, he, ?_,
      FibInv.supported hreg_pres (fun _ _ => rfl) (he.bounded hb) ⟨hb, hbr, hraw'⟩,
      Modifies.refl _ _, by rw [potential_supported hreg_pres]; omega⟩
    simp only [PQCode.decode, code, y, x1, Data.set_regs,
      Function.update_of_ne (by decide : outFlag ≠ outK),
      Function.update_of_ne (by decide : outFlag ≠ s0), Function.update_self, hin_ne, ↓reduceIte]
    rfl

theorem insertCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (v : Fin n) (k : ℕ) (hinv : FibInv n K_max w base s x)
    (hval : s v = none ∧ k ≤ K_max) (hv_reg : x.regs argV = v.val) (hk_reg : x.regs argK = k) :
    ∃ y t, ExecWithin w insertCode x y t ∧
      FibInv n K_max w base (Function.update s v (some k)) y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤ 121 + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  have hfit_stop := hbr.fits_stop hb
  let st := RawState.ofData n base x
  obtain ⟨ts, hts, hnd, hdom, hin_spec, hkey_spec, hsz, hnr, hnm, hcons, hrl⟩ := hraw
  have hb0 : x.regs baseReg = base := hbr.2.2.1
  have hb1 : x.regs parBase = base + n := hbr.2.2.2.1
  have hb2 : x.regs childBase = base + 2 * n := hbr.2.2.2.2.1
  have hb5 : x.regs degBase = base + 5 * n := hbr.2.2.2.2.2.2.2.1
  have hb6 : x.regs markBase = base + 6 * n := hbr.2.2.2.2.2.2.2.2.1
  have hb7 : x.regs inBase = base + 7 * n := hbr.2.2.2.2.2.2.2.2.2.1
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  have ho_k := owns_arr_addr (base := base) (k := 0) (by decide) v.isLt
  have ho_p := owns_arr_addr (base := base) (k := 1) (by decide) v.isLt
  have ho_c := owns_arr_addr (base := base) (k := 2) (by decide) v.isLt
  have ho_d := owns_arr_addr (base := base) (k := 5) (by decide) v.isLt
  have ho_m := owns_arr_addr (base := base) (k := 6) (by decide) v.isLt
  have ho_i := owns_arr_addr (base := base) (k := 7) (by decide) v.isLt
  let x1 := (x.set s0 (base + v.val)).write (base + v.val) k
  let x2 := (x1.set s0 (base + n + v.val)).write (base + n + v.val) 0
  let x3 := (x2.set s0 (base + 2 * n + v.val)).write (base + 2 * n + v.val) 0
  let x4 := (x3.set s0 (base + 5 * n + v.val)).write (base + 5 * n + v.val) 0
  let x5 := (x4.set s0 (base + 6 * n + v.val)).write (base + 6 * n + v.val) 0
  let x6 := (x5.set s0 (base + 7 * n + v.val)).write (base + 7 * n + v.val) 1
  have wr_step : ∀ {a : Data rFib} {bReg valReg : Fin rFib} {addr val : ℕ},
      bReg ≠ s0 → valReg ≠ s0 → a.regs bReg + a.regs argV = addr → a.regs valReg = val →
      addr < base + space n →
      ExecWithin w (.seq (.op (.exactBin .add s0 bReg argV)) (.op (.store s0 valReg))) a
        ((a.set s0 addr).write addr val) 2 := by
    intro a bReg valReg addr val hb_ne hv_ne haddr hval_a hlt
    have ea : ExecWithin w (.op (.exactBin .add s0 bReg argV)) a (a.set s0 addr) 1 := by
      have h := execWithin_exactAdd (x := a) (d := s0) (i := bReg) (j := argV)
        (by rw [haddr]; exact hfit_stop.of_le (Nat.le_of_lt hlt))
      rw [haddr] at h
      exact h
    have es : ExecWithin (B := .exact) w (.op (.store s0 valReg)) (a.set s0 addr)
        ((a.set s0 addr).write addr val) 1 := by
      simpa only [Data.set_regs, Function.update_self, Function.update_of_ne hv_ne, hval_a] using
        (ExecWithin.store (B := .exact) (w := w) (x := a.set s0 addr) (a := s0) (s := valReg))
    exact ea.seq es
  have wr_cps : ∀ {T : ℕ} {a z : Data rFib} {bReg valReg : Fin rFib} {addr val : ℕ}
      {rest : Code .exact rFib},
      bReg ≠ s0 → valReg ≠ s0 → a.regs bReg + a.regs argV = addr → a.regs valReg = val →
      addr < base + space n →
      ExecWithin w rest ((a.set s0 addr).write addr val) z T →
      ExecWithin w (.seq (.op (.exactBin .add s0 bReg argV))
        (.seq (.op (.store s0 valReg)) rest)) a z (2 + T) := by
    intro T a z bReg valReg addr val rest hb_ne hv_ne haddr hval_a hlt hrest
    have ea : ExecWithin w (.op (.exactBin .add s0 bReg argV)) a (a.set s0 addr) 1 := by
      have h := execWithin_exactAdd (x := a) (d := s0) (i := bReg) (j := argV)
        (by rw [haddr]; exact hfit_stop.of_le (Nat.le_of_lt hlt))
      rw [haddr] at h
      exact h
    have es : ExecWithin (B := .exact) w (.op (.store s0 valReg)) (a.set s0 addr)
        ((a.set s0 addr).write addr val) 1 := by
      simpa only [Data.set_regs, Function.update_self, Function.update_of_ne hv_ne, hval_a] using
        (ExecWithin.store (B := .exact) (w := w) (x := a.set s0 addr) (a := s0) (s := valReg))
    exact (ea.seq (es.seq hrest)).mono (by omega)
  have hx_regs : ∀ {r : Fin rFib}, r ≠ s0 →
      x1.regs r = x.regs r ∧ x2.regs r = x.regs r ∧ x3.regs r = x.regs r ∧
      x4.regs r = x.regs r ∧ x5.regs r = x.regs r ∧ x6.regs r = x.regs r := fun hne => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [x6, x5, x4, x3, x2, x1, Data.write_regs, Data.set_regs,
        Function.update_of_ne hne]
  have e1 :=
    wr_step (a := x) (bReg := baseReg) (valReg := argK) (by decide) (by decide)
      (by rw [hb0, hv_reg]) hk_reg (by simpa only [Nat.zero_mul, Nat.add_zero] using ho_k.2)
  have e2 :=
    wr_step (a := x1) (bReg := parBase) (valReg := zeroP) (by decide) (by decide)
      (by rw [(hx_regs (by decide)).1, (hx_regs (by decide)).1, hb1, hv_reg])
      (by rw [(hx_regs (by decide)).1, hz0]) (by simpa only [Nat.one_mul] using ho_p.2)
  have e3 :=
    wr_step (a := x2) (bReg := childBase) (valReg := zeroP) (by decide) (by decide)
      (by rw [(hx_regs (by decide)).2.1, (hx_regs (by decide)).2.1, hb2, hv_reg])
      (by rw [(hx_regs (by decide)).2.1, hz0]) ho_c.2
  have e4 :=
    wr_step (a := x3) (bReg := degBase) (valReg := zeroP) (by decide) (by decide)
      (by rw [(hx_regs (by decide)).2.2.1, (hx_regs (by decide)).2.2.1, hb5, hv_reg])
      (by rw [(hx_regs (by decide)).2.2.1, hz0]) ho_d.2
  have e5 :=
    wr_step (a := x4) (bReg := markBase) (valReg := zeroP) (by decide) (by decide)
      (by rw [(hx_regs (by decide)).2.2.2.1, (hx_regs (by decide)).2.2.2.1, hb6, hv_reg])
      (by rw [(hx_regs (by decide)).2.2.2.1, hz0]) ho_m.2
  have e6 :=
    wr_step (a := x5) (bReg := inBase) (valReg := oneP) (by decide) (by decide)
      (by rw [(hx_regs (by decide)).2.2.2.2.1, (hx_regs (by decide)).2.2.2.2.1, hb7, hv_reg])
      (by rw [(hx_regs (by decide)).2.2.2.2.1, ho1]) ho_i.2
  have hb6_bnd : x6.Bounded w :=
    e6.bounded (e5.bounded (e4.bounded (e3.bounded (e2.bounded (e1.bounded hb)))))
  have hbr6 : BaseRegs n base x6 := by
    have he16 := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
    exact hbr.preserved he16 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have hmod16 : Modifies (Block.mk base (space n)).footprint x.mem x6.mem :=
    modifies_block_trans
      (Modifies.write_of_owns (by simpa only [Nat.zero_mul, Nat.add_zero] using ho_k) k) <|
    modifies_block_trans
      (Modifies.write_of_owns (by simpa only [Nat.one_mul] using ho_p) 0) <|
    modifies_block_trans (Modifies.write_of_owns ho_c 0) <|
    modifies_block_trans (Modifies.write_of_owns ho_d 0) <|
    modifies_block_trans (Modifies.write_of_owns ho_m 0)
      (Modifies.write_of_owns ho_i 1)
  have hst6 : RawState.ofData n base x6 =
      { st with
        key := Function.update st.key v k
        par := Function.update st.par v 0
        child := Function.update st.child v 0
        deg := Function.update st.deg v 0
        mark := Function.update st.mark v 0
        inHeap := Function.update st.inHeap v 1 } := by
    simp only [x6, x5, x4, x3, x2, x1, ofData_write_inHeap, ofData_write_mark,
      ofData_write_deg, ofData_write_child, ofData_write_par, ofData_write_key,
      ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
    rfl
  have hv_not_fn : v ∉ forestNodes ts := fun hm => by
    have := (hdom v).mp hm
    simp only [hval.1, Option.isSome_none, Bool.false_eq_true] at this
  have hnd_new : (forestNodes (.node v [] :: ts)).Nodup := by
    simp only [forestNodes, FHTree.nodes, List.singleton_append]
    exact List.nodup_cons.mpr ⟨hv_not_fn, hnd⟩
  have hTv : ValidRoot (RawState.ofData n base x6) none (.node v []) := by
    rw [hst6]
    exact ValidRoot.singleton
      (by simp only [Function.update_self, ne_eq, one_ne_zero, not_false_eq_true])
      (by simp only [Function.update_self]) (by simp only [Function.update_self])
      (by simp only [Function.update_self]) (by simp only [Function.update_self])
  have hts6 : ∀ T ∈ ts, ValidRoot (RawState.ofData n base x6) none T := by
    intro T hT
    have hv_not_T : v ∉ T.nodes := fun hm => hv_not_fn (mem_forestNodes_iff.mpr ⟨T, hT, hm⟩)
    have hvr : T.root ≠ v := fun e => hv_not_T (e ▸ T.root_mem_nodes)
    have hold := hts T hT
    rw [hst6]
    refine ⟨hold.1.frame (fun u hu => ?_) (fun u hu => ?_),
      by simp only [Function.update_of_ne hvr]; exact hold.2.1,
      by simp only [Function.update_of_ne hvr]; exact hold.2.2⟩
    · have huv : u ≠ v := fun e => hv_not_T (e ▸ hu)
      simp only [Function.update_of_ne huv]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · have huv : u ≠ v := fun e =>
        hv_not_T (e ▸ (T.nodes_eq ▸ List.mem_cons_of_mem T.root hu))
      simp only [Function.update_of_ne huv]
      exact ⟨rfl, rfl, rfl, trivial⟩
  have hrl6 : (ts = [] ∧ (RawState.ofData n base x6).minRoot = 0) ∨
      ∃ (m : Fin n) (rtail : List (Fin n)),
        (RawState.ofData n base x6).minRoot = m.val + 1 ∧
        IsCircList (RawState.ofData n base x6).left (RawState.ofData n base x6).right
          (m :: rtail) ∧
        (m :: rtail).Perm (ts.map FHTree.root) ∧
        ∀ T ∈ ts, IndexedMinPQ.PrioLE
          (m, (RawState.ofData n base x6).key m)
          (T.root, (RawState.ofData n base x6).key T.root) := by
    rcases hrl with ⟨rfl, hm0⟩ | ⟨m, rtail, hm, hcirc, hperm, hmin_le⟩
    · exact Or.inl ⟨rfl, by rw [hst6]; exact hm0⟩
    · refine Or.inr ⟨m, rtail, by rw [hst6]; exact hm, by rw [hst6]; exact hcirc, hperm, ?_⟩
      intro T hT
      obtain ⟨Rm, hRm, hRm_r⟩ := List.mem_map.mp (hperm.subset List.mem_cons_self)
      have hmv : m ≠ v := fun e =>
        hv_not_fn (mem_forestNodes_iff.mpr ⟨Rm, hRm, e ▸ hRm_r ▸ Rm.root_mem_nodes⟩)
      have htv : T.root ≠ v := fun e =>
        hv_not_fn (mem_forestNodes_iff.mpr ⟨T, hT, e ▸ T.root_mem_nodes⟩)
      rw [hst6]
      simp only [Function.update_of_ne hmv, Function.update_of_ne htv]
      exact hmin_le T hT
  have hx6_v : x6.regs argV = v.val := (hx_regs (by decide)).2.2.2.2.2.trans hv_reg
  obtain ⟨x7, he_add, hbr7, hmod7, hst7_props⟩ :=
    addRootAndUpdateMin_exec hb6_bnd hbr6
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      hx6_v (T_u := .node v []) rfl hnd_new hTv hts6 (by rw [hst6]; exact hnr) hrl6
  dsimp only at hst7_props
  obtain ⟨hk7, hp7, hc7, hd7, hm7, hi7, hcons7, hnm7, hsz7, hnr7, hvalid7, hrl7⟩ := hst7_props
  have hdom_new : IndexedMinPQ.dom (Function.update s v (some k)) = insert v (IndexedMinPQ.dom s) :=
    IndexedMinPQ.dom_insert s v k
  have hv_not_dom : v ∉ IndexedMinPQ.dom s := IndexedMinPQ.notMem_dom_iff.mpr hval.1
  have hcard_new : (IndexedMinPQ.dom (Function.update s v (some k))).card = st.sz + 1 := by
    rw [hdom_new, Finset.card_insert_of_notMem hv_not_dom, hsz]
  have hcard_le : st.sz + 1 ≤ n := by
    rw [← hcard_new]
    exact (Finset.card_le_univ _).trans (by simp only [Fintype.card_fin, le_rfl])
  let y := x7.set szReg (st.sz + 1)
  have hx7_sz : x7.regs szReg = st.sz := by
    change (RawState.ofData n base x7).sz = st.sz
    rw [hsz7, hst6]
  have hx7_o : x7.regs oneP = 1 := hbr7.2.2.2.2.2.2.2.2.2.2.2.2
  have he_sz : ExecWithin w (.op (.exactBin .add szReg szReg oneP)) x7 y 1 := by
    simpa only [hx7_sz, hx7_o] using
      execWithin_exactAdd (x := x7) (d := szReg) (i := szReg) (j := oneP)
        (by rw [hx7_sz, hx7_o]; unfold space at hfit_stop; exact hfit_stop.of_le (by omega))
  have he : ExecWithin w insertCode x y 41 := by
    unfold insertCode
    exact (wr_cps (a := x) (by decide) (by decide) (by rw [hb0, hv_reg]) hk_reg
      (by simpa only [Nat.zero_mul, Nat.add_zero] using ho_k.2) <|
      wr_cps (a := x1) (by decide) (by decide)
        (by rw [(hx_regs (by decide)).1, (hx_regs (by decide)).1, hb1, hv_reg])
        (by rw [(hx_regs (by decide)).1, hz0])
        (by simpa only [Nat.one_mul] using ho_p.2) <|
      wr_cps (a := x2) (by decide) (by decide)
        (by rw [(hx_regs (by decide)).2.1, (hx_regs (by decide)).2.1, hb2, hv_reg])
        (by rw [(hx_regs (by decide)).2.1, hz0]) ho_c.2 <|
      wr_cps (a := x3) (by decide) (by decide)
        (by rw [(hx_regs (by decide)).2.2.1, (hx_regs (by decide)).2.2.1, hb5, hv_reg])
        (by rw [(hx_regs (by decide)).2.2.1, hz0]) ho_d.2 <|
      wr_cps (a := x4) (by decide) (by decide)
        (by rw [(hx_regs (by decide)).2.2.2.1, (hx_regs (by decide)).2.2.2.1, hb6, hv_reg])
        (by rw [(hx_regs (by decide)).2.2.2.1, hz0]) ho_m.2 <|
      wr_cps (a := x5) (by decide) (by decide)
        (by rw [(hx_regs (by decide)).2.2.2.2.1, (hx_regs (by decide)).2.2.2.2.1, hb7, hv_reg])
        (by rw [(hx_regs (by decide)).2.2.2.2.1, ho1]) ho_i.2
        (he_add.seq he_sz)).mono (by omega)
  have hsty : RawState.ofData n base y =
      { RawState.ofData n base x7 with sz := st.sz + 1 } := ofData_set_sz x7 (st.sz + 1)
  have hmod : Modifies (Block.mk base (space n)).footprint x.mem y.mem :=
    modifies_block_trans hmod16 hmod7
  refine ⟨y, 41, he, ⟨he.bounded hb, hbr7.set_non_base (by decide) _, ?_⟩, hmod, ?_⟩
  · refine ⟨.node v [] :: ts, ?_, hnd_new, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr ?_⟩
    · intro T hT
      have h7 := hvalid7 T hT
      rw [hsty]
      exact ⟨h7.1.frame (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)
        (fun _ _ => ⟨rfl, rfl, rfl, Iff.rfl⟩), h7.2.1, h7.2.2⟩
    · intro u
      simp only [forestNodes, FHTree.nodes, List.singleton_append, List.mem_cons]
      by_cases huv : u = v
      · subst huv; simp only [true_or, Function.update_self, Option.isSome_some]
      · simp only [huv, false_or, Function.update_of_ne huv, hdom u]
    · intro u
      rw [hsty]
      dsimp only
      rw [hi7, hst6]
      by_cases huv : u = v
      · subst huv
        simp only [Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Option.isSome_some,
          le_rfl, and_self]
      · simp only [Function.update_of_ne huv]
        exact hin_spec u
    · intro u ku hsu
      rw [hsty]
      dsimp only
      rw [hk7, hst6]
      by_cases huv : u = v
      · subst huv
        simp only [Function.update_self, Option.some.injEq] at hsu
        subst hsu
        simp only [Function.update_self, hval.2, and_self]
      · simp only [Function.update_of_ne huv] at hsu ⊢
        exact hkey_spec u ku hsu
    · rw [hsty, hcard_new]
    · rw [hsty]; exact hnr7
    · have hm_eq : markedCount (RawState.ofData n base y) = markedCount st := by
        apply markedCount_congr
        intro u
        rw [hsty]
        dsimp only
        rw [hi7, hm7, hst6]
        by_cases huv : u = v
        · subst huv
          have hin0 : st.inHeap u = 0 := by
            by_contra hne
            have := (hin_spec u).1.mp hne
            simp only [hval.1, Option.isSome_none, Bool.false_eq_true] at this
          simp only [Function.update_self, hin0, ne_eq, not_true_eq_false, and_false, false_and]
        · simp only [Function.update_of_ne huv]
      rw [hm_eq, hsty]
      dsimp only
      rw [hnm7, hst6]
      exact hnm
    · intro d hd
      rw [hsty]
      dsimp only
      rw [hcons7, hst6]
      exact hcons d hd
    · obtain ⟨m', rtail', hm', hcirc', hperm', hle'⟩ := hrl7
      exact ⟨m', rtail', by rw [hsty]; exact hm', by rw [hsty]; exact hcirc', hperm',
        fun T hT => by rw [hsty]; exact hle' T hT⟩
  · have hy_nr : y.regs numRootsReg = st.numRoots + 1 := by
      change (RawState.ofData n base y).numRoots = st.numRoots + 1
      rw [hsty]
      dsimp only
      rw [hnr7, List.length_cons, hnr]
    have hy_nm : y.regs numMarkedReg = st.numMarked := by
      change (RawState.ofData n base y).numMarked = st.numMarked
      rw [hsty]
      dsimp only
      rw [hnm7, hst6]
    have hx_nr : x.regs numRootsReg = st.numRoots := rfl
    have hx_nm : x.regs numMarkedReg = st.numMarked := rfl
    simp only [potential, hy_nr, hy_nm, hx_nr, hx_nm, unitCredit]
    omega

end Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap
