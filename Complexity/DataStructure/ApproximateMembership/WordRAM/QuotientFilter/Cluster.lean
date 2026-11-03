/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.ApproximateMembership.QuotientFilter.Operations
public import Complexity.DataStructure.ApproximateMembership.WordRAM.QuotientFilter.SlotArray

/-!
# Word-RAM Cluster Navigation, Scan, and Shift Loops for the Quotient Filter

This file implements the cluster-level Word-RAM programs for the quotient filter on `Data 248`:
* `findClusterCode`: walks backwards and forwards from `q` (`reg 2`) to locate the maximal full
  cluster `[o .. o + ℓ)` around `q`, computing `a = backLen q` (`reg 4`),
  `o = clusterStart q` (`reg 5`), and `ℓ = clusterLen q` (`reg 6`) in `O(ℓ + 1)` instructions.
* `scanClusterCode`: computes `occBefore st o a` (`reg 10`), `(st.isOcc q).toNat` (`reg 11`),
  `occBefore st o (a + 1)` (`reg 12`), and scans `[o .. o + ℓ)` in a single `O(ℓ + 1)` pass to
  compute `s₀ = calcRunStart st o a ℓ` (`reg 15`), `s = calcTargetSlot st o a ℓ r` (`reg 16`),
  `e = calcDeleteStop st o a ℓ` (`reg 17`), and `(queryCluster st o a ℓ r).toNat` (`reg 18`).
* `insertClusterCode` and `deleteClusterCode`: perform `shiftRight` / `shiftLeft` and update the
  slot metadata and remainders to realize `insertCluster` and `deleteCluster` in `O(ℓ + 1)`
  instructions.
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.WordRAM.QuotientFilter

open Cslib.WordRAM
open Cslib.DataStructure.ApproximateMembership.QuotientFilter
open scoped Finset

/-! ## Section 1: `ClusterState`, `AgreeOutsideScratch`, and constant-time conditional helpers -/

/-- Register agreement outside the `SlotArray` scratch range `30..35`. -/
@[expose] def AgreeOutsideScratch (g s : Data rQF) : Prop :=
  ∀ j : Fin rQF, (j.val < 30 ∨ 36 ≤ j.val) → s.regs j = g.regs j

theorem AgreeOutsideScratch.refl (x : Data rQF) : AgreeOutsideScratch x x :=
  fun _ _ => rfl

theorem AgreeOutsideScratch.regs_lt {g s : Data rQF} (h : AgreeOutsideScratch g s)
    (j : Fin rQF) (hj : j.val < 30 := by decide) : s.regs j = g.regs j :=
  h j (Or.inl hj)

theorem AgreeOutsideScratch.regs_ge {g s : Data rQF} (h : AgreeOutsideScratch g s)
    {j : Fin rQF} (hj : 36 ≤ j.val) : s.regs j = g.regs j :=
  h j (Or.inr hj)

theorem AgreeOutsideScratch.set {g s : Data rQF} (h : AgreeOutsideScratch g s)
    (d : Fin rQF) (v : ℕ) : AgreeOutsideScratch (g.set d v) (s.set d v) := by
  intro j hj
  by_cases hjd : j = d
  · subst hjd; simp [Data.set_regs]
  · simp [Data.set_regs, Function.update_of_ne hjd, h j hj]

/-- Bundled execution state invariant coupling concrete machine state `s : Data rQF` with ghost
register state `g : Data rQF` and pure filter state
`st : FilterState (quotBits w₀ n) (remBits w₀ k)`. -/
structure ClusterState (base w w₀ n k : ℕ) (mem₀ : ℕ → ℕ)
    (g : Data rQF) (st : FilterState (quotBits w₀ n) (remBits w₀ k)) (s : Data rQF) : Prop where
  /-- All registers and memory words fit in `w` bits. -/
  bounded : s.Bounded w
  /-- Registers outside `30..35` agree with `g`. -/
  agree : AgreeOutsideScratch g s
  /-- Extracted filter state equals `st`. -/
  filterState : extractFilterState base w w₀ n k s.mem = st
  /-- Memory outside the 4 slot arrays `[fullBase, base + space)` equals `mem₀`. -/
  mem_outside : ∀ a, (a < fullBase base w w₀ n ∨ base + space w w₀ n k ≤ a) → s.mem a = mem₀ a

theorem ClusterState.init (base w w₀ n k : ℕ) {x : Data rQF} (hx : x.Bounded w) :
    ClusterState base w w₀ n k x.mem x (extractFilterState base w w₀ n k x.mem) x :=
  ⟨hx, AgreeOutsideScratch.refl x, rfl, fun _ _ => rfl⟩

theorem ClusterState.set {base w w₀ n k : ℕ} {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s) (d : Fin rQF) {v : ℕ} (hfit : Fits w v) :
    ClusterState base w w₀ n k mem₀ (g.set d v) st (s.set d v) where
  bounded := hs.bounded.set hfit
  agree := hs.agree.set d v
  filterState := hs.filterState
  mem_outside := hs.mem_outside

theorem step_const {base w w₀ n k : ℕ} {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s) (d : Fin rQF) {v : ℕ} (hfit : Fits w v) :
    Exec w (.op (.const d v) : Code .exact rQF) s (s.set d v) 1 ∧
      ClusterState base w w₀ n k mem₀ (g.set d v) st (s.set d v) :=
  ⟨Exec.const hfit, hs.set d hfit⟩

theorem step_copy {base w w₀ n k : ℕ} {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s) (d src : Fin rQF) {v : ℕ}
    (hsrc_eq : g.regs src = v)
    (hsrc : src.val < 30 := by decide) :
    Exec w (.op (.copy d src) : Code .exact rQF) s (s.set d v) 1 ∧
      ClusterState base w w₀ n k mem₀ (g.set d v) st (s.set d v) := by
  have hreg : s.regs src = v := by rw [hs.agree.regs_lt src hsrc, hsrc_eq]
  have hfit : Fits w v := hreg ▸ hs.bounded.1 src
  have hex : Exec w (.op (.copy d src) : Code .exact rQF) s (s.set d v) 1 := by
    rw [← hreg]
    exact Exec.copy
  exact ⟨hex, hs.set d hfit⟩

theorem step_bin {base w w₀ n k : ℕ} {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s) (op : BinOp) (d s1 s2 : Fin rQF) {v : ℕ}
    (hev : op.evalExact (g.regs s1) (g.regs s2) = some v) (hfit : Fits w v)
    (hs1 : s1.val < 30 := by decide) (hs2 : s2.val < 30 := by decide) :
    Exec w (.op (.exactBin op d s1 s2) : Code .exact rQF) s (s.set d v) 1 ∧
      ClusterState base w w₀ n k mem₀ (g.set d v) st (s.set d v) := by
  have h1 : s.regs s1 = g.regs s1 := hs.agree.regs_lt s1 hs1
  have h2 : s.regs s2 = g.regs s2 := hs.agree.regs_lt s2 hs2
  have hex : Exec w (.op (.exactBin op d s1 s2) : Code .exact rQF) s (s.set d v) 1 := by
    apply Exec.op
    rw [Op.eval_exactBin, h1, h2, hev]
    exact Data.put_of_fits hfit
  exact ⟨hex, hs.set d hfit⟩

private theorem set_self_regs (x : Data rQF) (r : Fin rQF) : x.set r (x.regs r) = x := by
  cases x
  simp [Data.set]

private theorem exec_nop (w : ℕ) (x : Data rQF) :
    Exec w (.op (.copy 29 29) : Code .exact rQF) x x 1 := by
  have h := Exec.copy (B := .exact) (w := w) (d := 29) (s := 29) (x := x)
  rwa [set_self_regs] at h

/-- Evaluate comparison `c` into `dst` as `0` or `1` (`(decide (c.Holds x)).toNat`) in `3`
instructions. -/
@[expose] def evalCondCode (c : Cond rQF) (dst : Fin rQF) : Code .exact rQF :=
  .branch c (.seq (.op (.const dst 1)) (.op (.copy 29 29))) (.op (.const dst 0))

theorem evalCondCode_exec {w : ℕ} (hw : 1 ≤ w) (c : Cond rQF) (dst : Fin rQF) (x : Data rQF) :
    Exec w (evalCondCode c dst) x (x.set dst (decide (c.Holds x)).toNat) 3 := by
  have hfit0 : Fits w 0 := Nat.two_pow_pos w
  have hfit1 : Fits w 1 := Nat.one_lt_two_pow (by omega)
  by_cases hc : c.Holds x
  · have e1 : Exec w (.op (.const dst 1) : Code .exact rQF) x (x.set dst 1) 1 :=
      Exec.const hfit1
    have e2 := exec_nop w (x.set dst 1)
    simpa [evalCondCode, hc] using Exec.branch_pos hc (e1.seq e2)
  · have e1 : Exec w (.op (.const dst 0) : Code .exact rQF) x (x.set dst 0) 1 :=
      Exec.const hfit0
    simpa [evalCondCode, hc] using Exec.branch_neg hc e1

/-- Conditionally copy `src` into `dst` when `c` holds, in `3` instructions. -/
@[expose] def condCopyCode (c : Cond rQF) (dst src : Fin rQF) : Code .exact rQF :=
  .branch c (.seq (.op (.copy dst src)) (.op (.copy 29 29))) (.op (.copy 29 29))

theorem condCopyCode_exec (w : ℕ) (c : Cond rQF) (dst src : Fin rQF) (x : Data rQF) :
    Exec w (condCopyCode c dst src) x
      (x.set dst (if c.Holds x then x.regs src else x.regs dst)) 3 := by
  by_cases hc : c.Holds x
  · have e1 : Exec w (.op (.copy dst src) : Code .exact rQF) x (x.set dst (x.regs src)) 1 :=
      Exec.copy
    have e2 := exec_nop w (x.set dst (x.regs src))
    simpa [condCopyCode, hc] using Exec.branch_pos hc (e1.seq e2)
  · have e1 := exec_nop w x
    have hset : x.set dst (if c.Holds x then x.regs src else x.regs dst) = x := by
      simp [hc, set_self_regs]
    rw [hset]
    exact Exec.branch_neg hc e1

theorem step_evalLt {base w w₀ n k : ℕ} (hw : 1 ≤ w) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s) (a b dst : Fin rQF) {va vb : ℕ}
    (ha_eq : g.regs a = va) (hb_eq : g.regs b = vb)
    (ha : a.val < 30 := by decide) (hb : b.val < 30 := by decide) :
    let v := (decide (va < vb)).toNat
    Exec w (evalCondCode (.lt a b) dst) s (s.set dst v) 3 ∧
      ClusterState base w w₀ n k mem₀ (g.set dst v) st (s.set dst v) := by
  intro v
  have hc : (Cond.lt a b).Holds s ↔ va < vb := by
    simp [Cond.Holds, hs.agree.regs_lt a ha, hs.agree.regs_lt b hb, ha_eq, hb_eq]
  have hv : (decide ((Cond.lt a b).Holds s)).toNat = v := by simp [v, hc]
  have hfit : Fits w v := by
    have hlt : v < 2 := Bool.toNat_lt _
    have hpow : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw
    exact hlt.trans_le hpow
  have hex := evalCondCode_exec hw (.lt a b) dst s
  rw [hv] at hex
  exact ⟨hex, hs.set dst hfit⟩

theorem step_evalEq {base w w₀ n k : ℕ} (hw : 1 ≤ w) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s) (a b dst : Fin rQF) {va vb : ℕ}
    (ha_eq : g.regs a = va) (hb_eq : g.regs b = vb)
    (ha : a.val < 30 := by decide) (hb : b.val < 30 := by decide) :
    let v := (decide (va = vb)).toNat
    Exec w (evalCondCode (.eq a b) dst) s (s.set dst v) 3 ∧
      ClusterState base w w₀ n k mem₀ (g.set dst v) st (s.set dst v) := by
  intro v
  have hc : (Cond.eq a b).Holds s ↔ va = vb := by
    simp [Cond.Holds, hs.agree.regs_lt a ha, hs.agree.regs_lt b hb, ha_eq, hb_eq]
  have hv : (decide ((Cond.eq a b).Holds s)).toNat = v := by simp [v, hc]
  have hfit : Fits w v := by
    have hlt : v < 2 := Bool.toNat_lt _
    have hpow : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw
    exact hlt.trans_le hpow
  have hex := evalCondCode_exec hw (.eq a b) dst s
  rw [hv] at hex
  exact ⟨hex, hs.set dst hfit⟩

theorem step_condCopyLt {base w w₀ n k : ℕ} {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s) (a b dst src : Fin rQF)
    {va vb vdst vsrc : ℕ}
    (ha_eq : g.regs a = va) (hb_eq : g.regs b = vb)
    (hdst_eq : g.regs dst = vdst) (hsrc_eq : g.regs src = vsrc)
    (ha : a.val < 30 := by decide) (hb : b.val < 30 := by decide)
    (hdst : dst.val < 30 := by decide) (hsrc : src.val < 30 := by decide) :
    let v := if va < vb then vsrc else vdst
    Exec w (condCopyCode (.lt a b) dst src) s (s.set dst v) 3 ∧
      ClusterState base w w₀ n k mem₀ (g.set dst v) st (s.set dst v) := by
  intro v
  have hc : (Cond.lt a b).Holds s ↔ va < vb := by
    simp [Cond.Holds, hs.agree.regs_lt a ha, hs.agree.regs_lt b hb, ha_eq, hb_eq]
  have hv : (if (Cond.lt a b).Holds s then s.regs src else s.regs dst) = v := by
    simp [v, hc, hs.agree.regs_lt src hsrc, hs.agree.regs_lt dst hdst, hsrc_eq, hdst_eq]
  have hfit : Fits w v := by
    dsimp only [v]
    split_ifs
    · have h1 : s.regs src = vsrc := by rw [hs.agree.regs_lt src hsrc, hsrc_eq]
      exact h1 ▸ hs.bounded.1 src
    · have h1 : s.regs dst = vdst := by rw [hs.agree.regs_lt dst hdst, hdst_eq]
      exact h1 ▸ hs.bounded.1 dst
  have hex := condCopyCode_exec w (.lt a b) dst src s
  rw [hv] at hex
  exact ⟨hex, hs.set dst hfit⟩

theorem step_probeSlot {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (baseSlotReg offReg dstReg : Fin rQF)
    (o : Fin (2 ^ quotBits w₀ n)) {d : ℕ} (hd : d ≤ 2 ^ quotBits w₀ n)
    (ho : g.regs baseSlotReg = o.val) (hoff : g.regs offReg = d)
    (hb_lt30 : baseSlotReg.val < 30 := by decide)
    (hoff_lt30 : offReg.val < 30 := by decide)
    (hdst_lt30 : dstReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (probeSlotCode (quotBits w₀ n) baseSlotReg offReg dstReg) s y 3 ∧
      ClusterState base w w₀ n k mem₀
        (g.set dstReg (probeSlot (quotBits w₀ n) o d).val) st y := by
  have hb_ne : baseSlotReg ≠ 30 := Fin.ne_of_val_ne (by change baseSlotReg.val ≠ 30; omega)
  have hoff_ne : offReg ≠ 30 := Fin.ne_of_val_ne (by change offReg.val ≠ 30; omega)
  have hdst_ne : dstReg ≠ 30 := Fin.ne_of_val_ne (by change dstReg.val ≠ 30; omega)
  have ho_s : s.regs baseSlotReg = o.val := by rw [hs.agree.regs_lt baseSlotReg hb_lt30, ho]
  have hoff_s : s.regs offReg = d := by rw [hs.agree.regs_lt offReg hoff_lt30, hoff]
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    probeSlotCode_exec hb_lt hb_ne hoff_ne hdst_ne o hd ho_s hoff_s
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjd : j = dstReg
    · subst hjd; simp [hy_dst]
    · have hj30 : j ≠ 30 := Fin.ne_of_val_ne (by change j.val ≠ 30; omega)
      rw [hy_regs j hjd hj30, Data.set_regs, Function.update_of_ne hjd, hs.agree j hj]
  · rw [hy_mem]; exact hs.filterState
  · intro a ha; rw [hy_mem]; exact hs.mem_outside a ha

theorem step_backSlot {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (slotReg offReg dstReg : Fin rQF)
    (q : Fin (2 ^ quotBits w₀ n)) {a : ℕ} (ha : a ≤ 2 ^ quotBits w₀ n)
    (hq : g.regs slotReg = q.val) (hoff : g.regs offReg = a)
    (hs_lt30 : slotReg.val < 30 := by decide)
    (hoff_lt30 : offReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (backSlotCode (quotBits w₀ n) slotReg offReg dstReg) s y 5 ∧
      ClusterState base w w₀ n k mem₀
        (g.set dstReg (backSlot (quotBits w₀ n) q a).val) st y := by
  have hs_ne : slotReg ≠ 30 := Fin.ne_of_val_ne (by change slotReg.val ≠ 30; omega)
  have hoff_ne : offReg ≠ 30 := Fin.ne_of_val_ne (by change offReg.val ≠ 30; omega)
  have hq_s : s.regs slotReg = q.val := by rw [hs.agree.regs_lt slotReg hs_lt30, hq]
  have hoff_s : s.regs offReg = a := by rw [hs.agree.regs_lt offReg hoff_lt30, hoff]
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    backSlotCode_exec hb_lt hs_ne hoff_ne q ha hq_s hoff_s
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjd : j = dstReg
    · subst hjd; simp [hy_dst]
    · have hj30 : j ≠ 30 := Fin.ne_of_val_ne (by change j.val ≠ 30; omega)
      have hj31 : j ≠ 31 := Fin.ne_of_val_ne (by change j.val ≠ 31; omega)
      rw [hy_regs j hjd hj30 hj31, Data.set_regs, Function.update_of_ne hjd, hs.agree j hj]
  · rw [hy_mem]; exact hs.filterState
  · intro a' ha'; rw [hy_mem]; exact hs.mem_outside a' ha'

theorem step_readFull {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k)) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (idxReg dstReg : Fin rQF) (q : Fin (2 ^ quotBits w₀ n))
    (h0 : g.regs 0 = base) (hidx : g.regs idxReg = q.val)
    (hidx_lt : idxReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (readFullCode w w₀ n idxReg dstReg) s y 13 ∧
      ClusterState base w w₀ n k mem₀ (g.set dstReg (st.isFull q).toNat) st y := by
  have h0_s : s.regs 0 = base := by rw [hs.agree.regs_lt 0, h0]
  have hidx_s : s.regs idxReg = q.val := by rw [hs.agree.regs_lt idxReg hidx_lt, hidx]
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    readFullCode_exec (k := k) (dstReg := dstReg) hb_lt hw hfit_space hidx_lt q hs.bounded
      h0_s hidx_s
  rw [hs.filterState] at hy_dst
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjd : j = dstReg
    · subst hjd; simp [hy_dst]
    · rw [hy_regs j hjd (by omega), Data.set_regs, Function.update_of_ne hjd, hs.agree j hj]
  · rw [hy_mem]; exact hs.filterState
  · intro a ha; rw [hy_mem]; exact hs.mem_outside a ha

theorem step_readOcc {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k)) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (idxReg dstReg : Fin rQF) (q : Fin (2 ^ quotBits w₀ n))
    (h0 : g.regs 0 = base) (hidx : g.regs idxReg = q.val)
    (hidx_lt : idxReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (readOccCode w w₀ n idxReg dstReg) s y 13 ∧
      ClusterState base w w₀ n k mem₀ (g.set dstReg (st.isOcc q).toNat) st y := by
  have h0_s : s.regs 0 = base := by rw [hs.agree.regs_lt 0, h0]
  have hidx_s : s.regs idxReg = q.val := by rw [hs.agree.regs_lt idxReg hidx_lt, hidx]
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    readOccCode_exec (k := k) (dstReg := dstReg) hb_lt hw hfit_space hidx_lt q hs.bounded
      h0_s hidx_s
  rw [hs.filterState] at hy_dst
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjd : j = dstReg
    · subst hjd; simp [hy_dst]
    · rw [hy_regs j hjd (by omega), Data.set_regs, Function.update_of_ne hjd, hs.agree j hj]
  · rw [hy_mem]; exact hs.filterState
  · intro a ha; rw [hy_mem]; exact hs.mem_outside a ha

theorem step_readRunStart {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k)) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (idxReg dstReg : Fin rQF) (q : Fin (2 ^ quotBits w₀ n))
    (h0 : g.regs 0 = base) (hidx : g.regs idxReg = q.val)
    (hidx_lt : idxReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (readRunStartCode w w₀ n idxReg dstReg) s y 13 ∧
      ClusterState base w w₀ n k mem₀ (g.set dstReg (st.isRunStart q).toNat) st y := by
  have h0_s : s.regs 0 = base := by rw [hs.agree.regs_lt 0, h0]
  have hidx_s : s.regs idxReg = q.val := by rw [hs.agree.regs_lt idxReg hidx_lt, hidx]
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    readRunStartCode_exec (k := k) (dstReg := dstReg) hb_lt hw hfit_space hidx_lt q hs.bounded
      h0_s hidx_s
  rw [hs.filterState] at hy_dst
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjd : j = dstReg
    · subst hjd; simp [hy_dst]
    · rw [hy_regs j hjd (by omega), Data.set_regs, Function.update_of_ne hjd, hs.agree j hj]
  · rw [hy_mem]; exact hs.filterState
  · intro a ha; rw [hy_mem]; exact hs.mem_outside a ha

theorem step_readRem {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w)
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k)) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (idxReg dstReg : Fin rQF) (q : Fin (2 ^ quotBits w₀ n))
    (h0 : g.regs 0 = base) (hidx : g.regs idxReg = q.val)
    (hidx_lt : idxReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (readRemCode w w₀ n k idxReg dstReg) s y 13 ∧
      ClusterState base w w₀ n k mem₀ (g.set dstReg (st.remAt q).val) st y := by
  have h0_s : s.regs 0 = base := by rw [hs.agree.regs_lt 0, h0]
  have hidx_s : s.regs idxReg = q.val := by rw [hs.agree.regs_lt idxReg hidx_lt, hidx]
  obtain ⟨y, hy_exec, hy_mem, hy_dst, hy_regs⟩ :=
    readRemCode_exec (dstReg := dstReg) hb_lt hw₀_pos hw hfit_space hidx_lt q hs.bounded
      h0_s hidx_s
  rw [hs.filterState] at hy_dst
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjd : j = dstReg
    · subst hjd; simp [hy_dst]
    · rw [hy_regs j hjd (by omega), Data.set_regs, Function.update_of_ne hjd, hs.agree j hj]
  · rw [hy_mem]; exact hs.filterState
  · intro a ha; rw [hy_mem]; exact hs.mem_outside a ha

theorem step_writeFull {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k)) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (idxReg valReg : Fin rQF) (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool)
    (h0 : g.regs 0 = base) (hidx : g.regs idxReg = q.val) (hval : g.regs valReg = bval.toNat)
    (hidx_lt : idxReg.val < 30 := by decide) (hval_lt : valReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (writeFullCode w w₀ n idxReg valReg) s y 17 ∧
      ClusterState base w w₀ n k mem₀ g (st.setFull q bval) y := by
  have h0_s : s.regs 0 = base := by rw [hs.agree.regs_lt 0, h0]
  have hidx_s : s.regs idxReg = q.val := by rw [hs.agree.regs_lt idxReg hidx_lt, hidx]
  have hval_s : s.regs valReg = bval.toNat := by rw [hs.agree.regs_lt valReg hval_lt, hval]
  obtain ⟨y, hy_exec, hy_st, hy_out, hy_regs⟩ :=
    writeFullCode_exec (k := k) hb_lt hw hfit_space hidx_lt hval_lt q bval hs.bounded
      h0_s hidx_s hval_s
  rw [hs.filterState] at hy_st
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, hy_st, ?_⟩
  · intro j hj; rw [hy_regs j hj, hs.agree j hj]
  · intro a ha; rw [hy_out a ha, hs.mem_outside a ha]

theorem step_writeOcc {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k)) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (idxReg valReg : Fin rQF) (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool)
    (h0 : g.regs 0 = base) (hidx : g.regs idxReg = q.val) (hval : g.regs valReg = bval.toNat)
    (hidx_lt : idxReg.val < 30 := by decide) (hval_lt : valReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (writeOccCode w w₀ n idxReg valReg) s y 17 ∧
      ClusterState base w w₀ n k mem₀ g (st.setOcc q bval) y := by
  have h0_s : s.regs 0 = base := by rw [hs.agree.regs_lt 0, h0]
  have hidx_s : s.regs idxReg = q.val := by rw [hs.agree.regs_lt idxReg hidx_lt, hidx]
  have hval_s : s.regs valReg = bval.toNat := by rw [hs.agree.regs_lt valReg hval_lt, hval]
  obtain ⟨y, hy_exec, hy_st, hy_out, hy_regs⟩ :=
    writeOccCode_exec (k := k) hb_lt hw hfit_space hidx_lt hval_lt q bval hs.bounded
      h0_s hidx_s hval_s
  rw [hs.filterState] at hy_st
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, hy_st, ?_⟩
  · intro j hj; rw [hy_regs j hj, hs.agree j hj]
  · intro a ha; rw [hy_out a ha, hs.mem_outside a ha]

theorem step_writeRunStart {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k)) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (idxReg valReg : Fin rQF) (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool)
    (h0 : g.regs 0 = base) (hidx : g.regs idxReg = q.val) (hval : g.regs valReg = bval.toNat)
    (hidx_lt : idxReg.val < 30 := by decide) (hval_lt : valReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (writeRunStartCode w w₀ n idxReg valReg) s y 17 ∧
      ClusterState base w w₀ n k mem₀ g (st.setRunStart q bval) y := by
  have h0_s : s.regs 0 = base := by rw [hs.agree.regs_lt 0, h0]
  have hidx_s : s.regs idxReg = q.val := by rw [hs.agree.regs_lt idxReg hidx_lt, hidx]
  have hval_s : s.regs valReg = bval.toNat := by rw [hs.agree.regs_lt valReg hval_lt, hval]
  obtain ⟨y, hy_exec, hy_st, hy_out, hy_regs⟩ :=
    writeRunStartCode_exec (k := k) hb_lt hw hfit_space hidx_lt hval_lt q bval hs.bounded
      h0_s hidx_s hval_s
  rw [hs.filterState] at hy_st
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, hy_st, ?_⟩
  · intro j hj; rw [hy_regs j hj, hs.agree j hj]
  · intro a ha; rw [hy_out a ha, hs.mem_outside a ha]

theorem step_writeRem {base w w₀ n k : ℕ} (hb_lt : quotBits w₀ n < w)
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k)) {mem₀ : ℕ → ℕ}
    {g : Data rQF} {st : FilterState (quotBits w₀ n) (remBits w₀ k)} {s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (idxReg valReg : Fin rQF) (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k))
    (h0 : g.regs 0 = base) (hidx : g.regs idxReg = q.val) (hval : g.regs valReg = r.val)
    (hidx_lt : idxReg.val < 30 := by decide) (hval_lt : valReg.val < 30 := by decide) :
    ∃ y : Data rQF,
      Exec w (writeRemCode w w₀ n k idxReg valReg) s y 17 ∧
      ClusterState base w w₀ n k mem₀ g (st.setRem q r) y := by
  have h0_s : s.regs 0 = base := by rw [hs.agree.regs_lt 0, h0]
  have hidx_s : s.regs idxReg = q.val := by rw [hs.agree.regs_lt idxReg hidx_lt, hidx]
  have hval_s : s.regs valReg = r.val := by rw [hs.agree.regs_lt valReg hval_lt, hval]
  obtain ⟨y, hy_exec, hy_st, hy_out, hy_regs⟩ :=
    writeRemCode_exec hb_lt hw₀_pos hw hfit_space hidx_lt hval_lt q r hs.bounded
      h0_s hidx_s hval_s
  rw [hs.filterState] at hy_st
  refine ⟨y, hy_exec, hy_exec.bounded hs.bounded, ?_, hy_st, ?_⟩
  · intro j hj; rw [hy_regs j hj, hs.agree j hj]
  · intro a ha; rw [hy_out a ha, hs.mem_outside a ha]

/-! ## Section 2: `findClusterCode` (backward and forward full-slot walk) -/

/-- Loop walking backwards from `q` (`reg 2`) while `st.isFull (backSlot b q (d + 1)) = true`
(`0 < reg 9`). -/
@[expose] def backLenLoop (w w₀ n : ℕ) : Code .exact rQF :=
  .loop (.lt 29 9)
    (.seq (.op (.exactBin .add 4 4 28))
    (.seq (.op (.exactBin .add 7 7 28))
    (.seq (backSlotCode (quotBits w₀ n) 2 7 8)
          (readFullCode w w₀ n 8 9))))

theorem backLenLoop_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (q : Fin (2 ^ quotBits w₀ n)) {a : ℕ} (ha_lt : a < 2 ^ quotBits w₀ n)
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    (hfull : ∀ d < a, st.isFull (backSlot (quotBits w₀ n) q (d + 1)) = true)
    (hempty : st.isFull (backSlot (quotBits w₀ n) q (a + 1)) = false)
    {mem₀ : ℕ → ℕ} :
    ∀ (rem d : ℕ) (g s : Data rQF),
      d + rem = a →
      ClusterState base w w₀ n k mem₀ g st s →
      g.regs 0 = base →
      g.regs 2 = q.val →
      g.regs 4 = d →
      g.regs 7 = d + 1 →
      g.regs 9 = (st.isFull (backSlot (quotBits w₀ n) q (d + 1))).toNat →
      g.regs 28 = 1 →
      g.regs 29 = 0 →
      ∃ g' y : Data rQF,
        Exec w (backLenLoop w w₀ n) s y (22 * rem + 2) ∧
        ClusterState base w w₀ n k mem₀ g' st y ∧
        g'.regs 0 = base ∧
        g'.regs 1 = g.regs 1 ∧
        g'.regs 2 = q.val ∧
        g'.regs 3 = g.regs 3 ∧
        g'.regs 4 = a ∧
        g'.regs 28 = 1 ∧
        g'.regs 29 = 0 ∧
        ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  intro rem
  have hpow_b : 2 ^ quotBits w₀ n < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  induction rem with
  | zero =>
    intro d g s hsum hs h0 h2 h4 _ h9 h28 h29
    have hd_eq : d = a := by omega
    subst hd_eq
    have hc : ¬(Cond.lt 29 9).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 29, hs.agree.regs_lt 9, h29, h9, hempty]
    exact ⟨g, s, Exec.loop_exit hc, hs, h0, rfl, h2, rfl, h4, h28, h29, fun _ _ => rfl⟩
  | succ rem ih =>
    intro d g s hsum hs h0 h2 h4 h7 h9 h28 h29
    have hd_lt : d < a := by omega
    have hfull_d : st.isFull (backSlot (quotBits w₀ n) q (d + 1)) = true := hfull d hd_lt
    have hc : (Cond.lt 29 9).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 29, hs.agree.regs_lt 9, h29, h9, hfull_d]
    have hfit_d1 : Fits w (d + 1) := by change d + 1 < 2 ^ w; omega
    have hfit_d2 : Fits w (d + 2) := by change d + 2 < 2 ^ w; omega
    obtain ⟨e1, hs1⟩ := step_bin hs .add 4 4 28 (v := d + 1)
      (by simp +decide [h4, h28]) hfit_d1
    obtain ⟨e2, hs2⟩ := step_bin hs1 .add 7 7 28 (v := d + 2)
      (by simp +decide [h7, h28]) hfit_d2
    obtain ⟨s3, e3, hs3⟩ := step_backSlot hb_lt hs2 2 7 8 q (a := d + 2) (by omega)
      (by simp +decide [h2]) (by simp +decide)
    obtain ⟨s4, e4, hs4⟩ := step_readFull hb_lt hw hfit_space hs3 8 9
      (backSlot (quotBits w₀ n) q (d + 2))
      (by simp +decide [h0]) (by simp +decide)
    obtain ⟨g', y, hy_exec, hy_st, h0', h1', h2', h3', h4', h28', h29', h240'⟩ :=
      ih (d + 1) _ s4 (by omega) hs4
        (by simp +decide [h0])
        (by simp +decide [h2])
        (by simp +decide)
        (by simp +decide)
        (by simp +decide)
        (by simp +decide [h28])
        (by simp +decide [h29])
    have hiter := Exec.loop_iter hc (e1.seq (e2.seq (e3.seq e4))) hy_exec
    refine ⟨g', y, ?_, hy_st, h0', ?_, h2', ?_, h4', h28', h29', ?_⟩
    · simpa only [backLenLoop,
        show (1 + (1 + (5 + 13))) + (22 * rem + 2) + 2 = 22 * (rem + 1) + 2 by omega] using hiter
    · rw [h1']; simp +decide
    · rw [h3']; simp +decide
    · intro j hj
      rw [h240' j hj]
      have hj4 : j ≠ 4 := Fin.ne_of_val_ne (by change j.val ≠ 4; omega)
      have hj7 : j ≠ 7 := Fin.ne_of_val_ne (by change j.val ≠ 7; omega)
      have hj8 : j ≠ 8 := Fin.ne_of_val_ne (by change j.val ≠ 8; omega)
      have hj9 : j ≠ 9 := Fin.ne_of_val_ne (by change j.val ≠ 9; omega)
      simp [hj4, hj7, hj8, hj9]

/-- Loop walking forwards from `q` (`reg 2`) while `st.isFull (probeSlot b q d) = true`
(`0 < reg 9`). -/
@[expose] def fwdLenLoop (w w₀ n : ℕ) : Code .exact rQF :=
  .loop (.lt 29 9)
    (.seq (.op (.exactBin .add 7 7 28))
    (.seq (probeSlotCode (quotBits w₀ n) 2 7 8)
          (readFullCode w w₀ n 8 9)))

theorem fwdLenLoop_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (q : Fin (2 ^ quotBits w₀ n)) {t : ℕ} (ht_lt : t < 2 ^ quotBits w₀ n)
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    (hfull : ∀ d < t, st.isFull (probeSlot (quotBits w₀ n) q d) = true)
    (hempty : st.isFull (probeSlot (quotBits w₀ n) q t) = false)
    {mem₀ : ℕ → ℕ} :
    ∀ (rem d : ℕ) (g s : Data rQF),
      d + rem = t →
      ClusterState base w w₀ n k mem₀ g st s →
      g.regs 0 = base →
      g.regs 2 = q.val →
      g.regs 7 = d →
      g.regs 9 = (st.isFull (probeSlot (quotBits w₀ n) q d)).toNat →
      g.regs 28 = 1 →
      g.regs 29 = 0 →
      ∃ g' y : Data rQF,
        Exec w (fwdLenLoop w w₀ n) s y (19 * rem + 2) ∧
        ClusterState base w w₀ n k mem₀ g' st y ∧
        g'.regs 0 = base ∧
        g'.regs 1 = g.regs 1 ∧
        g'.regs 2 = q.val ∧
        g'.regs 3 = g.regs 3 ∧
        g'.regs 4 = g.regs 4 ∧
        g'.regs 5 = g.regs 5 ∧
        g'.regs 7 = t ∧
        g'.regs 28 = 1 ∧
        g'.regs 29 = 0 ∧
        ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  intro rem
  have hpow_b : 2 ^ quotBits w₀ n < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  induction rem with
  | zero =>
    intro d g s hsum hs h0 h2 h7 h9 h28 h29
    have hd_eq : d = t := by omega
    subst hd_eq
    have hc : ¬(Cond.lt 29 9).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 29, hs.agree.regs_lt 9, h29, h9, hempty]
    exact ⟨g, s, Exec.loop_exit hc, hs, h0, rfl, h2, rfl, rfl, rfl, h7, h28, h29, fun _ _ => rfl⟩
  | succ rem ih =>
    intro d g s hsum hs h0 h2 h7 h9 h28 h29
    have hd_lt : d < t := by omega
    have hfull_d : st.isFull (probeSlot (quotBits w₀ n) q d) = true := hfull d hd_lt
    have hc : (Cond.lt 29 9).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 29, hs.agree.regs_lt 9, h29, h9, hfull_d]
    have hfit_d1 : Fits w (d + 1) := by change d + 1 < 2 ^ w; omega
    obtain ⟨e1, hs1⟩ := step_bin hs .add 7 7 28 (v := d + 1)
      (by simp +decide [h7, h28]) hfit_d1
    obtain ⟨s2, e2, hs2⟩ := step_probeSlot hb_lt hs1 2 7 8 q (d := d + 1) (by omega)
      (by simp +decide [h2]) (by simp +decide)
    obtain ⟨s3, e3, hs3⟩ := step_readFull hb_lt hw hfit_space hs2 8 9
      (probeSlot (quotBits w₀ n) q (d + 1))
      (by simp +decide [h0]) (by simp +decide)
    obtain ⟨g', y, hy_exec, hy_st, h0', h1', h2', h3', h4', h5', h7', h28', h29', h240'⟩ :=
      ih (d + 1) _ s3 (by omega) hs3
        (by simp +decide [h0])
        (by simp +decide [h2])
        (by simp +decide)
        (by simp +decide)
        (by simp +decide [h28])
        (by simp +decide [h29])
    have hiter := Exec.loop_iter hc (e1.seq (e2.seq e3)) hy_exec
    refine ⟨g', y, ?_, hy_st, h0', ?_, h2', ?_, ?_, ?_, h7', h28', h29', ?_⟩
    · simpa only [fwdLenLoop,
        show (1 + (3 + 13)) + (19 * rem + 2) + 2 = 19 * (rem + 1) + 2 by omega] using hiter
    · rw [h1']; simp +decide
    · rw [h3']; simp +decide
    · rw [h4']; simp +decide
    · rw [h5']; simp +decide
    · intro j hj
      rw [h240' j hj]
      have hj7 : j ≠ 7 := Fin.ne_of_val_ne (by change j.val ≠ 7; omega)
      have hj8 : j ≠ 8 := Fin.ne_of_val_ne (by change j.val ≠ 8; omega)
      have hj9 : j ≠ 9 := Fin.ne_of_val_ne (by change j.val ≠ 9; omega)
      simp [hj7, hj8, hj9]

/-- Word-RAM program computing `a = backLen q` (`reg 4`), `o = clusterStart q` (`reg 5`), and
`ℓ = clusterLen q` (`reg 6`) from `q` (`reg 2`) and `base` (`reg 0`). -/
@[expose] def findClusterCode (w w₀ n : ℕ) : Code .exact rQF :=
  .seq (.op (.const 28 1))
  (.seq (.op (.const 29 0))
  (.seq (.op (.const 4 0))
  (.seq (.op (.const 7 1))
  (.seq (backSlotCode (quotBits w₀ n) 2 7 8)
  (.seq (readFullCode w w₀ n 8 9)
  (.seq (backLenLoop w w₀ n)
  (.seq (backSlotCode (quotBits w₀ n) 2 4 5)
  (.seq (.op (.const 7 0))
  (.seq (readFullCode w w₀ n 2 9)
  (.seq (fwdLenLoop w w₀ n)
        (.op (.exactBin .add 6 4 7))))))))))))

/-- Exact instruction count of `findClusterCode` for backward length `a` and forward length `t`. -/
@[expose] def findClusterSteps (a t : ℕ) : ℕ :=
  22 * a + 19 * t + 46

theorem findClusterCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (q : Fin (2 ^ quotBits w₀ n)) {a t : ℕ} (hat_lt : a + t < 2 ^ quotBits w₀ n)
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    (hback_full : ∀ d < a, st.isFull (backSlot (quotBits w₀ n) q (d + 1)) = true)
    (hback_empty : st.isFull (backSlot (quotBits w₀ n) q (a + 1)) = false)
    (hfwd_full : ∀ d < t, st.isFull (probeSlot (quotBits w₀ n) q d) = true)
    (hfwd_empty : st.isFull (probeSlot (quotBits w₀ n) q t) = false)
    {mem₀ : ℕ → ℕ} {g s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (h0 : g.regs 0 = base) (h2 : g.regs 2 = q.val) :
    ∃ g' y : Data rQF,
      Exec w (findClusterCode w w₀ n) s y (findClusterSteps a t) ∧
      ClusterState base w w₀ n k mem₀ g' st y ∧
      g'.regs 0 = base ∧
      g'.regs 1 = g.regs 1 ∧
      g'.regs 2 = q.val ∧
      g'.regs 3 = g.regs 3 ∧
      g'.regs 4 = a ∧
      g'.regs 5 = (backSlot (quotBits w₀ n) q a).val ∧
      g'.regs 6 = a + t ∧
      g'.regs 28 = 1 ∧
      g'.regs 29 = 0 ∧
      ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  have hpow_b : 2 ^ quotBits w₀ n < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  have hfit0 : Fits w 0 := Nat.two_pow_pos w
  have hfit1 : Fits w 1 := Nat.one_lt_two_pow (by omega)
  have hfit_at : Fits w (a + t) := by change a + t < 2 ^ w; omega
  obtain ⟨e1, hs1⟩ := step_const hs 28 hfit1
  obtain ⟨e2, hs2⟩ := step_const hs1 29 hfit0
  obtain ⟨e3, hs3⟩ := step_const hs2 4 hfit0
  obtain ⟨e4, hs4⟩ := step_const hs3 7 hfit1
  obtain ⟨s5, e5, hs5⟩ := step_backSlot hb_lt hs4 2 7 8 q (a := 1) Nat.one_le_two_pow
    (by simp +decide [h2]) (by simp +decide)
  obtain ⟨s6, e6, hs6⟩ := step_readFull hb_lt hw hfit_space hs5 8 9
    (backSlot (quotBits w₀ n) q 1)
    (by simp +decide [h0]) (by simp +decide)
  obtain ⟨g7, s7, e7, hs7, h7_0, h7_1, h7_2, h7_3, h7_4, h7_28, h7_29, h7_240⟩ :=
    backLenLoop_exec (a := a) hb_lt hw hfit_space q (by omega) hback_full hback_empty
      a 0 _ s6 (by omega) hs6
      (by simp +decide [h0])
      (by simp +decide [h2])
      (by simp +decide)
      (by simp +decide)
      (by simp +decide)
      (by simp +decide)
      (by simp +decide)
  obtain ⟨s8, e8, hs8⟩ := step_backSlot hb_lt hs7 2 4 5 q (a := a) (by omega)
    h7_2 h7_4
  obtain ⟨e9, hs9⟩ := step_const hs8 7 hfit0
  obtain ⟨s10, e10, hs10⟩ := step_readFull hb_lt hw hfit_space hs9 2 9 q
    (by simp +decide [h7_0]) (by simp +decide [h7_2])
  have h9_10 :
      (g7.set 5 (backSlot (quotBits w₀ n) q a).val |>.set 7 0 |>.set 9 (st.isFull q).toNat).regs 9 =
        (st.isFull (probeSlot (quotBits w₀ n) q 0)).toNat := by
    rw [probeSlot_zero]
    simp +decide
  obtain ⟨g11, s11, e11, hs11, h11_0, h11_1, h11_2, h11_3, h11_4, h11_5, h11_7, h11_28, h11_29,
      h11_240⟩ :=
    fwdLenLoop_exec (t := t) hb_lt hw hfit_space q (by omega) hfwd_full hfwd_empty
      t 0 _ s10 (by omega) hs10
      (by simp +decide [h7_0])
      (by simp +decide [h7_2])
      (by simp +decide)
      h9_10
      (by simp +decide [h7_28])
      (by simp +decide [h7_29])
  have h11_4_eq : g11.regs 4 = a := by
    rw [h11_4]; simp +decide [h7_4]
  obtain ⟨e12, hs12⟩ := step_bin hs11 .add 6 4 7 (v := a + t)
    (by simp [h11_4_eq, h11_7]) hfit_at
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq
    (e7.seq (e8.seq (e9.seq (e10.seq (e11.seq e12))))))))))
  refine ⟨g11.set 6 (a + t), s11.set 6 (a + t), ?_, hs12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [findClusterCode, findClusterSteps,
      show 1 + (1 + (1 + (1 + (5 + (13 + ((22 * a + 2) + (5 + (1 + (13 +
        ((19 * t + 2) + 1)))))))))) = 22 * a + 19 * t + 46 by omega] using hall
  · simp +decide [h11_0]
  · simp +decide [h11_1, h7_1]
  · simp +decide [h11_2]
  · simp +decide [h11_3, h7_3]
  · simp +decide [h11_4_eq]
  · simp +decide [h11_5]
  · simp +decide
  · simp +decide [h11_28]
  · simp +decide [h11_29]
  · intro j hj
    have hj6 : j ≠ 6 := Fin.ne_of_val_ne (by change j.val ≠ 6; omega)
    have hj5 : j ≠ 5 := Fin.ne_of_val_ne (by change j.val ≠ 5; omega)
    have hj7 : j ≠ 7 := Fin.ne_of_val_ne (by change j.val ≠ 7; omega)
    have hj8 : j ≠ 8 := Fin.ne_of_val_ne (by change j.val ≠ 8; omega)
    have hj9 : j ≠ 9 := Fin.ne_of_val_ne (by change j.val ≠ 9; omega)
    have hj4 : j ≠ 4 := Fin.ne_of_val_ne (by change j.val ≠ 4; omega)
    have hj28 : j ≠ 28 := Fin.ne_of_val_ne (by change j.val ≠ 28; omega)
    have hj29 : j ≠ 29 := Fin.ne_of_val_ne (by change j.val ≠ 29; omega)
    simp only [Data.set_regs, Function.update_of_ne hj6]
    rw [h11_240 j hj]
    simp only [Data.set_regs, Function.update_of_ne hj9, Function.update_of_ne hj7,
      Function.update_of_ne hj5]
    rw [h7_240 j hj]
    simp [hj9, hj8, hj7, hj4, hj29, hj28]

/-! ## Section 3: `scanClusterCode` (single-pass prefix scan over `[o .. o + ℓ)`) -/

/-- Prefix version of `calcDeleteStop`: first `m < i` with
`a < m ∧ occBefore st o m < runsBefore st o (m + 1)`, or `ℓ` if none exists in `[0, i)`. -/
@[expose] def calcDeleteStopPrefix {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    (a ℓ i : ℕ) : ℕ :=
  (((List.range i).filter fun m =>
    decide (a < m ∧ occBefore st o m < runsBefore st o (m + 1))).head?).getD ℓ

/-- Prefix version of the `any` scan in `queryCluster`. -/
@[expose] def queryAnyPrefix {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    (a i : ℕ) (r : Fin (2 ^ f)) : Bool :=
  (List.range i).any fun m =>
    decide (occBefore st o a < runsBefore st o (m + 1) ∧
      runsBefore st o (m + 1) ≤ occBefore st o (a + 1)) &&
    decide (st.remAt (probeSlot b o m) = r)

theorem calcRunStart_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a : ℕ) :
    calcRunStart st o a 0 = 0 := rfl

theorem calcRunStart_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a m : ℕ) :
    calcRunStart st o a (m + 1) =
      calcRunStart st o a m + (decide (runsBefore st o (m + 1) ≤ occBefore st o a)).toNat := by
  simp only [calcRunStart, List.range_succ, List.filter_append, List.length_append,
    List.filter_cons, List.filter_nil]
  cases decide (runsBefore st o (m + 1) ≤ occBefore st o a) <;> rfl

theorem calcTargetSlot_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a : ℕ)
    (r : Fin (2 ^ f)) :
    calcTargetSlot st o a 0 r = 0 := rfl

theorem calcTargetSlot_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a m : ℕ)
    (r : Fin (2 ^ f)) :
    calcTargetSlot st o a (m + 1) r =
      calcTargetSlot st o a m r +
        (decide (runsBefore st o (m + 1) ≤ occBefore st o a) ||
          (decide (runsBefore st o (m + 1) ≤ occBefore st o (a + 1)) &&
            decide (st.remAt (probeSlot b o m) < r))).toNat := by
  simp only [calcTargetSlot, List.range_succ, List.filter_append, List.length_append,
    List.filter_cons, List.filter_nil, Bool.decide_or, Bool.decide_and]
  cases (decide (runsBefore st o (m + 1) ≤ occBefore st o a) ||
    (decide (runsBefore st o (m + 1) ≤ occBefore st o (a + 1)) &&
      decide (st.remAt (probeSlot b o m) < r))) <;> rfl

theorem calcDeleteStopPrefix_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ) :
    calcDeleteStopPrefix st o a ℓ 0 = ℓ := rfl

theorem calcDeleteStopPrefix_eq_calcDeleteStop {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    (a ℓ : ℕ) :
    calcDeleteStopPrefix st o a ℓ ℓ = calcDeleteStop st o a ℓ := rfl

theorem calcDeleteStopPrefix_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    (a ℓ : ℕ) {m : ℕ} (hm : m < ℓ) :
    let e := calcDeleteStopPrefix st o a ℓ m
    let cond :=
      decide (e = ℓ) && decide (a < m) && decide (occBefore st o m < runsBefore st o (m + 1))
    calcDeleteStopPrefix st o a ℓ (m + 1) = if cond then m else e := by
  intro e cond
  let P : ℕ → Bool := fun k => decide (a < k ∧ occBefore st o k < runsBefore st o (k + 1))
  have hcond_P :
      (decide (a < m) && decide (occBefore st o m < runsBefore st o (m + 1))) = P m := by
    simp [P, Bool.decide_and]
  change ((List.range (m + 1)).filter P).head?.getD ℓ =
    if (decide (((List.range m).filter P).head?.getD ℓ = ℓ) &&
      decide (a < m) && decide (occBefore st o m < runsBefore st o (m + 1))) = true then m
    else ((List.range m).filter P).head?.getD ℓ
  rw [Bool.and_assoc, hcond_P, List.range_succ, List.filter_append]
  cases hL : List.filter P (List.range m) with
  | nil =>
    simp only [List.nil_append, List.head?_nil, Option.getD_none, decide_true, Bool.true_and,
      List.filter_cons, List.filter_nil]
    cases P m <;> rfl
  | cons x xs =>
    have hx_mem : x ∈ List.filter P (List.range m) := by simp [hL]
    have hx_lt : x < m := List.mem_range.mp (List.mem_of_mem_filter hx_mem)
    have hne : ¬(x = ℓ) := by omega
    simp [hne]

theorem queryAnyPrefix_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a : ℕ)
    (r : Fin (2 ^ f)) :
    queryAnyPrefix st o a 0 r = false := rfl

theorem queryAnyPrefix_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a m : ℕ)
    (r : Fin (2 ^ f)) :
    queryAnyPrefix st o a (m + 1) r =
      (queryAnyPrefix st o a m r ||
        (decide (occBefore st o a < runsBefore st o (m + 1)) &&
          decide (runsBefore st o (m + 1) ≤ occBefore st o (a + 1)) &&
          decide (st.remAt (probeSlot b o m) = r))) := by
  simp [queryAnyPrefix, List.range_succ, List.any_append, Bool.decide_and, Bool.and_assoc]

theorem queryCluster_eq_and_queryAnyPrefix {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    (a ℓ : ℕ) (r : Fin (2 ^ f)) :
    queryCluster st o a ℓ r = (st.isOcc (probeSlot b o a) && queryAnyPrefix st o a ℓ r) := rfl

/-- Loop computing `occBefore st o a` into `reg 10` as `reg 7` walks from `0` to `a` (`reg 4`). -/
@[expose] def occBeforeLoop (w w₀ n : ℕ) : Code .exact rQF :=
  .loop (.lt 7 4)
    (.seq (probeSlotCode (quotBits w₀ n) 5 7 8)
    (.seq (readOccCode w w₀ n 8 9)
    (.seq (.op (.exactBin .add 10 10 9))
          (.op (.exactBin .add 7 7 28)))))

theorem occBeforeLoop_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw : 2 ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (o : Fin (2 ^ quotBits w₀ n)) {a : ℕ} (ha_lt : a < 2 ^ quotBits w₀ n)
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    {mem₀ : ℕ → ℕ} :
    ∀ (rem j : ℕ) (g s : Data rQF),
      j + rem = a →
      ClusterState base w w₀ n k mem₀ g st s →
      g.regs 0 = base →
      g.regs 4 = a →
      g.regs 5 = o.val →
      g.regs 7 = j →
      g.regs 10 = occBefore st o j →
      g.regs 28 = 1 →
      g.regs 29 = 0 →
      ∃ g' y : Data rQF,
        Exec w (occBeforeLoop w w₀ n) s y (20 * rem + 2) ∧
        ClusterState base w w₀ n k mem₀ g' st y ∧
        g'.regs 0 = base ∧
        g'.regs 1 = g.regs 1 ∧
        g'.regs 2 = g.regs 2 ∧
        g'.regs 3 = g.regs 3 ∧
        g'.regs 4 = a ∧
        g'.regs 5 = o.val ∧
        g'.regs 6 = g.regs 6 ∧
        g'.regs 10 = occBefore st o a ∧
        g'.regs 28 = 1 ∧
        g'.regs 29 = 0 ∧
        ∀ r : Fin rQF, 240 ≤ r.val → g'.regs r = g.regs r := by
  intro rem
  have hpow_b : 2 ^ quotBits w₀ n < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  induction rem with
  | zero =>
    intro j g s hsum hs h0 h4 h5 h7 h10 h28 h29
    have hj_eq : j = a := by omega
    subst hj_eq
    have hc : ¬(Cond.lt 7 4).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 7, hs.agree.regs_lt 4, h7, h4]
    exact ⟨g, s, Exec.loop_exit hc, hs, h0, rfl, rfl, rfl, h4, h5, rfl, h10, h28, h29,
      fun _ _ => rfl⟩
  | succ rem ih =>
    intro j g s hsum hs h0 h4 h5 h7 h10 h28 h29
    have hj_lt : j < a := by omega
    have hc : (Cond.lt 7 4).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 7, hs.agree.regs_lt 4, h7, h4, hj_lt]
    have hocc_le : occBefore st o (j + 1) ≤ j + 1 := by
      dsimp only [occBefore]
      exact (List.countP_le_length).trans (by simp)
    have hfit_occ : Fits w (occBefore st o (j + 1)) := by
      change occBefore st o (j + 1) < 2 ^ w
      omega
    have hfit_j1 : Fits w (j + 1) := by change j + 1 < 2 ^ w; omega
    obtain ⟨s1, e1, hs1⟩ := step_probeSlot hb_lt hs 5 7 8 o (d := j) (by omega)
      h5 h7
    obtain ⟨s2, e2, hs2⟩ := step_readOcc hb_lt hw hfit_space hs1 8 9
      (probeSlot (quotBits w₀ n) o j)
      (by simp +decide [h0]) (by simp +decide)
    have hocc_step :
        occBefore st o j + (st.isOcc (probeSlot (quotBits w₀ n) o j)).toNat =
          occBefore st o (j + 1) := by
      rw [occBefore_succ]
      cases st.isOcc (probeSlot (quotBits w₀ n) o j) <;> rfl
    obtain ⟨e3, hs3⟩ := step_bin hs2 .add 10 10 9 (v := occBefore st o (j + 1))
      (by simp +decide [h10, hocc_step]) hfit_occ
    obtain ⟨e4, hs4⟩ := step_bin hs3 .add 7 7 28 (v := j + 1)
      (by simp +decide [h7, h28]) hfit_j1
    obtain ⟨g', y, hy_exec, hy_st, h0', h1', h2', h3', h4', h5', h6', h10', h28', h29', h240'⟩ :=
      ih (j + 1) _ (s2.set 10 (occBefore st o (j + 1)) |>.set 7 (j + 1)) (by omega) hs4
        (by simp +decide [h0])
        (by simp +decide [h4])
        (by simp +decide [h5])
        (by simp +decide)
        (by simp +decide)
        (by simp +decide [h28])
        (by simp +decide [h29])
    have hiter := Exec.loop_iter hc (e1.seq (e2.seq (e3.seq e4))) hy_exec
    refine ⟨g', y, ?_, hy_st, h0', ?_, ?_, ?_, h4', h5', ?_, h10', h28', h29', ?_⟩
    · simpa only [occBeforeLoop,
        show (3 + (13 + (1 + 1))) + (20 * rem + 2) + 2 = 20 * (rem + 1) + 2 by omega] using hiter
    · rw [h1']; simp +decide
    · rw [h2']; simp +decide
    · rw [h3']; simp +decide
    · rw [h6']; simp +decide
    · intro r hr
      rw [h240' r hr]
      have hr7 : r ≠ 7 := Fin.ne_of_val_ne (by change r.val ≠ 7; omega)
      have hr8 : r ≠ 8 := Fin.ne_of_val_ne (by change r.val ≠ 8; omega)
      have hr9 : r ≠ 9 := Fin.ne_of_val_ne (by change r.val ≠ 9; omega)
      have hr10 : r ≠ 10 := Fin.ne_of_val_ne (by change r.val ≠ 10; omega)
      simp [hr7, hr8, hr9, hr10]

private theorem toNat_not (b : Bool) : (!b).toNat = 1 - b.toNat := by
  cases b <;> rfl

private theorem toNat_and (b₁ b₂ : Bool) : (b₁ && b₂).toNat = b₁.toNat &&& b₂.toNat := by
  cases b₁ <;> cases b₂ <;> rfl

private theorem toNat_or (b₁ b₂ : Bool) : (b₁ || b₂).toNat = b₁.toNat ||| b₂.toNat := by
  cases b₁ <;> cases b₂ <;> rfl

private theorem decide_le_eq_not_decide_lt (x y : ℕ) :
    decide (x ≤ y) = !decide (y < x) := by
  by_cases h : y < x <;> simp [h, not_lt.mp]

/-- Single-pass loop over `m = 0 .. ℓ - 1` (`reg 7 < reg 6`) computing `calcRunStart`,
`calcTargetSlot`, `calcDeleteStopPrefix`, and `queryAnyPrefix`. -/
@[expose] def scanClusterLoop (w w₀ n k : ℕ) : Code .exact rQF :=
  .loop (.lt 7 6)
    (.seq (probeSlotCode (quotBits w₀ n) 5 7 8)
    (.seq (readOccCode w w₀ n 8 20)
    (.seq (readRunStartCode w w₀ n 8 21)
    (.seq (readRemCode w w₀ n k 8 22)
    (.seq (.op (.exactBin .add 14 14 21))
    (.seq (evalCondCode (.lt 10 14) 23)
    (.seq (.op (.exactBin .sub 24 28 23))
    (.seq (.op (.exactBin .add 15 15 24))
    (.seq (evalCondCode (.lt 12 14) 25)
    (.seq (.op (.exactBin .sub 25 28 25))
    (.seq (evalCondCode (.lt 22 3) 26)
    (.seq (.op (.exactBin .and 26 25 26))
    (.seq (.op (.exactBin .or 26 24 26))
    (.seq (.op (.exactBin .add 16 16 26))
    (.seq (evalCondCode (.eq 22 3) 26)
    (.seq (.op (.exactBin .and 27 23 25))
    (.seq (.op (.exactBin .and 27 27 26))
    (.seq (.op (.exactBin .or 18 18 27))
    (.seq (evalCondCode (.eq 17 6) 23)
    (.seq (evalCondCode (.lt 4 7) 24)
    (.seq (evalCondCode (.lt 13 14) 25)
    (.seq (.op (.exactBin .and 23 23 24))
    (.seq (.op (.exactBin .and 23 23 25))
    (.seq (condCopyCode (.lt 29 23) 17 7)
    (.seq (.op (.exactBin .add 13 13 20))
          (.op (.exactBin .add 7 7 28)))))))))))))))))))))))))))

theorem scanClusterLoop_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (o : Fin (2 ^ quotBits w₀ n)) {a ℓ : ℕ} (hℓ_lt : ℓ < 2 ^ quotBits w₀ n)
    (r : Fin (2 ^ remBits w₀ k))
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    {mem₀ : ℕ → ℕ} :
    ∀ (rem m : ℕ) (g s : Data rQF),
      m + rem = ℓ →
      ClusterState base w w₀ n k mem₀ g st s →
      g.regs 0 = base →
      g.regs 3 = r.val →
      g.regs 4 = a →
      g.regs 5 = o.val →
      g.regs 6 = ℓ →
      g.regs 7 = m →
      g.regs 10 = occBefore st o a →
      g.regs 12 = occBefore st o (a + 1) →
      g.regs 13 = occBefore st o m →
      g.regs 14 = runsBefore st o m →
      g.regs 15 = calcRunStart st o a m →
      g.regs 16 = calcTargetSlot st o a m r →
      g.regs 17 = calcDeleteStopPrefix st o a ℓ m →
      g.regs 18 = (queryAnyPrefix st o a m r).toNat →
      g.regs 28 = 1 →
      g.regs 29 = 0 →
      ∃ g' y : Data rQF,
        Exec w (scanClusterLoop w w₀ n k) s y (82 * rem + 2) ∧
        ClusterState base w w₀ n k mem₀ g' st y ∧
        g'.regs 0 = base ∧
        g'.regs 1 = g.regs 1 ∧
        g'.regs 2 = g.regs 2 ∧
        g'.regs 3 = r.val ∧
        g'.regs 4 = a ∧
        g'.regs 5 = o.val ∧
        g'.regs 6 = ℓ ∧
        g'.regs 11 = g.regs 11 ∧
        g'.regs 15 = calcRunStart st o a ℓ ∧
        g'.regs 16 = calcTargetSlot st o a ℓ r ∧
        g'.regs 17 = calcDeleteStop st o a ℓ ∧
        g'.regs 18 = (queryAnyPrefix st o a ℓ r).toNat ∧
        g'.regs 28 = 1 ∧
        g'.regs 29 = 0 ∧
        ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  intro rem
  have hw2 : 2 ≤ w := by omega
  have hw1 : 1 ≤ w := by omega
  have hpow_b : 2 ^ quotBits w₀ n < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  have hpow_1 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw1
  have hfit_bool : ∀ b : Bool, Fits w b.toNat := fun b => (Bool.toNat_lt b).trans_le hpow_1
  induction rem with
  | zero =>
    intro m g s hsum hs h0 h3 h4 h5 h6 h7 _ _ _ _ h15 h16 h17 h18 h28 h29
    have hm_eq : m = ℓ := by omega
    subst hm_eq
    have hc : ¬(Cond.lt 7 6).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 7, hs.agree.regs_lt 6, h7, h6]
    exact ⟨g, s, Exec.loop_exit hc, hs, h0, rfl, rfl, h3, h4, h5, h6, rfl,
      h15, h16, h17, h18, h28, h29, fun _ _ => rfl⟩
  | succ rem ih =>
    intro m g s hsum hs h0 h3 h4 h5 h6 h7 h10 h12 h13 h14 h15 h16 h17 h18 h28 h29
    have hm_lt : m < ℓ := by omega
    have hc : (Cond.lt 7 6).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 7, hs.agree.regs_lt 6, h7, h6, hm_lt]
    let p := probeSlot (quotBits w₀ n) o m
    have hruns_le : runsBefore st o (m + 1) ≤ m + 1 := by
      dsimp only [runsBefore]
      exact (List.countP_le_length).trans (by simp)
    have hocc_le : occBefore st o (m + 1) ≤ m + 1 := by
      dsimp only [occBefore]
      exact (List.countP_le_length).trans (by simp)
    have hs₀_le : calcRunStart st o a (m + 1) ≤ m + 1 := by
      dsimp only [calcRunStart]
      exact (List.length_filter_le _ _).trans (by simp)
    have hs_le : calcTargetSlot st o a (m + 1) r ≤ m + 1 := by
      dsimp only [calcTargetSlot]
      exact (List.length_filter_le _ _).trans (by simp)
    have hfit_runs1 : Fits w (runsBefore st o (m + 1)) := by
      change runsBefore st o (m + 1) < 2 ^ w; omega
    have hfit_occ1 : Fits w (occBefore st o (m + 1)) := by
      change occBefore st o (m + 1) < 2 ^ w; omega
    have hfit_s₀1 : Fits w (calcRunStart st o a (m + 1)) := by
      change calcRunStart st o a (m + 1) < 2 ^ w; omega
    have hfit_s1 : Fits w (calcTargetSlot st o a (m + 1) r) := by
      change calcTargetSlot st o a (m + 1) r < 2 ^ w; omega
    have hfit_m1 : Fits w (m + 1) := by change m + 1 < 2 ^ w; omega
    -- 1. probeSlotCode (3 steps)
    obtain ⟨s1, e1, hs1⟩ := step_probeSlot hb_lt hs 5 7 8 o (d := m) (by omega) h5 h7
    -- 2. readOccCode (13 steps)
    obtain ⟨s2, e2, hs2⟩ := step_readOcc hb_lt hw2 hfit_space hs1 8 20 p
      (by simp +decide [h0]) (by simp +decide [p])
    -- 3. readRunStartCode (13 steps)
    obtain ⟨s3, e3, hs3⟩ := step_readRunStart hb_lt hw2 hfit_space hs2 8 21 p
      (by simp +decide [h0]) (by simp +decide [p])
    -- 4. readRemCode (13 steps)
    obtain ⟨s4, e4, hs4⟩ := step_readRem hb_lt hw₀_pos hw hfit_space hs3 8 22 p
      (by simp +decide [h0]) (by simp +decide [p])
    -- 5. runsBefore st o (m + 1) (1 step)
    have hruns_step : runsBefore st o m + (st.isRunStart p).toNat = runsBefore st o (m + 1) := by
      rw [runsBefore_succ]; cases st.isRunStart p <;> rfl
    obtain ⟨e5, hs5⟩ := step_bin hs4 .add 14 14 21 (v := runsBefore st o (m + 1))
      (by simp +decide [h14, hruns_step]) hfit_runs1
    -- 6. evalCondCode (.lt 10 14) 23 (3 steps)
    obtain ⟨e6, hs6⟩ := step_evalLt hw1 hs5 10 14 23
      (va := occBefore st o a) (vb := runsBefore st o (m + 1))
      (by simp +decide [h10]) (by simp +decide)
    -- 7. reg 24 ← reg 28 - reg 23 (1 step)
    let b_gt_a := decide (occBefore st o a < runsBefore st o (m + 1))
    let b_le_a := decide (runsBefore st o (m + 1) ≤ occBefore st o a)
    have h24_eq : 1 - b_gt_a.toNat = b_le_a.toNat := by
      dsimp only [b_gt_a, b_le_a]
      rw [decide_le_eq_not_decide_lt, toNat_not]
    have hsub_24 :
        BinOp.sub.evalExact
          ((g.set 8 p.val |>.set 20 (st.isOcc p).toNat |>.set 21 (st.isRunStart p).toNat
            |>.set 22 (st.remAt p).val |>.set 14 (runsBefore st o (m + 1))
            |>.set 23 b_gt_a.toNat).regs 28)
          ((g.set 8 p.val |>.set 20 (st.isOcc p).toNat |>.set 21 (st.isRunStart p).toNat
            |>.set 22 (st.remAt p).val |>.set 14 (runsBefore st o (m + 1))
            |>.set 23 b_gt_a.toNat).regs 23) = some b_le_a.toNat := by
      have hlt : b_gt_a.toNat ≤ 1 := Nat.le_of_lt_succ (Bool.toNat_lt b_gt_a)
      simp +decide [BinOp.evalExact, h28, hlt, h24_eq]
    obtain ⟨e7, hs7⟩ := step_bin hs6 .sub 24 28 23 (v := b_le_a.toNat) hsub_24 (hfit_bool b_le_a)
    -- 8. reg 15 ← reg 15 + reg 24 (1 step)
    obtain ⟨e8, hs8⟩ := step_bin hs7 .add 15 15 24 (v := calcRunStart st o a (m + 1))
      (by simp +decide [h15, calcRunStart_succ, b_le_a]) hfit_s₀1
    -- 9. evalCondCode (.lt 12 14) 25 (3 steps)
    obtain ⟨e9, hs9⟩ := step_evalLt hw1 hs8 12 14 25
      (va := occBefore st o (a + 1)) (vb := runsBefore st o (m + 1))
      (by simp +decide [h12]) (by simp +decide)
    -- 10. reg 25 ← reg 28 - reg 25 (1 step)
    let b_gt_a1 := decide (occBefore st o (a + 1) < runsBefore st o (m + 1))
    let b_le_a1 := decide (runsBefore st o (m + 1) ≤ occBefore st o (a + 1))
    have h25_eq : 1 - b_gt_a1.toNat = b_le_a1.toNat := by
      dsimp only [b_gt_a1, b_le_a1]
      rw [decide_le_eq_not_decide_lt, toNat_not]
    have hsub_25 :
        BinOp.sub.evalExact
          ((g.set 8 p.val |>.set 20 (st.isOcc p).toNat |>.set 21 (st.isRunStart p).toNat
            |>.set 22 (st.remAt p).val |>.set 14 (runsBefore st o (m + 1))
            |>.set 23 b_gt_a.toNat |>.set 24 b_le_a.toNat
            |>.set 15 (calcRunStart st o a (m + 1))
            |>.set 25 b_gt_a1.toNat).regs 28)
          ((g.set 8 p.val |>.set 20 (st.isOcc p).toNat |>.set 21 (st.isRunStart p).toNat
            |>.set 22 (st.remAt p).val |>.set 14 (runsBefore st o (m + 1))
            |>.set 23 b_gt_a.toNat |>.set 24 b_le_a.toNat
            |>.set 15 (calcRunStart st o a (m + 1))
            |>.set 25 b_gt_a1.toNat).regs 25) = some b_le_a1.toNat := by
      have hlt : b_gt_a1.toNat ≤ 1 := Nat.le_of_lt_succ (Bool.toNat_lt b_gt_a1)
      simp +decide [BinOp.evalExact, h28, hlt, h25_eq]
    obtain ⟨e10, hs10⟩ := step_bin hs9 .sub 25 28 25 (v := b_le_a1.toNat)
      hsub_25 (hfit_bool b_le_a1)
    -- 11. evalCondCode (.lt 22 3) 26 (3 steps)
    obtain ⟨e11, hs11⟩ := step_evalLt hw1 hs10 22 3 26
      (va := (st.remAt p).val) (vb := r.val)
      (by simp +decide) (by simp +decide [h3])
    -- 12. reg 26 ← reg 25 &&& reg 26 (1 step)
    let b_rem_lt := decide (st.remAt p < r)
    obtain ⟨e12, hs12⟩ := step_bin hs11 .and 26 25 26 (v := (b_le_a1 && b_rem_lt).toNat)
      (by simp +decide [b_rem_lt, toNat_and]) (hfit_bool _)
    -- 13. reg 26 ← reg 24 ||| reg 26 (1 step)
    obtain ⟨e13, hs13⟩ := step_bin hs12 .or 26 24 26
      (v := (b_le_a || (b_le_a1 && b_rem_lt)).toNat)
      (by simp +decide [toNat_or]) (hfit_bool _)
    -- 14. reg 16 ← reg 16 + reg 26 (1 step)
    obtain ⟨e14, hs14⟩ := step_bin hs13 .add 16 16 26 (v := calcTargetSlot st o a (m + 1) r)
      (by simp +decide [h16, calcTargetSlot_succ, b_le_a, b_le_a1, b_rem_lt, p]) hfit_s1
    -- 15. evalCondCode (.eq 22 3) 26 (3 steps)
    obtain ⟨e15, hs15⟩ := step_evalEq hw1 hs14 22 3 26
      (va := (st.remAt p).val) (vb := r.val)
      (by simp +decide) (by simp +decide [h3])
    -- 16. reg 27 ← reg 23 &&& reg 25 (1 step)
    let b_rem_eq := decide (st.remAt p = r)
    have hrem_eq_val : decide ((st.remAt p).val = r.val) = b_rem_eq := by
      simp [b_rem_eq, Fin.ext_iff]
    obtain ⟨e16, hs16⟩ := step_bin hs15 .and 27 23 25 (v := (b_gt_a && b_le_a1).toNat)
      (by simp +decide [b_gt_a, toNat_and]) (hfit_bool _)
    -- 17. reg 27 ← reg 27 &&& reg 26 (1 step)
    obtain ⟨e17, hs17⟩ := step_bin hs16 .and 27 27 26
      (v := (b_gt_a && b_le_a1 && b_rem_eq).toNat)
      (by simp +decide [hrem_eq_val, toNat_and]) (hfit_bool _)
    -- 18. reg 18 ← reg 18 ||| reg 27 (1 step)
    obtain ⟨e18, hs18⟩ := step_bin hs17 .or 18 18 27
      (v := (queryAnyPrefix st o a (m + 1) r).toNat)
      (by simp +decide [h18, queryAnyPrefix_succ, b_gt_a, b_le_a1, b_rem_eq, p, toNat_or])
      (hfit_bool _)
    -- 19. evalCondCode (.eq 17 6) 23 (3 steps)
    obtain ⟨e19, hs19⟩ := step_evalEq hw1 hs18 17 6 23
      (va := calcDeleteStopPrefix st o a ℓ m) (vb := ℓ)
      (by simp +decide [h17]) (by simp +decide [h6])
    -- 20. evalCondCode (.lt 4 7) 24 (3 steps)
    obtain ⟨e20, hs20⟩ := step_evalLt hw1 hs19 4 7 24
      (va := a) (vb := m)
      (by simp +decide [h4]) (by simp +decide [h7])
    -- 21. evalCondCode (.lt 13 14) 25 (3 steps)
    obtain ⟨e21, hs21⟩ := step_evalLt hw1 hs20 13 14 25
      (va := occBefore st o m) (vb := runsBefore st o (m + 1))
      (by simp +decide [h13]) (by simp +decide)
    -- 22. reg 23 ← reg 23 &&& reg 24 (1 step)
    let b_e_eq := decide (calcDeleteStopPrefix st o a ℓ m = ℓ)
    let b_a_lt := decide (a < m)
    let b_occ_lt := decide (occBefore st o m < runsBefore st o (m + 1))
    obtain ⟨e22, hs22⟩ := step_bin hs21 .and 23 23 24 (v := (b_e_eq && b_a_lt).toNat)
      (by simp +decide [b_e_eq, b_a_lt, toNat_and]) (hfit_bool _)
    -- 23. reg 23 ← reg 23 &&& reg 25 (1 step)
    let b_del_cond := b_e_eq && b_a_lt && b_occ_lt
    obtain ⟨e23, hs23⟩ := step_bin hs22 .and 23 23 25 (v := b_del_cond.toNat)
      (by simp +decide [b_occ_lt, b_del_cond, toNat_and]) (hfit_bool _)
    -- 24. condCopyCode (.lt 29 23) 17 7 (3 steps)
    obtain ⟨e24, hs24⟩ := step_condCopyLt hs23 29 23 17 7
      (va := 0) (vb := b_del_cond.toNat)
      (vdst := calcDeleteStopPrefix st o a ℓ m) (vsrc := m)
      (by simp +decide [h29]) (by simp +decide) (by simp +decide [h17]) (by simp +decide [h7])
    -- 25. reg 13 ← reg 13 + reg 20 (1 step)
    have hocc_step : occBefore st o m + (st.isOcc p).toNat = occBefore st o (m + 1) := by
      rw [occBefore_succ]; cases st.isOcc p <;> rfl
    obtain ⟨e25, hs25⟩ := step_bin hs24 .add 13 13 20 (v := occBefore st o (m + 1))
      (by simp +decide [h13, hocc_step]) hfit_occ1
    -- 26. reg 7 ← reg 7 + reg 28 (1 step)
    obtain ⟨e26, hs26⟩ := step_bin hs25 .add 7 7 28 (v := m + 1)
      (by simp +decide [h7, h28]) hfit_m1
    have h17_next :
        (if 0 < b_del_cond.toNat then m else calcDeleteStopPrefix st o a ℓ m) =
          calcDeleteStopPrefix st o a ℓ (m + 1) := by
      rw [calcDeleteStopPrefix_succ st o a ℓ hm_lt]
      change (if 0 < b_del_cond.toNat then m else _) = if b_del_cond = true then m else _
      cases b_del_cond <;> rfl
    obtain ⟨g', y, hy_exec, hy_st, h0', h1', h2', h3', h4', h5', h6', h11',
        h15', h16', h17', h18', h28', h29', h240'⟩ :=
      ih (m + 1) _ _ (by omega) hs26
        (by simp +decide [h0])
        (by simp +decide [h3])
        (by simp +decide [h4])
        (by simp +decide [h5])
        (by simp +decide [h6])
        (by simp +decide)
        (by simp +decide [h10])
        (by simp +decide [h12])
        (by simp +decide)
        (by simp +decide)
        (by simp +decide)
        (by simp +decide)
        (by simp +decide [h17_next])
        (by simp +decide)
        (by simp +decide [h28])
        (by simp +decide [h29])
    have ebody := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
      (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq (e16.seq (e17.seq (e18.seq (e19.seq (e20.seq
      (e21.seq (e22.seq (e23.seq (e24.seq (e25.seq e26))))))))))))))))))))))))
    have hiter := Exec.loop_iter hc ebody hy_exec
    refine ⟨g', y, ?_, hy_st, h0', ?_, ?_, h3', h4', h5', h6', ?_,
      h15', h16', h17', h18', h28', h29', ?_⟩
    · simpa only [scanClusterLoop,
        show (3 + (13 + (13 + (13 + (1 + (3 + (1 + (1 + (3 + (1 + (3 + (1 + (1 + (1 + (3 + (1 +
          (1 + (1 + (3 + (3 + (3 + (1 + (1 + (3 + (1 + 1))))))))))))))))))))))))) +
          (82 * rem + 2) + 2 = 82 * (rem + 1) + 2 by omega] using hiter
    · rw [h1']; simp +decide
    · rw [h2']; simp +decide
    · rw [h11']; simp +decide
    · intro j hj
      rw [h240' j hj]
      have hj7 : j ≠ 7 := Fin.ne_of_val_ne (by change j.val ≠ 7; omega)
      have hj8 : j ≠ 8 := Fin.ne_of_val_ne (by change j.val ≠ 8; omega)
      have hj13 : j ≠ 13 := Fin.ne_of_val_ne (by change j.val ≠ 13; omega)
      have hj14 : j ≠ 14 := Fin.ne_of_val_ne (by change j.val ≠ 14; omega)
      have hj15 : j ≠ 15 := Fin.ne_of_val_ne (by change j.val ≠ 15; omega)
      have hj16 : j ≠ 16 := Fin.ne_of_val_ne (by change j.val ≠ 16; omega)
      have hj17 : j ≠ 17 := Fin.ne_of_val_ne (by change j.val ≠ 17; omega)
      have hj18 : j ≠ 18 := Fin.ne_of_val_ne (by change j.val ≠ 18; omega)
      have hj20 : j ≠ 20 := Fin.ne_of_val_ne (by change j.val ≠ 20; omega)
      have hj21 : j ≠ 21 := Fin.ne_of_val_ne (by change j.val ≠ 21; omega)
      have hj22 : j ≠ 22 := Fin.ne_of_val_ne (by change j.val ≠ 22; omega)
      have hj23 : j ≠ 23 := Fin.ne_of_val_ne (by change j.val ≠ 23; omega)
      have hj24 : j ≠ 24 := Fin.ne_of_val_ne (by change j.val ≠ 24; omega)
      have hj25 : j ≠ 25 := Fin.ne_of_val_ne (by change j.val ≠ 25; omega)
      have hj26 : j ≠ 26 := Fin.ne_of_val_ne (by change j.val ≠ 26; omega)
      have hj27 : j ≠ 27 := Fin.ne_of_val_ne (by change j.val ≠ 27; omega)
      simp [hj7, hj8, hj13, hj14, hj15, hj16, hj17, hj18, hj20, hj21, hj22, hj23, hj24, hj25,
        hj26, hj27]

/-- Word-RAM program scanning cluster `[o .. o + ℓ)` to compute `s₀` (`reg 15`), `s` (`reg 16`),
`e` (`reg 17`), and `(queryCluster st o a ℓ r).toNat` (`reg 18`). -/
@[expose] def scanClusterCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (.op (.const 7 0))
  (.seq (.op (.const 10 0))
  (.seq (occBeforeLoop w w₀ n)
  (.seq (readOccCode w w₀ n 2 11)
  (.seq (.op (.exactBin .add 12 10 11))
  (.seq (.op (.const 7 0))
  (.seq (.op (.const 13 0))
  (.seq (.op (.const 14 0))
  (.seq (.op (.const 15 0))
  (.seq (.op (.const 16 0))
  (.seq (.op (.copy 17 6))
  (.seq (.op (.const 18 0))
  (.seq (scanClusterLoop w w₀ n k)
        (.op (.exactBin .and 18 11 18))))))))))))))

/-- Exact instruction count of `scanClusterCode` for offset `a` and cluster length `ℓ`. -/
@[expose] def scanClusterSteps (a ℓ : ℕ) : ℕ :=
  20 * a + 82 * ℓ + 28

theorem scanClusterCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (o : Fin (2 ^ quotBits w₀ n)) {a ℓ : ℕ} (ha_le : a ≤ ℓ) (hℓ_lt : ℓ < 2 ^ quotBits w₀ n)
    (r : Fin (2 ^ remBits w₀ k))
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    {mem₀ : ℕ → ℕ} {g s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (h0 : g.regs 0 = base)
    (h2 : g.regs 2 = (probeSlot (quotBits w₀ n) o a).val)
    (h3 : g.regs 3 = r.val)
    (h4 : g.regs 4 = a)
    (h5 : g.regs 5 = o.val)
    (h6 : g.regs 6 = ℓ)
    (h28 : g.regs 28 = 1)
    (h29 : g.regs 29 = 0) :
    ∃ g' y : Data rQF,
      Exec w (scanClusterCode w w₀ n k) s y (scanClusterSteps a ℓ) ∧
      ClusterState base w w₀ n k mem₀ g' st y ∧
      g'.regs 0 = base ∧
      g'.regs 1 = g.regs 1 ∧
      g'.regs 2 = (probeSlot (quotBits w₀ n) o a).val ∧
      g'.regs 3 = r.val ∧
      g'.regs 4 = a ∧
      g'.regs 5 = o.val ∧
      g'.regs 6 = ℓ ∧
      g'.regs 11 = (st.isOcc (probeSlot (quotBits w₀ n) o a)).toNat ∧
      g'.regs 15 = calcRunStart st o a ℓ ∧
      g'.regs 16 = calcTargetSlot st o a ℓ r ∧
      g'.regs 17 = calcDeleteStop st o a ℓ ∧
      g'.regs 18 = (queryCluster st o a ℓ r).toNat ∧
      g'.regs 28 = 1 ∧
      g'.regs 29 = 0 ∧
      ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  have hw2 : 2 ≤ w := by omega
  have hpow_b : 2 ^ quotBits w₀ n < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  have hfit0 : Fits w 0 := Nat.two_pow_pos w
  have hocc_a1_le : occBefore st o (a + 1) ≤ a + 1 := by
    dsimp only [occBefore]; exact (List.countP_le_length).trans (by simp)
  have hfit_occ_a1 : Fits w (occBefore st o (a + 1)) := by
    change occBefore st o (a + 1) < 2 ^ w; omega
  have hpow_1 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
  have hfit_q : Fits w (queryCluster st o a ℓ r).toNat :=
    (Bool.toNat_lt _).trans_le hpow_1
  obtain ⟨e1, hs1⟩ := step_const hs 7 hfit0
  obtain ⟨e2, hs2⟩ := step_const hs1 10 hfit0
  obtain ⟨g3, s3, e3, hs3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_10, h3_28, h3_29, h3_240⟩ :=
    occBeforeLoop_exec (a := a) hb_lt hw2 hfit_space o (by omega) a 0 _ (s.set 7 0 |>.set 10 0)
      (by omega) hs2
      (by simp +decide [h0])
      (by simp +decide [h4])
      (by simp +decide [h5])
      (by simp +decide)
      (by simp +decide)
      (by simp +decide [h28])
      (by simp +decide [h29])
  have h3_2_eq : g3.regs 2 = (probeSlot (quotBits w₀ n) o a).val := by
    rw [h3_2]; simp +decide [h2]
  have h3_3_eq : g3.regs 3 = r.val := by
    rw [h3_3]; simp +decide [h3]
  have h3_6_eq : g3.regs 6 = ℓ := by
    rw [h3_6]; simp +decide [h6]
  obtain ⟨s4, e4, hs4⟩ := step_readOcc hb_lt hw2 hfit_space hs3 2 11
    (probeSlot (quotBits w₀ n) o a) h3_0 h3_2_eq
  have hocc_a1_step :
      occBefore st o a + (st.isOcc (probeSlot (quotBits w₀ n) o a)).toNat =
        occBefore st o (a + 1) := by
    rw [occBefore_succ]; cases st.isOcc (probeSlot (quotBits w₀ n) o a) <;> rfl
  obtain ⟨e5, hs5⟩ := step_bin hs4 .add 12 10 11 (v := occBefore st o (a + 1))
    (by simp +decide [h3_10, hocc_a1_step]) hfit_occ_a1
  obtain ⟨e6, hs6⟩ := step_const hs5 7 hfit0
  obtain ⟨e7, hs7⟩ := step_const hs6 13 hfit0
  obtain ⟨e8, hs8⟩ := step_const hs7 14 hfit0
  obtain ⟨e9, hs9⟩ := step_const hs8 15 hfit0
  obtain ⟨e10, hs10⟩ := step_const hs9 16 hfit0
  obtain ⟨e11, hs11⟩ := step_copy hs10 17 6 (v := ℓ) (by simp +decide [h3_6_eq])
  obtain ⟨e12, hs12⟩ := step_const hs11 18 hfit0
  obtain ⟨g13, s13, e13, hs13, h13_0, h13_1, h13_2, h13_3, h13_4, h13_5, h13_6, h13_11,
      h13_15, h13_16, h13_17, h13_18, h13_28, h13_29, h13_240⟩ :=
    scanClusterLoop_exec (a := a) (ℓ := ℓ) hb_lt hw₀_pos hw hfit_space o hℓ_lt r
      ℓ 0 _ _ (by omega) hs12
      (by simp +decide [h3_0])
      (by simp +decide [h3_3_eq])
      (by simp +decide [h3_4])
      (by simp +decide [h3_5])
      (by simp +decide [h3_6_eq])
      (by simp +decide)
      (by simp +decide [h3_10])
      (by simp +decide)
      (by simp +decide)
      (by simp +decide)
      (by simp +decide [calcRunStart_zero])
      (by simp +decide [calcTargetSlot_zero])
      (by simp +decide [calcDeleteStopPrefix_zero])
      (by simp +decide [queryAnyPrefix_zero])
      (by simp +decide [h3_28])
      (by simp +decide [h3_29])
  have h13_11_eq : g13.regs 11 = (st.isOcc (probeSlot (quotBits w₀ n) o a)).toNat := by
    rw [h13_11]; simp +decide
  obtain ⟨e14, hs14⟩ := step_bin hs13 .and 18 11 18 (v := (queryCluster st o a ℓ r).toNat)
    (by simp [h13_11_eq, h13_18, queryCluster_eq_and_queryAnyPrefix, toNat_and]) hfit_q
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq
    (e9.seq (e10.seq (e11.seq (e12.seq (e13.seq e14))))))))))))
  refine ⟨g13.set 18 (queryCluster st o a ℓ r).toNat, s13.set 18 (queryCluster st o a ℓ r).toNat,
    ?_, hs14, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [scanClusterCode, scanClusterSteps,
      show 1 + (1 + ((20 * a + 2) + (13 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
        ((82 * ℓ + 2) + 1)))))))))))) = 20 * a + 82 * ℓ + 28 by omega] using hall
  · simp +decide [h13_0]
  · simp +decide [h13_1, h3_1]
  · simp +decide [h13_2, h3_2_eq]
  · simp +decide [h13_3]
  · simp +decide [h13_4]
  · simp +decide [h13_5]
  · simp +decide [h13_6]
  · simp +decide [h13_11_eq]
  · simp +decide [h13_15]
  · simp +decide [h13_16]
  · simp +decide [h13_17]
  · simp +decide
  · simp +decide [h13_28]
  · simp +decide [h13_29]
  · intro j hj
    have hj18 : j ≠ 18 := Fin.ne_of_val_ne (by change j.val ≠ 18; omega)
    have hj17 : j ≠ 17 := Fin.ne_of_val_ne (by change j.val ≠ 17; omega)
    have hj16 : j ≠ 16 := Fin.ne_of_val_ne (by change j.val ≠ 16; omega)
    have hj15 : j ≠ 15 := Fin.ne_of_val_ne (by change j.val ≠ 15; omega)
    have hj14 : j ≠ 14 := Fin.ne_of_val_ne (by change j.val ≠ 14; omega)
    have hj13 : j ≠ 13 := Fin.ne_of_val_ne (by change j.val ≠ 13; omega)
    have hj12 : j ≠ 12 := Fin.ne_of_val_ne (by change j.val ≠ 12; omega)
    have hj11 : j ≠ 11 := Fin.ne_of_val_ne (by change j.val ≠ 11; omega)
    have hj10 : j ≠ 10 := Fin.ne_of_val_ne (by change j.val ≠ 10; omega)
    have hj7 : j ≠ 7 := Fin.ne_of_val_ne (by change j.val ≠ 7; omega)
    simp only [Data.set_regs, Function.update_of_ne hj18]
    rw [h13_240 j hj]
    simp only [Data.set_regs, Function.update_of_ne hj18, Function.update_of_ne hj17,
      Function.update_of_ne hj16, Function.update_of_ne hj15, Function.update_of_ne hj14,
      Function.update_of_ne hj13, Function.update_of_ne hj7, Function.update_of_ne hj12,
      Function.update_of_ne hj11]
    rw [h3_240 j hj]
    simp [hj10, hj7]

/-! ## Section 4: `shiftRightLoop`, `insertAfterScanCode`, and `insertClusterCode` -/

theorem FilterState.setRunStart_self {b f : ℕ} (st : FilterState b f) (p : Fin (2 ^ b)) :
    st.setRunStart p (st.isRunStart p) = st := by
  cases st
  simp [FilterState.setRunStart]

theorem FilterState.setOcc_self {b f : ℕ} (st : FilterState b f) (p : Fin (2 ^ b)) :
    st.setOcc p (st.isOcc p) = st := by
  cases st
  simp [FilterState.setOcc]

/-- Loop shifting `(isRunStart, remAt)` right by 1 slot on `[s .. s + rem)` as `reg 7` (`s + rem`)
decrements down to `reg 16` (`s`). -/
@[expose] def shiftRightLoop (w w₀ n k : ℕ) : Code .exact rQF :=
  .loop (.lt 16 7)
    (.seq (probeSlotCode (quotBits w₀ n) 5 7 9)
    (.seq (.op (.exactBin .sub 7 7 28))
    (.seq (probeSlotCode (quotBits w₀ n) 5 7 8)
    (.seq (readRunStartCode w w₀ n 8 21)
    (.seq (readRemCode w w₀ n k 8 22)
    (.seq (writeRunStartCode w w₀ n 9 21)
          (writeRemCode w w₀ n k 9 22)))))))

theorem shiftRightLoop_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (o : Fin (2 ^ quotBits w₀ n)) (s_idx : ℕ)
    {mem₀ : ℕ → ℕ} :
    ∀ (rem : ℕ) (st : FilterState (quotBits w₀ n) (remBits w₀ k)) (g s : Data rQF),
      s_idx + rem < 2 ^ quotBits w₀ n →
      ClusterState base w w₀ n k mem₀ g st s →
      g.regs 0 = base →
      g.regs 5 = o.val →
      g.regs 7 = s_idx + rem →
      g.regs 16 = s_idx →
      g.regs 28 = 1 →
      g.regs 29 = 0 →
      ∃ g' y : Data rQF,
        Exec w (shiftRightLoop w w₀ n k) s y (69 * rem + 2) ∧
        ClusterState base w w₀ n k mem₀ g' (shiftRight st o s_idx rem) y ∧
        g'.regs 0 = base ∧
        g'.regs 1 = g.regs 1 ∧
        g'.regs 2 = g.regs 2 ∧
        g'.regs 3 = g.regs 3 ∧
        g'.regs 4 = g.regs 4 ∧
        g'.regs 5 = o.val ∧
        g'.regs 6 = g.regs 6 ∧
        g'.regs 15 = g.regs 15 ∧
        g'.regs 16 = s_idx ∧
        g'.regs 23 = g.regs 23 ∧
        g'.regs 28 = 1 ∧
        g'.regs 29 = 0 ∧
        ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  intro rem
  have hw2 : 2 ≤ w := by omega
  have hpow_b : 2 ^ quotBits w₀ n < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  induction rem with
  | zero =>
    intro st g s hlt hs h0 h5 h7 h16 h28 h29
    have hc : ¬(Cond.lt 16 7).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 16, hs.agree.regs_lt 7, h16, h7]
    exact ⟨g, s, Exec.loop_exit hc, hs, h0, rfl, rfl, rfl, rfl, h5, rfl, rfl, h16, rfl,
      h28, h29, fun _ _ => rfl⟩
  | succ rem ih =>
    intro st g s hlt hs h0 h5 h7 h16 h28 h29
    have hc : (Cond.lt 16 7).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 16, hs.agree.regs_lt 7, h16, h7]
    let src := probeSlot (quotBits w₀ n) o (s_idx + rem)
    let dst := probeSlot (quotBits w₀ n) o (s_idx + rem + 1)
    have hfit_sr : Fits w (s_idx + rem) := by change s_idx + rem < 2 ^ w; omega
    -- 1. probeSlotCode 5 7 9 (3 steps)
    obtain ⟨s1, e1, hs1⟩ := step_probeSlot hb_lt hs 5 7 9 o (d := s_idx + rem + 1) (by omega)
      h5 (by simpa [Nat.add_assoc] using h7)
    -- 2. reg 7 ← reg 7 - reg 28 (1 step)
    have hsub7 :
        BinOp.sub.evalExact
          ((g.set 9 dst.val).regs 7) ((g.set 9 dst.val).regs 28) = some (s_idx + rem) := by
      simp +decide [BinOp.evalExact, h7, h28]
    obtain ⟨e2, hs2⟩ := step_bin hs1 .sub 7 7 28 (v := s_idx + rem) hsub7 hfit_sr
    -- 3. probeSlotCode 5 7 8 (3 steps)
    obtain ⟨s3, e3, hs3⟩ := step_probeSlot hb_lt hs2 5 7 8 o (d := s_idx + rem) (by omega)
      (by simp +decide [h5]) (by simp +decide)
    -- 4. readRunStartCode 8 21 (13 steps)
    obtain ⟨s4, e4, hs4⟩ := step_readRunStart hb_lt hw2 hfit_space hs3 8 21 src
      (by simp +decide [h0]) (by simp +decide [src])
    -- 5. readRemCode 8 22 (13 steps)
    obtain ⟨s5, e5, hs5⟩ := step_readRem hb_lt hw₀_pos hw hfit_space hs4 8 22 src
      (by simp +decide [h0]) (by simp +decide [src])
    -- 6. writeRunStartCode 9 21 (17 steps)
    obtain ⟨s6, e6, hs6⟩ := step_writeRunStart hb_lt hw2 hfit_space hs5 9 21 dst
      (st.isRunStart src)
      (by simp +decide [h0]) (by simp +decide [dst]) (by simp +decide)
    -- 7. writeRemCode 9 22 (17 steps)
    obtain ⟨s7, e7, hs7⟩ := step_writeRem hb_lt hw₀_pos hw hfit_space hs6 9 22 dst
      (st.remAt src)
      (by simp +decide [h0]) (by simp +decide [dst]) (by simp +decide)
    obtain ⟨g', y, hy_exec, hy_st, h0', h1', h2', h3', h4', h5', h6', h15', h16', h23',
        h28', h29', h240'⟩ :=
      ih ((st.setRunStart dst (st.isRunStart src)).setRem dst (st.remAt src)) _ s7
        (by omega) hs7
        (by simp +decide [h0])
        (by simp +decide [h5])
        (by simp +decide)
        (by simp +decide [h16])
        (by simp +decide [h28])
        (by simp +decide [h29])
    have ebody := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
    have hiter := Exec.loop_iter hc ebody hy_exec
    refine ⟨g', y, ?_, hy_st, h0', ?_, ?_, ?_, ?_, h5', ?_, ?_, h16', ?_, h28', h29', ?_⟩
    · simpa only [shiftRightLoop,
        show (3 + (1 + (3 + (13 + (13 + (17 + 17)))))) + (69 * rem + 2) + 2 =
          69 * (rem + 1) + 2 by omega] using hiter
    · rw [h1']; simp +decide
    · rw [h2']; simp +decide
    · rw [h3']; simp +decide
    · rw [h4']; simp +decide
    · rw [h6']; simp +decide
    · rw [h15']; simp +decide
    · rw [h23']; simp +decide
    · intro j hj
      rw [h240' j hj]
      have hj7 : j ≠ 7 := Fin.ne_of_val_ne (by change j.val ≠ 7; omega)
      have hj8 : j ≠ 8 := Fin.ne_of_val_ne (by change j.val ≠ 8; omega)
      have hj9 : j ≠ 9 := Fin.ne_of_val_ne (by change j.val ≠ 9; omega)
      have hj21 : j ≠ 21 := Fin.ne_of_val_ne (by change j.val ≠ 21; omega)
      have hj22 : j ≠ 22 := Fin.ne_of_val_ne (by change j.val ≠ 22; omega)
      simp [hj7, hj8, hj9, hj21, hj22]

/-- Word-RAM program performing the post-scan steps of `insertCluster`. -/
@[expose] def insertAfterScanCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (evalCondCode (.eq 16 15) 23)
  (.seq (.op (.exactBin .and 24 11 23))
  (.seq (.op (.exactBin .sub 24 28 24))
  (.seq (probeSlotCode (quotBits w₀ n) 5 15 8)
  (.seq (readRunStartCode w w₀ n 8 21)
  (.seq (.op (.exactBin .and 21 21 24))
  (.seq (writeRunStartCode w w₀ n 8 21)
  (.seq (.op (.copy 7 6))
  (.seq (shiftRightLoop w w₀ n k)
  (.seq (probeSlotCode (quotBits w₀ n) 5 16 8)
  (.seq (writeRunStartCode w w₀ n 8 23)
  (.seq (writeRemCode w w₀ n k 8 3)
  (.seq (writeOccCode w w₀ n 2 28)
  (.seq (probeSlotCode (quotBits w₀ n) 5 6 8)
        (writeFullCode w w₀ n 8 28))))))))))))))

/-- Exact instruction count of `insertAfterScanCode` when shifting `ℓ - s` slots. -/
@[expose] def insertAfterScanSteps (ℓ s : ℕ) : ℕ :=
  69 * (ℓ - s) + 116

theorem insertAfterScanCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (o : Fin (2 ^ quotBits w₀ n)) {a ℓ : ℕ} (_ha_le : a ≤ ℓ) (hℓ_lt : ℓ < 2 ^ quotBits w₀ n)
    (r : Fin (2 ^ remBits w₀ k))
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    {mem₀ : ℕ → ℕ} {g s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (h0 : g.regs 0 = base)
    (h2 : g.regs 2 = (probeSlot (quotBits w₀ n) o a).val)
    (h3 : g.regs 3 = r.val)
    (_h4 : g.regs 4 = a)
    (h5 : g.regs 5 = o.val)
    (h6 : g.regs 6 = ℓ)
    (h11 : g.regs 11 = (st.isOcc (probeSlot (quotBits w₀ n) o a)).toNat)
    (h15 : g.regs 15 = calcRunStart st o a ℓ)
    (h16 : g.regs 16 = calcTargetSlot st o a ℓ r)
    (h28 : g.regs 28 = 1)
    (h29 : g.regs 29 = 0) :
    ∃ g' y : Data rQF,
      Exec w (insertAfterScanCode w w₀ n k) s y
        (insertAfterScanSteps ℓ (calcTargetSlot st o a ℓ r)) ∧
      ClusterState base w w₀ n k mem₀ g' (insertCluster st o a ℓ r) y ∧
      g'.regs 0 = base ∧
      g'.regs 1 = g.regs 1 ∧
      ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  have hw2 : 2 ≤ w := by omega
  have hw1 : 1 ≤ w := by omega
  have hpow_1 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw1
  have hfit_bool : ∀ b : Bool, Fits w b.toNat := fun b => (Bool.toNat_lt b).trans_le hpow_1
  let q := probeSlot (quotBits w₀ n) o a
  let s₀ := calcRunStart st o a ℓ
  let s_idx := calcTargetSlot st o a ℓ r
  have hs₀_le : s₀ ≤ ℓ := by
    dsimp only [s₀, calcRunStart]; exact (List.length_filter_le _ _).trans (by simp)
  have hs_le : s_idx ≤ ℓ := by
    dsimp only [s_idx, calcTargetSlot]; exact (List.length_filter_le _ _).trans (by simp)
  -- 1. evalCondCode (.eq 16 15) 23 (3 steps)
  obtain ⟨e1, hs1⟩ := step_evalEq hw1 hs 16 15 23 (va := s_idx) (vb := s₀) h16 h15
  -- 2. reg 24 ← reg 11 &&& reg 23 (1 step)
  let b_eq := decide (s_idx = s₀)
  let b_clr := st.isOcc q && b_eq
  obtain ⟨e2, hs2⟩ := step_bin hs1 .and 24 11 23 (v := b_clr.toNat)
    (by simp +decide [h11, q, b_eq, b_clr, toNat_and]) (hfit_bool _)
  -- 3. reg 24 ← reg 28 - reg 24 (1 step)
  let b_keep := !b_clr
  have h24_sub :
      BinOp.sub.evalExact
        ((g.set 23 b_eq.toNat |>.set 24 b_clr.toNat).regs 28)
        ((g.set 23 b_eq.toNat |>.set 24 b_clr.toNat).regs 24) = some b_keep.toNat := by
    have hlt : b_clr.toNat ≤ 1 := Nat.le_of_lt_succ (Bool.toNat_lt b_clr)
    simp +decide [BinOp.evalExact, h28, hlt, b_keep, toNat_not]
  obtain ⟨e3, hs3⟩ := step_bin hs2 .sub 24 28 24 (v := b_keep.toNat) h24_sub (hfit_bool _)
  -- 4. probeSlotCode 5 15 8 (3 steps)
  let p₀ := probeSlot (quotBits w₀ n) o s₀
  obtain ⟨s4, e4, hs4⟩ := step_probeSlot hb_lt hs3 5 15 8 o (d := s₀) (by omega)
    (by simp +decide [h5]) (by simp +decide [h15, s₀])
  -- 5. readRunStartCode 8 21 (13 steps)
  obtain ⟨s5, e5, hs5⟩ := step_readRunStart hb_lt hw2 hfit_space hs4 8 21 p₀
    (by simp +decide [h0]) (by simp +decide [p₀])
  -- 6. reg 21 ← reg 21 &&& reg 24 (1 step)
  let b_rs₀ := st.isRunStart p₀ && b_keep
  obtain ⟨e6, hs6⟩ := step_bin hs5 .and 21 21 24 (v := b_rs₀.toNat)
    (by simp +decide [b_rs₀, toNat_and]) (hfit_bool _)
  -- 7. writeRunStartCode 8 21 (17 steps)
  obtain ⟨s7, e7, hs7⟩ := step_writeRunStart hb_lt hw2 hfit_space hs6 8 21 p₀ b_rs₀
    (by simp +decide [h0]) (by simp +decide [p₀]) (by simp +decide)
  have hst₁_eq :
      st.setRunStart p₀ b_rs₀ =
        (if st.isOcc q && decide (s_idx = s₀) then st.setRunStart p₀ false else st) := by
    dsimp only [b_rs₀, b_keep, b_clr, b_eq]
    cases st.isOcc q && decide (s_idx = s₀)
    · simp [FilterState.setRunStart_self]
    · simp
  -- 8. copy 7 6 (1 step)
  obtain ⟨e8, hs8⟩ := step_copy hs7 7 6 (v := ℓ) (by simp +decide [h6])
  -- 9. shiftRightLoop (69 * (ℓ - s_idx) + 2 steps)
  have hadd_rem : s_idx + (ℓ - s_idx) = ℓ := Nat.add_sub_of_le hs_le
  obtain ⟨g9, s9, e9, hs9, h9_0, h9_1, h9_2, h9_3, _h9_4, h9_5, h9_6, _h9_15, h9_16, h9_23,
      h9_28, _h9_29, h9_240⟩ :=
    shiftRightLoop_exec hb_lt hw₀_pos hw hfit_space o s_idx (ℓ - s_idx)
      (st.setRunStart p₀ b_rs₀) _ _ (by omega) hs8
      (by simp +decide [h0])
      (by simp +decide [h5])
      (by simp +decide [hadd_rem])
      (by simp +decide [h16, s_idx])
      (by simp +decide [h28])
      (by simp +decide [h29])
  -- 10. probeSlotCode 5 16 8 (3 steps)
  let p_s := probeSlot (quotBits w₀ n) o s_idx
  obtain ⟨s10, e10, hs10⟩ := step_probeSlot hb_lt hs9 5 16 8 o (d := s_idx) (by omega)
    h9_5 h9_16
  -- 11. writeRunStartCode 8 23 (17 steps)
  have h9_23_eq : g9.regs 23 = b_eq.toNat := by rw [h9_23]; simp +decide [b_eq]
  have h9_3_eq : g9.regs 3 = r.val := by rw [h9_3]; simp +decide [h3]
  have h9_2_eq : g9.regs 2 = q.val := by rw [h9_2]; simp +decide [h2, q]
  have h9_6_eq : g9.regs 6 = ℓ := by rw [h9_6]; simp +decide [h6]
  obtain ⟨s11, e11, hs11⟩ := step_writeRunStart hb_lt hw2 hfit_space hs10 8 23 p_s b_eq
    (by simp +decide [h9_0]) (by simp +decide [p_s]) (by simp +decide [h9_23_eq])
  -- 12. writeRemCode 8 3 (17 steps)
  obtain ⟨s12, e12, hs12⟩ := step_writeRem hb_lt hw₀_pos hw hfit_space hs11 8 3 p_s r
    (by simp +decide [h9_0]) (by simp +decide [p_s]) (by simp +decide [h9_3_eq])
  -- 13. writeOccCode 2 28 (17 steps)
  obtain ⟨s13, e13, hs13⟩ := step_writeOcc hb_lt hw2 hfit_space hs12 2 28 q true
    (by simp +decide [h9_0]) (by simp +decide [h9_2_eq]) (by simp +decide [h9_28])
  -- 14. probeSlotCode 5 6 8 (3 steps)
  let p_ℓ := probeSlot (quotBits w₀ n) o ℓ
  obtain ⟨s14, e14, hs14⟩ := step_probeSlot hb_lt hs13 5 6 8 o (d := ℓ) (by omega)
    (by simp +decide [h9_5]) (by simp +decide [h9_6_eq])
  -- 15. writeFullCode 8 28 (17 steps)
  obtain ⟨s15, e15, hs15⟩ := step_writeFull hb_lt hw2 hfit_space hs14 8 28 p_ℓ true
    (by simp +decide [h9_0]) (by simp +decide [p_ℓ]) (by simp +decide [h9_28])
  have hst_final :
      ((((shiftRight (st.setRunStart p₀ b_rs₀) o s_idx (ℓ - s_idx)).setRunStart p_s b_eq).setRem
        p_s r).setOcc q true).setFull p_ℓ true = insertCluster st o a ℓ r := by
    rw [hst₁_eq]
    rfl
  rw [hst_final] at hs15
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq
    (e9.seq (e10.seq (e11.seq (e12.seq (e13.seq (e14.seq e15)))))))))))))
  refine ⟨_, s15, ?_, hs15, ?_, ?_, ?_⟩
  · simpa only [insertAfterScanCode, insertAfterScanSteps,
      show 3 + (1 + (1 + (3 + (13 + (1 + (17 + (1 + ((69 * (ℓ - s_idx) + 2) +
        (3 + (17 + (17 + (17 + (3 + 17))))))))))))) = 69 * (ℓ - s_idx) + 116 by omega] using hall
  · simp +decide [h9_0]
  · simp +decide [h9_1]
  · intro j hj
    have hj8 : j ≠ 8 := Fin.ne_of_val_ne (by change j.val ≠ 8; omega)
    have hj7 : j ≠ 7 := Fin.ne_of_val_ne (by change j.val ≠ 7; omega)
    have hj21 : j ≠ 21 := Fin.ne_of_val_ne (by change j.val ≠ 21; omega)
    have hj23 : j ≠ 23 := Fin.ne_of_val_ne (by change j.val ≠ 23; omega)
    have hj24 : j ≠ 24 := Fin.ne_of_val_ne (by change j.val ≠ 24; omega)
    simp only [Data.set_regs, Function.update_of_ne hj8]
    rw [h9_240 j hj]
    simp [hj7, hj8, hj21, hj23, hj24]

/-! ## Section 5: `shiftLeftLoop`, `deleteAfterScanCode`, and top-level cluster programs -/

/-- Loop shifting `(isRunStart, remAt)` left by 1 slot on `[s + 1 .. e)` into `[s .. e - 1)` as
`reg 7` (`cur`) increments up to `reg 19` (`e - 1`). -/
@[expose] def shiftLeftLoop (w w₀ n k : ℕ) : Code .exact rQF :=
  .loop (.lt 7 19)
    (.seq (probeSlotCode (quotBits w₀ n) 5 7 9)
    (.seq (.op (.exactBin .add 7 7 28))
    (.seq (probeSlotCode (quotBits w₀ n) 5 7 8)
    (.seq (readRunStartCode w w₀ n 8 21)
    (.seq (readRemCode w w₀ n k 8 22)
    (.seq (writeRunStartCode w w₀ n 9 21)
          (writeRemCode w w₀ n k 9 22)))))))

theorem shiftLeftLoop_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (o : Fin (2 ^ quotBits w₀ n)) (endIdx : ℕ) (hend_lt : endIdx < 2 ^ quotBits w₀ n)
    {mem₀ : ℕ → ℕ} :
    ∀ (rem cur : ℕ) (st : FilterState (quotBits w₀ n) (remBits w₀ k)) (g s : Data rQF),
      cur + rem = endIdx →
      ClusterState base w w₀ n k mem₀ g st s →
      g.regs 0 = base →
      g.regs 5 = o.val →
      g.regs 7 = cur →
      g.regs 19 = endIdx →
      g.regs 28 = 1 →
      g.regs 29 = 0 →
      ∃ g' y : Data rQF,
        Exec w (shiftLeftLoop w w₀ n k) s y (69 * rem + 2) ∧
        ClusterState base w w₀ n k mem₀ g' (shiftLeft st o cur rem) y ∧
        g'.regs 0 = base ∧
        g'.regs 1 = g.regs 1 ∧
        g'.regs 2 = g.regs 2 ∧
        g'.regs 3 = g.regs 3 ∧
        g'.regs 4 = g.regs 4 ∧
        g'.regs 5 = o.val ∧
        g'.regs 6 = g.regs 6 ∧
        g'.regs 11 = g.regs 11 ∧
        g'.regs 15 = g.regs 15 ∧
        g'.regs 16 = g.regs 16 ∧
        g'.regs 19 = endIdx ∧
        g'.regs 23 = g.regs 23 ∧
        g'.regs 24 = g.regs 24 ∧
        g'.regs 28 = 1 ∧
        g'.regs 29 = 0 ∧
        ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  intro rem
  have hw2 : 2 ≤ w := by omega
  have hpow_b : 2 ^ quotBits w₀ n < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  induction rem with
  | zero =>
    intro cur st g s hsum hs h0 h5 h7 h19 h28 h29
    have hcur_eq : cur = endIdx := by omega
    subst hcur_eq
    have hc : ¬(Cond.lt 7 19).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 7, hs.agree.regs_lt 19, h7, h19]
    exact ⟨g, s, Exec.loop_exit hc, hs, h0, rfl, rfl, rfl, rfl, h5, rfl, rfl, rfl, rfl,
      h19, rfl, rfl, h28, h29, fun _ _ => rfl⟩
  | succ rem ih =>
    intro cur st g s hsum hs h0 h5 h7 h19 h28 h29
    have hcur_lt : cur < endIdx := by omega
    have hc : (Cond.lt 7 19).Holds s := by
      simp [Cond.Holds, hs.agree.regs_lt 7, hs.agree.regs_lt 19, h7, h19, hcur_lt]
    let dst := probeSlot (quotBits w₀ n) o cur
    let src := probeSlot (quotBits w₀ n) o (cur + 1)
    have hfit_c1 : Fits w (cur + 1) := by change cur + 1 < 2 ^ w; omega
    -- 1. probeSlotCode 5 7 9 (3 steps)
    obtain ⟨s1, e1, hs1⟩ := step_probeSlot hb_lt hs 5 7 9 o (d := cur) (by omega) h5 h7
    -- 2. reg 7 ← reg 7 + reg 28 (1 step)
    obtain ⟨e2, hs2⟩ := step_bin hs1 .add 7 7 28 (v := cur + 1)
      (by simp +decide [h7, h28]) hfit_c1
    -- 3. probeSlotCode 5 7 8 (3 steps)
    obtain ⟨s3, e3, hs3⟩ := step_probeSlot hb_lt hs2 5 7 8 o (d := cur + 1) (by omega)
      (by simp +decide [h5]) (by simp +decide)
    -- 4. readRunStartCode 8 21 (13 steps)
    obtain ⟨s4, e4, hs4⟩ := step_readRunStart hb_lt hw2 hfit_space hs3 8 21 src
      (by simp +decide [h0]) (by simp +decide [src])
    -- 5. readRemCode 8 22 (13 steps)
    obtain ⟨s5, e5, hs5⟩ := step_readRem hb_lt hw₀_pos hw hfit_space hs4 8 22 src
      (by simp +decide [h0]) (by simp +decide [src])
    -- 6. writeRunStartCode 9 21 (17 steps)
    obtain ⟨s6, e6, hs6⟩ := step_writeRunStart hb_lt hw2 hfit_space hs5 9 21 dst
      (st.isRunStart src)
      (by simp +decide [h0]) (by simp +decide [dst]) (by simp +decide)
    -- 7. writeRemCode 9 22 (17 steps)
    obtain ⟨s7, e7, hs7⟩ := step_writeRem hb_lt hw₀_pos hw hfit_space hs6 9 22 dst
      (st.remAt src)
      (by simp +decide [h0]) (by simp +decide [dst]) (by simp +decide)
    obtain ⟨g', y, hy_exec, hy_st, h0', h1', h2', h3', h4', h5', h6', h11', h15', h16',
        h19', h23', h24', h28', h29', h240'⟩ :=
      ih (cur + 1) ((st.setRunStart dst (st.isRunStart src)).setRem dst (st.remAt src)) _ s7
        (by omega) hs7
        (by simp +decide [h0])
        (by simp +decide [h5])
        (by simp +decide)
        (by simp +decide [h19])
        (by simp +decide [h28])
        (by simp +decide [h29])
    have ebody := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
    have hiter := Exec.loop_iter hc ebody hy_exec
    refine ⟨g', y, ?_, hy_st, h0', ?_, ?_, ?_, ?_, h5', ?_, ?_, ?_, ?_, h19', ?_, ?_, h28', h29',
      ?_⟩
    · simpa only [shiftLeftLoop,
        show (3 + (1 + (3 + (13 + (13 + (17 + 17)))))) + (69 * rem + 2) + 2 =
          69 * (rem + 1) + 2 by omega] using hiter
    · rw [h1']; simp +decide
    · rw [h2']; simp +decide
    · rw [h3']; simp +decide
    · rw [h4']; simp +decide
    · rw [h6']; simp +decide
    · rw [h11']; simp +decide
    · rw [h15']; simp +decide
    · rw [h16']; simp +decide
    · rw [h23']; simp +decide
    · rw [h24']; simp +decide
    · intro j hj
      rw [h240' j hj]
      have hj7 : j ≠ 7 := Fin.ne_of_val_ne (by change j.val ≠ 7; omega)
      have hj8 : j ≠ 8 := Fin.ne_of_val_ne (by change j.val ≠ 8; omega)
      have hj9 : j ≠ 9 := Fin.ne_of_val_ne (by change j.val ≠ 9; omega)
      have hj21 : j ≠ 21 := Fin.ne_of_val_ne (by change j.val ≠ 21; omega)
      have hj22 : j ≠ 22 := Fin.ne_of_val_ne (by change j.val ≠ 22; omega)
      simp [hj7, hj8, hj9, hj21, hj22]

/-- Word-RAM program performing the post-scan steps of `deleteCluster`. -/
@[expose] def deleteAfterScanCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (.op (.exactBin .add 19 15 28))
  (.seq (evalCondCode (.lt 19 17) 23)
  (.seq (probeSlotCode (quotBits w₀ n) 5 19 8)
  (.seq (readRunStartCode w w₀ n 8 21)
  (.seq (.op (.exactBin .sub 21 28 21))
  (.seq (.op (.exactBin .and 23 23 21))
  (.seq (evalCondCode (.eq 16 15) 24)
  (.seq (.op (.exactBin .sub 19 17 28))
  (.seq (.op (.copy 7 16))
  (.seq (shiftLeftLoop w w₀ n k)
  (.seq (.op (.exactBin .and 25 11 23))
  (.seq (writeOccCode w w₀ n 2 25)
  (.seq (probeSlotCode (quotBits w₀ n) 5 15 8)
  (.seq (readRunStartCode w w₀ n 8 21)
  (.seq (.op (.exactBin .and 26 23 24))
  (.seq (.op (.exactBin .or 21 21 26))
  (.seq (writeRunStartCode w w₀ n 8 21)
  (.seq (probeSlotCode (quotBits w₀ n) 5 19 8)
  (.seq (writeFullCode w w₀ n 8 29)
  (.seq (writeRunStartCode w w₀ n 8 29)
        (writeRemCode w w₀ n k 8 29))))))))))))))))))))

/-- Exact instruction count of `deleteAfterScanCode` when shifting `e - 1 - s` slots. -/
@[expose] def deleteAfterScanSteps (e s : ℕ) : ℕ :=
  69 * (e - 1 - s) + 136

theorem deleteAfterScanCode_exec {base w w₀ n k : ℕ}
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (o : Fin (2 ^ quotBits w₀ n)) {a ℓ : ℕ} (_ha_lt : a < ℓ) (hℓ_lt : ℓ < 2 ^ quotBits w₀ n)
    (r : Fin (2 ^ remBits w₀ k))
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    (hs_lt_e : calcTargetSlot st o a ℓ r < calcDeleteStop st o a ℓ)
    (he_le_ℓ : calcDeleteStop st o a ℓ ≤ ℓ)
    {mem₀ : ℕ → ℕ} {g s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (h0 : g.regs 0 = base)
    (h2 : g.regs 2 = (probeSlot (quotBits w₀ n) o a).val)
    (_h3 : g.regs 3 = r.val)
    (_h4 : g.regs 4 = a)
    (h5 : g.regs 5 = o.val)
    (h6 : g.regs 6 = ℓ)
    (h11 : g.regs 11 = (st.isOcc (probeSlot (quotBits w₀ n) o a)).toNat)
    (h15 : g.regs 15 = calcRunStart st o a ℓ)
    (h16 : g.regs 16 = calcTargetSlot st o a ℓ r)
    (h17 : g.regs 17 = calcDeleteStop st o a ℓ)
    (h28 : g.regs 28 = 1)
    (h29 : g.regs 29 = 0) :
    ∃ g' y : Data rQF,
      Exec w (deleteAfterScanCode w w₀ n k) s y
        (deleteAfterScanSteps (calcDeleteStop st o a ℓ) (calcTargetSlot st o a ℓ r)) ∧
      ClusterState base w w₀ n k mem₀ g' (deleteCluster st o a ℓ r) y ∧
      g'.regs 0 = base ∧
      g'.regs 1 = g.regs 1 ∧
      ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  have hw2 : 2 ≤ w := by omega
  have hw1 : 1 ≤ w := by omega
  have hpow_b : 2 ^ quotBits w₀ n < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hb_lt
  have hpow_1 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw1
  have hfit_bool : ∀ b : Bool, Fits w b.toNat := fun b => (Bool.toNat_lt b).trans_le hpow_1
  let q := probeSlot (quotBits w₀ n) o a
  let s₀ := calcRunStart st o a ℓ
  let s_idx := calcTargetSlot st o a ℓ r
  let e_idx := calcDeleteStop st o a ℓ
  have hs₀_le : s₀ ≤ ℓ := by
    dsimp only [s₀, calcRunStart]; exact (List.length_filter_le _ _).trans (by simp)
  have hfit_s₀1 : Fits w (s₀ + 1) := by change s₀ + 1 < 2 ^ w; omega
  have hfit_e1 : Fits w (e_idx - 1) := by change e_idx - 1 < 2 ^ w; omega
  -- 1. reg 19 ← reg 15 + reg 28 (`s₀ + 1`, 1 step)
  obtain ⟨e1, hs1⟩ := step_bin hs .add 19 15 28 (v := s₀ + 1)
    (by simp +decide [h15, h28, s₀]) hfit_s₀1
  -- 2. evalCondCode (.lt 19 17) 23 (3 steps)
  obtain ⟨e2, hs2⟩ := step_evalLt hw1 hs1 19 17 23 (va := s₀ + 1) (vb := e_idx)
    (by simp +decide) (by simp +decide [h17, e_idx])
  -- 3. probeSlotCode 5 19 8 (3 steps)
  let p_s₀1 := probeSlot (quotBits w₀ n) o (s₀ + 1)
  obtain ⟨s3, e3, hs3⟩ := step_probeSlot hb_lt hs2 5 19 8 o (d := s₀ + 1) (by omega)
    (by simp +decide [h5]) (by simp +decide)
  -- 4. readRunStartCode 8 21 (13 steps)
  obtain ⟨s4, e4, hs4⟩ := step_readRunStart hb_lt hw2 hfit_space hs3 8 21 p_s₀1
    (by simp +decide [h0]) (by simp +decide [p_s₀1])
  -- 5. reg 21 ← reg 28 - reg 21 (1 step)
  let b_not_rs1 := !st.isRunStart p_s₀1
  have hsub21 :
      BinOp.sub.evalExact
        ((g.set 19 (s₀ + 1) |>.set 23 (decide (s₀ + 1 < e_idx)).toNat
          |>.set 8 p_s₀1.val |>.set 21 (st.isRunStart p_s₀1).toNat).regs 28)
        ((g.set 19 (s₀ + 1) |>.set 23 (decide (s₀ + 1 < e_idx)).toNat
          |>.set 8 p_s₀1.val |>.set 21 (st.isRunStart p_s₀1).toNat).regs 21) =
        some b_not_rs1.toNat := by
    have hlt : (st.isRunStart p_s₀1).toNat ≤ 1 :=
      Nat.le_of_lt_succ (Bool.toNat_lt (st.isRunStart p_s₀1))
    simp +decide [BinOp.evalExact, h28, hlt, b_not_rs1, toNat_not]
  obtain ⟨e5, hs5⟩ := step_bin hs4 .sub 21 28 21 (v := b_not_rs1.toNat) hsub21 (hfit_bool _)
  -- 6. reg 23 ← reg 23 &&& reg 21 (`hasMore.toNat`, 1 step)
  let hasMore := decide (s₀ + 1 < e_idx) && b_not_rs1
  obtain ⟨e6, hs6⟩ := step_bin hs5 .and 23 23 21 (v := hasMore.toNat)
    (by simp +decide [hasMore, toNat_and]) (hfit_bool _)
  -- 7. evalCondCode (.eq 16 15) 24 (3 steps)
  let b_eq := decide (s_idx = s₀)
  obtain ⟨e7, hs7⟩ := step_evalEq hw1 hs6 16 15 24 (va := s_idx) (vb := s₀)
    (by simp +decide [h16, s_idx]) (by simp +decide [h15, s₀])
  -- 8. reg 19 ← reg 17 - reg 28 (`e_idx - 1`, 1 step)
  have hsub19 :
      BinOp.sub.evalExact
        ((g.set 19 (s₀ + 1) |>.set 23 (decide (s₀ + 1 < e_idx)).toNat
          |>.set 8 p_s₀1.val |>.set 21 (st.isRunStart p_s₀1).toNat
          |>.set 21 b_not_rs1.toNat |>.set 23 hasMore.toNat
          |>.set 24 b_eq.toNat).regs 17)
        ((g.set 19 (s₀ + 1) |>.set 23 (decide (s₀ + 1 < e_idx)).toNat
          |>.set 8 p_s₀1.val |>.set 21 (st.isRunStart p_s₀1).toNat
          |>.set 21 b_not_rs1.toNat |>.set 23 hasMore.toNat
          |>.set 24 b_eq.toNat).regs 28) = some (e_idx - 1) := by
    have he_pos : 1 ≤ e_idx := by omega
    simp +decide [BinOp.evalExact, h17, h28, he_pos, e_idx]
  obtain ⟨e8, hs8⟩ := step_bin hs7 .sub 19 17 28 (v := e_idx - 1) hsub19 hfit_e1
  -- 9. copy 7 16 (`s_idx`, 1 step)
  obtain ⟨e9, hs9⟩ := step_copy hs8 7 16 (v := s_idx) (by simp +decide [h16, s_idx])
  -- 10. shiftLeftLoop (`69 * (e_idx - 1 - s_idx) + 2` steps)
  obtain ⟨g10, s10, e10, hs10, h10_0, h10_1, h10_2, _h10_3, _h10_4, h10_5, _h10_6, h10_11,
      h10_15, _h10_16, h10_19, h10_23, h10_24, h10_28, h10_29, h10_240⟩ :=
    shiftLeftLoop_exec hb_lt hw₀_pos hw hfit_space o (e_idx - 1) (by omega)
      (e_idx - 1 - s_idx) s_idx st _ _ (by omega) hs9
      (by simp +decide [h0])
      (by simp +decide [h5])
      (by simp +decide)
      (by simp +decide)
      (by simp +decide [h28])
      (by simp +decide [h29])
  let st₁ := shiftLeft st o s_idx (e_idx - 1 - s_idx)
  have h10_2_eq : g10.regs 2 = q.val := by rw [h10_2]; simp +decide [h2, q]
  have h10_11_eq : g10.regs 11 = (st.isOcc q).toNat := by rw [h10_11]; simp +decide [h11, q]
  have h10_15_eq : g10.regs 15 = s₀ := by rw [h10_15]; simp +decide [h15, s₀]
  have h10_23_eq : g10.regs 23 = hasMore.toNat := by rw [h10_23]; simp +decide
  have h10_24_eq : g10.regs 24 = b_eq.toNat := by rw [h10_24]; simp +decide [b_eq]
  -- 11. reg 25 ← reg 11 &&& reg 23 (1 step)
  let b_occ_new := st.isOcc q && hasMore
  obtain ⟨e11, hs11⟩ := step_bin hs10 .and 25 11 23 (v := b_occ_new.toNat)
    (by simp +decide [h10_11_eq, h10_23_eq, b_occ_new, toNat_and]) (hfit_bool _)
  -- 12. writeOccCode 2 25 (17 steps)
  obtain ⟨s12, e12, hs12⟩ := step_writeOcc hb_lt hw2 hfit_space hs11 2 25 q b_occ_new
    (by simp +decide [h10_0]) (by simp +decide [h10_2_eq]) (by simp +decide)
  -- 13. probeSlotCode 5 15 8 (3 steps)
  let p₀ := probeSlot (quotBits w₀ n) o s₀
  obtain ⟨s13, e13, hs13⟩ := step_probeSlot hb_lt hs12 5 15 8 o (d := s₀) (by omega)
    (by simp +decide [h10_5]) (by simp +decide [h10_15_eq])
  -- 14. readRunStartCode 8 21 (13 steps)
  obtain ⟨s14, e14, hs14⟩ := step_readRunStart hb_lt hw2 hfit_space hs13 8 21 p₀
    (by simp +decide [h10_0]) (by simp +decide [p₀])
  -- 15. reg 26 ← reg 23 &&& reg 24 (1 step)
  let b_set_rs₀ := hasMore && b_eq
  obtain ⟨e15, hs15⟩ := step_bin hs14 .and 26 23 24 (v := b_set_rs₀.toNat)
    (by simp +decide [h10_23_eq, h10_24_eq, b_set_rs₀, toNat_and]) (hfit_bool _)
  -- 16. reg 21 ← reg 21 ||| reg 26 (1 step)
  let b_rs₀_new := (st₁.setOcc q b_occ_new).isRunStart p₀ || b_set_rs₀
  obtain ⟨e16, hs16⟩ := step_bin hs15 .or 21 21 26 (v := b_rs₀_new.toNat)
    (by simp +decide [b_rs₀_new, st₁, toNat_or]) (hfit_bool _)
  -- 17. writeRunStartCode 8 21 (17 steps)
  obtain ⟨s17, e17, hs17⟩ := step_writeRunStart hb_lt hw2 hfit_space hs16 8 21 p₀ b_rs₀_new
    (by simp +decide [h10_0]) (by simp +decide [p₀]) (by simp +decide)
  -- 18. probeSlotCode 5 19 8 (3 steps)
  let p_end := probeSlot (quotBits w₀ n) o (e_idx - 1)
  obtain ⟨s18, e18, hs18⟩ := step_probeSlot hb_lt hs17 5 19 8 o (d := e_idx - 1) (by omega)
    (by simp +decide [h10_5]) (by simp +decide [h10_19])
  -- 19. writeFullCode 8 29 (17 steps)
  obtain ⟨s19, e19, hs19⟩ := step_writeFull hb_lt hw2 hfit_space hs18 8 29 p_end false
    (by simp +decide [h10_0]) (by simp +decide [p_end]) (by simp +decide [h10_29])
  -- 20. writeRunStartCode 8 29 (17 steps)
  obtain ⟨s20, e20, hs20⟩ := step_writeRunStart hb_lt hw2 hfit_space hs19 8 29 p_end false
    (by simp +decide [h10_0]) (by simp +decide [p_end]) (by simp +decide [h10_29])
  -- 21. writeRemCode 8 29 (17 steps)
  obtain ⟨s21, e21, hs21⟩ := step_writeRem hb_lt hw₀_pos hw hfit_space hs20 8 29 p_end
    ⟨0, Nat.two_pow_pos (remBits w₀ k)⟩
    (by simp +decide [h10_0]) (by simp +decide [p_end]) (by simp +decide [h10_29])
  have hst₂_eq :
      (st₁.setOcc q b_occ_new).setRunStart p₀ b_rs₀_new =
        (if !hasMore then st₁.setOcc q false
         else if s_idx = s₀ then st₁.setRunStart p₀ true
         else st₁) := by
    have hocc_st₁ : st₁.isOcc q = st.isOcc q := by simp [st₁]
    dsimp only [b_occ_new, b_rs₀_new, b_set_rs₀, b_eq]
    rw [← hocc_st₁]
    cases hmore : hasMore
    · have : (st₁.setOcc q false).setRunStart p₀ (st₁.isRunStart p₀) = st₁.setOcc q false := by
        cases st₁; simp [FilterState.setOcc, FilterState.setRunStart]
      simpa using this
    · by_cases heq : s_idx = s₀
      · simp [heq, FilterState.setOcc_self]
      · simp [heq, FilterState.setOcc_self, FilterState.setRunStart_self]
  have hst_final :
      ((((st₁.setOcc q b_occ_new).setRunStart p₀ b_rs₀_new).setFull p_end false).setRunStart
        p_end false).setRem p_end ⟨0, Nat.two_pow_pos (remBits w₀ k)⟩ =
        deleteCluster st o a ℓ r := by
    rw [hst₂_eq]
    rfl
  rw [hst_final] at hs21
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
    (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq (e16.seq (e17.seq (e18.seq (e19.seq
    (e20.seq e21)))))))))))))))))))
  refine ⟨_, s21, ?_, hs21, ?_, ?_, ?_⟩
  · simpa only [deleteAfterScanCode, deleteAfterScanSteps,
      show 1 + (3 + (3 + (13 + (1 + (1 + (3 + (1 + (1 + ((69 * (e_idx - 1 - s_idx) + 2) +
        (1 + (17 + (3 + (13 + (1 + (1 + (17 + (3 + (17 + (17 + 17))))))))))))))))))) =
        69 * (e_idx - 1 - s_idx) + 136 by omega] using hall
  · simp +decide [h10_0]
  · simp +decide [h10_1]
  · intro j hj
    have hj8 : j ≠ 8 := Fin.ne_of_val_ne (by change j.val ≠ 8; omega)
    have hj7 : j ≠ 7 := Fin.ne_of_val_ne (by change j.val ≠ 7; omega)
    have hj19 : j ≠ 19 := Fin.ne_of_val_ne (by change j.val ≠ 19; omega)
    have hj21 : j ≠ 21 := Fin.ne_of_val_ne (by change j.val ≠ 21; omega)
    have hj23 : j ≠ 23 := Fin.ne_of_val_ne (by change j.val ≠ 23; omega)
    have hj24 : j ≠ 24 := Fin.ne_of_val_ne (by change j.val ≠ 24; omega)
    have hj25 : j ≠ 25 := Fin.ne_of_val_ne (by change j.val ≠ 25; omega)
    have hj26 : j ≠ 26 := Fin.ne_of_val_ne (by change j.val ≠ 26; omega)
    simp only [Data.set_regs, Function.update_of_ne hj8, Function.update_of_ne hj21,
      Function.update_of_ne hj26, Function.update_of_ne hj25]
    rw [h10_240 j hj]
    simp [hj7, hj8, hj19, hj21, hj23, hj24]

/-- Complete Word-RAM cluster query program: locates the maximal full cluster around `q` (`reg 2`),
scans it for remainder `r` (`reg 3`), and copies the `0`/`1` answer into `reg 1`. -/
@[expose] def queryClusterCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (findClusterCode w w₀ n)
  (.seq (scanClusterCode w w₀ n k)
        (.op (.copy 1 18)))

/-- Complete Word-RAM cluster insertion program: locates the maximal full cluster around `q`
(`reg 2`), scans it for remainder `r` (`reg 3`), and inserts `r` in canonical run order. -/
@[expose] def insertClusterCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (findClusterCode w w₀ n)
  (.seq (scanClusterCode w w₀ n k)
        (insertAfterScanCode w w₀ n k))

/-- Complete Word-RAM cluster deletion program: locates the maximal full cluster around `q`
(`reg 2`), scans it for remainder `r` (`reg 3`), and deletes one copy of `r` in canonical run
order. -/
@[expose] def deleteClusterCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (findClusterCode w w₀ n)
  (.seq (scanClusterCode w w₀ n k)
        (deleteAfterScanCode w w₀ n k))

theorem FilterInv.queryClusterCode_exec {U base w w₀ n k : ℕ}
    {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)}
    {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    (hinv : FilterInv n S quot rem st)
    (hS_lt : #S < 2 ^ quotBits w₀ n)
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (u : Fin U)
    {mem₀ : ℕ → ℕ} {g s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (h0 : g.regs 0 = base)
    (h2 : g.regs 2 = (quot u).val)
    (h3 : g.regs 3 = (rem u).val) :
    let a := hinv.backLen hS_lt (quot u)
    let t := hinv.fwdLen hS_lt (quot u)
    let ℓ := hinv.clusterLen hS_lt (quot u)
    ∃ g' y : Data rQF,
      Exec w (queryClusterCode w w₀ n k) s y
        (findClusterSteps a t + (scanClusterSteps a ℓ + 1)) ∧
      ClusterState base w w₀ n k mem₀ g' st y ∧
      g'.regs 0 = base ∧
      g'.regs 1 = (decide (rem u ∈ bucketRun S quot rem (quot u))).toNat ∧
      ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  intro a t ℓ
  have hw2 : 2 ≤ w := by omega
  let q := quot u
  let r := rem u
  let o := hinv.clusterStart hS_lt q
  have hℓ_lt : ℓ < 2 ^ quotBits w₀ n :=
    lt_of_le_of_lt (hinv.clusterLen_le_card hS_lt q) hS_lt
  have ha_le : a ≤ ℓ := Nat.le_add_right a t
  have hq_probe : q = probeSlot (quotBits w₀ n) o a := by
    dsimp only [o, FilterInv.clusterStart]
    have h1 := probeSlot_backSlot_add q a 0
    rw [add_zero, probeSlot_zero] at h1
    exact h1.symm
  obtain ⟨g1, s1, e1, hs1, h1_0, _h1_1, h1_2, h1_3, h1_4, h1_5, h1_6, h1_28, h1_29, h1_240⟩ :=
    findClusterCode_exec hb_lt hw2 hfit_space (quot u) hℓ_lt
      (fun d hd => hinv.isFull_backSlot_of_le_backLen hS_lt (quot u)
        (Nat.succ_pos d) (Nat.succ_le_of_lt hd))
      (hinv.isFull_backSlot_succ_backLen hS_lt (quot u))
      (fun d hd => hinv.isFull_probeSlot_of_lt_fwdLen hS_lt (quot u) hd)
      (hinv.isFull_probeSlot_fwdLen hS_lt (quot u))
      hs h0 h2
  have h1_2_probe : g1.regs 2 = (probeSlot (quotBits w₀ n) o a).val := by
    rw [h1_2, ← hq_probe]
  have h1_3_eq : g1.regs 3 = r.val := by rw [h1_3, h3]
  obtain ⟨g2, s2, e2, hs2, h2_0, _h2_1, _h2_2, _h2_3, _h2_4, _h2_5, _h2_6, _h2_11,
      _h2_15, _h2_16, _h2_17, h2_18, _h2_28, _h2_29, h2_240⟩ :=
    scanClusterCode_exec hb_lt hw₀_pos hw hfit_space o ha_le hℓ_lt r
      hs1 h1_0 h1_2_probe h1_3_eq h1_4 h1_5 h1_6 h1_28 h1_29
  have hq_eq :
      queryCluster st o a ℓ r = decide (r ∈ bucketRun S quot rem q) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    exact (hinv.querySlot_eq_true_iff hS_lt u).trans (mem_bucketRun_iff S quot rem q r).symm
  rw [hq_eq] at h2_18
  obtain ⟨e3, hs3⟩ := step_copy hs2 1 18
    (v := (decide (r ∈ bucketRun S quot rem q)).toNat) h2_18
  refine ⟨_, _, e1.seq (e2.seq e3), hs3, ?_, ?_, ?_⟩
  · simp +decide [h2_0]
  · simp +decide [q, r]
  · intro j hj
    have hj1 : j ≠ 1 := Fin.ne_of_val_ne (by change j.val ≠ 1; omega)
    simp only [Data.set_regs, Function.update_of_ne hj1]
    rw [h2_240 j hj, h1_240 j hj]

theorem FilterInv.insertClusterCode_exec {U base w w₀ n k : ℕ}
    {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)}
    {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    (hinv : FilterInv n S quot rem st)
    (hS_lt : #S < 2 ^ quotBits w₀ n)
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (u : Fin U)
    {mem₀ : ℕ → ℕ} {g s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (h0 : g.regs 0 = base)
    (h2 : g.regs 2 = (quot u).val)
    (h3 : g.regs 3 = (rem u).val) :
    let a := hinv.backLen hS_lt (quot u)
    let t := hinv.fwdLen hS_lt (quot u)
    let o := hinv.clusterStart hS_lt (quot u)
    let ℓ := hinv.clusterLen hS_lt (quot u)
    let s_idx := calcTargetSlot st o a ℓ (rem u)
    ∃ g' y : Data rQF,
      Exec w (insertClusterCode w w₀ n k) s y
        (findClusterSteps a t + (scanClusterSteps a ℓ + insertAfterScanSteps ℓ s_idx)) ∧
      ClusterState base w w₀ n k mem₀ g' (hinv.insertState hS_lt u) y ∧
      g'.regs 0 = base ∧
      g'.regs 1 = g.regs 1 ∧
      ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  intro a t o ℓ s_idx
  have hw2 : 2 ≤ w := by omega
  let q := quot u
  let r := rem u
  have hℓ_lt : ℓ < 2 ^ quotBits w₀ n :=
    lt_of_le_of_lt (hinv.clusterLen_le_card hS_lt q) hS_lt
  have ha_le : a ≤ ℓ := Nat.le_add_right a t
  have hq_probe : q = probeSlot (quotBits w₀ n) o a := by
    dsimp only [o, FilterInv.clusterStart]
    have h1 := probeSlot_backSlot_add q a 0
    rw [add_zero, probeSlot_zero] at h1
    exact h1.symm
  obtain ⟨g1, s1, e1, hs1, h1_0, h1_1, h1_2, h1_3, h1_4, h1_5, h1_6, h1_28, h1_29, h1_240⟩ :=
    findClusterCode_exec hb_lt hw2 hfit_space (quot u) hℓ_lt
      (fun d hd => hinv.isFull_backSlot_of_le_backLen hS_lt (quot u)
        (Nat.succ_pos d) (Nat.succ_le_of_lt hd))
      (hinv.isFull_backSlot_succ_backLen hS_lt (quot u))
      (fun d hd => hinv.isFull_probeSlot_of_lt_fwdLen hS_lt (quot u) hd)
      (hinv.isFull_probeSlot_fwdLen hS_lt (quot u))
      hs h0 h2
  have h1_2_probe : g1.regs 2 = (probeSlot (quotBits w₀ n) o a).val := by
    rw [h1_2, ← hq_probe]
  have h1_3_eq : g1.regs 3 = r.val := by rw [h1_3, h3]
  obtain ⟨g2, s2, e2, hs2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_11,
      h2_15, h2_16, _h2_17, _h2_18, h2_28, h2_29, h2_240⟩ :=
    scanClusterCode_exec hb_lt hw₀_pos hw hfit_space o ha_le hℓ_lt r
      hs1 h1_0 h1_2_probe h1_3_eq h1_4 h1_5 h1_6 h1_28 h1_29
  obtain ⟨g3, s3, e3, hs3, h3_0, h3_1, h3_240⟩ :=
    insertAfterScanCode_exec hb_lt hw₀_pos hw hfit_space o ha_le hℓ_lt r
      hs2 h2_0 h2_2 h2_3 h2_4 h2_5 h2_6 h2_11 h2_15 h2_16 h2_28 h2_29
  refine ⟨g3, s3, e1.seq (e2.seq e3), hs3, h3_0, ?_, ?_⟩
  · rw [h3_1, h2_1, h1_1]
  · intro j hj
    rw [h3_240 j hj, h2_240 j hj, h1_240 j hj]

theorem FilterInv.deleteClusterCode_exec {U base w w₀ n k : ℕ}
    {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)}
    {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    {st : FilterState (quotBits w₀ n) (remBits w₀ k)}
    (hinv : FilterInv n S quot rem st)
    (hS_lt : #S < 2 ^ quotBits w₀ n)
    (hb_lt : quotBits w₀ n < w) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {u : Fin U} (hu : u ∈ S)
    {mem₀ : ℕ → ℕ} {g s : Data rQF}
    (hs : ClusterState base w w₀ n k mem₀ g st s)
    (h0 : g.regs 0 = base)
    (h2 : g.regs 2 = (quot u).val)
    (h3 : g.regs 3 = (rem u).val) :
    let a := hinv.backLen hS_lt (quot u)
    let t := hinv.fwdLen hS_lt (quot u)
    let o := hinv.clusterStart hS_lt (quot u)
    let ℓ := hinv.clusterLen hS_lt (quot u)
    let s_idx := calcTargetSlot st o a ℓ (rem u)
    let e_idx := calcDeleteStop st o a ℓ
    ∃ g' y : Data rQF,
      Exec w (deleteClusterCode w w₀ n k) s y
        (findClusterSteps a t + (scanClusterSteps a ℓ + deleteAfterScanSteps e_idx s_idx)) ∧
      ClusterState base w w₀ n k mem₀ g' (hinv.deleteState hS_lt u) y ∧
      g'.regs 0 = base ∧
      g'.regs 1 = g.regs 1 ∧
      ∀ j : Fin rQF, 240 ≤ j.val → g'.regs j = g.regs j := by
  intro a t o ℓ s_idx e_idx
  have hw2 : 2 ≤ w := by omega
  let q := quot u
  let r := rem u
  have hℓ_lt : ℓ < 2 ^ quotBits w₀ n :=
    lt_of_le_of_lt (hinv.clusterLen_le_card hS_lt q) hS_lt
  have hq_probe : q = probeSlot (quotBits w₀ n) o a := by
    dsimp only [o, FilterInv.clusterStart]
    have h1 := probeSlot_backSlot_add q a 0
    rw [add_zero, probeSlot_zero] at h1
    exact h1.symm
  have ha_lt : a < ℓ := by
    have hr_mem : r ∈ bucketRun S quot rem q :=
      (mem_bucketRun_iff S quot rem q r).mpr ⟨u, hu, rfl, rfl⟩
    have hocc_q : st.isOcc q = true := by
      rw [hinv.isOcc_eq q]
      cases h : bucketRun S quot rem q with
      | nil => simp [h] at hr_mem
      | cons _ _ => rfl
    have hfull_q : st.isFull q = true := by
      cases h : st.isFull q
      · have := (hinv.empty_slot q h).1
        rw [hocc_q] at this
        cases this
      · rfl
    have ht_pos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with ht0 | hpos
      · have h1 := hinv.isFull_probeSlot_fwdLen hS_lt q
        change st.isFull (probeSlot (quotBits w₀ n) q t) = false at h1
        rw [ht0, probeSlot_zero, hfull_q] at h1
        cases h1
      · exact hpos
    change a < a + t
    omega
  have hvalid₀ : IntervalValid S quot rem st o ℓ := hinv.intervalValid_cluster hS_lt q
  obtain ⟨_ha_lt_e, he_le_ℓ, he_run, _⟩ := hvalid₀.calcDeleteStop_spec hinv.isOcc_eq ha_lt
  have hs_lt_e : s_idx < e_idx := by
    have hs_eq := hvalid₀.calcTargetSlot_eq hinv.isOcc_eq ha_lt (rem u)
    have hr_mem : rem u ∈ bucketRun S quot rem (probeSlot (quotBits w₀ n) o a) :=
      (mem_bucketRun_iff S quot rem _ (rem u)).mpr ⟨u, hu, hq_probe, rfl⟩
    have hpw := pairwise_le_bucketRun S quot rem (probeSlot (quotBits w₀ n) o a)
    have her := erase_eq_take_append_drop_of_pairwise hpw hr_mem
    have hcnt_lt :
        (bucketRun S quot rem (probeSlot (quotBits w₀ n) o a)).countP (· < rem u) <
          (bucketRun S quot rem (probeSlot (quotBits w₀ n) o a)).length := by
      by_contra! hge
      have h1 := congrArg List.length her
      simp only [List.length_erase_of_mem hr_mem, List.length_append, List.length_take,
        List.length_drop] at h1
      have hpos : 0 < (bucketRun S quot rem (probeSlot (quotBits w₀ n) o a)).length :=
        List.length_pos_iff.mpr (List.ne_nil_of_mem hr_mem)
      omega
    have hrun_a1 :
        runOffset S quot rem o (a + 1) =
          runOffset S quot rem o a +
            (bucketRun S quot rem (probeSlot (quotBits w₀ n) o a)).length :=
      runOffset_succ S quot rem o a
    have hrun_le_e : runOffset S quot rem o (a + 1) ≤ calcDeleteStop st o a ℓ := by
      rw [← he_run]
      exact runOffset_mono S quot rem o (by omega)
    dsimp only [s_idx, e_idx]
    omega
  obtain ⟨g1, s1, e1, hs1, h1_0, h1_1, h1_2, h1_3, h1_4, h1_5, h1_6, h1_28, h1_29, h1_240⟩ :=
    findClusterCode_exec hb_lt hw2 hfit_space (quot u) hℓ_lt
      (fun d hd => hinv.isFull_backSlot_of_le_backLen hS_lt (quot u)
        (Nat.succ_pos d) (Nat.succ_le_of_lt hd))
      (hinv.isFull_backSlot_succ_backLen hS_lt (quot u))
      (fun d hd => hinv.isFull_probeSlot_of_lt_fwdLen hS_lt (quot u) hd)
      (hinv.isFull_probeSlot_fwdLen hS_lt (quot u))
      hs h0 h2
  have h1_2_probe : g1.regs 2 = (probeSlot (quotBits w₀ n) o a).val := by
    rw [h1_2, ← hq_probe]
  have h1_3_eq : g1.regs 3 = r.val := by rw [h1_3, h3]
  obtain ⟨g2, s2, e2, hs2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_11,
      h2_15, h2_16, h2_17, _h2_18, h2_28, h2_29, h2_240⟩ :=
    scanClusterCode_exec hb_lt hw₀_pos hw hfit_space o ha_lt.le hℓ_lt r
      hs1 h1_0 h1_2_probe h1_3_eq h1_4 h1_5 h1_6 h1_28 h1_29
  obtain ⟨g3, s3, e3, hs3, h3_0, h3_1, h3_240⟩ :=
    deleteAfterScanCode_exec hb_lt hw₀_pos hw hfit_space o ha_lt hℓ_lt r hs_lt_e he_le_ℓ
      hs2 h2_0 h2_2 h2_3 h2_4 h2_5 h2_6 h2_11 h2_15 h2_16 h2_17 h2_28 h2_29
  refine ⟨g3, s3, e1.seq (e2.seq e3), hs3, h3_0, ?_, ?_⟩
  · rw [h3_1, h2_1, h1_1]
  · intro j hj
    rw [h3_240 j hj, h2_240 j hj, h1_240 j hj]

end Cslib.DataStructure.ApproximateMembership.WordRAM.QuotientFilter
