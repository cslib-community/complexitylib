/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Recursive
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Root
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Report

/-!
# Complete native root evaluation and ordered reporting

## Main results

* `PrunedQuery.exec_evaluate`: actual root deduplication, all-depth native traversal and ordered
  reporting, allowing duplicate input queries and arbitrary original memory outside the workspace.

The query function specifies the words of the supplied input list. The machine computes its own
distinct set, every recursive child list and every reported index. All scratch addresses, signed
fits, fresh generations and instruction charges follow from the ordinary numerical premises.
This module is an internal implementation API used to prove the initialized and pointer-based
client interfaces in `Pruned.Flat`, `Pruned.Width` and `Pruned.Kernel`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Evaluate the actual supplied queries after workspace pointers have been computed. The result
uses the existing finite request-set semantics; no initialized directory or traversal certificate
is supplied. Only the original source cells and an upper bound on old timestamps are required. -/
theorem exec_evaluate {w L f a0 b0 q0 o0 Q E A B : ℕ}
    (a b : Leaf L → ℤ) (qs : Fin Q → OutStr L) (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hQ : x.regs queryCount = Q)
    (hq0 : x.regs queries = q0) (ho0 : x.regs output = o0) (hE : x.regs epoch = E)
    (hinput : ∀ i, x.mem (q0 + i.val) = (queryIndex (qs i)).val)
    (hleft : ∀ v, x.mem (a0 + (Encoding.leafIndex v).val) = encode (a v))
    (hright : ∀ v, x.mem (b0 + (Encoding.leafIndex v).val) = encode (b v))
    (hbeforeA : a0 + 10 ^ L ≤ f) (hbeforeB : b0 + 10 ^ L ≤ f)
    (hqueryOut : q0 + Q ≤ o0) (houtFrame : o0 + Q ≤ f)
    (hmarks : ∀ q < 10 ^ L,
      x.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ E)
    (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hw : 0 < w) (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (evaluationBudget L f a0 b0 q0 o0 Q E)) :
    ∃ y, ExecWithin (w + 2) (ram[ ⟪rootList⟫; ⟪controller⟫; ⟪report⟫ ]) x y
        (29 * Q + traceWeight (Finset.univ.image qs) + 24) ∧
      (∀ i, y.mem (o0 + i.val) = encode
        (Pruned.result L a b (Finset.univ.image qs) (qs i))) ∧
      (∀ c, ¬(o0 ≤ c ∧ c < o0 + Q) →
        ¬(f ≤ c ∧ c < f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + 10 ^ L) →
          y.mem c = x.mem c) ∧ y.regs output = o0 ∧
      E + 1 ≤ y.regs epoch ∧ y.regs epoch ≤ E + 1 + epochAllowance L ∧
      (∀ q < 10 ^ L,
        y.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ y.regs epoch) := by
  let S : Finset (OutStr L) := Finset.univ.image qs
  let codes := fun i => if hi : i < Q then (queryIndex (qs ⟨i, hi⟩)).val else 0
  have himage : (Finset.range Q).image codes = S.image (fun v => (queryIndex v).val) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_range, S, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, he⟩
      exact ⟨qs ⟨i, hi⟩, ⟨⟨i, hi⟩, rfl⟩, by simpa only [codes, dite_eq_left hi] using he⟩
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.val, i.isLt, by simp only [codes, dite_eq_left i.isLt]⟩
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  have hcodes (i : ℕ) (hi : i < Q) : codes i < 10 ^ L := by
    simpa only [codes, dite_eq_left hi] using (queryIndex (qs ⟨i, hi⟩)).isLt
  obtain ⟨u, hroot, hul, hum, hua, hue, hur, huc, hup, hus, hut, _, hrootFrame, _⟩ :=
    exec_rootList (N := Q) (capacity := 10 ^ L) x codes hQ
      (fun i hi => by simpa only [hq0, codes, dite_eq_left hi] using hinput ⟨i, hi⟩) hcodes
      (by rw [hregs.lists_eq, hregs.stamps_eq]; nlinarith only [hpow])
      (by rw [hq0, hregs.lists_eq]; omega)
      (by rw [hregs.frames_eq, hregs.lists_eq]; omega)
      (by rw [hq0, hregs.frames_eq]; omega)
      (by simpa only [hregs.stamps_eq, hE] using hmarks)
      hregs.nil_eq hregs.one_eq hregs.ten_eq hregs.nine_eq
      (hfit.of_le (by
        rw [hq0, hregs.lists_eq, hregs.stamps_eq, hE, hregs.frames_eq]
        unfold evaluationBudget nodeBudget
        nlinarith only [hpow, hL]))
  have huregs : KernelRegs L f a0 b0 u := by
    constructor
    · exact (hroot.regs_eq (by decide : rootList.Preserves inputDepth)).trans hregs.depth_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves span)).trans hregs.span_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves arrayA)).trans hregs.left_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves arrayB)).trans hregs.right_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves frames)).trans hregs.frames_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves lists)).trans hregs.lists_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves values)).trans hregs.values_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves stamps)).trans hregs.stamps_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves nil)).trans hregs.nil_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves one)).trans hregs.one_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves ten)).trans hregs.ten_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves nine)).trans hregs.nine_eq
    · exact (hroot.regs_eq (by decide : rootList.Preserves frameWidth)).trans hregs.frameWidth_eq
  have hu : NodeReady L f a0 b0 L 0 0 (E + 1) S u := by
    refine ⟨huregs, by omega, by simp, hul, hum, hua, ?_, ?_, ?_⟩
    · simpa only [hE] using hue
    · intro j
      change u.mem (f + 4 * 0 + j.val) = ![S.card, 0, 10 ^ 0, 0] j
      fin_cases j
      · change u.mem (f) = S.card
        simpa only [hregs.frames_eq, himage, card_image_queryIndex] using huc
      · change u.mem (f + 1) = 0
        simpa only [hregs.frames_eq] using hup
      · change u.mem (f + 2) = 1
        simpa only [hregs.frames_eq] using hus
      · change u.mem (f + 3) = 0
        simpa only [hregs.frames_eq] using hut
    · simpa only [hregs.lists_eq, hregs.stamps_eq, hE, himage, Nat.zero_mul, Nat.add_zero]
        using hur
  have hrootBefore (c : ℕ) (hc : c < f) : u.mem c = x.mem c := by
    apply hrootFrame c
    all_goals simp only [hregs.lists_eq, hregs.stamps_eq, hregs.frames_eq, Block.Owns]
    all_goals omega
  have hsourceA (v : Leaf L) : u.mem (a0 + 0 + 10 ^ 0 * (Encoding.leafIndex v).val) =
      encode (a v) := by
    simp only [Nat.add_zero, pow_zero, Nat.one_mul]
    rw [hrootBefore _ (by have := (Encoding.leafIndex v).isLt; omega)]
    exact hleft v
  have hsourceB (v : Leaf L) : u.mem (b0 + 0 + 10 ^ 0 * (Encoding.leafIndex v).val) =
      encode (b v) := by
    simp only [Nat.add_zero, pow_zero, Nat.one_mul]
    rw [hrootBefore _ (by have := (Encoding.leafIndex v).isLt; omega)]
    exact hright v
  obtain ⟨v, hv, hcontroller⟩ := exec_ready L S a b u hu hsourceA hsourceB hbeforeA hbeforeB
    ha hb hw hmag (hfit.of_le (by unfold evaluationBudget; omega))
  have hexit : ExecWithin (w + 2) controller v v 2 := ExecWithin.loop_exit
    (by simp only [Cond.holds_lt, hv.regs.nil_eq, hv.active_eq]; decide)
  have hloop := hcontroller v 2 hexit
  have hqv : v.regs queries = q0 :=
    (hloop.regs_eq (by decide : controller.Preserves queries)).trans
      ((hroot.regs_eq (by decide : rootList.Preserves queries)).trans hq0)
  have hov : v.regs output = o0 :=
    (hloop.regs_eq (by decide : controller.Preserves output)).trans
      ((hroot.regs_eq (by decide : rootList.Preserves output)).trans ho0)
  have hQv : v.regs queryCount = Q :=
    (hloop.regs_eq (by decide : controller.Preserves queryCount)).trans
      ((hroot.regs_eq (by decide : rootList.Preserves queryCount)).trans hQ)
  have hquery (i : ℕ) (hi : i < Q) : v.mem (v.regs queries + i) = codes i := by
    rw [hqv, hv.frame _ (notMem_nodeWrites_before (Nat.zero_le _) (by omega)),
      hrootBefore _ (by omega)]
    simpa only [codes, dite_eq_left hi] using hinput ⟨i, hi⟩
  obtain ⟨y, hreport, _, hvalues, hreportFrame, _⟩ := exec_report (N := Q)
    (capacity := 10 ^ L) v codes hQv hquery hcodes (Or.inl (by rw [hqv, hov]; omega))
    (Or.inr (by rw [hov, hv.regs.values_eq]; omega)) hv.regs.one_eq
    (hfit.of_le (by
      rw [hqv, hov, hv.regs.values_eq]
      unfold evaluationBudget nodeBudget
      nlinarith only [hpow, hL]))
  have he : ExecWithin (w + 2) (ram[ ⟪rootList⟫; ⟪controller⟫; ⟪report⟫ ]) x y
      (29 * Q + traceWeight S + 24) := (hroot.seq (hloop.seq hreport)).mono (by omega)
  refine ⟨y, he, ?_, ?_, (hreport.regs_eq (by decide : report.Preserves output)).trans hov,
    ?_, ?_, ?_⟩
  · intro i
    have hr := hvalues i.val i.isLt
    rw [hov, hv.regs.values_eq] at hr
    have hqi : codes i.val = (queryIndex (qs i)).val := by
      simp only [codes, dite_eq_left i.isLt]
    rw [hqi] at hr
    have hval := hv.values (qs i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    simp only [Nat.zero_mul, Nat.add_zero] at hval
    exact hr.trans hval
  · intro c hout hscratch
    have htwo : 2 * (L + 1) * 10 ^ L = (L + 1) * 10 ^ L + (L + 1) * 10 ^ L := by ring
    rw [htwo] at hscratch
    have hcap : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
    rw [hreportFrame c (by simpa only [hov, Block.mem_footprint, Block.Owns] using hout)]
    have hnot : c ∉ nodeWrites L f 0 := by
      rw [mem_nodeWrites_iff (Nat.zero_le _)]
      simp only [Nat.zero_mul, Nat.add_zero, htwo]
      omega
    rw [hv.frame c hnot]
    apply hrootFrame c
    all_goals simp only [hregs.lists_eq, hregs.stamps_eq, hregs.frames_eq, Block.Owns, htwo]
    all_goals omega
  · rw [hreport.regs_eq (by decide : report.Preserves epoch)]
    exact hv.epoch_le
  · rw [hreport.regs_eq (by decide : report.Preserves epoch)]
    exact hv.epoch_upper
  · intro q hq
    rw [hreportFrame _ (by
      rw [Block.mem_footprint]
      simp only [hov, Block.Owns]
      omega), hreport.regs_eq (by decide : report.Preserves epoch)]
    exact hv.timestamps q hq

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
