/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.InputSpec

/-!
# Complete record-to-original-input preparation

All runtime metadata is read by the real descriptor code. The logarithm, five original-header
stores and three native array copies compose to linear preparation work. The readback premises
here are internal; the producer client derives them from the actual prepared instance.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

-- The finite preservation test traverses the relocated 320-register code.
set_option maxRecDepth 4096 in
/-- `readRecord` preserves the 64-register producer bank and the ordinal register `64`. -/
theorem read_preserves : ∀ i : Fin 320, i.val < 65 → readRecord.Preserves i := by decide

/-- Execute the shared `readRecord → logarithm → writeHeader` prefix before a continuation
`tail`, returning the five-word header state, preserved pointers, memory frame outside
`[b, b + 5)`, and producer-bank register frame. -/
theorem exec_readLogHeader {W b m n i out rho piece s t q Q : ℕ} (x : Data 320)
    (hD : x.mem 1 = D m) (hn : x.mem 3 = n)
    (hi : x.regs Reg.ordinal = i) (hout : x.regs 39 = out) (hb : x.regs 42 = b)
    (hrec : out + i * (6 + 2 * (n * D m)) + 6 ≤ b)
    (hrecord : (Block.mk (out + i * (6 + 2 * (n * D m))) 6).Realizes x.mem
      ![rho, piece, q, Q, s, t])
    (hfit : Fits W (2 * b + 2 * (n * D m) + 2 * Q + 20 * m + D m + n + 256)) :
    ∃ h,
      (∀ {tail y T}, ExecWithin W tail h y T →
        ExecWithin W (.seq readRecord (.seq logarithm (.seq writeHeader tail))) x y
          (8 * m + 48 + T)) ∧
      (Block.mk b 5).Realizes h.mem ![4 + 2 * (n * D m) + 2 * Q, 19 * m, m, n, Q] ∧
      h.regs Reg.base = b ∧ h.regs Reg.area = n * D m ∧ h.regs Reg.count = Q ∧
      h.regs Reg.left = s ∧ h.regs Reg.right = t ∧ h.regs Reg.queries = q ∧
      (∀ a, a < b ∨ b + 5 ≤ a → h.mem a = x.mem a) ∧
      ∀ j : Fin 320, j.val < 65 → h.regs j = x.regs j := by
  obtain ⟨r, hr, rm, _, rn, rA, rAA, rb, _, _, _, rq, rQ, rs, rt,
    rarg, r1, r2, r19, r4⟩ := exec_readRecord x ![rho, piece, q, Q, s, t]
      hD hn hi hout hb hrec hrecord (hfit.of_le (by omega))
  have rq' : r.regs Reg.queries = q := by simpa +decide using rq
  have rQ' : r.regs Reg.count = Q := by simpa +decide using rQ
  have rs' : r.regs Reg.left = s := by simpa +decide using rs
  have rt' : r.regs Reg.right = t := by simpa +decide using rt
  obtain ⟨l, hl, lmDepth, lm, lr⟩ := exec_logarithm r rarg (hfit.of_le (by
    change D m + 2 * m + 3 ≤ _
    omega))
  have lb : l.regs Reg.base = b := (lr _ (by decide)).trans rb
  obtain ⟨h, hh, hhead, hframe, hregs⟩ := exec_writeHeader l lb lmDepth
    ((lr _ (by decide)).trans rAA) ((lr _ (by decide)).trans rQ')
    ((lr _ (by decide)).trans rn) ((lr _ (by decide)).trans r1)
    ((lr _ (by decide)).trans r2) ((lr _ (by decide)).trans r19)
    ((lr _ (by decide)).trans r4) (hfit.of_le (by omega))
  refine ⟨h, fun hy => (hr.seq (hl.seq (hh.seq hy))).mono (by omega), hhead,
    (hregs _ (by decide)).trans lb,
    (hregs _ (by decide)).trans ((lr _ (by decide)).trans rA),
    (hregs _ (by decide)).trans ((lr _ (by decide)).trans rQ'),
    (hregs _ (by decide)).trans ((lr _ (by decide)).trans rs'),
    (hregs _ (by decide)).trans ((lr _ (by decide)).trans rt'),
    (hregs _ (by decide)).trans ((lr _ (by decide)).trans rq'),
    fun a ha => (hframe a ha).trans ((congrFun lm a).trans (congrFun rm a)),
    fun j hj => (hregs _ (by omega)).trans
      ((lr _ (Or.inl (by omega))).trans (hr.regs_eq (read_preserves j hj)))⟩

/-- Complete native preparation from a selected record and its actual three source spans.
No source execution, encoded matrix or routing table is supplied. -/
theorem exec_prepare {W b m n i out rho piece s t q : ℕ}
    (X : Matrix (Fin n) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin n) ℤ)
    (qs : List (Fin n × Fin n)) (x : Data 320)
    (hD : x.mem 1 = D m) (hn : x.mem 3 = n)
    (hi : x.regs Reg.ordinal = i) (hout : x.regs 39 = out) (hb : x.regs 42 = b)
    (hrec : out + i * (6 + 2 * (n * D m)) + 6 ≤ b)
    (hrecord : (Block.mk (out + i * (6 + 2 * (n * D m))) 6).Realizes x.mem
      ![rho, piece, q, qs.length, s, t])
    (hsb : s + n * D m ≤ b) (htb : t + n * D m ≤ b)
    (hqb : q + 2 * qs.length ≤ b)
    (hleft : ∀ a < n * D m, x.mem (s + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem (5 + a))
    (hright : ∀ a < n * D m, x.mem (t + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
        (5 + n * D m + a))
    (hqueries : ∀ a < 2 * qs.length, x.mem (q + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
        (5 + 2 * (n * D m) + a))
    (hfit : Fits W (2 * b + 2 * (n * D m) + 2 * qs.length + 20 * m + D m + n + 256)) :
    ∃ y, ExecWithin W prepare x y (8 * m + 14 * (n * D m) + 14 * qs.length + 69) ∧
      y.regs Reg.base = b ∧
      (∀ a, a < QueriedProduct.inputEnd m n qs.length → y.mem (b + a) =
        (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a) ∧
      (∀ a, a < b ∨ b + QueriedProduct.inputEnd m n qs.length ≤ a → y.mem a = x.mem a) ∧
      ∀ j : Fin 320, j.val < 65 → y.regs j = x.regs j := by
  obtain ⟨h, hrun, hhead, hb', hA, hQ, hs, ht, hq, hframe, hregs⟩ :=
    exec_readLogHeader x hD hn hi hout hb hrec hrecord hfit
  obtain ⟨y, hy, yleft, yright, yqueries, yframe, yregs⟩ :=
    exec_copyInputs h hb' hA hQ hs ht hq hsb htb hqb (hfit.of_le (by omega))
  refine ⟨y, (hrun hy).mono (by omega),
    (yregs _ (by decide) (by decide)).trans hb', ?_, ?_, ?_⟩
  · apply local_input X Y qs y.mem
    · intro j
      have hj : j.val < 5 := j.isLt
      change y.mem (b + j.val) = _
      exact (yframe _ (Or.inl (by omega))).trans (hhead j)
    · exact fun a ha => (yleft a ha).trans ((hframe _ (Or.inl (by omega))).trans (hleft a ha))
    · exact fun a ha => (yright a ha).trans ((hframe _ (Or.inl (by omega))).trans (hright a ha))
    · exact fun a ha => (yqueries a ha).trans ((hframe _ (Or.inl (by omega))).trans (hqueries a ha))
  · intro a ha
    have hI : QueriedProduct.inputEnd m n qs.length =
        5 + 2 * (n * D m) + 2 * qs.length := rfl
    exact (yframe _ (by rw [hI] at ha; omega)).trans (hframe _ (by rw [hI] at ha; omega))
  · intro j hj
    have jne : j ≠ Reg.address := by intro heq; subst j; simp [Reg.address] at hj
    exact (yregs _ (by omega) jne).trans (hregs j hj)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
