/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Patch
import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Prepare

/-!
# Record decoding without low-payload staging

Only the selected record, logarithm and five scalar/header words are prepared, followed by the
ordinary threshold patch. Raw matrices and query occurrences remain at their physical source
pointers. Contiguous-input preparation with low-payload array copies is provided separately by
`RecordProduct.prepare`.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open RecordProduct

/-- Read and decode an actual record, then initialize only the scalar header and threshold. -/
@[expose] def prepare : Code .standard 320 :=
  .seq readRecord (.seq logarithm (.seq writeHeader patchInput))

/-- Actual pointer preparation has no matrix or coordinate copying stage. -/
theorem exec_prepare {W b m n i out rho piece s t q : ℕ}
    (X : Matrix (Fin n) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin n) ℤ)
    (qs : List (Fin n × Fin n)) (x : Data 320)
    (hD : x.mem 1 = D m) (hn : x.mem 3 = n)
    (hi : x.regs Reg.ordinal = i) (hout : x.regs 39 = out) (hb : x.regs 42 = b)
    (hrec : out + i * (6 + 2 * (n * D m)) + 6 ≤ b)
    (hrecord : (Block.mk (out + i * (6 + 2 * (n * D m))) 6).Realizes x.mem
      ![rho, piece, q, qs.length, s, t])
    (hfit : Fits W (2 * b + 2 * (n * D m) + 2 * qs.length + 20 * m + D m + n + 256)) :
    ∃ y, ExecWithin W prepare x y (8 * m + 64) ∧
      y.regs Reg.base = b ∧ y.regs Reg.left = s ∧ y.regs Reg.right = t ∧
      y.regs Reg.queries = q ∧
      (∀ a < 5, y.mem (b + a) =
        (State.init (BoxProduct.input true (21 * m) (m / 9) X Y qs) : State 160).data.mem a) ∧
      y.mem (b + QueriedProduct.inputEnd m n qs.length) = m / 9 ∧
      (∀ a, a < b ∨ b + QueriedProduct.inputEnd m n qs.length + 1 ≤ a →
        y.mem a = x.mem a) ∧
      ∀ j : Fin 320, j.val < 65 → y.regs j = x.regs j := by
  obtain ⟨r, hr, rm, rD, rn, rA, rAA, rb, rrec, rrho, rpiece, rq, rQ, rs, rt,
    rarg, r1, r2, r19, r4⟩ := exec_readRecord x ![rho, piece, q, qs.length, s, t]
      hD hn hi hout hb hrec hrecord (hfit.of_le (by omega))
  have rq' : r.regs Reg.queries = q := by simpa +decide using rq
  have rQ' : r.regs Reg.count = qs.length := by simpa +decide using rQ
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
  have hb' : h.regs Reg.base = b := (hregs _ (by decide)).trans lb
  have hI : 5 ≤ QueriedProduct.inputEnd m n qs.length := by
    unfold QueriedProduct.inputEnd; omega
  have hlen : h.mem b = QueriedProduct.inputEnd m n qs.length - 1 := by
    have hh := hhead (0 : Fin 5)
    change h.mem (b + 0) = 4 + 2 * (n * D m) + 2 * qs.length at hh
    simp only [Nat.add_zero] at hh
    unfold QueriedProduct.inputEnd
    omega
  have hm : h.mem (b + 2) = m := hhead (2 : Fin 5)
  have hmD : m ≤ D m := (Nat.lt_pow_self (by decide : 1 < (4 : ℕ))).le
  obtain ⟨y, hy, ym, yb, yr⟩ := exec_patchInput h hb' hm hlen hI
    (hfit.of_le (by unfold QueriedProduct.inputEnd; omega))
  have head (a : ℕ) (ha : a < 5) : h.mem (b + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a := by
    have hh := hhead ⟨a, ha⟩
    have hs := original_header X Y qs ⟨a, ha⟩
    change h.mem (b + a) = _ at hh
    change (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
      (0 + a) = _ at hs
    exact hh.trans (by simpa only [Nat.zero_add] using hs.symm)
  refine ⟨y, (hr.seq (hl.seq (hh.seq hy))).mono (by omega), yb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hy.regs_eq (by decide)).trans
      ((hregs _ (by decide)).trans ((lr _ (by decide)).trans rs'))
  · exact (hy.regs_eq (by decide)).trans
      ((hregs _ (by decide)).trans ((lr _ (by decide)).trans rt'))
  · exact (hy.regs_eq (by decide)).trans
      ((hregs _ (by decide)).trans ((lr _ (by decide)).trans rq'))
  · intro a ha
    by_cases h0 : a = 0
    · subst a
      rw [ym]
      simp only [Nat.add_zero]
      rw [Function.update_of_ne (by omega), Function.update_self]
      exact (BoxProduct.input_length true (21 * m) (m / 9) X Y qs).symm
    · by_cases h1 : a = 1
      · subst a
        rw [ym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
        rfl
      · rw [ym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), head a ha]
        exact (QueriedProduct.input_change_level true (19 * m) (21 * m) X Y qs a h1).trans
          (BoxProduct.input_prefix true X Y qs a (by omega) (by omega)).symm
  · rw [ym, Function.update_self]
  · intro a ha
    rw [ym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), hframe a (by omega), lm, rm]
  · intro j hj
    rw [yr j hj, hregs _ (by omega), lr _ (Or.inl (by omega))]
    exact hr.regs_eq (RecordProduct.read_preserves j hj)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
