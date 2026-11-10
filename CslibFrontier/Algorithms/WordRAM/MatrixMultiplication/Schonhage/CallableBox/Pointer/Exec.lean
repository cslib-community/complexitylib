/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Core
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Finish
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Exec
import CslibFrontier.Computability.WordRAM.Call

/-!
# Exact physical pointer-input box products

The public endpoint accepts actual external raw arrays and interleaved query occurrences,
including duplicates. It computes its own layout, gathers directly into the snapshot, executes
the unchanged mathematical back end and returns physically exact signed answers. The private
low payload may be dirty; the five scalar words and appended threshold are original input data.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open CallableProduct

/-- Full charge including conservative original-input and answer normalization. -/
@[expose] def timeBound (m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) : ℕ :=
  coreTime m t qs + 2 + 7 * (QueriedProduct.inputEnd m N qs.length + 1) + 7 * qs.length + 14

-- The finite traversal checks the separate pointer bank against every compiled source instruction.
set_option maxRecDepth 4096 in
private theorem pointer_registers_preserved :
    program.Preserves Reg.left ∧ program.Preserves Reg.right ∧ program.Preserves Reg.queries :=
  by decide

/-- Execute fixed pointer code from actual external readback, without a solver certificate. -/
theorem exec {W b m t N s r q : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 173)
    (hb : x.regs Reg.base = b) (hs : x.regs Reg.left = s)
    (hr : x.regs Reg.right = r) (hq : x.regs Reg.queries = q)
    (hheader : ∀ a < 5, x.mem (b + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem a)
    (hthreshold : x.mem (b + QueriedProduct.inputEnd m N qs.length) = t)
    (hsb : s + N * D m ≤ b) (hrb : r + N * D m ≤ b) (hqb : q + 2 * qs.length ≤ b)
    (hleft : ∀ a < N * D m, x.mem (s + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem (5 + a))
    (hright : ∀ a < N * D m, x.mem (r + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
        (5 + N * D m + a))
    (hqueries : ∀ a < 2 * qs.length, x.mem (q + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
        (5 + 2 * (N * D m) + a))
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (ht : t ≤ m) (hN : D m ^ 18 ≤ N)
    (hfit : Fits W (2 * b + 4 * windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W program x y (timeBound m t qs) ∧
      y.regs (callableBank CallableProduct.Reg.result) =
        b + QueriedProduct.outputBase (21 * m) m N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (21 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a < QueriedProduct.inputEnd m N qs.length + 1,
        y.mem (b + a) =
          (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem a) ∧
      (∀ a, a < b ∨ b + windowSize N qs.length ≤ a → y.mem a = x.mem a) ∧
      y.regs Reg.left = s ∧ y.regs Reg.right = r ∧ y.regs Reg.queries = q := by
  obtain ⟨c, hc, cb, cM, cI, cQ, cO, cv, ci, cf⟩ := exec_core X Y qs x hb hs hr hq
    hheader hthreshold hsb hrb hqb hleft hright hqueries hX hY ht hN hfit
  obtain ⟨hsep, hspan⟩ := CallableBoxProduct.spans_le_budget (21 * m) m t N qs.length
  have hbudget := (CallableBoxProduct.source_admission (Q := qs.length) ht hN).2.2
  have hbound : QueriedProduct.inputEnd m N qs.length + 1 +
      QueriedProduct.outputBase (21 * m) m N qs.length + qs.length + 2 <
        windowSize N qs.length := hspan.trans_lt hbudget
  obtain ⟨y, hy, ⟨yr, yi, yv, yf⟩, _⟩ := ExecWithin.rename_post callableBank_injective
    (exec_finish (c.comap callableBank) cb cI cQ cO cM (Nat.two_pow_pos _) hsep
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
      (fun i => Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ci cv
      (hfit.of_le (by omega)))
  have he : ExecWithin W program x y
      (coreTime m t qs + (2 + 7 * (QueriedProduct.inputEnd m N qs.length + 1) +
        7 * qs.length + 14)) := hc.seq hy
  refine ⟨y, he.mono (by unfold timeBound; omega), yr, yv, yi, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (yf a (by omega) (by omega)).trans (cf a ha)
  · exact (he.regs_eq pointer_registers_preserved.1).trans hs
  · exact (he.regs_eq pointer_registers_preserved.2.1).trans hr
  · exact (he.regs_eq pointer_registers_preserved.2.2).trans hq

/-- Allowance identity relating `CallableBoxProduct.timeBound` plus `gatherTime` to `timeBound`
plus the translated snapshot-copy term. -/
theorem timeBound_ledger (m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) :
    CallableBoxProduct.timeBound m t qs + gatherTime (N * D m) qs.length =
      timeBound m t qs + 3 * (7 * QueriedProduct.inputEnd m N qs.length + 10) := by
  have hs := PointerInput.source_ledger (21 * m) m t qs
  unfold CallableBoxProduct.timeBound CallableBoxProduct.coreTime timeBound coreTime
  omega

/-- One fixed flat native instruction list, returning the physical answer pointer. -/
@[expose] def nativeCode : Program .standard 173 :=
  program.program (callableBank CallableProduct.Reg.result)

-- The finite traversal includes the compiled box-product source and the four native copies.
set_option maxRecDepth 4096 in
/-- Pointer gathering retains fixed code and does not inspect the physical word width. -/
theorem nativeCode_fixed : nativeCode.length ≤ 131584 ∧ ¬nativeCode.ReadsWidth := by
  constructor
  · simp only [nativeCode, Code.program, List.length_append, Code.length_assemble,
      List.length_singleton]
    decide
  · apply Code.not_readsWidth_program
    decide

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct
