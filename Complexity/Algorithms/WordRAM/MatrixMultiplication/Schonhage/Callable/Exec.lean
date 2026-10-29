/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Core
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Return

/-!
# Complete native callable queried-product execution

The caller supplies original zero/one matrices and coordinate occurrences in a local original
input block. The product computes its own tables, layouts, groups, encoded bands, epochs and
answers. Every source memory access is translated to actual base addition and load/store code;
dirty words are normalized without bulk clearing. The final answer pointer is absolute.

This is the callable product prerequisite for an ET-record adapter, not that adapter, an
Exact Triangle solver or the complete ordinary-3SUM bound under #1394.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The complete charge includes two linear span normalizations and the computed setup. -/
@[expose] def timeBound {m N : ℕ} (qs : List (Fin N × Fin N)) : ℕ :=
  coreTime (m := m) qs + 7 * QueriedProduct.inputEnd m N qs.length + 7 * qs.length + 14

private theorem spans_le_budget (L m N Q : ℕ) :
    QueriedProduct.inputEnd m N Q ≤ QueriedProduct.outputBase L m N Q ∧
      QueriedProduct.inputEnd m N Q + QueriedProduct.outputBase L m N Q + Q + 2 ≤
        QueriedProduct.wordBudget L m N Q := by
  have hsep : QueriedProduct.inputEnd m N Q ≤ QueriedProduct.outputBase L m N Q := by
    unfold QueriedProduct.outputBase QueriedProduct.groupedBase QueriedProduct.originalBase
      QueriedProduct.codeBase QueriedProduct.offsetBase QueriedProduct.snapshotBase
    omega
  have hend : QueriedProduct.outputBase L m N Q + Q ≤ QueriedProduct.memoryEnd L m N Q := by
    unfold QueriedProduct.memoryEnd QueriedProduct.stampBase QueriedProduct.scratchBase
    have := Nat.zero_le (2 * (L + 1) * 10 ^ L)
    have := Nat.zero_le (10 ^ L)
    omega
  refine ⟨hsep, ?_⟩
  unfold QueriedProduct.wordBudget
  omega

/-- Caller-safe actual native product execution. The only local memory premise is the original
input block; all remaining target memory may be dirty. Every original occurrence is answered
exactly, original input words are restored exactly, and the caller memory outside the window
is preserved. The numerical width hypothesis is derived from original dimensions and base. -/
theorem exec {W b m N : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 163) (hb : x.regs Reg.base = b)
    (hinput : ∀ a, a < QueriedProduct.inputEnd m N qs.length →
      x.mem (b + a) =
        (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hN : D m ^ 18 ≤ N) (hfit : Fits W (b + 4 * windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W program x y (timeBound (m := m) qs) ∧
      y.regs Reg.result = b + QueriedProduct.outputBase (19 * m) m N qs.length ∧
      y.regs Reg.base = b ∧ y.regs Reg.modulus = windowSize N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (19 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length → y.mem (b + a) = x.mem (b + a)) ∧
      (∀ a, a < b ∨ b + windowSize N qs.length ≤ a → y.mem a = x.mem a) := by
  obtain ⟨hsep, hspan⟩ := spans_le_budget (19 * m) m N qs.length
  have hbudget := (source_admission (Q := qs.length) hN).2.2
  have hbound : QueriedProduct.inputEnd m N qs.length +
      QueriedProduct.outputBase (19 * m) m N qs.length + qs.length + 2 <
        windowSize N qs.length := hspan.trans_lt hbudget
  have hM : 0 < windowSize N qs.length := Nat.two_pow_pos _
  obtain ⟨c, hc, cb, cM, cI, cQ, cO, cv, ci, cf⟩ := exec_core X Y qs x hb hinput hX hY hN hfit
  have hIfit : Fits W (b + QueriedProduct.inputEnd m N qs.length +
      windowSize N qs.length + 2) := hfit.of_le (by omega)
  obtain ⟨s, hs, sm, sr⟩ := exec_restoreInput c cb cI cM hM hIfit
  have sb : s.regs Reg.base = b := (sr _ (by decide)).trans cb
  have sM : s.regs Reg.modulus = windowSize N qs.length := (sr _ (by decide)).trans cM
  have sQ : s.regs Reg.queryCount = qs.length := (sr _ (by decide)).trans cQ
  have sO : s.regs Reg.output = QueriedProduct.outputBase (19 * m) m N qs.length :=
    (sr _ (by decide)).trans cO
  have hOfit : Fits W (b + QueriedProduct.outputBase (19 * m) m N qs.length + qs.length +
      windowSize N qs.length + 2) := hfit.of_le (by omega)
  obtain ⟨y, hy, ym, yr, yf⟩ := exec_returnOutput s sb sO sQ sM hM hOfit
  refine ⟨y, (hc.seq (hs.seq hy)).mono (by unfold timeBound; omega), yr,
    (yf _ (by decide)).trans sb, (yf _ (by decide)).trans sM, ?_, ?_, ?_⟩
  · intro i
    rw [ym]
    rw [show b + (QueriedProduct.outputBase (19 * m) m N qs.length + i.val) =
      (b + QueriedProduct.outputBase (19 * m) m N qs.length) + i.val by omega]
    rw [ArrayNormalize.normalizePrefix_read _ _ _ _ _ i.isLt, sm,
      ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega)]
    simpa only [Nat.add_assoc] using cv i
  · intro a ha
    rw [ym, ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega), sm,
      ArrayNormalize.normalizePrefix_read _ _ _ _ _ ha]
    exact ci a ha
  · intro a ha
    rw [ym, ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega), sm,
      ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega)]
    exact cf a ha

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
