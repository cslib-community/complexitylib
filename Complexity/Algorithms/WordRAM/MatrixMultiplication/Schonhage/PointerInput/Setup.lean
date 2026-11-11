/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput.Program
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Exec

/-!
# Runtime-computed pointer-front layout

The protected snapshot address and threshold are computed by charged source instructions from
ordinary scalar/header words. No runtime geometry or synthesized program is an input.
`source_ledger` relates this executed prefix and the shared snapshot continuation to the
original contiguous-source allowance.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput

open Cslib.WordRAM

/-- Compute layout and retain threshold without reading the dirty low matrix/query payload. -/
theorem exec_setupLayout {W L m t N Q : ℕ} (hm : m ≤ L) (x : Data 160)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N)
    (hQ : x.mem 4 = Q) (ht : x.mem (QueriedProduct.inputEnd m N Q) = t)
    (hfit : Fits W (BoxProduct.wordBudget L m t N Q)) :
    ∃ y, ExecWithin W setupLayout x y (prefixTime L) ∧
      QueriedProduct.Parameters L m N Q y ∧ y.regs BoxProduct.Reg.threshold = t ∧
      y.mem = x.mem := by
  obtain ⟨u, hu, ut, um⟩ := BoxProduct.exec_loadThreshold hm x hL hmemory hN hQ ht hfit
  obtain ⟨p, hp, pp, pm, _⟩ := QueriedProduct.exec_parameters hm u
    (by rw [um]; exact hL) (by rw [um]; exact hmemory) (by rw [um]; exact hN)
    (BoxProduct.old_fits hfit)
  obtain ⟨y, hy, yp, ym⟩ := QueriedProduct.exec_layout p pp
    (by rw [pm, um]; exact hQ) (BoxProduct.old_fits hfit)
  refine ⟨y, (hu.seq (hp.seq hy)).mono (by unfold prefixTime; omega), yp, ?_,
    ym.trans (pm.trans um)⟩
  exact (hy.regs_eq (by decide)).trans ((hp.regs_eq (by decide)).trans ut)

/-- Exact identity between the source allowances; only the original snapshot pass is omitted. -/
theorem source_ledger (L m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) :
    prefixTime L + (7 * QueriedProduct.inputEnd m N qs.length + 10) +
      BoxProduct.snapshotTimeBound L m t qs = BoxProduct.timeBound L m t qs := by
  unfold prefixTime BoxProduct.snapshotTimeBound BoxProduct.snapshotFrontTime
    QueriedProduct.routingFromSnapshotTime BoxProduct.timeBound BoxProduct.frontTime
    QueriedProduct.routingTimeBound
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput
