/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Copy
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandParameters

/-!
# Caller scalars from actual native parameters

## Main results

* `QueriedProduct.producer_fits`: original numerical admission covers both producer kernels.
* `QueriedProduct.exec_parameters`: actual powers, mask counting, root and band count,
  with a charge and complete high-register/memory frame.

The parameter phase reads original headers only. No computed roots, subset tables or
intermediate-state fit assertions are supplied by the caller.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM

/-- Numerical admission is on original scalar parameters, not machine states. -/
public theorem producer_fits {w L m N Q : ℕ} (hfit : Fits w (wordBudget L m N Q)) :
    Fits w (BandPreparation.wordBudget L m N) ∧ Fits w (Wanted.wordBudget L m N Q) := by
  constructor <;> apply hfit.of_le <;> unfold wordBudget <;> omega

/-- A common numerical margin covers caller counters, all allocation endpoints and constants. -/
public theorem caller_fits {w L m N Q : ℕ} (hfit : Fits w (wordBudget L m N Q)) :
    Fits w (16 * (L + N + Q + memoryEnd L m N Q + 16)) := by
  apply hfit.of_le
  unfold wordBudget
  omega

/-- All actual parameter computation is charged, and the original matrix/query memory is
untouched. Reusing the low bank preserves every high caller register. -/
public theorem exec_parameters {w L m N Q : ℕ} (hm : m ≤ L) (x : Data 160)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w parameters x y
        ((16 * L + 49) + ((6 * L + 16) * 2 ^ L + 14)) ∧
      BandPreparation.BandParameters L m N (y.comap bank) ∧ y.mem = x.mem ∧
      (∀ i, 96 ≤ i.val → y.regs i = x.regs i) := by
  obtain ⟨h, hh, hp, hm⟩ := BandPreparation.exec_header hm (x.comap bank) hL hmemory hN
    (producer_fits hfit).1
  obtain ⟨c, hc, cp, cm⟩ := BandPreparation.exec_countCode h hp (producer_fits hfit).1
  have he := (hh.seq hc).rename bank_injective
  change ExecWithin w parameters x (c.extend bank x)
    ((16 * L + 49) + ((6 * L + 16) * 2 ^ L + 14)) at he
  refine ⟨c.extend bank x, he, ?_, cm.trans hm, ?_⟩
  · simpa only [Data.comap_extend bank_injective] using cp
  · intro i hi
    have hnot : ¬∃ j, bank j = i := by
      rintro ⟨j, hj⟩
      have hv := congrArg (fun r : Fin 160 => r.val) hj
      change j.val = i.val at hv
      omega
    exact Function.extend_apply' _ _ _ hnot

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
