/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate (Mathlib, Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean)

public import Complexity.Init
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Monotone convergence for `ℝ≥0∞`-valued sums

`tsum` commutes with the supremum of a monotone sequence of `ℝ≥0∞`-valued functions.

## Main results

* `ENNReal.tsum_iSup_of_monotone`: the exchange of `tsum` and a monotone `iSup`.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- Monotone convergence for `ℝ≥0∞`-valued sums: `tsum` commutes with a monotone `iSup`. -/
theorem tsum_iSup_of_monotone {α : Type*} {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ a, Monotone fun n => f n a) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  rw [tsum_eq_iSup_sum]
  simp_rw [finsetSum_iSup_of_monotone hf]
  rw [iSup_comm]
  simp_rw [← tsum_eq_iSup_sum]

end ENNReal
