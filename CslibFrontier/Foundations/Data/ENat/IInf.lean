/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/ENat/Lattice.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.ENat.Lattice
import Mathlib.Order.SuccPred.CompleteLinearOrder

/-!
# Finite bounds on an infimum of natural numbers in `ℕ∞`

A complexity measure defined as `⨅ w, cost w` over a type of witnesses is at most a finite budget
`k` exactly when some witness costs at most `k`. This is the `ℕ∞` case of Mathlib's
`iInf_le_iff_of_not_isPredPrelimit`: a finite `k` is covered by `k + 1`, so it is not a
predecessor prelimit. The lemmas below discharge that side condition once for their clients.

## Main results

* `ENat.iInf_le_natCast_iff`: `⨅ i, f i ≤ k ↔ ∃ i, f i ≤ k` for a finite `k`.
* `ENat.iInf_natCast_le_natCast_iff`: the same for a family of natural numbers.
-/

public section

namespace ENat

variable {ι : Sort*}

/-- An infimum in `ℕ∞` is at most a finite `k` exactly when some term is: the `ℕ∞` case of
`iInf_le_iff_of_not_isPredPrelimit`. -/
theorem iInf_le_natCast_iff {f : ι → ℕ∞} {k : ℕ} : ⨅ i, f i ≤ k ↔ ∃ i, f i ≤ k :=
  iInf_le_iff_of_not_isPredPrelimit fun h =>
    h _ (Order.covBy_succ_of_not_isMax (not_isMax_iff_ne_top.2 (natCast_ne_top k)))

/-- An infimum of natural numbers is at most `k` exactly when some term is. -/
theorem iInf_natCast_le_natCast_iff {f : ι → ℕ} {k : ℕ} :
    ⨅ i, (f i : ℕ∞) ≤ k ↔ ∃ i, f i ≤ k := by
  simp only [iInf_le_natCast_iff, natCast_le_natCast]

end ENat
