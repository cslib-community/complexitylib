/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/ENat/Lattice.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.ENat.Lattice

/-!
# Finite bounds on an infimum of natural numbers in `ℕ∞`

A complexity measure defined as `⨅ w, cost w` over a type of witnesses is at most a finite budget
`k` exactly when some witness costs at most `k`. The infimum of a nonempty family is attained
(`ENat.exists_eq_iInf`), and an empty family has infimum `⊤`, which exceeds every `k`.

## Main results

* `ENat.iInf_le_natCast_iff`: `⨅ i, f i ≤ k ↔ ∃ i, f i ≤ k` for a finite `k`.
* `ENat.iInf_natCast_le_natCast_iff`: the same for a family of natural numbers.
-/

public section

namespace ENat

variable {ι : Sort*}

/-- An infimum in `ℕ∞` is at most a finite `k` exactly when some term is. -/
theorem iInf_le_natCast_iff {f : ι → ℕ∞} {k : ℕ} : ⨅ i, f i ≤ k ↔ ∃ i, f i ≤ k := by
  refine ⟨fun h => ?_, fun ⟨i, hi⟩ => (iInf_le f i).trans hi⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp at h
  obtain ⟨i, hi⟩ := exists_eq_iInf f
  exact ⟨i, hi.trans_le h⟩

/-- An infimum of natural numbers is at most `k` exactly when some term is. -/
theorem iInf_natCast_le_natCast_iff {f : ι → ℕ} {k : ℕ} :
    ⨅ i, (f i : ℕ∞) ≤ k ↔ ∃ i, f i ≤ k := by
  simp only [iInf_le_natCast_iff, natCast_le_natCast]

end ENat
