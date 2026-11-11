/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Linear codes

A *linear code* is a submodule `C` of the words `ι → M`, usually with `M = F` a field
[MacWilliams and Sloane, Chapter 1][MacWilliamsSloane1977]. The Hamming distance between two words
is the Hamming weight `hammingNorm` of their difference, and the difference of two codewords is a
codeword, so the minimum distance of a linear code is the least weight of a nonzero codeword
(`Cslib.Code.le_minDist_iff_hammingNorm`, `Cslib.Code.minDist_eq_iInf_hammingNorm`).

## Main results

* `Cslib.Code.le_minDist_iff_hammingNorm`: lower bounds on the minimum distance of a linear code
  are lower bounds on the weights of its nonzero codewords.
* `Cslib.Code.minDist_eq_iInf_hammingNorm`: the minimum distance of a linear code is the least
  weight of a nonzero codeword.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

@[expose] public section

namespace Cslib.Code

variable {ι R M : Type*} [Fintype ι] [Ring R] [AddCommGroup M] [Module R M] [DecidableEq M]

/-- The minimum distance of a linear code is at least `d` iff every nonzero codeword has weight at
least `d`. -/
theorem le_minDist_iff_hammingNorm (C : Submodule R (ι → M)) {d : ℕ∞} :
    d ≤ minDist (C : Set (ι → M)) ↔ ∀ x ∈ C, x ≠ 0 → d ≤ hammingNorm x := by
  rw [le_minDist_iff]
  refine ⟨fun h x hx hx0 => ?_, fun h x hx y hy hxy => ?_⟩
  · rw [← hammingDist_zero_right]
    exact h x hx 0 C.zero_mem hx0
  · rw [hammingDist_eq_hammingNorm]
    exact h _ (C.add_mem (C.neg_mem hx) hy) fun h0 => hxy (neg_add_eq_zero.1 h0)

/-- **Minimum weight.** The minimum distance of a linear code is the least weight of a nonzero
codeword, and `⊤` for the zero code. -/
theorem minDist_eq_iInf_hammingNorm (C : Submodule R (ι → M)) :
    minDist (C : Set (ι → M)) = ⨅ x ∈ C, ⨅ _ : x ≠ 0, (hammingNorm x : ℕ∞) :=
  le_antisymm
    (le_iInf₂ fun x hx => le_iInf fun hx0 => (le_minDist_iff_hammingNorm C).1 le_rfl x hx hx0)
    ((le_minDist_iff_hammingNorm C).2 fun _ hx hx0 => iInf₂_le_of_le _ hx (iInf_le _ hx0))

end Cslib.Code
