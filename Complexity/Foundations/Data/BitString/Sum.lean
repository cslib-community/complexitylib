/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.SymmDiff

/-!
# Finset sums of bit strings

Elementary cancellation properties of `Finset.sum` in `Cslib.BitString b` (where every element has
additive order dividing `2`).

## Main results

* `Cslib.BitString.sum_bitString_eq_iff_sum_symmDiff_eq_zero`: two finset sums in `BitString b` are
  equal if and only if the sum over the symmetric difference `symmDiff S₁ S₂` is `0`.
-/

public section

namespace Cslib.BitString

open scoped BigOperators

/-- In `BitString b` (where every element has additive order dividing `2`), two finset sums are
equal if and only if the sum over their symmetric difference is `0`. -/
theorem sum_bitString_eq_iff_sum_symmDiff_eq_zero {ι : Type*} [DecidableEq ι] {b : ℕ}
    (S₁ S₂ : Finset ι) (g : ι → BitString b) :
    ∑ α ∈ S₁, g α = ∑ α ∈ S₂, g α ↔ ∑ α ∈ symmDiff S₁ S₂, g α = 0 := by
  have hdisj₁ : Disjoint (S₁ \ S₂) (S₁ ∩ S₂) := Finset.disjoint_sdiff_inter S₁ S₂
  have hdisj₂ : Disjoint (S₂ \ S₁) (S₁ ∩ S₂) := by
    rw [Finset.inter_comm]
    exact Finset.disjoint_sdiff_inter S₂ S₁
  have hdisj_symm : Disjoint (S₁ \ S₂) (S₂ \ S₁) := disjoint_sdiff_sdiff
  have hunion₁ : S₁ \ S₂ ∪ S₁ ∩ S₂ = S₁ := Finset.sdiff_union_inter S₁ S₂
  have hunion₂ : S₂ \ S₁ ∪ S₁ ∩ S₂ = S₂ := by
    rw [Finset.inter_comm]
    exact Finset.sdiff_union_inter S₂ S₁
  have hsum₁ : ∑ α ∈ S₁, g α = ∑ α ∈ S₁ \ S₂, g α + ∑ α ∈ S₁ ∩ S₂, g α := by
    conv_lhs => rw [← hunion₁, Finset.sum_union hdisj₁]
  have hsum₂ : ∑ α ∈ S₂, g α = ∑ α ∈ S₂ \ S₁, g α + ∑ α ∈ S₁ ∩ S₂, g α := by
    conv_lhs => rw [← hunion₂, Finset.sum_union hdisj₂]
  have hsymm : ∑ α ∈ symmDiff S₁ S₂, g α = ∑ α ∈ S₁ \ S₂, g α + ∑ α ∈ S₂ \ S₁, g α := by
    change ∑ α ∈ S₁ \ S₂ ∪ S₂ \ S₁, g α = _
    exact Finset.sum_union hdisj_symm
  rw [hsum₁, hsum₂, hsymm, add_right_cancel_iff]
  constructor
  · intro h
    rw [h, BitString.add_self]
  · intro h
    calc ∑ α ∈ S₁ \ S₂, g α
        = ∑ α ∈ S₁ \ S₂, g α + (∑ α ∈ S₁ \ S₂, g α + ∑ α ∈ S₂ \ S₁, g α) := by
          rw [h, add_zero]
      _ = ∑ α ∈ S₂ \ S₁, g α := BitString.add_cancel_left _ _

end Cslib.BitString
