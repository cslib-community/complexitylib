/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.Weight
import Mathlib.Data.Fintype.Powerset

/-!
# Strings of a given weight below or above a string

In the pointwise order on `ι → Bool`, the strings `x ≤ y` of weight `a` are the indicators of the
`a`-element subsets of the support of `y`, so there are `C(|y|, a)` of them
(`Cslib.BitString.card_filter_le_and_weight_eq`). Complementing every bit reverses the order, so
the strings `y ≥ x` of weight `b ≤ |ι|` number `C(|ι| - |x|, |ι| - b)`
(`Cslib.BitString.card_filter_ge_and_weight_eq`). These count the partners in the containment
relation between two weight layers that adversary arguments use.

## Main results

* `Cslib.BitString.card_filter_le_and_weight_eq`: `#{x ≤ y | |x| = a} = C(|y|, a)`.
* `Cslib.BitString.card_filter_ge_and_weight_eq`: `#{y ≥ x | |y| = b} = C(|ι| - |x|, |ι| - b)`.
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The strings of weight `a` below `y` are the indicators of the `a`-element subsets of the
support of `y`: there are `C(|y|, a)` of them. -/
theorem card_filter_le_and_weight_eq (y : ι → Bool) (a : ℕ) :
    #{x : ι → Bool | x ≤ y ∧ weight x = a} = (weight y).choose a := by
  rw [weight, ← card_powersetCard]
  refine card_nbij' (fun x => ({i | x i = true} : Finset ι)) (fun s i => decide (i ∈ s))
    (fun x hx => ?_) (fun s hs => ?_) (fun x _ => ?_) (fun s _ => ?_)
  · obtain ⟨hxy, hw⟩ := (mem_filter.1 hx).2
    refine mem_powersetCard.2 ⟨fun i hi => ?_, hw⟩
    have hxi : x i = true := (mem_filter.1 hi).2
    exact mem_filter.2 ⟨mem_univ i, le_antisymm (Bool.le_true _) (hxi ▸ hxy i)⟩
  · obtain ⟨hsub, hcard⟩ := mem_powersetCard.1 hs
    refine mem_filter.2 ⟨mem_univ _, fun i => ?_, ?_⟩
    · by_cases hi : i ∈ s
      · have := (mem_filter.1 (hsub hi)).2
        simp [hi, this]
      · simp [hi]
    · rw [← hcard, weight]
      congr 1
      ext i
      simp
  · funext i
    simp
  · ext i
    simp

/-- The strings of weight `b ≤ |ι|` above `x` are the complements of the strings of weight
`|ι| - b` below the complement of `x`: there are `C(|ι| - |x|, |ι| - b)` of them. -/
theorem card_filter_ge_and_weight_eq (x : ι → Bool) {b : ℕ} (hb : b ≤ Fintype.card ι) :
    #{y : ι → Bool | x ≤ y ∧ weight y = b} =
      (Fintype.card ι - weight x).choose (Fintype.card ι - b) := by
  rw [← weight_not x, ← card_filter_le_and_weight_eq]
  refine card_nbij' (fun y i => !y i) (fun z i => !z i) (fun y hy => ?_) (fun z hz => ?_)
    (fun y _ => ?_) (fun z _ => ?_)
  · obtain ⟨hxy, hw⟩ := (mem_filter.1 hy).2
    refine mem_filter.2 ⟨mem_univ _, fun i => ?_, ?_⟩
    · have : x i ≤ y i := hxy i
      change (!y i) ≤ !x i
      revert this
      cases x i <;> cases y i <;> decide
    · change weight (fun i => !y i) = Fintype.card ι - b
      rw [weight_not, hw]
  · obtain ⟨hzx, hw⟩ := (mem_filter.1 hz).2
    refine mem_filter.2 ⟨mem_univ _, fun i => ?_, ?_⟩
    · have : z i ≤ !x i := hzx i
      change x i ≤ !z i
      revert this
      cases x i <;> cases z i <;> decide
    · change weight (fun i => !z i) = b
      rw [weight_not, hw]
      omega
  · funext i
    simp
  · funext i
    simp

end Cslib.BitString
