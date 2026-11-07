/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Bitwise
import Mathlib.Combinatorics.Colex

/-!
# Sparse binary words

Sums of distinct powers of two have exactly their specified set bits. Thus an injective
placement of Boolean coefficients cannot generate binary carries. The statements concern
natural-number arithmetic, independently of a machine word width or execution cost.

## Main results

* `Nat.testBit_sum_two_pow`: the set bits of a sum of distinct powers of two.
* `Nat.testBit_sum_injective`: injectively placed Boolean coefficients are recovered exactly.
* `Nat.and_sum_two_pow`: masking by sparse positions is their Boolean-weighted sum.

## References

These extend Mathlib's finite-set/binary-digit correspondence.
-/

@[expose] public section

namespace Nat

open Finset

/-- A sum of distinct powers of two has exactly the specified set bits. -/
theorem testBit_sum_two_pow (s : Finset ℕ) (k : ℕ) :
    (∑ i ∈ s, 2 ^ i).testBit k = true ↔ k ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

/-- Boolean coefficients placed at distinct bit positions do not carry into one another. -/
theorem testBit_sum_injective {α : Type*} (s : Finset α)
    (f : α → ℕ) (hf : Set.InjOn f s) (c : α → Bool) (k : ℕ) :
    (∑ i ∈ s, (c i).toNat * 2 ^ f i).testBit k = true ↔
      ∃ i ∈ s, c i = true ∧ f i = k := by
  classical
  have he : (∑ i ∈ s, (c i).toNat * 2 ^ f i) =
      ∑ i ∈ (s.filter (fun i => c i = true)).image f, 2 ^ i := by
    rw [sum_image (hf.mono (filter_subset _ _)), sum_filter]
    apply sum_congr rfl
    intro i _
    cases c i <;> simp
  rw [he, testBit_sum_two_pow]
  simp only [mem_image, mem_filter, and_assoc]

/-- Masking by sparse positions selects their original coefficients. -/
theorem and_sum_two_pow {α : Type*} [Fintype α]
    (f : α → ℕ) (hf : Function.Injective f) (x : ℕ) :
    x &&& (∑ i, 2 ^ f i) = ∑ i, (x.testBit (f i)).toNat * 2 ^ f i := by
  classical
  apply Nat.eq_of_testBit_eq
  intro k
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_land, Bool.and_eq_true, testBit_sum_injective _ f
    (fun _ _ _ _ h => hf h)]
  have hm : (∑ i, 2 ^ f i).testBit k = true ↔ ∃ i, f i = k := by
    rw [← sum_image (fun _ _ _ _ h => hf h), testBit_sum_two_pow]
    simp
  rw [hm]
  constructor
  · rintro ⟨hx, i, hi⟩
    exact ⟨i, mem_univ _, hi ▸ hx, hi⟩
  · rintro ⟨i, _, hx, hi⟩
    exact ⟨hi ▸ hx, i, hi⟩

/-- A Boolean-weighted sparse word fits below any width containing all its positions. -/
theorem sum_injective_lt_two_pow {α : Type*} (s : Finset α) (f : α → ℕ)
    (hf : Set.InjOn f s) (c : α → Bool) {L : ℕ} (hL : ∀ i ∈ s, f i < L) :
    (∑ i ∈ s, (c i).toNat * 2 ^ f i) < 2 ^ L := by
  classical
  calc
    (∑ i ∈ s, (c i).toNat * 2 ^ f i) ≤ ∑ i ∈ s, 2 ^ f i := by
      apply sum_le_sum
      intro i _
      cases c i <;> simp
    _ = ∑ j ∈ s.image f, 2 ^ j := (sum_image hf).symm
    _ < 2 ^ L := Nat.geomSum_lt (by decide) (by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      exact hL i hi)

/-- Increasing placements of the same Boolean coefficients give the same comparisons.
Gaps between bits do not affect numeric order. -/
theorem sum_strictMono_lt_iff {α : Type*} [Fintype α] [LinearOrder α]
    (f g : α → ℕ) (hf : StrictMono f) (hg : StrictMono g) (c d : α → Bool) :
    (∑ i, (c i).toNat * 2 ^ f i) < (∑ i, (d i).toNat * 2 ^ f i) ↔
      (∑ i, (c i).toNat * 2 ^ g i) < (∑ i, (d i).toNat * 2 ^ g i) := by
  classical
  have he (a : α → ℕ) (ha : Function.Injective a) (v : α → Bool) :
      (∑ i, (v i).toNat * 2 ^ a i) =
        ∑ j ∈ (univ.filter (fun i => v i = true)).image a, 2 ^ j := by
    rw [sum_image (fun _ _ _ _ h => ha h), sum_filter]
    apply sum_congr rfl
    intro i _
    cases v i <;> simp
  rw [he f hf.injective c, he f hf.injective d, he g hg.injective c, he g hg.injective d,
    geomSum_lt_geomSum_iff_toColex_lt_toColex (by decide : 2 ≤ 2),
    geomSum_lt_geomSum_iff_toColex_lt_toColex (by decide : 2 ≤ 2),
    Colex.toColex_image_lt_toColex_image hf, Colex.toColex_image_lt_toColex_image hg]

end Nat
