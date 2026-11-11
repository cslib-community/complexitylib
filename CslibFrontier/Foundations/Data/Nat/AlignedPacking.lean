/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `Mathlib/Algebra/BigOperators/Ring/Finset.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max

/-!
# Aligned packing of power-size blocks

Blocks of sizes `b ^ ℓ i`, for `i` in a finite set `s`, fit side by side into
`[0, ∑ i ∈ s, b ^ ℓ i)` so that every block starts at a multiple of its own size
(`Nat.exists_aligned_packing`). Place the blocks in decreasing order of size: each starting point is
then a sum of larger powers of `b`, all divisible by the next block's size.

For `b = 2` an aligned block is a binary address prefix: the numbers in the block of `i` are those
whose bits above position `ℓ i` are the bits of its start. A circuit reading a table of all the
blocks at an address in block `i` therefore needs only the bits of the start above `ℓ i` and the
offset bits below, with no addition.

## Main results

* `Nat.exists_aligned_packing`: blocks of sizes `b ^ ℓ i` pack into their total size with aligned
  starting points.
-/

public section

namespace Nat

open Finset

/-- **Aligned packing.** Blocks of sizes `b ^ ℓ i`, for `i ∈ s`, can be placed at pairwise disjoint
positions `o i` inside `[0, ∑ i ∈ s, b ^ ℓ i)` so that each starts at a multiple of its size:
place them in decreasing order of size. -/
theorem exists_aligned_packing {ι : Type*} (b : ℕ) (ℓ : ι → ℕ) (s : Finset ι) :
    ∃ o : ι → ℕ, (∀ i ∈ s, b ^ ℓ i ∣ o i ∧ o i + b ^ ℓ i ≤ ∑ j ∈ s, b ^ ℓ j) ∧
      ∀ i ∈ s, ∀ j ∈ s, ∀ t, o i ≤ t → t < o i + b ^ ℓ i → o j ≤ t → t < o j + b ^ ℓ j →
        i = j := by
  classical
  induction s using Finset.induction_on_min_value ℓ with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a s ha hmin ih =>
    obtain ⟨o, hfit, hdisj⟩ := ih
    refine ⟨Function.update o a (∑ j ∈ s, b ^ ℓ j), ?_, ?_⟩
    · intro i hi
      rw [sum_insert ha]
      rcases mem_insert.1 hi with rfl | hi
      · rw [Function.update_self]
        exact ⟨dvd_sum fun j hj => pow_dvd_pow b (hmin j hj), by omega⟩
      · have hne : i ≠ a := fun h => ha (h ▸ hi)
        rw [Function.update_of_ne hne]
        exact ⟨(hfit i hi).1, by have := (hfit i hi).2; omega⟩
    · intro i hi j hj t hi₁ hi₂ hj₁ hj₂
      have hside (u : ι) (hu : u ∈ s) : o u + b ^ ℓ u ≤ ∑ j ∈ s, b ^ ℓ j := (hfit u hu).2
      rcases mem_insert.1 hi with rfl | hi' <;> rcases mem_insert.1 hj with rfl | hj'
      · rfl
      · have hne : j ≠ i := fun h => ha (h ▸ hj')
        rw [Function.update_self] at hi₁
        rw [Function.update_of_ne hne] at hj₁ hj₂
        have := hside j hj'
        omega
      · have hne : i ≠ j := fun h => ha (h ▸ hi')
        rw [Function.update_self] at hj₁
        rw [Function.update_of_ne hne] at hi₁ hi₂
        have := hside i hi'
        omega
      · have hni : i ≠ a := fun h => ha (h ▸ hi')
        have hnj : j ≠ a := fun h => ha (h ▸ hj')
        rw [Function.update_of_ne hni] at hi₁ hi₂
        rw [Function.update_of_ne hnj] at hj₁ hj₂
        exact hdisj i hi' j hj' t hi₁ hi₂ hj₁ hj₂

end Nat
