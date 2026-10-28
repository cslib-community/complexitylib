/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ChanHe.Defs

/-!
# Size bounds for the Chan–He selectors, including their default

Bounding the modulus does not require either filter to succeed: a failed filter returns one.
These bounds therefore apply to native execution with arbitrary nonnegative collision thresholds,
including empty input sets. They do not assert the collision-shrinking property of a successful
search.

## Main results

* `minOrOne_filter_bounds`: a positive bounded candidate set keeps its filtered selector bounded.
* `modulus_bounds_of_candidates`: both selections, including defaults, have product in `[1,m²]`.

The bounds are original elementary consequences of the existing finite selectors.
-/

@[expose] public section

namespace Cslib.Algorithms.ThreeSum.ChanHe

open Finset

/-- Filtering positive candidates bounded by `m` keeps the default-one selector in `[1,m]`.
The candidate set and the filtered set may both be empty. -/
theorem minOrOne_filter_bounds {Q : Finset ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hpos : ∀ q ∈ Q, 1 ≤ q) (hle : ∀ q ∈ Q, q ≤ m)
    (A : ℕ → Prop) [DecidablePred A] :
    1 ≤ minOrOne {q ∈ Q | A q} ∧ minOrOne {q ∈ Q | A q} ≤ m := by
  let S := {q ∈ Q | A q}
  by_cases h : S.Nonempty
  · have hmem : S.min' h ∈ Q := (mem_filter.mp (min'_mem S h)).1
    change 1 ≤ minOrOne S ∧ minOrOne S ≤ m
    rw [minOrOne, dite_eq_left h]
    exact ⟨hpos _ hmem, hle _ hmem⟩
  · change 1 ≤ minOrOne S ∧ minOrOne S ≤ m
    rw [minOrOne, dite_eq_right h]
    exact ⟨le_rfl, hm⟩

/-- Positive bounded candidates bound the modulus regardless of whether either filter succeeds.
This is a size bound only; no magnitude or successful-search premise is needed. -/
theorem modulus_bounds_of_candidates {Q : Finset ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hpos : ∀ q ∈ Q, 1 ≤ q) (hle : ∀ q ∈ Q, q ≤ m)
    (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    1 ≤ modulus Q Λ S₁ S₂ S₃ ∧ modulus Q Λ S₁ S₂ S₃ ≤ m ^ 2 := by
  have hp : 1 ≤ firstP Q Λ S₁ S₂ S₃ ∧ firstP Q Λ S₁ S₂ S₃ ≤ m :=
    minOrOne_filter_bounds hm hpos hle _
  have hq : 1 ≤ secondP Q Λ S₁ S₂ S₃ (firstP Q Λ S₁ S₂ S₃) ∧
      secondP Q Λ S₁ S₂ S₃ (firstP Q Λ S₁ S₂ S₃) ≤ m :=
    minOrOne_filter_bounds hm hpos hle _
  exact ⟨Nat.mul_le_mul hp.1 hq.1,
    (Nat.mul_le_mul hp.2 hq.2).trans_eq (pow_two m).symm⟩

end Cslib.Algorithms.ThreeSum.ChanHe
