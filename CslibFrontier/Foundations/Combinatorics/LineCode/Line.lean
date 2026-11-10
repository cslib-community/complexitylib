/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.LineCode.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Punctured affine lines

A punctured line `puncturedLine u v` through the anchor `u` with a nonzero direction `v` has
`Fintype.card K - 1` points and omits `u`. A point `y` lies on it exactly when `v` is a nonzero
multiple of `y - u`, so a point other than the anchor lies on the punctured lines of exactly
`Fintype.card K - 1` nonzero directions. Consequently a set `B` meets the punctured lines through
`u` of at most `#(B.erase u) * (Fintype.card K - 1)` nonzero directions; in particular, an
occupied anchor blocks nothing. A list of `g` lines occupies at most `g * (Fintype.card K - 1)`
points. Cleanliness of a request (`IsClean`) is decidable.

## Main results

* `Cslib.LineCode.card_subtype_ne_zero`: there are `Fintype.card K ^ ℓ - 1` nonzero directions.
* `Cslib.LineCode.card_puncturedLine`: a punctured line has `Fintype.card K - 1` points.
* `Cslib.LineCode.notMem_puncturedLine_self`: a punctured line omits its anchor.
* `Cslib.LineCode.mem_puncturedLine_iff_exists_eq_smul`: `y` is on the line of direction `v`
  iff `v` is a nonzero multiple of `y - u`.
* `Cslib.LineCode.card_filter_mem_puncturedLine`: a point other than the anchor lies on the lines
  of exactly `Fintype.card K - 1` nonzero directions.
* `Cslib.LineCode.card_filter_not_disjoint_puncturedLine_le`: the blocking bound.
* `Cslib.LineCode.disjoint_puncturedLine_iff`: two punctured lines through one anchor are
  disjoint iff their directions are not proportional.
* `Cslib.LineCode.card_occupiedPoints_le`: `g` lines occupy at most `g * (Fintype.card K - 1)`
  points.

## References

* Adapted, with nonzero vectors in place of projective directions, from
  MassProduction/Scheduler.lean and MassProduction/Nonuniform/PhaseMenu.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.LineCode

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- Whether a request is clean is decidable. -/
instance {k : ℕ} (occupied : Finset (Fin ℓ → K)) (targets directions : Fin k → Fin ℓ → K) :
    DecidablePred (IsClean occupied targets directions) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- There are `Fintype.card K ^ ℓ - 1` nonzero directions. -/
theorem card_subtype_ne_zero :
    Fintype.card {v : Fin ℓ → K // v ≠ 0} = Fintype.card K ^ ℓ - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_fin]

/-- Membership in a punctured line is witnessed by a nonzero scalar. -/
theorem mem_puncturedLine {u v y : Fin ℓ → K} :
    y ∈ puncturedLine u v ↔ ∃ c : K, c ≠ 0 ∧ u + c • v = y := by
  simp [puncturedLine]

/-- A punctured line has at most `Fintype.card K - 1` points, one for each nonzero scalar. -/
theorem card_puncturedLine_le (u v : Fin ℓ → K) :
    #(puncturedLine u v) ≤ Fintype.card K - 1 :=
  card_image_le.trans_eq (by rw [card_erase_of_mem (mem_univ _), card_univ])

/-- A punctured line with a nonzero direction has exactly `Fintype.card K - 1` points. -/
theorem card_puncturedLine (u : Fin ℓ → K) {v : Fin ℓ → K} (hv : v ≠ 0) :
    #(puncturedLine u v) = Fintype.card K - 1 := by
  rw [puncturedLine, card_image_of_injective _
      (show Function.Injective fun c : K => u + c • v from
        (add_right_injective u).comp (smul_left_injective K hv)),
    card_erase_of_mem (mem_univ _), card_univ]

/-- A punctured line with a nonzero direction omits its anchor. -/
theorem notMem_puncturedLine_self (u : Fin ℓ → K) {v : Fin ℓ → K} (hv : v ≠ 0) :
    u ∉ puncturedLine u v := by
  rw [mem_puncturedLine]
  rintro ⟨c, hc, h⟩
  exact smul_ne_zero hc hv (add_eq_left.mp h)

/-- The point `y` lies on the punctured line through `u` with direction `v` iff `v` is a nonzero
multiple of `y - u`. -/
theorem mem_puncturedLine_iff_exists_eq_smul {u v y : Fin ℓ → K} :
    y ∈ puncturedLine u v ↔ ∃ c : K, c ≠ 0 ∧ v = c • (y - u) := by
  rw [mem_puncturedLine]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [add_sub_cancel_left, inv_smul_smul₀ hc]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [inv_smul_smul₀ hc, add_sub_cancel]⟩

/-- A point other than the anchor lies on the punctured lines of exactly `Fintype.card K - 1`
nonzero directions: the nonzero multiples of `y - u`. -/
theorem card_filter_mem_puncturedLine {u y : Fin ℓ → K} (hy : y ≠ u) :
    #{v ∈ univ.erase 0 | y ∈ puncturedLine u v} = Fintype.card K - 1 := by
  have hyu : y - u ≠ 0 := sub_ne_zero.mpr hy
  have h : ({v ∈ univ.erase 0 | y ∈ puncturedLine u v} : Finset (Fin ℓ → K)) =
      ((univ : Finset K).erase 0).image fun c => c • (y - u) := by
    ext v
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_image,
      mem_puncturedLine_iff_exists_eq_smul]
    constructor
    · rintro ⟨-, c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨smul_ne_zero hc hyu, c, hc, rfl⟩
  rw [h, card_image_of_injective _ (smul_left_injective K hyu), card_erase_of_mem (mem_univ _),
    card_univ]

/-- **Blocking bound.** A set `B` meets the punctured lines through `u` of at most
`#(B.erase u) * (Fintype.card K - 1)` nonzero directions. The anchor `u` blocks nothing. -/
theorem card_filter_not_disjoint_puncturedLine_le (u : Fin ℓ → K) (B : Finset (Fin ℓ → K)) :
    #{v ∈ univ.erase 0 | ¬Disjoint (puncturedLine u v) B} ≤
      #(B.erase u) * (Fintype.card K - 1) := by
  calc #{v ∈ univ.erase 0 | ¬Disjoint (puncturedLine u v) B}
      ≤ #((B.erase u).biUnion fun y => {v ∈ univ.erase 0 | y ∈ puncturedLine u v}) := by
        refine card_le_card fun v hv => ?_
        obtain ⟨hv, hvB⟩ := mem_filter.mp hv
        obtain ⟨y, hyL, hyB⟩ := not_disjoint_iff.mp hvB
        have hy : y ≠ u := fun h => notMem_puncturedLine_self u (ne_of_mem_erase hv) (h ▸ hyL)
        exact mem_biUnion.mpr ⟨y, mem_erase.mpr ⟨hy, hyB⟩, mem_filter.mpr ⟨hv, hyL⟩⟩
    _ ≤ ∑ y ∈ B.erase u, #{v ∈ univ.erase 0 | y ∈ puncturedLine u v} := card_biUnion_le
    _ = #(B.erase u) * (Fintype.card K - 1) := by
        rw [sum_congr rfl fun y hy => card_filter_mem_puncturedLine (ne_of_mem_erase hy),
          sum_const, smul_eq_mul]

/-- Two punctured lines through the same anchor are disjoint iff their directions are not
proportional: `v ≠ c • w` for every nonzero `c`. -/
theorem disjoint_puncturedLine_iff {u v w : Fin ℓ → K} :
    Disjoint (puncturedLine u v) (puncturedLine u w) ↔ ∀ c : K, c ≠ 0 → v ≠ c • w := by
  rw [disjoint_left]
  constructor
  · rintro h c hc rfl
    exact h (mem_puncturedLine.mpr ⟨1, one_ne_zero, rfl⟩)
      (mem_puncturedLine.mpr ⟨c, hc, by rw [one_smul]⟩)
  · intro h y hv hw
    obtain ⟨a, ha, rfl⟩ := mem_puncturedLine.mp hv
    obtain ⟨b, hb, hab⟩ := mem_puncturedLine.mp hw
    refine h (a⁻¹ * b) (mul_ne_zero (inv_ne_zero ha) hb) ?_
    rw [mul_smul, add_left_cancel hab, inv_smul_smul₀ ha]

/-- A list of `g` lines occupies at most `g * (Fintype.card K - 1)` points. -/
theorem card_occupiedPoints_le {g : ℕ} (lines : Fin g → Option ((Fin ℓ → K) × (Fin ℓ → K))) :
    #(occupiedPoints lines) ≤ g * (Fintype.card K - 1) := by
  calc #(occupiedPoints lines)
      ≤ ∑ i, #((lines i).elim ∅ fun line => puncturedLine line.1 line.2) := card_biUnion_le
    _ ≤ ∑ _i : Fin g, (Fintype.card K - 1) := by
        refine sum_le_sum fun i _ => ?_
        cases lines i with
        | none => exact Nat.zero_le _
        | some line => exact card_puncturedLine_le _ _
    _ = g * (Fintype.card K - 1) := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end Cslib.LineCode
