/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Cubes
public import Complexity.Foundations.Data.Finset.Lowest

/-!
# Canonical boxes of tensor leaves

A box has at most `m - t` stars or fixed P0 terms, with every star preceding every
fixed P0 term. Thus its leaves all have order at least `t`. Every box is obtained
uniquely from its P0 completion by turning an initial segment of its P0 coordinates
into stars; `Finset.lowest` supplies that initial segment without a separate rank API.

This adapts [AlmanWilliams2026, Section 4.2] and the primary formal source
[Boxes.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean) at `anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The definitions have the source's natural truncated subtraction: claims about order
explicitly require `t ≤ m`. These are finite statements, with no stored table or time bound.
-/

public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

variable {L : ℕ}

/-- A cube with a bounded number of stars/P0 symbols, stars preceding all fixed P0 symbols. -/
@[expose] def IsBox (m t : ℕ) (π : Cube L) : Prop :=
  π.starLevels.card + π.P0Levels.card ≤ m - t ∧
    ∀ ℓ ∈ π.starLevels, ∀ ℓ' ∈ π.P0Levels, ℓ < ℓ'

instance IsBox.instDecidable (m t : ℕ) (π : Cube L) : Decidable (IsBox m t π) :=
  inferInstanceAs (Decidable (π.starLevels.card + π.P0Levels.card ≤ m - t ∧
    ∀ ℓ ∈ π.starLevels, ∀ ℓ' ∈ π.P0Levels, ℓ < ℓ'))

/-- A lower bound on order is an upper bound on the number of P0 terms. -/
theorem le_order_iff {m t : ℕ} (ht : t ≤ m) (τ : Leaf L) :
    (t : ℤ) ≤ order m τ ↔ (P0Levels τ).card ≤ m - t := by
  unfold order
  omega

/-- A matching leaf can use P0 only at a star or a coordinate fixed to P0. -/
theorem P0Levels_subset_of_mem_leaves {π : Cube L} {τ : Leaf L} (hτ : τ ∈ Cube.leaves π) :
    P0Levels τ ⊆ Cube.P0Levels π ∪ Cube.starLevels π := by
  intro ℓ hℓ
  rw [mem_P0Levels] at hℓ
  rw [mem_union, Cube.mem_P0Levels, Cube.mem_starLevels, ← hℓ]
  exact (Cube.mem_leaves.1 hτ ℓ).symm

/-- Every leaf of a box has the required minimum order. -/
theorem le_order_of_mem_leaves {m t : ℕ} (ht : t ≤ m) {π : Cube L} (hπ : IsBox m t π)
    {τ : Leaf L} (hτ : τ ∈ Cube.leaves π) : (t : ℤ) ≤ order m τ := by
  rw [le_order_iff ht]
  calc (P0Levels τ).card ≤ (Cube.P0Levels π ∪ Cube.starLevels π).card :=
        card_le_card (P0Levels_subset_of_mem_leaves hτ)
    _ ≤ (Cube.P0Levels π).card + (Cube.starLevels π).card := card_union_le _ _
    _ ≤ m - t := (add_comm _ _).trans_le hπ.1

/-- The canonical cube made by starring the lowest P0 coordinates. -/
@[expose] def starLowest (e : ℕ) (τ : Leaf L) : Cube L := Cube.starAt (lowest e (P0Levels τ)) τ

/-- The selected initial segment is exactly the star set. -/
theorem starLevels_starLowest (e : ℕ) (τ : Leaf L) :
    Cube.starLevels (starLowest e τ) = lowest e (P0Levels τ) :=
  Cube.starLevels_starAt _ τ

/-- Unselected P0 coordinates remain fixed. -/
theorem P0Levels_starLowest (e : ℕ) (τ : Leaf L) :
    Cube.P0Levels (starLowest e τ) = P0Levels τ \ lowest e (P0Levels τ) :=
  Cube.P0Levels_starAt _ τ

/-- Completion recovers the original leaf, including when selection saturates. -/
theorem starsToP0_starLowest (e : ℕ) (τ : Leaf L) : Cube.starsToP0 (starLowest e τ) = τ :=
  Cube.starsToP0_starAt (lowest_subset _ _)

/-- The star-order condition characterizes the canonical form of a cube. -/
theorem eq_starLowest_starsToP0 (π : Cube L)
    (h : ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ') :
    π = starLowest (Cube.starLevels π).card (Cube.starsToP0 π) := by
  have hlow : Cube.starLevels π =
      lowest (Cube.starLevels π).card (P0Levels (Cube.starsToP0 π)) := by
    refine eq_lowest_of_lt ?_ fun ℓ hℓ ℓ' hℓ' => h ℓ hℓ ℓ' ?_
    · rw [P0Levels_starsToP0]
      exact subset_union_left
    · rw [P0Levels_starsToP0, mem_sdiff, mem_union] at hℓ'
      tauto
  rw [starLowest, ← hlow, Cube.starAt_starLevels_starsToP0]

/-- Starring any initial segment preserves the box count and order conditions. -/
theorem isBox_starLowest (m t e : ℕ) (τ : Leaf L) (hτ : (P0Levels τ).card ≤ m - t) :
    IsBox m t (starLowest e τ) := by
  rw [IsBox, ← card_P0Levels_starsToP0, starsToP0_starLowest, starLevels_starLowest,
    P0Levels_starLowest]
  exact ⟨hτ, fun ℓ hℓ ℓ' hℓ' => lowest_lt hℓ hℓ'⟩

end Cslib.Algorithms.MatrixMultiplication.Schonhage
