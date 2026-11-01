/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxPartition

/-!
# Output boxes indexed by leaves of exactly the threshold order

Completing the stars of an output box gives its unique contributing leaf of order `t`.
Conversely `starBelow` constructs this box from such a leaf. The high-order partition
remains the one in `BoxPartition`; this is an additional finite indexing bijection.

Adapted from [AlmanWilliams2026, Section 4.2] and the primary formal source
[BoxesFromLeaves.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec4/BoxesFromLeaves.lean) at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
No native enumeration or lookup-cost statement is supplied by this bijection.
-/

public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

variable {L m t : ℕ} {η : OutStr L} {τ : Leaf L}

/-- An output box has exactly the prescribed combined star and P0 count. -/
theorem card_starLevels_add_card_P0Levels {π : Cube L} (hπ : π ∈ (boxLevelSets m t η).biUnion
  (boxesAt η)) :
    (Cube.starLevels π).card + (Cube.P0Levels π).card = m - t := by
  obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
  rw [← card_union_of_disjoint (Cube.disjoint_starLevels_P0Levels π),
    boxesAt_starLevels_union_P0Levels hπV, (mem_powersetCard.1 hV).2]

/-- Star the P0 coordinates preceding every non-P0 inner coordinate. -/
@[expose] def starBelow (η : OutStr L) (τ : Leaf L) : Cube L :=
  Cube.starAt (initialLevels (innerSetO η) (P0LevelsWithin (innerSetO η) τ)) τ

private lemma card_P0LevelsWithin_eq (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    (P0LevelsWithin (innerSetO η) τ).card = m - t := by
  have := order_eq_sub_card_P0LevelsWithin m η τ hτ
  omega

private lemma paddedLevels_eq_self (Q Z : Finset (Fin L)) (hZ : Z.card = m - t) : paddedLevels m t
  Q Z = Z := by
  simp [paddedLevels, lowest, hZ]

/-- At exact threshold order, the padded construction is the initial-star construction. -/
theorem boxOfLeaf_eq_starBelow (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    boxOfLeaf m t η τ = starBelow η τ := by
  rw [boxOfLeaf, starBelow, paddedLevels_eq_self _ _ (card_P0LevelsWithin_eq hτ hord)]

/-- Initial starring retains the original leaf. -/
theorem mem_leaves_starBelow (η : OutStr L) (τ : Leaf L) : τ ∈ Cube.leaves (starBelow η τ) :=
  Cube.mem_leaves_starAt _ τ

/-- A contributing leaf of exact threshold order gives an eligible output box. -/
theorem starBelow_mem (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    starBelow η τ ∈ (boxLevelSets m t η).biUnion (boxesAt η) := by
  have hmem := boxOfLeaf_mem_boxesAt m t hτ
  rw [boxOfLeaf_eq_starBelow hτ hord, paddedLevels_eq_self _ _ (card_P0LevelsWithin_eq hτ hord)]
    at hmem
  exact mem_biUnion.2 ⟨_, mem_powersetCard.2 ⟨filter_subset _ _, card_P0LevelsWithin_eq hτ hord⟩,
    hmem⟩

/-- Completing the initial stars recovers the original leaf. -/
theorem starsToP0_starBelow (η : OutStr L) (τ : Leaf L) : Cube.starsToP0 (starBelow η τ) = τ :=
  Cube.starsToP0_starAt fun _ hℓ => mem_P0Levels.2 (mem_filter.1 (initialLevels_subset _ _ hℓ)).2

/-- Completing an output box gives a contributing leaf of exact threshold order. -/
theorem starsToP0_of_mem (ht : t ≤ m) (hη : (innerSetO η).card = m) {π : Cube L}
    (hπ : π ∈ (boxLevelSets m t η).biUnion (boxesAt η)) :
    Leaf.Contributes (Cube.starsToP0 π) η ∧ order m (Cube.starsToP0 π) = t := by
  refine ⟨((contributes_high_iff_mem_box_leaves m t ht η hη _).2 ⟨π, hπ, Cube.starsToP0_mem_leaves
    π⟩).1, ?_⟩
  rw [order, card_P0Levels_starsToP0, card_starLevels_add_card_P0Levels hπ]
  omega

/-- Each output box has exactly one exact-threshold leaf giving its initial-star form. -/
theorem existsUnique_starBelow_eq (ht : t ≤ m) (hη : (innerSetO η).card = m) {π : Cube L}
    (hπ : π ∈ (boxLevelSets m t η).biUnion (boxesAt η)) :
    ∃! τ : Leaf L, (Leaf.Contributes τ η ∧ order m τ = t) ∧ starBelow η τ = π := by
  obtain ⟨hτ, hord⟩ := starsToP0_of_mem ht hη hπ
  refine ⟨Cube.starsToP0 π, ⟨⟨hτ, hord⟩, ?_⟩, ?_⟩
  · -- both are boxes of `η` with this leaf, and by Lemma 28 there is only one
    exact (existsUnique_box_containing_leaf m t ht η hη _ hτ hord.ge).unique
      ⟨starBelow_mem hτ hord, mem_leaves_starBelow η _⟩ ⟨hπ, Cube.starsToP0_mem_leaves π⟩
  · rintro τ ⟨-, rfl⟩
    exact (starsToP0_starBelow η τ).symm

end Cslib.Algorithms.MatrixMultiplication.Schonhage
