/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Orders

/-!
# Cubes of tensor leaves for the improved thin-product decomposition

A cube fixes a term at some levels and permits every term at its star levels. It denotes a
finite set of the existing tensor leaves. Its integer value sums the actual products of the
existing two encodings. This is finite algebra; no cube is a native lookup or time certificate.

## Main definitions

* `CubeSymbol`, `Cube`: term-or-star symbols and their level-indexed tuples.
* `Cube.HasLeaf`, `Cube.leaves`, `Cube.starLevels`, `Cube.P0Levels`: finite incidence data.
* `Cube.val`: signed sum of existing encoded products.
* `Cube.ofLeaf`, `Cube.replace`, `Cube.starAt`, `Cube.starsToP0`: basic cube operations.

## Main results

* `Cube.card_leaves`: each star supplies ten independent term choices.
* `Cube.leaves_ofLeaf`: a cube fixing every level has exactly its original leaf.
* `Cube.mem_leaves_replace`: replacing a star selects the leaves using that term.
* `Cube.starLevels_starAt`, `Cube.P0Levels_starAt`: explicit readback of inserted stars.

## References

Adapted from [AlmanWilliams2026, Section 4.2] and the primary formal source at
[anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp):
`PaperStatements.lean` lines 1844–1901 and 1952–1954, and [Boxes.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean).
The local value expression uses `encodeLeft` and `encodeRight`, the existing versions of
that source's two encoding forms. No source machine, native execution or cost law is imported.
-/

public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

-- Expose the derived finite enumeration for checked box counts and signed-value clients.
@[expose] public section

/-- A fixed multiplication label or an unrestricted level. -/
inductive CubeSymbol : Type
  | term (lam : Term)
  | star
  deriving DecidableEq, Fintype

end

/-- Level-indexed term-or-star symbols over the existing tensor alphabets. -/
abbrev Cube (L : ℕ) : Type := Fin L → CubeSymbol

/-- A leaf agrees with every fixed term; stars impose no condition. -/
@[expose] def Cube.HasLeaf {L : ℕ} (π : Cube L) (τ : Leaf L) : Prop :=
  ∀ ℓ, π ℓ = .star ∨ π ℓ = .term (τ ℓ)

/-- Finite leaf membership is executable in the specification. -/
instance Cube.instDecidableHasLeaf {L : ℕ} (π : Cube L) (τ : Leaf L) :
    Decidable (π.HasLeaf τ) :=
  inferInstanceAs (Decidable (∀ ℓ, π ℓ = .star ∨ π ℓ = .term (τ ℓ)))

/-- All leaves matching the fixed terms of the cube. -/
@[expose] def Cube.leaves {L : ℕ} (π : Cube L) : Finset (Leaf L) :=
  univ.filter π.HasLeaf

/-- Levels at which every term is allowed. -/
@[expose] def Cube.starLevels {L : ℕ} (π : Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = .star

/-- Levels fixed to the distinguished multiplication term. -/
@[expose] def Cube.P0Levels {L : ℕ} (π : Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = .term .P0

/-- Sum of the existing signed encoding products over the leaves of the cube. -/
@[expose] def Cube.val {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L) : ℤ :=
  ∑ τ ∈ π.leaves, encodeLeft τ a * encodeRight τ b

/-- The cube fixing each level to the given leaf. -/
@[expose] def Cube.ofLeaf {L : ℕ} (τ : Leaf L) : Cube L := fun ℓ => .term (τ ℓ)

/-- Fix one level to a multiplication label. -/
@[expose] def Cube.replace {L : ℕ} (π : Cube L) (ℓ : Fin L) (lam : Term) : Cube L :=
  Function.update π ℓ (.term lam)

/-- Replace the specified levels of a leaf with unrestricted stars. -/
@[expose] def Cube.starAt {L : ℕ} (F : Finset (Fin L)) (τ : Leaf L) : Cube L :=
  fun ℓ => if ℓ ∈ F then .star else .term (τ ℓ)

/-- Complete every star with the distinguished term, retaining all fixed terms. -/
@[expose] def Cube.starsToP0 {L : ℕ} (π : Cube L) : Leaf L :=
  fun ℓ => match π ℓ with
    | .term lam => lam
    | .star => .P0

variable {L : ℕ}

@[simp] theorem Cube.mem_leaves {π : Cube L} {τ : Leaf L} :
    τ ∈ π.leaves ↔ ∀ ℓ, π ℓ = .star ∨ π ℓ = .term (τ ℓ) := by
  simp only [Cube.leaves, mem_filter, mem_univ, true_and, Cube.HasLeaf]

/-- A fixed symbol determines the corresponding coordinate of every matching leaf. -/
theorem Cube.eq_of_mem_leaves {π : Cube L} {τ : Leaf L} (hτ : τ ∈ π.leaves)
    {ℓ : Fin L} {lam : Term} (h : π ℓ = .term lam) : τ ℓ = lam := by
  simpa [h, eq_comm] using Cube.mem_leaves.mp hτ ℓ

@[simp] theorem Cube.mem_starLevels {π : Cube L} {ℓ : Fin L} :
    ℓ ∈ π.starLevels ↔ π ℓ = .star := by
  simp [Cube.starLevels]

@[simp] theorem Cube.mem_P0Levels {π : Cube L} {ℓ : Fin L} :
    ℓ ∈ π.P0Levels ↔ π ℓ = .term .P0 := by
  simp [Cube.P0Levels]

/-- A level cannot be both a star and fixed to the distinguished term. -/
theorem Cube.disjoint_starLevels_P0Levels (π : Cube L) :
    Disjoint π.starLevels π.P0Levels := by
  rw [disjoint_left]
  intro ℓ hs hp
  rw [Cube.mem_starLevels] at hs
  rw [Cube.mem_P0Levels, hs] at hp
  cases hp

private def symbolTerms : CubeSymbol → Finset Term
  | .term lam => {lam}
  | .star => univ

private theorem leaves_eq_piFinset (π : Cube L) :
    π.leaves = Fintype.piFinset fun ℓ => symbolTerms (π ℓ) := by
  ext τ
  rw [Cube.mem_leaves, Fintype.mem_piFinset]
  refine forall_congr' fun ℓ => ?_
  cases h : π ℓ <;> simp [symbolTerms, eq_comm]

/-- Each star independently contributes ten possible labels, including at zero levels. -/
theorem Cube.card_leaves (π : Cube L) : π.leaves.card = 10 ^ π.starLevels.card := by
  have hc : ∀ ℓ, (symbolTerms (π ℓ)).card = if ℓ ∈ π.starLevels then 10 else 1 := by
    intro ℓ
    cases h : π ℓ <;> simp [symbolTerms, h, card_term]
  rw [leaves_eq_piFinset, Fintype.card_piFinset]
  simp only [hc]
  rw [prod_ite_mem_const, one_pow, mul_one]

/-- Fixing every coordinate gives a singleton leaf set. -/
@[simp] theorem Cube.leaves_ofLeaf (τ : Leaf L) : (Cube.ofLeaf τ).leaves = {τ} := by
  ext σ
  simp [Cube.ofLeaf, funext_iff, eq_comm]

@[simp] theorem Cube.starLevels_ofLeaf (τ : Leaf L) : (Cube.ofLeaf τ).starLevels = ∅ := by
  ext ℓ
  simp [Cube.ofLeaf]

@[simp] theorem Cube.P0Levels_ofLeaf (τ : Leaf L) :
    (Cube.ofLeaf τ).P0Levels =
    Cslib.Algorithms.MatrixMultiplication.Schonhage.P0Levels τ := by
  ext ℓ
  simp [Cube.ofLeaf]

/-- Replacing a star retains precisely the leaves that use the chosen term there. -/
theorem Cube.mem_leaves_replace {π : Cube L} {ℓ : Fin L} (hℓ : π ℓ = .star)
    (lam : Term) (τ : Leaf L) :
    τ ∈ (π.replace ℓ lam).leaves ↔ τ ∈ π.leaves ∧ τ ℓ = lam := by
  rw [Cube.mem_leaves, Cube.mem_leaves, Cube.replace,
    Function.forall_update_iff π fun k s => s = .star ∨ s = .term (τ k)]
  constructor
  · rintro ⟨hlam, h⟩
    refine ⟨fun k => ?_, by simpa [eq_comm] using hlam⟩
    by_cases hk : k = ℓ
    · exact Or.inl (hk ▸ hℓ)
    · exact h k hk
  · rintro ⟨h, rfl⟩
    exact ⟨Or.inr rfl, fun k _ => h k⟩

@[simp] theorem Cube.starLevels_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    (Cube.starAt F τ).starLevels = F := by
  ext ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

@[simp] theorem Cube.P0Levels_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    (Cube.starAt F τ).P0Levels =
    Cslib.Algorithms.MatrixMultiplication.Schonhage.P0Levels τ \ F := by
  ext ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

/-- Inserting stars never removes the original leaf from the represented set. -/
theorem Cube.mem_leaves_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    τ ∈ (Cube.starAt F τ).leaves := by
  rw [Cube.mem_leaves]
  intro ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

/-- Completing inserted stars with P0 recovers leaves that originally use P0 there. -/
theorem Cube.starsToP0_starAt {F : Finset (Fin L)} {τ : Leaf L}
    (h : F ⊆ Cslib.Algorithms.MatrixMultiplication.Schonhage.P0Levels τ) :
    (Cube.starAt F τ).starsToP0 = τ := by
  funext ℓ
  unfold Cube.starsToP0 Cube.starAt
  split_ifs with hℓ
  · exact (Cslib.Algorithms.MatrixMultiplication.Schonhage.mem_P0Levels.mp (h hℓ)).symm
  · rfl

/-- Fixing a coordinate removes it from the remaining stars. -/
theorem Cube.starLevels_replace (π : Cube L) (ℓ : Fin L) (lam : Term) :
    (π.replace ℓ lam).starLevels = π.starLevels.erase ℓ := by
  ext k
  by_cases hk : k = ℓ <;> simp [Cube.replace, hk]

/-- Fixing a coordinate can introduce P0 only at that coordinate. -/
theorem Cube.P0Levels_replace_subset (π : Cube L) (ℓ : Fin L) (lam : Term) :
    (π.replace ℓ lam).P0Levels ⊆ insert ℓ π.P0Levels := by
  intro k hk
  by_cases hkl : k = ℓ
  · exact mem_insert.2 (Or.inl hkl)
  · simpa [Cube.replace, hkl] using hk

/-- Completing stars always gives one of the represented leaves. -/
theorem Cube.starsToP0_mem_leaves (π : Cube L) : π.starsToP0 ∈ π.leaves := by
  rw [Cube.mem_leaves]
  intro ℓ
  unfold Cube.starsToP0
  cases π ℓ <;> simp

/-- Completion followed by restoring the original stars recovers the cube. -/
theorem Cube.starAt_starLevels_starsToP0 (π : Cube L) :
    Cube.starAt π.starLevels π.starsToP0 = π := by
  funext ℓ
  unfold Cube.starAt Cube.starsToP0
  cases h : π ℓ <;> simp [h]

/-- A cube with no stars fixes the leaf given by its completion. -/
theorem Cube.eq_ofLeaf_of_starLevels_eq_empty (π : Cube L) (hπ : π.starLevels = ∅) :
    π = Cube.ofLeaf π.starsToP0 := by
  conv_lhs => rw [← Cube.starAt_starLevels_starsToP0 π, hπ]
  funext ℓ
  simp [Cube.starAt, Cube.ofLeaf]

/-- Completion chooses P0 precisely at the stars and the coordinates already fixed to P0. -/
theorem P0Levels_starsToP0 (π : Cube L) :
    P0Levels π.starsToP0 = π.starLevels ∪ π.P0Levels := by
  ext ℓ
  rw [mem_P0Levels, mem_union, Cube.mem_starLevels, Cube.mem_P0Levels]
  unfold Cube.starsToP0
  cases h : π ℓ <;> simp

/-- Completion turns the disjoint star and P0 sets into one P0 set. -/
theorem card_P0Levels_starsToP0 (π : Cube L) :
    (P0Levels π.starsToP0).card = π.starLevels.card + π.P0Levels.card := by
  rw [P0Levels_starsToP0, card_union_of_disjoint (Cube.disjoint_starLevels_P0Levels π)]

/-- A fully fixed cube has the product of its two original encoded values. -/
@[simp] theorem Cube.val_ofLeaf (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) :
    Cube.val a b (Cube.ofLeaf τ) = encodeLeft τ a * encodeRight τ b := by
  rw [Cube.val, Cube.leaves_ofLeaf, sum_singleton]

/-- Partitioning a star by its term partitions the signed value, including cancellation. -/
theorem Cube.val_eq_sum_replace (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L)
    (ℓ : Fin L) (hℓ : π ℓ = .star) :
    Cube.val a b π = ∑ lam : Term, Cube.val a b (π.replace ℓ lam) := by
  unfold Cube.val
  rw [← sum_fiberwise π.leaves (fun τ => τ ℓ)]
  refine sum_congr rfl fun lam _ => sum_congr ?_ fun _ _ => rfl
  ext τ
  rw [mem_filter, Cube.mem_leaves_replace hℓ]

end Cslib.Algorithms.MatrixMultiplication.Schonhage
