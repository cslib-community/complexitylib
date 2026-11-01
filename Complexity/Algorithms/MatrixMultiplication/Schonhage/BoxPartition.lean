/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxValues

/-!
# Disjoint box decomposition of the contributing leaves

For an output with `m` inner levels and `t ≤ m`, pad each high-order leaf's P0 levels
from below. Its resulting box is unique. Different indexing sets give disjoint box
families, and their leaf sets partition exactly the high-order contributing leaves.
The remaining low-order leaves are explicit in `boxQuery`; `bilinearProduct_eq_boxQuery`
holds for arbitrary signed input arrays, including cancellation.

The level assignment is finite algebra from [AlmanWilliams2026, Lemmas 27–28], adapted
from [Lemma27_28.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec4/Lemma27_28.lean) at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
It uses the existing alphabets, encodings, contribution relation, signed leaf order
and alpha counts. There is no assumed native lookup, enumeration, layout or cost contract.
-/

public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Pad a restricted P0 set with the lowest remaining levels to the threshold size. -/
@[expose] def paddedLevels {L : ℕ} (m t : ℕ) (Q Z : Finset (Fin L)) : Finset (Fin L) :=
  Z ∪ lowest (m - t - Z.card) (Q \ Z)

/-- Levels preceding every omitted level; if none are omitted this is all of `Q`. -/
@[expose] def initialLevels {L : ℕ} (Q V : Finset (Fin L)) : Finset (Fin L) :=
  Q.filter fun ℓ => ∀ ℓ' ∈ Q \ V, ℓ < ℓ'

/-- Cubes for an output and an indexing set, with stars, fixed P0, nine-way and private regions. -/
@[expose] def boxesAt {L : ℕ} (η : OutStr L) (V : Finset (Fin L)) : Finset (Cube L) :=
  univ.filter fun π => ∀ ℓ,
    (ℓ ∈ initialLevels (innerSetO η) V → π ℓ = .star) ∧
    (ℓ ∈ V \ initialLevels (innerSetO η) V → π ℓ = .term .P0) ∧
    (ℓ ∈ innerSetO η \ V → ∃ i j, π ℓ = .term (.P i j)) ∧
    (ℓ ∉ innerSetO η → π ℓ = .term (privateLeaf η ℓ))

/-- Eligible indexing sets have the required cardinality within the output's inner levels. -/
@[expose] def boxLevelSets {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Finset (Fin L)) :=
  (innerSetO η).powersetCard (m - t)

/-- The contributing leaves below the order threshold, retained explicitly in every query. -/
@[expose] def lowLeaves {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Leaf L) :=
  univ.filter fun τ => Leaf.Contributes τ η ∧ order m τ < (t : ℤ)

/-- Complete finite query expression: low-order products plus the values of the output's boxes. -/
@[expose] def boxQuery {L : ℕ} (m t : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (η : OutStr L) : ℤ :=
  ∑ τ ∈ lowLeaves m t η, encodeLeft τ a * encodeRight τ b +
    ∑ V ∈ boxLevelSets m t η, ∑ π ∈ boxesAt η V, Cube.val a b π

variable {L : ℕ}

/-- The P0 coordinates of a leaf lying in the selected levels. -/
@[expose] def P0LevelsWithin (Q : Finset (Fin L)) (τ : Leaf L) : Finset (Fin L) :=
  Q.filter fun ℓ => τ ℓ = Term.P0

private lemma contributes_iff_eq_privateLeaf (η : OutStr L) (τ : Leaf L) :
    Leaf.Contributes τ η ↔ ∀ ℓ, ℓ ∉ innerSetO η → τ ℓ = privateLeaf η ℓ := by
  refine forall_congr' fun ℓ => ?_
  rw [Term.contributes_iff, mem_innerSetO]
  exact or_iff_not_imp_left

private lemma privateLeaf_ne_P0 {η : OutStr L} {ℓ : Fin L} (hℓ : ℓ ∉ innerSetO η) :
    privateLeaf η ℓ ≠ Term.P0 :=
  fun h => hℓ (mem_innerSetO.2 ((OutVar.privateTerm_eq_P0_iff _).1 h))

private lemma P0LevelsWithin_subset (Q : Finset (Fin L)) (τ : Leaf L) : P0LevelsWithin Q τ ⊆ Q :=
  filter_subset _ _

private lemma P0Levels_eq_P0LevelsWithin (η : OutStr L) (τ : Leaf L) (hτ : Leaf.Contributes τ η) :
    P0Levels τ = P0LevelsWithin (innerSetO η) τ := by
  ext ℓ
  rw [P0LevelsWithin, mem_filter, mem_P0Levels]
  exact ⟨fun h => ⟨P0Levels_subset hτ (mem_P0Levels.2 h), h⟩, fun h => h.2⟩

/-- Restricted P0 coordinates determine the order of a contributing leaf. -/
theorem order_eq_sub_card_P0LevelsWithin (m : ℕ) (η : OutStr L) (τ : Leaf L)
    (hτ : Leaf.Contributes τ η) :
    order m τ = (m : ℤ) - ((P0LevelsWithin (innerSetO η) τ).card : ℤ) := by
  rw [order, P0Levels_eq_P0LevelsWithin η τ hτ]

private lemma card_P0LevelsWithin_le {m t : ℕ} {η : OutStr L} {τ : Leaf L} (hτ : Leaf.Contributes
  τ η)
    (hord : (t : ℤ) ≤ order m τ) : (P0LevelsWithin (innerSetO η) τ).card ≤ m - t := by
  have := order_eq_sub_card_P0LevelsWithin m η τ hτ
  omega

/-- Padding stays within its ambient set. -/
theorem paddedLevels_subset (m t : ℕ) {Q Z : Finset (Fin L)} (hZ : Z ⊆ Q) : paddedLevels m t Q Z ⊆
  Q :=
  union_subset hZ ((lowest_subset _ _).trans sdiff_subset)

/-- Padding has the prescribed size under the explicit cardinality premises. -/
theorem card_paddedLevels {m t : ℕ} (ht : t ≤ m) {Q Z : Finset (Fin L)} (hQ : Q.card = m) (hZ : Z
  ⊆ Q)
    (hZc : Z.card ≤ m - t) : (paddedLevels m t Q Z).card = m - t := by
  have hdisj : Disjoint Z (lowest (m - t - Z.card) (Q \ Z)) :=
    disjoint_of_subset_right (lowest_subset _ _) disjoint_sdiff
  rw [paddedLevels, card_union_of_disjoint hdisj, card_lowest, card_sdiff_of_subset hZ, hQ]
  omega

private lemma paddedLevels_sdiff_lt (m t : ℕ) (Q Z : Finset (Fin L)) :
    ∀ ℓ ∈ paddedLevels m t Q Z \ Z, ∀ ℓ' ∈ Q \ paddedLevels m t Q Z, ℓ < ℓ' := by
  intro ℓ hℓ ℓ' hℓ'
  obtain ⟨hV, hZ⟩ := mem_sdiff.1 hℓ
  obtain ⟨hQ', hV'⟩ := mem_sdiff.1 hℓ'
  obtain ⟨hZ', hlow'⟩ := not_or.1 (mt mem_union.2 hV')
  exact lowest_lt ((mem_union.1 hV).resolve_left hZ)
    (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hQ', hZ'⟩, hlow'⟩)

/-- The initial levels are all levels at the boundary, or those below the first omission. -/
theorem initialLevels_eq (Q V : Finset (Fin L)) :
    initialLevels Q Q = Q ∧ ∀ h : (Q \ V).Nonempty, initialLevels Q V = Q.filter fun ℓ => ℓ < (Q \
      V).min' h := by
  refine ⟨by simp [initialLevels], fun h => filter_congr fun ℓ _ => ?_⟩
  rw [lt_min'_iff]

/-- The initial levels lie inside the selected set. -/
theorem initialLevels_subset (Q V : Finset (Fin L)) : initialLevels Q V ⊆ V := by
  intro ℓ hℓ
  by_contra hV
  exact lt_irrefl ℓ ((mem_filter.1 hℓ).2 ℓ (mem_sdiff.2 ⟨(mem_filter.1 hℓ).1, hV⟩))

private lemma mem_initialLevels_of_le {Q V : Finset (Fin L)} {ℓ ℓ' : Fin L} (hℓ : ℓ ∈
  initialLevels Q V)
    (hℓ' : ℓ' ∈ Q) (hle : ℓ' ≤ ℓ) : ℓ' ∈ initialLevels Q V :=
  mem_filter.2 ⟨hℓ', fun x hx => hle.trans_lt ((mem_filter.1 hℓ).2 x hx)⟩

private lemma sdiff_initialLevels_subset_iff {Q V Z : Finset (Fin L)} (hV : V ⊆ Q) :
    V \ initialLevels Q V ⊆ Z ↔ ∀ ℓ ∈ V \ Z, ∀ ℓ' ∈ Q \ V, ℓ < ℓ' := by
  constructor
  · intro h ℓ hℓ ℓ' hℓ'
    obtain ⟨hℓV, hℓZ⟩ := mem_sdiff.1 hℓ
    have hℓF : ℓ ∈ initialLevels Q V := by
      by_contra hF
      exact hℓZ (h (mem_sdiff.2 ⟨hℓV, hF⟩))
    exact (mem_filter.1 hℓF).2 ℓ' hℓ'
  · intro h ℓ hℓ
    obtain ⟨hℓV, hℓF⟩ := mem_sdiff.1 hℓ
    by_contra hZ
    exact hℓF (mem_filter.2 ⟨hV hℓV, h ℓ (mem_sdiff.2 ⟨hℓV, hZ⟩)⟩)

section boxesAt

variable {η : OutStr L} {V : Finset (Fin L)} {π : Cube L} {ℓ : Fin L}

private lemma boxesAt_star (hπ : π ∈ boxesAt η V) (hℓ : ℓ ∈ initialLevels (innerSetO η) V) : π ℓ =
  CubeSymbol.star :=
  ((mem_filter.1 hπ).2 ℓ).1 hℓ

private lemma boxesAt_P0 (hπ : π ∈ boxesAt η V) (hℓ : ℓ ∈ V \ initialLevels (innerSetO η) V) :
    π ℓ = CubeSymbol.term Term.P0 :=
  ((mem_filter.1 hπ).2 ℓ).2.1 hℓ

private lemma boxesAt_nine (hπ : π ∈ boxesAt η V) (hℓ : ℓ ∈ innerSetO η \ V) :
    ∃ i j, π ℓ = CubeSymbol.term (Term.P i j) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.1 hℓ

private lemma boxesAt_outside (hπ : π ∈ boxesAt η V) (hℓ : ℓ ∉ innerSetO η) :
    π ℓ = CubeSymbol.term (privateLeaf η ℓ) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.2 hℓ

private lemma level_cases (Q V : Finset (Fin L)) (ℓ : Fin L) :
    ℓ ∈ initialLevels Q V ∨ ℓ ∈ V \ initialLevels Q V ∨ ℓ ∈ Q \ V ∨ ℓ ∉ Q := by
  simp only [mem_sdiff]
  tauto

/-- The stars of a family member are exactly its initial levels. -/
theorem boxesAt_starLevels (hπ : π ∈ boxesAt η V) : Cube.starLevels π = initialLevels (innerSetO
  η) V := by
  ext ℓ
  rw [Cube.mem_starLevels]
  refine ⟨fun h => ?_, boxesAt_star hπ⟩
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · exact hℓ
  · simp [boxesAt_P0 hπ hℓ] at h
  · obtain ⟨i, j, hij⟩ := boxesAt_nine hπ hℓ
    simp [hij] at h
  · simp [boxesAt_outside hπ hℓ] at h

/-- Fixed P0 coordinates occupy the rest of the selected levels. -/
theorem boxesAt_P0Levels (hπ : π ∈ boxesAt η V) : Cube.P0Levels π = V \ initialLevels (innerSetO
  η) V := by
  ext ℓ
  rw [Cube.mem_P0Levels]
  refine ⟨fun h => ?_, boxesAt_P0 hπ⟩
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · simp [boxesAt_star hπ hℓ] at h
  · exact hℓ
  · obtain ⟨i, j, hij⟩ := boxesAt_nine hπ hℓ
    simp [hij] at h
  · rw [boxesAt_outside hπ hℓ] at h
    exact absurd (CubeSymbol.term.inj h) (privateLeaf_ne_P0 hℓ)

/-- A family member recovers its indexing set from its stars and P0 symbols. -/
theorem boxesAt_starLevels_union_P0Levels (hπ : π ∈ boxesAt η V) :
    Cube.starLevels π ∪ Cube.P0Levels π = V := by
  rw [boxesAt_starLevels hπ, boxesAt_P0Levels hπ, union_sdiff_of_subset (initialLevels_subset _ _)]

private lemma boxesAt_ext {π' : Cube L} (hπ : π ∈ boxesAt η V) (hπ' : π' ∈ boxesAt η V)
    (h : ∀ ℓ ∈ innerSetO η \ V, π ℓ = π' ℓ) : π = π' := by
  funext ℓ
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · rw [boxesAt_star hπ hℓ, boxesAt_star hπ' hℓ]
  · rw [boxesAt_P0 hπ hℓ, boxesAt_P0 hπ' hℓ]
  · exact h ℓ hℓ
  · rw [boxesAt_outside hπ hℓ, boxesAt_outside hπ' hℓ]

private lemma boxesAt_eq_term_of_leaf (hπ : π ∈ boxesAt η V) {τ : Leaf L} (hτ : τ ∈ Cube.leaves π)
    (hℓ : ℓ ∈ innerSetO η \ V) : π ℓ = CubeSymbol.term (τ ℓ) := by
  obtain ⟨i, j, hij⟩ := boxesAt_nine hπ hℓ
  rw [hij, Cube.eq_of_mem_leaves hτ hij]

end boxesAt

private def allowed (η : OutStr L) (V : Finset (Fin L)) (ℓ : Fin L) : Finset CubeSymbol :=
  univ.filter fun s =>
    (ℓ ∈ initialLevels (innerSetO η) V → s = CubeSymbol.star) ∧
    (ℓ ∈ V \ initialLevels (innerSetO η) V → s = CubeSymbol.term Term.P0) ∧
    (ℓ ∈ innerSetO η \ V → ∃ i j, s = CubeSymbol.term (Term.P i j)) ∧
    (ℓ ∉ innerSetO η → s = CubeSymbol.term (privateLeaf η ℓ))

private lemma boxesAt_eq_piFinset (η : OutStr L) (V : Finset (Fin L)) :
    boxesAt η V = Fintype.piFinset (allowed η V) := by
  ext π
  simp [boxesAt, allowed, Fintype.mem_piFinset]

private lemma card_allowed (η : OutStr L) (V : Finset (Fin L)) (hV : V ⊆ innerSetO η)
    (ℓ : Fin L) : (allowed η V ℓ).card = if ℓ ∈ innerSetO η \ V then 9 else 1 := by
  have hnine :
      (univ.filter fun s : CubeSymbol => ∃ i j, s = CubeSymbol.term (Term.P i j)).card = 9 := by
    decide
  have hinitialLevels := @initialLevels_subset L (innerSetO η) V ℓ
  have hVQ := @hV ℓ
  unfold allowed
  by_cases hF : ℓ ∈ initialLevels (innerSetO η) V
  · simp [hF, hinitialLevels hF, hVQ (hinitialLevels hF), filter_eq']
  by_cases hℓV : ℓ ∈ V
  · simp [hF, hℓV, hVQ hℓV, filter_eq']
  by_cases hℓQ : ℓ ∈ innerSetO η
  · simp [hF, hℓV, hℓQ, hnine]
  · simp [hF, hℓV, hℓQ, filter_eq']

/-- There are nine choices at each free inner coordinate and one at every other coordinate. -/
theorem card_boxesAt (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (V : Finset (Fin L)) (hV : V ∈ boxLevelSets m t η) : (boxesAt η V).card = 9 ^ t := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [boxesAt_eq_piFinset η V, Fintype.card_piFinset]
  simp only [card_allowed η V hVQ]
  rw [prod_ite_mem_const, one_pow, mul_one, card_sdiff_of_subset hVQ, hη, hVc,
    Nat.sub_sub_self ht]

/-- Every member of an eligible output family satisfies the global box conditions. -/
theorem boxesAt_isBox {m t : ℕ} {η : OutStr L} {V : Finset (Fin L)} (hV : V ∈ boxLevelSets m t η)
  {π : Cube L}
    (hπ : π ∈ boxesAt η V) : IsBox m t π := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [IsBox, boxesAt_starLevels hπ, boxesAt_P0Levels hπ, add_comm,
    card_sdiff_add_card_eq_card (initialLevels_subset _ _)]
  refine ⟨hVc.le, fun ℓ hℓ ℓ' hℓ' => ?_⟩
  obtain ⟨hℓ'V, hℓ'F⟩ := mem_sdiff.1 hℓ'
  by_contra hlt
  exact hℓ'F (mem_initialLevels_of_le hℓ (hVQ hℓ'V) (not_lt.1 hlt))

/-- Different indexing sets give disjoint families of cubes. -/
theorem boxesAt_pairwiseDisjoint (η : OutStr L) (s : Set (Finset (Fin L))) :
    s.PairwiseDisjoint (boxesAt η) :=
  fun _ _ _ _ hne => disjoint_left.2 fun _ hπ hπ' =>
    hne ((boxesAt_starLevels_union_P0Levels hπ).symm.trans (boxesAt_starLevels_union_P0Levels hπ'))

private lemma starAt_mem_boxesAt {η : OutStr L} {V : Finset (Fin L)} {τ : Leaf L}
    (hτ : Leaf.Contributes τ η) (hVZ : V \ initialLevels (innerSetO η) V ⊆ P0LevelsWithin
      (innerSetO η) τ)
    (hZV : P0LevelsWithin (innerSetO η) τ ⊆ V) : Cube.starAt (initialLevels (innerSetO η) V) τ ∈
      boxesAt η V := by
  refine mem_filter.2
    ⟨mem_univ _, fun ℓ => ⟨fun hF => ite_eq_left hF, fun hVF => ?_, fun hQV => ?_, fun hQ => ?_⟩⟩
  · -- at a level of `V ∖ F_V`, which is a level of `Z`, the leaf chooses `P₀`
    rw [Cube.starAt, ite_eq_right (mem_sdiff.1 hVF).2, (mem_filter.1 (hVZ hVF)).2]
  · -- at a level of `Q ∖ V`, which is not a level of `Z`, the leaf chooses another term
    obtain ⟨hQ, hV⟩ := mem_sdiff.1 hQV
    rw [Cube.starAt, ite_eq_right fun hF => hV (initialLevels_subset _ _ hF)]
    cases hterm : τ ℓ with
    | P i j => exact ⟨i, j, rfl⟩
    | P0 => exact absurd (hZV (mem_filter.2 ⟨hQ, hterm⟩)) hV
  · -- outside `Q` the leaf agrees with the private leaf
    rw [Cube.starAt, ite_eq_right fun hF : ℓ ∈ initialLevels (innerSetO η) V => hQ (mem_filter.1
      hF).1,
      (contributes_iff_eq_privateLeaf η τ).1 hτ ℓ hQ]

/-- Assign a cube by starring the initial levels of the padded P0 set. -/
@[expose] def boxOfLeaf (m t : ℕ) (η : OutStr L) (τ : Leaf L) : Cube L :=
  Cube.starAt (initialLevels (innerSetO η) (paddedLevels m t (innerSetO η) (P0LevelsWithin
    (innerSetO η) τ))) τ

/-- The assignment retains its original leaf. -/
theorem mem_leaves_boxOfLeaf (m t : ℕ) (η : OutStr L) (τ : Leaf L) :
    τ ∈ Cube.leaves (boxOfLeaf m t η τ) :=
  Cube.mem_leaves_starAt _ τ

/-- The assigned cube belongs to the family indexed by the padded P0 set. -/
theorem boxOfLeaf_mem_boxesAt (m t : ℕ) {η : OutStr L} {τ : Leaf L} (hτ : Leaf.Contributes τ η) :
    boxOfLeaf m t η τ ∈ boxesAt η (paddedLevels m t (innerSetO η) (P0LevelsWithin (innerSetO η)
      τ)) :=
  starAt_mem_boxesAt hτ
    ((sdiff_initialLevels_subset_iff (paddedLevels_subset m t (P0LevelsWithin_subset _ τ))).2
      (paddedLevels_sdiff_lt m t _ _))
    subset_union_left

/-- Leaf incidence in a family is equivalent to the two P0-set inclusions. -/
theorem exists_mem_boxesAt_leaf_iff {η : OutStr L} {V : Finset (Fin L)} (hV : V ⊆ innerSetO η)
    {τ : Leaf L} (hτ : Leaf.Contributes τ η) :
    (∃ π ∈ boxesAt η V, τ ∈ Cube.leaves π) ↔
      V \ initialLevels (innerSetO η) V ⊆ P0LevelsWithin (innerSetO η) τ ∧ P0LevelsWithin
        (innerSetO η) τ ⊆ V := by
  constructor
  · rintro ⟨π, hπ, hτπ⟩
    refine ⟨fun ℓ hℓ => mem_filter.2 ⟨hV (mem_sdiff.1 hℓ).1, ?_⟩, fun ℓ hℓ => ?_⟩
    · exact Cube.eq_of_mem_leaves hτπ (boxesAt_P0 hπ hℓ)
    · by_contra hℓV
      obtain ⟨hℓQ, hterm⟩ := mem_filter.1 hℓ
      obtain ⟨i, j, hij⟩ := boxesAt_nine hπ (mem_sdiff.2 ⟨hℓQ, hℓV⟩)
      simp [Cube.eq_of_mem_leaves hτπ hij] at hterm
  · exact fun ⟨hVZ, hZV⟩ => ⟨_, starAt_mem_boxesAt hτ hVZ hZV, Cube.mem_leaves_starAt _ τ⟩

/-- Within a single family, a leaf determines its cube. -/
theorem boxesAt_leaf_unique {η : OutStr L} {V : Finset (Fin L)} {τ : Leaf L} {π π' : Cube L}
    (hπ : π ∈ boxesAt η V) (hτπ : τ ∈ Cube.leaves π) (hπ' : π' ∈ boxesAt η V) (hτπ' : τ ∈
      Cube.leaves π') :
    π = π' :=
  boxesAt_ext hπ hπ' fun _ hℓ =>
    (boxesAt_eq_term_of_leaf hπ hτπ hℓ).trans (boxesAt_eq_term_of_leaf hπ' hτπ' hℓ).symm

/-- The prescribed padding is the unique set satisfying both incidence inclusions. -/
theorem paddedLevels_unique {L : ℕ} (m t : ℕ) (ht : t ≤ m) (Q Z : Finset (Fin L)) (hQ : Q.card = m)
    (hZ : Z ⊆ Q) (hZc : Z.card ≤ m - t) (V : Finset (Fin L)) :
    (V ⊆ Q ∧ V.card = m - t ∧ V \ initialLevels Q V ⊆ Z ∧ Z ⊆ V) ↔ V = paddedLevels m t Q Z := by
  constructor
  · rintro ⟨hVQ, hVc, hVZ, hZV⟩
    have hrest : (Q \ Z) \ (V \ Z) = Q \ V := sdiff_sdiff_sdiff_cancel_right hZV
    have hlow := eq_lowest_of_lt (sdiff_subset_sdiff hVQ (le_refl Z))
      (hrest ▸ (sdiff_initialLevels_subset_iff hVQ).1 hVZ)
    rw [card_sdiff_of_subset hZV, hVc] at hlow
    rw [paddedLevels, ← hlow, union_sdiff_of_subset hZV]
  · rintro rfl
    have hVQ := paddedLevels_subset m t hZ
    exact ⟨hVQ, card_paddedLevels ht hQ hZ hZc, (sdiff_initialLevels_subset_iff hVQ).2
      (paddedLevels_sdiff_lt m t Q Z),
      subset_union_left⟩

/-- The families cover exactly the contributing leaves above the threshold. -/
theorem contributes_high_iff_mem_box_leaves {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη :
  (innerSetO η).card = m)
    (τ : Leaf L) :
    (Leaf.Contributes τ η ∧ (t : ℤ) ≤ order m τ) ↔
      ∃ π ∈ (boxLevelSets m t η).biUnion (boxesAt η), τ ∈ Cube.leaves π := by
  constructor
  · -- "Conversely, a leaf τ contributing to w, of order at least t," is a leaf of its box.
    rintro ⟨hτ, hord⟩
    refine ⟨boxOfLeaf m t η τ, mem_biUnion.2 ⟨_, mem_powersetCard.2 ?_, boxOfLeaf_mem_boxesAt m t
      hτ⟩,
      mem_leaves_boxOfLeaf m t η τ⟩
    exact ⟨paddedLevels_subset m t (P0LevelsWithin_subset _ τ),
      card_paddedLevels ht hη (P0LevelsWithin_subset _ τ) (card_P0LevelsWithin_le hτ hord)⟩
  · -- "Every leaf of a box of 𝓑_V agrees with the private leaf of w outside Q, so it contributes
    rintro ⟨π, hπ, hτπ⟩
    obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
    exact ⟨(contributes_iff_eq_privateLeaf η τ).2 fun ℓ hℓ =>
        Cube.eq_of_mem_leaves hτπ (boxesAt_outside hπV hℓ),
      le_order_of_mem_leaves ht (boxesAt_isBox hV hπV) hτπ⟩

private lemma eq_paddedLevels_of_mem_leaves {m t : ℕ} (ht : t ≤ m) {η : OutStr L}
    (hη : (innerSetO η).card = m) {τ : Leaf L} (hτ : Leaf.Contributes τ η)
    (hord : (t : ℤ) ≤ order m τ) {V : Finset (Fin L)} (hV : V ∈ boxLevelSets m t η) {π : Cube L}
    (hπ : π ∈ boxesAt η V) (hτπ : τ ∈ Cube.leaves π) :
    V = paddedLevels m t (innerSetO η) (P0LevelsWithin (innerSetO η) τ) := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  obtain ⟨hVZ, hZV⟩ := (exists_mem_boxesAt_leaf_iff hVQ hτ).1 ⟨π, hπ, hτπ⟩
  exact (paddedLevels_unique m t ht _ _ hη (P0LevelsWithin_subset _ τ) (card_P0LevelsWithin_le hτ
    hord) V).1 ⟨hVQ, hVc, hVZ, hZV⟩

/-- Each high-order contributing leaf lies in exactly one output box. -/
theorem existsUnique_box_containing_leaf {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη :
  (innerSetO η).card = m)
    (τ : Leaf L) (hτ : Leaf.Contributes τ η) (hord : (t : ℤ) ≤ order m τ) :
    ∃! π : Cube L, π ∈ (boxLevelSets m t η).biUnion (boxesAt η) ∧ τ ∈ Cube.leaves π := by
  obtain ⟨π, hπ, hτπ⟩ := (contributes_high_iff_mem_box_leaves m t ht η hη τ).1 ⟨hτ, hord⟩
  refine ⟨π, ⟨hπ, hτπ⟩, ?_⟩
  rintro π' ⟨hπ', hτπ'⟩
  obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
  obtain ⟨V', hV', hπV'⟩ := mem_biUnion.1 hπ'
  obtain rfl : V' = V := (eq_paddedLevels_of_mem_leaves ht hη hτ hord hV' hπV' hτπ').trans
    (eq_paddedLevels_of_mem_leaves ht hη hτ hord hV hπV hτπ).symm
  exact boxesAt_leaf_unique hπV' hτπ' hπV hτπ

/-- A sum splits into low-order leaves and the disjoint output boxes. -/
theorem sum_contributing_eq_low_add_boxes {G : Type*} [AddCommMonoid G] (m t : ℕ) (ht : t ≤ m)
    (η : OutStr L) (hη : (innerSetO η).card = m) (g : Leaf L → G) :
    ∑ τ : Leaf L with Leaf.Contributes τ η, g τ =
      ∑ τ ∈ lowLeaves m t η, g τ + ∑ V ∈ boxLevelSets m t η, ∑ π ∈ boxesAt η V, ∑ τ ∈ Cube.leaves
        π, g τ := by
  have hdisjoint :
      (((boxLevelSets m t η).biUnion (boxesAt η) : Finset (Cube L)) : Set (Cube L)).PairwiseDisjoint
        Cube.leaves := by
    intro π hπ π' hπ' hne
    rw [Function.onFun, disjoint_left]
    intro τ hτ hτ'
    obtain ⟨hc, hord⟩ := (contributes_high_iff_mem_box_leaves m t ht η hη τ).2 ⟨π, hπ, hτ⟩
    exact hne ((existsUnique_box_containing_leaf m t ht η hη τ hc hord).unique ⟨hπ, hτ⟩ ⟨hπ', hτ'⟩)
  have hhigh : ((boxLevelSets m t η).biUnion (boxesAt η)).biUnion Cube.leaves =
      univ.filter fun τ : Leaf L => Leaf.Contributes τ η ∧ ¬ order m τ < (t : ℤ) := by
    ext τ
    rw [mem_biUnion, mem_filter, not_lt, ← contributes_high_iff_mem_box_leaves m t ht η hη τ]
    simp
  rw [← sum_biUnion (boxesAt_pairwiseDisjoint η _), ← sum_biUnion hdisjoint, hhigh, lowLeaves,
    ← filter_filter, ← filter_filter, sum_filter_add_sum_filter_not]

/-- The signed bilinear product equals the complete query expression. -/
theorem bilinearProduct_eq_boxQuery (m t : ℕ) (ht : t ≤ m) (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (η : OutStr L) (hη : (innerSetO η).card = m) : bilinearProduct a b η = boxQuery m t a b η :=
  sum_contributing_eq_low_add_boxes m t ht η hη fun τ => encodeLeft τ a * encodeRight τ b

/-- Low-order leaves and box leaves account for each contributing leaf once. -/
theorem card_low_add_box_leaves (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    (lowLeaves m t η).card + ∑ π ∈ (boxLevelSets m t η).biUnion (boxesAt η), (Cube.leaves π).card
      = 10 ^ m := by
  have hsplit := sum_contributing_eq_low_add_boxes m t ht η hη fun _ => 1
  rw [← card_eq_sum_ones, card_filter_contributes η hη] at hsplit
  rw [hsplit, sum_biUnion (boxesAt_pairwiseDisjoint η _)]
  simp

private lemma lowLeaves_eq_biUnion (m t : ℕ) (η : OutStr L) (hη : (innerSetO η).card = m) :
    lowLeaves m t η = (range t).biUnion fun d =>
      univ.filter fun τ : Leaf L => Leaf.Contributes τ η ∧ order m τ = d := by
  ext τ
  simp only [lowLeaves, mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
  constructor
  · rintro ⟨hτ, hlt⟩
    have hnonneg := order_nonneg hη hτ
    exact ⟨(order m τ).toNat, by omega, hτ, (Int.toNat_of_nonneg hnonneg).symm⟩
  · rintro ⟨d, hd, hτ, heq⟩
    exact ⟨hτ, by omega⟩

/-- The exact query counts are given by the existing alpha function. -/
theorem box_query_counts {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    (lowLeaves m t η).card = ∑ d ∈ range t, alpha m d ∧
      ∑ V ∈ boxLevelSets m t η, (boxesAt η V).card = alpha m t ∧
      ((boxLevelSets m t η).biUnion (boxesAt η)).card = alpha m t := by
  have hsum : ∑ V ∈ boxLevelSets m t η, (boxesAt η V).card = alpha m t := by
    rw [sum_congr rfl fun V hV => card_boxesAt m t ht η hη V hV, sum_const, boxLevelSets,
      card_powersetCard, hη, Nat.choose_symm ht, smul_eq_mul, alpha]
  refine ⟨?_, hsum, ?_⟩
  · -- "α_d leaves of order d contribute to w"
    rw [lowLeaves_eq_biUnion m t η hη, card_biUnion]
    · exact sum_congr rfl fun d _ => card_contributing_of_order η hη d
    · intro d _ d' _ hne
      rw [Function.onFun, disjoint_left]
      intro τ hd hd'
      exact hne (by exact_mod_cast (mem_filter.1 hd).2.2.symm.trans (mem_filter.1 hd').2.2)
  · rw [card_biUnion (boxesAt_pairwiseDisjoint η _), hsum]

/-- An output box belongs to the global box set at its actual star count. -/
theorem mem_boxesWithStars_of_mem_boxesAt {L : ℕ} (m t : ℕ) (η : OutStr L) (V : Finset (Fin L))
  (hV : V ∈ boxLevelSets m t η)
    (π : Cube L) (hπ : π ∈ boxesAt η V) : π ∈ boxesWithStars L m t (initialLevels (innerSetO η)
      V).card :=
  mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, boxesAt_isBox hV hπ⟩, by rw [boxesAt_starLevels hπ]⟩

end Cslib.Algorithms.MatrixMultiplication.Schonhage
