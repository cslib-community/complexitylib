/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxesFromLeaves
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Values

/-!
# Values of sparse native box-query leaves

The query visits only contributing leaves of order at most the threshold. A lower-order
leaf supplies its direct signed product; an exact-threshold leaf supplies the stored value
of its unique canonical box. Existing finite box partition and indexing results identify
the resulting sum with the original bilinear product.

These finite statements reuse [AlmanWilliams2026, Section 4.2] through `BoxesFromLeaves`.
They introduce no enumeration, layout, execution or timing assumption.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The contributing leaves actually visited by the threshold-pruned query traversal. -/
@[expose] def queryLeaves {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Leaf L) :=
  univ.filter fun τ => Leaf.Contributes τ η ∧ order m τ ≤ (t : ℤ)

/-- A low leaf is evaluated directly; a threshold leaf selects its existing canonical box. -/
@[expose] def leafQueryValue {L : ℕ} (m t : ℕ) (η : OutStr L)
    (a b : Leaf L → ℤ) (τ : Leaf L) : ℤ :=
  if order m τ < (t : ℤ) then a τ * b τ else
    BoxTable.slotValue a b (BoxTable.cubeSlot (starBelow η τ))

/-- Mathematical value accumulated by the complete sparse query. -/
@[expose] def queryValue {L : ℕ} (m t : ℕ) (η : OutStr L) (a b : Leaf L → ℤ) : ℤ :=
  ∑ τ ∈ queryLeaves m t η, leafQueryValue m t η a b τ

@[simp] theorem mem_queryLeaves {L m t : ℕ} {η : OutStr L} {τ : Leaf L} :
    τ ∈ queryLeaves m t η ↔ Leaf.Contributes τ η ∧ order m τ ≤ (t : ℤ) := by
  simp [queryLeaves]

private def thresholdLeaves {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Leaf L) :=
  univ.filter fun τ => Leaf.Contributes τ η ∧ order m τ = (t : ℤ)

private theorem starBelow_isBox {L m t : ℕ} {η : OutStr L} {τ : Leaf L}
    (hτ : Leaf.Contributes τ η) (hord : order m τ = (t : ℤ)) :
    IsBox m t (starBelow η τ) := by
  obtain ⟨V, hV, hπ⟩ := mem_biUnion.mp (starBelow_mem hτ hord)
  exact boxesAt_isBox hV hπ

private theorem slotValue_cubeSlot {L m t : ℕ} (a b : Leaf L → ℤ) (π : Cube L)
    (hπ : IsBox m t π) :
    BoxTable.slotValue a b (BoxTable.cubeSlot π) = boxValue a b π.starLevels.card π := by
  rw [BoxTable.slotValue, BoxTable.slotCube_cubeSlot hπ]
  congr 1
  exact BoxTable.recordStars_slot _ _

/-- Each exact-threshold contributing leaf selects one output box, with no repetitions. -/
theorem sum_threshold_values {L m t : ℕ} (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) (a b : Leaf L → ℤ) :
    (∑ τ ∈ univ.filter (fun τ : Leaf L =>
      Leaf.Contributes τ η ∧ order m τ = (t : ℤ)),
        BoxTable.slotValue a b (BoxTable.cubeSlot (starBelow η τ))) =
      ∑ π ∈ (boxLevelSets m t η).biUnion (boxesAt η),
        boxValue a b π.starLevels.card π := by
  refine sum_bij (fun τ _ => starBelow η τ) ?_ ?_ ?_ ?_
  · intro τ hτ
    obtain ⟨hc, ho⟩ := (mem_filter.mp hτ).2
    exact starBelow_mem hc ho
  · intro τ _ τ' _ h
    have hh := congrArg Cube.starsToP0 h
    simpa only [starsToP0_starBelow] using hh
  · intro π hπ
    obtain ⟨τ, ⟨⟨hc, ho⟩, hτ⟩, _⟩ := existsUnique_starBelow_eq ht hη hπ
    exact ⟨τ, mem_filter.mpr ⟨mem_univ _, hc, ho⟩, hτ⟩
  · intro τ hτ
    obtain ⟨hc, ho⟩ := (mem_filter.mp hτ).2
    exact slotValue_cubeSlot a b _ (starBelow_isBox hc ho)

/-- The sparse traversal's exact sum is the existing low-products-plus-box-values formula. -/
theorem queryValue_eq_low_add_boxes {L m t : ℕ} (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) (a b : Leaf L → ℤ) :
    queryValue m t η a b =
      (∑ τ ∈ lowLeaves m t η, a τ * b τ) +
        ∑ π ∈ (boxLevelSets m t η).biUnion (boxesAt η),
          boxValue a b π.starLevels.card π := by
  have hsplit : queryLeaves m t η = lowLeaves m t η ∪ thresholdLeaves m t η := by
    ext τ
    simp only [mem_queryLeaves, lowLeaves, thresholdLeaves, mem_filter, mem_univ,
      true_and, mem_union]
    constructor
    · rintro ⟨hc, ho⟩
      by_cases hlt : order m τ < (t : ℤ)
      · exact Or.inl ⟨hc, hlt⟩
      · exact Or.inr ⟨hc, by omega⟩
    · rintro (⟨hc, ho⟩ | ⟨hc, ho⟩) <;> exact ⟨hc, by omega⟩
  have hdisj : Disjoint (lowLeaves m t η) (thresholdLeaves m t η) := by
    rw [disjoint_left]
    intro τ hl hh
    have hl' := (mem_filter.mp hl).2.2
    have hh' := (mem_filter.mp hh).2.2
    omega
  rw [queryValue, hsplit, sum_union hdisj]
  congr 1
  · apply sum_congr rfl
    intro τ hτ
    exact ite_eq_left (mem_filter.mp hτ).2.2
  · rw [← sum_threshold_values ht η hη a b]
    apply sum_congr rfl
    intro τ hτ
    have heq := (mem_filter.mp hτ).2.2
    exact ite_eq_right (by omega)

/-- With the existing tensor encodings, the actual query expression is the bilinear product. -/
theorem queryValue_encoding {L m t : ℕ} (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) :
    queryValue m t η (encodingL a) (encodingR b) = bilinearProduct a b η := by
  rw [queryValue_eq_low_add_boxes ht η hη]
  rw [bilinearProduct_eq_boxQuery m t ht a b η hη]
  unfold boxQuery
  congr 1
  rw [← sum_biUnion (boxesAt_pairwiseDisjoint η _)]
  apply sum_congr rfl
  intro π hπ
  obtain ⟨V, hV, hπV⟩ := mem_biUnion.mp hπ
  exact boxValue_eq_val L m t π.starLevels.card a b π
    (mem_boxesWithStars.mpr ⟨boxesAt_isBox hV hπV, rfl⟩)

/-- The sparse traversal visits exactly the existing alpha counts through the threshold. -/
theorem card_queryLeaves {L m : ℕ} (t : ℕ) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    (queryLeaves m t η).card = ∑ d ∈ range (t + 1), alpha m d := by
  have hsort : queryLeaves m t η = (range (t + 1)).biUnion fun d =>
      univ.filter fun τ : Leaf L => Leaf.Contributes τ η ∧ order m τ = (d : ℤ) := by
    ext τ
    simp only [mem_queryLeaves, mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hc, ho⟩
      have hnonneg := order_nonneg hη hc
      exact ⟨(order m τ).toNat, by omega, hc, (Int.toNat_of_nonneg hnonneg).symm⟩
    · rintro ⟨d, hd, hc, ho⟩
      exact ⟨hc, by omega⟩
  rw [hsort, card_biUnion]
  · exact sum_congr rfl fun d _ => card_contributing_of_order η hη d
  · intro d _ d' _ hne
    rw [Function.onFun, disjoint_left]
    intro τ hd hd'
    exact hne (by exact_mod_cast (mem_filter.mp hd).2.2.symm.trans (mem_filter.mp hd').2.2)

/-- The sparse set never exceeds the complete contributing leaf set. -/
theorem card_queryLeaves_le {L m : ℕ} (t : ℕ) (η : OutStr L)
    (hη : (innerSetO η).card = m) : (queryLeaves m t η).card ≤ 10 ^ m := by
  rw [← card_filter_contributes η hη]
  exact card_le_card fun τ hτ => mem_filter.mpr ⟨mem_univ _, (mem_queryLeaves.mp hτ).1⟩

/-- Its cardinality also fits the original native encoding span. -/
theorem card_queryLeaves_le_span {L m : ℕ} (t : ℕ) (η : OutStr L)
    (hη : (innerSetO η).card = m) : (queryLeaves m t η).card ≤ 10 ^ L := by
  have hm : m ≤ L := by simpa only [hη, card_univ, Fintype.card_fin] using
    (card_le_univ (innerSetO η))
  exact (card_queryLeaves_le t η hη).trans (Nat.pow_le_pow_right (by decide) hm)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
