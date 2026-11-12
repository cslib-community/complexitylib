/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Finset.Powerset
import CslibFrontier.Probability.PMF.UniformSubset

/-!
# Uniform distributions over fixed-cardinality subsets (`powersetCard`)

Uniform sampling identities for `Finset.powersetCard` under `Cslib.Probability.PMF.uniformOfFinset`:

* `uniformOfFinset_powersetCard_erase`: drawing a uniform `t`-subset `U` of `S` (`1 ≤ t ≤ |S|`) and
  erasing a uniformly chosen element `e ∈ U` yields the uniform distribution on `(t - 1)`-subsets
  of `S`.
* `uniformOfFinset_powersetCard_hitOrErase`: for a fixed `p ∈ S` and `1 ≤ t ≤ |S|`, drawing a
  uniform `t`-subset `U` of `S` and returning `U.erase p` when `p ∈ U` or erasing a uniformly
  chosen element `e ∈ U` when `p ∉ U` yields the uniform distribution on `(t - 1)`-subsets of
  `S.erase p`.
* `toOuterMeasure_uniformOfFinset_powersetCard_notMem`: for `p ∈ S` and `t ≤ |S|`, a uniform
  `t`-subset of `S` misses `p` with probability `(|S| - t) / |S|`.

These identities underlie the stale-page cache distribution invariant of randomized marking
(`CslibFrontier.DataStructure.Paging.Marking`).
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

section PowersetCard

section WithDecidableEq

variable {α : Type*} [DecidableEq α]

/-- Helper step for erasing a uniform element from a subset `U`: returns `U.erase e` for a uniform
`e ∈ U` when `U` is nonempty, and `∅` on the unreachable empty case. -/
@[expose]
noncomputable def uniformErase (U : Finset α) : PMF (Finset α) :=
  if hU : U.Nonempty then
    (uniformOfFinset U hU).map fun e => U.erase e
  else
    PMF.pure ∅

private theorem uniformErase_apply_of_card {U V : Finset α} {t : ℕ} (ht : 1 ≤ t)
    (hcard : U.card = t) :
    uniformErase U V =
      if ∃ e ∈ U, U.erase e = V then (t : ℝ≥0∞)⁻¹ else 0 := by
  have hU : U.Nonempty := Finset.card_pos.mp (by omega)
  rw [uniformErase, dite_eq_left hU, PMF.map_apply]
  by_cases hex : ∃ e ∈ U, U.erase e = V
  · simp only [hex, ↓reduceIte]
    rcases hex with ⟨e₀, he₀U, he₀V⟩
    rw [tsum_eq_single e₀]
    · simp only [he₀V, ↓reduceIte, uniformOfFinset_apply, he₀U, hcard]
    · intro e he
      split_ifs with hV
      · by_cases heU : e ∈ U
        · exfalso
          apply he
          have he_not_V : e ∉ V := hV ▸ Finset.notMem_erase e U
          have hins : insert e V = insert e₀ V := by
            calc insert e V = insert e (U.erase e) := by rw [hV]
              _ = U := Finset.insert_erase heU
              _ = insert e₀ (U.erase e₀) := (Finset.insert_erase he₀U).symm
              _ = insert e₀ V := by rw [he₀V]
          have hmem : e ∈ insert e₀ V := hins ▸ Finset.mem_insert_self e V
          rcases Finset.mem_insert.mp hmem with rfl | hmemV
          · rfl
          · exact absurd hmemV he_not_V
        · simp only [uniformOfFinset_apply, heU, ↓reduceIte]
      · rfl
  · simp only [hex, ↓reduceIte]
    rw [tsum_eq_zero_iff]
    intro e
    by_cases heU : e ∈ U
    · have hne : V ≠ U.erase e := fun h => hex ⟨e, heU, h.symm⟩
      simp only [hne, ↓reduceIte]
    · simp only [uniformOfFinset_apply, heU, ↓reduceIte, ite_self]

/-- Characterization of the `t`-subsets `U` of `S` from which erasing one element yields a given
`(t - 1)`-subset `V ⊆ S`: they are precisely `insert e V` for `e ∈ S \ V`. -/
private theorem filter_powersetCard_exists_erase_eq {S V : Finset α} {t : ℕ}
    (hVS : V ⊆ S) (hVcard : V.card = t - 1) (ht : 1 ≤ t) :
    (S.powersetCard t).filter (fun U => ∃ e ∈ U, U.erase e = V) =
      (S \ V).image (fun e => insert e V) := by
  ext U
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hUS, _⟩, e, heU, rfl⟩
    exact ⟨e, ⟨hUS heU, Finset.notMem_erase e U⟩, Finset.insert_erase heU⟩
  · rintro ⟨e, ⟨heS, heV⟩, rfl⟩
    refine ⟨⟨Finset.insert_subset heS hVS, ?_⟩, e, Finset.mem_insert_self e V,
      Finset.erase_insert heV⟩
    rw [Finset.card_insert_of_notMem heV, hVcard]
    omega

private theorem card_image_insert_sdiff {S V : Finset α} (hVS : V ⊆ S) :
    ((S \ V).image (fun e => insert e V)).card = S.card - V.card := by
  rw [Finset.card_image_of_injOn, Finset.card_sdiff_of_subset hVS]
  intro e₁ he₁ e₂ _ hins
  dsimp only at hins
  have he₁V : e₁ ∉ V := (Finset.mem_sdiff.mp he₁).2
  have hmem : e₁ ∈ insert e₂ V := hins ▸ Finset.mem_insert_self e₁ V
  rcases Finset.mem_insert.mp hmem with rfl | hmemV
  · rfl
  · exact absurd hmemV he₁V

/-- Drawing a uniform `t`-subset `U` of `S` (`1 ≤ t ≤ |S|`) and erasing a uniformly chosen element
of `U` yields the uniform distribution on `(t - 1)`-subsets of `S`. -/
theorem uniformOfFinset_powersetCard_erase {S : Finset α} {t : ℕ}
    (ht : 1 ≤ t) (htS : t ≤ S.card) :
    (uniformOfFinset (S.powersetCard t) (Finset.powersetCard_nonempty.mpr htS)).bind uniformErase =
      uniformOfFinset (S.powersetCard (t - 1))
        (Finset.powersetCard_nonempty.mpr (by omega)) := by
  set c : ℝ≥0∞ :=
    ((S.card - (t - 1) : ℕ) : ℝ≥0∞) *
      (((S.powersetCard t).card : ℝ≥0∞)⁻¹ * (t : ℝ≥0∞)⁻¹)
  refine pmf_eq_uniformOfFinset_of_ite_const
    (Finset.powersetCard_nonempty.mpr (by omega)) (c := c) fun V => ?_
  rw [PMF.bind_apply]
  by_cases hV : V ∈ S.powersetCard (t - 1)
  · simp only [hV, ↓reduceIte]
    obtain ⟨hVS, hVcard⟩ := Finset.mem_powersetCard.mp hV
    rw [tsum_eq_sum (s := S.powersetCard t)]
    · have hsum :
          ∑ U ∈ S.powersetCard t,
            uniformOfFinset (S.powersetCard t) (Finset.powersetCard_nonempty.mpr htS) U *
              uniformErase U V =
          ∑ U ∈ (S.powersetCard t).filter (fun U => ∃ e ∈ U, U.erase e = V),
            (((S.powersetCard t).card : ℝ≥0∞)⁻¹ * (t : ℝ≥0∞)⁻¹) := by
        symm
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun U hU => ?_
        have hUcard : U.card = t := (Finset.mem_powersetCard.mp hU).2
        rw [uniformOfFinset_apply, ite_eq_left hU, uniformErase_apply_of_card ht hUcard]
        split_ifs <;> simp only [mul_zero]
      rw [hsum, Finset.sum_const, filter_powersetCard_exists_erase_eq hVS hVcard ht,
        card_image_insert_sdiff hVS, hVcard, nsmul_eq_mul]
    · intro U hU
      simp only [uniformOfFinset_apply, hU, ↓reduceIte, zero_mul]
  · simp only [hV, ↓reduceIte]
    rw [tsum_eq_zero_iff]
    intro U
    by_cases hU : U ∈ S.powersetCard t
    · obtain ⟨hUS, hUcard⟩ := Finset.mem_powersetCard.mp hU
      rw [uniformErase_apply_of_card ht hUcard]
      have hno : ¬ ∃ e ∈ U, U.erase e = V := by
        rintro ⟨e, heU, rfl⟩
        apply hV
        rw [Finset.mem_powersetCard]
        exact ⟨(Finset.erase_subset e U).trans hUS, by rw [Finset.card_erase_of_mem heU, hUcard]⟩
      simp only [hno, ↓reduceIte, mul_zero]
    · simp only [uniformOfFinset_apply, hU, ↓reduceIte, zero_mul]

/-- For `p ∈ S` and `1 ≤ t ≤ |S|`, drawing a uniform `t`-subset `U` of `S` and returning
`U.erase p` when `p ∈ U` or `uniformErase U` when `p ∉ U` yields the uniform distribution on
`(t - 1)`-subsets of `S.erase p`. -/
theorem uniformOfFinset_powersetCard_hitOrErase {S : Finset α} {p : α} {t : ℕ}
    (hpS : p ∈ S) (ht : 1 ≤ t) (htS : t ≤ S.card) :
    (uniformOfFinset (S.powersetCard t) (Finset.powersetCard_nonempty.mpr htS)).bind
      (fun U => if p ∈ U then PMF.pure (U.erase p) else uniformErase U) =
      uniformOfFinset ((S.erase p).powersetCard (t - 1))
        (Finset.powersetCard_nonempty.mpr
          (by rw [Finset.card_erase_of_mem hpS]; omega)) := by
  have hne' : ((S.erase p).powersetCard (t - 1)).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by rw [Finset.card_erase_of_mem hpS]; omega)
  set invN : ℝ≥0∞ := ((S.powersetCard t).card : ℝ≥0∞)⁻¹
  set c : ℝ≥0∞ := invN + ((S.card - t : ℕ) : ℝ≥0∞) * (invN * (t : ℝ≥0∞)⁻¹)
  refine pmf_eq_uniformOfFinset_of_ite_const hne' (c := c) fun V => ?_
  rw [PMF.bind_apply]
  by_cases hV : V ∈ (S.erase p).powersetCard (t - 1)
  · simp only [hV, ↓reduceIte]
    obtain ⟨hVsub, hVcard⟩ := Finset.mem_powersetCard.mp hV
    have hpV : p ∉ V := fun hp => Finset.notMem_erase p S (hVsub hp)
    have hVS : V ⊆ S := hVsub.trans (Finset.erase_subset p S)
    rw [tsum_eq_sum (s := S.powersetCard t)]
    · have hpart :
          ∑ U ∈ S.powersetCard t,
            uniformOfFinset (S.powersetCard t) (Finset.powersetCard_nonempty.mpr htS) U *
              (if p ∈ U then PMF.pure (U.erase p) else uniformErase U) V =
          ∑ U ∈ (S.powersetCard t).filter (p ∈ ·),
            invN * (if V = U.erase p then 1 else 0) +
          ∑ U ∈ (S.powersetCard t).filter (p ∉ ·),
            invN * uniformErase U V := by
        rw [← Finset.sum_filter_add_sum_filter_not (S.powersetCard t) (p ∈ ·)]
        congr 1
        · refine Finset.sum_congr rfl fun U hU => ?_
          obtain ⟨hUmem, hpU⟩ := Finset.mem_filter.mp hU
          simp only [uniformOfFinset_apply, hUmem, hpU, ↓reduceIte, PMF.pure_apply, invN]
          congr 1
          split_ifs <;> rfl
        · refine Finset.sum_congr rfl fun U hU => ?_
          obtain ⟨hUmem, hpU⟩ := Finset.mem_filter.mp hU
          simp only [uniformOfFinset_apply, hUmem, hpU, ↓reduceIte, invN]
      rw [hpart]
      have hhit_set :
          ((S.powersetCard t).filter (p ∈ ·)).filter (fun U => V = U.erase p) = {insert p V} := by
        ext U
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨⟨_, _⟩, hpU⟩, rfl⟩
          exact (Finset.insert_erase hpU).symm
        · rintro rfl
          refine ⟨⟨⟨Finset.insert_subset hpS hVS, ?_⟩, Finset.mem_insert_self p V⟩,
            (Finset.erase_insert hpV).symm⟩
          rw [Finset.card_insert_of_notMem hpV, hVcard]
          omega
      have hhit :
          ∑ U ∈ (S.powersetCard t).filter (p ∈ ·), invN * (if V = U.erase p then 1 else 0) =
            invN := by
        have hmul :
            ∑ U ∈ (S.powersetCard t).filter (p ∈ ·), invN * (if V = U.erase p then 1 else 0) =
              ∑ U ∈ ((S.powersetCard t).filter (p ∈ ·)).filter (fun U => V = U.erase p), invN := by
          symm
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun U _ => ?_
          split_ifs <;> simp only [mul_one, mul_zero]
        rw [hmul, hhit_set, Finset.sum_singleton]
      have hfilter_not :
          (S.powersetCard t).filter (p ∉ ·) = (S.erase p).powersetCard t := by
        ext U
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_erase]
        tauto
      have hmiss :
          ∑ U ∈ (S.powersetCard t).filter (p ∉ ·), invN * uniformErase U V =
            ((S.card - t : ℕ) : ℝ≥0∞) * (invN * (t : ℝ≥0∞)⁻¹) := by
        rw [hfilter_not]
        have hrew :
            ∑ U ∈ (S.erase p).powersetCard t, invN * uniformErase U V =
              ∑ U ∈ ((S.erase p).powersetCard t).filter (fun U => ∃ e ∈ U, U.erase e = V),
                (invN * (t : ℝ≥0∞)⁻¹) := by
          symm
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun U hU => ?_
          have hUcard : U.card = t := (Finset.mem_powersetCard.mp hU).2
          rw [uniformErase_apply_of_card ht hUcard]
          split_ifs <;> simp only [mul_zero]
        rw [hrew, Finset.sum_const, filter_powersetCard_exists_erase_eq hVsub hVcard ht,
          card_image_insert_sdiff hVsub, Finset.card_erase_of_mem hpS, hVcard, nsmul_eq_mul]
        have hsub_eq : S.card - 1 - (t - 1) = S.card - t := by omega
        rw [hsub_eq]
      rw [hhit, hmiss]
    · intro U hU
      simp only [uniformOfFinset_apply, hU, ↓reduceIte, zero_mul]
  · simp only [hV, ↓reduceIte]
    rw [tsum_eq_zero_iff]
    intro U
    by_cases hU : U ∈ S.powersetCard t
    · obtain ⟨hUS, hUcard⟩ := Finset.mem_powersetCard.mp hU
      by_cases hpU : p ∈ U
      · simp only [hpU, ↓reduceIte, PMF.pure_apply]
        have hneV : V ≠ U.erase p := by
          rintro rfl
          apply hV
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.erase_subset_erase p hUS, by rw [Finset.card_erase_of_mem hpU, hUcard]⟩
        simp only [hneV, ↓reduceIte, mul_zero]
      · simp only [hpU, ↓reduceIte, uniformErase_apply_of_card ht hUcard]
        have hUsub : U ⊆ S.erase p := Finset.subset_erase.mpr ⟨hUS, hpU⟩
        have hno : ¬ ∃ e ∈ U, U.erase e = V := by
          rintro ⟨e, heU, rfl⟩
          apply hV
          rw [Finset.mem_powersetCard]
          exact ⟨(Finset.erase_subset e U).trans hUsub,
            by rw [Finset.card_erase_of_mem heU, hUcard]⟩
        simp only [hno, ↓reduceIte, mul_zero]
    · simp only [uniformOfFinset_apply, hU, ↓reduceIte, zero_mul]

end WithDecidableEq

/-- A uniform `t`-subset of `S` (`t ≤ |S|`) misses a fixed element `p ∈ S` with probability
`(|S| - t) / |S|`. -/
theorem toOuterMeasure_uniformOfFinset_powersetCard_notMem {α : Type*} {S : Finset α} {p : α}
    {t : ℕ} (hpS : p ∈ S) (htS : t ≤ S.card) :
    (uniformOfFinset (S.powersetCard t)
      (Finset.powersetCard_nonempty.mpr htS)).toOuterMeasure {U | p ∉ U} =
      ((S.card - t : ℕ) : ℝ≥0∞) * (S.card : ℝ≥0∞)⁻¹ := by
  classical
  rw [toOuterMeasure_uniformOfFinset]
  have hfilter :
      (S.powersetCard t).filter (· ∈ {U : Finset α | p ∉ U}) = (S.erase p).powersetCard t := by
    ext U
    simp only [Finset.mem_filter, Set.mem_ofPred_eq, Finset.mem_powersetCard, Finset.subset_erase]
    tauto
  rw [hfilter, Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_erase_of_mem hpS]
  have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨p, hpS⟩
  have hchoose_nat :
      (S.card - 1).choose t * S.card = S.card.choose t * (S.card - t) := by
    simpa [Nat.sub_add_cancel hS_pos] using Nat.choose_mul_succ_eq (S.card - 1) t
  have hchoose :
      (((S.card - 1).choose t : ℕ) : ℝ≥0∞) * (S.card : ℝ≥0∞) =
        (S.card.choose t : ℝ≥0∞) * ((S.card - t : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hchoose_nat
  have hSne : (S.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hCne : (S.card.choose t : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos htS).ne'
  calc (((S.card - 1).choose t : ℕ) : ℝ≥0∞) * (S.card.choose t : ℝ≥0∞)⁻¹
      = ((((S.card - 1).choose t : ℕ) : ℝ≥0∞) * (S.card : ℝ≥0∞)) *
          ((S.card : ℝ≥0∞)⁻¹ * (S.card.choose t : ℝ≥0∞)⁻¹) := by
        rw [mul_assoc, ← mul_assoc (S.card : ℝ≥0∞),
          ENNReal.mul_inv_cancel hSne (ENNReal.natCast_ne_top _), one_mul]
    _ = ((S.card.choose t : ℝ≥0∞) * ((S.card - t : ℕ) : ℝ≥0∞)) *
          ((S.card : ℝ≥0∞)⁻¹ * (S.card.choose t : ℝ≥0∞)⁻¹) := by
        rw [hchoose]
    _ = (((S.card - t : ℕ) : ℝ≥0∞) * (S.card : ℝ≥0∞)⁻¹) *
          ((S.card.choose t : ℝ≥0∞) * (S.card.choose t : ℝ≥0∞)⁻¹) := by
        ring
    _ = ((S.card - t : ℕ) : ℝ≥0∞) * (S.card : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.mul_inv_cancel hCne (ENNReal.natCast_ne_top _), mul_one]

end PowersetCard

end Cslib.Probability.PMF
