/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.WeightedRow

/-!
# Normalization of weighted signed occurrences

The preprocessing preceding [ChenJiangZhu2027], equation (23) and Theorem 7.1,
Section 7.1, PDF pp. 22–24. Occurrences may repeat variables with either polarity.
Aggregation extracts the common constant; complementation minimizes the demand;
coefficient capping preserves Boolean solutions. This module does not certify bit
complexity or perform the subsequent capped affine rank reduction.
-/

public section

namespace Cslib.Logic.PL.WeightedRow

open scoped BigOperators

/-- Original occurrence-indexed input, including signed integer targets. -/
structure Occurrences (r m : ℕ) where
  /-- Variable referenced by each occurrence. -/
  var : Fin m → Fin r
  /-- True for a positive literal, false for a negative one. -/
  sign : Fin m → Bool
  /-- Positive occurrence coefficients (natural numbers represent binary integers). -/
  weight : Fin m → ℕ
  positive : ∀ j, 0 < weight j
  /-- Original integer target, before constant extraction. -/
  target : ℤ

/-- Sum of original literal contributions. -/
@[expose] def Occurrences.value {r m : ℕ} (R : Occurrences r m) (σ : Fin r → Bool) : ℕ :=
  ∑ j, if σ (R.var j) = R.sign j then R.weight j else 0

/-- Aggregate coefficients of one polarity. -/
@[expose] def Occurrences.aggregate {r m : ℕ} (R : Occurrences r m)
    (i : Fin r) (s : Bool) : ℕ :=
  ∑ j, if R.var j = i ∧ R.sign j = s then R.weight j else 0

/-- The constant extracted from opposite polarities. -/
@[expose] def Occurrences.constant {r m : ℕ} (R : Occurrences r m) : ℕ :=
  ∑ i, min (R.aggregate i true) (R.aggregate i false)

/-- Remaining nonnegative difference coefficient. -/
@[expose] def Occurrences.difference {r m : ℕ} (R : Occurrences r m) (i : Fin r) : ℕ :=
  (R.aggregate i true - R.aggregate i false) +
    (R.aggregate i false - R.aggregate i true)

/-- Sign of the larger aggregate; the sign of a zero coefficient is immaterial. -/
@[expose] def Occurrences.polarity {r m : ℕ} (R : Occurrences r m) (i : Fin r) : Bool :=
  decide (R.aggregate i false < R.aggregate i true)

/-- Contribution after common-constant extraction, before complementation or capping. -/
@[expose] def Occurrences.residual {r m : ℕ} (R : Occurrences r m)
    (σ : Fin r → Bool) : ℕ :=
  ∑ i, if σ i = R.polarity i then R.difference i else 0

/-- Repeated occurrences aggregate without changing their value. -/
theorem Occurrences.value_aggregate {r m : ℕ} (R : Occurrences r m) (σ : Fin r → Bool) :
    R.value σ = ∑ i, R.aggregate i (σ i) := by
  unfold value aggregate
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [ite_and]
  simp [eq_comm]

/-- Pointwise extraction of the constant, with no restriction on repeated polarities. -/
theorem Occurrences.value_extract {r m : ℕ} (R : Occurrences r m) (σ : Fin r → Bool) :
    R.value σ = R.constant + R.residual σ := by
  rw [R.value_aggregate]
  unfold constant residual
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold polarity difference
  cases σ i <;> by_cases hp : R.aggregate i false < R.aggregate i true <;>
    simp only [hp, decide_true, decide_false, Bool.false_eq_true,
      Bool.true_eq_false, ite_true, ite_false] <;> omega

/-- Total residual weight. -/
@[expose] def Occurrences.total {r m : ℕ} (R : Occurrences r m) : ℕ :=
  ∑ i, R.difference i

/-- Target after subtracting the common constant, still an integer. -/
@[expose] def Occurrences.shifted {r m : ℕ} (R : Occurrences r m) : ℤ :=
  R.target - R.constant

/-- The residual cannot exceed its total weight. -/
theorem Occurrences.residual_le {r m : ℕ} (R : Occurrences r m) (σ : Fin r → Bool) :
    R.residual σ ≤ R.total := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> omega

/-- Extraction preserves the exact equation even for negative targets. -/
theorem Occurrences.extract_iff {r m : ℕ} (R : Occurrences r m) (σ : Fin r → Bool) :
    (R.value σ : ℤ) = R.target ↔ (R.residual σ : ℤ) = R.shifted := by
  rw [R.value_extract]
  simp only [Nat.cast_add, shifted]
  omega

/-- Targets outside the residual interval reject every assignment. -/
theorem Occurrences.reject {r m : ℕ} (R : Occurrences r m)
    (h : R.shifted < 0 ∨ (R.total : ℤ) < R.shifted) (σ : Fin r → Bool) :
    (R.value σ : ℤ) ≠ R.target := by
  intro he
  have he := (R.extract_iff σ).mp he
  have := R.residual_le σ
  omega

/-- Whether all residual literals should be complemented. -/
@[expose] def Occurrences.flip {r m : ℕ} (R : Occurrences r m) : Bool :=
  decide ((R.total : ℤ) - R.shifted < R.shifted)

/-- The smaller residual demand, with validity checked separately. -/
@[expose] def Occurrences.demand {r m : ℕ} (R : Occurrences r m) : ℕ :=
  (min R.shifted ((R.total : ℤ) - R.shifted)).toNat

/-- Signs after optional complementation. -/
@[expose] def Occurrences.normalSign {r m : ℕ} (R : Occurrences r m) (i : Fin r) : Bool :=
  if R.flip then !R.polarity i else R.polarity i

/-- Contribution after optional complementation. -/
@[expose] def Occurrences.normalValue {r m : ℕ} (R : Occurrences r m)
    (σ : Fin r → Bool) : ℕ :=
  ∑ i, if σ i = R.normalSign i then R.difference i else 0

/-- Complementing every literal subtracts its value from the total weight. -/
theorem Occurrences.complement_value {r m : ℕ} (R : Occurrences r m) (σ : Fin r → Bool) :
    R.normalValue σ = if R.flip then R.total - R.residual σ else R.residual σ := by
  by_cases hf : R.flip = true
  · have hsum : R.normalValue σ + R.residual σ = R.total := by
      unfold normalValue residual total
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [normalSign, hf, ↓reduceIte]
      cases σ i <;> cases R.polarity i <;> simp
    simp only [hf, ↓reduceIte]
    omega
  · have hf : R.flip = false := Bool.eq_false_iff.mpr hf
    simp [normalValue, normalSign, hf, residual]

/-- Valid targets are preserved by demand-minimizing complementation. -/
theorem Occurrences.normal_iff {r m : ℕ} (R : Occurrences r m)
    (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) (σ : Fin r → Bool) :
    (R.value σ : ℤ) = R.target ↔ R.normalValue σ = R.demand := by
  rw [R.extract_iff, R.complement_value]
  have hr := R.residual_le σ
  unfold flip demand
  by_cases h : (R.total : ℤ) - R.shifted < R.shifted
  · simp only [h, decide_true, ite_true, min_eq_right (by omega :
      (R.total : ℤ) - R.shifted ≤ R.shifted)]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false,
      min_eq_left (by omega : R.shifted ≤ (R.total : ℤ) - R.shifted)]
    omega

/-- Capping selected contributions at `b + 1` preserves equality, including `b = 0`. -/
private theorem cap_sum {V : Type*} (s : Finset V) (w : V → ℕ) (b : ℕ) :
    (∑ i ∈ s, min (w i) (b + 1)) = b ↔ (∑ i ∈ s, w i) = b := by
  constructor
  · intro h
    have hw : ∀ i ∈ s, w i ≤ b := by
      intro i hi
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (min (w j) (b + 1))) hi
      rw [h] at this
      omega
    rw [Finset.sum_congr rfl (fun i hi => min_eq_left (by have := hw i hi; omega))] at h
    exact h
  · intro h
    have hw : ∀ i ∈ s, w i ≤ b := by
      intro i hi
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) hi
      omega
    rw [Finset.sum_congr rfl (fun i hi => min_eq_left (by have := hw i hi; omega))]
    exact h

/-- Distinct nonzero variables, with optional complementation and capped weights.
Only the normalized demand bound is supplied; correctness is proved below. -/
@[expose] def Occurrences.toRow {r m : ℕ} (R : Occurrences r m) (d : ℕ)
    (hd : R.demand ≤ d) : Row (Fin r) d where
  support := Finset.univ.filter fun i => 0 < R.difference i
  sign := R.normalSign
  weight := fun i => min (R.difference i) (R.demand + 1)
  demand := R.demand
  positive := fun i hi => Nat.lt_min.mpr ⟨(Finset.mem_filter.mp hi).2, by omega⟩
  bounded := hd
  capped := fun _ _ => min_le_right _ _

/-- Omitting zero differences and capping preserve the exact Boolean solution set. -/
theorem Occurrences.toRow_iff {r m : ℕ} (R : Occurrences r m) (d : ℕ)
    (hd : R.demand ≤ d) (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ))
    (σ : Fin r → Bool) :
    (R.toRow d hd).value σ = (R.toRow d hd).demand ↔ (R.value σ : ℤ) = R.target := by
  rw [R.normal_iff hv]
  change (∑ i ∈ (Finset.univ.filter fun i => 0 < R.difference i).filter
    (fun i => σ i = R.normalSign i), min (R.difference i) (R.demand + 1)) =
      R.demand ↔ R.normalValue σ = R.demand
  rw [cap_sum]
  have he : (∑ i ∈ (Finset.univ.filter fun i => 0 < R.difference i).filter
      (fun i => σ i = R.normalSign i), R.difference i) = R.normalValue σ := by
    simp only [Finset.sum_filter, normalValue]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> omega
  rw [he]

/-- The existing weighted CNF/DNF frontend now applies to original repeated occurrences. -/
theorem Occurrences.formula_iff {r m : ℕ} (R : Occurrences r m) (d : ℕ)
    (hd : R.demand ≤ d) (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ))
    (σ : Fin r → Bool) :
    ((R.toRow d hd).upper.eval σ = true ∧ (R.toRow d hd).attainment.eval σ = true) ↔
      (R.value σ : ℤ) = R.target :=
  (row_eval _ σ).trans (R.toRow_iff d hd hv σ)

/-- All declared variables remain counted, including variables omitted from the row. -/
theorem Occurrences.count_preserved {r m : ℕ} (R : Occurrences r m) (d : ℕ)
    (hd : R.demand ≤ d) (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) :
    Fintype.card {σ : Fin r → Bool // (R.value σ : ℤ) = R.target} =
      Fintype.card {σ : Fin r → Bool //
        (R.toRow d hd).value σ = (R.toRow d hd).demand} := by
  classical
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun σ => (R.toRow_iff d hd hv σ).symm)

/-- Original occurrence equations feed the existing two-query count identity.
This does not select independent rows or establish the final variable/clause budget. -/
theorem original_counting_identity {n m h d : ℕ} (R : Fin (h + 1) → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d)
    (hv : ∀ j, 0 ≤ (R j).shifted ∧ (R j).shifted ≤ ((R j).total : ℤ)) :
    Fintype.card {σ : Fin n → Bool // ∀ j, ((R j).value σ : ℤ) = (R j).target} =
      Fintype.card {σ : Fin n ⊕ Fin h → Bool //
        (query (fun j => (R j).toRow d (hd j)) false).eval σ = true} -
      Fintype.card {σ : Fin n ⊕ Fin h → Bool //
        (query (fun j => (R j).toRow d (hd j)) true).eval σ = true} := by
  classical
  calc
    _ = Fintype.card {σ : Fin n → Bool // ∀ j,
        ((R j).toRow d (hd j)).value σ = ((R j).toRow d (hd j)).demand} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro σ
      exact forall_congr' fun j => ((R j).toRow_iff d (hd j) (hv j) σ).symm
    _ = _ := counting_identity (fun j => (R j).toRow d (hd j))

/-- Normalization result: contradiction, a deleted true row, or a retained capped row. -/
inductive Normalized (r d : ℕ) where
  | reject
  | trivial
  | row (R : Row (Fin r) d)

/-- Meaning of a normalization result, on the original declared variables. -/
@[expose] def Normalized.Holds {r d : ℕ} (N : Normalized r d) (σ : Fin r → Bool) : Prop :=
  match N with
  | .reject => False
  | .trivial => True
  | .row R => R.value σ = R.demand

/-- Execute interval rejection, constant-row removal, complementation and capping. -/
@[expose] def Occurrences.normalize {r m : ℕ} (R : Occurrences r m) (d : ℕ)
    (hd : R.demand ≤ d) : Normalized r d :=
  if 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ) then
    if R.total = 0 then .trivial else .row (R.toRow d hd)
  else .reject

/-- Each branch preserves precisely the original Boolean assignments. -/
theorem Occurrences.normalize_iff {r m : ℕ} (R : Occurrences r m) (d : ℕ)
    (hd : R.demand ≤ d) (σ : Fin r → Bool) :
    (R.normalize d hd).Holds σ ↔ (R.value σ : ℤ) = R.target := by
  unfold normalize
  split_ifs with hv hz
  · have hr := R.residual_le σ
    have he := R.extract_iff σ
    simp only [Normalized.Holds, true_iff]
    apply he.mpr
    rw [hz] at hr hv
    omega
  · exact R.toRow_iff d hd hv σ
  · simp only [Normalized.Holds, false_iff]
    apply R.reject
    omega

open Classical in
/-- Rejection and true-row removal preserve counts as well as capped-row replacement. -/
theorem Occurrences.normalize_count {r m : ℕ} (R : Occurrences r m) (d : ℕ)
    (hd : R.demand ≤ d) :
    Fintype.card {σ : Fin r → Bool // (R.normalize d hd).Holds σ} =
      Fintype.card {σ : Fin r → Bool // (R.value σ : ℤ) = R.target} := by
  classical
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun σ => R.normalize_iff d hd σ)

end Cslib.Logic.PL.WeightedRow
