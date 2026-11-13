/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Subsets.Geometric
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Counting conditional parity witnesses

A conditioning witness chooses at most `k` coordinates from an allowed set `U`, and one
alphabet value on each chosen coordinate. Assignments have domain precisely the chosen
coordinates: there is no multiplicity from arbitrary values outside that domain.
-/

@[expose] public section

namespace Cslib.Communication.Lifting

open Finset

/-- Coordinates and values of a bounded-size conditioning assignment. -/
structure ConditioningAssignment {α : Type*} (U : Finset α) (m k : ℕ) where
  /-- The coordinates being fixed. -/
  coordinates : Finset α
  /-- Only allowed coordinates are fixed. -/
  subset : coordinates ⊆ U
  /-- The conditioning size budget. -/
  card_le : coordinates.card ≤ k
  /-- Values are specified only on the fixed coordinates. -/
  values : coordinates → Fin m

/-- The finite encoding used to count conditioning assignments. -/
noncomputable def ConditioningAssignment.equivSigma {α : Type*} (U : Finset α) (m k : ℕ) :
    ConditioningAssignment U m k ≃
      ((J : ↥(U.powerset.filter fun J => J.card ≤ k)) × (J.val → Fin m)) := by
  classical
  exact
    { toFun := fun a => ⟨⟨a.coordinates, mem_filter.mpr ⟨mem_powerset.mpr a.subset, a.card_le⟩⟩,
        a.values⟩
      invFun := fun a => ⟨a.1.val, mem_powerset.mp (mem_filter.mp a.1.property).1,
        (mem_filter.mp a.1.property).2, a.2⟩
      left_inv := fun a => by cases a; rfl
      right_inv := fun a => by rcases a with ⟨⟨J, hJ⟩, a⟩; rfl }

noncomputable instance {α : Type*} (U : Finset α) (m k : ℕ) :
    Fintype (ConditioningAssignment U m k) := by
  classical
  exact Fintype.ofEquiv _ (ConditioningAssignment.equivSigma U m k).symm

/-- The exact number of partial conditioning assignments, including thresholds above `U.card`. -/
theorem card_conditioningAssignment {α : Type*} (U : Finset α) (m k : ℕ) :
    Fintype.card (ConditioningAssignment U m k) =
      ∑ j ∈ range (k + 1), U.card.choose j * m ^ j := by
  classical
  rw [Fintype.card_congr (ConditioningAssignment.equivSigma U m k), Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  rw [Finset.sum_coe_sort (U.powerset.filter fun J => J.card ≤ k)
    (fun J : Finset α => m ^ J.card)]
  calc
    (∑ J ∈ U.powerset.filter (fun J => J.card ≤ k), m ^ J.card) =
        ∑ j ∈ range (k + 1),
          ∑ J ∈ (U.powerset.filter fun J => J.card ≤ k).filter (fun J => J.card = j),
            m ^ J.card := by
      symm
      apply sum_fiberwise_of_maps_to
      intro J hJ
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hJ).2)
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have heq : (U.powerset.filter fun J => J.card ≤ k).filter (fun J => J.card = j) =
          U.powersetCard j := by
        ext J
        simp only [mem_filter, mem_powerset, mem_powersetCard]
        exact ⟨fun h => ⟨h.1.1, h.2⟩,
          fun h => ⟨⟨h.1, h.2.le.trans (Nat.le_of_lt_succ (mem_range.mp hj))⟩, h.2⟩⟩
      rw [heq]
      calc
        _ = ∑ _J ∈ U.powersetCard j, m ^ j := by
          apply sum_congr rfl
          intro J hJ
          rw [(mem_powersetCard.mp hJ).2]
        _ = _ := by simp

/-- Counting by the actual coordinate universe avoids a factor depending on an oversized
threshold. Only `U.card + 1` distinct cardinalities can occur. -/
theorem card_conditioningAssignment_le {α : Type*} (U : Finset α) (m k N : ℕ)
    (hU : U.card ≤ N) (hNm : 1 ≤ N * m) :
    Fintype.card (ConditioningAssignment U m k) ≤ (N + 1) * (N * m) ^ k := by
  classical
  have hsets : (U.powerset.filter fun J => J.card ≤ k) =
      (U.powerset.filter fun J => J.card ≤ min k U.card) := by
    ext J
    simp only [mem_filter, mem_powerset]
    exact ⟨fun h => ⟨h.1, le_min h.2 (card_le_card h.1)⟩,
      fun h => ⟨h.1, (le_min_iff.mp h.2).1⟩⟩
  have heq : Fintype.card (ConditioningAssignment U m k) =
      Fintype.card (ConditioningAssignment U m (min k U.card)) := by
    rw [Fintype.card_congr (ConditioningAssignment.equivSigma U m k),
      Fintype.card_congr (ConditioningAssignment.equivSigma U m (min k U.card))]
    apply Fintype.card_congr'
    rw [hsets]
  rw [heq, card_conditioningAssignment]
  calc
    _ ≤ ∑ _j ∈ range (min k U.card + 1), (N * m) ^ k := by
      apply sum_le_sum
      intro j hj
      have hjk : j ≤ k := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
      calc
        U.card.choose j * m ^ j ≤ U.card ^ j * m ^ j :=
          Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
        _ ≤ N ^ j * m ^ j := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hU _)
        _ = (N * m) ^ j := (mul_pow _ _ _).symm
        _ ≤ (N * m) ^ k := Nat.pow_le_pow_right (by omega) hjk
    _ = (min k U.card + 1) * (N * m) ^ k := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add_right ((min_le_right _ _).trans hU) 1)

/-- The geometric total over nonempty parity supports, with every bounded conditioning
assignment on its complement counted once. -/
theorem sum_conditioningAssignment_mul_pow_le (n m k : ℕ) (hNm : 1 ≤ n * m)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hnq : n * q ≤ 1 / 2) :
    (∑ S ∈ (univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
      (Fintype.card (ConditioningAssignment (univ \ S) m k) : ℝ) * q ^ S.card) ≤
        (n + 1 : ℕ) * ((n * m : ℕ) : ℝ) ^ k := by
  classical
  have hweight := sum_nonempty_powerset_pow_card_le_one (univ : Finset (Fin n))
    hq hq1 (by simpa using hnq)
  calc
    _ ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
        ((n + 1 : ℕ) * ((n * m : ℕ) : ℝ) ^ k) * q ^ S.card := by
      apply sum_le_sum
      intro S _
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq _)
      exact_mod_cast card_conditioningAssignment_le (univ \ S) m k n
        (by simpa using card_le_card (sdiff_subset : univ \ S ⊆ univ)) hNm
    _ = ((n + 1 : ℕ) * ((n * m : ℕ) : ℝ) ^ k) *
        ∑ S ∈ (univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
          q ^ S.card := by rw [mul_sum]
    _ ≤ _ := mul_le_of_le_one_right
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) hweight

/-- A size-dependent conditioning budget gives a geometric witness count for each nonempty
parity support. The factor `n + 1` is absorbed once per parity coordinate. -/
theorem card_conditioningAssignment_le_pow {n m k : ℕ} (hNm : 1 ≤ n * m)
    (S : Finset (Fin n)) (hS : S.Nonempty) {u : ℝ} (hu : 0 ≤ u)
    (hk : ((n * m : ℕ) : ℝ) ^ k ≤ u ^ S.card) :
    (Fintype.card (ConditioningAssignment (univ \ S) m k) : ℝ) ≤
      (((n + 1 : ℕ) : ℝ) * u) ^ S.card := by
  have hc : (Fintype.card (ConditioningAssignment (univ \ S) m k) : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * ((n * m : ℕ) : ℝ) ^ k := by
    exact_mod_cast card_conditioningAssignment_le (univ \ S) m k n
      (by simpa using card_le_card (sdiff_subset : univ \ S ⊆ univ)) hNm
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) * u ^ S.card :=
      hc.trans (mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _))
    _ ≤ (((n + 1 : ℕ) : ℝ) ^ S.card) * u ^ S.card :=
      mul_le_mul_of_nonneg_right
        (le_self_pow₀ (by exact_mod_cast Nat.le_add_left 1 n) hS.card_pos.ne')
        (pow_nonneg hu _)
    _ = _ := (mul_pow _ _ _).symm

/-- Geometric summation of canonical witnesses with a support-dependent size budget. -/
theorem sum_conditioningAssignment_mul_pow_le_one (n m : ℕ)
    (k : Finset (Fin n) → ℕ) (hNm : 1 ≤ n * m) {u q : ℝ}
    (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hk : ∀ S : Finset (Fin n), S.Nonempty →
      ((n * m : ℕ) : ℝ) ^ k S ≤ u ^ S.card)
    (hw : (((n + 1 : ℕ) : ℝ) * u * q) ≤ 1)
    (hnw : n * (((n + 1 : ℕ) : ℝ) * u * q) ≤ 1 / 2) :
    (∑ S ∈ (univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
      (Fintype.card (ConditioningAssignment (univ \ S) m (k S)) : ℝ) * q ^ S.card) ≤ 1 := by
  classical
  calc
    _ ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
        (((n + 1 : ℕ) : ℝ) * u * q) ^ S.card := by
      apply sum_le_sum
      intro S hS
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (card_conditioningAssignment_le_pow hNm S (mem_filter.mp hS).2 hu
          (hk S (mem_filter.mp hS).2)) (pow_nonneg hq _)
    _ ≤ 1 := sum_nonempty_powerset_pow_card_le_one _
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hq) hw (by simpa using hnw)

end Cslib.Communication.Lifting
