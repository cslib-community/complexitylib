/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.FixedEffects.Matrix
public import Complexity.Statistics.LeastSquares.Stability
import Mathlib.Tactic

/-!
# Group-preserving fixed-column audits

For [XuGaoHu2027], equation (2) and Theorem 4.1, identify retained-row
within-group regression with the generic fixed-column inverse problem whenever
every original group survives. This condition is essential: a vanished group's
zero dummy is singular. The small-deletion criterion below derives preservation
from group cardinalities rather than assuming the two stability models agree.
-/

noncomputable section

public section


namespace Cslib.LeastSquares.FixedEffects.MatrixModel

open Matrix Set

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {I : G → Type*} [∀ g, Fintype (I g)] [DecidableEq (Sigma I)]

open Classical in
/-- Row positions retained within each original group, preserving multiplicities. -/
abbrev Kept (s : Finset (Sigma I)) (g : G) := {i : I g // Sigma.mk g i ∈ s}

open Classical in
/-- Restrict data to retained row positions. -/
@[expose] def restrict (z : (g : G) → I g → ℝ) (s : Finset (Sigma I))
    (g : G) (i : Kept s g) : ℝ := z g i.val

open Classical in
/-- Every original dummy still has at least one retained observation. -/
@[expose] def PreservesGroups (s : Finset (Sigma I)) : Prop :=
  ∀ g, ∃ i : I g, Sigma.mk g i ∈ s

open Classical in
/-- The actual retained Gram matrix equals deletion by zero-one weights in the
original column space. No change of dummy coordinates is hidden in this equality. -/
theorem restricted_gram (x : (g : G) → I g → ℝ) (s : Finset (Sigma I)) :
    gram (restrict x s) = weightedGram 0 Finset.univ (row x)
      (fun p => if p ∈ s then 1 else 0) := by
  ext j k
  simp only [gram, weightedGram, zero_add, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, vecMulVec, Matrix.of_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  change (∑ i : Kept s g, row x ⟨g, i.val⟩ j * row x ⟨g, i.val⟩ k) = _
  rw [← Finset.sum_subtype (Finset.univ.filter fun i : I g => Sigma.mk g i ∈ s)
    (by simp) (fun i => row x ⟨g, i⟩ j * row x ⟨g, i⟩ k), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all only [one_mul, zero_mul]

open Classical in
/-- The retained response vector has the same fixed-column interpretation. -/
theorem restricted_response (x y : (g : G) → I g → ℝ) (s : Finset (Sigma I)) :
    response (restrict x s) (restrict y s) =
      weightedResponse 0 Finset.univ (row x) (fun p => y p.1 p.2)
        (fun p => if p ∈ s then 1 else 0) := by
  ext j
  simp only [response, weightedResponse, zero_add, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  change (∑ i : Kept s g, y g i.val * row x ⟨g, i.val⟩ j) = _
  rw [← Finset.sum_subtype (Finset.univ.filter fun i : I g => Sigma.mk g i ∈ s)
    (by simp) (fun i => y g i * row x ⟨g, i⟩ j), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all only [one_mul, zero_mul]

omit [Fintype G] [DecidableEq G] [∀ g, Fintype (I g)] [DecidableEq (Sigma I)] in
open Classical in
/-- Group preservation supplies exactly the nonempty retained-group instances
needed by the matrix uniqueness theorem. -/
theorem preservesGroups_iff (s : Finset (Sigma I)) :
    PreservesGroups s ↔ ∀ g, Nonempty (Kept s g) := by
  simp [PreservesGroups, Kept, nonempty_subtype]

open Classical in
/-- The scalar within-scatter/sign test is the actual generic inverse-matrix
feasibility test for every group-preserving subset. -/
theorem feasible_iff (x y : (g : G) → I g → ℝ) (s : Finset (Sigma I))
    (hs : PreservesGroups s) :
    Feasible (row x) (fun p => y p.1 p.2) (Pi.single none 1) 0
      (fun p => if p ∈ s then 1 else 0) ↔
      0 < scatter (restrict x s) ∧ cross (restrict x s) (restrict y s) ≤ 0 := by
  let (g : G) : Nonempty (Kept s g) := (preservesGroups_iff s).mp hs g
  have hb : ∀ p : Sigma I, (if p ∈ s then (1 : ℝ) else 0) ∈ Icc 0 1 := by
    intro p; split_ifs <;> norm_num
  have he : weightedEstimate 0 0 Finset.univ (row x) (fun p => y p.1 p.2)
      (fun p => if p ∈ s then 1 else 0) =
      (gram (restrict x s))⁻¹ *ᵥ response (restrict x s) (restrict y s) := by
    rw [weightedEstimate, ← restricted_gram, ← restricted_response]
  constructor
  · rintro ⟨_, hG, ht⟩
    rw [← restricted_gram, gram_posDef_iff] at hG
    rw [he, single_dotProduct, one_mul] at ht
    exact ⟨hG, (inverse_slope_nonpos_iff _ _ hG).mp ht⟩
  · rintro ⟨hv, ht⟩
    refine ⟨hb, ?_, ?_⟩
    · rw [← restricted_gram, gram_posDef_iff]
      exact hv
    · rw [he, single_dotProduct, one_mul]
      exact (inverse_slope_nonpos_iff _ _ hv).mpr ht

open Classical in
/-- Positive definiteness of the original-column weighted design forces every
group to survive. Thus this condition follows from fixed-column feasibility. -/
theorem preservesGroups_of_posDef (x : (g : G) → I g → ℝ) (s : Finset (Sigma I))
    (hG : (weightedGram 0 Finset.univ (row x)
      (fun p => if p ∈ s then 1 else 0)).PosDef) : PreservesGroups s := by
  intro g
  by_contra hn
  have he : IsEmpty (Kept s g) := ⟨by
    rintro ⟨i, hi⟩
    exact hn ⟨i, hi⟩⟩
  let := he
  rw [← restricted_gram] at hG
  exact not_posDef_of_empty_group (restrict x s) g hG

open Classical in
/-- Complete subset characterization, including exclusion of vanished dummies. -/
theorem feasible_iff_preservesGroups (x y : (g : G) → I g → ℝ)
    (s : Finset (Sigma I)) :
    Feasible (row x) (fun p => y p.1 p.2) (Pi.single none 1) 0
      (fun p => if p ∈ s then 1 else 0) ↔
      PreservesGroups s ∧ 0 < scatter (restrict x s) ∧
        cross (restrict x s) (restrict y s) ≤ 0 := by
  constructor
  · intro h
    have hs := preservesGroups_of_posDef x s h.2.1
    exact ⟨hs, (feasible_iff x y s hs).mp h⟩
  · rintro ⟨hs, h⟩
    exact (feasible_iff x y s hs).mpr h

omit [DecidableEq G] [DecidableEq (Sigma I)] in
open Classical in
/-- Removing fewer observations than any group's size cannot erase a dummy.
The bound counts actual row positions, even for repeated data. -/
theorem preservesGroups_of_deletions_lt (s : Finset (Sigma I))
    (hs : ∀ g, Fintype.card (Sigma I) - s.card < Fintype.card (I g)) :
    PreservesGroups s := by
  classical
  intro g
  by_contra hn
  have hsub : Finset.univ.map ⟨Sigma.mk g, fun i j h => eq_of_heq (Sigma.mk.inj h).2⟩ ⊆ sᶜ := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hp
    simp only [Finset.mem_compl]
    exact fun hi => hn ⟨i, hi⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_univ, Finset.card_compl] at hc
  exact (not_le_of_gt (hs g)) hc

open Classical in
/-- The refitted scalar subset problem, which permits empty groups. Empty
within terms contribute zero; feasibility still requires positive pooled scatter. -/
@[expose] noncomputable def subsetStability (x y : (g : G) → I g → ℝ) : ℕ :=
  sInf {k : ℕ | ∃ s : Finset (Sigma I),
    (0 < scatter (restrict x s) ∧ cross (restrict x s) (restrict y s) ≤ 0) ∧
      k = Fintype.card (Sigma I) - s.card}

open Classical in
/-- A sufficient, derived model-comparison criterion. If the refitted optimum
uses fewer deletions than every group has observations, its attaining subset
preserves every dummy and fixed-column stability is exactly the refitted value.
No general equality between these two models is asserted. -/
theorem integralStability_eq_subsetStability (x y : (g : G) → I g → ℝ)
    (hne : ∃ s : Finset (Sigma I),
      0 < scatter (restrict x s) ∧ cross (restrict x s) (restrict y s) ≤ 0)
    (hsmall : ∀ g, subsetStability x y < Fintype.card (I g)) :
    integralStability (row x) (fun p => y p.1 p.2) (Pi.single none 1) 0 =
      subsetStability x y := by
  classical
  let D := {k : ℕ | ∃ s : Finset (Sigma I),
    (0 < scatter (restrict x s) ∧ cross (restrict x s) (restrict y s) ≤ 0) ∧
      k = Fintype.card (Sigma I) - s.card}
  have hD : D.Nonempty := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨_, s, hs, rfl⟩
  obtain ⟨s, hs, hc⟩ := Nat.sInf_mem hD
  have hpres : PreservesGroups s := preservesGroups_of_deletions_lt s (by
    intro g
    have hg : sInf D < Fintype.card (I g) := hsmall g
    simpa only [hc] using hg)
  have hf := (feasible_iff x y s hpres).mpr hs
  apply le_antisymm
  · change _ ≤ sInf D
    rw [hc]
    apply Nat.sInf_le
    refine ⟨s, ?_, rfl⟩
    convert hf using 1; (funext p; split_ifs <;> rfl)
  · unfold integralStability
    apply le_csInf
    · refine ⟨_, s, ?_, rfl⟩
      convert hf using 1; (funext p; split_ifs <;> rfl)
    · rintro k ⟨t, ht, rfl⟩
      apply Nat.sInf_le
      refine ⟨t, ((feasible_iff_preservesGroups x y t).mp ?_).2, rfl⟩
      convert ht using 1; (funext p; split_ifs <;> rfl)

end Cslib.LeastSquares.FixedEffects.MatrixModel
