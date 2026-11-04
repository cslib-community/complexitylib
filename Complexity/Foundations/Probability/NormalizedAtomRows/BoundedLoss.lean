/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.Output
public import Complexity.Foundations.Analysis.RowCompression.Decoder

/-!
# Bounded common-loss comparison for actual normalized atoms

Arbitrary nonnegative true first entries are allowed on every rank endpoint. Only the
common first loss is bounded by `atomCap`; common defaults and second losses are unrestricted.
Saturation is proved inside the scalar output, leaving raw rows and compression unchanged.
This original cap-free extension is deterministic and assumes raw clipped error, rather
than the desired normalized-output bound. It does not supply recursive moment budgets.
-/

public section
namespace Matrix.FourthRootHierarchyParams.NormalizedRow
open Finset Cslib Matrix Cslib.RowCompression
open scoped BigOperators
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

/-- The hierarchy scalar cap is strictly positive. -/
lemma cap_pos : 0 < HP.toHierarchyParams.atomCap := by
  have h := HP.toHierarchyParams.atomCap_gt
  have h0 := Nat.cast_nonneg (α := ℝ) HP.k
  exact lt_trans (by positivity : (0:ℝ) < (HP.k:ℝ)+1)
    ((le_max_left _ _).trans_lt h)

/-- Scalar caps preserve the exact normalized output, including its closed rank gate. -/
lemma output_upperCapped (ζ d v r : ℝ) :
    output HP.toHierarchyParams.atomCutoff HP.ρ ζ d v r = output HP.toHierarchyParams.atomCutoff
      HP.ρ ζ (min HP.toHierarchyParams.atomCap d) v
      (min HP.toHierarchyParams.atomCap r) := by
  let T := HP.toHierarchyParams.atomCap
  have hT := cap_pos HP
  have hgate : HP.η₂ ≤ T := by
    have h := HP.toHierarchyParams.atomCap_gt
    have hmargin := threshold_margin HP
    dsimp only [T]
    linarith [le_max_right ((HP.k:ℝ)+1) HP.θ₂, HP.θ_lt_θ₂]
  have he : HP.toHierarchyParams.atomCutoff d = HP.toHierarchyParams.atomCutoff (min T d) := by
    simp only [HierarchyParams.atomCutoff]
    by_cases hd : d ≤ T
    · rw [min_eq_right hd]
    · have hTd : T ≤ d := (not_le.mp hd).le
      rw [min_eq_left hTd, max_eq_right (hT.le.trans hTd), min_eq_left hTd,
        max_eq_right hT.le, min_self]
  by_cases hr : r ≤ T
  · change output HP.toHierarchyParams.atomCutoff HP.ρ ζ d v r = output
      HP.toHierarchyParams.atomCutoff HP.ρ ζ (min T d) v (min T r)
    simp only [output, he, min_eq_right hr]
  · rw [gate_zero HP (hgate.trans (not_le.mp hr).le), min_eq_left (not_le.mp hr).le,
      gate_zero HP hgate]

/-- Static comparison for arbitrary nonnegative truth, with only the actual first preloss
bounded. No input row or compression state is capped. -/
theorem boundedLoss_root_bound {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (s : Finset ι) (z : ℝ)
      (truth raw loss : ι → Fin 2 → ℝ),
      (∀ y ∈ s, 0 ≤ truth y 0) →
      (∀ y ∈ s, |loss y 0| ≤ HP.toHierarchyParams.atomCap) →
      ∀ ε : ℝ, 0 ≤ ε →
      (∀ y ∈ s, clippedError (truth y 0) (truth y 1) (raw y) ≤ ε) →
      ∀ y ∈ s, |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s HP.K
      ⟨z,raw+loss⟩ ⟨z,truth+loss⟩ y| ≤ C*ε := by
  exact exists_boundedLoss_decoder_bound _ (cap_pos HP)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (HP.Q_nonneg _) _))
    (output_upperCapped HP ζ)
    (root_range HP ζ) (root_dist HP hζ) (rank_pos HP)

end Matrix.FourthRootHierarchyParams.NormalizedRow
