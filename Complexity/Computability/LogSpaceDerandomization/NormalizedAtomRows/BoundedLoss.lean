/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.NormalizedAtomRows.Output
public import Complexity.Computability.LogSpaceDerandomization.RowCompression.BoundedCap
public import Complexity.Computability.LogSpaceDerandomization.RowCompression.SaturatedRoot
import Complexity.Foundations.Data.Finset.KthLargest.Truncation

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
    output HP ζ d v r = output HP ζ (min HP.toHierarchyParams.atomCap d) v
      (min HP.toHierarchyParams.atomCap r) := by
  let T := HP.toHierarchyParams.atomCap
  have hT := cap_pos HP
  have hgate : HP.η₂ ≤ T := by
    have h := HP.toHierarchyParams.atomCap_gt
    have hmargin := threshold_margin HP
    dsimp only [T]
    linarith [le_max_right ((HP.k:ℝ)+1) HP.θ₂, HP.θ_lt_θ₂]
  have he : HP.toHierarchyParams.atomCutoff d = HP.toHierarchyParams.atomCutoff (min T d) := by
    grind [HierarchyParams.atomCutoff, min_self]
  by_cases hr : r ≤ T
  · change output HP ζ d v r = output HP ζ (min T d) v (min T r)
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
      ∀ y ∈ s, |stateRootError (output HP ζ) s HP.K ⟨z,raw+loss⟩ ⟨z,truth+loss⟩ y| ≤ C*ε := by
  obtain ⟨L,hL,hroot⟩ := root_dist HP hζ
  let T := HP.toHierarchyParams.atomCap
  let B := 4*T+5
  let R := HP.Q T ^ (4⁻¹:ℝ)
  have hT : 0 < T := cap_pos HP
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hR : 0 ≤ R := Real.rpow_nonneg (HP.Q_nonneg _) _
  refine ⟨4*R+L*(2*B+1), by positivity, ?_⟩
  intro ι s z truth raw loss hfirst hloss ε hε herr y hy
  by_cases hs : ε ≤ 1/2
  · have he (x : ι) (hx : x ∈ s) := abs_sub_le_of_clippedError_le
      (hfirst x hx) (by linarith : ε < 1) (herr x hx)
    have hc (x : ι) (hx : x ∈ s) :
        |min T ((raw+loss) x 0)-min T ((truth+loss) x 0)| ≤ B*ε :=
      abs_min_add_sub_min_add_le hT hε hs (he x hx).1 (hloss x hx)
    have hq : |min T (firstRank s HP.K z (raw+loss))-
        min T (firstRank s HP.K z (truth+loss))| ≤ B*ε := by
      simp only [firstRank, min_max_distrib_left]
      rw [← kthLargest_min (f := fun x => (raw+loss) x 0) (rank_pos HP) hT.le,
        ← kthLargest_min (f := fun x => (truth+loss) x 0) (rank_pos HP) hT.le]
      exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le
        (by simpa only [sub_self, abs_zero] using mul_nonneg hB hε)
        (abs_kthLargest_sub_kthLargest_le (rank_pos HP) (mul_nonneg hB hε) hc))
    unfold stateRootError
    rw [output_upperCapped HP, output_upperCapped HP ζ ((truth+loss) y 0)]
    apply (hroot _ _ _ _ _ _).trans
    have hv : |(raw+loss) y 1-(truth+loss) y 1| ≤ ε := by
      simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using (he y hy).2
    have hh := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hc y hy) hv) hq) hL
    nlinarith [mul_nonneg hR hε]
  · have ha := root_range HP ζ ((raw+loss) y 0) ((raw+loss) y 1) (firstRank s HP.K z (raw+loss))
    have hb := root_range HP ζ ((truth+loss) y 0) ((truth+loss) y 1) (firstRank s HP.K z
      (truth+loss))
    change 0 ≤ _ ∧ _ ≤ 2*R at ha hb
    have hh : |stateRootError (output HP ζ) s HP.K ⟨z,raw+loss⟩ ⟨z,truth+loss⟩ y| ≤ 2*R :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    apply hh.trans
    have he : 1/2 < ε := not_le.mp hs
    nlinarith [mul_nonneg (by positivity : 0 ≤ L*(2*B+1)) hε]

end Matrix.FourthRootHierarchyParams.NormalizedRow
