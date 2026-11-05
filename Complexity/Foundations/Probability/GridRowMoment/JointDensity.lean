/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.GridRowMoment

/-!
# Joint densities of rounded grid channels

Two distinct role coordinates are independent even with arbitrary inherited copy padding.
The exact joint density is the product of the rounded grid masses. This extracts the
calculation previously used inside the initial perturbation estimate.

## Main results

* `grid_joint_density`: exact product mass on distinct endpoint roles.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability NormalizedMoments
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Exact independent endpoint mass, including arbitrary copy suffixes and zero padding. -/
theorem grid_joint_density (D : ZMod P) (s t : Fin J) (hst : s ≠ t) (ks ka : ℕ)
    (ss st : List (ZMod P)) (x y : ZMod P) :
    (({σ : Environment P J | retainedMask s (side P ks) D ss σ x ∧
      retainedMask t (side P ka) D st σ y} : Finset _).dens : ℝ) =
      gridMass P ks * gridMass P ka := by
  have hh := congrArg (fun z : ℚ≥0 => (z : ℝ))
    (independent (P := P) s t hst.symm
      (side P ks) (side P ka) (CopyPadding.identifier D ss x)
        (CopyPadding.identifier D st y))
  have hmarg (k : ℕ) (v : ZMod P) :
      (dens {a : FrameChannel P 4 1 | frameRetains P 4 (side P k) a v} : ℝ) =
        gridMass P k := by
    have h := congrArg (fun z : ℚ≥0 => (z : ℝ))
      (dens_eval_mem_retentionBox (P := P) (H := 4) (r := 1)
        (by decide) (side_le P k) v)
    push_cast at h
    simp only [nnratCast_dens] at h ⊢
    convert h using 1
    congr 2
  have hl := hmarg ks (CopyPadding.identifier D ss x)
  have hr := hmarg ka (CopyPadding.identifier D st y)
  simp only [NNRat.cast_mul, nnratCast_dens] at hh hl hr ⊢
  convert hh.trans (congrArg₂ (· * ·) hl hr) using 1
  congr 2
  apply congrArg Finset.card
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  rfl

end Matrix.HierarchyParams.H4RankEnvironment
