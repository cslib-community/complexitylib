/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyResidualDomination

/-!
# Direct bins and the separate negative correction against the signed target

Both bounds follow from the genuine positive input domination. They include zero
targets and do not identify an approximate child's support with canonical support.
The correction bound is for the one negative request, before its subtraction.
-/

public section
open Finset
namespace Matrix.HierarchyParams
variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  {f : ℝ} {C : Matrix V V ℝ}

/-- A nonnegative bin below the genuine base is dominated by the actual signed
residual. No lower bound on the target or finite-bin coverage is required. -/
theorem bin_le_residual (hf : 0 < f)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ f) {A : Matrix V V ℝ}
    (hAC : ∀ x y, A x y ≤ C x y) (x y : V) :
    A x y ≤ max 1 (((P.k : ℝ) + 1) / P.θ) * P.residual X Y f C x y := by
  apply (hAC x y).trans
  apply le_trans ?_ (P.correctionInput_last_le_residual X Y hf hC hC1 hCf x y)
  change C x y ≤ C x y + (P.correctionIter X Y f C P.k * C) x y
  exact le_add_of_nonneg_right (sum_nonneg fun z _ => mul_nonneg
    ((P.isCorrectionSeq_correctionIter (X := X) (Y := Y) hf hC).nonneg P.k x z)
    (hC z y))

/-- The once-negative canonical correction is dominated before subtracting it.
This is derived from the actual nonnegative residual, not target agreement. -/
theorem correction_le_residual (hf : 0 < f)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ f) (x y : V) :
    P.correction X Y f C x y ≤
      max 1 (((P.k : ℝ) + 1) / P.θ) * P.residual X Y f C x y := by
  have hn := P.residual_nonneg (X := X) (Y := Y) hf hC x y
  have hd := P.correctionInput_last_le_residual X Y hf hC hC1 hCf x y
  rw [P.residual_eq, Matrix.add_apply, Matrix.sub_apply] at hn
  simp only [correctionInput, P.correctionIter_last, Matrix.add_apply] at hd
  linarith

end Matrix.HierarchyParams
