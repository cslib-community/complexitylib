/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.PilotRowStability
public import CslibFrontier.Computability.LogSpaceDerandomization.TrueSampleMeans

/-!
# Transporting the actual detector payment to score row moments

The detector's two literal means are integrated by finite Fubini. Reinserting its
terminal conditioning costs the reciprocal of a lower bound on the actual terminal
density. The source rank remains inside its original mask. Estimated scores may
share all outer coordinates; no pointwise extraction from environment atoms is used.
These original finite contracts do not allocate recursive calls or bound parameter growth.

## Main results

* `Matrix.HierarchyParams.PilotRowRecipe.sourceDetector_sum_moment`:
  source-dependent score payment.
* `Matrix.HierarchyParams.PilotRowRecipe.sourceDetector_row_moment_transport`:
  full-product payment.
-/
public section
noncomputable section
open Finset Cslib
open scoped BigOperators

namespace Matrix.HierarchyParams.PilotRowRecipe
variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s x, Decidable (X s x)] [∀ t y, Decidable (Y t y)]

/-- Reinsertion of the terminal event pays its actual density. Both the padded source
rank and double mean retain the child’s source argument. The score table need
not be nonnegative or independent of its terminal seed. -/
theorem sourceDetector_sum_moment {π : ℝ} (hπ : 0 < π)
    (hY : ∀ y, π ≤ (dens {t | Y t y} : ℝ)) (A B : ι → κ → Matrix V V ℝ) :
    (∑ y, |sourceDetector P X Y A y - sourceDetector P X Y B y| ^ 4) ≤
      π⁻¹ * 𝔼 s, 𝔼 t, ∑ x ∈ ({x | X s x} : Finset V),
        ∑ y ∈ ({y | Y t y} : Finset V), |A s t x y - B s t x y| ^ 4 := by
  classical
  let E := fun s t y => ∑ x ∈ ({x | X s x} : Finset V), |A s t x y - B s t x y| ^ 4
  have he (s : ι) (t : κ) (y : V) : 0 ≤ E s t y :=
    sum_nonneg fun _ _ => by positivity
  have hc (s : ι) (y : V) :
      (𝔼 t ∈ {t | Y t y}, E s t y) ≤
        π⁻¹ * 𝔼 t, if Y t y then E s t y else 0 := by
    have hid : (𝔼 t, if Y t y then E s t y else 0) =
        (dens {t | Y t y} : ℝ) * 𝔼 t ∈ {t | Y t y}, E s t y := by
      simpa only [mem_filter, mem_univ, true_and, NNRat.smul_def] using
        (Fintype.expect_ite_mem ({t | Y t y} : Finset κ) (E s · y))
    rw [hid]
    have hm : 0 ≤ 𝔼 t ∈ {t | Y t y}, E s t y := expect_nonneg fun t _ => he s t y
    have hi : 1 ≤ π⁻¹ * (dens {t | Y t y} : ℝ) := by
      rw [inv_mul_eq_div, le_div_iff₀ hπ]
      simpa only [one_mul] using hY y
    nlinarith [mul_le_mul_of_nonneg_right hi hm]
  calc
    _ ≤ ∑ y, 𝔼 s, 𝔼 t ∈ {t | Y t y}, E s t y :=
      sum_le_sum fun y _ => sourceDetector_moment P X Y A B y
    _ ≤ ∑ y, 𝔼 s, π⁻¹ * 𝔼 t, if Y t y then E s t y else 0 :=
      sum_le_sum fun y _ => expect_le_expect fun s _ => hc s y
    _ = _ := by
      simp_rw [← mul_expect]
      rw [← mul_sum, ← expect_sum_comm]
      congr 1
      apply expect_congr rfl
      intro s _
      rw [← expect_sum_comm]
      apply expect_congr rfl
      intro t _
      rw [← sum_filter]
      dsimp only [E]
      rw [sum_comm]

/-- The literal detector payment is a score row moment on the full product of its
outer coordinates and its two actual integration variables. The parent source costs
one vertex width; source normalization changes by `v/u`. Terminal conditioning costs
`1/π`. No source coordinate or spectator dependency is discarded from the child norm. -/
theorem sourceDetector_row_moment_transport {Ω : Type*} [Fintype Ω]
    (Xs Z : Ω → V → Prop) [∀ σ x, Decidable (Xs σ x)] [∀ σ y, Decidable (Z σ y)]
    {N u v π : ℝ} (hN : 0 < N) (hu : 0 < u) (hv : 0 < v) (hπ : 0 < π)
    (hY : ∀ y, π ≤ (dens {t | Y t y} : ℝ))
    (A B : Ω → ι → κ → Matrix V V ℝ) :
    rowNormPow 4 N u Xs Z (fun σ _ y => sourceDetector P X Y (A σ) y -
      sourceDetector P X Y (B σ) y) ≤
    (Fintype.card V : ℝ) * v / (u * π) *
      rowNormPow 4 N v
        (fun (p : Ω × (ι × κ)) x => X p.2.1 x)
        (fun p y => Y p.2.2 y)
        (fun p x y => A p.1 p.2.1 p.2.2 x y - B p.1 p.2.1 p.2.2 x y) := by
  classical
  have hpoint (σ : Ω) :
      (∑ _a ∈ ({a | Xs σ a} : Finset V), ∑ y ∈ ({y | Z σ y} : Finset V),
        |sourceDetector P X Y (A σ) y - sourceDetector P X Y (B σ) y| ^ 4) ≤
      (Fintype.card V : ℝ) * (π⁻¹ * 𝔼 s, 𝔼 t,
        ∑ x ∈ ({x | X s x} : Finset V), ∑ y ∈ ({y | Y t y} : Finset V),
          |A σ s t x y - B σ s t x y| ^ 4) := by
    have hsum : (∑ y ∈ ({y | Z σ y} : Finset V),
        |sourceDetector P X Y (A σ) y - sourceDetector P X Y (B σ) y| ^ 4) ≤
        ∑ y, |sourceDetector P X Y (A σ) y - sourceDetector P X Y (B σ) y| ^ 4 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    calc
      _ ≤ ∑ _a ∈ ({a | Xs σ a} : Finset V),
          ∑ y, |sourceDetector P X Y (A σ) y - sourceDetector P X Y (B σ) y| ^ 4 :=
        sum_le_sum fun _ _ => hsum
      _ ≤ (Fintype.card V : ℝ) *
          (∑ y, |sourceDetector P X Y (A σ) y - sourceDetector P X Y (B σ) y| ^ 4) := by
        simp only [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sourceDetector_sum_moment P X Y hπ hY (A σ) (B σ)) (Nat.cast_nonneg _)
  unfold rowNormPow
  apply (mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => hpoint σ)
    (inv_nonneg.mpr (mul_pos hN hu).le)).trans_eq
  rw [← univ_product_univ, expect_product]
  simp_rw [← univ_product_univ, expect_product]
  rw [← mul_expect, ← mul_expect]
  field_simp

/-- Reinsertion of the terminal event pays its actual density. Both the padded source
rank and the double mean are those of `PilotRowRecipe.detector`. The score table need
not be nonnegative or independent of its terminal seed. -/
theorem detector_sum_moment {π : ℝ} (hπ : 0 < π)
    (hY : ∀ y, π ≤ (dens {t | Y t y} : ℝ)) (A B : κ → Matrix V V ℝ) :
    (∑ y, |detector P X Y A y - detector P X Y B y| ^ 4) ≤
      π⁻¹ * 𝔼 s, 𝔼 t, ∑ x ∈ ({x | X s x} : Finset V),
        ∑ y ∈ ({y | Y t y} : Finset V), |A t x y - B t x y| ^ 4 :=
  sourceDetector_sum_moment P X Y hπ hY (fun _ => A) (fun _ => B)

/-- The literal detector payment is a score row moment on the full product of its
outer coordinates and its two actual integration variables. The parent source costs
one vertex width; source normalization changes by `v/u`. Terminal conditioning costs
`1/π`. No source coordinate or spectator dependency is discarded from the child norm. -/
theorem detector_row_moment_transport {Ω : Type*} [Fintype Ω]
    (Xs Z : Ω → V → Prop) [∀ σ x, Decidable (Xs σ x)] [∀ σ y, Decidable (Z σ y)]
    {N u v π : ℝ} (hN : 0 < N) (hu : 0 < u) (hv : 0 < v) (hπ : 0 < π)
    (hY : ∀ y, π ≤ (dens {t | Y t y} : ℝ))
    (A B : Ω → κ → Matrix V V ℝ) :
    rowNormPow 4 N u Xs Z (fun σ _ y => detector P X Y (A σ) y -
      detector P X Y (B σ) y) ≤
    (Fintype.card V : ℝ) * v / (u * π) *
      rowNormPow 4 N v
        (fun (p : Ω × (ι × κ)) x => X p.2.1 x)
        (fun p y => Y p.2.2 y)
        (fun p x y => A p.1 p.2.2 x y - B p.1 p.2.2 x y) :=
  sourceDetector_row_moment_transport P X Y Xs Z hN hu hv hπ hY (fun σ _ => A σ) (fun σ _ => B σ)

end Matrix.HierarchyParams.PilotRowRecipe
