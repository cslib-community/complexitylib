/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.DenseRowRecipes
public import Complexity.Foundations.Analysis.RootError
public import Complexity.Foundations.Data.Finset.KthLargest.Stability

/-!
# Absolute stability of dense preparation

Preparation compares signed raw rows on the same retained rank slice. Its error is
controlled by the entry error and the full-slice maximum absolute error, both divided
by the actual rate. No target range or independence is required.
-/

public section
namespace Matrix.DenseRowRecipe
open Finset Cslib

/-- Pointwise preparation stability with explicit absolute entry and full-rank errors.
The same padded rank domain is used on both sides, even when it is empty. -/
theorem atomPrep_stability {V : Type*}
    {h ρ : ℝ → ℝ} {Lh Lρ : ℝ} (hh : ∀ z, h z ∈ Set.Icc 0 1)
    (hρ : ∀ z, ρ z ∈ Set.Icc 0 1)
    (hlh : ∀ a b, |h a - h b| ≤ Lh * |a - b|)
    (hlρ : ∀ a b, |ρ a - ρ b| ≤ Lρ * |a - b|)
    (hLρ : 0 ≤ Lρ) {K : ℕ} (hK : 0 < K) {r : ℝ} (hr : 0 < r)
    (A B : Matrix V V ℝ) (S : Finset V) (x y : V) :
    |atomPrep h ρ K r A S x y - atomPrep h ρ K r B S x y| ≤
      (Lh * |A x y - B x y| +
        Lρ * kthLargest 1 S (fun w => |A x w - B x w|)) / r := by
  classical
  let e := kthLargest 1 S (fun w => |A x w - B x w|)
  have hq : |kthLargest K S (fun w => A x w / r) -
      kthLargest K S (fun w => B x w / r)| ≤ e / r :=
    abs_kthLargest_div_sub_div_le hK hr S (A x) (B x)
  have hgate := (hlρ (kthLargest K S (fun w => A x w / r))
    (kthLargest K S (fun w => B x w / r))).trans
    (mul_le_mul_of_nonneg_left hq hLρ)
  have hentry := hlh (A x y / r) (B x y / r)
  rw [← sub_div, abs_div, abs_of_pos hr] at hentry
  have hsplit : |h (A x y / r) * rowGate ρ K r A S x -
      h (B x y / r) * rowGate ρ K r B S x| ≤
      |h (A x y / r) - h (B x y / r)| +
        |rowGate ρ K r A S x - rowGate ρ K r B S x| := by
    calc
      _ = |(h (A x y / r) - h (B x y / r)) * rowGate ρ K r A S x +
          h (B x y / r) * (rowGate ρ K r A S x - rowGate ρ K r B S x)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (by
        rw [abs_mul, abs_mul, rowGate, abs_of_nonneg (hh _).1,
          abs_of_nonneg (hρ _).1]
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (hρ _).2)
          (mul_le_of_le_one_left (abs_nonneg _) (hh _).2))
  exact hsplit.trans ((add_le_add hentry hgate).trans_eq (by dsimp only [e]; ring))

end Matrix.DenseRowRecipe
