/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric.WeightedError
public import Complexity.Foundations.Probability.ProductError

/-!
# Unaveraged weighted product perturbations

Bounded conversion applies to the product before conditional averaging. The
coupled rooted product estimate retains the right factor's reset source, its own
usage mask and the exact source-rate ratio. All factors may share one environment.
These original finite inequalities introduce no environment-cardinality loss.

## Main results

* `Cslib.rowNormPow_weighted_product_sub_le_root`: ordinary fourth-moment transport
  from the two own-domain rooted errors, with explicit ranges, gates and weights.
-/

public section
noncomputable section
open Finset
open scoped BigOperators

namespace Cslib

/-- Unaveraged product perturbation on a parent's terminal mask. The right error
is on its own reset-source/usage masks. The explicit finite weight norm may
contain midpoint density and importance factors. No environment atom is extracted. -/
theorem rowNormPow_weighted_product_sub_le_root
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u f CA CB : ℝ}
    (hN : 0 < N) (hu : 0 < u) (hf : 0 < f) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (X Z Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ z, Decidable (Z σ z)] [∀ σ y, Decidable (Y σ y)]
    [∀ σ y, Decidable (U σ y)]
    (L L' R R' : Ω → V → V → ℝ) (w : V → ℝ) (KL KR Kc : ℕ)
    (hL : ∀ σ x z, L σ x z ∈ Set.Icc 0 CA)
    (hL' : ∀ σ x z, L' σ x z ∈ Set.Icc 0 CA)
    (hR : ∀ σ z y, R σ z y ∈ Set.Icc 0 CB)
    (hR' : ∀ σ z y, R' σ z y ∈ Set.Icc 0 CB)
    (hl : ∀ σ x, #{z ∈ ({z | Z σ z} : Finset V) | L σ x z ≠ 0} ≤ KL)
    (hl' : ∀ σ x, #{z ∈ ({z | Z σ z} : Finset V) | L' σ x z ≠ 0} ≤ KL)
    (hr : ∀ σ z, Z σ z → #{y ∈ ({y | U σ y} : Finset V) | R σ z y ≠ 0} ≤ KR)
    (hc : ∀ σ z, Z σ z → #{x ∈ ({x | X σ x} : Finset V) | L' σ x z ≠ 0} ≤ Kc)
    (hoff : ∀ σ z y, ¬ U σ y → R σ z y = 0 ∧ R' σ z y = 0) :
    rowNormPow 4 N u X Y (fun σ x y => w y *
      ((∑ z ∈ ({z | Z σ z} : Finset V), L σ x z * R σ z y) -
        ∑ z ∈ ({z | Z σ z} : Finset V), L' σ x z * R' σ z y)) ≤
      ‖w‖ ^ 4 * (4 * ((KL : ℝ) * CA * CB) ^ ((3 : ℝ) / 4)) ^ 4 *
        (16384 * (CB * KR * rootDistPow 4 N u X Z L L' +
          CA * Kc * (f / u) * rootDistPow 4 N f Z U R R')) := by
  classical
  let F := fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), L σ x z * R σ z y
  let F' := fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), L' σ x z * R' σ z y
  have bound (A B : Ω → V → V → ℝ)
      (ha : ∀ σ x z, A σ x z ∈ Set.Icc 0 CA)
      (hb : ∀ σ z y, B σ z y ∈ Set.Icc 0 CB)
      (hk : ∀ σ x, #{z ∈ ({z | Z σ z} : Finset V) | A σ x z ≠ 0} ≤ KL)
      (σ : Ω) (x y : V) :
      (∑ z ∈ ({z | Z σ z} : Finset V), A σ x z * B σ z y) ∈
        Set.Icc 0 ((KL : ℝ) * CA * CB) := by
    refine ⟨sum_nonneg (fun z _ => mul_nonneg (ha σ x z).1 (hb σ z y).1), ?_⟩
    rw [← sum_filter_of_ne (p := fun z => A σ x z ≠ 0)
      (fun z _ h hz => h (by rw [hz, zero_mul]))]
    calc
      _ ≤ ∑ z ∈ ({z | Z σ z} : Finset V) with A σ x z ≠ 0, CA * CB :=
        sum_le_sum fun z _ => mul_le_mul (ha σ x z).2 (hb σ z y).2
          (hb σ z y).1 hCA
      _ ≤ (KL : ℝ) * CA * CB := by
        rw [sum_const, nsmul_eq_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk σ x) (mul_nonneg hCA hCB)
  have hw := rowNormPow_weighted_sub_le_rootDistPow (mul_pos hN hu).le X Y U F F' w
    (bound L R hL hR hl) (bound L' R' hL' hR' hl') (by
      intro σ x y hy
      have hr0 : ∀ z, R σ z y = 0 := fun z => (hoff σ z y hy).1
      have hr1 : ∀ z, R' σ z y = 0 := fun z => (hoff σ z y hy).2
      simp only [F, F', hr0, hr1, mul_zero, sum_const_zero])
  have hp := rootDistPow_mul_le (s := 4) (by decide) hN hu hf
    (fun σ x z => (hL σ x z).1) (fun σ x z => (hL' σ x z).1)
    (fun σ z y => (hR σ z y).1) (fun σ z y => (hR' σ z y).1)
    hCA hCB (fun σ x z => (hL' σ x z).2) (fun σ z y => (hR σ z y).2) hr hc
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat] at hp
  exact hw.trans (mul_le_mul_of_nonneg_left hp (by positivity))

end Cslib
