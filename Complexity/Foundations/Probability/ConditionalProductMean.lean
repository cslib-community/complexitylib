/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.ProductError
public import Complexity.Foundations.Probability.TrueSampleMeans
public import Complexity.Foundations.Analysis.RootError
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional product means

The conditioning event for a source `x` and endpoint `y` is the actual finite slice
`{σ | X σ x ∧ Y σ y}`. Its mean is `Cslib.conditionalTableMean`. The homogeneous loss
contracts through this finite expectation; multiplication by the slice's actual density
cancels the conditioning denominator before the source and endpoint sums are taken.
Empty slices have mean zero and need no nonemptiness hypothesis.

The resulting root-metric comparison consumes the concrete coupled product estimate of
`Complexity.Foundations.Probability.ProductError`. For a coarse bin `b ≥ a`, the common
coefficient is `(b / a) * (f / πf)`: homogeneity contributes one factor `b / a`, and source
release contributes exactly `f / u` to the right error. The conservative comparison constant
is `(2 ^ (s - 1) * s ^ s) * (2 ^ (2 * (s - 1)) * s ^ s)`.

The product-seed slice identity connects this finite operator to the actual true-atom
expectation in `Matrix.expect_correctionAtom_mul_denseAtom`. No estimator mean or error
contract is assumed. Fine-bin conditioning changes, domination of true signed contributions,
and the recursive estimator remain separate.

## Main results

* `Cslib.dens_mul_homogeneousLoss_expect_le`: finite conditional contraction with exact density.
* `Cslib.rootDistPow_conditionalTableMean_mul_le`: the integrated root-error comparison.
* `Cslib.rootDistPow_coarseProductMean_le`: the coarse-bin coefficient and source release.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 7.2--7.3, Lemmas 7.1--7.3, September 23, 2026 revision `7ef5c0cc`
  (preprint, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib

/-- The homogeneous loss contracts through an actual finite mean, including the empty mean. -/
theorem homogeneousLoss_expect_le {Ω : Type*} (S : Finset Ω) {s : ℕ} (hs : s ≠ 0)
    {H H' : Ω → ℝ} (hH : ∀ σ ∈ S, 0 ≤ H σ) (hH' : ∀ σ ∈ S, 0 ≤ H' σ) :
    homogeneousLoss s (𝔼 σ ∈ S, H σ) (𝔼 σ ∈ S, H' σ) ≤
      𝔼 σ ∈ S, homogeneousLoss s (H σ) (H' σ) := by
  simpa only [expect_eq_sum_div_card, div_eq_inv_mul, mul_sum] using
    homogeneousLoss_sum_le S hs (w := fun _ => (#S : ℝ)⁻¹)
      (fun _ _ => by positivity) hH hH'

/-- Multiplying by the actual conditioning density cancels the conditional denominator.
All quantities may depend on the same draw, and the slice may be empty. -/
theorem dens_mul_homogeneousLoss_expect_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (S : Finset Ω)
    {s : ℕ} (hs : s ≠ 0) {H H' : Ω → ℝ}
    (hH : ∀ σ ∈ S, 0 ≤ H σ) (hH' : ∀ σ ∈ S, 0 ≤ H' σ) :
    (dens S : ℝ) * homogeneousLoss s (𝔼 σ ∈ S, H σ) (𝔼 σ ∈ S, H' σ) ≤
      𝔼 σ, if σ ∈ S then homogeneousLoss s (H σ) (H' σ) else 0 := by
  classical
  calc
    _ ≤ (dens S : ℝ) * 𝔼 σ ∈ S, homogeneousLoss s (H σ) (H' σ) :=
      mul_le_mul_of_nonneg_left (homogeneousLoss_expect_le S hs hH hH') (by positivity)
    _ = _ := by
      rw [expect_eq_dens_mul_expect_of_eq_zero S _ (fun σ hσ => ite_eq_right hσ)]
      congr 1
      exact expect_congr rfl fun σ hσ => (ite_eq_left hσ).symm

private theorem dens_mul_root_expect_sub_pow_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) {s : ℕ} (hs : s ≠ 0) {c : ℝ} (hc : 0 ≤ c) {H H' : Ω → ℝ}
    (hH : ∀ σ ∈ S, 0 ≤ H σ) (hH' : ∀ σ ∈ S, 0 ≤ H' σ) :
    (dens S : ℝ) * |(c * 𝔼 σ ∈ S, H σ) ^ (s⁻¹ : ℝ) -
        (c * 𝔼 σ ∈ S, H' σ) ^ (s⁻¹ : ℝ)| ^ s ≤
      (2 ^ (s - 1) * (s : ℝ) ^ s) * c *
        𝔼 σ, if σ ∈ S then |H σ ^ (s⁻¹ : ℝ) - H' σ ^ (s⁻¹ : ℝ)| ^ s else 0 := by
  classical
  have hmean := rpow_inv_sub_pow_le_homogeneousLoss hs
    (mul_nonneg hc (expect_nonneg hH)) (mul_nonneg hc (expect_nonneg hH'))
  have hpoint : (𝔼 σ, if σ ∈ S then homogeneousLoss s (H σ) (H' σ) else 0) ≤
      (s : ℝ) ^ s * 𝔼 σ, if σ ∈ S then |H σ ^ (s⁻¹ : ℝ) - H' σ ^ (s⁻¹ : ℝ)| ^ s else 0 := by
    rw [mul_expect]
    refine expect_le_expect fun σ _ => ?_
    split_ifs with hσ
    · exact homogeneousLoss_le_rpow_inv_sub_pow hs (hH σ hσ) (hH' σ hσ)
    · simp
  calc
    _ ≤ (dens S : ℝ) * (2 ^ (s - 1) * homogeneousLoss s
        (c * 𝔼 σ ∈ S, H σ) (c * 𝔼 σ ∈ S, H' σ)) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = (2 ^ (s - 1) * c) * ((dens S : ℝ) * homogeneousLoss s
        (𝔼 σ ∈ S, H σ) (𝔼 σ ∈ S, H' σ)) := by
      rw [homogeneousLoss_mul hs hc]
      ring
    _ ≤ (2 ^ (s - 1) * c) *
        𝔼 σ, if σ ∈ S then homogeneousLoss s (H σ) (H' σ) else 0 :=
      mul_le_mul_of_nonneg_left (dens_mul_homogeneousLoss_expect_le S hs hH hH') (by positivity)
    _ ≤ (2 ^ (s - 1) * c) * ((s : ℝ) ^ s *
        𝔼 σ, if σ ∈ S then |H σ ^ (s⁻¹ : ℝ) - H' σ ^ (s⁻¹ : ℝ)| ^ s else 0) :=
      mul_le_mul_of_nonneg_left hpoint (by positivity)
    _ = _ := by ring

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

/-- The actual finite conditional mean on the source/endpoint slice. It is zero when that
slice is empty. The output is a deterministic table, indexed by the source and endpoint. -/
@[expose] noncomputable def conditionalTableMean (X Y : Ω → V → Prop)
    [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (H : Ω → V → V → ℝ) (x y : V) : ℝ :=
  𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), H σ x y

omit [Fintype V] in
/-- With separate source, intermediate and terminal seed coordinates, the actual slice is
exactly the product slice used by `Matrix.expect_correctionAtom_mul_denseAtom`. -/
theorem conditionalTableMean_eq_expect_product {ι κ υ : Type*}
    [Fintype ι] [Fintype κ] [Fintype υ] (X : ι → V → Prop) (Y : υ → V → Prop)
    [∀ t x, Decidable (X t x)] [∀ t y, Decidable (Y t y)]
    (H : ((ι × κ) × υ) → V → V → ℝ) (x y : V) :
    conditionalTableMean (fun d v => X d.1.1 v) (fun d v => Y d.2 v) H x y =
      𝔼 d ∈ (({t | X t x} : Finset ι) ×ˢ (univ : Finset κ)) ×ˢ ({t | Y t y} : Finset υ),
        H d x y := by
  unfold conditionalTableMean
  congr 1
  ext d
  simp

variable {s : ℕ} {N u : ℝ} {X Y : Ω → V → Prop}
  [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]

/-- Exchange the finite expectation with the source and endpoint sums, preserving their
actual joint mask. The two masks and the table may depend on the same draw. -/
theorem expect_filtered_sum_eq (H : Ω → V → V → ℝ) :
    (𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), H σ x y) =
      ∑ x, ∑ y, 𝔼 σ, if X σ x ∧ Y σ y then H σ x y else 0 := by
  have hpoint : ∀ σ,
      (∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), H σ x y) =
        ∑ x, ∑ y, if X σ x ∧ Y σ y then H σ x y else 0 := by
    intro σ
    rw [sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : X σ x
    · simp [hx, sum_filter]
    · simp [hx]
  simp_rw [hpoint]
  rw [expect_sum_comm]
  exact sum_congr rfl fun x _ => expect_sum_comm _ _ _

/-- A constant restricted to a finite event has expectation equal to its actual density
times that constant, including empty events and empty ambient types. -/
theorem expect_mask_const [DecidableEq Ω] (S : Finset Ω) (c : ℝ) :
    (𝔼 σ, if σ ∈ S then c else 0) = (dens S : ℝ) * c := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · simpa only [NNRat.smul_def, expect_const hS] using Fintype.expect_ite_mem S (fun _ => c)

/-- **Integrated conditional-mean comparison**. Multiplication by the same nonnegative scalar
costs one power of that scalar. The actual conditioning density cancels before summing over
source and endpoint coordinates. Neither nonempty slices nor independence are required. -/
theorem rootDistPow_conditionalTableMean_mul_le (hs : s ≠ 0) (hN : 0 < N) (hu : 0 < u)
    {c : ℝ} (hc : 0 ≤ c) {H H' : Ω → V → V → ℝ}
    (hH : ∀ σ x y, 0 ≤ H σ x y) (hH' : ∀ σ x y, 0 ≤ H' σ x y) :
    rootDistPow s N u X Y (fun _ x y => c * conditionalTableMean X Y H x y)
        (fun _ x y => c * conditionalTableMean X Y H' x y) ≤
      (2 ^ (s - 1) * (s : ℝ) ^ s) * c * rootDistPow s N u X Y H H' := by
  classical
  rw [rootDistPow, rowNormPow, expect_filtered_sum_eq]
  calc
    _ ≤ (N * u)⁻¹ * ∑ x, ∑ y, (2 ^ (s - 1) * (s : ℝ) ^ s) * c *
        𝔼 σ, if X σ x ∧ Y σ y then |H σ x y ^ (s⁻¹ : ℝ) - H' σ x y ^ (s⁻¹ : ℝ)| ^ s else 0 := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => sum_le_sum fun y _ => ?_)
        (by positivity)
      have hmask := expect_mask_const ({σ | X σ x ∧ Y σ y} : Finset Ω)
        (|(c * conditionalTableMean X Y H x y) ^ (s⁻¹ : ℝ) -
          (c * conditionalTableMean X Y H' x y) ^ (s⁻¹ : ℝ)| ^ s)
      simp only [mem_filter, mem_univ, true_and] at hmask
      rw [hmask]
      simpa only [conditionalTableMean, mem_filter, mem_univ, true_and] using
        dens_mul_root_expect_sub_pow_le ({σ | X σ x ∧ Y σ y} : Finset Ω) hs hc
          (fun σ _ => hH σ x y) (fun σ _ => hH' σ x y)
    _ = _ := by
      rw [rootDistPow, rowNormPow, expect_filtered_sum_eq]
      simp only [← mul_sum]
      ring

/-- **Coarse-bin conditional product comparison**. The sample is the actual finite product
mean multiplied by `(b / a) * (f / πf)`, as in (7.2) after division by `a`, with `b ≥ a`.
The coefficient `f / πf` is left explicit; identifying `πf` with the intermediate channel's
uniform hit density is part of `Matrix.expect_correctionAtom_mul_denseAtom`.

This estimate proves the single-power `b / a` cost and exact right-source factor `f / u`.
It concerns root error; clipped relative error additionally needs domination by the true raw
input, and the finer `b < a` bound requires changing terminal conditioning first. -/
theorem rootDistPow_coarseProductMean_le {Z : Ω → V → Prop}
    [∀ σ z, Decidable (Z σ z)] {a b f πf : ℝ}
    (hs : s ≠ 0) (hN : 0 < N) (hu : 0 < u) (ha : 0 < a) (hab : a ≤ b)
    (hf : 0 < f) (hπf : 0 < πf) {F F' B B' : Ω → V → V → ℝ}
    (hF : ∀ σ x z, 0 ≤ F σ x z) (hF' : ∀ σ x z, 0 ≤ F' σ x z)
    (hB : ∀ σ z y, 0 ≤ B σ z y) (hB' : ∀ σ z y, 0 ≤ B' σ z y)
    {CF CB : ℝ} (hCF : 0 ≤ CF) (hCB : 0 ≤ CB)
    (hFbound : ∀ σ x z, F' σ x z ≤ CF) (hBbound : ∀ σ z y, B σ z y ≤ CB)
    {Kr Kc : ℕ} (hrow : ∀ σ z, Z σ z → #{y ∈ ({y | Y σ y} : Finset V) | B σ z y ≠ 0} ≤ Kr)
    (hcol : ∀ σ z, Z σ z → #{x ∈ ({x | X σ x} : Finset V) | F' σ x z ≠ 0} ≤ Kc) :
    let P := fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), F σ x z * B σ z y
    let P' := fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), F' σ x z * B' σ z y
    rootDistPow s N u X Y (fun _ x y => (b / a) * (f / πf) * conditionalTableMean X Y P x y)
        (fun _ x y => (b / a) * (f / πf) * conditionalTableMean X Y P' x y) ≤
      ((2 ^ (s - 1) * (s : ℝ) ^ s) * (2 ^ (2 * (s - 1)) * (s : ℝ) ^ s)) *
        ((b / a) * (f / πf)) *
        (CB * Kr * rootDistPow s N u X Z F F' +
          CF * Kc * (f / u) * rootDistPow s N f Z Y B B') := by
  dsimp only
  have hb : 0 ≤ b := ha.le.trans hab
  have hc : 0 ≤ (b / a) * (f / πf) := by positivity
  calc
    _ ≤ (2 ^ (s - 1) * (s : ℝ) ^ s) * ((b / a) * (f / πf)) *
        rootDistPow s N u X Y
          (fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), F σ x z * B σ z y)
          (fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), F' σ x z * B' σ z y) :=
      rootDistPow_conditionalTableMean_mul_le hs hN hu hc
        (fun σ x y => sum_nonneg fun z _ => mul_nonneg (hF σ x z) (hB σ z y))
        (fun σ x y => sum_nonneg fun z _ => mul_nonneg (hF' σ x z) (hB' σ z y))
    _ ≤ (2 ^ (s - 1) * (s : ℝ) ^ s) * ((b / a) * (f / πf)) *
        ((2 ^ (2 * (s - 1)) * (s : ℝ) ^ s) *
          (CB * Kr * rootDistPow s N u X Z F F' +
            CF * Kc * (f / u) * rootDistPow s N f Z Y B B')) :=
      mul_le_mul_of_nonneg_left
        (rootDistPow_mul_le hs hN hu hf hF hF' hB hB' hCF hCB hFbound hBbound hrow hcol)
        (by positivity)
    _ = _ := by ring

end Cslib
