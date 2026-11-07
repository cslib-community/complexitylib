/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.ConditionalProductMean
public import Complexity.Foundations.Probability.RootMetric.WeightedError
public import Complexity.Foundations.Probability.RootMetric.Minkowski
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Clipped accuracy of positive conditional means

These finite estimates clip after averaging on the actual joint slice. Only the canonical
mean is dominated by the target; the approximate mean needs no such support hypothesis.
They do not control centered sampling noise or a separate saturated preparation signal.
The fourth-power fidelity estimate follows from the homogeneous-loss API, avoiding a
second proof of reverse Minkowski. The scalar constant agrees with `fidelity` in the supplied
OpenAI reference `AffineSampling.lean` at revision `4eaee87548250b2682affda7d05d947c05554bae`.

## Main results

* `Cslib.min_relative_sub_le_root_four`: scalar fidelity with one-sided domination.
* `Cslib.min_relative_expect_sub_four_le`: a positive conditional-mean moment payment.
* `Cslib.min_abs_sum_div_le`: signed sums after the positive-summand comparisons.
* `Cslib.rowNormPow_le_rootDistPow_of_conditional`: own-mask integration of conditional bounds.
* `Cslib.rowNormPow_clipped_sum_le`: correlated signed sums of clipped payments.
* `Cslib.rowNormPow_sliceMean_change_terminal_fourth_le`: exact density-cubed mean transport.
-/
public section
namespace Cslib
open Finset
open scoped BigOperators

/-- Clipped fourth-root fidelity. The canonical value `s` is dominated, but `t` may be
arbitrarily large. This is the scalar reference `fidelity`, with the same constant 32. -/
theorem min_relative_sub_le_root_four {s t D K : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hD : 0 ≤ D) (hK : 1 ≤ K) (hdom : s ≤ K * D) :
    min 1 (|s - t| / (1 + D)) ≤ 32 * K * |s ^ (4⁻¹ : ℝ) - t ^ (4⁻¹ : ℝ)| := by
  have hk : 0 ≤ K := by linarith
  have h := mul_min_pow_le_homogeneousLoss (s := 4) (by decide) hk hD
    (by norm_num : (0 : ℝ) < 1) hs hdom ht
  have hr := homogeneousLoss_le_rpow_inv_sub_pow (s := 4) (by decide) hs ht
  norm_num only [one_mul, Nat.reduceSub, Nat.cast_ofNat] at h
  norm_num only [Nat.cast_ofNat, show (4⁻¹ : ℝ) = 1 / 4 from by norm_num] at hr ⊢
  have hc : 2 * (3 * K + 3) ^ 3 * (4 : ℝ) ^ 4 ≤ (32 * K) ^ 4 := by
    have h3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 * K + 3)
      (show 3 * K + 3 ≤ 6 * K by linarith) 3
    have h4 : K ^ 3 ≤ K ^ 4 := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ K ^ 3) (sub_nonneg.mpr hK)]
    nlinarith
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4 ≠ 0)).mp
  rw [mul_pow]
  have hm := mul_le_mul_of_nonneg_right hc
    (pow_nonneg (abs_nonneg (s ^ (1 / 4 : ℝ) - t ^ (1 / 4 : ℝ))) 4)
  exact h.trans ((mul_le_mul_of_nonneg_left hr (by positivity)).trans (by nlinarith))

/-- Clipped triangle inequality for signed errors with one fixed positive denominator. -/
theorem min_abs_add_div_le {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    min 1 (|x + y| / a) ≤ min 1 (|x| / a) + min 1 (|y| / a) := by
  have hx : 0 ≤ min 1 (|x| / a) := by positivity
  have hy : 0 ≤ min 1 (|y| / a) := by positivity
  by_cases hx1 : 1 ≤ |x| / a
  · rw [min_eq_left hx1]
    exact (min_le_left _ _).trans (by linarith)
  by_cases hy1 : 1 ≤ |y| / a
  · rw [min_eq_left hy1]
    exact (min_le_left _ _).trans (by linarith)
  rw [min_eq_right (le_of_not_ge hx1), min_eq_right (le_of_not_ge hy1), ← add_div]
  exact (min_le_right _ _).trans
    (div_le_div_of_nonneg_right (abs_add_le x y) ha.le)

/-- Finite signed sums are clipped after adding. Apply positive mean domination to each
summand separately before invoking this inequality on a paired difference or prefix. -/
theorem min_abs_sum_div_le {ι : Type*} (S : Finset ι) {a : ℝ} (ha : 0 < a) (e : ι → ℝ) :
    min 1 (|∑ i ∈ S, e i| / a) ≤ ∑ i ∈ S, min 1 (|e i| / a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (min_abs_add_div_le ha _ _).trans (add_le_add_right ih _)

/-- Clipping after a common finite conditional mean costs one power of the physical
scale `c`. Empty slices are allowed. All samples may be correlated. Domination is required
before subtracting any signed summands. Ordinary progress is a separate payment. -/
theorem min_relative_expect_sub_four_le {Ω : Type*} (S : Finset Ω)
    {C A : Ω → ℝ} {c D K : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hC : ∀ σ ∈ S, 0 ≤ C σ) (hA : ∀ σ ∈ S, 0 ≤ A σ)
    (hdom : c * (𝔼 σ ∈ S, C σ) ≤ K * D) :
    min 1 (|c * (𝔼 σ ∈ S, (A σ - C σ))| / (1 + D)) ^ 4 ≤
      (512 * (3 * K + 3) ^ 3) * c *
        𝔼 σ ∈ S, |A σ ^ (4⁻¹ : ℝ) - C σ ^ (4⁻¹ : ℝ)| ^ 4 := by
  have h := mul_min_pow_le_homogeneousLoss (s := 4) (by decide) hK hD
    (by norm_num : (0 : ℝ) < 1) (mul_nonneg hc (expect_nonneg hC)) hdom
    (mul_nonneg hc (expect_nonneg hA))
  rw [one_mul, homogeneousLoss_mul (by decide) hc] at h
  have he := homogeneousLoss_expect_le S (s := 4) (by decide) hC hA
  have hp : (𝔼 σ ∈ S, homogeneousLoss 4 (C σ) (A σ)) ≤
      256 * 𝔼 σ ∈ S, |A σ ^ (4⁻¹ : ℝ) - C σ ^ (4⁻¹ : ℝ)| ^ 4 := by
    rw [mul_expect]
    apply expect_le_expect
    intro σ hσ
    have hr := homogeneousLoss_le_rpow_inv_sub_pow (s := 4) (by decide) (hC σ hσ) (hA σ hσ)
    norm_num only [Nat.cast_ofNat, show (4 : ℝ) ^ 4 = 256 from by norm_num] at hr
    simpa only [abs_sub_comm, show (4⁻¹ : ℝ) = 1 / 4 from by norm_num] using hr
  have heq : |c * (𝔼 σ ∈ S, (A σ - C σ))| =
      |c * (𝔼 σ ∈ S, C σ) - c * (𝔼 σ ∈ S, A σ)| := by
    rw [expect_sub_distrib, mul_sub, abs_sub_comm]
  rw [heq]
  calc
    _ ≤ 2 * (3 * K + 3) ^ (4 - 1) * (c * homogeneousLoss 4
        (𝔼 σ ∈ S, C σ) (𝔼 σ ∈ S, A σ)) := h
    _ ≤ 2 * (3 * K + 3) ^ (4 - 1) * (c * (256 *
        𝔼 σ ∈ S, |A σ ^ (4⁻¹ : ℝ) - C σ ^ (4⁻¹ : ℝ)| ^ 4)) := by
      gcongr
      exact he.trans hp
    _ = _ := by ring

/-- Integrate a conditional clipped estimate onto the error's own terminal mask.
The endpoint coefficient is linear, not fourth-powered. Fubini cancels the actual joint
slice densities; errors and both masks may be correlated. Off-usage equality is essential. -/
theorem rowNormPow_le_rootDistPow_of_conditional
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] [∀ σ y, Decidable (U σ y)]
    (A C : Ω → V → V → ℝ) (e : V → V → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hoff : ∀ σ x y, ¬ U σ y → A σ x y = C σ x y)
    (h : ∀ x y, |e x y| ^ 4 ≤ c *
      𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω),
        |A σ x y ^ (4⁻¹ : ℝ) - C σ x y ^ (4⁻¹ : ℝ)| ^ 4) :
    rowNormPow 4 N u X Y (fun _ => e) ≤ c * rootDistPow 4 N u X U A C := by
  let E := fun σ x y => A σ x y ^ (4⁻¹ : ℝ) - C σ x y ^ (4⁻¹ : ℝ)
  have hj : rowNormPow 4 N u X Y (fun _ => e) ≤ c * rowNormPow 4 N u X Y E := by
    apply rowNormPow_le_of_conditional_expect_le hNu E (fun _ => e) c
    intro x y
    let S : Finset Ω := {σ | X σ x ∧ Y σ y}
    rcases S.eq_empty_or_nonempty with hs | hs
    · simp only [show ({σ | X σ x ∧ Y σ y} : Finset Ω) = S from rfl,
        hs, expect_empty, mul_zero, le_refl]
    · rw [show (𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), |e x y| ^ 4) =
          |e x y| ^ 4 from expect_const hs _]
      exact h x y
  have hm : rowNormPow 4 N u X (fun _ _ => True) E = rowNormPow 4 N u X U E := by
    have he : (fun σ x y => if U σ y then E σ x y else 0) = E := by
      funext σ x y
      split_ifs with hy
      · rfl
      · simp only [E, hoff σ x y hy, sub_self]
    have hh := rowNormPow_usage_mask (N := N) (u := u) (X := X)
      (Y := fun _ _ => True) (U := U) (fun _ _ _ => True.intro) E
    rwa [he] at hh
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ hc
  change rowNormPow 4 N u X Y E ≤ rowNormPow 4 N u X U E
  rw [← hm]
  exact rowNormPow_mono_terminal hNu (fun _ _ _ => True.intro) E

/-- Changing a terminal conditioning slice before Jensen retains three powers of its
relative density. The mean and density identities concern the same environment; no
independence of the error table is assumed. -/
theorem rowNormPow_sliceMean_change_terminal_fourth_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u q : ℝ}
    (hNu : 0 ≤ N * u) (hq : 0 ≤ q)
    (X Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] [∀ σ y, Decidable (U σ y)]
    (F : Ω → V → V → ℝ)
    (hmean : ∀ x y, rowSliceMean X Y F x y = q * rowSliceMean X U F x y)
    (hdens : ∀ x y,
      (({σ | X σ x ∧ Y σ y} : Finset Ω).dens : ℝ) * q =
        (({σ | X σ x ∧ U σ y} : Finset Ω).dens : ℝ)) :
    rowNormPow 4 N u X Y (fun _ => rowSliceMean X Y F) ≤
      q ^ 3 * rowNormPow 4 N u X U F := by
  classical
  have he : rowNormPow 4 N u X Y (fun _ => rowSliceMean X Y F) =
      q ^ 3 * rowNormPow 4 N u X U (fun _ => rowSliceMean X U F) := by
    rw [rowNormPow_eq_sum_dens_mul_expect, rowNormPow_eq_sum_dens_mul_expect]
    have hc (Z : Ω → V → Prop) [∀ σ y, Decidable (Z σ y)]
        (x y : V) (v : ℝ) :
        (({σ | X σ x ∧ Z σ y} : Finset Ω).dens : ℝ) *
          (𝔼 _σ ∈ ({σ | X σ x ∧ Z σ y} : Finset Ω), |v| ^ 4) =
        (({σ | X σ x ∧ Z σ y} : Finset Ω).dens : ℝ) * |v| ^ 4 := by
      rcases ({σ | X σ x ∧ Z σ y} : Finset Ω).eq_empty_or_nonempty with h | h
      · simp only [h, dens_empty, NNRat.cast_zero, zero_mul]
      · rw [expect_const h]
    simp_rw [hc, hmean, abs_mul, abs_of_nonneg hq, mul_pow]
    simp_rw [show ∀ x y, (({σ | X σ x ∧ Y σ y} : Finset Ω).dens : ℝ) *
        (q ^ 4 * |rowSliceMean X U F x y| ^ 4) =
        q ^ 3 * ((({σ | X σ x ∧ U σ y} : Finset Ω).dens : ℝ) *
          |rowSliceMean X U F x y| ^ 4) from fun x y => by rw [← hdens x y]; ring]
    simp only [← mul_sum]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (rowNormPow_sliceMean_fourth_le hNu X U F)
    (pow_nonneg hq 3)

/-- The clipped relative triangle inequality at fourth-moment level. The arrays and
masks can share all their randomness; this does not turn a clipped bound into a raw bound. -/
theorem rowNormPow_clipped_add_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (e f : V → V → ℝ) (a : V → V → ℝ) (ha : ∀ x y, 0 < a x y) :
    rowNormPow 4 N u X Y (fun _ x y => min 1 (|e x y + f x y| / a x y)) ≤
      8 * (rowNormPow 4 N u X Y (fun _ x y => min 1 (|e x y| / a x y)) +
        rowNormPow 4 N u X Y (fun _ x y => min 1 (|f x y| / a x y))) := by
  apply le_trans ?_ (rowNormPow_add_le hNu
    (fun _ x y => min 1 (|e x y| / a x y)) (fun _ x y => min 1 (|f x y| / a x y)))
  apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
  intro σ x y _ _
  have haxy := ha x y
  rw [one_mul,
    abs_of_nonneg (show 0 ≤ min 1 (|e x y + f x y| / a x y) by positivity),
    abs_of_nonneg (show 0 ≤ min 1 (|e x y| / a x y) + min 1 (|f x y| / a x y) by positivity)]
  exact pow_le_pow_left₀ (by positivity) (min_abs_add_div_le haxy _ _) 4

/-- Signed, correlated conditional means pay only a finite cardinality cube.
Each summand is clipped before this comparison; the resulting sum is clipped after addition. -/
theorem rowNormPow_clipped_sum_le
    {I Ω V : Type*} [Fintype Ω] [Fintype V] (S : Finset I)
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (e : I → V → V → ℝ) (a : V → V → ℝ) (ha : ∀ x y, 0 < a x y) :
    rowNormPow 4 N u X Y (fun _ x y => min 1 (|∑ i ∈ S, e i x y| / a x y)) ≤
      (#S : ℝ) ^ 3 * ∑ i ∈ S,
        rowNormPow 4 N u X Y (fun _ x y => min 1 (|e i x y| / a x y)) := by
  apply le_trans ?_ (rowNormPow_sum_fourth_le S hNu X Y
    (fun i _ x y => min 1 (|e i x y| / a x y)))
  apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
  intro σ x y _ _
  have haxy := ha x y
  rw [one_mul, abs_of_nonneg (show 0 ≤ min 1 (|∑ i ∈ S, e i x y| / a x y) by positivity),
    abs_of_nonneg (show 0 ≤ ∑ i ∈ S, min 1 (|e i x y| / a x y) by
      exact sum_nonneg fun i _ => le_min (by norm_num) (div_nonneg (abs_nonneg _) haxy.le))]
  exact pow_le_pow_left₀ (by positivity) (min_abs_sum_div_le S (ha x y) _) 4

/-- Correlated signed clipped means pay the fourth power of the sum of rooted budgets.
This is Minkowski on the unchanged joint slice, including empty sums and zero budgets. -/
theorem rowNormPow_clipped_sum_le_pow_sum
    {I Ω V : Type*} [Fintype Ω] [Fintype V] (S : Finset I)
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (e : I → V → V → ℝ) (a : V → V → ℝ) (ha : ∀ x y, 0 < a x y)
    (ε : I → ℝ)
    (herr : ∀ i ∈ S, rowNormPow 4 N u X Y
      (fun _ x y => min 1 (|e i x y| / a x y)) ≤ ε i) :
    rowNormPow 4 N u X Y (fun _ x y => min 1 (|∑ i ∈ S, e i x y| / a x y)) ≤
      (∑ i ∈ S, ε i ^ (4⁻¹ : ℝ)) ^ 4 := by
  have hε (i : I) (hi : i ∈ S) : 0 ≤ ε i :=
    (rowNormPow_nonneg hNu _).trans (herr i hi)
  apply le_trans ?_ (by
    simpa only [one_mul] using rowNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0)
      hNu Y S (fun i _ x y => min 1 (|e i x y| / a x y)) (fun _ => 1)
      (fun i => ε i ^ (4⁻¹ : ℝ)) (fun _ _ => by norm_num)
      (fun i hi => Real.rpow_nonneg (hε i hi) _)
      (fun i hi => by
        have he : (ε i ^ (4⁻¹ : ℝ)) ^ 4 = ε i := by
          convert Real.rpow_inv_natCast_pow (n := 4) (hε i hi) (by decide) using 1
        rw [he]
        exact herr i hi))
  apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
  intro σ x y _ _
  have haxy := ha x y
  rw [one_mul, abs_of_nonneg (show 0 ≤ min 1 (|∑ i ∈ S, e i x y| / a x y) by positivity),
    abs_of_nonneg (show 0 ≤ ∑ i ∈ S, min 1 (|e i x y| / a x y) by
      exact sum_nonneg fun i _ => le_min (by norm_num)
        (div_nonneg (abs_nonneg _) (ha x y).le))]
  exact pow_le_pow_left₀ (by positivity) (min_abs_sum_div_le S (ha x y) _) 4

end Cslib
