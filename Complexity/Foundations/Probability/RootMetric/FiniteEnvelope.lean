/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.RootMetric.AbsoluteError

/-!
# Common envelopes for finitely many row tables

The zero-padded maximum of scaled absolute prefix envelopes dominates each prefix.
Its fourth moment costs the sum of the scaled prefix fourth moments. Empty prefix
sets give zero. The masks and all tables may share one finite environment.

## Main definitions

* `Cslib.finiteEnvelope`: zero-padded maximum of scaled absolute prefix envelopes.

## Main results

* `Cslib.rowNormPow_finiteEnvelope_le`: sum of scaled prefix moments pays the maximum.
* `Cslib.rowNormPow_finiteEnvelope_le_card_mul`: finite uniform allocation.
-/
public section
noncomputable section
namespace Cslib
open Finset
open scoped BigOperators

/-- A common deterministic envelope, with zero padding for an empty prefix set. -/
@[expose] def finiteEnvelope {I V : Type*} (S : Finset I)
    (a : I → ℝ) (E : I → V → V → ℝ) (x y : V) : ℝ :=
  kthLargest 1 S (fun i => |E i x y / a i|)

/-- Zero padding makes every common envelope nonnegative. -/
lemma finiteEnvelope_nonneg {I V : Type*} (S : Finset I)
    (a : I → ℝ) (E : I → V → V → ℝ) (x y : V) :
    0 ≤ finiteEnvelope S a E x y := kthLargest_nonneg

/-- No prefixes means zero, including at the zero horizon. -/
@[simp] lemma finiteEnvelope_empty {I V : Type*}
    (a : I → ℝ) (E : I → V → V → ℝ) (x y : V) :
    finiteEnvelope ∅ a E x y = 0 := by
  simp [finiteEnvelope, kthLargest]

/-- Each actual prefix is below the common envelope times its positive scale. -/
lemma le_finiteEnvelope_mul {I V : Type*} (S : Finset I)
    (a : I → ℝ) (E : I → V → V → ℝ) {i : I} (hi : i ∈ S)
    (ha : 0 < a i) (x y : V) :
    |E i x y| ≤ finiteEnvelope S a E x y * a i := by
  have h := abs_le_kthLargest_one S (fun i => E i x y / a i) i hi
  rw [abs_div, abs_of_pos ha] at h
  exact (div_le_iff₀ ha).mp h

/-- Max fourth power is at most the sum of scaled actual prefix powers. -/
lemma finiteEnvelope_pow_four_le {I V : Type*} (S : Finset I)
    (a : I → ℝ) (E : I → V → V → ℝ) (x y : V) :
    |finiteEnvelope S a E x y| ^ 4 ≤ ∑ i ∈ S, |E i x y / a i| ^ 4 :=
  abs_kthLargest_pow_le_sum S (fun i => E i x y / a i) (by decide)

/-- Integrating a finite common envelope preserves every prefix's actual mask density. -/
theorem rowNormPow_finiteEnvelope_le {I Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : Finset I) (a : I → ℝ) (E : I → V → V → ℝ)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u X Y (fun _ => finiteEnvelope S a E) ≤
      ∑ i ∈ S, rowNormPow 4 N u X Y (fun _ x y => E i x y / a i) := by
  unfold rowNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ y ∈ ({y | Y σ y} : Finset V), ∑ i ∈ S, |E i x y / a i| ^ 4 := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
      exact sum_le_sum fun x _ => sum_le_sum fun y _ => finiteEnvelope_pow_four_le S a E x y
    _ = _ := by
      simp_rw [sum_comm (s := ({y | Y _ y} : Finset V)) (t := S)]
      simp_rw [sum_comm (s := ({x | X _ x} : Finset V)) (t := S)]
      rw [expect_sum_comm, mul_sum]

/-- A finite uniform allocation suffices when every divisor is at least one.
The explicit factor is the number of prefixes; no horizon-independent growth is claimed. -/
theorem rowNormPow_finiteEnvelope_le_card_mul {I Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : Finset I) (a : I → ℝ) (E : I → V → V → ℝ)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    {N u budget : ℝ} (hNu : 0 ≤ N * u) (ha : ∀ i ∈ S, 1 ≤ a i)
    (hE : ∀ i ∈ S, rowNormPow 4 N u X Y (fun _ => E i) ≤ budget) :
    rowNormPow 4 N u X Y (fun _ => finiteEnvelope S a E) ≤ S.card * budget := by
  apply (rowNormPow_finiteEnvelope_le S a E X Y hNu).trans
  calc
    _ ≤ ∑ _i ∈ S, budget := sum_le_sum fun i hi => le_trans (by
      unfold rowNormPow
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu)
      apply expect_le_expect
      intro σ _
      refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
      rw [abs_div, abs_of_nonneg (zero_le_one.trans (ha i hi))]
      exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (zero_le_one.trans (ha i hi)))
        (div_le_self (abs_nonneg _) (ha i hi)) 4) (hE i hi)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

end Cslib
