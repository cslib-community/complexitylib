/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Minkowski bounds for integrated vertex and row norms

The existing `vertexNormPow` is a normalized finite moment on retained sources. Applying
Mathlib's finite Minkowski inequality to the joint environment/source domain gives a bound
on finite sums with arbitrary correlations. The normalization may vanish, and the environment
or retained source sets may be empty.

The weighted budget theorem turns individual moment budgets into a bound by the power of
their weighted sum. In particular, it introduces no factor counting the number of summands.

## Main results

* `Cslib.vertexNormPow_add_rpow_le`: the rooted triangle inequality.
* `Cslib.vertexNormPow_sum_rpow_le`: the rooted finite-sum inequality.
* `Cslib.vertexNormPow_sum_le_pow_sum`: a finite weighted sum of individual moment budgets.
* `Cslib.rowNormPow_sum_le_pow_sum`: the same bound on joint source/terminal slices.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib

variable {Ω V I : Type*} [Fintype Ω] [Fintype V]
  {p : ℕ} {N u : ℝ} {X : Ω → V → Prop} [∀ σ x, Decidable (X σ x)]

private theorem vertexNormPow_eq_mul_sum (hp : p ≠ 0) (v : Ω → V → ℝ) :
    vertexNormPow p N u X v =
      ((N * u)⁻¹ * (Fintype.card Ω : ℝ)⁻¹) *
        ∑ z : Ω × V, |if X z.1 z.2 then v z.1 z.2 else 0| ^ p := by
  simp only [vertexNormPow, expect_eq_sum_div_card, card_univ, Fintype.sum_prod_type,
    sum_filter, div_eq_mul_inv]
  simp_rw [apply_ite (fun t : ℝ => |t| ^ p), abs_zero, zero_pow hp]
  ring

/-- Minkowski's inequality in the existing normalized vertex norm. The two arrays may use
the same environment and retained source set. -/
theorem vertexNormPow_add_rpow_le (hp : p ≠ 0) (hNu : 0 ≤ N * u)
    (f g : Ω → V → ℝ) :
    vertexNormPow p N u X (fun σ x => f σ x + g σ x) ^ (p⁻¹ : ℝ) ≤
      vertexNormPow p N u X f ^ (p⁻¹ : ℝ) +
        vertexNormPow p N u X g ^ (p⁻¹ : ℝ) := by
  let c : ℝ := (N * u)⁻¹ * (Fintype.card Ω : ℝ)⁻¹
  have hc : 0 ≤ c := mul_nonneg (inv_nonneg.mpr hNu) (by positivity)
  let F : Ω × V → ℝ := fun z => if X z.1 z.2 then f z.1 z.2 else 0
  let G : Ω × V → ℝ := fun z => if X z.1 z.2 then g z.1 z.2 else 0
  have hmask (z : Ω × V) :
      (if X z.1 z.2 then f z.1 z.2 + g z.1 z.2 else 0) = F z + G z := by
    simp only [F, G]
    split_ifs <;> simp
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
  have h := Real.Lp_add_le (univ : Finset (Ω × V)) F G hp'
  simp only [Real.rpow_natCast, one_div] at h
  rw [vertexNormPow_eq_mul_sum hp, vertexNormPow_eq_mul_sum hp,
    vertexNormPow_eq_mul_sum hp]
  simp_rw [hmask]
  change (c * ∑ z, |F z + G z| ^ p) ^ (p⁻¹ : ℝ) ≤
    (c * ∑ z, |F z| ^ p) ^ (p⁻¹ : ℝ) + (c * ∑ z, |G z| ^ p) ^ (p⁻¹ : ℝ)
  rw [Real.mul_rpow hc (by positivity), Real.mul_rpow hc (by positivity),
    Real.mul_rpow hc (by positivity), ← mul_add]
  exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hc _)

/-- Finite Minkowski inequality. No independence among the arrays is required. -/
theorem vertexNormPow_sum_rpow_le (hp : p ≠ 0) (hNu : 0 ≤ N * u)
    (s : Finset I) (f : I → Ω → V → ℝ) :
    vertexNormPow p N u X (fun σ x => ∑ i ∈ s, f i σ x) ^ (p⁻¹ : ℝ) ≤
      ∑ i ∈ s, vertexNormPow p N u X (f i) ^ (p⁻¹ : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vertexNormPow, hp]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (vertexNormPow_add_rpow_le hp hNu (f i) (fun σ x => ∑ j ∈ s, f j σ x)).trans
      (add_le_add le_rfl ih)

/-- A constant scalar factors out of the normalized moment with its absolute `p`-th power. -/
theorem vertexNormPow_const_mul (w : ℝ) (f : Ω → V → ℝ) :
    vertexNormPow p N u X (fun σ x => w * f σ x) = |w| ^ p * vertexNormPow p N u X f := by
  simp only [vertexNormPow, abs_mul, mul_pow, ← mul_sum, ← mul_expect]
  ring

/-- Individual moment budgets control a weighted finite sum by the `p`-th power of the
weighted sum of budgets, without a factor depending on the number of terms. -/
theorem vertexNormPow_sum_le_pow_sum (hp : p ≠ 0) (hNu : 0 ≤ N * u)
    (s : Finset I) (f : I → Ω → V → ℝ) (w ε : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hε : ∀ i ∈ s, 0 ≤ ε i)
    (hf : ∀ i ∈ s, vertexNormPow p N u X (f i) ≤ ε i ^ p) :
    vertexNormPow p N u X (fun σ x => ∑ i ∈ s, w i * f i σ x) ≤
      (∑ i ∈ s, w i * ε i) ^ p := by
  have hroot := vertexNormPow_sum_rpow_le (X := X) (N := N) (u := u)
    hp hNu s (fun i σ x => w i * f i σ x)
  have hterm : ∀ i ∈ s,
      vertexNormPow p N u X (fun σ x => w i * f i σ x) ^ (p⁻¹ : ℝ) ≤ w i * ε i := by
    intro i hi
    rw [vertexNormPow_const_mul, abs_of_nonneg (hw i hi),
      Real.mul_rpow (pow_nonneg (hw i hi) _) (vertexNormPow_nonneg hNu _),
      Real.pow_rpow_inv_natCast (hw i hi) hp]
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    exact (Real.rpow_le_rpow (vertexNormPow_nonneg hNu _) (hf i hi) (by positivity)).trans_eq
      (Real.pow_rpow_inv_natCast (hε i hi) hp)
  have h := pow_le_pow_left₀ (Real.rpow_nonneg (vertexNormPow_nonneg hNu _) _)
    (hroot.trans (sum_le_sum hterm)) p
  rwa [Real.rpow_inv_natCast_pow (vertexNormPow_nonneg hNu _) hp] at h

/-- Rows are vertices indexed by endpoint pairs, with the same joint masks and normalization. -/
theorem rowNormPow_eq_vertexNormPow (f : Ω → V → V → ℝ)
    (Y : Ω → V → Prop) [∀ σ y, Decidable (Y σ y)] :
    rowNormPow p N u X Y f = vertexNormPow p N u
      (fun σ (xy : V × V) => X σ xy.1 ∧ Y σ xy.2)
      (fun σ xy => f σ xy.1 xy.2) := by
  simp only [rowNormPow, vertexNormPow, sum_filter, Fintype.sum_prod_type]
  congr 2
  funext σ
  apply sum_congr rfl
  intro x _
  by_cases hx : X σ x <;> simp [hx]

/-- A constant scale factors out of a row moment on its unchanged joint masks. -/
theorem rowNormPow_const_mul (w : ℝ) (f : Ω → V → V → ℝ)
    (Y : Ω → V → Prop) [∀ σ y, Decidable (Y σ y)] :
    rowNormPow p N u X Y (fun σ x y => w * f σ x y) =
      |w| ^ p * rowNormPow p N u X Y f := by
  rw [rowNormPow_eq_vertexNormPow, vertexNormPow_const_mul, rowNormPow_eq_vertexNormPow]

/-- Finite weighted Minkowski for rows on their original joint source/terminal slice.
No independence or count of bins or prefixes is used. -/
theorem rowNormPow_sum_le_pow_sum (hp : p ≠ 0) (hNu : 0 ≤ N * u)
    (Y : Ω → V → Prop) [∀ σ y, Decidable (Y σ y)]
    (s : Finset I) (f : I → Ω → V → V → ℝ) (w ε : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hε : ∀ i ∈ s, 0 ≤ ε i)
    (hf : ∀ i ∈ s, rowNormPow p N u X Y (f i) ≤ ε i ^ p) :
    rowNormPow p N u X Y (fun σ x y => ∑ i ∈ s, w i * f i σ x y) ≤
      (∑ i ∈ s, w i * ε i) ^ p := by
  simp_rw [rowNormPow_eq_vertexNormPow] at hf ⊢
  exact vertexNormPow_sum_le_pow_sum hp hNu s
    (fun i σ (xy : V × V) => f i σ xy.1 xy.2) w ε hw hε hf

end Cslib
