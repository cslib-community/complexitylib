/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Progress
public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import Cslib.Foundations.Data.BitString
import CslibFrontier.Foundations.Quantum.Measurement.Overlap

/-!
# Weighted quantum adversary method

A weighted adversary scheme (`Cslib.Quantum.WeightScheme`) attaches nonnegative pair weights
`w(x, y)` to a relation `R` of input pairs and nonnegative coordinate weights `u(x, y, i)` and
`v(x, y, i)` satisfying `w(x, y)² ≤ u(x, y, i) · v(x, y, i)` whenever `xᵢ ≠ yᵢ`
[Ambainis2006], Section 3.3, Definitions 1–3; [Zhang2005], Definition 1.

From the endpoint weights `wtFst x = ∑_{(x, y) ∈ R} w(x, y)` and
`wtSnd y = ∑_{(x, y) ∈ R} w(x, y)` and coordinate loads `loadFst x i` and `loadSnd y i`, balancing
`Cslib.Quantum.one_sub_mul_sum_le_of_sq_le` across the two endpoints yields:

* **Weighted adversary bound** [Ambainis2006], Lemma 1: if `loadFst x i ≤ vA · wtFst x` and
  `loadSnd y i ≤ vB · wtSnd y` for all endpoints and coordinates, then
  `(1 - δ) ∑_{(x, y) ∈ R} w(x, y) ≤ 2 T √(vA · vB) ∑_{(x, y) ∈ R} w(x, y)`
  (`Cslib.Quantum.WeightScheme.one_sub_mul_sum_le`).
* **Ratio form** [Zhang2005], Theorem 3 (`Alb₃`): if `0 < ∑_{(x, y) ∈ R} w(x, y)`,
  `mA · loadFst x i ≤ wtFst x`, and `mB · loadSnd y i ≤ wtSnd y`, then
  `(1 - δ) √(mA · mB) ≤ 2 T` (`Cslib.Quantum.WeightScheme.one_sub_mul_sqrt_le_of_load_le`).
* **Subsumption of unweighted bounds** [Zhang2005], Theorem 5 (`Alb₂ ≤ Alb₃`): every unweighted
  counting instance `(R, m, m', L)` embeds via `Cslib.Quantum.WeightScheme.ofUnweighted`.

## Main definitions

* `Cslib.Quantum.WeightScheme`: a weighted adversary scheme on `BitString N`.
* `Cslib.Quantum.WeightScheme.weightSum`, `Cslib.Quantum.WeightScheme.wtFst`,
  `Cslib.Quantum.WeightScheme.wtSnd`: pair-weight sums.
* `Cslib.Quantum.WeightScheme.loadFst`, `Cslib.Quantum.WeightScheme.loadSnd`: coordinate loads.
* `Cslib.Quantum.WeightScheme.ofUnweighted`: weight scheme induced by unweighted counts.

## Main results

* `Cslib.Quantum.WeightScheme.one_sub_mul_sum_le` and
  `Cslib.Quantum.WeightScheme.one_sub_two_mul_sqrt_mul_sum_le`: Ambainis's weighted adversary bound.
* `Cslib.Quantum.WeightScheme.one_sub_mul_sqrt_le_of_load_le` and
  `Cslib.Quantum.WeightScheme.one_sub_two_mul_sqrt_mul_sqrt_le_of_load_le`: Zhang's ratio form.
* `Cslib.Quantum.WeightScheme.ofUnweighted`, `Cslib.Quantum.WeightScheme.ofUnweighted_wtFst`,
  `Cslib.Quantum.WeightScheme.ofUnweighted_wtSnd`,
  `Cslib.Quantum.WeightScheme.ofUnweighted_loadFst_le`,
  `Cslib.Quantum.WeightScheme.ofUnweighted_loadSnd_le`: unweighted-to-weighted embedding
  (`Alb₂ ≤ Alb₃`).

## References

* [A. Ambainis, *Polynomial degree vs. quantum query complexity*][Ambainis2006]
* [S. Zhang, *On the power of Ambainis lower bounds*][Zhang2005]
-/

public section

namespace Cslib.Quantum

open Finset

variable {N : ℕ} {W : Type*} [Fintype W]

/-- A weighted adversary scheme on `N`-bit inputs ([Ambainis2006], Section 3.3, Definition 1;
[Zhang2005], Definition 1): nonnegative pair weights `w` on `R` and coordinate weights `u, v`
satisfying `w(x, y)² ≤ u(x, y, i) · v(x, y, i)` whenever `(x, y) ∈ R` and `xᵢ ≠ yᵢ`. -/
@[ext] structure WeightScheme (N : ℕ) where
  /-- The relation of input pairs. -/
  R : Finset (BitString N × BitString N)
  /-- Nonnegative pair weights on `R`. -/
  w : BitString N × BitString N → ℝ
  /-- First-endpoint coordinate weights. -/
  u : BitString N × BitString N → Fin N → ℝ
  /-- Second-endpoint coordinate weights. -/
  v : BitString N × BitString N → Fin N → ℝ
  /-- Pair weights are nonnegative on `R`. -/
  w_nonneg : ∀ p ∈ R, 0 ≤ w p
  /-- First-endpoint coordinate weights are nonnegative on differing pairs. -/
  u_nonneg : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ u p i
  /-- Second-endpoint coordinate weights are nonnegative on differing pairs. -/
  v_nonneg : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ v p i
  /-- Splitting inequality `w(p)² ≤ u(p, i) · v(p, i)` on differing pairs. -/
  sq_le : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → w p ^ 2 ≤ u p i * v p i

namespace WeightScheme

/-- Total pair weight of a weight scheme. -/
@[expose] def weightSum (S : WeightScheme N) : ℝ := ∑ p ∈ S.R, S.w p

/-- Total weight `wt(x)` of pairs in `R` with first endpoint `x`. -/
@[expose] noncomputable def wtFst (S : WeightScheme N) (x : BitString N) : ℝ :=
  ∑ p ∈ S.R with p.1 = x, S.w p

/-- Total weight `wt(y)` of pairs in `R` with second endpoint `y`. -/
@[expose] noncomputable def wtSnd (S : WeightScheme N) (y : BitString N) : ℝ :=
  ∑ p ∈ S.R with p.2 = y, S.w p

/-- Coordinate load `v(x, i)` of coordinate `i` at first endpoint `x`. -/
@[expose] noncomputable def loadFst (S : WeightScheme N) (x : BitString N) (i : Fin N) : ℝ :=
  ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p.1 = x, S.u p i

/-- Coordinate load `v(y, i)` of coordinate `i` at second endpoint `y`. -/
@[expose] noncomputable def loadSnd (S : WeightScheme N) (y : BitString N) (i : Fin N) : ℝ :=
  ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p.2 = y, S.v p i

theorem weightSum_nonneg (S : WeightScheme N) : 0 ≤ S.weightSum :=
  sum_nonneg S.w_nonneg

theorem wtFst_nonneg (S : WeightScheme N) (x : BitString N) : 0 ≤ S.wtFst x :=
  sum_nonneg fun p hp => S.w_nonneg p (mem_filter.1 hp).1

theorem wtSnd_nonneg (S : WeightScheme N) (y : BitString N) : 0 ≤ S.wtSnd y :=
  sum_nonneg fun p hp => S.w_nonneg p (mem_filter.1 hp).1

theorem loadFst_nonneg (S : WeightScheme N) (x : BitString N) (i : Fin N) : 0 ≤ S.loadFst x i :=
  sum_nonneg fun p hp => S.u_nonneg p (mem_filter.1 hp).1 i (mem_filter.1 hp).2.1

theorem loadSnd_nonneg (S : WeightScheme N) (y : BitString N) (i : Fin N) : 0 ≤ S.loadSnd y i :=
  sum_nonneg fun p hp => S.v_nonneg p (mem_filter.1 hp).1 i (mem_filter.1 hp).2.1

theorem sum_wtFst_eq_weightSum (S : WeightScheme N) :
    ∑ x ∈ S.R.image Prod.fst, S.wtFst x = S.weightSum := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (s := S.R) (g := Prod.fst)
    (t := S.R.image Prod.fst) (f := S.w) (fun _ h => mem_image_of_mem _ h)

theorem sum_wtSnd_eq_weightSum (S : WeightScheme N) :
    ∑ y ∈ S.R.image Prod.snd, S.wtSnd y = S.weightSum := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (s := S.R) (g := Prod.snd)
    (t := S.R.image Prod.snd) (f := S.w) (fun _ h => mem_image_of_mem _ h)

/-- Rescaled progress-measure bound for any positive balancing factor `c > 0`. -/
private theorem one_sub_mul_sum_le_of_pos (S : WeightScheme N)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    {δ : ℝ} (hδ : ∀ p ∈ S.R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ)
    {vA vB : ℝ} (hvA : 0 ≤ vA) (hvB : 0 ≤ vB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, S.loadFst x i ≤ vA * S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, S.loadSnd y i ≤ vB * S.wtSnd y)
    {c : ℝ} (hc : 0 < c) :
    (1 - δ) * S.weightSum ≤ T * (c * vA + vB / c) * S.weightSum := by
  have htel := one_sub_mul_sum_le_of_sq_le U hψ₀ T S.R S.w hδ
    (fun p i => c * S.u p i) (fun p i => S.v p i / c)
    (fun x => c * vA * S.wtFst x) (fun y => (vB / c) * S.wtSnd y)
    S.w_nonneg
    (fun p hp i hi => mul_nonneg hc.le (S.u_nonneg p hp i hi))
    (fun p hp i hi => div_nonneg (S.v_nonneg p hp i hi) hc.le)
    (fun p hp i hi => by
      have hs := S.sq_le p hp i hi
      calc S.w p ^ 2 ≤ S.u p i * S.v p i := hs
        _ = (c * S.u p i) * (S.v p i / c) := by field_simp)
    (fun x _ => mul_nonneg (mul_nonneg hc.le hvA) (S.wtFst_nonneg x))
    (fun y _ => mul_nonneg (div_nonneg hvB hc.le) (S.wtSnd_nonneg y))
    (fun x hx i => by
      rw [← mul_sum]
      calc c * S.loadFst x i ≤ c * (vA * S.wtFst x) :=
            mul_le_mul_of_nonneg_left (hA x hx i) hc.le
        _ = c * vA * S.wtFst x := by ring)
    (fun y hy i => by
      calc ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p.2 = y, S.v p i / c
          = S.loadSnd y i / c := (sum_div _ _ c).symm
        _ ≤ (vB * S.wtSnd y) / c := div_le_div_of_nonneg_right (hB y hy i) hc.le
        _ = (vB / c) * S.wtSnd y := by ring)
  rw [← mul_sum, ← mul_sum, S.sum_wtFst_eq_weightSum, S.sum_wtSnd_eq_weightSum] at htel
  calc (1 - δ) * S.weightSum ≤
        (T : ℝ) * (c * vA * S.weightSum + (vB / c) * S.weightSum) := htel
    _ = T * (c * vA + vB / c) * S.weightSum := by ring

/-- **Weighted quantum adversary bound** ([Ambainis2006], Section 3.3, Lemma 1):
if `T` queries leave every related pair with state overlap at most `δ`, and the coordinate loads
satisfy `loadFst x i ≤ vA · wtFst x` and `loadSnd y i ≤ vB · wtSnd y`, then
`(1 - δ) ∑_{(x, y) ∈ R} w(x, y) ≤ 2 T √(vA · vB) ∑_{(x, y) ∈ R} w(x, y)`. -/
theorem one_sub_mul_sum_le (S : WeightScheme N) (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) {δ : ℝ}
    (hδ : ∀ p ∈ S.R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ)
    {vA vB : ℝ} (hvA : 0 ≤ vA) (hvB : 0 ≤ vB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, S.loadFst x i ≤ vA * S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, S.loadSnd y i ≤ vB * S.wtSnd y) :
    (1 - δ) * S.weightSum ≤ 2 * T * √(vA * vB) * S.weightSum := by
  rcases hvA.eq_or_lt with rfl | hvA_pos
  · simp only [zero_mul, Real.sqrt_zero, mul_zero, zero_mul]
    by_contra hlt
    push Not at hlt
    have hpos : 0 < (1 - δ) * S.weightSum := hlt
    set M := ((T : ℝ) * vB * S.weightSum + 1) / ((1 - δ) * S.weightSum) * 2
    have hM : 0 < M := by
      have := S.weightSum_nonneg
      positivity
    have hbal := S.one_sub_mul_sum_le_of_pos U hψ₀ T hδ le_rfl hvB hA hB hM
    simp only [mul_zero, zero_add] at hbal
    have h1 : (T : ℝ) * (vB / M) * S.weightSum = (T * vB * S.weightSum) / M := by ring
    have h2 : (T : ℝ) * vB * S.weightSum / M < (1 - δ) * S.weightSum := by
      have : (T : ℝ) * vB * S.weightSum / M =
          ((T : ℝ) * vB * S.weightSum / ((T : ℝ) * vB * S.weightSum + 1)) *
            ((1 - δ) * S.weightSum / 2) := by
        dsimp only [M]
        field_simp [hpos.ne']
      have hfrac : (T : ℝ) * vB * S.weightSum / ((T : ℝ) * vB * S.weightSum + 1) < 1 := by
        have := S.weightSum_nonneg
        rw [div_lt_one (by positivity)]
        linarith
      nlinarith
    linarith [h1.symm ▸ hbal]
  rcases hvB.eq_or_lt with rfl | hvB_pos
  · simp only [mul_zero, Real.sqrt_zero, zero_mul]
    by_contra hlt
    push Not at hlt
    have hpos : 0 < (1 - δ) * S.weightSum := hlt
    set M := ((1 - δ) * S.weightSum) / (((T : ℝ) * vA * S.weightSum + 1) * 2)
    have hM : 0 < M := by
      have := S.weightSum_nonneg
      positivity
    have hbal := S.one_sub_mul_sum_le_of_pos U hψ₀ T hδ hvA_pos.le le_rfl hA hB hM
    simp only [zero_div, add_zero] at hbal
    have h1 : (T : ℝ) * (M * vA) * S.weightSum = M * ((T : ℝ) * vA * S.weightSum) := by ring
    have h2 : M * ((T : ℝ) * vA * S.weightSum) < (1 - δ) * S.weightSum := by
      have : M * ((T : ℝ) * vA * S.weightSum) =
          (((T : ℝ) * vA * S.weightSum) / ((T : ℝ) * vA * S.weightSum + 1)) *
            ((1 - δ) * S.weightSum / 2) := by
        dsimp only [M]
        field_simp
      have hfrac : (T : ℝ) * vA * S.weightSum / ((T : ℝ) * vA * S.weightSum + 1) < 1 := by
        have := S.weightSum_nonneg
        rw [div_lt_one (by positivity)]
        linarith
      nlinarith
    linarith [h1.symm ▸ hbal]
  · set c := √vB / √vA
    have hc : 0 < c := div_pos (Real.sqrt_pos.2 hvB_pos) (Real.sqrt_pos.2 hvA_pos)
    have hbal := S.one_sub_mul_sum_le_of_pos U hψ₀ T hδ hvA_pos.le hvB_pos.le hA hB hc
    have hcoeff : c * vA + vB / c = 2 * √(vA * vB) := by
      rw [Real.sqrt_mul hvA_pos.le]
      have hsqA : √vA * √vA = vA := Real.mul_self_sqrt hvA_pos.le
      have hsqB : √vB * √vB = vB := Real.mul_self_sqrt hvB_pos.le
      dsimp only [c]
      rw [div_mul_eq_mul_div, div_div_eq_mul_div]
      calc √vB * vA / √vA + vB * √vA / √vB
          = √vB * (√vA * √vA) / √vA + (√vB * √vB) * √vA / √vB := by rw [hsqA, hsqB]
        _ = 2 * (√vA * √vB) := by
            field_simp [Real.sqrt_ne_zero'.2 hvA_pos, Real.sqrt_ne_zero'.2 hvB_pos]
            ring
    rw [hcoeff] at hbal
    linarith

/-- **Weighted quantum adversary bound for Boolean outputs** ([Ambainis2006], Lemma 1):
if a `T`-query algorithm accepts the first input of every pair in `R` with probability at least
`1 - ε` and the second with probability at most `ε ≤ 1/2`, then
`(1 - 2√(ε(1-ε))) ∑ w ≤ 2 T √(vA · vB) ∑ w`. -/
theorem one_sub_two_mul_sqrt_mul_sum_le (S : WeightScheme N)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_acc : Finset (Fin N × Bool × W)) {ε : ℝ}
    (h₁ : ∀ p ∈ S.R, 1 - ε ≤ measureProb (run U ψ₀ p.1 T) S_acc)
    (h₂ : ∀ p ∈ S.R, measureProb (run U ψ₀ p.2 T) S_acc ≤ ε) (hε : 2 * ε ≤ 1)
    {vA vB : ℝ} (hvA : 0 ≤ vA) (hvB : 0 ≤ vB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, S.loadFst x i ≤ vA * S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, S.loadSnd y i ≤ vB * S.wtSnd y) :
    (1 - 2 * √(ε * (1 - ε))) * S.weightSum ≤ 2 * T * √(vA * vB) * S.weightSum :=
  S.one_sub_mul_sum_le U hψ₀ T
    (fun p hp => norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀])
      (by rw [norm_run, hψ₀]) (h₁ p hp) (h₂ p hp) hε)
    hvA hvB hA hB

/-- **Weighted quantum adversary bound, ratio form** ([Zhang2005], Theorem 3, `Alb₃`):
if `0 < ∑ p ∈ R, w p`, `mA · loadFst x i ≤ wtFst x`, and `mB · loadSnd y i ≤ wtSnd y`, then
`(1 - δ) √(mA · mB) ≤ 2 T`. -/
theorem one_sub_mul_sqrt_le_of_load_le (S : WeightScheme N)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (hW : 0 < S.weightSum) {δ : ℝ}
    (hδ : ∀ p ∈ S.R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ)
    {mA mB : ℝ} (hmA : 0 ≤ mA) (hmB : 0 ≤ mB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, mA * S.loadFst x i ≤ S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, mB * S.loadSnd y i ≤ S.wtSnd y) :
    (1 - δ) * √(mA * mB) ≤ 2 * T := by
  rcases hmA.eq_or_lt with rfl | hmA_pos
  · simp only [zero_mul, Real.sqrt_zero, mul_zero]; positivity
  rcases hmB.eq_or_lt with rfl | hmB_pos
  · simp only [mul_zero, Real.sqrt_zero, mul_zero]; positivity
  have hbal := S.one_sub_mul_sum_le U hψ₀ T hδ (vA := mA⁻¹) (vB := mB⁻¹)
    (inv_nonneg.2 hmA_pos.le) (inv_nonneg.2 hmB_pos.le)
    (fun x hx i => by
      rw [inv_mul_eq_div, le_div_iff₀' hmA_pos]
      exact hA x hx i)
    (fun y hy i => by
      rw [inv_mul_eq_div, le_div_iff₀' hmB_pos]
      exact hB y hy i)
  have hcancel : 1 - δ ≤ 2 * (T : ℝ) * √(mA⁻¹ * mB⁻¹) := by
    have := mul_le_mul_of_nonneg_right hbal (inv_nonneg.2 hW.le)
    simpa [mul_assoc, hW.ne'] using this
  have hpos : 0 < √(mA * mB) := Real.sqrt_pos.2 (mul_pos hmA_pos hmB_pos)
  calc (1 - δ) * √(mA * mB)
      ≤ 2 * (T : ℝ) * √(mA⁻¹ * mB⁻¹) * √(mA * mB) :=
        mul_le_mul_of_nonneg_right hcancel hpos.le
    _ = 2 * (T : ℝ) * (√(mA⁻¹ * mB⁻¹) * √(mA * mB)) := by ring
    _ = 2 * (T : ℝ) := by
        rw [← Real.sqrt_mul (by positivity)]
        have hid : (mA⁻¹ * mB⁻¹) * (mA * mB) = 1 := by
          field_simp [hmA_pos.ne', hmB_pos.ne']
        rw [hid, Real.sqrt_one, mul_one]

/-- **Weighted quantum adversary bound for Boolean outputs, ratio form** ([Zhang2005],
Theorem 3): `(1 - 2√(ε(1-ε))) √(mA · mB) ≤ 2 T`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_le_of_load_le (S : WeightScheme N)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (hW : 0 < S.weightSum) (S_acc : Finset (Fin N × Bool × W)) {ε : ℝ}
    (h₁ : ∀ p ∈ S.R, 1 - ε ≤ measureProb (run U ψ₀ p.1 T) S_acc)
    (h₂ : ∀ p ∈ S.R, measureProb (run U ψ₀ p.2 T) S_acc ≤ ε) (hε : 2 * ε ≤ 1)
    {mA mB : ℝ} (hmA : 0 ≤ mA) (hmB : 0 ≤ mB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, mA * S.loadFst x i ≤ S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, mB * S.loadSnd y i ≤ S.wtSnd y) :
    (1 - 2 * √(ε * (1 - ε))) * √(mA * mB) ≤ 2 * T :=
  S.one_sub_mul_sqrt_le_of_load_le U hψ₀ T hW
    (fun p hp => norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀])
      (by rw [norm_run, hψ₀]) (h₁ p hp) (h₂ p hp) hε)
    hmA hmB hA hB

/-- Weight scheme induced by an unweighted adversary relation `(R, L)` with
`l_{x,i} · l_{y,i} ≤ L` ([Zhang2005], Theorem 5): `w(p) = 1`, `u(p, i) = √L / l_{x,i}`, and
`v(p, i) = √L / l_{y,i}`. -/
@[expose] noncomputable def ofUnweighted (R : Finset (BitString N × BitString N)) (L : ℕ)
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L) :
    WeightScheme N where
  R := R
  w := fun _ => 1
  u := fun p i => √L / #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1}
  v := fun p i => √L / #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2}
  w_nonneg := fun _ _ => zero_le_one
  u_nonneg := fun _ _ _ _ => by positivity
  v_nonneg := fun _ _ _ _ => by positivity
  sq_le := fun p hp i hi => by
    classical
    have hl₁ : (0 : ℝ) < #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} :=
      Nat.cast_pos.2 (card_pos.2 ⟨p, mem_filter.2 ⟨hp, hi, rfl⟩⟩)
    have hl₂ : (0 : ℝ) < #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} :=
      Nat.cast_pos.2 (card_pos.2 ⟨p, mem_filter.2 ⟨hp, hi, rfl⟩⟩)
    have hprod : (#{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} : ℝ) *
        #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ √L * √L := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg L)]
      exact_mod_cast hL p hp i hi
    rw [one_pow, div_mul_div_comm, le_div_iff₀ (mul_pos hl₁ hl₂)]
    simpa [one_mul] using hprod

theorem ofUnweighted_wtFst {R : Finset (BitString N × BitString N)} {L : ℕ}
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L)
    (x : BitString N) :
    (ofUnweighted R L hL).wtFst x = (#{q ∈ R | q.1 = x} : ℝ) := by
  simp [wtFst, ofUnweighted]

theorem ofUnweighted_wtSnd {R : Finset (BitString N × BitString N)} {L : ℕ}
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L)
    (y : BitString N) :
    (ofUnweighted R L hL).wtSnd y = (#{q ∈ R | q.2 = y} : ℝ) := by
  simp [wtSnd, ofUnweighted]

/-- A sum over `S` of terms each equal to `√L / #S` is at most `√L`. -/
private theorem sum_le_sqrt_of_eq_div_card {α : Type*} {S : Finset α} {L : ℕ} {f : α → ℝ}
    (hf : ∀ p ∈ S, f p = √L / (#S : ℝ)) : ∑ p ∈ S, f p ≤ √L := by
  rw [sum_congr rfl hf, sum_const, nsmul_eq_mul, ← mul_div_assoc]
  simpa only [div_one, mul_one] using mul_div_mul_left_le (c := (#S : ℝ)) (a := √L) (b := 1)
    (div_nonneg (Real.sqrt_nonneg L) zero_le_one)

theorem ofUnweighted_loadFst_le {R : Finset (BitString N × BitString N)} {L : ℕ}
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L)
    (x : BitString N) (i : Fin N) :
    (ofUnweighted R L hL).loadFst x i ≤ √L := by
  classical
  exact sum_le_sqrt_of_eq_div_card fun p hp => by simp only [ofUnweighted, (mem_filter.1 hp).2.2]

theorem ofUnweighted_loadSnd_le {R : Finset (BitString N × BitString N)} {L : ℕ}
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L)
    (y : BitString N) (i : Fin N) :
    (ofUnweighted R L hL).loadSnd y i ≤ √L := by
  classical
  exact sum_le_sqrt_of_eq_div_card fun p hp => by simp only [ofUnweighted, (mem_filter.1 hp).2.2]

end WeightScheme

end Cslib.Quantum
