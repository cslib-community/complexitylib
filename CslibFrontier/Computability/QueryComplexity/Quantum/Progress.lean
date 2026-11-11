/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import Cslib.Foundations.Data.BitString

/-!
# Weighted progress measures for quantum query adversary arguments

A `T`-query quantum algorithm (`Cslib.Quantum.run`) running from a unit initial state `ψ₀` preserves
inner products up to the positions where two inputs `x` and `y` differ:
one controlled phase-oracle step changes `⟨ψ, φ⟩` by `2 ∑_{i : xᵢ ≠ yᵢ} ⟨Π_i ψ, Π_i φ⟩`
(`Cslib.Quantum.inner_phaseOracle_phaseOracle`), where `Π_i` is `Cslib.Quantum.ctrlProj`.

For any finite set `R` of input pairs and nonnegative pair weights
`γ : BitString N × BitString N → ℝ`, the **weighted progress measure** after `t` queries is
`∑_{(x, y) ∈ R} γ(x, y) |⟨ψₓᵗ, ψ_yᵗ⟩|` (`Cslib.Quantum.weightedProgress`). Before any query all
states agree (`weightedProgress_zero`). Choosing nonnegative step weights `a, b` on `(p, i)` with
`γ(p)² ≤ a(p, i) b(p, i)` whenever `p.1 i ≠ p.2 i` splits each overlap loss across the two
endpoints using `∑_i ‖Π_i ψ‖² ≤ 1` (`Cslib.Quantum.sum_sq_norm_ctrlProj_le`), giving the generic
adversary inequality `Cslib.Quantum.one_sub_mul_sum_le_of_sq_le` used by both the spectral
sensitivity bound (`CslibFrontier.Computability.QueryComplexity.Quantum.Adversary`) and
Ambainis's relational adversary bound
(`CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary`).

## Main definitions

* `Cslib.Quantum.weightedProgress`: weighted sum of state overlaps over a pair set after
  `t` queries.

## Main results

* `Cslib.Quantum.inner_phaseOracle_phaseOracle`: one query changes the overlap of two states by
  `2 ∑_{i : xᵢ ≠ yᵢ} ⟨Π_i ψ, Π_i φ⟩`.
* `Cslib.Quantum.norm_inner_phaseOracle_phaseOracle_ge`: per-step overlap loss bound.
* `Cslib.Quantum.sum_sq_norm_ctrlProj_le`: the query magnitudes of a unit state sum to at most `1`.
* `Cslib.Quantum.weightedProgress_zero`: at time `0`, `weightedProgress` equals `∑ p ∈ R, γ p`.
* `Cslib.Quantum.weightedProgress_zero_sub_le`: `T` queries lower `weightedProgress` by at most
  `T * (∑ x ∈ R.image Prod.fst, α x + ∑ y ∈ R.image Prod.snd, β y)`.
* `Cslib.Quantum.one_sub_mul_sum_le_of_sq_le`: generic weighted adversary inequality.
-/

public section

namespace Cslib.Quantum

open Finset Function

variable {N : ℕ} {W : Type*} [Fintype W]

/-- **One query on two inputs**: the oracles of `x` and `y` differ only on the query indices `i`
with `xᵢ ≠ yᵢ` and control bit `1`, so applying them changes the overlap of two states by
`2 ∑_{i : xᵢ ≠ yᵢ} ⟨Π_i ψ, Π_i φ⟩`. -/
theorem inner_phaseOracle_phaseOracle (x y : Fin N → Bool) (ψ φ : State N W) :
    inner ℂ (phaseOracle x ψ) (phaseOracle y φ) =
      inner ℂ ψ φ - 2 * ∑ i with x i ≠ y i, inner ℂ (ctrlProj i ψ) (ctrlProj i φ) := by
  classical
  simp only [PiLp.inner_apply, RCLike.inner_apply', mul_sum]
  rw [sum_comm, ← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  obtain ⟨j, b, w⟩ := p
  simp only [phaseOracle_apply, ctrlProj, PiLp.toLp_apply]
  cases b
  · simp
  · by_cases hj : x j = y j
    · have : ∀ i ∈ univ.filter (fun i => x i ≠ y i), (2 : ℂ) *
          ((starRingEnd ℂ) (if j = i ∧ true = true then ψ.ofLp (j, true, w) else 0) *
            (if j = i ∧ true = true then φ.ofLp (j, true, w) else 0)) = 0 := by
        intro i hi
        have hji : j ≠ i := by grind
        simp [hji]
      rw [sum_eq_zero this, hj]
      cases y j <;> simp
    · rw [sum_eq_single j]
      · cases hx : x j <;> cases hy : y j <;> simp_all <;> ring
      · intro i _ hij
        simp [Ne.symm hij]
      · intro h
        simp [hj] at h

/-- One query lowers the overlap of the states on two inputs by at most
`2 ∑_{i : xᵢ ≠ yᵢ} ‖Π_i ψ‖ ‖Π_i φ‖`. -/
theorem norm_inner_phaseOracle_phaseOracle_ge (x y : Fin N → Bool) (ψ φ : State N W) :
    ‖inner ℂ ψ φ‖ - 2 * ∑ i with x i ≠ y i, ‖ctrlProj i ψ‖ * ‖ctrlProj i φ‖ ≤
      ‖inner ℂ (phaseOracle x ψ) (phaseOracle y φ)‖ := by
  rw [inner_phaseOracle_phaseOracle]
  have h₁ : ‖∑ i with x i ≠ y i, inner ℂ (ctrlProj i ψ) (ctrlProj i φ)‖ ≤
      ∑ i with x i ≠ y i, ‖ctrlProj i ψ‖ * ‖ctrlProj i φ‖ :=
    (norm_sum_le _ _).trans (sum_le_sum fun i _ => norm_inner_le_norm _ _)
  have h₂ := norm_sub_norm_le (inner ℂ ψ φ)
    (2 * ∑ i with x i ≠ y i, inner ℂ (ctrlProj i ψ) (ctrlProj i φ))
  rw [norm_mul, RCLike.norm_ofNat] at h₂
  linarith

/-- The query magnitudes of a unit state sum to at most `1`. -/
theorem sum_sq_norm_ctrlProj_le (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (x : BitString N) (t : ℕ) :
    ∑ i, ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 ≤ 1 :=
  calc
    ∑ i, ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 ≤ ∑ i, regProb (run U ψ₀ x t) i :=
      sum_le_sum fun i _ => norm_sq_ctrlProj_le i _
    _ = 1 := by rw [sum_regProb, norm_run, hψ₀, one_pow]

/-- The weighted progress measure of a quantum query adversary argument: the weighted sum of state
overlaps on `R` after `t` queries. -/
noncomputable def weightedProgress (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W)
    (R : Finset (BitString N × BitString N)) (γ : BitString N × BitString N → ℝ) (t : ℕ) : ℝ :=
  ∑ p ∈ R, γ p * ‖inner ℂ (run U ψ₀ p.1 t) (run U ψ₀ p.2 t)‖

/-- Before any query the states agree, so the weighted progress measure is `∑ p ∈ R, γ p`. -/
theorem weightedProgress_zero (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (R : Finset (BitString N × BitString N))
    (γ : BitString N × BitString N → ℝ) :
    weightedProgress U ψ₀ R γ 0 = ∑ p ∈ R, γ p := by
  have h : ‖inner ℂ (U 0 ψ₀) (U 0 ψ₀)‖ = 1 := by
    rw [LinearIsometry.inner_map_map, inner_self_eq_norm_sq_to_K, hψ₀]
    simp
  simp only [weightedProgress, run, h, mul_one]

/-- Weighted AM–GM: for `w² ≤ a b` with `a, b, x, y ≥ 0`, `2 w (x y) ≤ a x² + b y²`. -/
private theorem two_mul_mul_le_of_sq_le_mul {w x y a b : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : w ^ 2 ≤ a * b) :
    2 * w * (x * y) ≤ a * x ^ 2 + b * y ^ 2 := by
  have hw : w ≤ √a * √b := (Real.le_sqrt_of_sq_le h).trans_eq (Real.sqrt_mul ha b)
  calc
    2 * w * (x * y) ≤ 2 * (√a * x) * (√b * y) := by nlinarith [mul_nonneg hx hy]
    _ ≤ (√a * x) ^ 2 + (√b * y) ^ 2 := two_mul_le_add_sq _ _
    _ = a * x ^ 2 + b * y ^ 2 := by simp [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- Summing coordinatewise query-magnitude losses across one endpoint projection `k`. -/
private theorem sum_weighted_norm_sq_ctrlProj_le
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1)
    (R : Finset (BitString N × BitString N)) (k : BitString N × BitString N → BitString N)
    (w : BitString N × BitString N → Fin N → ℝ) (α : BitString N → ℝ)
    (hα₀ : ∀ x ∈ R.image k, 0 ≤ α x)
    (hα : ∀ x ∈ R.image k, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ k p = x, w p i ≤ α x)
    (t : ℕ) :
    ∑ p ∈ R, ∑ i with p.1 i ≠ p.2 i, w p i * ‖ctrlProj i (run U ψ₀ (k p) t)‖ ^ 2 ≤
      ∑ x ∈ R.image k, α x := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := R) (g := k) (t := R.image k)
    fun _ h => mem_image_of_mem k h]
  refine sum_le_sum fun x hx => ?_
  calc
    ∑ p ∈ R with k p = x, ∑ i with p.1 i ≠ p.2 i, w p i * ‖ctrlProj i (run U ψ₀ (k p) t)‖ ^ 2
        = ∑ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ k p = x,
            w p i * ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 := by
          trans ∑ p ∈ R, ∑ i,
            if p.1 i ≠ p.2 i ∧ k p = x then w p i * ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 else 0
          · simp only [sum_filter]
            refine sum_congr rfl fun p _ => ?_
            by_cases hkx : k p = x <;> simp [hkx]
          · simp only [sum_filter]
            exact sum_comm
    _ = ∑ i, (∑ p ∈ R with p.1 i ≠ p.2 i ∧ k p = x, w p i) *
          ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 := by simp only [sum_mul]
    _ ≤ ∑ i, α x * ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hα x hx i) (sq_nonneg _)
    _ = α x * ∑ i, ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 := (mul_sum ..).symm
    _ ≤ α x := (mul_le_mul_of_nonneg_left (sum_sq_norm_ctrlProj_le U hψ₀ x t)
          (hα₀ x hx)).trans_eq (mul_one _)

/-- **One query lowers `weightedProgress`** by at most the endpoint weight budgets. -/
private theorem weightedProgress_sub_succ_le
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1)
    (R : Finset (BitString N × BitString N)) (γ : BitString N × BitString N → ℝ)
    (a b : BitString N × BitString N → Fin N → ℝ) (α β : BitString N → ℝ)
    (hγ : ∀ p ∈ R, 0 ≤ γ p)
    (ha : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ a p i)
    (hb : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ b p i)
    (hγsq : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → γ p ^ 2 ≤ a p i * b p i)
    (hα₀ : ∀ x ∈ R.image Prod.fst, 0 ≤ α x)
    (hβ₀ : ∀ y ∈ R.image Prod.snd, 0 ≤ β y)
    (hα : ∀ x ∈ R.image Prod.fst, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.1 = x, a p i ≤ α x)
    (hβ : ∀ y ∈ R.image Prod.snd, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.2 = y, b p i ≤ β y)
    (t : ℕ) :
    weightedProgress U ψ₀ R γ t - weightedProgress U ψ₀ R γ (t + 1) ≤
      ∑ x ∈ R.image Prod.fst, α x + ∑ y ∈ R.image Prod.snd, β y := by
  classical
  have hstep : weightedProgress U ψ₀ R γ t - weightedProgress U ψ₀ R γ (t + 1) ≤
      (∑ p ∈ R, ∑ i with p.1 i ≠ p.2 i, a p i * ‖ctrlProj i (run U ψ₀ p.1 t)‖ ^ 2) +
        ∑ p ∈ R, ∑ i with p.1 i ≠ p.2 i, b p i * ‖ctrlProj i (run U ψ₀ p.2 t)‖ ^ 2 := by
    simp only [weightedProgress, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    have h := norm_inner_phaseOracle_phaseOracle_ge p.1 p.2 (run U ψ₀ p.1 t) (run U ψ₀ p.2 t)
    change γ p * ‖inner ℂ (run U ψ₀ p.1 t) (run U ψ₀ p.2 t)‖ -
        γ p * ‖inner ℂ (U (t + 1) (phaseOracle p.1 (run U ψ₀ p.1 t)))
          (U (t + 1) (phaseOracle p.2 (run U ψ₀ p.2 t)))‖ ≤ _
    rw [LinearIsometry.inner_map_map]
    have h1 : γ p * ‖inner ℂ (run U ψ₀ p.1 t) (run U ψ₀ p.2 t)‖ -
          γ p * ‖inner ℂ (phaseOracle p.1 (run U ψ₀ p.1 t))
            (phaseOracle p.2 (run U ψ₀ p.2 t))‖ ≤
        ∑ i with p.1 i ≠ p.2 i,
          2 * γ p * (‖ctrlProj i (run U ψ₀ p.1 t)‖ * ‖ctrlProj i (run U ψ₀ p.2 t)‖) := by
      have hm := mul_le_mul_of_nonneg_left h (hγ p hp)
      rw [mul_sub, ← mul_assoc, mul_comm (γ p) 2, mul_sum] at hm
      linarith
    refine h1.trans (sum_le_sum fun i hi => ?_)
    have hi' := (mem_filter.1 hi).2
    exact two_mul_mul_le_of_sq_le_mul (norm_nonneg _) (norm_nonneg _)
      (ha p hp i hi') (hb p hp i hi') (hγsq p hp i hi')
  have hX := sum_weighted_norm_sq_ctrlProj_le U hψ₀ R Prod.fst a α hα₀ hα t
  have hY := sum_weighted_norm_sq_ctrlProj_le U hψ₀ R Prod.snd b β hβ₀ hβ t
  linarith

/-- **Telescoping**: `T` queries lower `weightedProgress` by at most `T` times the endpoint
weight budgets. -/
theorem weightedProgress_zero_sub_le
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1)
    (R : Finset (BitString N × BitString N)) (γ : BitString N × BitString N → ℝ)
    (a b : BitString N × BitString N → Fin N → ℝ) (α β : BitString N → ℝ)
    (hγ : ∀ p ∈ R, 0 ≤ γ p)
    (ha : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ a p i)
    (hb : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ b p i)
    (hγsq : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → γ p ^ 2 ≤ a p i * b p i)
    (hα₀ : ∀ x ∈ R.image Prod.fst, 0 ≤ α x)
    (hβ₀ : ∀ y ∈ R.image Prod.snd, 0 ≤ β y)
    (hα : ∀ x ∈ R.image Prod.fst, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.1 = x, a p i ≤ α x)
    (hβ : ∀ y ∈ R.image Prod.snd, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.2 = y, b p i ≤ β y)
    (T : ℕ) :
    weightedProgress U ψ₀ R γ 0 - weightedProgress U ψ₀ R γ T ≤
      T * (∑ x ∈ R.image Prod.fst, α x + ∑ y ∈ R.image Prod.snd, β y) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hstep := weightedProgress_sub_succ_le U hψ₀ R γ a b α β hγ ha hb hγsq hα₀ hβ₀ hα hβ T
    push_cast
    linarith

/-- **Weighted quantum adversary inequality**: if after `T` queries the states on every pair in
`R` have overlap at most `δ`, and weights `a, b` satisfy `γ(p)² ≤ a(p, i) b(p, i)` whenever
`p.1 i ≠ p.2 i` with coordinatewise fiber budgets `α` and `β`, then
`(1 - δ) ∑_{p ∈ R} γ p ≤ T (∑_{x ∈ fst(R)} α x + ∑_{y ∈ snd(R)} β y)`. -/
theorem one_sub_mul_sum_le_of_sq_le
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (R : Finset (BitString N × BitString N)) (γ : BitString N × BitString N → ℝ)
    {δ : ℝ} (hδ : ∀ p ∈ R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ)
    (a b : BitString N × BitString N → Fin N → ℝ) (α β : BitString N → ℝ)
    (hγ : ∀ p ∈ R, 0 ≤ γ p)
    (ha : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ a p i)
    (hb : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ b p i)
    (hγsq : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → γ p ^ 2 ≤ a p i * b p i)
    (hα₀ : ∀ x ∈ R.image Prod.fst, 0 ≤ α x)
    (hβ₀ : ∀ y ∈ R.image Prod.snd, 0 ≤ β y)
    (hα : ∀ x ∈ R.image Prod.fst, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.1 = x, a p i ≤ α x)
    (hβ : ∀ y ∈ R.image Prod.snd, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.2 = y, b p i ≤ β y) :
    (1 - δ) * ∑ p ∈ R, γ p ≤
      T * (∑ x ∈ R.image Prod.fst, α x + ∑ y ∈ R.image Prod.snd, β y) := by
  have htel := weightedProgress_zero_sub_le U hψ₀ R γ a b α β hγ ha hb hγsq hα₀ hβ₀ hα hβ T
  rw [weightedProgress_zero U hψ₀] at htel
  have hend : weightedProgress U ψ₀ R γ T ≤ δ * ∑ p ∈ R, γ p := by
    calc
      weightedProgress U ψ₀ R γ T ≤ ∑ p ∈ R, γ p * δ :=
        sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hδ p hp) (hγ p hp)
      _ = δ * ∑ p ∈ R, γ p := by rw [← sum_mul, mul_comm]
  linarith

end Cslib.Quantum
