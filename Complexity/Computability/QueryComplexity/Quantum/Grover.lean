/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.Search
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Grover's algorithm

Grover's algorithm finds the marked item among `N ≥ 2` with `O(√N)` queries, matching the BBBV
lower bound (`Cslib.Quantum.card_sub_two_le`) up to a constant [Grover][Grover1996]. In the query
model of `Cslib.Quantum.run`, with a trivial workspace, it starts in the uniform superposition
`|s⟩` of the query indices with control bit `1` (`Cslib.Quantum.uniform`) and alternates the
controlled phase oracle with the *diffusion* `D = 2|s⟩⟨s| - I`, the reflection about `|s⟩`
(`Cslib.Quantum.diffusion`, `Cslib.Quantum.grover`). The state never leaves the control-`1`
subspace, where the oracle acts as the phase oracle `(-1)^{x_i}`.

Let `θ = arcsin(1 / √N)`. After `k` queries on the input marking `z`, the amplitude of `z` is
`sin((2k + 1) θ)` and every other amplitude with control bit `1` is `cos((2k + 1) θ) / √(N - 1)`
(`Cslib.Quantum.run_grover`): each round rotates the state by `2θ` in the plane spanned by `|z⟩`
and the uniform superposition of the other items. So `z` is measured with probability
`sin²((2k + 1) θ)` (`Cslib.Quantum.regProb_run_grover`). With `k = ⌊π / (4θ)⌋ ≤ π√N / 4` queries,
`(2k + 1) θ` lies within `θ` of `π / 2`, and the success probability is at least `1 - 1 / N`
(`Cslib.Quantum.grover_success`).

**Source mapping.** The algorithm is Grover's (§3 of arXiv:quant-ph/9605043v3): it alternates the
inversion of the phase of the marked item with the diffusion transform `D_ij = 2/N` for `i ≠ j`,
`D_ii = -1 + 2/N` (equation (4.0)), the inversion about the average (§4). Grover takes `N = 2^n`
and implements `D = WRW` with Walsh–Hadamard transforms (Theorem 1 in §5); here `D` is the
reflection about `|s⟩` for every `N ≥ 2`, and only queries are counted. Grover shows a success
probability of at least `1/2` after `O(√N)` iterations. The closed form `sin((2k + 1) θ)` and the
choice `⌊π / (4θ)⌋`, with failure probability at most `1/N` and at most `π√N / 4` iterations, are
from [Boyer, Brassard, Høyer, Tapp][BoyerBrassardHoyerTapp1998] (numbering of
arXiv:quant-ph/9605034v1): §2, equation (2), and §3 with one solution. For `N = 4` the angle is
`π / 6` and one query succeeds with certainty, their §3.1.

## Main definitions

* `Cslib.Quantum.uniform`: the uniform superposition.
* `Cslib.Quantum.diffusion`: the reflection about the uniform superposition.
* `Cslib.Quantum.grover`: the isometries of Grover's algorithm.

## Main results

* `Cslib.Quantum.run_grover`: the state of Grover's algorithm after `k` queries.
* `Cslib.Quantum.regProb_run_grover`: its success probability `sin²((2k + 1) θ)`.
* `Cslib.Quantum.grover_success`: `⌊π / (4θ)⌋ ≤ π√N / 4` queries find the marked item with
  probability at least `1 - 1 / N`.

## References

* [L. K. Grover, *A Fast Quantum Mechanical Algorithm for Database Search*][Grover1996]
* [M. Boyer, G. Brassard, P. Høyer, A. Tapp, *Tight Bounds on Quantum
  Searching*][BoyerBrassardHoyerTapp1998]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset Real

variable {N : ℕ}

/-- The uniform superposition `|s⟩ = N^{-1/2} ∑_i |i, 1⟩` with control bit `1`. -/
noncomputable def uniform (N : ℕ) : State N Unit :=
  WithLp.toLp 2 fun p => if p.2.1 then ((Real.sqrt N)⁻¹ : ℝ) else 0

theorem norm_uniform (hN : 0 < N) : ‖uniform N‖ = 1 := by
  have h : ‖uniform N‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.univ_unit, sum_singleton, uniform,
      PiLp.toLp_apply, ite_true, Bool.false_eq_true, ite_false, norm_zero, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp
    ring
  nlinarith [norm_nonneg (uniform N)]

/-- The **diffusion** `D = 2|s⟩⟨s| - I`: the reflection about the uniform superposition. -/
noncomputable def diffusion (N : ℕ) : State N Unit ≃ₗᵢ[ℂ] State N Unit :=
  (ℂ ∙ uniform N).reflection

/-- The diffusion inverts every control-`1` amplitude about their mean:
`(Dψ)(i, b) = 2 b · mean_j ψ(j, 1) - ψ(i, b)`. -/
theorem diffusion_apply (hN : 0 < N) (ψ : State N Unit) (p : Fin N × Bool × Unit) :
    (diffusion N ψ).ofLp p =
      2 * (if p.2.1 then (N : ℂ)⁻¹ * ∑ q, (if q.2.1 then ψ.ofLp q else 0) else 0) - ψ.ofLp p := by
  rw [diffusion, Submodule.reflection_apply, Submodule.starProjection_singleton,
    norm_uniform hN]
  simp only [one_pow, PiLp.sub_apply, PiLp.smul_apply,
    EuclideanSpace.inner_eq_star_dotProduct, uniform, smul_eq_mul, nsmul_eq_mul]
  have hsq : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = (N : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    push_cast
    ring
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, apply_ite, Complex.conj_ofReal, map_zero]
  push_cast
  rw [div_one]
  have hdot : (∑ q : Fin N × Bool × Unit,
      if q.2.1 then ψ.ofLp q * ((Real.sqrt N : ℂ))⁻¹ else ψ.ofLp q * 0) =
      ((Real.sqrt N : ℂ))⁻¹ * ∑ q, (if q.2.1 then ψ.ofLp q else 0) := by
    rw [mul_sum]
    refine sum_congr rfl fun q _ => ?_
    split_ifs <;> ring
  rw [hdot]
  split_ifs
  · linear_combination (2 * ∑ q : Fin N × Bool × Unit, (if q.2.1 then ψ.ofLp q else 0)) * hsq
  · ring

/-- The isometries of **Grover's algorithm**: the identity, then the diffusion after every
query. Its initial state is `uniform N`. -/
noncomputable def grover (N : ℕ) : ℕ → State N Unit →ₗᵢ[ℂ] State N Unit
  | 0 => LinearIsometry.id
  | _ + 1 => (diffusion N).toLinearIsometry

/-- The Grover angle `θ = arcsin(1 / √N)`. -/
noncomputable def groverAngle (N : ℕ) : ℝ := Real.arcsin (Real.sqrt N)⁻¹

/-- The sine and cosine of the Grover angle: `sin θ = 1 / √N` and `cos θ / √(N - 1) = 1 / √N`. -/
private theorem sin_groverAngle (hN : 2 ≤ N) : Real.sin (groverAngle N) = (Real.sqrt N)⁻¹ := by
  have hpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by positivity)
  have hle : (Real.sqrt N)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hpos, Real.one_le_sqrt]
    exact_mod_cast (by omega : 1 ≤ N)
  exact Real.sin_arcsin (by linarith [inv_nonneg.mpr hpos.le]) hle

private theorem cos_groverAngle (hN : 2 ≤ N) :
    Real.cos (groverAngle N) = Real.sqrt (N - 1) * (Real.sqrt N)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (0 : ℝ) ≤ N - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [groverAngle, Real.cos_arcsin, inv_pow, Real.sq_sqrt hN0.le, ← Real.sqrt_inv,
    ← Real.sqrt_mul hN1]
  congr 1
  field_simp

variable [DecidableEq (Fin N)]

/-- **The state of Grover's algorithm after `k` queries** on the input marking `z`: with control
bit `1`, amplitude `sin((2k + 1) θ)` on `z` and `cos((2k + 1) θ) / √(N - 1)` elsewhere; with
control bit `0`, amplitude `0`. -/
theorem run_grover (hN : 2 ≤ N) (z : Fin N) (k : ℕ) (p : Fin N × Bool × Unit) :
    (run (grover N) (uniform N) (marked z) k).ofLp p =
      if p.2.1 then ((if p.1 = z then Real.sin ((2 * k + 1) * groverAngle N)
        else Real.cos ((2 * k + 1) * groverAngle N) / Real.sqrt (N - 1) : ℝ) : ℂ) else 0 := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (0 : ℝ) < N - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hsN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsN1 : (0 : ℝ) < Real.sqrt (N - 1) := Real.sqrt_pos.mpr hN1
  set θ := groverAngle N
  have hs := sin_groverAngle hN
  have hc := cos_groverAngle hN
  induction k generalizing p with
  | zero =>
    simp only [run, grover, LinearIsometry.id_apply, uniform, PiLp.toLp_apply, Nat.cast_zero,
      mul_zero, zero_add, one_mul]
    split_ifs
    · rw [hs]
    · rw [hc]
      congr 1
      field_simp
    · rfl
  | succ k ih =>
    set a := Real.sin ((2 * k + 1) * θ)
    set b := Real.cos ((2 * k + 1) * θ) / Real.sqrt (N - 1)
    have hsum : ∑ q : Fin N × Bool × Unit, (if q.2.1 then (phaseOracle (marked z)
        (run (grover N) (uniform N) (marked z) k)).ofLp q else 0) =
          ((-a + (N - 1) * b : ℝ) : ℂ) := by
      simp only [phaseOracle_apply, ih, marked, decide_eq_true_eq, Fintype.sum_prod_type,
        Fintype.univ_unit, sum_singleton, Fintype.sum_bool, ite_true, Bool.true_and,
        Bool.false_eq_true, ite_false, add_zero]
      have hterm : ∀ x : Fin N, (if x = z then (-1 : ℂ) else 1) *
          ((if x = z then a else b : ℝ) : ℂ) =
            (b : ℂ) + (if x = z then ((-a - b : ℝ) : ℂ) else 0) := by
        intro x
        by_cases h : x = z <;> simp [h]
      rw [sum_congr rfl fun x _ => hterm x, sum_add_distrib, sum_ite_eq', ite_eq_left (mem_univ z),
        sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    have hX : (Real.sqrt (N - 1) * (Real.sqrt N)⁻¹) ^ 2 = (N - 1) * (N : ℝ)⁻¹ := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hN1.le, Real.sq_sqrt hN0.le]
    have hS2 : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hN0.le]
    have hNinv : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN0.ne'
    have hcosx : Real.cos ((2 * k + 1) * θ) = b * Real.sqrt (N - 1) := by
      simp only [b]
      field_simp
    have harg : (2 * ((k + 1 : ℕ) : ℝ) + 1) * θ = (2 * k + 1) * θ + 2 * θ := by
      push_cast
      ring
    simp only [run, grover, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [diffusion_apply (by omega), hsum, phaseOracle_apply, ih]
    obtain ⟨i, c, u⟩ := p
    cases c
    · simp
    simp only [marked, decide_eq_true_eq, Bool.true_and, ite_true]
    by_cases h : i = z
    · have hreal : 2 * ((N : ℝ)⁻¹ * (-a + (N - 1) * b)) + a =
          Real.sin ((2 * ((k + 1 : ℕ) : ℝ) + 1) * θ) := by
        rw [harg, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc, hcosx]
        linear_combination (-(2 * a + 2 * b)) * hX + (-2 * a) * hNinv
      simp only [h, ite_true]
      rw [← hreal]
      push_cast
      ring
    · have hreal : 2 * ((N : ℝ)⁻¹ * (-a + (N - 1) * b)) - b =
          Real.cos ((2 * ((k + 1 : ℕ) : ℝ) + 1) * θ) / Real.sqrt (N - 1) := by
        rw [harg, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc, hcosx,
          eq_div_iff hsN1.ne']
        linear_combination (2 * a * Real.sqrt (N - 1)) * hS2 +
          (-2 * b * Real.sqrt (N - 1)) * hX
      simp only [h, ite_false]
      rw [← hreal]
      push_cast
      ring

/-- **Grover's success probability**: after `k` queries on the input marking `z`, measuring the
query register gives `z` with probability `sin²((2k + 1) θ)`. -/
theorem regProb_run_grover (hN : 2 ≤ N) (z : Fin N) (k : ℕ) :
    regProb (run (grover N) (uniform N) (marked z) k) z =
      Real.sin ((2 * k + 1) * groverAngle N) ^ 2 := by
  simp only [regProb_eq_sum, run_grover hN, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.univ_unit, sum_singleton, ite_true, Bool.false_eq_true, ite_false, norm_zero,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- **Grover's algorithm** [Grover][Grover1996], with the analysis of [Boyer, Brassard, Høyer,
Tapp][BoyerBrassardHoyerTapp1998]: for `N ≥ 2` and every `z`, with
`T = ⌊π / (4θ)⌋` queries, where `θ = arcsin(1 / √N)`, the algorithm outputs the marked item `z`
with probability at least `1 - 1 / N`, and `T ≤ π √N / 4`. -/
theorem grover_success (hN : 2 ≤ N) (z : Fin N) :
    1 - (N : ℝ)⁻¹ ≤ regProb (run (grover N) (uniform N) (marked z)
        ⌊Real.pi / (4 * groverAngle N)⌋₊) z ∧
      (⌊Real.pi / (4 * groverAngle N)⌋₊ : ℝ) ≤ Real.pi * Real.sqrt N / 4 := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hsN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN0
  set θ := groverAngle N
  have hs : Real.sin θ = (Real.sqrt N)⁻¹ := sin_groverAngle hN
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (inv_pos.mpr hsN)
  have hθpi : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsinθ : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  set T := ⌊Real.pi / (4 * θ)⌋₊
  have hx : 0 ≤ Real.pi / (4 * θ) := by positivity
  have hT1 : (T : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le hx
  have hT2 : Real.pi / (4 * θ) < T + 1 := Nat.lt_floor_add_one _
  refine ⟨?_, ?_⟩
  · rw [regProb_run_grover hN]
    set y := (2 * (T : ℝ) + 1) * θ
    -- `y` lies within `θ` of `π / 2`.
    have hy1 : y ≤ Real.pi / 2 + θ := by
      have : (T : ℝ) * (4 * θ) ≤ Real.pi := (le_div_iff₀ (by positivity)).mp hT1
      simp only [y]
      nlinarith
    have hy2 : Real.pi / 2 - θ < y := by
      have : Real.pi < ((T : ℝ) + 1) * (4 * θ) := (div_lt_iff₀ (by positivity)).mp hT2
      simp only [y]
      nlinarith
    -- So `|cos y| = |sin (π/2 - y)| ≤ sin θ`.
    have hcos : Real.cos y ^ 2 ≤ Real.sin θ ^ 2 := by
      rw [← Real.sin_pi_div_two_sub]
      have hu1 : -θ ≤ Real.pi / 2 - y := by linarith
      have hu2 : Real.pi / 2 - y ≤ θ := by linarith
      have h1 : Real.sin (Real.pi / 2 - y) ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hθpi hu2
      have h2 : Real.sin (-θ) ≤ Real.sin (Real.pi / 2 - y) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hu1
      rw [Real.sin_neg] at h2
      nlinarith
    have hsq : Real.sin θ ^ 2 = (N : ℝ)⁻¹ := by
      rw [hs, inv_pow, Real.sq_sqrt hN0.le]
    nlinarith [Real.sin_sq_add_cos_sq y]
  · calc
      (T : ℝ) ≤ Real.pi / (4 * θ) := hT1
      _ ≤ Real.pi / (4 * Real.sin θ) := by
        gcongr
        rw [hs]
        positivity
      _ = Real.pi * Real.sqrt N / 4 := by
        rw [hs]
        field_simp

end Cslib.Quantum
