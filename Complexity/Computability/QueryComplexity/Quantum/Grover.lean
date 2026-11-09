/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.Search
public import Complexity.Foundations.Data.BitString.Weight
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

The general marked-weight formula is shared with the unknown-count search analysis:
`run_grover_of_weight` handles all marked counts, and `run_grover` specializes it to one
marked item.

## Main definitions

* `Cslib.Quantum.searchAngle`: the angle for an arbitrary number of marked items.
* `Cslib.Quantum.uniform`: the uniform superposition.
* `Cslib.Quantum.diffusion`: the reflection about the uniform superposition.
* `Cslib.Quantum.grover`: the isometries of Grover's algorithm.

## Main results

* `Cslib.Quantum.run_grover_of_weight`: the state for any number of marked items.
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

open Finset Real BitString

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

/-- The angle `θ ∈ [0, π / 2]` with `sin² θ = t / N`. -/
noncomputable def searchAngle (N t : ℕ) : ℝ := Real.arcsin (Real.sqrt (t / N))

private theorem div_le_one_of_le' {t : ℕ} (ht : t ≤ N) : (t : ℝ) / N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]
    exact_mod_cast ht

theorem sin_searchAngle {t : ℕ} (ht : t ≤ N) :
    Real.sin (searchAngle N t) = Real.sqrt (t / N) := by
  refine Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((t : ℝ) / N)]) ?_
  rw [Real.sqrt_le_one]
  exact div_le_one_of_le' ht

theorem cos_searchAngle (t : ℕ) :
    Real.cos (searchAngle N t) = Real.sqrt (1 - t / N) := by
  rw [searchAngle, Real.cos_arcsin, Real.sq_sqrt (by positivity)]

theorem searchAngle_nonneg (N t : ℕ) : 0 ≤ searchAngle N t :=
  Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)

theorem searchAngle_self (hN : 0 < N) : searchAngle N N = π / 2 := by
  rw [searchAngle, div_self (by exact_mod_cast hN.ne'), Real.sqrt_one, Real.arcsin_one]

theorem searchAngle_zero (N : ℕ) : searchAngle N 0 = 0 := by
  simp [searchAngle]

/-- **Grover's algorithm with any number of marked items** [Boyer, Brassard, Høyer,
Tapp][BoyerBrassardHoyerTapp1998]: on an input with `t` marked items, after `k` queries, with
control bit `1`, every marked item has amplitude `sin((2k + 1) θ) / √t` and every other item
`cos((2k + 1) θ) / √(N - t)`, where `sin² θ = t / N`; with control bit `0`, every amplitude is
`0`. -/
theorem run_grover_of_weight (hN : 0 < N) (x : Fin N → Bool) (k : ℕ) (p : Fin N × Bool × Unit) :
    (run (grover N) (uniform N) x k).ofLp p =
      if p.2.1 then ((if x p.1 then
          Real.sin ((2 * k + 1) * searchAngle N (weight x)) / Real.sqrt (weight x)
        else Real.cos ((2 * k + 1) * searchAngle N (weight x)) / Real.sqrt (N - weight x) : ℝ) :
          ℂ) else 0 := by
  set t := weight x with ht_def
  have htN : t ≤ N := weight_le_length x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have htN' : (t : ℝ) ≤ N := by exact_mod_cast htN
  set θ := searchAngle N t
  set sN := Real.sqrt N
  set st := Real.sqrt t
  set su := Real.sqrt (N - t)
  have hsN : 0 < sN := Real.sqrt_pos.mpr hN0
  have hsN2 : sN ^ 2 = N := Real.sq_sqrt hN0.le
  have hst2 : st ^ 2 = t := Real.sq_sqrt (Nat.cast_nonneg t)
  have hsu2 : su ^ 2 = N - t := Real.sq_sqrt (by linarith)
  have hs : Real.sin θ = st / sN := by
    rw [sin_searchAngle htN, Real.sqrt_div' _ hN0.le]
  have hc : Real.cos θ = su / sN := by
    rw [cos_searchAngle, show (1 : ℝ) - t / N = (N - t) / N by field_simp,
      Real.sqrt_div' _ hN0.le]
  -- A marked item exists only if `t ≠ 0`, and an unmarked one only if `t ≠ N`.
  have hmarked : ∀ i, x i = true → st ≠ 0 := by
    intro i hi
    refine (Real.sqrt_pos.mpr ?_).ne'
    have : 0 < t := card_pos.mpr ⟨i, by simp [hi]⟩
    exact_mod_cast this
  have hunmarked : ∀ i, x i = false → su ≠ 0 := by
    intro i hi
    refine (Real.sqrt_pos.mpr ?_).ne'
    have h1 : 0 < #{j | x j = false} := card_pos.mpr ⟨i, by simp [hi]⟩
    have h2 := card_filter_eq_false_eq_card_sub_weight x
    rw [Fintype.card_fin] at h2
    have : t < N := by omega
    have : (t : ℝ) < N := by exact_mod_cast this
    linarith
  induction k generalizing p with
  | zero =>
    obtain ⟨i, c, u⟩ := p
    simp only [run, grover, LinearIsometry.id_apply, uniform, PiLp.toLp_apply, Nat.cast_zero,
      mul_zero, zero_add, one_mul]
    cases c
    · rfl
    simp only [ite_true]
    congr 1
    cases hi : x i
    · simp only [Bool.false_eq_true, ite_false, hc]
      field_simp [hunmarked i hi]
      rfl
    · simp only [ite_true, hs]
      field_simp [hmarked i hi]
      rfl
  | succ k ih =>
    set S := Real.sin ((2 * k + 1) * θ) with hS
    set C := Real.cos ((2 * k + 1) * θ) with hC
    -- The total control-`1` amplitude after the oracle.
    have hta : (t : ℝ) * (S / st) = st * S := by
      by_cases h : st = 0
      · have : (t : ℝ) = 0 := by rw [← hst2, h]; ring
        simp [h, this]
      · field_simp
        rw [← hst2]
        ring
    have hub : ((N : ℝ) - t) * (C / su) = su * C := by
      by_cases h : su = 0
      · have : (N : ℝ) - t = 0 := by rw [← hsu2, h]; ring
        simp [h, this]
      · field_simp
        rw [← hsu2]
        ring
    have hsum : ∑ q : Fin N × Bool × Unit, (if q.2.1 then (phaseOracle x
        (run (grover N) (uniform N) x k)).ofLp q else 0) = ((-(st * S) + su * C : ℝ) : ℂ) := by
      simp only [phaseOracle_apply, ih, Fintype.sum_prod_type, Fintype.univ_unit, sum_singleton,
        Fintype.sum_bool, ite_true, Bool.true_and, Bool.false_eq_true, ite_false, add_zero]
      have hterm : ∀ i : Fin N, (if x i = true then (-1 : ℂ) else 1) *
          ((if x i = true then S / st else C / su : ℝ) : ℂ) =
            if x i = true then ((-(S / st) : ℝ) : ℂ) else ((C / su : ℝ) : ℂ) := by
        intro i
        by_cases h : x i = true <;> simp [h]
      rw [sum_congr rfl fun i _ => hterm i, sum_ite, sum_const, sum_const]
      have hcardT : #(univ.filter fun i : Fin N => x i = true) = t := rfl
      have hcardF : #(univ.filter fun i : Fin N => ¬x i = true) = N - t := by
        simpa [Fintype.card_fin] using card_filter_eq_false_eq_card_sub_weight x
      rw [hcardT, hcardF, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub htN]
      rw [← hta, ← hub]
      push_cast
      ring
    have harg : (2 * ((k + 1 : ℕ) : ℝ) + 1) * θ = (2 * k + 1) * θ + 2 * θ := by
      push_cast
      ring
    simp only [run, grover, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [diffusion_apply hN, hsum, phaseOracle_apply, ih]
    obtain ⟨i, c, u⟩ := p
    cases c
    · simp
    simp only [Bool.true_and, ite_true]
    cases hi : x i
    · have hsu0 := hunmarked i hi
      have hreal : 2 * ((N : ℝ)⁻¹ * (-(st * S) + su * C)) - C / su =
          Real.cos ((2 * ((k + 1 : ℕ) : ℝ) + 1) * θ) / su := by
        rw [harg, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc, ← hS, ← hC]
        field_simp
        rw [← hsN2]
        ring
      simp only [Bool.false_eq_true, ite_false]
      rw [← hreal]
      push_cast
      ring
    · have hst0 := hmarked i hi
      have hreal : 2 * ((N : ℝ)⁻¹ * (-(st * S) + su * C)) + S / st =
          Real.sin ((2 * ((k + 1 : ℕ) : ℝ) + 1) * θ) / st := by
        have hrel : sN ^ 2 = st ^ 2 + su ^ 2 := by rw [hsN2, hst2, hsu2]; ring
        rw [harg, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc, ← hS, ← hC]
        field_simp
        rw [← hsN2]
        linear_combination (2 * S * sN ^ 2) * hrel
      simp only [ite_true]
      rw [← hreal]
      push_cast
      ring

variable [DecidableEq (Fin N)]

/-- **The state of Grover's algorithm after `k` queries** on the input marking `z`: with control
bit `1`, amplitude `sin((2k + 1) θ)` on `z` and `cos((2k + 1) θ) / √(N - 1)` elsewhere; with
control bit `0`, amplitude `0`. -/
theorem run_grover (hN : 2 ≤ N) (z : Fin N) (k : ℕ) (p : Fin N × Bool × Unit) :
    (run (grover N) (uniform N) (marked z) k).ofLp p =
      if p.2.1 then ((if p.1 = z then Real.sin ((2 * k + 1) * groverAngle N)
        else Real.cos ((2 * k + 1) * groverAngle N) / Real.sqrt (N - 1) : ℝ) : ℂ) else 0 := by
  have hweight : weight (marked z) = 1 := by
    simp [weight, marked, Finset.filter_eq']
  have hangle : searchAngle N 1 = groverAngle N := by
    simp only [searchAngle, groverAngle, Nat.cast_one, one_div, Real.sqrt_inv]
  simpa only [hweight, hangle, Nat.cast_one, Real.sqrt_one, div_one, marked,
    decide_eq_true_eq] using
    run_grover_of_weight (by omega) (marked z) k p

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
