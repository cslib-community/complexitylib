/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Midrijanis
public import Complexity.Computability.QueryComplexity.Quantum.Polynomial
public import Complexity.Computability.QueryComplexity.SpectralSensitivity
import Complexity.Foundations.Quantum.Measurement.Overlap

/-!
# Spectral sensitivity bounds quantum queries, and `D(f) = O(Q(f)⁴)`

A `T`-query algorithm computing `f` with error `ε ≤ 1/2` gives
`(1 - 2√(ε(1-ε))) λ(f) ≤ 2T` (`Cslib.Quantum.one_sub_mul_spectralSensitivity_le`), where `λ(f)`
is the spectral sensitivity (`Cslib.BitString.spectralSensitivity`). With Huang's
`deg(f) ≤ λ(f)²` (`Cslib.QueryComplexity.degree_le_spectralSensitivity_sq`) this gives
`deg(f) ≤ 1296 T²` at error `1/3` (`Cslib.Quantum.degree_le_mul_sq`), and with Midrijanis's
`D(f) ≤ deg(f) bs(f)` and the polynomial method's `bs(f) ≤ 16 T²` it gives the theorem of
[Aaronson, Ben-David, Kothari, Rao, Tal][AaronsonBenDavidKothariRaoTal2021]:
a deterministic decision tree of depth at most `20736 T⁴ = (12 T)⁴` computes `f`
(`Cslib.Quantum.complexity_le_mul_pow_four`). This improves the `4096 T⁶` of
`Cslib.Quantum.complexity_le_mul_pow_six` once `T ≥ 3`.

**The adversary argument.** Let `ψₓᵗ` be the state after `t` queries on input `x`, and fix
nonnegative weights `u` and `w` on the cube. The progress measure sums
`u(x) w(x ⊕ eᵢ) |⟨ψₓᵗ, ψ_{x ⊕ eᵢ}ᵗ⟩|` over the sensitive edges `(x, i)` of `f`.
* Before any query all states are equal, so the measure is the form
  `⟨u, A_f w⟩ = ∑_x ∑_{i sensitive at x} u(x) w(x ⊕ eᵢ)`.
* The inputs `x` and `x ⊕ eᵢ` have oracles that differ only on query index `i` with control bit
  `1`, so one query changes their overlap by `2 ⟨Π_i ψₓ, Π_i ψ_{x ⊕ eᵢ}⟩`
  (`Cslib.Quantum.inner_phaseOracle_update_not`), where `Π_i` is `Cslib.Quantum.ctrlProj`. By
  `2ab ≤ a² + b²` and `∑_i ‖Π_i ψ‖² ≤ 1`, counting each edge from both of its ends, a query lowers
  the measure by at most `‖u‖² + ‖w‖²`.
* At the end, inputs with different values of `f` have overlap at most `2√(ε(1-ε))`, because
  `|⟨ψ, φ⟩|² + (p - q)² ≤ 1` for unit states whose acceptance probabilities are `p` and `q`
  (`Cslib.Quantum.norm_inner_sq_add_sq_measureProb_sub_le_one`).

So `(1 - 2√(ε(1-ε))) ⟨u, A_f w⟩ ≤ T (‖u‖² + ‖w‖²)`
(`Cslib.Quantum.one_sub_mul_sum_sensitiveCoords_le`), and unit vectors bound `λ(f)` by
`Cslib.BitString.spectralSensitivity_le_of_forall_sum_le`.

**Source mapping** (numbering of arXiv:2010.12629v1). `complexity_le_mul_pow_four` is
Theorem 2, `D(f) = O(Q(f)⁴)`, proved as in the source (p. 2) from Midrijanis's inequality (4),
`bs(f) = O(Q(f)²)` and Theorem 3. `degree_le_mul_sq` is Theorem 3, `deg(f) = O(Q(f)²)`, from
Theorem 1 and Lemma 9. `one_sub_mul_spectralSensitivity_le` is the part `λ(f) = O(Q(f))` of
Lemma 9 (for total functions). The source proves Lemma 9 by taking the spectral adversary matrix
`Γ = A_f` and citing `Q(f) = Ω(SA(f))` [BSS03 in the source]; here the progress-measure argument
for this `Γ` is carried out directly in the query model of `Cslib.Quantum.run`, with weights from
two nonnegative unit vectors in place of a principal eigenvector. The constants `2`, `36`, `1296`
and `20736` are those of this proof; the source states only `O(·)` bounds. Like the polynomial
method, the bounds hold for each algorithm; there is no separate definition of quantum query
complexity.

## Main results

* `Cslib.Quantum.inner_phaseOracle_update_not`: one query changes the overlap of the states on
  neighboring inputs by `2 ⟨Π_i ψ, Π_i φ⟩`.
* `Cslib.Quantum.one_sub_mul_sum_sensitiveCoords_le`: the adversary bound for the sensitivity graph.
* `Cslib.Quantum.one_sub_mul_spectralSensitivity_le`: `(1 - 2√(ε(1-ε))) λ(f) ≤ 2T`.
* `Cslib.Quantum.spectralSensitivity_le_thirty_six_mul`: `λ(f) ≤ 36 T` at error `1/3`.
* `Cslib.Quantum.degree_le_mul_sq`: `deg(f) ≤ 1296 T²` at error `1/3`.
* `Cslib.Quantum.complexity_le_mul_pow_four`: `D(f) ≤ 20736 T⁴` at error `1/3`.

## References

* [S. Aaronson, S. Ben-David, R. Kothari, S. Rao, A. Tal, *Degree vs. approximate degree and
  quantum implications of Huang's sensitivity theorem*][AaronsonBenDavidKothariRaoTal2021]
* [G. Midrijanis, *Exact quantum query complexity for total Boolean functions*][Midrijanis2004]
* [R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf, *Quantum lower bounds by
  polynomials*][BealsBuhrmanCleveMoscaDeWolf2001]
-/

public section

namespace Cslib.Quantum

open Finset Function BitString QueryComplexity

variable {N : ℕ} {W : Type*} [Fintype W]

/-- **One query on neighboring inputs**: the oracles of `x` and of `x ⊕ eᵢ` differ only on query
index `i` with control bit `1`, so applying them changes the overlap of two states by
`2 ⟨Π_i ψ, Π_i φ⟩`. -/
theorem inner_phaseOracle_update_not (x : Fin N → Bool) (i : Fin N) (ψ φ : State N W) :
    inner ℂ (phaseOracle x ψ) (phaseOracle (update x i (!x i)) φ) =
      inner ℂ ψ φ - 2 * inner ℂ (ctrlProj i ψ) (ctrlProj i φ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  obtain ⟨j, b, w⟩ := p
  simp only [phaseOracle_apply, ctrlProj, PiLp.toLp_apply, map_mul]
  by_cases hj : j = i
  · subst hj
    cases b <;> cases x j <;>
      simp only [Bool.and_self, Bool.and_true, Bool.and_false, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, update_self, and_self, and_false, map_one, map_neg,
        map_zero, one_mul, neg_mul, mul_neg, mul_zero, sub_zero] <;>
      ring
  · have hji : update x i (!x i) j = x j := update_of_ne hj _ _
    simp only [hji, hj, false_and, ↓reduceIte, map_zero, mul_zero, sub_zero]
    split_ifs <;> simp

/-- A query algorithm with a unit initial state and error `ε ≤ 1/2` leaves the states on inputs
with different values of `f` with overlap at most `2√(ε(1-ε))`. -/
theorem norm_inner_run_le {f : BooleanFunction N} {ε : ℝ}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε)
    (hε : 2 * ε ≤ 1) {x y : Fin N → Bool} (hxy : f x ≠ f y) :
    ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)‖ ≤ 2 * √(ε * (1 - ε)) := by
  have hov := norm_inner_sq_add_sq_measureProb_sub_le_one (norm_run U ψ₀ x T ▸ hψ₀)
    (norm_run U ψ₀ y T ▸ hψ₀) S
  obtain ⟨hx₁, hx₂⟩ := abs_le.1 (h x)
  obtain ⟨hy₁, hy₂⟩ := abs_le.1 (h y)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h x)
  -- the acceptance probabilities differ by at least `1 - 2ε`
  have hgap : (1 - 2 * ε) ^ 2 ≤
      (measureProb (run U ψ₀ x T) S - measureProb (run U ψ₀ y T) S) ^ 2 := by
    rw [← sq_abs (measureProb (run U ψ₀ x T) S - measureProb (run U ψ₀ y T) S)]
    refine pow_le_pow_left₀ (by linarith) ?_ 2
    cases hfx : f x <;> cases hfy : f y <;> simp only [hfx, hfy, ne_eq, not_true_eq_false] at hxy
    · simp only [hfx, hfy, bitVal_false, bitVal_true, sub_zero] at hx₁ hx₂ hy₁ hy₂
      rw [abs_sub_comm]
      exact (by linarith : 1 - 2 * ε ≤ _).trans (le_abs_self _)
    · simp only [hfx, hfy, bitVal_false, bitVal_true, sub_zero] at hx₁ hx₂ hy₁ hy₂
      exact (by linarith : 1 - 2 * ε ≤ _).trans (le_abs_self _)
  have hc : (2 * √(ε * (1 - ε))) ^ 2 = 4 * (ε * (1 - ε)) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hε0 (by linarith))]
    norm_num
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [hc]
  nlinarith

section Progress

/-- The progress measure of the adversary argument: the overlaps after `t` queries of the states
on the ends of the sensitive edges `(x, i)` of `f`, weighted by `u(x) w(x ⊕ eᵢ)`. -/
private noncomputable def progress (f : BooleanFunction N) (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    (ψ₀ : State N W) (u w : BitString N → ℝ) (t : ℕ) : ℝ :=
  ∑ x, ∑ i ∈ sensitiveCoords f x, u x * w (update x i (!x i)) *
    ‖inner ℂ (run U ψ₀ x t) (run U ψ₀ (update x i (!x i)) t)‖

variable {f : BooleanFunction N} (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W}
  {u w : BitString N → ℝ}

/-- One query lowers the overlap of the states on `x` and on `x ⊕ eᵢ` by at most
`2 ‖Π_i ψₓ‖ ‖Π_i ψ_{x ⊕ eᵢ}‖`. -/
private theorem norm_inner_run_succ (x : Fin N → Bool) (i : Fin N) (t : ℕ) :
    ‖inner ℂ (run U ψ₀ x t) (run U ψ₀ (update x i (!x i)) t)‖ -
        2 * (‖ctrlProj i (run U ψ₀ x t)‖ * ‖ctrlProj i (run U ψ₀ (update x i (!x i)) t)‖) ≤
      ‖inner ℂ (run U ψ₀ x (t + 1)) (run U ψ₀ (update x i (!x i)) (t + 1))‖ := by
  change _ ≤ ‖inner ℂ (U (t + 1) (phaseOracle x (run U ψ₀ x t)))
    (U (t + 1) (phaseOracle (update x i (!x i)) (run U ψ₀ (update x i (!x i)) t)))‖
  rw [LinearIsometry.inner_map_map, inner_phaseOracle_update_not]
  have h₁ := norm_inner_le_norm (𝕜 := ℂ) (ctrlProj i (run U ψ₀ x t))
    (ctrlProj i (run U ψ₀ (update x i (!x i)) t))
  have h₂ := norm_sub_norm_le (inner ℂ (run U ψ₀ x t) (run U ψ₀ (update x i (!x i)) t))
    (2 * inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ (update x i (!x i)) t)))
  rw [norm_mul, RCLike.norm_ofNat] at h₂
  linarith

/-- **One query makes little progress**: it lowers the progress measure by at most
`‖u‖² + ‖w‖²`. -/
private theorem progress_sub_progress_succ_le (hψ₀ : ‖ψ₀‖ = 1) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (t : ℕ) :
    progress f U ψ₀ u w t - progress f U ψ₀ u w (t + 1) ≤ ∑ x, u x ^ 2 + ∑ x, w x ^ 2 := by
  set a : BitString N → Fin N → ℝ := fun x i => ‖ctrlProj i (run U ψ₀ x t)‖ with ha_def
  -- the query magnitudes of a unit state sum to at most `1`
  have ha (x : BitString N) : ∑ i, a x i ^ 2 ≤ 1 := by
    calc ∑ i, a x i ^ 2 ≤ ∑ i, regProb (run U ψ₀ x t) i :=
          sum_le_sum fun i _ => norm_sq_ctrlProj_le i _
      _ = 1 := by rw [sum_regProb, norm_run, hψ₀, one_pow]
  have hweight (v : BitString N → ℝ) :
      ∑ x, ∑ i ∈ sensitiveCoords f x, v x ^ 2 * a x i ^ 2 ≤ ∑ x, v x ^ 2 := by
    refine sum_le_sum fun x _ => ?_
    calc ∑ i ∈ sensitiveCoords f x, v x ^ 2 * a x i ^ 2 ≤ ∑ i, v x ^ 2 * a x i ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => by positivity
      _ = v x ^ 2 * ∑ i, a x i ^ 2 := by rw [mul_sum]
      _ ≤ v x ^ 2 * 1 := mul_le_mul_of_nonneg_left (ha x) (sq_nonneg _)
      _ = v x ^ 2 := mul_one _
  have h₁ := hweight u
  -- the weights at the far ends, counted from those ends
  have h₂ := hweight w
  rw [← sum_sum_sensitiveCoords_update f fun i y => w y ^ 2 * a y i ^ 2] at h₂
  have key : progress f U ψ₀ u w t - progress f U ψ₀ u w (t + 1) ≤
      ∑ x, ∑ i ∈ sensitiveCoords f x, (u x ^ 2 * a x i ^ 2 +
        w (update x i (!x i)) ^ 2 * a (update x i (!x i)) i ^ 2) := by
    simp only [progress, ← sum_sub_distrib]
    refine sum_le_sum fun x _ => sum_le_sum fun i _ => ?_
    have hstep := norm_inner_run_succ U (ψ₀ := ψ₀) x i t
    have huw : 0 ≤ u x * w (update x i (!x i)) := mul_nonneg (hu x) (hw _)
    have := mul_le_mul_of_nonneg_left hstep huw
    simp only [ha_def]
    nlinarith [sq_nonneg (u x * ‖ctrlProj i (run U ψ₀ x t)‖ -
      w (update x i (!x i)) * ‖ctrlProj i (run U ψ₀ (update x i (!x i)) t)‖)]
  simp only [sum_add_distrib] at key
  linarith

/-- Telescoping: `T` queries lower the progress measure by at most `T (‖u‖² + ‖w‖²)`. -/
private theorem progress_zero_sub_le (hψ₀ : ‖ψ₀‖ = 1) (hu : 0 ≤ u) (hw : 0 ≤ w) (T : ℕ) :
    progress f U ψ₀ u w 0 - progress f U ψ₀ u w T ≤ T * (∑ x, u x ^ 2 + ∑ x, w x ^ 2) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have := progress_sub_progress_succ_le (f := f) U hψ₀ hu hw T
    push_cast
    linarith

/-- Before any query the states agree, so the progress measure is the form `⟨u, A_f w⟩`. -/
private theorem progress_zero (hψ₀ : ‖ψ₀‖ = 1) :
    progress f U ψ₀ u w 0 = ∑ x, ∑ i ∈ sensitiveCoords f x, u x * w (update x i (!x i)) := by
  have h : ‖inner ℂ (U 0 ψ₀) (U 0 ψ₀)‖ = 1 := by
    rw [LinearIsometry.inner_map_map, inner_self_eq_norm_sq_to_K, hψ₀]
    simp
  simp only [progress, run, h, mul_one]

end Progress

/-- **The adversary bound for the sensitivity graph**: if a `T`-query algorithm with a unit
initial state accepts every input `x`, by an outcome in `S`, with probability within `ε ≤ 1/2` of
`f(x)`, then for all nonnegative weights `u` and `w` on the cube,
`(1 - 2√(ε(1-ε))) ⟨u, A_f w⟩ ≤ T (‖u‖² + ‖w‖²)`, where `A_f` is the adjacency matrix of the
sensitivity graph. -/
theorem one_sub_mul_sum_sensitiveCoords_le {f : BooleanFunction N} {ε : ℝ}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε)
    (hε : 2 * ε ≤ 1) {u w : BitString N → ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    (1 - 2 * √(ε * (1 - ε))) * ∑ x, ∑ i ∈ sensitiveCoords f x, u x * w (update x i (!x i)) ≤
      T * (∑ x, u x ^ 2 + ∑ x, w x ^ 2) := by
  have hT := progress_zero_sub_le (f := f) U hψ₀ hu hw T
  rw [progress_zero U hψ₀] at hT
  -- at the end, the overlaps across sensitive edges are small
  have hend : progress f U ψ₀ u w T ≤
      2 * √(ε * (1 - ε)) * ∑ x, ∑ i ∈ sensitiveCoords f x, u x * w (update x i (!x i)) := by
    simp only [progress, mul_sum]
    refine sum_le_sum fun x _ => sum_le_sum fun i hi => ?_
    have hxy : f x ≠ f (update x i (!x i)) := (mem_sensitiveCoords.1 hi).symm
    have := norm_inner_run_le U hψ₀ T S h hε hxy
    have huw : 0 ≤ u x * w (update x i (!x i)) := mul_nonneg (hu x) (hw _)
    nlinarith
  linarith

/-- **Spectral sensitivity bounds quantum queries**: if a `T`-query algorithm with a unit initial
state accepts every input `x`, by an outcome in `S`, with probability within `ε ≤ 1/2` of `f(x)`,
then `(1 - 2√(ε(1-ε))) λ(f) ≤ 2T` [AaronsonBenDavidKothariRaoTal2021], Lemma 9, with the
constant of this proof. -/
theorem one_sub_mul_spectralSensitivity_le {f : BooleanFunction N} {ε : ℝ}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε)
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * spectralSensitivity f ≤ 2 * T := by
  set c := 1 - 2 * √(ε * (1 - ε))
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h fun _ => false)
  have hc : 0 ≤ c := by
    have : √(ε * (1 - ε)) ≤ 1 / 2 :=
      (Real.sqrt_le_left (by norm_num)).2 (by nlinarith [sq_nonneg (1 - 2 * ε)])
    linarith
  rcases hc.eq_or_lt with hc0 | hc0
  · rw [← hc0, zero_mul]
    positivity
  have hlam : spectralSensitivity f ≤ 2 * T / c := by
    refine spectralSensitivity_le_of_forall_sum_le (by positivity)
      fun u w hu hw hu1 hw1 => ?_
    have := one_sub_mul_sum_sensitiveCoords_le U hψ₀ T S h hε hu hw
    rw [hu1, hw1] at this
    rw [le_div_iff₀ hc0]
    linarith
  rwa [le_div_iff₀ hc0, mul_comm] at hlam

/-- **Spectral sensitivity bounds bounded-error quantum queries**: if a `T`-query algorithm with a
unit initial state accepts every input `x`, by an outcome in `S`, with probability within `1/3` of
`f(x)`, then `λ(f) ≤ 36 T`. -/
theorem spectralSensitivity_le_thirty_six_mul {f : BooleanFunction N}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ 1 / 3) :
    spectralSensitivity f ≤ 36 * T := by
  have := one_sub_mul_spectralSensitivity_le U hψ₀ T S h (by norm_num)
  -- `2√(2/9) ≤ 17/18`, since `8/9 = 288/324 ≤ 289/324`
  have hsqrt : √((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 17 / 36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hlam := spectralSensitivity_nonneg f
  nlinarith

/-- **Degree is at most quadratic in bounded-error quantum queries**: if a `T`-query algorithm with
a unit initial state accepts every input `x`, by an outcome in `S`, with probability within `1/3`
of `f(x)`, then `deg(f) ≤ 1296 T²` [AaronsonBenDavidKothariRaoTal2021], Theorem 3, with the
constant of this proof. -/
theorem degree_le_mul_sq {f : BooleanFunction N}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ 1 / 3) :
    degree f ≤ 1296 * T ^ 2 := by
  have h₁ := degree_le_spectralSensitivity_sq f
  have h₂ := pow_le_pow_left₀ (spectralSensitivity_nonneg f)
    (spectralSensitivity_le_thirty_six_mul U hψ₀ T S h) 2
  have : (degree f : ℝ) ≤ 1296 * T ^ 2 := by nlinarith
  exact_mod_cast this

/-- **Deterministic simulation of bounded-error quantum queries with a quartic overhead**: if a
`T`-query algorithm with a unit initial state accepts every input `x`, by an outcome in `S`, with
probability within `1/3` of `f(x)`, then a deterministic decision tree of depth at most
`20736 T⁴ = (12 T)⁴` computes `f` [AaronsonBenDavidKothariRaoTal2021], Theorem 2, with the
constant of this proof. -/
theorem complexity_le_mul_pow_four {f : BooleanFunction N}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ 1 / 3) :
    DecisionTree.complexity f ≤ 20736 * T ^ 4 :=
  (DecisionTree.complexity_le_degree_mul_blockSensitivity f).trans
    ((Nat.mul_le_mul (degree_le_mul_sq U hψ₀ T S h)
      (blockSensitivity_le_sixteen_mul_sq U hψ₀ T S h)).trans_eq (by ring))

end Cslib.Quantum
