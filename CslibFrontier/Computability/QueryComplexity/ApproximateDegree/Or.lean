/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.NisanSzegedy
public import CslibFrontier.Computability.QueryComplexity.Threshold
public import Mathlib.RingTheory.Polynomial.Chebyshev
import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# The approximate degree of disjunction

The disjunction `OR_n` of `n` bits has approximate degree `Θ(√n)` [NisanSzegedy1994].

* **Lower bound**: `OR_n` is sensitive to every bit at the all-false input, so `bs(OR_n) = n`
  (`QueryComplexity.blockSensitivity_threshold_one_right`) and `n ≤ 6 adeg(OR_n)²` by the
  Nisan–Szegedy bound (`QueryComplexity.card_le_six_mul_approxDegree_threshold_one_right_sq`).
* **Upper bound**: a Chebyshev polynomial `T_d` stays in `[-1, 1]` on `[-1, 1]` and grows at least
  like `1 + d² μ` at `1 + μ` (`Polynomial.Chebyshev.one_add_sq_mul_le_eval_T`). With
  `u(k) = (n - k) / (n - 1)`, the polynomial `Q(k) = 1 - T_d(u(k)) / T_d(u(0))` vanishes at `0` and
  is within `1 / T_d(1 + 1/(n - 1)) ≤ 1 / 3` of `1` at `k = 1, …, n` once `d² ≥ 2 (n - 1)`;
  evaluated at the weight it has degree at most `d` on the cube
  (`QueryComplexity.approxDegree_threshold_one_right_le`). So `adeg(OR_n) ≤ ⌊√(2n)⌋ + 1`
  (`QueryComplexity.approxDegree_threshold_one_right_le_sqrt`).

## Main results

* `Polynomial.Chebyshev.one_add_sq_mul_le_eval_T`: `T_n(1 + μ) ≥ 1 + n² μ` for `μ ≥ 0`.
* `Cslib.QueryComplexity.card_le_six_mul_approxDegree_threshold_one_right_sq`:
  `n ≤ 6 adeg(OR_n)²`.
* `Cslib.QueryComplexity.approxDegree_threshold_one_right_le`: `adeg(OR_n) ≤ d` whenever
  `2n ≤ d² + 1`.
* `Cslib.QueryComplexity.approxDegree_threshold_one_right_le_sqrt`: `adeg(OR_n) ≤ ⌊√(2n)⌋ + 1`.

## References

* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Polynomial.Chebyshev

/-- **Growth of Chebyshev polynomials beyond `1`**: `T_n(1 + μ) ≥ 1 + n² μ` for `μ ≥ 0`. -/
theorem one_add_sq_mul_le_eval_T (n : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) :
    1 + n ^ 2 * μ ≤ (T ℝ n).eval (1 + μ) := by
  set a : ℕ → ℝ := fun k => (T ℝ k).eval (1 + μ)
  have hrec (k : ℕ) : a (k + 2) = 2 * (1 + μ) * a (k + 1) - a k := by
    simp only [a, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, T_add_two, eval_sub, eval_mul,
      eval_ofNat, eval_X]
  -- the increments grow: `a (k + 1) - a k ≥ (2k + 1) μ`
  suffices h : ∀ k : ℕ, 1 + k ^ 2 * μ ≤ a k ∧ (2 * k + 1) * μ ≤ a (k + 1) - a k from (h n).1
  intro k
  induction k with
  | zero => simp [a]
  | succ k ih =>
    obtain ⟨h₁, h₂⟩ := ih
    have h₃ : 1 + ((k + 1 : ℕ) : ℝ) ^ 2 * μ ≤ a (k + 1) := by push_cast; nlinarith
    refine ⟨h₃, ?_⟩
    have ha1 : 1 ≤ a (k + 1) := by
      have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 * μ := by positivity
      linarith
    have ha : μ ≤ μ * a (k + 1) := by nlinarith
    rw [hrec]
    push_cast at h₃ ⊢
    nlinarith

end Polynomial.Chebyshev

namespace Cslib.QueryComplexity

open BitString Polynomial

variable {n : ℕ}

/-- **The approximate degree of disjunction is at least `√(n / 6)`**: `n ≤ 6 adeg(OR_n)²`. -/
theorem card_le_six_mul_approxDegree_threshold_one_right_sq :
    n ≤ 6 * approxDegree (1 / 3) (threshold n 1) ^ 2 :=
  blockSensitivity_threshold_one_right.symm.trans_le
    (blockSensitivity_le_six_mul_approxDegree_sq _)

/-- **The approximate degree of disjunction is at most `√(2n)`**: `adeg(OR_n) ≤ d` whenever
`2n ≤ d² + 1`, by a rescaled Chebyshev polynomial of degree `d` evaluated at the weight. -/
theorem approxDegree_threshold_one_right_le {d : ℕ} (hd : 2 * n ≤ d ^ 2 + 1) :
    approxDegree (1 / 3) (threshold n 1) ≤ d := by
  rcases lt_or_ge n 2 with hn | hn
  · -- at most one bit: the disjunction itself has degree `n ≤ d`
    refine (approxDegree_le_degree (by norm_num)).trans ?_
    rw [degree_threshold_one_right]
    rcases Nat.lt_or_ge d 1 with hd1 | hd1
    · interval_cases d
      omega
    · omega
  have hN : (1 : ℝ) ≤ n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set N : ℝ := n - 1
  have hN0 : 0 < N := by linarith
  -- `L k = (n - k) / (n - 1)`, from `L 0 = 1 + 1 / N` down to `L n = 0`
  set L : ℝ[X] := C (n / N) - C (1 / N) * X
  have hL (t : ℝ) : L.eval t = (n - t) / N := by
    simp only [L, eval_sub, eval_C, eval_mul, eval_X]
    ring
  set τ := (Chebyshev.T ℝ d).eval (L.eval 0)
  have hτ : 3 ≤ τ := by
    have h := Chebyshev.one_add_sq_mul_le_eval_T d (μ := 1 / N) (by positivity)
    have hL0 : L.eval 0 = 1 + 1 / N := by
      rw [hL]
      field_simp
      ring
    have hd' : 2 * N ≤ (d : ℝ) ^ 2 := by
      have : (2 * n : ℝ) ≤ d ^ 2 + 1 := by exact_mod_cast hd
      linarith
    have : 2 ≤ (d : ℝ) ^ 2 * (1 / N) := by
      rw [mul_one_div, le_div_iff₀ hN0]
      exact hd'
    simp only [τ, hL0]
    linarith
  have hτ0 : 0 < τ := by linarith
  set Q : ℝ[X] := 1 - C τ⁻¹ * (Chebyshev.T ℝ d).comp L
  have hQdeg : Q.natDegree ≤ d := by
    have hLdeg : L.natDegree ≤ 1 :=
      natDegree_sub_le_of_le ((natDegree_C _).le.trans zero_le_one)
        ((natDegree_C_mul_le _ _).trans natDegree_X_le)
    have hTL : ((Chebyshev.T ℝ d).comp L).natDegree ≤ d := by
      refine natDegree_comp_le.trans ?_
      rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
      nlinarith
    exact (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans hTL))
  refine approxDegree_le_of_mem_lowDegree (p := fun x => Q.eval (weight x : ℝ))
    (lowDegree_mono hQdeg (eval_weight_mem_lowDegree Q)) fun x => ?_
  have hQ (t : ℝ) : Q.eval t = 1 - τ⁻¹ * (Chebyshev.T ℝ d).eval (L.eval t) := by
    simp only [Q, eval_sub, eval_one, eval_mul, eval_C, eval_comp]
  rw [threshold_apply, hQ]
  rcases Nat.eq_zero_or_pos (weight x) with h0 | hpos
  · -- the all-false input: `Q 0 = 0`
    rw [h0, Nat.cast_zero, inv_mul_cancel₀ hτ0.ne']
    simp
  · -- an input of weight `k ≥ 1`: `|Q k - 1| ≤ 1 / τ ≤ 1 / 3`
    have hk : (1 : ℝ) ≤ weight x := by exact_mod_cast hpos
    have hkn : (weight x : ℝ) ≤ n := by
      have := weight_le x
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have hu : |L.eval (weight x : ℝ)| ≤ 1 := by
      rw [hL, abs_le]
      constructor
      · rw [le_div_iff₀ hN0]; linarith
      · rw [div_le_iff₀ hN0]; linarith
    have hT := Chebyshev.abs_eval_T_real_le_one d hu
    have h1 : decide (1 ≤ weight x) = true := decide_eq_true hpos
    rw [h1, bitVal_true, sub_sub_cancel_left, abs_neg, abs_mul, abs_inv, abs_of_pos hτ0]
    calc τ⁻¹ * |(Chebyshev.T ℝ d).eval (L.eval (weight x : ℝ))| ≤ τ⁻¹ * 1 := by gcongr
      _ ≤ 1 / 3 := by
        rw [mul_one, inv_le_comm₀ hτ0 (by norm_num)]
        norm_num
        exact hτ

/-- `adeg(OR_n) ≤ ⌊√(2n)⌋ + 1`. -/
theorem approxDegree_threshold_one_right_le_sqrt :
    approxDegree (1 / 3) (threshold n 1) ≤ Nat.sqrt (2 * n) + 1 :=
  approxDegree_threshold_one_right_le (by nlinarith [Nat.lt_succ_sqrt (2 * n)])

end Cslib.QueryComplexity
