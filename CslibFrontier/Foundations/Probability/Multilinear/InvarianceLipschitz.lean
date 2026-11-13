/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Multilinear.Invariance
public import Mathlib.Topology.EMetricSpace.Lipschitz
import CslibFrontier.Foundations.Analysis.Calculus.LipschitzSmoothing
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz

/-!
# The Basic Invariance Principle for Lipschitz test functions

**Corollary 11.68** of [O'Donnell][ODonnell2014]: in the setting of Corollary 11.67
(`abs_integral_comp_multilinearEval_sub_le_of_influence_le`: `F` of degree at most `k` with
`Var[F] ≤ 1` and all influences at most `ε`, and independent variables whose laws satisfy
Hypothesis 11.65), if `ψ : ℝ → ℝ` is merely `K`-Lipschitz, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ 9 K · 2ᵏ · ε^(1/4)`.

The proof smooths `ψ` by the four-fold moving average from
`CslibFrontier.Foundations.Analysis.Calculus.LipschitzSmoothing`: with window `h > 0`, `ψ̃` is of
class `C⁴`, satisfies `|ψ̃ - ψ| ≤ 4 K h` and `|ψ̃''''| ≤ 8 K / h³`. The general transfer
`abs_integral_comp_sub_le_of_lipschitzWith` turns any `C⁴` comparison
`|E[φ(X)] - E[φ(Y)]| ≤ C τ⁴` (for `|φ''''| ≤ C`) into `|E[ψ(X)] - E[ψ(Y)]| ≤ 16 K τ`, by taking
`h = τ`. With the bound `C / 12 · k · 9ᵏ · ε` of Corollary 11.67 one may take
`τ = 9/16 · 2ᵏ · ε^(1/4)`, since `k 9ᵏ ε / 12 ≤ τ⁴` by `k 9ᵏ ≤ 16ᵏ`.

Lipschitz tests are also stable under `L²` perturbations, `|E[ψ(X)] - E[ψ(Y)]| ≤ K ‖X - Y‖₂`
(`LipschitzWith.abs_integral_comp_sub_le_sqrt`), so
by the orthonormality of monomials two polynomials `F` and `G` in variables satisfying
Hypothesis 11.65 give `|E[ψ(F(z))] - E[ψ(G(z))]| ≤ K ‖F̂ - Ĝ‖₂`. This is the tail estimate in the
proof of Corollary 11.69.

## Main results

* `ProbabilityTheory.abs_integral_comp_sub_le_of_lipschitzWith`: from `C⁴` tests to Lipschitz
  tests.
* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le_of_lipschitzWith`:
  Corollary 11.68.
* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le_sqrt`:
  `|E[ψ(F(z))] - E[ψ(G(z))]| ≤ K √(∑ S, (F̂(S) - Ĝ(S))²)` under Hypothesis 11.65.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.6.
-/

public section

open MeasureTheory Finset Real
open scoped NNReal

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {Q : Measure Ω'}

/-! ### From `C⁴` tests to Lipschitz tests -/

/-- If `φ(X)` is integrable and `|ψ - φ| ≤ M`, then `ψ(X)` is integrable and its expectation is
within `M` of that of `φ(X)`. -/
private theorem integrable_and_abs_integral_sub_le [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ u, |ψ u - φ u| ≤ M) (hφX : Integrable (fun ω => φ (X ω)) P) :
    Integrable (fun ω => ψ (X ω)) P ∧ |∫ ω, ψ (X ω) ∂P - ∫ ω, φ (X ω) ∂P| ≤ M := by
  have hb : ∀ᵐ ω ∂P, ‖ψ (X ω) - φ (X ω)‖ ≤ M := ae_of_all _ fun ω => hM (X ω)
  have hd : Integrable (fun ω => ψ (X ω) - φ (X ω)) P :=
    Integrable.of_bound ((hψ.sub hφ).comp_aestronglyMeasurable hX.aestronglyMeasurable) M hb
  have hψX : Integrable (fun ω => ψ (X ω)) P :=
    (hd.add hφX).congr (ae_of_all _ fun ω => sub_add_cancel _ _)
  refine ⟨hψX, ?_⟩
  rw [← integral_sub hψX hφX]
  simpa using norm_integral_le_of_norm_le_const hb

/-- **From `C⁴` tests to Lipschitz tests**: suppose that for every `φ` of class `C⁴` with
`|φ''''| ≤ C`, the random variables `φ(X)` and `φ(Y)` are integrable and
`|E[φ(X)] - E[φ(Y)]| ≤ C τ⁴`. Then `|E[ψ(X)] - E[ψ(Y)]| ≤ 16 K τ` for every `K`-Lipschitz `ψ`.
This is the smoothing argument behind [O'Donnell, Corollary 11.68][ODonnell2014]. -/
theorem abs_integral_comp_sub_le_of_lipschitzWith [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {X : Ω → ℝ} {Y : Ω' → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (h : ∀ (φ : ℝ → ℝ) (C : ℝ), ContDiff ℝ 4 φ → (∀ u, |iteratedDeriv 4 φ u| ≤ C) →
      Integrable (fun ω => φ (X ω)) P ∧ Integrable (fun ω => φ (Y ω)) Q ∧
        |∫ ω, φ (X ω) ∂P - ∫ ω, φ (Y ω) ∂Q| ≤ C * τ ^ 4)
    {ψ : ℝ → ℝ} {K : ℝ≥0} (hψ : LipschitzWith K ψ) :
    |∫ ω, ψ (X ω) ∂P - ∫ ω, ψ (Y ω) ∂Q| ≤ 16 * K * τ := by
  have hid := h (fun u => u) 0 contDiff_id (fun u => by simp [iteratedDeriv_fun_id])
  have hX : AEMeasurable X P := hid.1.aemeasurable
  have hY : AEMeasurable Y Q := hid.2.1.aemeasurable
  have key (t : ℝ) (ht : 0 < t) :
      |∫ ω, ψ (X ω) ∂P - ∫ ω, ψ (Y ω) ∂Q| ≤ 8 * K * t + 8 * K / t ^ 3 * τ ^ 4 := by
    set φ := (movingAverage t)^[4] ψ
    have hφ : ContDiff ℝ 4 φ := contDiff_iterate_movingAverage hψ.continuous 4
    have hC (u : ℝ) : |iteratedDeriv 4 φ u| ≤ 2 ^ 3 * K / t ^ 3 :=
      hψ.abs_iteratedDeriv_iterate_movingAverage_le ht (k := 3) (m := 4) (by norm_num) u
    have hM (u : ℝ) : |ψ u - φ u| ≤ 4 * K * t := by
      rw [abs_sub_comm]
      exact_mod_cast hψ.abs_iterate_movingAverage_sub_le ht 4 u
    obtain ⟨hφX, hφY, hXY⟩ := h φ _ hφ hC
    have hX' := (integrable_and_abs_integral_sub_le hX hφ.continuous hψ.continuous hM hφX).2
    have hY' := (integrable_and_abs_integral_sub_le hY hφ.continuous hψ.continuous hM hφY).2
    calc |∫ ω, ψ (X ω) ∂P - ∫ ω, ψ (Y ω) ∂Q|
        = |(∫ ω, ψ (X ω) ∂P - ∫ ω, φ (X ω) ∂P) + (∫ ω, φ (X ω) ∂P - ∫ ω, φ (Y ω) ∂Q) -
            (∫ ω, ψ (Y ω) ∂Q - ∫ ω, φ (Y ω) ∂Q)| := by congr 1; ring
      _ ≤ |∫ ω, ψ (X ω) ∂P - ∫ ω, φ (X ω) ∂P| + |∫ ω, φ (X ω) ∂P - ∫ ω, φ (Y ω) ∂Q| +
            |∫ ω, ψ (Y ω) ∂Q - ∫ ω, φ (Y ω) ∂Q| :=
          (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ 4 * K * t + 2 ^ 3 * K / t ^ 3 * τ ^ 4 + 4 * K * t := by gcongr
      _ = 8 * K * t + 8 * K / t ^ 3 * τ ^ 4 := by ring
  rcases hτ.eq_or_lt with rfl | hτ
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have ht : 0 < δ / (8 * K + 1) := by positivity
    refine (key _ ht).trans ?_
    rw [zero_pow (by norm_num), mul_zero, add_zero, mul_zero, zero_add, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith [K.2]
  · refine (key τ hτ).trans_eq ?_
    field_simp
    ring

/-! ### Corollary 11.68 -/

/-- `k 9ᵏ ≤ 16ᵏ`, so that `(k 9ᵏ)^(1/4) ≤ 2ᵏ`. -/
private theorem mul_nine_pow_le (k : ℕ) : k * 9 ^ k ≤ 16 ^ k := by
  rcases k with _ | _ | k
  · simp
  · norm_num
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ 9, pow_succ 16]
    have h9 : 0 ≤ 9 ^ (k + 2) := Nat.zero_le _
    nlinarith

/-- The arithmetic of Corollary 11.68: `k 9ᵏ ε / 12 ≤ (9/16 · 2ᵏ · ε^(1/4))⁴`. -/
private theorem mul_nine_pow_mul_div_le (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    k * 9 ^ k * ε / 12 ≤ (9 / 16 * 2 ^ k * ε ^ (1 / 4 : ℝ)) ^ 4 := by
  have hk : (k : ℝ) * 9 ^ k ≤ 16 ^ k := by exact_mod_cast mul_nine_pow_le k
  have he : (ε ^ (1 / 4 : ℝ)) ^ 4 = ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε]
    norm_num
  rw [mul_pow, mul_pow, he, ← pow_mul, mul_comm k 4, pow_mul]
  have h16 : (0 : ℝ) ≤ 16 ^ k * ε := by positivity
  norm_num
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (μ ν : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]

/-- **Corollary 11.68** [O'Donnell, Corollary 11.68][ODonnell2014]: in the setting of the Basic
Invariance Principle `abs_integral_comp_multilinearEval_sub_le`, if moreover
`Var[F] = ∑_{S ≠ ∅} F̂(S) ^ 2 ≤ 1` and `Inf_t[F] ≤ ε` for all `t`, then for every `K`-Lipschitz
`ψ : ℝ → ℝ`, `|E[ψ(F(x))] - E[ψ(F(y))]| ≤ 9 K · 2ᵏ · ε^(1/4)`. -/
theorem abs_integral_comp_multilinearEval_sub_le_of_lipschitzWith
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) (hvar : ∑ S with S ≠ ∅, c S ^ 2 ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ t, multilinearInfluence c t ≤ ε) {ψ : ℝ → ℝ} {K : ℝ≥0}
    (hψ : LipschitzWith K ψ) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval c z) ∂Measure.pi ν| ≤
      9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ) := by
  refine (abs_integral_comp_sub_le_of_lipschitzWith (X := multilinearEval c)
    (Y := multilinearEval c) (τ := 9 / 16 * 2 ^ k * ε ^ (1 / 4 : ℝ)) (by positivity)
    (fun φ C hφ hC => ⟨integrable_comp_multilinearEval μ (fun i => (hμ i).memLp_four) c
      (n := 3) le_rfl hφ hC, integrable_comp_multilinearEval ν (fun i => (hν i).memLp_four) c
      (n := 3) le_rfl hφ hC, ?_⟩) hψ).trans_eq (by ring)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine (abs_integral_comp_multilinearEval_sub_le_of_influence_le μ ν hμ hν hc hvar hε0 hε hφ
    hC).trans ?_
  calc C / 12 * k * 9 ^ k * ε = C * (k * 9 ^ k * ε / 12) := by ring
    _ ≤ C * (9 / 16 * 2 ^ k * ε ^ (1 / 4 : ℝ)) ^ 4 := by
        gcongr
        exact mul_nine_pow_mul_div_le k hε0

/-! ### Lipschitz tests of nearby polynomials -/

omit [DecidableEq ι] in
/-- For variables whose laws satisfy Hypothesis 11.65 and `K`-Lipschitz `ψ`,
`|E[ψ(F(z))] - E[ψ(G(z))]| ≤ K ‖F - G‖₂ = K √(∑ S, (F̂(S) - Ĝ(S))²)`, by Cauchy–Schwarz and the
orthonormality of monomials [O'Donnell, Remark 11.64][ODonnell2014]. This is the tail estimate
in the proof of [O'Donnell, Corollary 11.69][ODonnell2014]. -/
theorem abs_integral_comp_multilinearEval_sub_le_sqrt (hμ : ∀ i, HasInvarianceMoments (μ i))
    {ψ : ℝ → ℝ} {K : ℝ≥0} (hψ : LipschitzWith K ψ) (c d : Finset ι → ℝ) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval d z) ∂Measure.pi μ| ≤
      K * √(∑ S, (c S - d S) ^ 2) := by
  have hL (e : Finset ι → ℝ) : MemLp (multilinearEval e) 2 (Measure.pi μ) := by
    have h := memLp_multilinearEval μ (p := 2) two_ne_zero
      (fun i => (hμ i).memLp_four.mono_exponent (by norm_num)) e
    exact_mod_cast h
  have hD (z : ι → ℝ) : multilinearEval c z - multilinearEval d z =
      multilinearEval (c - d) z := by
    simp only [multilinearEval_def, Pi.sub_apply, sub_mul, sum_sub_distrib]
  refine (hψ.abs_integral_comp_sub_le_sqrt (hL c) (hL d)).trans_eq ?_
  simp_rw [hD]
  rw [integral_multilinearEval_sq_of_hasInvarianceMoments μ hμ]
  simp

end ProbabilityTheory
