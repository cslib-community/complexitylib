/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Multilinear.Basic
public import CslibFrontier.Foundations.Probability.Gaussian.Moments
public import CslibFrontier.Foundations.Probability.Reasonable
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate

/-!
# The Bonami Lemma for independent random variables

A real random variable `z` satisfies *Hypothesis 11.65* of [O'Donnell][ODonnell2014] when
`E[z] = 0`, `E[z²] = 1`, `E[z³] = 0` and `E[z⁴] ≤ 9`, the last condition saying that `z` is
`9`-reasonable in the sense of Definition 9.1 (`HasInvarianceMoments`). Uniform `±1` bits and
standard Gaussians are the main examples (`hasInvarianceMoments_gaussianReal`; the bits are in
`CslibFrontier.Foundations.BooleanAnalysis.Invariance`).

**The Bonami Lemma** [O'Donnell, Corollary 9.6][ODonnell2014]: if `z₁, …, zₙ` are independent,
not necessarily identically distributed, each `B`-reasonable (`IsReasonable`) with
`E[zᵢ] = E[zᵢ³] = 0`, and `F` is a formal multilinear polynomial of degree at most `k`, then `F(z)`
is `max(B, 9) ^ k`-reasonable, `E[F(z)⁴] ≤ max(B, 9) ^ k E[F(z)²] ^ 2`
(`isReasonable_multilinearEval`). The second moments `E[zᵢ²]` are not normalized. Under
Hypothesis 11.65 this reads `E[F(z)⁴] ≤ 9 ^ k (∑_S F̂(S) ^ 2) ^ 2`
(`integral_multilinearEval_pow_four_le`). The proof is the book's induction (Exercise 9.4): write
`F = E_i F + z i · D_i F`, integrate out `z i` to get
`E[F⁴] = E[(E_i F)⁴] + 6 E[zᵢ²] E[(E_i F)² (D_i F)²] + E[zᵢ⁴] E[(D_i F)⁴]`
(`integral_add_mul_pow_four`), and bound the middle term by Cauchy–Schwarz
(`MeasureTheory.sq_integral_mul_le`). For uniform `±1` bits, the Boolean-cube form of the Bonami
Lemma (`E[f⁴] ≤ 9 ^ k E[f²] ^ 2` for `f` of degree at most `k`) is
`Cslib.BitString.expect_pow_four_le`; the bridge
`CslibFrontier.Foundations.BooleanAnalysis.Invariance` identifies the two settings.

## Main definitions

* `ProbabilityTheory.HasInvarianceMoments`: Hypothesis 11.65.

## Main results

* `ProbabilityTheory.hasInvarianceMoments_gaussianReal`: standard Gaussians satisfy it.
* `ProbabilityTheory.HasInvarianceMoments.isReasonable`,
  `ProbabilityTheory.hasInvarianceMoments_iff`: Hypothesis 11.65 is `9`-reasonableness together
  with the moments `E[z] = 0`, `E[z²] = 1` and `E[z³] = 0`.
* `ProbabilityTheory.integral_multilinearEval_sq_of_hasInvarianceMoments`: `E[F(z)²] = ∑_S F̂(S)²`.
* `ProbabilityTheory.isReasonable_multilinearEval`: the Bonami Lemma for `B`-reasonable variables.
* `ProbabilityTheory.integral_multilinearEval_pow_four_le`: the Bonami Lemma under
  Hypothesis 11.65.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Sections 9.1 and 11.6.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

/-- **Hypothesis 11.65** of [O'Donnell][ODonnell2014]: the real random variable with law `μ` has
`E[z] = 0`, `E[z²] = 1`, `E[z³] = 0`, and is `9`-reasonable, `E[z⁴] ≤ 9` (Definition 9.1). The
fourth moment is assumed finite. -/
structure HasInvarianceMoments (μ : Measure ℝ) : Prop where
  memLp_four : MemLp id 4 μ
  integral_id : ∫ z, z ∂μ = 0
  integral_sq : ∫ z, z ^ 2 ∂μ = 1
  integral_pow_three : ∫ z, z ^ 3 ∂μ = 0
  integral_pow_four_le : ∫ z, z ^ 4 ∂μ ≤ 9

/-- Standard Gaussians satisfy Hypothesis 11.65, with `E[z⁴] = 3`. -/
theorem hasInvarianceMoments_gaussianReal : HasInvarianceMoments (gaussianReal 0 1) where
  memLp_four := by exact_mod_cast memLp_id_gaussianReal (μ := 0) (v := 1) 4
  integral_id := integral_id_gaussianReal
  integral_sq := integral_sq_gaussianReal
  integral_pow_three := integral_pow_three_gaussianReal
  integral_pow_four_le := by rw [integral_pow_four_gaussianReal]; norm_num

/-- A variable satisfying Hypothesis 11.65 is `9`-reasonable. -/
theorem HasInvarianceMoments.isReasonable {m : Measure ℝ} (hm : HasInvarianceMoments m) :
    IsReasonable 9 id m :=
  ⟨hm.memLp_four, by simpa [hm.integral_sq] using hm.integral_pow_four_le⟩

/-- **Hypothesis 11.65** [O'Donnell, Section 11.6][ODonnell2014] is `9`-reasonableness of a
variable with mean `0`, second moment `1` and third moment `0`. -/
theorem hasInvarianceMoments_iff {ν : Measure ℝ} :
    HasInvarianceMoments ν ↔ IsReasonable 9 id ν ∧ ∫ z, z ∂ν = 0 ∧ ∫ z, z ^ 2 ∂ν = 1 ∧
      ∫ z, z ^ 3 ∂ν = 0 := by
  refine ⟨fun h => ⟨h.isReasonable, h.integral_id, h.integral_sq, h.integral_pow_three⟩, ?_⟩
  rintro ⟨⟨h4, hle⟩, h1, h2, h3⟩
  exact ⟨h4, h1, h2, h3, by simpa [h2] using hle⟩

variable {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)]

/-- **Orthonormality of monomials** under Hypothesis 11.65: `E[F(z)²] = ∑_S F̂(S) ^ 2`
[O'Donnell, Remark 11.64][ODonnell2014]. -/
theorem integral_multilinearEval_sq_of_hasInvarianceMoments
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (c : Finset ι → ℝ) :
    ∫ z, multilinearEval c z ^ 2 ∂Measure.pi μ = ∑ S, c S ^ 2 :=
  integral_multilinearEval_sq μ (fun i => (hμ i).memLp_four) (fun i => (hμ i).integral_id)
    (fun i => (hμ i).integral_sq) c

/-- The real-number step of the Bonami induction. Write `a₂ = E[e²]` and `X = E[e⁴]` for
`e = E_a F`, `b₂ = E[d²]` and `Y = E[d⁴]` for `d = D_a F`, `Z = E[e² d²]`, and `s₂ = E[z²]` and
`m₄ = E[z⁴]` for the variable `z` split off. From the induction hypotheses
`X ≤ C ^ (k + 1) a₂²` and `Y ≤ C ^ k b₂²`, Cauchy–Schwarz `Z² ≤ X Y` and `m₄ ≤ C s₂²` with
`9 ≤ C`, the fourth moment `X + 6 s₂ Z + m₄ Y` of `e + z d` is at most `C ^ (k + 1)` times its
squared second moment `(a₂ + s₂ b₂)²`. -/
private theorem bonami_step_le {C a₂ b₂ X Y Z s₂ m₄ : ℝ} {k : ℕ} (hC : 9 ≤ C) (ha₂ : 0 ≤ a₂)
    (hb₂ : 0 ≤ b₂) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hs₂ : 0 ≤ s₂) (hX : X ≤ C ^ (k + 1) * a₂ ^ 2)
    (hYk : Y ≤ C ^ k * b₂ ^ 2) (hCS : Z ^ 2 ≤ X * Y) (hm : m₄ ≤ C * s₂ ^ 2) :
    X + 6 * Z * s₂ + Y * m₄ ≤ C ^ (k + 1) * (a₂ + b₂ * s₂) ^ 2 := by
  have hCk : 0 ≤ C ^ k := pow_nonneg (by linarith) k
  -- `3 Z ≤ C ^ (k + 1) a₂ b₂`, using `9 ≤ C`
  have hZ3 : 3 * Z ≤ C ^ (k + 1) * a₂ * b₂ := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    calc (3 * Z) ^ 2 = 9 * Z ^ 2 := by ring
      _ ≤ 9 * ((C ^ (k + 1) * a₂ ^ 2) * (C ^ k * b₂ ^ 2)) := by gcongr; exact hCS.trans (by gcongr)
      _ ≤ C * ((C ^ (k + 1) * a₂ ^ 2) * (C ^ k * b₂ ^ 2)) := by gcongr
      _ = (C ^ (k + 1) * a₂ * b₂) ^ 2 := by ring
  have hYm : Y * m₄ ≤ (C ^ k * b₂ ^ 2) * (C * s₂ ^ 2) :=
    (mul_le_mul_of_nonneg_left hm hY).trans
      (mul_le_mul_of_nonneg_right hYk (mul_nonneg (by linarith) (sq_nonneg s₂)))
  have := mul_le_mul_of_nonneg_left hZ3 (by positivity : (0 : ℝ) ≤ 2 * s₂)
  calc X + 6 * Z * s₂ + Y * m₄
      ≤ C ^ (k + 1) * a₂ ^ 2 + 2 * s₂ * (C ^ (k + 1) * a₂ * b₂) +
          (C ^ k * b₂ ^ 2) * (C * s₂ ^ 2) := by linarith
    _ = C ^ (k + 1) * (a₂ + b₂ * s₂) ^ 2 := by ring

/-- The Bonami induction on the coordinates in `T` that `F` mentions, for independent
`C`-reasonable variables with `E[z] = E[z³] = 0` and `9 ≤ C`. -/
private theorem integral_multilinearEval_pow_four_le_aux {C : ℝ} (hC : 9 ≤ C)
    (hμ : ∀ i, IsReasonable C id (μ i)) (h1 : ∀ i, ∫ z, z ∂μ i = 0)
    (h3 : ∀ i, ∫ z, z ^ 3 ∂μ i = 0) (T : Finset ι) :
    ∀ (k : ℕ) (c : Finset ι → ℝ), (∀ S, ¬ S ⊆ T → c S = 0) → (∀ S, k < #S → c S = 0) →
      ∫ z, multilinearEval c z ^ 4 ∂Measure.pi μ ≤
        C ^ k * (∫ z, multilinearEval c z ^ 2 ∂Measure.pi μ) ^ 2 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro k c hc _
    simp only [multilinearEval_of_forall_nonempty fun S hS => hc S (by
      simpa [subset_empty, nonempty_iff_ne_empty] using hS), integral_const, probReal_univ,
      smul_eq_mul, one_mul]
    have : (1 : ℝ) ≤ C ^ k := one_le_pow₀ (by linarith)
    nlinarith [sq_nonneg (c ∅ ^ 2)]
  | insert a T ha ih =>
    intro k c hc hk
    have h4 (i : ι) : MemLp id 4 (μ i) := (hμ i).memLp
    have hint (c' : Finset ι → ℝ) {j : ℕ} (hj : j ≤ 4) :=
      integrable_multilinearEval_pow μ h4 c' hj
    set P := Measure.pi μ
    set E := multilinearEval (multilinearExpectCoeff c a)
    set D := multilinearEval (multilinearDerivCoeff c a)
    set σ := ∫ z, z ^ 2 ∂μ a
    set m₄ := ∫ z, z ^ 4 ∂μ a
    have hE4 : Integrable (fun v => E v ^ 4) P := hint _ le_rfl
    have hD4 : Integrable (fun v => D v ^ 4) P := hint _ le_rfl
    have hED : Integrable (fun v => E v ^ 2 * D v ^ 2) P := by
      refine ((hE4.add hD4).div_const 2).mono'
        ((((continuous_multilinearEval _).pow 2).mul
          ((continuous_multilinearEval _).pow 2)).aestronglyMeasurable) (ae_of_all _ fun v => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
      nlinarith [sq_nonneg (E v ^ 2 - D v ^ 2)]
    rw [← integral_integral_update μ (hint c (j := 4) le_rfl) a,
      ← integral_integral_update μ (hint c (j := 2) (by norm_num)) a]
    simp_rw [multilinearEval_update c a, integral_add_mul_pow_four (h4 a) (h1 a) (h3 a),
      integral_add_mul_sq ((h4 a).mono_exponent (by norm_num)) (h1 a)]
    change ∫ v, E v ^ 4 + 6 * (E v ^ 2 * D v ^ 2) * σ + D v ^ 4 * m₄ ∂P ≤
      C ^ k * (∫ v, E v ^ 2 + D v ^ 2 * σ ∂P) ^ 2
    rw [integral_add (f := fun v => E v ^ 4 + 6 * (E v ^ 2 * D v ^ 2) * σ)
        (g := fun v => D v ^ 4 * m₄) (hE4.add ((hED.const_mul 6).mul_const σ))
        (hD4.mul_const m₄),
      integral_add (f := fun v => E v ^ 4) (g := fun v => 6 * (E v ^ 2 * D v ^ 2) * σ) hE4
        ((hED.const_mul 6).mul_const σ), integral_mul_const, integral_mul_const,
      integral_const_mul,
      integral_add (f := fun v => E v ^ 2) (g := fun v => D v ^ 2 * σ) (hint _ (by norm_num))
        ((hint _ (by norm_num)).mul_const σ), integral_mul_const]
    have hX := ih k _ (multilinearExpectCoeff_eq_zero_of_not_subset hc)
      (multilinearExpectCoeff_eq_zero_of_card_lt hk a)
    rcases k with _ | k
    · -- degree zero: `D_a F = 0`
      have hDz : D = 0 := funext fun v => by
        simp [D, multilinearDerivCoeff_eq_zero_of_degree_zero hk a]
      simpa [hDz] using hX
    · have hCS := sq_integral_mul_le (f := fun v => E v ^ 2) (g := fun v => D v ^ 2) (P := P)
        (by simpa only [← pow_mul] using hE4) (by simpa only [← pow_mul] using hD4) hED
      simp only [← pow_mul] at hCS
      exact bonami_step_le hC (integral_nonneg fun _ => sq_nonneg _)
        (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => by positivity)
        (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => sq_nonneg _) hX
        (ih k _ (multilinearDerivCoeff_eq_zero_of_not_subset hc)
          (multilinearDerivCoeff_eq_zero_of_card_lt hk a)) hCS
        (by simpa using (hμ a).integral_pow_four_le)

/-- **The Bonami Lemma for reasonable variables** [O'Donnell, Corollary 9.6][ODonnell2014]: if
`z₁, …, zₙ` are independent, each `B`-reasonable with `E[zᵢ] = E[zᵢ³] = 0`, and `F` has degree at
most `k`, then `F(z)` is `max(B, 9) ^ k`-reasonable. The variables need not be identically
distributed, and their second moments are not normalized. -/
theorem isReasonable_multilinearEval {B : ℝ} (hμ : ∀ i, IsReasonable B id (μ i))
    (h1 : ∀ i, ∫ z, z ∂μ i = 0) (h3 : ∀ i, ∫ z, z ^ 3 ∂μ i = 0) {k : ℕ} {c : Finset ι → ℝ}
    (hc : ∀ S, k < #S → c S = 0) :
    IsReasonable (max B 9 ^ k) (multilinearEval c) (Measure.pi μ) := by
  classical
  have h4 : MemLp (multilinearEval c) (4 : ℕ) (Measure.pi μ) :=
    memLp_multilinearEval μ (by norm_num) (fun i => by exact_mod_cast (hμ i).memLp) c
  refine ⟨by exact_mod_cast h4, ?_⟩
  exact integral_multilinearEval_pow_four_le_aux μ (le_max_right B 9)
    (fun i => (hμ i).mono (le_max_left B 9)) h1 h3 univ k c
    (fun S hS => absurd (subset_univ S) hS) hc

/-- **The Bonami Lemma** for independent variables satisfying Hypothesis 11.65 (the case
`B = 9`, variance `1`, of [O'Donnell, Corollary 9.6][ODonnell2014],
`isReasonable_multilinearEval`): if `F` has degree at most `k`, then
`E[F(z)⁴] ≤ 9 ^ k (∑_S F̂(S) ^ 2) ^ 2`, where `∑_S F̂(S) ^ 2 = E[F(z)²]`
(`integral_multilinearEval_sq_of_hasInvarianceMoments`). -/
theorem integral_multilinearEval_pow_four_le (hμ : ∀ i, HasInvarianceMoments (μ i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) :
    ∫ z, multilinearEval c z ^ 4 ∂Measure.pi μ ≤ 9 ^ k * (∑ S, c S ^ 2) ^ 2 := by
  rw [← integral_multilinearEval_sq_of_hasInvarianceMoments μ hμ]
  simpa only [max_self, id] using (isReasonable_multilinearEval μ (fun i => (hμ i).isReasonable)
    (fun i => (hμ i).integral_id) (fun i => (hμ i).integral_pow_three) hc).integral_pow_four_le

end ProbabilityTheory
