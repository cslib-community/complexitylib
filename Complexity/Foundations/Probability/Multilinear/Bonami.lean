/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.Multilinear.Basic
public import Complexity.Foundations.Probability.Gaussian.Moments
import Complexity.Foundations.MeasureTheory.Integral.CauchySchwarz
import Complexity.Foundations.MeasureTheory.Integral.PiUpdate

/-!
# The Bonami Lemma for independent random variables

A real random variable `z` satisfies *Hypothesis 11.65* of [O'Donnell][ODonnell2014] when
`E[z] = 0`, `E[z²] = 1`, `E[z³] = 0` and `E[z⁴] ≤ 9`, the last condition saying that `z` is
`9`-reasonable in the sense of Definition 9.1 (`HasInvarianceMoments`). Uniform `±1` bits and
standard Gaussians are the main examples (`hasInvarianceMoments_gaussianReal`; the bits are in
`Complexity.Foundations.BooleanAnalysis.Invariance`).

**The Bonami Lemma** for such variables: if `z₁, …, zₙ` are independent and satisfy Hypothesis
11.65, and `F` is a formal multilinear polynomial of degree at most `k`, then
`E[F(z)⁴] ≤ 9 ^ k (∑_S F̂(S) ^ 2) ^ 2 = 9 ^ k E[F(z)²] ^ 2`
(`integral_multilinearEval_pow_four_le`). This is the case `B ≤ 9`, variance `1`, of
[O'Donnell, Corollary 9.6][ODonnell2014] (Exercise 9.4), which allows any `B`-reasonable variables
with `E[zᵢ] = E[zᵢ³] = 0` and concludes `max(B, 9) ^ k`-reasonableness. The proof is the book's
induction for the Bonami Lemma: write `F = E_i F + z i · D_i F`, integrate out `z i` to get
`E[F⁴] = E[(E_i F)⁴] + 6 E[(E_i F)² (D_i F)²] + E[zᵢ⁴] E[(D_i F)⁴]`, and bound the middle term by
Cauchy–Schwarz (`MeasureTheory.sq_integral_mul_le`). For uniform `±1` bits, the Boolean-cube form
of the Bonami Lemma (`E[f⁴] ≤ 9 ^ k E[f²] ^ 2` for `f` of degree at most `k`) is
`Cslib.BitString.expect_pow_four_le`; the bridge
`Complexity.Foundations.BooleanAnalysis.Invariance` identifies the two settings.

## Main definitions

* `ProbabilityTheory.HasInvarianceMoments`: Hypothesis 11.65.

## Main results

* `ProbabilityTheory.hasInvarianceMoments_gaussianReal`: standard Gaussians satisfy it.
* `ProbabilityTheory.integral_multilinearEval_sq_of_hasInvarianceMoments`: `E[F(z)²] = ∑_S F̂(S)²`.
* `ProbabilityTheory.integral_multilinearEval_pow_four_le`: the Bonami Lemma.

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

namespace HasInvarianceMoments

variable {m : Measure ℝ} [IsProbabilityMeasure m]

/-- Expanding `E[(e + z d) ^ n]` by the binomial theorem. -/
private theorem integral_add_mul_pow {n : ℕ} (hm : MemLp id n m) (e d : ℝ) :
    ∫ z, (e + z * d) ^ n ∂m =
      ∑ j ∈ range (n + 1), (n.choose j : ℝ) * e ^ (n - j) * d ^ j * ∫ z, z ^ j ∂m := by
  have hint (j : ℕ) (hj : j ∈ range (n + 1)) :
      Integrable (fun z => (z * d) ^ j * e ^ (n - j) * (n.choose j : ℝ)) m := by
    refine ((integrable_pow_of_memLp hm (j := j) (Nat.lt_succ_iff.1 (mem_range.1 hj))).mul_const
      (d ^ j * e ^ (n - j) * (n.choose j : ℝ))).congr (ae_of_all _ fun z => ?_)
    simp only [mul_pow]; ring
  simp_rw [add_comm e, add_pow]
  rw [integral_finsetSum _ hint]
  refine sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]; congr 1; funext z; simp only [mul_pow]; ring

/-- `E[(e + z d)²] = e² + d²`. -/
theorem integral_add_mul_sq (hm : HasInvarianceMoments m) (e d : ℝ) :
    ∫ z, (e + z * d) ^ 2 ∂m = e ^ 2 + d ^ 2 :=
  ProbabilityTheory.integral_add_mul_sq (hm.memLp_four.mono_exponent (by norm_num))
    hm.integral_id hm.integral_sq e d

/-- `E[(e + z d)⁴] = e⁴ + 6 e² d² + E[z⁴] d⁴`. -/
theorem integral_add_mul_pow_four (hm : HasInvarianceMoments m) (e d : ℝ) :
    ∫ z, (e + z * d) ^ 4 ∂m = e ^ 4 + 6 * (e ^ 2 * d ^ 2) + d ^ 4 * ∫ z, z ^ 4 ∂m := by
  rw [integral_add_mul_pow (by exact_mod_cast hm.memLp_four) e d]
  simp [sum_range_succ, hm.integral_id, hm.integral_sq, hm.integral_pow_three, Nat.choose]
  ring

end HasInvarianceMoments

variable {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)]

/-- **Orthonormality of monomials** under Hypothesis 11.65: `E[F(z)²] = ∑_S F̂(S) ^ 2`
[O'Donnell, Remark 11.64][ODonnell2014]. -/
theorem integral_multilinearEval_sq_of_hasInvarianceMoments
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (c : Finset ι → ℝ) :
    ∫ z, multilinearEval c z ^ 2 ∂Measure.pi μ = ∑ S, c S ^ 2 :=
  integral_multilinearEval_sq μ (fun i => (hμ i).memLp_four) (fun i => (hμ i).integral_id)
    (fun i => (hμ i).integral_sq) c

private theorem integral_multilinearEval_pow_four_le_aux (hμ : ∀ i, HasInvarianceMoments (μ i))
    (T : Finset ι) : ∀ (k : ℕ) (c : Finset ι → ℝ), (∀ S, ¬ S ⊆ T → c S = 0) →
      (∀ S, k < #S → c S = 0) →
      ∫ z, multilinearEval c z ^ 4 ∂Measure.pi μ ≤
        9 ^ k * (∫ z, multilinearEval c z ^ 2 ∂Measure.pi μ) ^ 2 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro k c hc _
    simp only [multilinearEval_of_forall_nonempty fun S hS => hc S (by
      simpa [subset_empty, nonempty_iff_ne_empty] using hS), integral_const, probReal_univ,
      smul_eq_mul, one_mul]
    have : (1 : ℝ) ≤ 9 ^ k := one_le_pow₀ (by norm_num)
    nlinarith [sq_nonneg (c ∅ ^ 2)]
  | insert a T ha ih =>
    intro k c hc hk
    have hint (c' : Finset ι → ℝ) {j : ℕ} (hj : j ≤ 4) :=
      integrable_multilinearEval_pow μ (fun i => (hμ i).memLp_four) c' hj
    set P := Measure.pi μ
    set E := multilinearEval (multilinearExpectCoeff c a)
    set D := multilinearEval (multilinearDerivCoeff c a)
    set m4 := ∫ z, z ^ 4 ∂μ a
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
    simp_rw [multilinearEval_update c a, (hμ a).integral_add_mul_pow_four,
      (hμ a).integral_add_mul_sq]
    change ∫ v, E v ^ 4 + 6 * (E v ^ 2 * D v ^ 2) + D v ^ 4 * m4 ∂P ≤
      9 ^ k * (∫ v, E v ^ 2 + D v ^ 2 ∂P) ^ 2
    rw [integral_add (f := fun v => E v ^ 4 + 6 * (E v ^ 2 * D v ^ 2))
        (g := fun v => D v ^ 4 * m4) (hE4.add (hED.const_mul 6)) (hD4.mul_const m4),
      integral_add (f := fun v => E v ^ 4) (g := fun v => 6 * (E v ^ 2 * D v ^ 2)) hE4
        (hED.const_mul 6), integral_mul_const, integral_const_mul,
      integral_add (f := fun v => E v ^ 2) (g := fun v => D v ^ 2) (hint _ (by norm_num))
        (hint _ (by norm_num))]
    set A := ∫ v, E v ^ 2 ∂P
    set B := ∫ v, D v ^ 2 ∂P
    set X := ∫ v, E v ^ 4 ∂P
    set Y := ∫ v, D v ^ 4 ∂P
    set Z := ∫ v, E v ^ 2 * D v ^ 2 ∂P
    have hX : X ≤ 9 ^ k * A ^ 2 := ih k _ (multilinearExpectCoeff_eq_zero_of_not_subset hc)
      (multilinearExpectCoeff_eq_zero_of_card_lt hk a)
    have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
    have hB : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
    have hY0 : 0 ≤ Y := integral_nonneg fun _ => by positivity
    have hZ0 : 0 ≤ Z := integral_nonneg fun _ => by positivity
    have hm4 : m4 ≤ 9 := (hμ a).integral_pow_four_le
    rcases k with _ | k
    · -- degree zero: `D_a F = 0`
      have hDz : D = 0 := funext fun v => by
        simp [D, multilinearDerivCoeff_eq_zero_of_degree_zero hk a]
      have hY : Y = 0 := by simp [Y, hDz]
      have hZ : Z = 0 := by simp [Z, hDz]
      have hB' : B = 0 := by simp [B, hDz]
      rw [hY, hZ, hB']
      simpa using hX
    · have hY : Y ≤ 9 ^ k * B ^ 2 := ih k _ (multilinearDerivCoeff_eq_zero_of_not_subset hc)
        (multilinearDerivCoeff_eq_zero_of_card_lt hk a)
      have hCS : Z ^ 2 ≤ X * Y := by
        have h := sq_integral_mul_le (f := fun v => E v ^ 2) (g := fun v => D v ^ 2)
          (P := P) (by simpa only [← pow_mul] using hE4) (by simpa only [← pow_mul] using hD4) hED
        simpa only [← pow_mul] using h
      have hZ : Z ≤ 3 * 9 ^ k * A * B := by
        refine (pow_le_pow_iff_left₀ hZ0 (by positivity) two_ne_zero).1 ?_
        calc Z ^ 2 ≤ X * Y := hCS
          _ ≤ (9 ^ (k + 1) * A ^ 2) * (9 ^ k * B ^ 2) :=
            mul_le_mul hX hY hY0 (by positivity)
          _ = (3 * 9 ^ k * A * B) ^ 2 := by ring
      have hYm : Y * m4 ≤ Y * 9 := mul_le_mul_of_nonneg_left hm4 hY0
      calc X + 6 * Z + Y * m4
          ≤ 9 ^ (k + 1) * A ^ 2 + 6 * (3 * 9 ^ k * A * B) + 9 * (9 ^ k * B ^ 2) := by nlinarith
        _ = 9 ^ (k + 1) * (A + B) ^ 2 := by ring

/-- **The Bonami Lemma** for independent variables satisfying Hypothesis 11.65 (the case
`B ≤ 9`, variance `1`, of [O'Donnell, Corollary 9.6][ODonnell2014]): if `F` has degree at most
`k`, then `E[F(z)⁴] ≤ 9 ^ k (∑_S F̂(S) ^ 2) ^ 2`, where `∑_S F̂(S) ^ 2 = E[F(z)²]`
(`integral_multilinearEval_sq_of_hasInvarianceMoments`). -/
theorem integral_multilinearEval_pow_four_le (hμ : ∀ i, HasInvarianceMoments (μ i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) :
    ∫ z, multilinearEval c z ^ 4 ∂Measure.pi μ ≤ 9 ^ k * (∑ S, c S ^ 2) ^ 2 := by
  classical
  rw [← integral_multilinearEval_sq_of_hasInvarianceMoments μ hμ]
  exact integral_multilinearEval_pow_four_le_aux μ hμ univ k c
    (fun S hS => absurd (subset_univ S) hS) hc

end ProbabilityTheory
