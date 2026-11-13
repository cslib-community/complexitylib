/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
import CslibFrontier.Foundations.Combinatorics.BinomialTail
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Binary relative entropy

The binary relative entropy `binaryKL q p = q log (q / p) + (1 - q) log ((1 - q) / (1 - p))` of
Bernoulli parameters `q, p ∈ [0, 1]`, in nats, written with Mathlib's `klFun` as
`p klFun (q / p) + (1 - p) klFun ((1 - q) / (1 - p))`.

At `p ∈ {0, 1}` with `q ≠ p` the true divergence is infinite; `binaryKL` takes finite junk values
there, so Jensen's inequality is stated for pairs with `q = p` wherever `p ∈ {0, 1}`.

## Main definitions

* `Cslib.Probability.binaryKL`: the binary relative entropy.

## Main results

* `Cslib.Probability.binaryKL_nonneg`, `Cslib.Probability.binaryKL_self`: nonnegativity and
  vanishing on the diagonal.
* `Cslib.Probability.binaryKL_eq_mul_log`: the closed form for `p ∈ (0, 1)`.
* `Cslib.Probability.convexOn_binaryKL`, `Cslib.Probability.convexOn_exp_mul_binaryKL`: for fixed
  `p ∈ [0, 1]`, `binaryKL · p` and `exp (t binaryKL · p)` with `t ≥ 0` are convex on `[0, 1]`.
* `Cslib.Probability.choose_mul_pow_mul_exp_binaryKL_le_one`: a binomial probability is at most
  `exp (-m binaryKL (k / m) p)`.
* `Cslib.Probability.mul_klFun_integral_div_integral_le`: the log-sum inequality in integral form.
* `Cslib.Probability.binaryKL_integral_le_integral`: Jensen's inequality for `binaryKL`.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006]
-/

public section

namespace Cslib.Probability

open InformationTheory Set

/-- The binary relative entropy `q log (q / p) + (1 - q) log ((1 - q) / (1 - p))` of Bernoulli
parameters, in nats. -/
noncomputable def binaryKL (q p : ℝ) : ℝ :=
  p * klFun (q / p) + (1 - p) * klFun ((1 - q) / (1 - p))

theorem binaryKL_def (q p : ℝ) :
    binaryKL q p = p * klFun (q / p) + (1 - p) * klFun ((1 - q) / (1 - p)) := by
  rw [binaryKL]

theorem binaryKL_nonneg {q p : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hp : p ∈ Icc (0 : ℝ) 1) :
    0 ≤ binaryKL q p :=
  add_nonneg (mul_nonneg hp.1 (klFun_nonneg (div_nonneg hq.1 hp.1)))
    (mul_nonneg (sub_nonneg.2 hp.2)
      (klFun_nonneg (div_nonneg (sub_nonneg.2 hq.2) (sub_nonneg.2 hp.2))))

@[simp]
theorem binaryKL_self (p : ℝ) : binaryKL p p = 0 := by
  rw [binaryKL_def]
  rcases eq_or_ne p 0 with rfl | hp
  · simp [klFun_one]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [klFun_one]
  rw [div_self hp, div_self (sub_ne_zero.2 (Ne.symm hp1)), klFun_one]
  ring

/-- For fixed `p`, `binaryKL · p` is continuous. -/
@[fun_prop]
theorem continuous_binaryKL_left (p : ℝ) : Continuous fun q => binaryKL q p := by
  simp only [binaryKL_def]
  fun_prop

/-- For `p ∈ (0, 1)`, `binaryKL q p = q log (q / p) + (1 - q) log ((1 - q) / (1 - p))`. -/
theorem binaryKL_eq_mul_log {q p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    binaryKL q p = q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) := by
  have h1 : (1 - p) ≠ 0 := (sub_pos.2 hp1).ne'
  rw [binaryKL_def, klFun_apply, klFun_apply]
  set L1 := Real.log (q / p)
  set L2 := Real.log ((1 - q) / (1 - p))
  field_simp
  ring

private theorem exp_mul_log_eq_pow {y : ℝ} {n : ℕ} (h : 0 < y ∨ n = 0) :
    Real.exp (n * Real.log y) = y ^ n := by
  rcases h with h | rfl
  · rw [← Real.log_pow, Real.exp_log (pow_pos h n)]
  · simp

/-- A binomial probability is at most `exp (-m binaryKL (k / m) p)`:
`C(m, k) p ^ k (1 - p) ^ (m - k) exp (m binaryKL (k / m) p) ≤ 1` for `p ∈ [0, 1]` and `k ≤ m`.
The left side is the probability of `k` successes in `m` trials of success probability `k / m`. -/
theorem choose_mul_pow_mul_exp_binaryKL_le_one {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) {m k : ℕ}
    (hk : k ≤ m) :
    (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * Real.exp (m * binaryKL (k / m) p) ≤ 1 := by
  rcases hp.1.eq_or_lt with rfl | hp0
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · simp [zero_pow hk0.ne']
  rcases hp.2.eq_or_lt with rfl | hp1
  · rcases hk.eq_or_lt with rfl | hkm
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp
      · rw [div_self (Nat.cast_ne_zero.2 hk0.ne'), binaryKL_self]
        simp
    · simp [zero_pow (Nat.sub_pos_of_lt hkm).ne']
  set q : ℝ := k / m with hq
  have hmq : (m : ℝ) * q = k := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Nat.le_zero.1 hk]
    · rw [hq, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hm.ne')]
  have hmq' : (m : ℝ) * (1 - q) = ((m - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk, mul_one_sub, hmq]
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hq]
    · rw [hq, div_le_one (Nat.cast_pos.2 hm)]; exact_mod_cast hk
  have hexp : Real.exp (m * binaryKL q p) = (q / p) ^ k * ((1 - q) / (1 - p)) ^ (m - k) := by
    rw [binaryKL_eq_mul_log hp0 hp1, mul_add, ← mul_assoc, ← mul_assoc, hmq, hmq',
      Real.exp_add, exp_mul_log_eq_pow, exp_mul_log_eq_pow]
    · rcases Nat.eq_zero_or_pos (m - k) with h | h
      · exact Or.inr h
      · refine Or.inl (div_pos ?_ (sub_pos.2 hp1))
        have : (0 : ℝ) < ((m - k : ℕ) : ℝ) := Nat.cast_pos.2 h
        rw [← hmq'] at this
        exact pos_of_mul_pos_right this (Nat.cast_nonneg m)
    · rcases Nat.eq_zero_or_pos k with h | h
      · exact Or.inr h
      · refine Or.inl (div_pos ?_ hp0)
        have : (0 : ℝ) < k := Nat.cast_pos.2 h
        rw [← hmq] at this
        exact pos_of_mul_pos_right this (Nat.cast_nonneg m)
  have hterm : (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * Real.exp (m * binaryKL q p) =
      m.choose k * q ^ k * (1 - q) ^ (m - k) := by
    rw [hexp]
    calc (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) *
          ((q / p) ^ k * ((1 - q) / (1 - p)) ^ (m - k))
        = (p * (q / p)) ^ k * ((1 - p) * ((1 - q) / (1 - p))) ^ (m - k) * m.choose k := by
          rw [mul_pow, mul_pow]; ring
      _ = m.choose k * q ^ k * (1 - q) ^ (m - k) := by
        rw [mul_div_cancel₀ _ hp0.ne', mul_div_cancel₀ _ (sub_pos.2 hp1).ne']; ring
  rw [hterm]
  calc (m.choose k : ℝ) * q ^ k * (1 - q) ^ (m - k)
      ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * q ^ j * (1 - q) ^ (m - j) :=
        Finset.single_le_sum (f := fun j => (m.choose j : ℝ) * q ^ j * (1 - q) ^ (m - j))
          (fun j _ => by have := sub_nonneg.2 hq1; positivity)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    _ = 1 := Cslib.sum_choose_mul_pow_eq_one m q

/-- `q ↦ c klFun (α + β q)` is convex on `[0, 1]` when `c ≥ 0` and `α + β q ≥ 0` there. -/
private theorem convexOn_mul_klFun_affine {c α β : ℝ} (hc : 0 ≤ c)
    (hpos : ∀ q ∈ Icc (0 : ℝ) 1, 0 ≤ α + β * q) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) fun q => c * klFun (α + β * q) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := convexOn_klFun.2 (mem_Ici.2 (hpos x hx)) (mem_Ici.2 (hpos y hy)) ha hb hab
  have hlin : α + β * (a • x + b • y) = a • (α + β * x) + b • (α + β * y) := by
    simp only [smul_eq_mul]
    linear_combination α * hab.symm
  dsimp only
  rw [hlin]
  calc c * klFun (a • (α + β * x) + b • (α + β * y))
      ≤ c * (a • klFun (α + β * x) + b • klFun (α + β * y)) := mul_le_mul_of_nonneg_left h hc
    _ = a • (c * klFun (α + β * x)) + b • (c * klFun (α + β * y)) := by
      simp only [smul_eq_mul]; ring

/-- For fixed `p ∈ [0, 1]`, the binary relative entropy is convex in its first argument. -/
theorem convexOn_binaryKL {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) fun q => binaryKL q p := by
  have h1 := convexOn_mul_klFun_affine (c := p) (α := 0) (β := p⁻¹) hp.1
    fun q hq => by simpa using mul_nonneg (inv_nonneg.2 hp.1) hq.1
  have h2 := convexOn_mul_klFun_affine (c := 1 - p) (α := (1 - p)⁻¹) (β := -(1 - p)⁻¹)
    (sub_nonneg.2 hp.2) fun q hq => by
      rw [neg_mul, ← sub_eq_add_neg, ← mul_one_sub]
      exact mul_nonneg (inv_nonneg.2 (sub_nonneg.2 hp.2)) (sub_nonneg.2 hq.2)
  refine (h1.add h2).congr fun q _ => ?_
  simp only [binaryKL_def, Pi.add_apply, zero_add, div_eq_inv_mul, neg_mul, ← sub_eq_add_neg,
    ← mul_one_sub]

/-- For fixed `p ∈ [0, 1]` and `t ≥ 0`, `exp (t binaryKL · p)` is convex on `[0, 1]`. -/
theorem convexOn_exp_mul_binaryKL {p t : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) fun q => Real.exp (t * binaryKL q p) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := (convexOn_binaryKL hp).2 hx hy ha hb hab
  calc Real.exp (t * binaryKL (a • x + b • y) p)
      ≤ Real.exp (a • (t * binaryKL x p) + b • (t * binaryKL y p)) := by
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left h ht
        simp only [smul_eq_mul] at this ⊢
        linarith
    _ ≤ a • Real.exp (t * binaryKL x p) + b • Real.exp (t * binaryKL y p) :=
        convexOn_exp.2 trivial trivial ha hb hab

section Jensen

open MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- The tangent line of `klFun` at `t > 0` lies below it on `[0, ∞)`. -/
private theorem klFun_add_log_mul_sub_le {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    klFun t + Real.log t * (x - t) ≤ klFun x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [klFun_apply, klFun_zero]
    linarith
  · have h := mul_nonneg ht.le (klFun_nonneg (div_nonneg hx.le ht.le))
    have he : t * klFun (x / t) = x * Real.log x - x * Real.log t + t - x := by
      rw [klFun_apply, Real.log_div hx.ne' ht.ne']
      field_simp
    rw [klFun_apply, klFun_apply]
    linarith

/-- **The log-sum inequality** [CoverThomas2006, Theorem 2.7.1] in integral form: Jensen for the
perspective of `klFun`: for nonnegative integrable `a` and `b` with `a = 0` wherever `b = 0`,
`(∫ b) klFun ((∫ a) / ∫ b) ≤ ∫ b klFun (a / b)`. -/
theorem mul_klFun_integral_div_integral_le {a b : α → ℝ}
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hab : ∀ x, b x = 0 → a x = 0)
    (hai : Integrable a μ) (hbi : Integrable b μ)
    (hi : Integrable (fun x => b x * klFun (a x / b x)) μ) :
    (∫ x, b x ∂μ) * klFun ((∫ x, a x ∂μ) / ∫ x, b x ∂μ) ≤ ∫ x, b x * klFun (a x / b x) ∂μ := by
  have hnn (x : α) : 0 ≤ b x * klFun (a x / b x) :=
    mul_nonneg (hb x) (klFun_nonneg (div_nonneg (ha x) (hb x)))
  rcases (integral_nonneg (f := b) (μ := μ) hb).eq_or_lt with hB | hB
  · rw [← hB, zero_mul]
    exact integral_nonneg (μ := μ) fun x => hnn x
  rcases (integral_nonneg (f := a) (μ := μ) ha).eq_or_lt with hA | hA
  · have h0 : a =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg (fun x => ha x) hai).1 hA.symm
    rw [← hA, zero_div, klFun_zero, mul_one]
    refine (integral_congr_ae ?_).le
    filter_upwards [h0] with x hx
    rw [Pi.zero_apply] at hx
    simp [hx, klFun_zero]
  set A := ∫ x, a x ∂μ
  set B := ∫ x, b x ∂μ
  have ht : 0 < A / B := div_pos hA hB
  have hpt (x : α) : b x * klFun (A / B) + Real.log (A / B) * (a x - b x * (A / B)) ≤
      b x * klFun (a x / b x) := by
    rcases (hb x).eq_or_lt with h | h
    · rw [← h, hab x h.symm]
      simp
    · have hc : b x * (a x / b x) = a x := mul_div_cancel₀ _ h.ne'
      calc b x * klFun (A / B) + Real.log (A / B) * (a x - b x * (A / B))
          = b x * (klFun (A / B) + Real.log (A / B) * (a x / b x - A / B)) := by
            linear_combination -(Real.log (A / B)) * hc
        _ ≤ b x * klFun (a x / b x) := mul_le_mul_of_nonneg_left
            (klFun_add_log_mul_sub_le ht (div_nonneg (ha x) h.le)) h.le
  have hi1 : Integrable (fun x => b x * klFun (A / B)) μ := hbi.mul_const _
  have hi2 : Integrable (fun x => b x * (A / B)) μ := hbi.mul_const _
  have hi3 : Integrable (fun x => a x - b x * (A / B)) μ := hai.sub hi2
  have hi4 : Integrable (fun x => Real.log (A / B) * (a x - b x * (A / B))) μ :=
    hi3.const_mul _
  have hlin : Integrable
      (fun x => b x * klFun (A / B) + Real.log (A / B) * (a x - b x * (A / B))) μ := hi1.add hi4
  calc B * klFun (A / B)
      = ∫ x, (b x * klFun (A / B) + Real.log (A / B) * (a x - b x * (A / B))) ∂μ := by
        rw [integral_add hi1 hi4, integral_mul_const, integral_const_mul, integral_sub hai hi2,
          integral_mul_const, mul_div_cancel₀ _ hB.ne', sub_self, mul_zero, add_zero]
    _ ≤ ∫ x, b x * klFun (a x / b x) ∂μ := integral_mono hlin hi hpt

/-- **Jensen's inequality for the binary relative entropy**: for `q, p` with values in `[0, 1]`
under a probability measure, with `q = 0` wherever `p = 0` and `q = 1` wherever `p = 1`,
`binaryKL (∫ q) (∫ p) ≤ ∫ binaryKL q p`. Without the conditions on `p = 0` and `p = 1`, where the
true divergence is infinite unless `q = p`, the junk values of `binaryKL` are not convex. -/
theorem binaryKL_integral_le_integral [IsProbabilityMeasure μ] {q p : α → ℝ}
    (hq : ∀ x, q x ∈ Icc (0 : ℝ) 1) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ x, p x = 0 → q x = 0) (h1 : ∀ x, p x = 1 → q x = 1)
    (hqm : AEMeasurable q μ) (hpm : AEMeasurable p μ)
    (hkl : Integrable (fun x => binaryKL (q x) (p x)) μ) :
    binaryKL (∫ x, q x ∂μ) (∫ x, p x ∂μ) ≤ ∫ x, binaryKL (q x) (p x) ∂μ := by
  have hqi : Integrable q μ := Integrable.of_mem_Icc 0 1 hqm (ae_of_all _ hq)
  have hpi : Integrable p μ := Integrable.of_mem_Icc 0 1 hpm (ae_of_all _ hp)
  have hn1 (x : α) : 0 ≤ p x * klFun (q x / p x) :=
    mul_nonneg (hp x).1 (klFun_nonneg (div_nonneg (hq x).1 (hp x).1))
  have hn2 (x : α) : 0 ≤ (1 - p x) * klFun ((1 - q x) / (1 - p x)) :=
    mul_nonneg (sub_nonneg.2 (hp x).2)
      (klFun_nonneg (div_nonneg (sub_nonneg.2 (hq x).2) (sub_nonneg.2 (hp x).2)))
  have hi1 : Integrable (fun x => p x * klFun (q x / p x)) μ :=
    hkl.mono' (hpm.mul (measurable_klFun.comp_aemeasurable (hqm.div hpm))).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (hn1 x), binaryKL_def]
        exact le_add_of_nonneg_right (hn2 x))
  have hi2 : Integrable (fun x => (1 - p x) * klFun ((1 - q x) / (1 - p x))) μ :=
    hkl.mono' ((aemeasurable_const.sub hpm).mul (measurable_klFun.comp_aemeasurable
      ((aemeasurable_const.sub hqm).div (aemeasurable_const.sub hpm)))).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (hn2 x), binaryKL_def]
        exact le_add_of_nonneg_left (hn1 x))
  have j1 := mul_klFun_integral_div_integral_le (fun x => (hq x).1) (fun x => (hp x).1) h0 hqi
    hpi hi1
  have j2 := mul_klFun_integral_div_integral_le (μ := μ) (a := fun x => 1 - q x)
    (b := fun x => 1 - p x) (fun x => sub_nonneg.2 (hq x).2) (fun x => sub_nonneg.2 (hp x).2)
    (fun x h => by rw [h1 x (by linarith), sub_self])
    ((integrable_const 1).sub hqi) ((integrable_const 1).sub hpi) hi2
  rw [integral_sub (integrable_const 1) hqi, integral_sub (integrable_const 1) hpi] at j2
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at j2
  simp_rw [binaryKL_def]
  rw [integral_add hi1 hi2]
  exact add_le_add j1 j2

end Jensen

end Cslib.Probability
