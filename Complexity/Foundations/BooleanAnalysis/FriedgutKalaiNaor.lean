/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Anticoncentration
public import Complexity.Foundations.BooleanAnalysis.LevelWeight
import Complexity.Probability.KWiseIndependent.TugOfWar

/-!
# The Friedgut–Kalai–Naor Theorem

A Boolean function `f` whose Fourier weight at degree one is `W^1[f] ≥ 1 - δ` is `O(δ)`-close to a
dictator or a negated dictator `x ↦ ±x_i`: this is the **Friedgut–Kalai–Naor (FKN) Theorem**
[FriedgutKalaiNaor2002] [O'Donnell, Section 2.5][ODonnell2014]. We prove it with the explicit
constants of O'Donnell's proof via the anticoncentration of low-degree functions
[O'Donnell, Section 9.1][ODonnell2014]: if `δ ≤ 1 / 1600`, some degree-one coefficient has
`|f̂({i})| ≥ 1 - 3202 δ` (`BitString.exists_one_sub_le_abs_fourierCoeff_singleton`), and in general
`f` agrees with `x ↦ b ⊕ x_i` for some `i` and `b` except on a fraction at most `1601 δ` of the
inputs (`BitString.exists_hammingDist_xor_div_le_of_le_levelWeight_one`). With `δ = 0`, a
Boolean function with `W^1[f] = 1` is a dictator or a negated dictator
(`BitString.exists_eq_xor_of_levelWeight_one_eq_one`)
[O'Donnell, Exercise 1.19(a)][ODonnell2014].

The proof, following O'Donnell, writes `ℓ = f^{=1} = ∑ᵢ f̂({i}) χ_{i}`, so `𝔼 ℓ ^ 2 = W^1[f]` and
`𝔼 (f - ℓ) ^ 2 = 1 - W^1[f] ≤ δ`. The variance of `ℓ ^ 2` is
`2 ((∑ᵢ f̂({i}) ^ 2) ^ 2 - ∑ᵢ f̂({i}) ^ 4)` (`BitString.expect_sum_mul_signVal_sq_sub_expect_sq`)
[O'Donnell, Exercise 1.20][ODonnell2014]; this is the variance of the tug-of-war estimator
(`Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq`) for the identity hash family.
If it exceeded `6400 δ`, then by the anticoncentration of the degree-two function `ℓ ^ 2`
(`BitString.nine_div_sixteen_div_nine_pow_le_dens`), with probability at least `1 / 144` we would
have `|ℓ ^ 2 - 1| > 39 √δ`, hence `(f - ℓ) ^ 2 ≥ 169 δ` (`BitString.mul_le_sq_sub_of_sq_eq_one`,
[O'Donnell, Exercise 9.5][ODonnell2014]), so `𝔼 (f - ℓ) ^ 2 ≥ 169 δ / 144 > δ`. Thus
`∑ᵢ f̂({i}) ^ 4 ≥ 1 - 3202 δ`, which bounds the largest `|f̂({i})|` from below. The distance bound
`1601 δ = (1 - (1 - 3202 δ)) / 2` follows since `f̂({i}) = 1 - 2 dist(f, x ↦ x_i)`; for
`δ > 1 / 1600` it is trivial.

## Main results

* `Cslib.BitString.exists_hammingDist_xor_div_le_of_le_levelWeight_one`: the FKN Theorem,
  `W^1[f] ≥ 1 - δ` gives `dist(f, ±χ_i) ≤ 1601 δ` for some `i`.
* `Cslib.BitString.exists_one_sub_le_abs_fourierCoeff_singleton`: its coefficient form,
  `max_i |f̂({i})| ≥ 1 - 3202 δ` for `δ ≤ 1 / 1600`.
* `Cslib.BitString.exists_eq_xor_of_levelWeight_one_eq_one`: `W^1[f] = 1` forces `f = ±χ_i`.
* `Cslib.BitString.expect_sum_mul_signVal_sq_sub_expect_sq`: the variance of the square of a
  homogeneous degree-one function.
* `Cslib.BitString.mul_le_sq_sub_of_sq_eq_one`: the scalar estimate of Exercise 9.5.

## References

* [E. Friedgut, G. Kalai, A. Naor, *Boolean functions whose Fourier transform is concentrated on
  the first two levels*][FriedgutKalaiNaor2002]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

/-- Exercise 9.5 normalised to `f = 1` and `u = √δ`. -/
private theorem sq_mul_le_sq_one_sub {l u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1 / 40)
    (hl : 39 * u < |l ^ 2 - 1|) : 169 * u ^ 2 ≤ (1 - l) ^ 2 := by
  by_contra hlt
  push Not at hlt
  have h13 : |1 - l| < 13 * u := abs_lt_of_sq_lt_sq (by nlinarith) (by linarith)
  have hplus : |l + 1| ≤ |1 - l| + 2 := by
    calc |l + 1| = |2 - (1 - l)| := by ring_nf
      _ ≤ |(2 : ℝ)| + |1 - l| := abs_sub _ _
      _ = |1 - l| + 2 := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
  have hfac : |l ^ 2 - 1| = |1 - l| * |l + 1| := by
    rw [← abs_mul, show l ^ 2 - 1 = -((1 - l) * (l + 1)) by ring, abs_neg]
  have h1 : |l ^ 2 - 1| ≤ 13 * u * (13 * u + 2) := by
    rw [hfac]
    calc |1 - l| * |l + 1| ≤ 13 * u * (|1 - l| + 2) :=
          mul_le_mul h13.le hplus (abs_nonneg _) (by linarith)
      _ ≤ 13 * u * (13 * u + 2) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
  nlinarith

/-- **A sign far from a near-unit square**: if `f ^ 2 = 1`, `0 ≤ δ ≤ 1 / 1600` and
`|ℓ ^ 2 - 1| > 39 √δ`, then `(f - ℓ) ^ 2 ≥ 169 δ` [O'Donnell, Exercise 9.5][ODonnell2014]. -/
theorem mul_le_sq_sub_of_sq_eq_one {f l δ : ℝ} (hf : f ^ 2 = 1) (hδ₀ : 0 ≤ δ)
    (hδ₁ : δ ≤ 1 / 1600) (hl : 39 * √δ < |l ^ 2 - 1|) : 169 * δ ≤ (f - l) ^ 2 := by
  have hu₀ := Real.sqrt_nonneg δ
  have hu₁ : √δ ≤ 1 / 40 := by
    rw [show (1 / 40 : ℝ) = √(1 / 1600) by
      rw [show (1 / 1600 : ℝ) = (1 / 40) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hδ₁
  have hsq : √δ ^ 2 = δ := Real.sq_sqrt hδ₀
  rcases mul_eq_zero.mp (show (f - 1) * (f + 1) = 0 by linear_combination hf) with h | h
  · have := sq_mul_le_sq_one_sub hu₀ hu₁ hl
    rw [show f = 1 by linarith]
    nlinarith
  · have := sq_mul_le_sq_one_sub hu₀ hu₁ (l := -l) (by rwa [neg_sq])
    rw [show f = -1 by linarith]
    nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sign `signVal` has square one. -/
private theorem signVal_sq (b : Bool) : signVal b ^ 2 = 1 := by rw [sq, signVal_mul_self]

/-- The sign `signVal` has mean zero. -/
private theorem expect_signVal_bool : 𝔼 b : Bool, signVal b = 0 := by
  rw [Fintype.expect_bool]; norm_num

/-- **Parseval's identity for a homogeneous degree-one function**:
`𝔼 (∑ᵢ aᵢ xᵢ) ^ 2 = ∑ᵢ aᵢ ^ 2`. This is the unbiasedness of the tug-of-war estimator
(`Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign`) for the identity hash family, whose
seed `x : ι → Bool` is uniformly random. -/
theorem expect_sum_mul_signVal_sq (a : ι → ℝ) :
    𝔼 x : ι → Bool, (∑ i, a i * signVal (x i)) ^ 2 = ∑ i, a i ^ 2 :=
  (Probability.isKWiseIndependentHash_id (X := ι) (Y := Bool) 2).expect_sq_sum_mul_sign
    signVal_sq expect_signVal_bool univ a

/-- **The variance of the square of a homogeneous degree-one function**: for `ℓ = ∑ᵢ aᵢ xᵢ`,
`Var[ℓ ^ 2] = 2 ∑_{i ≠ j} aᵢ ^ 2 aⱼ ^ 2 = 2 ((∑ᵢ aᵢ ^ 2) ^ 2 - ∑ᵢ aᵢ ^ 4)`
[O'Donnell, Exercise 1.20][ODonnell2014]. This is the variance of the tug-of-war estimator
(`Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq`) for the identity hash
family. -/
theorem expect_sum_mul_signVal_sq_sub_expect_sq (a : ι → ℝ) :
    𝔼 x : ι → Bool, ((∑ i, a i * signVal (x i)) ^ 2 -
        𝔼 y : ι → Bool, (∑ i, a i * signVal (y i)) ^ 2) ^ 2 =
      2 * ((∑ i, a i ^ 2) ^ 2 - ∑ i, a i ^ 4) := by
  rw [expect_sum_mul_signVal_sq]
  exact Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq
    (Probability.isKWiseIndependentHash_id (X := ι) (Y := Bool) 4) signVal_sq expect_signVal_bool
    univ a

/-- **The FKN Theorem**, coefficient form: if a Boolean function `f`, read as signs, has
`W^1[f] ≥ 1 - δ` with `δ ≤ 1 / 1600`, then some degree-one coefficient has
`|f̂({i})| ≥ 1 - 3202 δ` [FriedgutKalaiNaor2002] [O'Donnell, Section 9.1][ODonnell2014]. The
constants are those of O'Donnell's proof. -/
theorem exists_one_sub_le_abs_fourierCoeff_singleton {f : (ι → Bool) → Bool} {δ : ℝ}
    (hδ : δ ≤ 1 / 1600) (hW : 1 - δ ≤ levelWeight 1 (fun x => signVal (f x))) :
    ∃ i, 1 - 3202 * δ ≤ |fourierCoeff (fun x => signVal (f x)) {i}| := by
  classical
  set F : (ι → Bool) → ℝ := fun x => signVal (f x) with hF
  set a : ι → ℝ := fun i => fourierCoeff F {i} with ha
  set ℓ : (ι → Bool) → ℝ := fun x => ∑ i, a i * signVal (x i) with hℓ
  set A := ∑ i, a i ^ 2 with hA
  have hWA : levelWeight 1 F = A := levelWeight_one F
  -- `𝔼 F ℓ = 𝔼 ℓ ^ 2 = A` and `𝔼 F ^ 2 = 1`
  have hFℓ : 𝔼 x, F x * ℓ x = A := by
    simp only [hℓ, mul_sum, expect_sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [show (fun x => F x * (a i * signVal (x i))) = fun x => a i * (F x * chi ℝ {i} x) from
      funext fun x => by rw [chi_singleton]; ring, ← mul_expect, sq]
    rfl
  have hℓℓ : 𝔼 x, ℓ x ^ 2 = A := expect_sum_mul_signVal_sq a
  have hFsq (x : ι → Bool) : F x ^ 2 = 1 := by simp only [hF, sq, signVal_mul_self]
  have hFF : 𝔼 x, F x ^ 2 = 1 := by simp only [hFsq, Fintype.expect_const]
  -- `δ' = 𝔼 (F - ℓ) ^ 2 = 1 - W^1[f] ≤ δ`
  set δ' := 𝔼 x, (F x - ℓ x) ^ 2 with hδ'
  have hδ'A : δ' = 1 - A := by
    rw [hδ', show (fun x => (F x - ℓ x) ^ 2) = fun x => F x ^ 2 - 2 * (F x * ℓ x) + ℓ x ^ 2 from
      funext fun x => by ring, expect_add_distrib, expect_sub_distrib, ← mul_expect, hFF, hFℓ,
      hℓℓ]
    ring
  have hδ'0 : 0 ≤ δ' := expect_nonneg fun x _ => sq_nonneg _
  have hδ'δ : δ' ≤ δ := by rw [hδ'A, ← hWA]; linarith
  have hδ'1 : δ' ≤ 1 / 1600 := hδ'δ.trans hδ
  -- the variance of `ℓ ^ 2` is at most `6400 δ'`
  set V := 𝔼 x, (ℓ x ^ 2 - 𝔼 y, ℓ y ^ 2) ^ 2 with hV
  have hVeq : V = 2 * (A ^ 2 - ∑ i, a i ^ 4) := expect_sum_mul_signVal_sq_sub_expect_sq a
  have hVle : V ≤ 6400 * δ' := by
    by_contra hVgt
    push Not at hVgt
    have hVpos : 0 < V := lt_of_le_of_lt (by positivity) hVgt
    have hℓdeg : (fun x => ℓ x ^ 2) ∈ lowDegree ℝ ι 2 := by
      have h1 : ℓ ∈ lowDegree ℝ ι 1 := by
        have : ℓ = ∑ i, a i • chi ℝ {i} := by
          funext x
          simp only [hℓ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chi_singleton]
        rw [this]
        exact sum_mem_lowDegree _ fun i _ =>
          Submodule.smul_mem _ _ (by simpa using chi_mem_lowDegree (F := ℝ) {i})
      exact pow_mem_lowDegree h1 2
    -- by anticoncentration, `|ℓ ^ 2 - A| > √V / 2` with probability at least `1 / 144`
    have h97 : (1 / 144 : ℝ) ≤ (dens {x | √V / 2 < |ℓ x ^ 2 - A|} : ℝ) := by
      have h := nine_div_sixteen_div_nine_pow_le_dens hℓdeg hVpos
      rw [← hV, hℓℓ] at h
      calc (1 / 144 : ℝ) = 9 / 16 / 9 ^ 2 := by norm_num
        _ ≤ _ := h
    have hsqrt : 40 * √δ' < √V / 2 := by
      have : √(6400 * δ') < √V := Real.sqrt_lt_sqrt (by positivity) hVgt
      rw [Real.sqrt_mul (by norm_num), show √(6400 : ℝ) = 80 by
        rw [show (6400 : ℝ) = 80 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
      linarith
    have hδsq : δ' ≤ √δ' := by
      have h1 : √δ' ≤ 1 := by
        rw [Real.sqrt_le_one]; linarith
      calc δ' = √δ' * √δ' := (Real.mul_self_sqrt hδ'0).symm
        _ ≤ √δ' * 1 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
        _ = √δ' := mul_one _
    -- on that event, `(F - ℓ) ^ 2 ≥ 169 δ'`
    have hsub : ({x | √V / 2 < |ℓ x ^ 2 - A|} : Finset (ι → Bool)) ⊆
        ({x | 169 * δ' ≤ (F x - ℓ x) ^ 2} : Finset (ι → Bool)) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      have h39 : 39 * √δ' < |ℓ x ^ 2 - 1| := by
        have htri : |ℓ x ^ 2 - A| ≤ |ℓ x ^ 2 - 1| + |1 - A| := abs_sub_le _ _ _
        have h1A : |1 - A| = δ' := by rw [← hδ'A]; exact abs_of_nonneg hδ'0
        linarith
      exact mul_le_sq_sub_of_sq_eq_one (hFsq x) hδ'0 hδ'1 h39
    have hd : (dens ({x | √V / 2 < |ℓ x ^ 2 - A|} : Finset (ι → Bool)) : ℝ) ≤
        (dens ({x | 169 * δ' ≤ (F x - ℓ x) ^ 2} : Finset (ι → Bool)) : ℝ) := by
      exact_mod_cast dens_le_dens hsub
    -- so by Markov, `δ' ≥ 169 δ' / 144`, forcing `δ' = 0`
    have hmk := Fintype.mul_dens_filter_le_expect (f := fun x => (F x - ℓ x) ^ 2)
      (fun x => sq_nonneg _) (169 * δ')
    rw [← hδ'] at hmk
    rcases hδ'0.lt_or_eq with hpos | hzero
    · nlinarith
    · -- `δ' = 0`: then `F = ℓ`, so `ℓ ^ 2 = 1 = A` everywhere, and the event is empty
      have hFℓ0 : ∀ x, F x = ℓ x := by
        have := (Fintype.expect_eq_zero_iff_of_nonneg (fun x => sq_nonneg (F x - ℓ x))).mp
          hzero.symm
        intro x
        have hx := congrFun this x
        simp only [Pi.zero_apply, sq_eq_zero_iff] at hx
        linarith
      have hempty : ({x | √V / 2 < |ℓ x ^ 2 - A|} : Finset (ι → Bool)) = ∅ := by
        ext x
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
        rw [← hFℓ0 x, show A = 1 by linarith, hFsq x, sub_self, abs_zero]
        positivity
      rw [hempty, dens_empty, NNRat.cast_zero] at h97
      norm_num at h97
  -- hence `∑ᵢ aᵢ ^ 4 ≥ 1 - 3202 δ'`, and the largest `aᵢ ^ 2` bounds it
  have h4 : 1 - 3202 * δ' ≤ ∑ i, a i ^ 4 := by
    have hA' : A = 1 - δ' := by linarith
    nlinarith
  cases isEmpty_or_nonempty ι with
  | inl h =>
    -- with no coordinates `W^1[f] = 0`, so `δ' = 1 > 1 / 1600`
    have h0 : A = 0 := by simp [hA, Finset.univ_eq_empty]
    linarith
  | inr h =>
    obtain ⟨i₀, -, hi₀⟩ := exists_max_image univ (fun i => a i ^ 2) univ_nonempty
    have hA1 : A ≤ 1 := by linarith
    have hsum4 : ∑ i, a i ^ 4 ≤ a i₀ ^ 2 := by
      calc ∑ i, a i ^ 4 = ∑ i, a i ^ 2 * a i ^ 2 := sum_congr rfl fun i _ => by ring
        _ ≤ ∑ i, a i₀ ^ 2 * a i ^ 2 :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hi₀ i (mem_univ _)) (sq_nonneg _)
        _ = a i₀ ^ 2 * A := by rw [← mul_sum]
        _ ≤ a i₀ ^ 2 * 1 := mul_le_mul_of_nonneg_left hA1 (sq_nonneg _)
        _ = a i₀ ^ 2 := mul_one _
    have habs1 : |a i₀| ≤ 1 := by
      rw [← sq_le_one_iff_abs_le_one]
      linarith [single_le_sum (f := fun i => a i ^ 2) (fun j _ => sq_nonneg _) (mem_univ i₀)]
    have hsqabs : a i₀ ^ 2 ≤ |a i₀| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (a i₀)]
    exact ⟨i₀, by linarith⟩

/-- **The Friedgut–Kalai–Naor (FKN) Theorem**: if a Boolean function `f`, read as signs, has
Fourier weight `W^1[f] ≥ 1 - δ` at degree one, then `f` is `1601 δ`-close to a dictator or a
negated dictator: for some coordinate `i` and bit `b`, `f x = b ⊕ x_i` except on a fraction at most
`1601 δ` of the inputs [FriedgutKalaiNaor2002] [O'Donnell, Section 2.5][ODonnell2014]. The
proof is O'Donnell's [O'Donnell, Section 9.1][ODonnell2014]; the constant `1601` is
`3202 / 2`, from his bound `|f̂({i})| ≥ 1 - 3202 δ`. -/
theorem exists_hammingDist_xor_div_le_of_le_levelWeight_one [Nonempty ι]
    {f : (ι → Bool) → Bool} {δ : ℝ} (hW : 1 - δ ≤ levelWeight 1 (fun x => signVal (f x))) :
    ∃ (i : ι) (b : Bool),
      (hammingDist f (fun x => b ^^ x i) : ℝ) / 2 ^ Fintype.card ι ≤ 1601 * δ := by
  classical
  by_cases hδ : δ ≤ 1 / 1600
  · obtain ⟨i, hi⟩ := exists_one_sub_le_abs_fourierCoeff_singleton hδ hW
    set a := fourierCoeff (fun x => signVal (f x)) {i}
    refine ⟨i, decide (a < 0), ?_⟩
    -- the correlation of `f` with `x ↦ b ⊕ x_i` is `signVal b * a = |a|`
    have hcorr := expect_signVal_mul_signVal f (fun x => decide (a < 0) ^^ x i)
    have hcorr' : 𝔼 x, signVal (f x) * signVal (decide (a < 0) ^^ x i) = |a| := by
      have : 𝔼 x, signVal (f x) * signVal (decide (a < 0) ^^ x i) =
          signVal (decide (a < 0)) * a := by
        rw [show a = 𝔼 x, signVal (f x) * chi ℝ {i} x from rfl, mul_expect]
        refine expect_congr rfl fun x _ => ?_
        rw [signVal_xor, chi_singleton]
        ring
      rw [this]
      by_cases ha : a < 0
      · rw [decide_eq_true ha, signVal_true, abs_of_neg ha]; ring
      · rw [decide_eq_false ha, signVal_false, abs_of_nonneg (not_lt.mp ha), one_mul]
    rw [hcorr', mul_div_assoc] at hcorr
    linarith
  · -- for `δ > 1 / 1600` the bound exceeds one and holds for any `i` and `b`
    push Not at hδ
    refine ⟨Classical.arbitrary ι, false, ?_⟩
    have h1 : (hammingDist f (fun x => false ^^ x (Classical.arbitrary ι)) : ℝ) ≤
        2 ^ Fintype.card ι := by
      have := hammingDist_le_card_fintype (x := f)
        (y := fun x => false ^^ x (Classical.arbitrary ι))
      rw [Fintype.card_fun, Fintype.card_bool] at this
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (Fintype.card ι)]

/-- **Boolean functions of degree-one weight one are signed dictators**: if `W^1[f] = 1`, then
`f x = b ⊕ x_i` for some coordinate `i` and bit `b` [O'Donnell, Exercise 1.19(a)][ODonnell2014].
This is the FKN Theorem with `δ = 0`. -/
theorem exists_eq_xor_of_levelWeight_one_eq_one {f : (ι → Bool) → Bool}
    (hW : levelWeight 1 (fun x => signVal (f x)) = 1) :
    ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    rw [levelWeight_one, Finset.univ_eq_empty, sum_empty] at hW
    exact absurd hW zero_ne_one
  | inr h =>
    obtain ⟨i, b, hib⟩ := exists_hammingDist_xor_div_le_of_le_levelWeight_one (f := f) (δ := 0)
      (by rw [hW]; norm_num)
    refine ⟨i, b, hammingDist_eq_zero.mp ?_⟩
    rw [mul_zero, div_le_iff₀ (by positivity), zero_mul] at hib
    exact_mod_cast le_antisymm hib (Nat.cast_nonneg _)

end Cslib.BitString
