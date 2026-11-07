/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
import Complexity.Probability.PMF.Chebyshev
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Expect

/-!
# The product estimator

A product `∏ k, r k` of numbers in `(0, 1]` can be estimated one factor at a time when each
factor is close to the probability of an event `A k` under a distribution `μ k` that can be
sampled. Draw `a` independent samples from each `μ k`, take the fraction of them that lie in `A k`
(`Cslib.Probability.PMF.empiricalFrequency`), and multiply these fractions over the stages
(`Cslib.Probability.PMF.productEstimate`). This is how [LevinPeres2017], Section 14.4.2, reduces
approximate counting of colorings to sampling.

The stages are independent, so the mean and the second moment of the product are the products of
the stage means and second moments (`Cslib.Probability.PMF.sum_pi_mul_prod`). The fraction of `a`
samples in an event of probability `p` has mean `p` and second moment `p² + p (1 - p) / a`. If
every `r k` is at least `b > 0` and `a` is large compared with `n / b`, where `n` is the number of
stages, the relative variance of the product is small, and Chebyshev's inequality gives the
concentration bound `Cslib.Probability.PMF.le_toOuterMeasure_productEstimate`.

## Main definitions

* `Cslib.Probability.PMF.empiricalFrequency`: the fraction of a sample that lies in an event.
* `Cslib.Probability.PMF.productEstimate`: the product of the stage frequencies.

## Main results

* `Cslib.Probability.PMF.sum_pi_mul_prod`: the mean of a product of coordinate functions under an
  independent product is the product of the means.
* `Cslib.Probability.PMF.sum_pi_mul_sum_sq`: the second moment of a sum of i.i.d. terms.
* `Cslib.Probability.PMF.sum_pi_mul_empiricalFrequency`,
  `Cslib.Probability.PMF.sum_pi_mul_empiricalFrequency_sq`: the mean and the second moment of an
  empirical frequency.
* `Cslib.Probability.PMF.sum_pi_mul_productEstimate`,
  `Cslib.Probability.PMF.sum_pi_mul_productEstimate_sq`: the mean and the second moment of the
  product estimator.
* `Cslib.Probability.PMF.le_toOuterMeasure_productEstimate`: if every stage probability is within
  relative error `ε / (6 n)` of `r k ≥ b > 0` and `48 n ≤ 5 η ε² a b`, then the product estimator is
  within relative error `ε` of `∏ k, r k` with probability at least `1 - η`.

## References

* [LevinPeres2017], Section 14.4.2 (proof of Theorem 14.14).
-/

public section

open scoped ENNReal

namespace Cslib.Probability.PMF

open Finset

section Prod

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The mean of a product of coordinate functions under the independent product `pi p` is the
product of their means. -/
theorem sum_pi_mul_prod (p : ∀ i, PMF (α i)) (f : ∀ i, α i → ℝ) :
    ∑ x, (pi p x).toReal * ∏ i, f i (x i) = ∏ i, ∑ a, (p i a).toReal * f i a := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pi_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]

end Prod

section IID

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S]

/-- The second moment of a sum of `|ι|` i.i.d. copies of `g`:
`|ι| E[g²] + |ι| (|ι| - 1) (E g)²`. -/
theorem sum_pi_mul_sum_sq (μ : PMF S) (g : S → ℝ) :
    ∑ x : ι → S, ((pi fun _ => μ) x).toReal * (∑ i, g (x i)) ^ 2 =
      Fintype.card ι * ∑ a, (μ a).toReal * g a ^ 2 +
        (Fintype.card ι * (Fintype.card ι - 1) : ℝ) * (∑ a, (μ a).toReal * g a) ^ 2 := by
  have hpair (i j : ι) : ∑ x : ι → S, ((pi fun _ => μ) x).toReal * (g (x i) * g (x j)) =
      if i = j then ∑ a, (μ a).toReal * g a ^ 2 else (∑ a, (μ a).toReal * g a) ^ 2 := by
    split_ifs with hij
    · subst hij
      simpa only [sq] using sum_pi_mul_eval (fun _ => μ) i (fun a => g a * g a)
    · have h := sum_pi_mul_prod (fun _ : ι => μ)
        (fun k a => if k = i then g a else if k = j then g a else 1)
      have hl : ∀ x : ι → S, ∏ k, (if k = i then g (x k) else if k = j then g (x k) else 1) =
          g (x i) * g (x j) := fun x => by
        rw [Finset.prod_eq_mul i j hij]
        · simp [Ne.symm hij]
        · intro c _ hc
          simp [hc.1, hc.2]
        · simp
        · simp
      have hr : ∏ k, ∑ a, (μ a).toReal *
          (if k = i then g a else if k = j then g a else 1) =
          (∑ a, (μ a).toReal * g a) ^ 2 := by
        rw [Finset.prod_eq_mul i j hij]
        · simp [Ne.symm hij, sq]
        · intro c _ hc
          simp [hc.1, hc.2, sum_toReal]
        · simp
        · simp
      simp only [hl] at h
      rw [h, hr]
  calc ∑ x : ι → S, ((pi fun _ => μ) x).toReal * (∑ i, g (x i)) ^ 2
      = ∑ i, ∑ j, ∑ x : ι → S, ((pi fun _ => μ) x).toReal * (g (x i) * g (x j)) := by
        have hx : ∀ x : ι → S, ((pi fun _ => μ) x).toReal * (∑ i, g (x i)) ^ 2 =
            ∑ i, ∑ j, ((pi fun _ => μ) x).toReal * (g (x i) * g (x j)) := fun x => by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          simp only [Finset.mul_sum]
        simp only [hx]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        set A := ∑ a, (μ a).toReal * g a ^ 2
        set B := (∑ a, (μ a).toReal * g a) ^ 2
        have h (i j : ι) : (if i = j then A else B) = B + if i = j then A - B else 0 := by
          split_ifs <;> ring
        simp only [hpair, h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end IID

section Frequency

variable {S : Type*}

/-- The fraction of the samples `x 0, …, x (a - 1)` that lie in `A` (`0` when `a = 0`). -/
noncomputable def empiricalFrequency {a : ℕ} (A : Set S) [DecidablePred (· ∈ A)]
    (x : Fin a → S) : ℝ :=
  ((Finset.univ.filter fun j => x j ∈ A).card : ℝ) / a

/-- The empirical frequency as an average of indicators. -/
theorem empiricalFrequency_eq {a : ℕ} (A : Set S) [DecidablePred (· ∈ A)] (x : Fin a → S) :
    empiricalFrequency A x = (∑ j, if x j ∈ A then (1 : ℝ) else 0) / a := by
  rw [empiricalFrequency, Finset.sum_boole]

variable [Fintype S]

/-- The probability of `A` as the mean of its indicator. -/
theorem toOuterMeasure_toReal_eq_sum_ite (μ : PMF S) (A : Set S) [DecidablePred (· ∈ A)] :
    (μ.toOuterMeasure A).toReal = ∑ s, (μ s).toReal * if s ∈ A then (1 : ℝ) else 0 := by
  rw [toOuterMeasure_apply_toReal]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

/-- The empirical frequency of `A` among `a > 0` i.i.d. samples is an unbiased estimator of the
probability of `A`. -/
theorem sum_pi_mul_empiricalFrequency (μ : PMF S) (A : Set S) [DecidablePred (· ∈ A)] {a : ℕ}
    (ha : 0 < a) :
    ∑ x : Fin a → S, ((pi fun _ => μ) x).toReal * empiricalFrequency A x =
      (μ.toOuterMeasure A).toReal := by
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  simp only [empiricalFrequency_eq, mul_div_assoc', ← Finset.sum_div]
  rw [sum_pi_mul_sum (fun _ => μ) fun _ s => if s ∈ A then (1 : ℝ) else 0]
  simp only [← toOuterMeasure_toReal_eq_sum_ite, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The second moment of the empirical frequency of an event of probability `P` among `a > 0`
i.i.d. samples is `P² + P (1 - P) / a`. -/
theorem sum_pi_mul_empiricalFrequency_sq (μ : PMF S) (A : Set S) [DecidablePred (· ∈ A)] {a : ℕ}
    (ha : 0 < a) :
    ∑ x : Fin a → S, ((pi fun _ => μ) x).toReal * empiricalFrequency A x ^ 2 =
      (μ.toOuterMeasure A).toReal ^ 2 +
        (μ.toOuterMeasure A).toReal * (1 - (μ.toOuterMeasure A).toReal) / a := by
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hsq : ∑ s, (μ s).toReal * (if s ∈ A then (1 : ℝ) else 0) ^ 2 =
      (μ.toOuterMeasure A).toReal := by
    rw [toOuterMeasure_toReal_eq_sum_ite]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  simp only [empiricalFrequency_eq, div_pow, mul_div_assoc', ← Finset.sum_div]
  rw [sum_pi_mul_sum_sq μ fun s => if s ∈ A then (1 : ℝ) else 0, hsq,
    ← toOuterMeasure_toReal_eq_sum_ite, Fintype.card_fin]
  field_simp
  ring

end Frequency

section ProductEstimate

variable {κ S : Type*} [Fintype κ]

/-- The **product estimator**: the product over the stages `k` of the empirical frequency of
`A k` among the `a` samples `x k`. -/
noncomputable def productEstimate {a : ℕ} (A : κ → Set S) [∀ k, DecidablePred (· ∈ A k)]
    (x : κ → Fin a → S) : ℝ :=
  ∏ k, empiricalFrequency (A k) (x k)

theorem productEstimate_eq {a : ℕ} (A : κ → Set S) [∀ k, DecidablePred (· ∈ A k)]
    (x : κ → Fin a → S) : productEstimate A x = ∏ k, empiricalFrequency (A k) (x k) := by
  simp only [productEstimate]

variable [DecidableEq κ] [Fintype S]

/-- The product estimator with independent stages is an unbiased estimator of the product of the
stage probabilities. -/
theorem sum_pi_mul_productEstimate (μ : κ → PMF S) (A : κ → Set S)
    [∀ k, DecidablePred (· ∈ A k)] {a : ℕ} (ha : 0 < a) :
    ∑ x, ((pi fun k => pi fun _ : Fin a => μ k) x).toReal * productEstimate A x =
      ∏ k, ((μ k).toOuterMeasure (A k)).toReal := by
  simp only [productEstimate]
  rw [sum_pi_mul_prod (fun k => pi fun _ : Fin a => μ k) fun k => empiricalFrequency (A k)]
  exact Finset.prod_congr rfl fun k _ => sum_pi_mul_empiricalFrequency (μ k) (A k) ha

/-- The second moment of the product estimator with independent stages. -/
theorem sum_pi_mul_productEstimate_sq (μ : κ → PMF S) (A : κ → Set S)
    [∀ k, DecidablePred (· ∈ A k)] {a : ℕ} (ha : 0 < a) :
    ∑ x, ((pi fun k => pi fun _ : Fin a => μ k) x).toReal * productEstimate A x ^ 2 =
      ∏ k, (((μ k).toOuterMeasure (A k)).toReal ^ 2 +
        ((μ k).toOuterMeasure (A k)).toReal * (1 - ((μ k).toOuterMeasure (A k)).toReal) / a) := by
  simp only [productEstimate, ← Finset.prod_pow]
  rw [sum_pi_mul_prod (fun k => pi fun _ : Fin a => μ k) fun k x => empiricalFrequency (A k) x ^ 2]
  exact Finset.prod_congr rfl fun k _ => sum_pi_mul_empiricalFrequency_sq (μ k) (A k) ha

end ProductEstimate

/-- `(1 + y) ^ n ≤ 1 + 2 n y` when `0 ≤ y` and `n y ≤ 1 / 2`. -/
private theorem one_add_pow_le_one_add_two_mul {y : ℝ} (hy : 0 ≤ y) {n : ℕ}
    (hny : n * y ≤ 1 / 2) : (1 + y) ^ n ≤ 1 + 2 * n * y := by
  have key : ∀ m : ℕ, m * y ≤ 1 → (1 + y) ^ m * (1 - m * y) ≤ 1 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      push_cast at hm ⊢
      have hm' : (m : ℝ) * y ≤ 1 := by nlinarith
      have h := ih hm'
      have hp : 0 ≤ (1 + y) ^ m := by positivity
      calc (1 + y) ^ (m + 1) * (1 - (m + 1) * y)
          = (1 + y) ^ m * ((1 + y) * (1 - (m + 1) * y)) := by ring
        _ ≤ (1 + y) ^ m * (1 - m * y) := by
            refine mul_le_mul_of_nonneg_left ?_ hp
            nlinarith [mul_nonneg (Nat.cast_nonneg m) (mul_nonneg hy hy)]
        _ ≤ 1 := h
  have h := key n (by linarith)
  have hP : 0 ≤ (1 + y) ^ n := by positivity
  have hz : 0 ≤ (n : ℝ) * y := mul_nonneg (Nat.cast_nonneg n) hy
  nlinarith [mul_nonneg hP (mul_nonneg hz (by linarith : (0 : ℝ) ≤ 1 / 2 - n * y))]

section Concentration

variable {κ S : Type*} [Fintype κ] [Finite S]

/-- **Concentration of the product estimator.** Let `n = |κ|` be the number of stages. Suppose
stage `k` draws `a` independent samples from `μ k`, the probability of `A k` under `μ k` is within
relative error `ε / (6 n)` of `r k ≥ b > 0`, `0 < ε ≤ 1`, `0 < η` and `48 n ≤ 5 η ε² a b`. Then the
product estimator lies within relative error `ε` of `∏ k, r k` with probability at least
`1 - η`. This is the second-moment argument of [LevinPeres2017], proof of Theorem 14.14, for
general stages. -/
theorem le_toOuterMeasure_productEstimate (μ : κ → PMF S) (A : κ → Set S)
    [∀ k, DecidablePred (· ∈ A k)] (r : κ → ℝ) {b ε η : ℝ} {a : ℕ} (hb : 0 < b)
    (hr : ∀ k, b ≤ r k) (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η)
    (hp : ∀ k, |((μ k).toOuterMeasure (A k)).toReal - r k| ≤ ε / (6 * Fintype.card κ) * r k)
    (ha : 48 * (Fintype.card κ : ℝ) ≤ 5 * η * ε ^ 2 * a * b) :
    1 - η ≤ ((pi fun k => pi fun _ : Fin a => μ k).toOuterMeasure
      {x | (1 - ε) * ∏ k, r k ≤ productEstimate A x ∧
        productEstimate A x ≤ (1 + ε) * ∏ k, r k}).toReal := by
  classical
  have := Fintype.ofFinite S
  obtain ⟨E, hE⟩ : ∃ E : Set (κ → Fin a → S), E = {x | (1 - ε) * ∏ k, r k ≤ productEstimate A x ∧
      productEstimate A x ≤ (1 + ε) * ∏ k, r k} := ⟨_, rfl⟩
  rw [← hE]
  -- No stages: the estimate is the empty product `1`.
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have hEu : E = Set.univ := by
      rw [hE]
      ext x
      simp only [productEstimate, Finset.univ_eq_empty, Finset.prod_empty, Set.mem_ofPred_eq,
        Set.mem_univ, iff_true, mul_one]
      constructor <;> linarith
    rw [hEu, (_root_.PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _),
      ENNReal.toReal_one]
    linarith
  -- The trivial range `η ≥ 1`.
  rcases le_or_gt 1 η with hη1 | hη1
  · linarith [ENNReal.toReal_nonneg (a := (pi fun k => pi fun _ : Fin a => μ k).toOuterMeasure E)]
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card κ = n := ⟨_, rfl⟩
  rw [hn] at hp ha
  have hn1 : (1 : ℝ) ≤ n := by
    rw [← hn]
    exact_mod_cast Fintype.card_pos
  have hn0 : (0 : ℝ) < n := by linarith
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, Nat.cast_zero] at ha
      linarith
    · exact h
  have ha0' : (0 : ℝ) < a := Nat.cast_pos.2 ha0
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ε / (6 * n) := ⟨_, rfl⟩
  rw [← hδ] at hp
  have hnδ : n * δ = ε / 6 := by
    rw [hδ]
    field_simp
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 / 6 := by
    rw [hδ, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨p, hpdef⟩ : ∃ p : κ → ℝ, p = fun k => ((μ k).toOuterMeasure (A k)).toReal := ⟨_, rfl⟩
  have hpk (k : κ) : ((μ k).toOuterMeasure (A k)).toReal = p k := by rw [hpdef]
  simp only [hpk] at hp
  have hp0 (k : κ) : 0 ≤ p k := by rw [← hpk]; exact ENNReal.toReal_nonneg
  have hp1 (k : κ) : p k ≤ 1 := by
    rw [← hpk]
    have := ENNReal.toReal_mono ENNReal.one_ne_top (toOuterMeasure_le_one (μ k) (A k))
    rwa [ENNReal.toReal_one] at this
  have hr0 (k : κ) : 0 < r k := hb.trans_le (hr k)
  have hplo (k : κ) : (1 - δ) * r k ≤ p k := by
    have := (abs_le.1 (hp k)).1
    linarith
  have hphi (k : κ) : p k ≤ (1 + δ) * r k := by
    have := (abs_le.1 (hp k)).2
    linarith
  have hpb (k : κ) : 5 / 6 * b ≤ p k := by
    have := mul_le_mul_of_nonneg_right hδ1 (hr0 k).le
    linarith [hplo k, hr k]
  -- The mean `m = ∏ p k` is within relative error `ε / 3` of `R = ∏ r k`.
  obtain ⟨R, hR⟩ : ∃ R, R = ∏ k, r k := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = ∏ k, p k := ⟨_, rfl⟩
  rw [← hR] at hE
  have hR0 : 0 < R := by rw [hR]; exact Finset.prod_pos fun k _ => hr0 k
  have hm_lo : (1 - ε / 6) * R ≤ m := by
    have h1 : (1 - ε / 6) ≤ (1 - δ) ^ n := by
      have := one_add_mul_le_pow (a := -δ) (by linarith) n
      rw [← sub_eq_add_neg] at this
      linarith
    calc (1 - ε / 6) * R ≤ (1 - δ) ^ n * R := mul_le_mul_of_nonneg_right h1 hR0.le
      _ = ∏ k, (1 - δ) * r k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hn, hR]
      _ ≤ m := by
          rw [hm]
          exact Finset.prod_le_prod₀ (fun k _ => mul_nonneg (by linarith) (hr0 k).le)
            fun k _ => hplo k
  have hm_hi : m ≤ (1 + ε / 3) * R := by
    have h1 : (1 + δ) ^ n ≤ 1 + ε / 3 := by
      have := one_add_pow_le_one_add_two_mul hδ0 (n := n) (by linarith)
      linarith
    calc m ≤ ∏ k, (1 + δ) * r k := by
          rw [hm]
          exact Finset.prod_le_prod₀ (fun k _ => hp0 k) fun k _ => hphi k
      _ = (1 + δ) ^ n * R := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hn, hR]
      _ ≤ (1 + ε / 3) * R := mul_le_mul_of_nonneg_right h1 hR0.le
  have hm0 : 0 < m := by
    have := mul_pos (by linarith : (0 : ℝ) < 1 - ε / 6) hR0
    linarith
  -- The second moment: `E W² ≤ (1 + 2 n y) m²` with `y = 6 / (5 a b)`.
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 6 / (5 * a * b) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have h8 : 8 * n * y ≤ η * ε ^ 2 := by
    rw [hy, show 8 * (n : ℝ) * (6 / (5 * a * b)) = 48 * n / (5 * a * b) by ring,
      div_le_iff₀ (by positivity)]
    linarith
  have hny : n * y ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left (pow_le_one₀ hε.le hε1 (n := 2)) hη.le
    linarith
  have hfac (k : κ) : p k ^ 2 + p k * (1 - p k) / a ≤ (1 + y) * p k ^ 2 := by
    have h1 : 1 / (a : ℝ) ≤ p k * y := by
      rw [hy, div_le_iff₀ ha0', show p k * (6 / (5 * a * b)) * a = 6 * p k / (5 * b) by
        field_simp, le_div_iff₀ (by positivity)]
      linarith [hpb k]
    have h2 : p k * (1 - p k) / a ≤ p k / a :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (p k)]) ha0'.le
    have h3 : p k / a ≤ y * p k ^ 2 := by
      calc p k / a = p k * (1 / a) := by ring
        _ ≤ p k * (p k * y) := mul_le_mul_of_nonneg_left h1 (hp0 k)
        _ = y * p k ^ 2 := by ring
    linarith
  obtain ⟨P, hP⟩ : ∃ P : PMF (κ → Fin a → S), P = pi fun k => pi fun _ : Fin a => μ k :=
    ⟨_, rfl⟩
  have h1 := sum_pi_mul_productEstimate μ A ha0
  have h2 := sum_pi_mul_productEstimate_sq μ A ha0
  rw [← hP] at h1 h2
  rw [← hP]
  simp only [hpk] at h1 h2
  rw [← hm] at h1
  have hW2 : ∑ x, (P x).toReal * productEstimate A x ^ 2 ≤ (1 + 2 * n * y) * m ^ 2 := by
    rw [h2]
    calc ∏ k, (p k ^ 2 + p k * (1 - p k) / a) ≤ ∏ k, ((1 + y) * p k ^ 2) :=
          Finset.prod_le_prod₀ (fun k _ => add_nonneg (sq_nonneg _)
            (div_nonneg (mul_nonneg (hp0 k) (by linarith [hp1 k])) ha0'.le)) fun k _ => hfac k
      _ = (1 + y) ^ n * m ^ 2 := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hn, Finset.prod_pow,
            hm]
      _ ≤ (1 + 2 * n * y) * m ^ 2 :=
          mul_le_mul_of_nonneg_right (one_add_pow_le_one_add_two_mul hy0 hny) (sq_nonneg _)
  have hvar : ∑ x, (P x).toReal * (productEstimate A x - m) ^ 2 =
      ∑ x, (P x).toReal * productEstimate A x ^ 2 -
        2 * m * ∑ x, (P x).toReal * productEstimate A x + m ^ 2 := by
    have hx (x : κ → Fin a → S) : (P x).toReal * (productEstimate A x - m) ^ 2 =
        (P x).toReal * productEstimate A x ^ 2 - 2 * m * ((P x).toReal * productEstimate A x) +
          m ^ 2 * (P x).toReal := by ring
    simp only [hx, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_toReal, mul_one]
  have hvar' : ∑ x, (P x).toReal * (productEstimate A x - m) ^ 2 ≤ 2 * n * y * m ^ 2 := by
    rw [hvar, h1]
    linarith [hW2]
  -- Chebyshev's inequality.
  have hc : 0 < ε / 2 * m := by positivity
  have hcheb := sum_mul_ite_le_sum_mul_sq_div P (productEstimate A) m hc
    (fun x => ε / 2 * m ≤ |productEstimate A x - m|) fun x hx => hx
  have hbad : (P.toOuterMeasure {x | ε / 2 * m ≤ |productEstimate A x - m|}).toReal ≤ η := by
    rw [toOuterMeasure_toReal_eq_sum_ite]
    refine hcheb.trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith [hvar', mul_le_mul_of_nonneg_right h8 (sq_nonneg m)]
  have hsub : Eᶜ ⊆ {x | ε / 2 * m ≤ |productEstimate A x - m|} := by
    intro x hx
    rw [hE] at hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hx
    simp only [Set.mem_ofPred_eq]
    by_contra hlt
    rw [not_le, abs_lt] at hlt
    have hεR : 0 ≤ ε * R := mul_nonneg hε.le hR0.le
    rcases hx with hx | hx
    · have h1 : (1 - ε / 2) * ((1 - ε / 6) * R) ≤ (1 - ε / 2) * m :=
        mul_le_mul_of_nonneg_left hm_lo (by linarith)
      have h2 : 0 ≤ ε * (ε * R) := mul_nonneg hε.le hεR
      linarith [hlt.1]
    · have h1 : (1 + ε / 2) * m ≤ (1 + ε / 2) * ((1 + ε / 3) * R) :=
        mul_le_mul_of_nonneg_left hm_hi (by linarith)
      have h2 : ε * (ε * R) ≤ 1 * (ε * R) := mul_le_mul_of_nonneg_right hε1 hεR
      linarith [hlt.2]
  have hcompl := toOuterMeasure_toReal_add_compl P E
  have hmono : (P.toOuterMeasure Eᶜ).toReal ≤
      (P.toOuterMeasure {x | ε / 2 * m ≤ |productEstimate A x - m|}).toReal :=
    ENNReal.toReal_mono (toOuterMeasure_ne_top _ _) (MeasureTheory.measure_mono hsub)
  linarith

end Concentration

end Cslib.Probability.PMF
