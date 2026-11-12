/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PoissonBinomial
public import CslibFrontier.Probability.StochasticDomination.Basic
public import Mathlib.Probability.Distributions.Binomial
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.PMF.ToReal

/-!
# Stochastic domination for Poisson-binomial and binomial distributions

Monotonicity of `Cslib.Probability.PMF.coin`, `Cslib.Probability.PMF.poissonBinomial`, and
Mathlib's `ProbabilityTheory.binomial` with respect to first-order stochastic domination,
together with the negative-binomial tail sum
`∑' t, (ProbabilityTheory.binomial t p).real (Set.Iio r) = r / p`.

## Main results

* `Cslib.Probability.PMF.coin_stochasticallyDominates_iff`: `coin q` stochastically dominates
  `coin p` if and only if `(p : ℝ) ≤ q`.
* `Cslib.Probability.PMF.poissonBinomial_stochasticallyDominates_of_forall₂`: parameterwise
  monotonicity of `poissonBinomial`.
* `Cslib.Probability.PMF.poissonBinomial_stochasticallyDominates_replicate`,
  `Cslib.Probability.PMF.replicate_stochasticallyDominates_poissonBinomial`: uniform lower and
  upper binomial bounds for `poissonBinomial`.
* `Cslib.Probability.binomial_stochasticallyDominates_of_le`,
  `Cslib.Probability.binomial_stochasticallyDominates_of_nat_le`: monotonicity of
  `ProbabilityTheory.binomial` in both `p` and `n`.
* `Cslib.Probability.tsum_binomial_real_Iio`: exact waiting-time series
  `∑' t, (ProbabilityTheory.binomial t p).real (Set.Iio r) = (r : ℝ) / p` for `0 < (p : ℝ)`.
-/

public section

namespace Cslib.Probability.PMF

open MeasureTheory
open scoped BigOperators ENNReal unitInterval

/-- `coin q` stochastically dominates `coin p` if and only if `(p : ℝ) ≤ q`. -/
theorem coin_stochasticallyDominates_iff {p q : I} :
    StochasticallyDominates (coin q) (coin p) ↔ (p : ℝ) ≤ q := by
  rw [stochasticallyDominates_bool_iff, coin_apply, coin_apply]
  simp only [↓reduceIte]
  exact ENNReal.ofReal_le_ofReal_iff q.2.1

/-- `coin q` stochastically dominates `coin p` whenever `(p : ℝ) ≤ q`. -/
theorem coin_stochasticallyDominates {p q : I} (hpq : (p : ℝ) ≤ q) :
    StochasticallyDominates (coin q) (coin p) :=
  coin_stochasticallyDominates_iff.mpr hpq

private theorem map_stochasticallyDominates_map_of_le {α β : Type*} [Preorder β]
    (p : PMF α) {f g : α → β} (hfg : ∀ a, f a ≤ g a) :
    StochasticallyDominates (p.map g) (p.map f) := by
  intro U hU
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  refine p.toOuterMeasure.mono fun a ha => ?_
  exact hU (hfg a) ha

/-- Prepending a larger success probability preserves stochastic domination of Poisson-binomial
distributions. -/
theorem poissonBinomial_stochasticallyDominates_cons {p q : I} {ps qs : List I}
    (hpq : (p : ℝ) ≤ q)
    (hdom : StochasticallyDominates (poissonBinomial qs) (poissonBinomial ps)) :
    StochasticallyDominates (poissonBinomial (q :: qs)) (poissonBinomial (p :: ps)) := by
  rw [poissonBinomial_cons, poissonBinomial_cons]
  refine (coin_stochasticallyDominates hpq).bind ?_ ?_
  · intro b
    refine hdom.map fun k₁ k₂ hk => ?_
    cases b <;> simp [hk]
  · intro b₁ b₂ hb
    refine map_stochasticallyDominates_map_of_le (poissonBinomial qs) fun k => ?_
    cases b₁ <;> cases b₂
    · exact le_rfl
    · exact Nat.le_succ k
    · exact absurd hb (by decide)
    · exact le_rfl

/-- If `ps` is pointwise bounded by `qs` (`List.Forall₂`), then `poissonBinomial qs`
stochastically dominates `poissonBinomial ps`. -/
theorem poissonBinomial_stochasticallyDominates_of_forall₂ {ps qs : List I}
    (h : List.Forall₂ (fun p q : I => (p : ℝ) ≤ q) ps qs) :
    StochasticallyDominates (poissonBinomial qs) (poissonBinomial ps) := by
  induction h with
  | nil => exact StochasticallyDominates.refl _
  | cons hp _ ih => exact poissonBinomial_stochasticallyDominates_cons hp ih

/-- If every probability in `ps` is at least `p`, then `poissonBinomial ps` stochastically dominates
`poissonBinomial (List.replicate ps.length p)`. -/
theorem poissonBinomial_stochasticallyDominates_replicate {ps : List I} {p : I}
    (hp : ∀ q ∈ ps, (p : ℝ) ≤ q) :
    StochasticallyDominates (poissonBinomial ps)
      (poissonBinomial (List.replicate ps.length p)) := by
  induction ps with
  | nil => exact StochasticallyDominates.refl _
  | cons q ps ih =>
    rw [List.length_cons, List.replicate_succ]
    exact poissonBinomial_stochasticallyDominates_cons (hp q (by simp))
      (ih fun r hr => hp r (by simp [hr]))

/-- If every probability in `ps` is at most `p`, then `poissonBinomial (List.replicate ps.length p)`
stochastically dominates `poissonBinomial ps`. -/
theorem replicate_stochasticallyDominates_poissonBinomial {ps : List I} {p : I}
    (hp : ∀ q ∈ ps, (q : ℝ) ≤ p) :
    StochasticallyDominates (poissonBinomial (List.replicate ps.length p))
      (poissonBinomial ps) := by
  induction ps with
  | nil => exact StochasticallyDominates.refl _
  | cons q ps ih =>
    rw [List.length_cons, List.replicate_succ]
    exact poissonBinomial_stochasticallyDominates_cons (hp q (by simp))
      (ih fun r hr => hp r (by simp [hr]))

/-- Adding a `ℕ`-valued step preserves/increases a `PMF ℕ` in stochastic order. -/
theorem bind_add_stochasticallyDominates_left (p q : PMF ℕ) :
    StochasticallyDominates (p.bind fun a => q.map fun b => a + b) p := by
  intro U hU
  rw [PMF.toOuterMeasure_bind_apply]
  have hterm (a : ℕ) : a ∈ U → (q.map fun b => a + b).toOuterMeasure U = 1 := by
    intro ha
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_eq_one_iff]
    intro b _
    exact hU (Nat.le_add_right a b) ha
  have hle : p.toOuterMeasure U ≤ ∑' a, p a * (q.map fun b => a + b).toOuterMeasure U := by
    rw [PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun a => ?_
    by_cases ha : a ∈ U
    · rw [Set.indicator_of_mem ha, hterm a ha, mul_one]
    · rw [Set.indicator_of_notMem ha]
      exact (zero_le : (0 : ℝ≥0∞) ≤ _)
  exact hle

/-- Adding more trials increases `poissonBinomial` in stochastic order. -/
theorem poissonBinomial_append_stochasticallyDominates_left (ps qs : List I) :
    StochasticallyDominates (poissonBinomial (ps ++ qs)) (poissonBinomial ps) := by
  rw [poissonBinomial_append]
  exact bind_add_stochasticallyDominates_left (poissonBinomial ps) (poissonBinomial qs)

end Cslib.Probability.PMF

namespace Cslib.Probability

open MeasureTheory
open scoped BigOperators ENNReal unitInterval

/-- `ProbabilityTheory.binomial n q` stochastically dominates `ProbabilityTheory.binomial n p`
whenever `(p : ℝ) ≤ q`. -/
theorem binomial_stochasticallyDominates_of_le (n : ℕ) {p q : I} (hpq : (p : ℝ) ≤ q) :
    StochasticallyDominates (ProbabilityTheory.binomial n q) (ProbabilityTheory.binomial n p) := by
  rw [← PMF.toMeasure_poissonBinomial_replicate n q,
    ← PMF.toMeasure_poissonBinomial_replicate n p]
  refine (PMF.stochasticallyDominates_iff_toMeasure_nat).mp ?_
  refine PMF.poissonBinomial_stochasticallyDominates_of_forall₂ ?_
  induction n with
  | zero => exact .nil
  | succ _ ih => exact .cons hpq ih

/-- `ProbabilityTheory.binomial n p` stochastically dominates `ProbabilityTheory.binomial m p`
whenever `m ≤ n`. -/
theorem binomial_stochasticallyDominates_of_nat_le {m n : ℕ} (hmn : m ≤ n) (p : I) :
    StochasticallyDominates (ProbabilityTheory.binomial n p) (ProbabilityTheory.binomial m p) := by
  rw [← PMF.toMeasure_poissonBinomial_replicate n p,
    ← PMF.toMeasure_poissonBinomial_replicate m p,
    ← PMF.stochasticallyDominates_iff_toMeasure_nat]
  have hrep : List.replicate n p = List.replicate m p ++ List.replicate (n - m) p := by
    rw [← List.replicate_add]
    congr 1
    omega
  rw [hrep]
  exact PMF.poissonBinomial_append_stochasticallyDominates_left _ _

/-- If every entry of `ps` is at least `p`, then `(poissonBinomial ps).toMeasure` stochastically
dominates `ProbabilityTheory.binomial ps.length p`. -/
theorem toMeasure_poissonBinomial_stochasticallyDominates_binomial {ps : List I} {p : I}
    (hp : ∀ q ∈ ps, (p : ℝ) ≤ q) :
    StochasticallyDominates (PMF.poissonBinomial ps).toMeasure
      (ProbabilityTheory.binomial ps.length p) := by
  rw [← PMF.toMeasure_poissonBinomial_replicate ps.length p]
  exact (PMF.poissonBinomial_stochasticallyDominates_replicate hp).toMeasure

/-- If every entry of `ps` is at most `p`, then `ProbabilityTheory.binomial ps.length p`
stochastically dominates `(poissonBinomial ps).toMeasure`. -/
theorem binomial_stochasticallyDominates_toMeasure_poissonBinomial {ps : List I} {p : I}
    (hp : ∀ q ∈ ps, (q : ℝ) ≤ p) :
    StochasticallyDominates (ProbabilityTheory.binomial ps.length p)
      (PMF.poissonBinomial ps).toMeasure := by
  rw [← PMF.toMeasure_poissonBinomial_replicate ps.length p]
  exact (PMF.replicate_stochasticallyDominates_poissonBinomial hp).toMeasure

private theorem binomial_real_Iio_eq_sum (t r : ℕ) (p : I) :
    (ProbabilityTheory.binomial t p).real (Set.Iio r) =
      ∑ k ∈ Finset.range r, (PMF.poissonBinomial (List.replicate t p) k).toReal := by
  rw [← PMF.toMeasure_poissonBinomial_replicate t p]
  have hset : Set.Iio r = (Finset.range r : Set ℕ) := by
    ext k
    simp
  rw [hset, measureReal_def, PMF.toMeasure_apply_finset]
  rw [ENNReal.toReal_sum fun k _ => PMF.apply_ne_top _ k]

/-- Pascal-style recurrence for `(ProbabilityTheory.binomial t p).real (Set.Iio r)`. -/
theorem binomial_real_Iio_succ (t r : ℕ) (p : I) :
    (ProbabilityTheory.binomial (t + 1) p).real (Set.Iio (r + 1)) =
      (1 - (p : ℝ)) * (ProbabilityTheory.binomial t p).real (Set.Iio (r + 1)) +
        (p : ℝ) * (ProbabilityTheory.binomial t p).real (Set.Iio r) := by
  simp only [binomial_real_Iio_eq_sum]
  rw [Finset.sum_range_succ' (fun k => (PMF.poissonBinomial (List.replicate (t + 1) p) k).toReal)]
  have hcons : List.replicate (t + 1) p = p :: List.replicate t p := List.replicate_succ
  simp_rw [hcons, PMF.poissonBinomial_cons_zero_toReal, PMF.poissonBinomial_cons_succ_toReal]
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsplit :
      (1 - (p : ℝ)) * (PMF.poissonBinomial (List.replicate t p) 0).toReal +
          (1 - (p : ℝ)) *
            ∑ k ∈ Finset.range r, (PMF.poissonBinomial (List.replicate t p) (k + 1)).toReal =
        (1 - (p : ℝ)) *
          ∑ k ∈ Finset.range (r + 1), (PMF.poissonBinomial (List.replicate t p) k).toReal := by
    rw [Finset.sum_range_succ' (fun k => (PMF.poissonBinomial (List.replicate t p) k).toReal)]
    ring
  linarith

private theorem binomial_zero_real_Iio_succ (r : ℕ) (p : I) :
    (ProbabilityTheory.binomial 0 p).real (Set.Iio (r + 1)) = 1 := by
  simp only [ProbabilityTheory.binomial_zero, Measure.real,
    Measure.dirac_apply' _ measurableSet_Iio, Set.mem_Iio, Nat.zero_lt_succ,
    Set.indicator_of_mem, Pi.one_apply, ENNReal.toReal_one]

/-- Partial sums of `(ProbabilityTheory.binomial t p).real (Set.Iio r)` are bounded by `r / p`. -/
theorem sum_binomial_real_Iio_le (N r : ℕ) {p : I} (hp : 0 < (p : ℝ)) :
    ∑ t ∈ Finset.range N, (ProbabilityTheory.binomial t p).real (Set.Iio r) ≤ (r : ℝ) / p := by
  rw [le_div_iff₀ hp]
  induction r generalizing N with
  | zero =>
    simp
  | succ r ih =>
    have hrec (t : ℕ) :
        (ProbabilityTheory.binomial t p).real (Set.Iio (r + 1)) * (p : ℝ) =
          ((ProbabilityTheory.binomial t p).real (Set.Iio (r + 1)) -
              (ProbabilityTheory.binomial (t + 1) p).real (Set.Iio (r + 1))) +
            (ProbabilityTheory.binomial t p).real (Set.Iio r) * (p : ℝ) := by
      linarith [binomial_real_Iio_succ t r p]
    rw [Finset.sum_mul]
    simp_rw [hrec, Finset.sum_add_distrib, Finset.sum_range_sub']
    have h0 := binomial_zero_real_Iio_succ r p
    have hN : 0 ≤ (ProbabilityTheory.binomial N p).real (Set.Iio (r + 1)) := measureReal_nonneg
    have htail :
        ∑ t ∈ Finset.range N, (ProbabilityTheory.binomial t p).real (Set.Iio r) * (p : ℝ) ≤ r := by
      rw [← Finset.sum_mul]
      exact ih N
    push_cast
    linarith

/-- Summability of the waiting-time tail probabilities
`(ProbabilityTheory.binomial t p).real (Set.Iio r)` for `0 < (p : ℝ)`. -/
theorem summable_binomial_real_Iio (r : ℕ) {p : I} (hp : 0 < (p : ℝ)) :
    Summable fun t : ℕ => (ProbabilityTheory.binomial t p).real (Set.Iio r) :=
  summable_of_sum_range_le (fun _ => measureReal_nonneg) fun N => sum_binomial_real_Iio_le N r hp

/-- Exact negative-binomial waiting-time series:
`∑' t, (ProbabilityTheory.binomial t p).real (Set.Iio r) = (r : ℝ) / p` for `0 < (p : ℝ)`. -/
theorem tsum_binomial_real_Iio (r : ℕ) {p : I} (hp : 0 < (p : ℝ)) :
    ∑' t : ℕ, (ProbabilityTheory.binomial t p).real (Set.Iio r) = (r : ℝ) / p := by
  rw [eq_div_iff hp.ne']
  induction r with
  | zero =>
    simp
  | succ r ih =>
    have hs1 : Summable fun t : ℕ => (ProbabilityTheory.binomial t p).real (Set.Iio (r + 1)) :=
      summable_binomial_real_Iio (r + 1) hp
    have hs0 : Summable fun t : ℕ => (ProbabilityTheory.binomial t p).real (Set.Iio r) :=
      summable_binomial_real_Iio r hp
    have hshift :
        ∑' t : ℕ, (ProbabilityTheory.binomial (t + 1) p).real (Set.Iio (r + 1)) =
          (∑' t : ℕ, (ProbabilityTheory.binomial t p).real (Set.Iio (r + 1))) -
            (ProbabilityTheory.binomial 0 p).real (Set.Iio (r + 1)) := by
      rw [hs1.tsum_eq_zero_add]
      ring
    have hrec_sum :
        ∑' t : ℕ, (ProbabilityTheory.binomial (t + 1) p).real (Set.Iio (r + 1)) =
          (1 - (p : ℝ)) * ∑' t : ℕ, (ProbabilityTheory.binomial t p).real (Set.Iio (r + 1)) +
            (p : ℝ) * ∑' t : ℕ, (ProbabilityTheory.binomial t p).real (Set.Iio r) := by
      simp_rw [binomial_real_Iio_succ]
      rw [Summable.tsum_add (hs1.mul_left _) (hs0.mul_left _), tsum_mul_left, tsum_mul_left]
    have h0 := binomial_zero_real_Iio_succ r p
    rw [hshift, h0] at hrec_sum
    push_cast
    linarith

end Cslib.Probability
