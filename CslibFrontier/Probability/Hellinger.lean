/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.StatisticalDistance
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Hellinger distance and the Bhattacharyya coefficient

The Bhattacharyya coefficient `BC(p, q) = ∑' a, √((p a).toReal * (q a).toReal)`, squared Hellinger
distance `h²(p, q) = 1 - BC(p, q) = (∑' a, (√(p a).toReal - √(q a).toReal)²) / 2`, and Hellinger
distance `h(p, q) = √(h²(p, q))` on discrete distributions (`PMF α`).

No competing `MetricSpace (PMF α)` instance is registered because `Cslib.Probability.PMF` already
uses that typeclass slot for half-`L¹` statistical distance (`dist`); instead, symmetry,
definiteness, and `hellingerDist_triangle` are exposed directly.

## Main definitions

* `Cslib.Probability.PMF.bhattacharyya`: the Bhattacharyya coefficient
  `∑' a, √((p a).toReal * (q a).toReal)`.
* `Cslib.Probability.PMF.hellingerSq`: the squared Hellinger distance `1 - bhattacharyya p q`.
* `Cslib.Probability.PMF.hellingerDist`: the Hellinger distance `√(hellingerSq p q) ∈ [0, 1]`.

## Main results

* `Cslib.Probability.PMF.bhattacharyya_nonneg`, `bhattacharyya_le_one`, `bhattacharyya_eq_one_iff`,
  `bhattacharyya_eq_zero_iff`: elementary bounds and equality/disjointness characterizations.
* `Cslib.Probability.PMF.hellingerDist_triangle`: the triangle inequality for `hellingerDist`.
* `Cslib.Probability.PMF.hellingerSq_le_dist`, `dist_le_sqrt_two_mul_hellingerDist`,
  `dist_le_hellingerDist_mul_sqrt_two_sub_hellingerSq`: comparison with total variation distance
  (`dist`, half-`L¹`, and Mathlib `tvDist` corollaries).
* `Cslib.Probability.PMF.bhattacharyya_pi`, `bhattacharyya_iid`, `hellingerSq_pi_le_sum`,
  `hellingerSq_iid_le`: product and `iid` tensorization.
* `Cslib.Probability.PMF.hellingerDist_bind_le`, `hellingerDist_map_le`,
  `hellingerSq_bind_le_sum`: data processing and joint convexity.
* `Cslib.Probability.PMF.dist_iid_le_sqrt_two_mul_nat_mul_hellingerDist`:
  `dist (iid p n) (iid q n) ≤ √(2 * n) * hellingerDist p q`.

## References

* [Alexandre B. Tsybakov, *Introduction to Nonparametric Estimation*][Tsybakov2009], Springer,
  2009, Section 2.4 (note Tsybakov scales squared Hellinger by `2`, whereas we normalize
  `h(p, q) ∈ [0, 1]`).
* [Clément L. Canonne, *Topics and Techniques in Distribution Testing*][Canonne2022], Foundations
  and Trends in Communications and Information Theory, 2022; locators checked against the
  author-hosted draft (March 10, 2024): Appendix B (Definition B.1, `(B.3)`, `(B.6)`, Lemma B.1)
  and Section 3.1 (`(3.3)`).
-/

public section

namespace Cslib.Probability.PMF

open Finset
open scoped BigOperators Cslib.Probability.PMF ENNReal

variable {α β ι : Type*}

private lemma sqrt_mul_le_add_div_two {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ (u + v) / 2 := by
  rw [Real.sqrt_mul hu]
  nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt v), Real.mul_self_sqrt hu, Real.mul_self_sqrt hv]

private lemma summable_sqrt_toReal_mul (p q : PMF α) :
    Summable (fun a => Real.sqrt ((p a).toReal * (q a).toReal)) :=
  Summable.of_nonneg_of_le (fun _ => Real.sqrt_nonneg _)
    (fun _ => sqrt_mul_le_add_div_two ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (((summable_toReal p).add (summable_toReal q)).div_const 2)

private lemma summable_sqrt_toReal_sub_sq (p q : PMF α) :
    Summable (fun a => (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2) := by
  have hle (a : α) : (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2 ≤
      2 * ((p a).toReal + (q a).toReal) := by
    have hp : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
    have hq : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
    nlinarith [sq_nonneg (Real.sqrt (p a).toReal + Real.sqrt (q a).toReal),
      Real.mul_self_sqrt hp, Real.mul_self_sqrt hq]
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle
    (((summable_toReal p).add (summable_toReal q)).mul_left 2)

private lemma abs_toReal_sub_eq (p q : PMF α) (a : α) :
    |(p a).toReal - (q a).toReal| =
      |Real.sqrt (p a).toReal - Real.sqrt (q a).toReal| *
        (Real.sqrt (p a).toReal + Real.sqrt (q a).toReal) := by
  have hdiff : (p a).toReal - (q a).toReal =
      (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) *
        (Real.sqrt (p a).toReal + Real.sqrt (q a).toReal) := by
    nlinarith [Real.mul_self_sqrt (ENNReal.toReal_nonneg (a := p a)),
      Real.mul_self_sqrt (ENNReal.toReal_nonneg (a := q a))]
  rw [hdiff, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

private lemma sqrt_mul_left_mul_sqrt_mul_left {c u v : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) :
    Real.sqrt (c * u) * Real.sqrt (c * v) = c * Real.sqrt (u * v) := by
  rw [Real.sqrt_mul hc, Real.sqrt_mul hc, Real.sqrt_mul hu]
  have hmul : Real.sqrt c * Real.sqrt u * (Real.sqrt c * Real.sqrt v) =
      (Real.sqrt c * Real.sqrt c) * (Real.sqrt u * Real.sqrt v) := by ring
  rw [hmul, Real.mul_self_sqrt hc]

private lemma one_sub_prod_le_sum_one_sub {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (hc0 : ∀ i ∈ s, 0 ≤ c i) (hc1 : ∀ i ∈ s, c i ≤ 1) :
    0 ≤ ∏ i ∈ s, c i ∧ ∏ i ∈ s, c i ≤ 1 ∧ 1 - ∏ i ∈ s, c i ≤ ∑ i ∈ s, (1 - c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hc0i : 0 ≤ c i := hc0 i (Finset.mem_insert_self i s)
    have hc1i : c i ≤ 1 := hc1 i (Finset.mem_insert_self i s)
    obtain ⟨hp0, hp1, hih⟩ := ih
      (fun j hj => hc0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc1 j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    refine ⟨mul_nonneg hc0i hp0, (mul_le_mul hc1i hp1 hp0 zero_le_one).trans_eq (mul_one 1), ?_⟩
    nlinarith

/-- The Bhattacharyya coefficient `∑' a, √((p a).toReal * (q a).toReal)` between two discrete
distributions. It lies in `[0, 1]`, equals `1` iff `p = q`, and equals `0` iff the supports are
disjoint. -/
noncomputable def bhattacharyya (p q : PMF α) : ℝ :=
  ∑' a, Real.sqrt ((p a).toReal * (q a).toReal)

/-- The squared Hellinger distance `1 - bhattacharyya p q` between two discrete distributions. -/
noncomputable def hellingerSq (p q : PMF α) : ℝ :=
  1 - bhattacharyya p q

/-- The Hellinger distance `√(1 - bhattacharyya p q)` between two discrete distributions. -/
noncomputable def hellingerDist (p q : PMF α) : ℝ :=
  Real.sqrt (hellingerSq p q)

theorem bhattacharyya_eq_tsum (p q : PMF α) :
    bhattacharyya p q = ∑' a, Real.sqrt ((p a).toReal * (q a).toReal) := by
  unfold bhattacharyya
  rfl

theorem bhattacharyya_eq_sum [Fintype α] (p q : PMF α) :
    bhattacharyya p q = ∑ a, Real.sqrt ((p a).toReal * (q a).toReal) :=
  tsum_fintype _

theorem bhattacharyya_nonneg (p q : PMF α) : 0 ≤ bhattacharyya p q :=
  tsum_nonneg fun _ => Real.sqrt_nonneg _

theorem bhattacharyya_le_one (p q : PMF α) : bhattacharyya p q ≤ 1 := by
  have hsum : Summable (fun a => ((p a).toReal + (q a).toReal) / 2) :=
    ((summable_toReal p).add (summable_toReal q)).div_const 2
  have hle : bhattacharyya p q ≤ ∑' a, ((p a).toReal + (q a).toReal) / 2 :=
    Summable.tsum_le_tsum (fun _ => sqrt_mul_le_add_div_two ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg) (summable_sqrt_toReal_mul p q) hsum
  have hrhs : ∑' a, ((p a).toReal + (q a).toReal) / 2 = 1 := by
    rw [tsum_div_const, Summable.tsum_add (summable_toReal p) (summable_toReal q),
      tsum_toReal, tsum_toReal]
    norm_num
  linarith

theorem bhattacharyya_comm (p q : PMF α) : bhattacharyya p q = bhattacharyya q p := by
  simp only [bhattacharyya, mul_comm]

@[simp]
theorem bhattacharyya_self (p : PMF α) : bhattacharyya p p = 1 := by
  simp only [bhattacharyya, ← sq, Real.sqrt_sq ENNReal.toReal_nonneg, tsum_toReal]

theorem hellingerSq_eq_one_sub_bhattacharyya (p q : PMF α) :
    hellingerSq p q = 1 - bhattacharyya p q := by
  unfold hellingerSq
  rfl

theorem hellingerSq_eq_tsum (p q : PMF α) :
    hellingerSq p q = (∑' a, (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2) / 2 := by
  have hpt (a : α) : (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2 =
      ((p a).toReal + (q a).toReal) - 2 * Real.sqrt ((p a).toReal * (q a).toReal) := by
    have hp : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
    have hq : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
    rw [Real.sqrt_mul hp]
    nlinarith [Real.mul_self_sqrt hp, Real.mul_self_sqrt hq]
  simp_rw [hpt]
  rw [Summable.tsum_sub ((summable_toReal p).add (summable_toReal q))
    ((summable_sqrt_toReal_mul p q).mul_left 2)]
  rw [Summable.tsum_add (summable_toReal p) (summable_toReal q), tsum_toReal, tsum_toReal,
    tsum_mul_left]
  rw [hellingerSq_eq_one_sub_bhattacharyya, ← bhattacharyya_eq_tsum]
  ring

theorem hellingerSq_eq_sum [Fintype α] (p q : PMF α) :
    hellingerSq p q = (∑ a, (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2) / 2 := by
  rw [hellingerSq_eq_tsum, tsum_fintype]

theorem hellingerSq_nonneg (p q : PMF α) : 0 ≤ hellingerSq p q := by
  rw [hellingerSq_eq_one_sub_bhattacharyya]
  linarith [bhattacharyya_le_one p q]

theorem hellingerSq_le_one (p q : PMF α) : hellingerSq p q ≤ 1 := by
  rw [hellingerSq_eq_one_sub_bhattacharyya]
  linarith [bhattacharyya_nonneg p q]

theorem hellingerSq_comm (p q : PMF α) : hellingerSq p q = hellingerSq q p := by
  simp only [hellingerSq, bhattacharyya_comm]

@[simp]
theorem hellingerSq_self (p : PMF α) : hellingerSq p p = 0 := by
  simp only [hellingerSq, bhattacharyya_self, sub_self]

theorem hellingerSq_eq_zero_iff (p q : PMF α) : hellingerSq p q = 0 ↔ p = q := by
  rw [hellingerSq_eq_tsum, div_eq_zero_iff, or_iff_left two_ne_zero]
  constructor
  · intro h
    ext a
    have hsq0 : (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2 = 0 := by
      by_contra hne
      exact ((summable_sqrt_toReal_sub_sq p q).tsum_pos (fun _ => sq_nonneg _) a
        ((sq_nonneg _).lt_of_ne' hne)).ne' h
    have ha : Real.sqrt (p a).toReal = Real.sqrt (q a).toReal :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
    have htoReal : (p a).toReal = (q a).toReal := by
      have := congrArg (· ^ 2) ha
      rwa [Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg] at this
    exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp htoReal
  · rintro rfl
    simp

theorem bhattacharyya_eq_one_iff (p q : PMF α) : bhattacharyya p q = 1 ↔ p = q := by
  have := hellingerSq_eq_zero_iff p q
  rw [hellingerSq_eq_one_sub_bhattacharyya, sub_eq_zero, eq_comm] at this
  exact this

theorem bhattacharyya_eq_zero_iff (p q : PMF α) :
    bhattacharyya p q = 0 ↔ Disjoint p.support q.support := by
  rw [bhattacharyya_eq_tsum, Set.disjoint_left]
  refine ⟨fun h a hap haq => ?_, fun h => ?_⟩
  · have hsqrt : Real.sqrt ((p a).toReal * (q a).toReal) = 0 := by
      by_contra hne
      exact ((summable_sqrt_toReal_mul p q).tsum_pos (fun _ => Real.sqrt_nonneg _) a
        ((Real.sqrt_nonneg _).lt_of_ne' hne)).ne' h
    have hmul : (p a).toReal * (q a).toReal = 0 :=
      (Real.sqrt_eq_zero (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).mp hsqrt
    rcases mul_eq_zero.mp hmul with hp0 | hq0
    · exact hap ((ENNReal.toReal_eq_zero_iff _).mp hp0 |>.resolve_right (p.apply_ne_top a))
    · exact haq ((ENNReal.toReal_eq_zero_iff _).mp hq0 |>.resolve_right (q.apply_ne_top a))
  · have hzero : ∀ a, Real.sqrt ((p a).toReal * (q a).toReal) = 0 := fun a => by
      by_cases hap : a ∈ p.support
      · have haq : q a = 0 := (PMF.apply_eq_zero_iff q a).mpr (h hap)
        simp [haq]
      · have hp0 : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr hap
        simp [hp0]
    simp [hzero]

theorem bhattacharyya_pure_left (a : α) (q : PMF α) :
    bhattacharyya (PMF.pure a) q = Real.sqrt (q a).toReal := by
  classical
  rw [bhattacharyya_eq_tsum, tsum_eq_single a]
  · simp
  · intro x hx
    simp [PMF.pure_apply, hx]

theorem bhattacharyya_pure_right (p : PMF α) (a : α) :
    bhattacharyya p (PMF.pure a) = Real.sqrt (p a).toReal := by
  rw [bhattacharyya_comm, bhattacharyya_pure_left]

theorem hellingerDist_eq_sqrt_hellingerSq (p q : PMF α) :
    hellingerDist p q = Real.sqrt (hellingerSq p q) := by
  unfold hellingerDist
  rfl

theorem hellingerDist_eq_sqrt_one_sub_bhattacharyya (p q : PMF α) :
    hellingerDist p q = Real.sqrt (1 - bhattacharyya p q) := by
  unfold hellingerDist hellingerSq
  rfl

@[simp]
theorem hellingerDist_sq (p q : PMF α) : hellingerDist p q ^ 2 = hellingerSq p q :=
  Real.sq_sqrt (hellingerSq_nonneg p q)

theorem hellingerDist_nonneg (p q : PMF α) : 0 ≤ hellingerDist p q :=
  Real.sqrt_nonneg _

theorem hellingerDist_le_one (p q : PMF α) : hellingerDist p q ≤ 1 := by
  rw [hellingerDist_eq_sqrt_hellingerSq]
  exact Real.sqrt_le_one.mpr (hellingerSq_le_one p q)

theorem hellingerDist_comm (p q : PMF α) : hellingerDist p q = hellingerDist q p := by
  simp only [hellingerDist, hellingerSq_comm]

@[simp]
theorem hellingerDist_self (p : PMF α) : hellingerDist p p = 0 := by
  simp only [hellingerDist, hellingerSq_self, Real.sqrt_zero]

theorem hellingerDist_eq_zero_iff (p q : PMF α) : hellingerDist p q = 0 ↔ p = q := by
  rw [hellingerDist_eq_sqrt_hellingerSq, Real.sqrt_eq_zero (hellingerSq_nonneg p q),
    hellingerSq_eq_zero_iff]

/-- The Hellinger distance satisfies the triangle inequality on finite types. -/
theorem hellingerDist_triangle [Finite α] (p q r : PMF α) :
    hellingerDist p r ≤ hellingerDist p q + hellingerDist q r := by
  let := Fintype.ofFinite α
  let u : α → ℝ := fun a => Real.sqrt (p a).toReal - Real.sqrt (q a).toReal
  let v : α → ℝ := fun a => Real.sqrt (q a).toReal - Real.sqrt (r a).toReal
  have huv_pr : ∑ a, (u a + v a) ^ 2 = 2 * hellingerSq p r := by
    rw [hellingerSq_eq_sum]
    have hpt (a : α) : (u a + v a) ^ 2 = (Real.sqrt (p a).toReal - Real.sqrt (r a).toReal) ^ 2 := by
      simp [u, v]
    simp_rw [hpt]
    ring
  have hu2 : ∑ a, u a ^ 2 = 2 * hellingerSq p q := by
    rw [hellingerSq_eq_sum]
    ring
  have hv2 : ∑ a, v a ^ 2 = 2 * hellingerSq q r := by
    rw [hellingerSq_eq_sum]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α) u v
  rw [hu2, hv2] at hcs
  have hdot : ∑ a, u a * v a ≤ 2 * (hellingerDist p q * hellingerDist q r) := by
    have hsq : (∑ a, u a * v a) ^ 2 ≤ (2 * (hellingerDist p q * hellingerDist q r)) ^ 2 := by
      calc (∑ a, u a * v a) ^ 2
        _ ≤ (2 * hellingerSq p q) * (2 * hellingerSq q r) := hcs
        _ = (2 * (hellingerDist p q * hellingerDist q r)) ^ 2 := by
          rw [mul_pow, mul_pow, hellingerDist_sq, hellingerDist_sq]
          ring
    exact le_of_sq_le_sq hsq
      (mul_nonneg (by positivity)
        (mul_nonneg (hellingerDist_nonneg _ _) (hellingerDist_nonneg _ _)))
  have hexp : ∑ a, (u a + v a) ^ 2 = ∑ a, u a ^ 2 + 2 * ∑ a, u a * v a + ∑ a, v a ^ 2 := by
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [mul_assoc]
  have hsq_le : hellingerSq p r ≤ (hellingerDist p q + hellingerDist q r) ^ 2 := by
    have hpq : hellingerSq p q = hellingerDist p q ^ 2 := (hellingerDist_sq p q).symm
    have hqr : hellingerSq q r = hellingerDist q r ^ 2 := (hellingerDist_sq q r).symm
    linarith
  exact Real.sqrt_le_iff.mpr ⟨add_nonneg (hellingerDist_nonneg _ _) (hellingerDist_nonneg _ _),
    hsq_le⟩

/-- Lower bound on half-`L¹` statistical distance: `h²(p, q) ≤ dist p q`. -/
theorem hellingerSq_le_dist [Fintype α] (p q : PMF α) :
    hellingerSq p q ≤ dist p q := by
  rw [hellingerSq_eq_sum, dist_eq]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
  rw [abs_toReal_sub_eq, ← sq_abs, sq]
  have habs_le : |Real.sqrt (p a).toReal - Real.sqrt (q a).toReal| ≤
      Real.sqrt (p a).toReal + Real.sqrt (q a).toReal := by
    rw [abs_le]
    constructor <;> linarith [Real.sqrt_nonneg (p a).toReal, Real.sqrt_nonneg (q a).toReal]
  exact mul_le_mul_of_nonneg_left habs_le (abs_nonneg _)

/-- Le Cam's sharp upper bound relating statistical distance and Hellinger distance:
`dist p q ^ 2 ≤ hellingerSq p q * (2 - hellingerSq p q)`. -/
theorem dist_sq_le_hellingerSq_mul_two_sub [Fintype α] (p q : PMF α) :
    dist p q ^ 2 ≤ hellingerSq p q * (2 - hellingerSq p q) := by
  have hpt (a : α) : |(p a).toReal - (q a).toReal| =
      |Real.sqrt (p a).toReal - Real.sqrt (q a).toReal| *
        (Real.sqrt (p a).toReal + Real.sqrt (q a).toReal) :=
    abs_toReal_sub_eq p q a
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => |Real.sqrt (p a).toReal - Real.sqrt (q a).toReal|)
    (fun a => Real.sqrt (p a).toReal + Real.sqrt (q a).toReal)
  have hsum1 : ∑ a, |Real.sqrt (p a).toReal - Real.sqrt (q a).toReal| ^ 2 =
      2 * hellingerSq p q := by
    simp_rw [sq_abs]
    rw [hellingerSq_eq_sum]
    ring
  have hsum2 : ∑ a, (Real.sqrt (p a).toReal + Real.sqrt (q a).toReal) ^ 2 =
      4 - 2 * hellingerSq p q := by
    have hpt2 (a : α) : (Real.sqrt (p a).toReal + Real.sqrt (q a).toReal) ^ 2 =
        (p a).toReal + (q a).toReal + 2 * Real.sqrt ((p a).toReal * (q a).toReal) := by
      rw [Real.sqrt_mul ENNReal.toReal_nonneg]
      nlinarith [Real.mul_self_sqrt (ENNReal.toReal_nonneg (a := p a)),
        Real.mul_self_sqrt (ENNReal.toReal_nonneg (a := q a))]
    simp_rw [hpt2]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_toReal, sum_toReal, ← bhattacharyya_eq_sum, hellingerSq_eq_one_sub_bhattacharyya]
    ring
  rw [hsum1, hsum2] at hcs
  have hdist : (∑ a, |(p a).toReal - (q a).toReal|) = 2 * dist p q := by
    rw [dist_eq]
    ring
  simp_rw [← hpt] at hcs
  rw [hdist] at hcs
  linarith

/-- Le Cam's sharp upper bound: `dist p q ≤ h(p, q) * √(2 - h²(p, q))`. -/
theorem dist_le_hellingerDist_mul_sqrt_two_sub_hellingerSq [Fintype α] (p q : PMF α) :
    dist p q ≤ hellingerDist p q * Real.sqrt (2 - hellingerSq p q) := by
  have h := Real.le_sqrt_of_sq_le (dist_sq_le_hellingerSq_mul_two_sub p q)
  rwa [Real.sqrt_mul (hellingerSq_nonneg p q)] at h

/-- Upper bound on half-`L¹` statistical distance: `dist p q ≤ √2 * hellingerDist p q`. -/
theorem dist_le_sqrt_two_mul_hellingerDist [Fintype α] (p q : PMF α) :
    dist p q ≤ Real.sqrt 2 * hellingerDist p q := by
  refine (dist_le_hellingerDist_mul_sqrt_two_sub_hellingerSq p q).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (hellingerDist_nonneg p q)
  exact Real.sqrt_le_sqrt (by linarith [hellingerSq_nonneg p q])

/-- Lower bound on Mathlib's full-`L¹` total variation distance: `2 * h²(p, q) ≤ tvDist p q`. -/
theorem two_mul_hellingerSq_le_tvDist [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) :
    2 * hellingerSq p q ≤ MeasureTheory.tvDist p.toMeasure q.toMeasure := by
  let := Fintype.ofFinite α
  have h := hellingerSq_le_dist p q
  rw [dist_eq_tvDist_toMeasure_div_two] at h
  linarith

/-- Upper bound on Mathlib's full-`L¹` total variation distance:
`tvDist p q ≤ 2 * √2 * hellingerDist p q`. -/
theorem tvDist_le_two_mul_sqrt_two_mul_hellingerDist [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α) :
    MeasureTheory.tvDist p.toMeasure q.toMeasure ≤ 2 * Real.sqrt 2 * hellingerDist p q := by
  let := Fintype.ofFinite α
  have h := dist_le_sqrt_two_mul_hellingerDist p q
  rw [dist_eq_tvDist_toMeasure_div_two] at h
  linarith

/-- Tensorization of the Bhattacharyya coefficient over finite independent products:
`BC(pi p, pi q) = ∏ i, BC(p i, q i)`. -/
theorem bhattacharyya_pi [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p q : ∀ i, PMF (α i)) :
    bhattacharyya (pi p) (pi q) = ∏ i, bhattacharyya (p i) (q i) := by
  let (i : ι) := Fintype.ofFinite (α i)
  classical
  rw [bhattacharyya_eq_sum]
  have hterm (u : ∀ i, α i) :
      Real.sqrt (((pi p u).toReal) * ((pi q u).toReal)) =
        ∏ i, Real.sqrt ((p i (u i)).toReal * (q i (u i)).toReal) := by
    simp only [pi_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
    exact Real.sqrt_prod Finset.univ (fun i _ =>
      mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i a => Real.sqrt ((p i a).toReal * (q i a).toReal))]
  simp_rw [← bhattacharyya_eq_sum]

/-- Tensorization of the Bhattacharyya coefficient for `n` i.i.d. draws:
`BC(iid p n, iid q n) = BC(p, q) ^ n`. -/
theorem bhattacharyya_iid [Finite α] (p q : PMF α) (n : ℕ) :
    bhattacharyya (iid p n) (iid q n) = bhattacharyya p q ^ n := by
  rw [iid_eq_pi, iid_eq_pi, bhattacharyya_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exact formula for the squared Hellinger distance between finite product distributions. -/
theorem hellingerSq_pi [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p q : ∀ i, PMF (α i)) :
    hellingerSq (pi p) (pi q) = 1 - ∏ i, (1 - hellingerSq (p i) (q i)) := by
  rw [hellingerSq_eq_one_sub_bhattacharyya, bhattacharyya_pi]
  refine congrArg (1 - ·) (Finset.prod_congr rfl fun i _ => ?_)
  rw [hellingerSq_eq_one_sub_bhattacharyya]
  ring

/-- Subadditivity of squared Hellinger distance for finite independent products. -/
theorem hellingerSq_pi_le_sum [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p q : ∀ i, PMF (α i)) :
    hellingerSq (pi p) (pi q) ≤ ∑ i, hellingerSq (p i) (q i) := by
  rw [hellingerSq_eq_one_sub_bhattacharyya, bhattacharyya_pi]
  refine (one_sub_prod_le_sum_one_sub Finset.univ (fun i => bhattacharyya (p i) (q i))
    (fun i _ => bhattacharyya_nonneg _ _) (fun i _ => bhattacharyya_le_one _ _)).2.2.trans_eq ?_
  rfl

/-- Exact formula for the squared Hellinger distance between `n`-fold i.i.d. distributions. -/
theorem hellingerSq_iid [Finite α] (p q : PMF α) (n : ℕ) :
    hellingerSq (iid p n) (iid q n) = 1 - (1 - hellingerSq p q) ^ n := by
  rw [hellingerSq_eq_one_sub_bhattacharyya, bhattacharyya_iid, hellingerSq_eq_one_sub_bhattacharyya]
  ring_nf

/-- Subadditivity of squared Hellinger distance for `n`-fold i.i.d. distributions. -/
theorem hellingerSq_iid_le [Finite α] (p q : PMF α) (n : ℕ) :
    hellingerSq (iid p n) (iid q n) ≤ n * hellingerSq p q := by
  rw [iid_eq_pi, iid_eq_pi]
  simpa using hellingerSq_pi_le_sum (fun _ : Fin n => p) (fun _ : Fin n => q)

/-- Subadditivity of Hellinger distance for `n`-fold i.i.d. distributions:
`h(iid p n, iid q n) ≤ √n * h(p, q)`. -/
theorem hellingerDist_iid_le [Finite α] (p q : PMF α) (n : ℕ) :
    hellingerDist (iid p n) (iid q n) ≤ Real.sqrt n * hellingerDist p q := by
  rw [hellingerDist_eq_sqrt_hellingerSq, hellingerDist_eq_sqrt_hellingerSq,
    ← Real.sqrt_mul (Nat.cast_nonneg n)]
  exact Real.sqrt_le_sqrt (hellingerSq_iid_le p q n)

/-- Product-distribution TV bound via squared Hellinger distance:
`dist (pi p) (pi q) ≤ √(2 * ∑ i, h²(p i, q i))`. -/
theorem dist_pi_le_sqrt_two_mul_sum_hellingerSq [DecidableEq ι] [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (p q : ∀ i, PMF (α i)) :
    dist (pi p) (pi q) ≤ Real.sqrt (2 * ∑ i, hellingerSq (p i) (q i)) := by
  refine (dist_le_sqrt_two_mul_hellingerDist (pi p) (pi q)).trans ?_
  rw [hellingerDist_eq_sqrt_hellingerSq, ← Real.sqrt_mul (by norm_num)]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hellingerSq_pi_le_sum p q) (by norm_num))

/-- Acceptance bound for `n` i.i.d. samples:
`dist (iid p n) (iid q n) ≤ √(2 * n) * hellingerDist p q`. -/
theorem dist_iid_le_sqrt_two_mul_nat_mul_hellingerDist [Fintype α] (p q : PMF α) (n : ℕ) :
    dist (iid p n) (iid q n) ≤ Real.sqrt (2 * n) * hellingerDist p q := by
  refine (dist_le_sqrt_two_mul_hellingerDist (iid p n) (iid q n)).trans ?_
  refine (mul_le_mul_of_nonneg_left (hellingerDist_iid_le p q n) (Real.sqrt_nonneg 2)).trans_eq ?_
  rw [← mul_assoc, ← Real.sqrt_mul (by norm_num)]

/-- Joint concavity of the Bhattacharyya coefficient under mixing with weights `μ`. -/
theorem sum_mul_bhattacharyya_le_bhattacharyya_bind [Finite α] [Finite β]
    (μ : PMF α) (p q : α → PMF β) :
    ∑' a, (μ a).toReal * bhattacharyya (p a) (q a) ≤ bhattacharyya (μ.bind p) (μ.bind q) := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [tsum_fintype, bhattacharyya_eq_sum]
  simp_rw [bhattacharyya_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  have hpt (a : α) :
      (μ a).toReal * Real.sqrt ((p a b).toReal * (q a b).toReal) =
        Real.sqrt ((μ a).toReal * (p a b).toReal) * Real.sqrt ((μ a).toReal * (q a b).toReal) :=
    (sqrt_mul_left_mul_sqrt_mul_left ENNReal.toReal_nonneg ENNReal.toReal_nonneg).symm
  simp_rw [hpt]
  have hcs := (Real.sum_sqrt_mul_sqrt_le Finset.univ
    (f := fun a => (μ a).toReal * (p a b).toReal)
    (g := fun a => (μ a).toReal * (q a b).toReal)
    (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).trans_eq
    (Real.sqrt_mul
      (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) _).symm
  simpa only [← bind_apply_toReal] using hcs

/-- Joint convexity of squared Hellinger distance under mixing with weights `μ`. -/
theorem hellingerSq_bind_le_sum [Finite α] [Finite β] (μ : PMF α) (p q : α → PMF β) :
    hellingerSq (μ.bind p) (μ.bind q) ≤ ∑' a, (μ a).toReal * hellingerSq (p a) (q a) := by
  let := Fintype.ofFinite α
  have h := sum_mul_bhattacharyya_le_bhattacharyya_bind μ p q
  rw [tsum_fintype] at h ⊢
  simp_rw [hellingerSq_eq_one_sub_bhattacharyya, mul_sub, mul_one, Finset.sum_sub_distrib,
    sum_toReal]
  linarith

/-- Data processing inequality for the Bhattacharyya coefficient: applying a shared Markov kernel
`kernel` never decreases `bhattacharyya`. -/
theorem bhattacharyya_le_bhattacharyya_bind [Finite α] [Finite β]
    (p q : PMF α) (kernel : α → PMF β) :
    bhattacharyya p q ≤ bhattacharyya (p.bind kernel) (q.bind kernel) := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [bhattacharyya_eq_sum, bhattacharyya_eq_sum]
  have hrewrite :
      ∑ a, Real.sqrt ((p a).toReal * (q a).toReal) =
        ∑ b, ∑ a, Real.sqrt ((p a).toReal * (kernel a b).toReal) *
          Real.sqrt ((q a).toReal * (kernel a b).toReal) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hpt (b : β) :
        Real.sqrt ((p a).toReal * (kernel a b).toReal) *
          Real.sqrt ((q a).toReal * (kernel a b).toReal) =
          Real.sqrt ((p a).toReal * (q a).toReal) * (kernel a b).toReal := by
      rw [mul_comm (p a).toReal, mul_comm (q a).toReal,
        sqrt_mul_left_mul_sqrt_mul_left ENNReal.toReal_nonneg ENNReal.toReal_nonneg, mul_comm]
    simp_rw [hpt, ← Finset.mul_sum, sum_toReal, mul_one]
  rw [hrewrite]
  refine Finset.sum_le_sum fun b _ => ?_
  have hcs := (Real.sum_sqrt_mul_sqrt_le Finset.univ
    (f := fun a => (p a).toReal * (kernel a b).toReal)
    (g := fun a => (q a).toReal * (kernel a b).toReal)
    (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).trans_eq
    (Real.sqrt_mul
      (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) _).symm
  simpa only [← bind_apply_toReal] using hcs

/-- Data processing inequality for squared Hellinger distance under a Markov kernel. -/
theorem hellingerSq_bind_le [Finite α] [Finite β] (p q : PMF α) (kernel : α → PMF β) :
    hellingerSq (p.bind kernel) (q.bind kernel) ≤ hellingerSq p q := by
  simp only [hellingerSq_eq_one_sub_bhattacharyya]
  linarith [bhattacharyya_le_bhattacharyya_bind p q kernel]

/-- Data processing inequality for Hellinger distance under a Markov kernel. -/
theorem hellingerDist_bind_le [Finite α] [Finite β] (p q : PMF α) (kernel : α → PMF β) :
    hellingerDist (p.bind kernel) (q.bind kernel) ≤ hellingerDist p q :=
  Real.sqrt_le_sqrt (hellingerSq_bind_le p q kernel)

/-- Data processing inequality for the Bhattacharyya coefficient under deterministic maps. -/
theorem bhattacharyya_le_bhattacharyya_map [Finite α] [Finite β]
    (p q : PMF α) (f : α → β) :
    bhattacharyya p q ≤ bhattacharyya (p.map f) (q.map f) := by
  simpa only [PMF.map, Function.comp_def] using
    bhattacharyya_le_bhattacharyya_bind p q (fun a => PMF.pure (f a))

/-- Data processing inequality for squared Hellinger distance under deterministic maps. -/
theorem hellingerSq_map_le [Finite α] [Finite β] (p q : PMF α) (f : α → β) :
    hellingerSq (p.map f) (q.map f) ≤ hellingerSq p q :=
  by
    simp only [hellingerSq_eq_one_sub_bhattacharyya]
    linarith [bhattacharyya_le_bhattacharyya_map p q f]

/-- Data processing inequality for Hellinger distance under deterministic maps. -/
theorem hellingerDist_map_le [Finite α] [Finite β] (p q : PMF α) (f : α → β) :
    hellingerDist (p.map f) (q.map f) ≤ hellingerDist p q :=
  Real.sqrt_le_sqrt (hellingerSq_map_le p q f)

/-- Injective relabeling preserves the Bhattacharyya coefficient. -/
theorem bhattacharyya_map_of_injective [Finite α] [Finite β]
    (p q : PMF α) {f : α → β} (hf : Function.Injective f) :
    bhattacharyya (p.map f) (q.map f) = bhattacharyya p q := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  classical
  have hmass (r : PMF α) (a : α) : (r.map f) (f a) = r a := by
    simp only [PMF.map_apply, hf.eq_iff, tsum_ite_eq']
  have hzero (r : PMF α) (b : β) (hb : b ∉ Set.range f) : (r.map f) b = 0 := by
    rw [PMF.apply_eq_zero_iff, PMF.support_map]
    exact fun ⟨a, _, ha⟩ => hb ⟨a, ha⟩
  rw [bhattacharyya_eq_sum, bhattacharyya_eq_sum]
  exact (Fintype.sum_of_injective f hf _ _
    (fun b hb => by rw [hzero p b hb, hzero q b hb]; simp)
    (fun a => by rw [hmass, hmass])).symm

/-- Injective relabeling preserves squared Hellinger distance. -/
theorem hellingerSq_map_of_injective [Finite α] [Finite β]
    (p q : PMF α) {f : α → β} (hf : Function.Injective f) :
    hellingerSq (p.map f) (q.map f) = hellingerSq p q := by
  simp only [hellingerSq_eq_one_sub_bhattacharyya, bhattacharyya_map_of_injective p q hf]

/-- Injective relabeling preserves Hellinger distance. -/
theorem hellingerDist_map_of_injective [Finite α] [Finite β]
    (p q : PMF α) {f : α → β} (hf : Function.Injective f) :
    hellingerDist (p.map f) (q.map f) = hellingerDist p q := by
  simp only [hellingerDist_eq_sqrt_hellingerSq, hellingerSq_map_of_injective p q hf]

end Cslib.Probability.PMF
