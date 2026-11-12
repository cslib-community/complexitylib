/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.Divergence
public import CslibFrontier.Probability.Hellinger
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.StatisticalDistance
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Chi-square divergence for discrete distributions

The Pearson `χ²` divergence `χ²(p ‖ q)` of `p : PMF α` with respect to reference distribution
`q : PMF α` (corresponding to `exp(D₂(p ‖ q)) - 1`, where `D₂` is Rényi divergence of order `2`):
* `echiSquare p q : ℝ≥0∞` equals `∑' a, ENNReal.ofReal (((p a).toReal - (q a).toReal) ^ 2) / q a`,
  so it is `⊤` whenever `p.support` is not contained in `q.support` (on finite types).
* `chiSquare p q : ℝ` is `(echiSquare p q).toReal`. Real-valued upper bounds and identities
  state `p.support ⊆ q.support` explicitly so off-support terms cannot silently vanish via
  `x / 0 = 0`.

Note that the reference/denominator distribution `q` is the **second** argument, matching
`MeasureTheory.InformationTheory.klDiv p.toMeasure q.toMeasure`.

## Main definitions

* `Cslib.Probability.PMF.echiSquare`: extended `ℝ≥0∞`-valued `χ²` divergence `χ²(p ‖ q)`.
* `Cslib.Probability.PMF.chiSquare`: real-valued `χ²` divergence `(echiSquare p q).toReal`.

## Main results

* `Cslib.Probability.PMF.echiSquare_ne_top_iff`: `echiSquare p q ≠ ⊤ ↔ p.support ⊆ q.support`.
* `Cslib.Probability.PMF.chiSquare_eq_sum`, `chiSquare_eq_sum_div_sub_one`,
  `one_add_chiSquare_eq_sum`: standard finite-sum formulas when `p.support ⊆ q.support`.
* `Cslib.Probability.PMF.one_add_echiSquare_pi`, `one_add_chiSquare_pi`,
  `one_add_echiSquare_iid`, `one_add_chiSquare_iid`: product and `iid` tensorization
  `1 + χ²(p^{\otimes n} ‖ q^{\otimes n}) = (1 + χ²(p ‖ q)) ^ n`.
* `Cslib.Probability.PMF.ofReal_four_mul_dist_sq_le_echiSquare`, `dist_le_sqrt_chiSquare_div_two`,
  `tvDist_le_sqrt_chiSquare`: `TV ≤ √(χ²) / 2` (for half-`L¹` `dist` and full-`L¹` `tvDist`).
* `Cslib.Probability.PMF.echiSquare_bind_le`, `chiSquare_bind_le`, `chiSquare_map_le`:
  data processing under Markov kernels and deterministic maps.
* `Cslib.Probability.PMF.one_add_chiSquare_bind_eq`, `one_add_chiSquare_bind_iid_eq`:
  the mixture second-moment identity (`Ingster` / `Le Cam`).
* `Cslib.Probability.PMF.two_mul_hellingerSq_le_toReal_klDiv`,
  `toReal_klDiv_le_log_one_add_chiSquare`, `toReal_klDiv_le_chiSquare`,
  `two_mul_hellingerSq_le_chiSquare`: comparison hierarchy `2 h² ≤ KL ≤ log(1 + χ²) ≤ χ²`.

## References

* [Alexandre B. Tsybakov, *Introduction to Nonparametric Estimation*][Tsybakov2009], Springer,
  2009, Section 2.4.
* [Clément L. Canonne, *Topics and Techniques in Distribution Testing*][Canonne2022], Foundations
  and Trends in Communications and Information Theory, 2022; locators checked against the
  author-hosted draft (March 10, 2024): Appendix B (Definition B.1, `(B.2)`, `(B.5)`, Lemmas B.2
  and B.5) and Section 3.1 (Lemma 3.1 and `(3.10)`).
-/

public section

namespace Cslib.Probability.PMF

open Finset MeasureTheory InformationTheory
open scoped BigOperators Cslib.Probability.PMF ENNReal

variable {α β θ ι : Type*}

private lemma sum_sub_sq_div_eq_sum_sq_div_sub_one [Fintype α] {p q : PMF α}
    (h : p.support ⊆ q.support) :
    ∑ a, ((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal =
      (∑ a, (p a).toReal ^ 2 / (q a).toReal) - 1 := by
  have hpt (a : α) :
      ((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal =
        (p a).toReal ^ 2 / (q a).toReal - 2 * (p a).toReal + (q a).toReal := by
    by_cases ha : q a = 0
    · have hpa : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr
        (fun hap => (PMF.apply_eq_zero_iff q a).mp ha (h hap))
      simp [ha, hpa]
    · have hqpos : (q a).toReal ≠ 0 :=
        ((ENNReal.toReal_pos ha (q.apply_ne_top a)).ne')
      field_simp
      ring
  simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_toReal]
  ring

private lemma finset_prod_sq_div (s : Finset ι) (f g : ι → ℝ≥0∞)
    (hf : ∀ i ∈ s, f i ≠ ⊤) (hg : ∀ i ∈ s, g i ≠ ⊤) :
    (∏ i ∈ s, f i) ^ 2 / ∏ i ∈ s, g i = ∏ i ∈ s, f i ^ 2 / g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hfi : f i ≠ ⊤ := hf i (Finset.mem_insert_self i s)
    have hgi : g i ≠ ⊤ := hg i (Finset.mem_insert_self i s)
    have hfs : ∏ j ∈ s, f j ≠ ⊤ :=
      ENNReal.prod_ne_top fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hgs : ∏ j ∈ s, g j ≠ ⊤ :=
      ENNReal.prod_ne_top fun j hj => hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, mul_pow,
      ← ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hg j (Finset.mem_insert_of_mem hj))]
    have htwo {a b c d : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hd : d ≠ ⊤) :
        (a * b) / (c * d) = (a / c) * (b / d) := by
      by_cases ha0 : a = 0
      · simp [ha0]
      by_cases hb0 : b = 0
      · simp [hb0]
      by_cases hc0 : c = 0
      · have hbd0 : b / d ≠ 0 := by
          intro h0
          rw [ENNReal.div_eq_zero_iff] at h0
          exact h0.elim hb0 hd
        rw [hc0, zero_mul, ENNReal.div_zero (mul_ne_zero ha0 hb0), ENNReal.div_zero ha0,
          ENNReal.top_mul hbd0]
      by_cases hd0 : d = 0
      · have hac0 : a / c ≠ 0 := by
          intro h0
          rw [ENNReal.div_eq_zero_iff] at h0
          exact h0.elim ha0 hc
        rw [hd0, mul_zero, ENNReal.div_zero (mul_ne_zero ha0 hb0), ENNReal.div_zero hb0,
          ENNReal.mul_top hac0]
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl hc0) (Or.inl hc)]
      ring
    exact htwo (ENNReal.pow_ne_top hfi) (ENNReal.pow_ne_top hfs) hgi hgs

/-- Extended Pearson `χ²` divergence of `p` with respect to `q`, valued in `ℝ≥0∞`.
It equals `∑' a, (p a - q a)² / q a` when `p.support ⊆ q.support`, and `⊤` otherwise (on finite
types). -/
noncomputable def echiSquare (p q : PMF α) : ℝ≥0∞ :=
  ∑' a, ENNReal.ofReal (((p a).toReal - (q a).toReal) ^ 2) / q a

/-- Real-valued Pearson `χ²` divergence `(echiSquare p q).toReal` of `p` with respect to `q`.
Real-valued theorems assume `p.support ⊆ q.support` so off-support mass cannot be dropped via
`toReal ⊤ = 0`. -/
noncomputable def chiSquare (p q : PMF α) : ℝ :=
  (echiSquare p q).toReal

theorem echiSquare_eq_tsum (p q : PMF α) :
    echiSquare p q = ∑' a, ENNReal.ofReal (((p a).toReal - (q a).toReal) ^ 2) / q a := by
  unfold echiSquare
  rfl

@[simp]
theorem echiSquare_self (p : PMF α) : echiSquare p p = 0 := by
  simp [echiSquare]

theorem chiSquare_nonneg (p q : PMF α) : 0 ≤ chiSquare p q :=
  ENNReal.toReal_nonneg

@[simp]
theorem chiSquare_self (p : PMF α) : chiSquare p p = 0 := by
  simp [chiSquare]

theorem echiSquare_ne_top_iff [Finite α] {p q : PMF α} :
    echiSquare p q ≠ ⊤ ↔ p.support ⊆ q.support := by
  let := Fintype.ofFinite α
  rw [echiSquare, tsum_fintype, ne_eq, ENNReal.sum_eq_top]
  constructor
  · intro h a hap
    by_contra haq
    apply h
    refine ⟨a, Finset.mem_univ _, ?_⟩
    have hqa0 : q a = 0 := (PMF.apply_eq_zero_iff q a).mpr haq
    have hpa0 : p a ≠ 0 := (PMF.mem_support_iff p a).mp hap
    have hpos : 0 < (p a).toReal := ENNReal.toReal_pos hpa0 (p.apply_ne_top a)
    have hne0 : ENNReal.ofReal (((p a).toReal - (q a).toReal) ^ 2) ≠ 0 := by
      simp [hqa0, hpos]
    rw [hqa0] at hne0 ⊢
    exact ENNReal.div_zero hne0
  · intro h ⟨a, _, ha⟩
    by_cases haq : q a = 0
    · have hpa0 : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr
        (fun hap => (PMF.apply_eq_zero_iff q a).mp haq (h hap))
      simp [haq, hpa0] at ha
    · exact ENNReal.div_ne_top ENNReal.ofReal_ne_top haq ha

theorem echiSquare_eq_top_iff [Finite α] {p q : PMF α} :
    echiSquare p q = ⊤ ↔ ¬ p.support ⊆ q.support := by
  simpa using not_congr (@echiSquare_ne_top_iff α _ p q)

theorem echiSquare_eq_ofReal [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) :
    echiSquare p q = ENNReal.ofReal (chiSquare p q) := by
  rw [chiSquare, ENNReal.ofReal_toReal (echiSquare_ne_top_iff.mpr h)]

theorem chiSquare_eq_sum [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    chiSquare p q = ∑ a, ((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal := by
  rw [chiSquare, echiSquare, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : q a = 0
    · have hpa : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr
        (fun hap => (PMF.apply_eq_zero_iff q a).mp ha (h hap))
      simp [ha, hpa]
    · rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (sq_nonneg _)]
  · intro a _
    by_cases ha : q a = 0
    · have hpa : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr
        (fun hap => (PMF.apply_eq_zero_iff q a).mp ha (h hap))
      simp [ha, hpa]
    · exact ENNReal.div_ne_top ENNReal.ofReal_ne_top ha

theorem chiSquare_eq_sum_div_sub_one [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    chiSquare p q = (∑ a, (p a).toReal ^ 2 / (q a).toReal) - 1 := by
  rw [chiSquare_eq_sum h, sum_sub_sq_div_eq_sum_sq_div_sub_one h]

theorem one_add_chiSquare_eq_sum [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    1 + chiSquare p q = ∑ a, (p a).toReal ^ 2 / (q a).toReal := by
  linarith [chiSquare_eq_sum_div_sub_one h]

theorem chiSquare_eq_zero_iff [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) :
    chiSquare p q = 0 ↔ p = q := by
  let := Fintype.ofFinite α
  rw [chiSquare_eq_sum h, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
    div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)]
  constructor
  · intro hzero
    ext a
    by_cases ha : q a = 0
    · have hpa : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr
        (fun hap => (PMF.apply_eq_zero_iff q a).mp ha (h hap))
      rw [ha, hpa]
    · have hqpos : 0 < (q a).toReal := ENNReal.toReal_pos ha (q.apply_ne_top a)
      have hterm := hzero a (Finset.mem_univ a)
      rw [div_eq_zero_iff] at hterm
      have hsub : (p a).toReal = (q a).toReal :=
        sub_eq_zero.mp (sq_eq_zero_iff.mp (hterm.resolve_right hqpos.ne'))
      exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp hsub
  · rintro rfl a _
    simp

theorem echiSquare_eq_zero_iff [Finite α] {p q : PMF α} : echiSquare p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hsup : p.support ⊆ q.support := echiSquare_ne_top_iff.mp (by simp [h])
    refine (chiSquare_eq_zero_iff hsup).mp ?_
    simp [chiSquare, h]
  · rintro rfl
    exact echiSquare_self p

theorem one_add_echiSquare_eq_tsum [Finite α] (p q : PMF α) :
    1 + echiSquare p q = ∑' a, p a ^ 2 / q a := by
  let := Fintype.ofFinite α
  rw [tsum_fintype]
  by_cases h : p.support ⊆ q.support
  · have hsum_rhs : ∑ a, p a ^ 2 / q a = ENNReal.ofReal (∑ a, (p a).toReal ^ 2 / (q a).toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : q a = 0
      · have hpa : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr
          (fun hap => (PMF.apply_eq_zero_iff q a).mp ha (h hap))
        simp [ha, hpa]
      · rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos ha (q.apply_ne_top a)),
          ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (p.apply_ne_top a),
          ENNReal.ofReal_toReal (q.apply_ne_top a)]
    rw [echiSquare_eq_ofReal h, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (chiSquare_nonneg p q),
      one_add_chiSquare_eq_sum h, hsum_rhs]
  · have htop : echiSquare p q = ⊤ := echiSquare_eq_top_iff.mpr h
    rw [htop, add_top, eq_comm, ENNReal.sum_eq_top]
    rcases Set.not_subset.mp h with ⟨a, hap, haq⟩
    refine ⟨a, Finset.mem_univ _, ?_⟩
    have hpa0 : p a ≠ 0 := (PMF.mem_support_iff p a).mp hap
    have hqa0 : q a = 0 := (PMF.apply_eq_zero_iff q a).mpr haq
    rw [hqa0, ENNReal.div_zero (pow_ne_zero 2 hpa0)]

/-- Multiplicative tensorization of `1 + echiSquare` over finite independent products, valid
without any support assumption. -/
theorem one_add_echiSquare_pi [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p q : ∀ i, PMF (α i)) :
    1 + echiSquare (pi p) (pi q) = ∏ i, (1 + echiSquare (p i) (q i)) := by
  let (i : ι) := Fintype.ofFinite (α i)
  classical
  have h1 : 1 + echiSquare (pi p) (pi q) = ∑ u : ∀ i, α i, pi p u ^ 2 / pi q u := by
    rw [one_add_echiSquare_eq_tsum, tsum_fintype]
  have h2 (i : ι) : 1 + echiSquare (p i) (q i) = ∑ a, p i a ^ 2 / q i a := by
    rw [one_add_echiSquare_eq_tsum, tsum_fintype]
  rw [h1]
  simp_rw [h2, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [pi_apply]
  exact finset_prod_sq_div Finset.univ (fun i => p i (u i)) (fun i => q i (u i))
    (fun i _ => (p i).apply_ne_top _) (fun i _ => (q i).apply_ne_top _)

/-- Tensorization of `1 + chiSquare` over finite independent products:
`1 + χ²(pi p ‖ pi q) = ∏ i, (1 + χ²(p i ‖ q i))`. -/
theorem one_add_chiSquare_pi [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p q : ∀ i, PMF (α i)) (h : ∀ i, (p i).support ⊆ (q i).support) :
    1 + chiSquare (pi p) (pi q) = ∏ i, (1 + chiSquare (p i) (q i)) := by
  have hpi : (pi p).support ⊆ (pi q).support := by
    intro u hu
    rw [mem_support_pi_iff] at hu ⊢
    exact fun i => h i (hu i)
  have hE := one_add_echiSquare_pi p q
  have hL : 1 + echiSquare (pi p) (pi q) = ENNReal.ofReal (1 + chiSquare (pi p) (pi q)) := by
    rw [echiSquare_eq_ofReal hpi, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (chiSquare_nonneg _ _)]
  have hR : ∏ i, (1 + echiSquare (p i) (q i)) =
      ENNReal.ofReal (∏ i, (1 + chiSquare (p i) (q i))) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => add_nonneg zero_le_one (chiSquare_nonneg _ _))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [echiSquare_eq_ofReal (h i), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (chiSquare_nonneg _ _)]
  rw [hL, hR] at hE
  exact (ENNReal.ofReal_eq_ofReal_iff (add_nonneg zero_le_one (chiSquare_nonneg _ _))
    (Finset.prod_nonneg fun _ _ => add_nonneg zero_le_one (chiSquare_nonneg _ _))).mp hE

/-- Multiplicative tensorization of `1 + echiSquare` for `n` i.i.d. draws, valid even when `n = 0`
or supports are not contained. -/
theorem one_add_echiSquare_iid [Finite α] (p q : PMF α) (n : ℕ) :
    1 + echiSquare (iid p n) (iid q n) = (1 + echiSquare p q) ^ n := by
  rw [iid_eq_pi, iid_eq_pi, one_add_echiSquare_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Tensorization of `1 + chiSquare` for `n` i.i.d. draws:
`1 + χ²(iid p n ‖ iid q n) = (1 + χ²(p ‖ q)) ^ n`. -/
theorem one_add_chiSquare_iid [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) (n : ℕ) :
    1 + chiSquare (iid p n) (iid q n) = (1 + chiSquare p q) ^ n := by
  rw [iid_eq_pi, iid_eq_pi, one_add_chiSquare_pi _ _ (fun _ => h), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- Comparison between statistical distance and `χ²` divergence: `4 * (dist p q) ^ 2 ≤ χ²(p ‖ q)`
when `p.support ⊆ q.support`. -/
theorem four_mul_dist_sq_le_chiSquare [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    4 * dist p q ^ 2 ≤ chiSquare p q := by
  have hpt (a : α) : |(p a).toReal - (q a).toReal| =
      (|(p a).toReal - (q a).toReal| / Real.sqrt (q a).toReal) * Real.sqrt (q a).toReal := by
    by_cases ha : q a = 0
    · have hpa : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr
        (fun hap => (PMF.apply_eq_zero_iff q a).mp ha (h hap))
      simp [ha, hpa]
    · have hqpos : 0 < Real.sqrt (q a).toReal :=
        Real.sqrt_pos.mpr (ENNReal.toReal_pos ha (q.apply_ne_top a))
      rw [div_mul_cancel₀ _ hqpos.ne']
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => |(p a).toReal - (q a).toReal| / Real.sqrt (q a).toReal)
    (fun a => Real.sqrt (q a).toReal)
  simp_rw [← hpt] at hcs
  have hleft : (∑ a, |(p a).toReal - (q a).toReal|) ^ 2 = 4 * dist p q ^ 2 := by
    rw [dist_eq]
    ring
  have hchi : ∑ a, (|(p a).toReal - (q a).toReal| / Real.sqrt (q a).toReal) ^ 2 =
      chiSquare p q := by
    rw [chiSquare_eq_sum h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [div_pow, sq_abs, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hnorm : ∑ a, Real.sqrt (q a).toReal ^ 2 = 1 := by
    simp_rw [Real.sq_sqrt ENNReal.toReal_nonneg, sum_toReal]
  rw [hleft, hchi, hnorm, mul_one] at hcs
  exact hcs

/-- Upper bound on half-`L¹` statistical distance via `χ²`:
`dist p q ≤ √(χ²(p ‖ q)) / 2` when `p.support ⊆ q.support`. -/
theorem dist_le_sqrt_chiSquare_div_two [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    dist p q ≤ Real.sqrt (chiSquare p q) / 2 := by
  have hsq : dist p q ^ 2 ≤ chiSquare p q / 4 := by linarith [four_mul_dist_sq_le_chiSquare h]
  have hle := Real.le_sqrt_of_sq_le hsq
  rwa [Real.sqrt_div (chiSquare_nonneg p q),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at hle

/-- Unconditional extended inequality `ENNReal.ofReal (4 * dist p q ^ 2) ≤ echiSquare p q`. -/
theorem ofReal_four_mul_dist_sq_le_echiSquare [Fintype α] (p q : PMF α) :
    ENNReal.ofReal (4 * dist p q ^ 2) ≤ echiSquare p q := by
  by_cases h : p.support ⊆ q.support
  · rw [echiSquare_eq_ofReal h]
    exact ENNReal.ofReal_le_ofReal (four_mul_dist_sq_le_chiSquare h)
  · rw [echiSquare_eq_top_iff.mpr h]
    exact le_top

/-- Upper bound on Mathlib's full-`L¹` total variation distance via `χ²`:
`tvDist p q ≤ √(χ²(p ‖ q))` when `p.support ⊆ q.support`. -/
theorem tvDist_le_sqrt_chiSquare [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {p q : PMF α} (h : p.support ⊆ q.support) :
    MeasureTheory.tvDist p.toMeasure q.toMeasure ≤ Real.sqrt (chiSquare p q) := by
  let := Fintype.ofFinite α
  have hd := dist_le_sqrt_chiSquare_div_two h
  rw [dist_eq_tvDist_toMeasure_div_two] at hd
  linarith

private lemma support_bind_subset {μ ν : PMF α} (h : μ.support ⊆ ν.support)
    (kernel : α → PMF β) :
    (μ.bind kernel).support ⊆ (ν.bind kernel).support := by
  intro b hb
  rw [PMF.support_bind, Set.mem_iUnion₂] at hb ⊢
  rcases hb with ⟨a, ha, hba⟩
  exact ⟨a, h ha, hba⟩

/-- Data processing inequality for `χ²` divergence under a Markov kernel (real-valued). -/
theorem chiSquare_bind_le [Finite α] [Finite β] {p q : PMF α} (h : p.support ⊆ q.support)
    (kernel : α → PMF β) :
    chiSquare (p.bind kernel) (q.bind kernel) ≤ chiSquare p q := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  have hbind : (p.bind kernel).support ⊆ (q.bind kernel).support :=
    support_bind_subset h kernel
  suffices hsum : 1 + chiSquare (p.bind kernel) (q.bind kernel) ≤ 1 + chiSquare p q by linarith
  rw [one_add_chiSquare_eq_sum hbind, one_add_chiSquare_eq_sum h]
  have hpt (b : β) :
      ((p.bind kernel b).toReal) ^ 2 / (q.bind kernel b).toReal ≤
        ∑ a, (p a).toReal ^ 2 / (q a).toReal * (kernel a b).toReal := by
    by_cases hqb : q.bind kernel b = 0
    · have hpb : p.bind kernel b = 0 := (PMF.apply_eq_zero_iff (p.bind kernel) b).mpr
        (fun hmem => (PMF.apply_eq_zero_iff (q.bind kernel) b).mp hqb (hbind hmem))
      rw [hqb, hpb]
      simp only [ENNReal.toReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_div]
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg (div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    · have hqb_pos : 0 < (q.bind kernel b).toReal :=
        ENNReal.toReal_pos hqb ((q.bind kernel).apply_ne_top b)
      have hrewrite : (p.bind kernel b).toReal =
          ∑ a, ((p a).toReal * Real.sqrt (kernel a b).toReal / Real.sqrt (q a).toReal) *
            Real.sqrt ((q a).toReal * (kernel a b).toReal) := by
        rw [bind_apply_toReal]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hqa : q a = 0
        · have hpa : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr
            (fun hap => (PMF.apply_eq_zero_iff q a).mp hqa (h hap))
          simp [hqa, hpa]
        · have hqapos : 0 < Real.sqrt (q a).toReal :=
            Real.sqrt_pos.mpr (ENNReal.toReal_pos hqa (q.apply_ne_top a))
          calc (p a).toReal * ((kernel a b).toReal)
            _ = (p a).toReal * (Real.sqrt (kernel a b).toReal * Real.sqrt (kernel a b).toReal) *
                  (Real.sqrt (q a).toReal / Real.sqrt (q a).toReal) := by
                rw [Real.mul_self_sqrt ENNReal.toReal_nonneg, div_self hqapos.ne', mul_one]
            _ = (p a).toReal * Real.sqrt (kernel a b).toReal / Real.sqrt (q a).toReal *
                  Real.sqrt ((q a).toReal * (kernel a b).toReal) := by
                rw [Real.sqrt_mul ENNReal.toReal_nonneg]
                ring
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
        (fun a => (p a).toReal * Real.sqrt (kernel a b).toReal / Real.sqrt (q a).toReal)
        (fun a => Real.sqrt ((q a).toReal * (kernel a b).toReal))
      rw [← hrewrite] at hcs
      have hleft :
          ∑ a, ((p a).toReal * Real.sqrt (kernel a b).toReal / Real.sqrt (q a).toReal) ^ 2 =
          ∑ a, (p a).toReal ^ 2 / (q a).toReal * (kernel a b).toReal := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [div_pow, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg,
          Real.sq_sqrt ENNReal.toReal_nonneg]
        ring
      have hright : ∑ a, Real.sqrt ((q a).toReal * (kernel a b).toReal) ^ 2 =
          (q.bind kernel b).toReal := by
        rw [bind_apply_toReal]
        exact Finset.sum_congr rfl fun a _ =>
          Real.sq_sqrt (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      rw [hleft, hright] at hcs
      exact (div_le_iff₀ hqb_pos).mpr hcs
  calc ∑ b, ((p.bind kernel b).toReal) ^ 2 / (q.bind kernel b).toReal
    _ ≤ ∑ b, ∑ a, (p a).toReal ^ 2 / (q a).toReal * (kernel a b).toReal :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = ∑ a, ∑ b, (p a).toReal ^ 2 / (q a).toReal * (kernel a b).toReal := Finset.sum_comm
    _ = ∑ a, (p a).toReal ^ 2 / (q a).toReal := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, sum_toReal, mul_one]

/-- Unconditional data processing inequality for extended `χ²` divergence under a Markov kernel. -/
theorem echiSquare_bind_le [Finite α] [Finite β] (p q : PMF α) (kernel : α → PMF β) :
    echiSquare (p.bind kernel) (q.bind kernel) ≤ echiSquare p q := by
  by_cases h : p.support ⊆ q.support
  · rw [echiSquare_eq_ofReal (support_bind_subset h kernel), echiSquare_eq_ofReal h]
    exact ENNReal.ofReal_le_ofReal (chiSquare_bind_le h kernel)
  · rw [echiSquare_eq_top_iff.mpr h]
    exact le_top

/-- Data processing inequality for `χ²` divergence under a deterministic map. -/
theorem chiSquare_map_le [Finite α] [Finite β] {p q : PMF α} (h : p.support ⊆ q.support)
    (f : α → β) :
    chiSquare (p.map f) (q.map f) ≤ chiSquare p q := by
  simpa only [PMF.map, Function.comp_def] using chiSquare_bind_le h (fun a => PMF.pure (f a))

/-- Unconditional data processing inequality for extended `χ²` divergence under a
deterministic map. -/
theorem echiSquare_map_le [Finite α] [Finite β] (p q : PMF α) (f : α → β) :
    echiSquare (p.map f) (q.map f) ≤ echiSquare p q := by
  simpa only [PMF.map, Function.comp_def] using echiSquare_bind_le p q (fun a => PMF.pure (f a))

/-- Support containment for a mixture `μ.bind K` inside `q.support` holds whenever every supported
component `(K t).support` is contained in `q.support`. -/
theorem support_bind_subset_of_forall {μ : PMF θ} {K : θ → PMF α} {q : PMF α}
    (h : ∀ t ∈ μ.support, (K t).support ⊆ q.support) :
    (μ.bind K).support ⊆ q.support := by
  intro a ha
  rw [PMF.support_bind, Set.mem_iUnion₂] at ha
  rcases ha with ⟨t, ht, hat⟩
  exact h t ht hat

/-- **Mixture second-moment identity** (Ingster / Le Cam):
for a mixture `μ.bind K` and reference distribution `q` with `(K t).support ⊆ q.support` for all
`t ∈ μ.support`,
`1 + χ²(μ.bind K ‖ q) =
  ∑ t, ∑ t', (μ t).toReal * (μ t').toReal *
    ∑ a, (K t a).toReal * (K t' a).toReal / (q a).toReal`. -/
theorem one_add_chiSquare_bind_eq [Fintype θ] [Fintype α] (μ : PMF θ) (K : θ → PMF α)
    (q : PMF α) (h : ∀ t ∈ μ.support, (K t).support ⊆ q.support) :
    1 + chiSquare (μ.bind K) q =
      ∑ t, ∑ t', (μ t).toReal * (μ t').toReal *
        ∑ a, (K t a).toReal * (K t' a).toReal / (q a).toReal := by
  rw [one_add_chiSquare_eq_sum (support_bind_subset_of_forall h)]
  have hsq (a : α) :
      ((μ.bind K a).toReal) ^ 2 / (q a).toReal =
        ∑ t, ∑ t', (μ t).toReal * (μ t').toReal *
          ((K t a).toReal * (K t' a).toReal / (q a).toReal) := by
    rw [sq, bind_apply_toReal, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun t' _ => ?_
    ring
  simp_rw [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [Finset.mul_sum]

/-- Product mixture second-moment identity:
`1 + χ²(μ.bind (fun t => pi (K t)) ‖ pi q)` expressed via products of coordinate second moments. -/
theorem one_add_chiSquare_bind_pi_eq [Fintype θ] [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (μ : PMF θ) (K : θ → ∀ i, PMF (α i)) (q : ∀ i, PMF (α i))
    (h : ∀ t ∈ μ.support, ∀ i, (K t i).support ⊆ (q i).support) :
    1 + chiSquare (μ.bind (fun t => pi (K t))) (pi q) =
      ∑ t, ∑ t', (μ t).toReal * (μ t').toReal *
        ∏ i, ∑ a, (K t i a).toReal * (K t' i a).toReal / (q i a).toReal := by
  classical
  have hsup : ∀ t ∈ μ.support, (pi (K t)).support ⊆ (pi q).support := by
    intro t ht u hu
    rw [mem_support_pi_iff] at hu ⊢
    exact fun i => h t ht i (hu i)
  rw [one_add_chiSquare_bind_eq μ (fun t => pi (K t)) (pi q) hsup]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
  congr 1
  have hterm (u : ∀ i, α i) :
      (pi (K t) u).toReal * (pi (K t') u).toReal / (pi q u).toReal =
        ∏ i, (K t i (u i)).toReal * (K t' i (u i)).toReal / (q i (u i)).toReal := by
    simp only [pi_apply, ENNReal.toReal_prod]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  simp_rw [hterm]
  exact (Fintype.prod_sum
    (fun i a => (K t i a).toReal * (K t' i a).toReal / (q i a).toReal)).symm

/-- `n`-fold i.i.d. mixture second-moment identity:
`1 + χ²(μ.bind (fun t => iid (K t) n) ‖ iid q n) =
  ∑ t, ∑ t', μ(t) μ(t') (∑ a, K(t, a) K(t', a) / q(a)) ^ n`. -/
theorem one_add_chiSquare_bind_iid_eq [Fintype θ] [Fintype α] (μ : PMF θ) (K : θ → PMF α)
    (q : PMF α) (n : ℕ) (h : ∀ t ∈ μ.support, (K t).support ⊆ q.support) :
    1 + chiSquare (μ.bind (fun t => iid (K t) n)) (iid q n) =
      ∑ t, ∑ t', (μ t).toReal * (μ t').toReal *
        (∑ a, (K t a).toReal * (K t' a).toReal / (q a).toReal) ^ n := by
  simp_rw [iid_eq_pi]
  rw [one_add_chiSquare_bind_pi_eq μ (fun t _ => K t) (fun _ => q) (fun t ht _ => h t ht)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma support_toReal_pos {p q : PMF α} (h : p.support ⊆ q.support) {a : α}
    (hpa : p a ≠ 0) : 0 < (p a).toReal ∧ 0 < (q a).toReal :=
  ⟨ENNReal.toReal_pos hpa (p.apply_ne_top a),
    ENNReal.toReal_pos
      (fun ha => (PMF.apply_eq_zero_iff q a).mp ha (h ((PMF.mem_support_iff p a).mpr hpa)))
      (q.apply_ne_top a)⟩

/-- Comparison between squared Hellinger distance and KL divergence (natural log):
`2 * hellingerSq p q ≤ (klDiv p.toMeasure q.toMeasure).toReal` when `p.support ⊆ q.support`. -/
theorem two_mul_hellingerSq_le_toReal_klDiv [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {p q : PMF α} (h : p.support ⊆ q.support) :
    2 * hellingerSq p q ≤ (klDiv p.toMeasure q.toMeasure).toReal := by
  let := Fintype.ofFinite α
  rw [toReal_klDiv_toMeasure h, hellingerSq_eq_one_sub_bhattacharyya, bhattacharyya_eq_sum]
  have hsum : 2 * (1 - ∑ a, Real.sqrt ((p a).toReal * (q a).toReal)) =
      ∑ a, 2 * ((p a).toReal - Real.sqrt ((p a).toReal * (q a).toReal)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_toReal]
  rw [hsum]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases hpa : p a = 0
  · simp [hpa]
  · obtain ⟨hppos, hqpos⟩ := support_toReal_pos h hpa
    have hrpos : 0 < Real.sqrt ((q a).toReal / (p a).toReal) :=
      Real.sqrt_pos.mpr (div_pos hqpos hppos)
    have hlog := Real.log_le_sub_one_of_pos hrpos
    rw [Real.sqrt_eq_rpow, Real.log_rpow (div_pos hqpos hppos),
      Real.log_div hqpos.ne' hppos.ne'] at hlog
    rw [← Real.sqrt_eq_rpow] at hlog
    have hmul : 2 * ((p a).toReal * (1 - Real.sqrt ((q a).toReal / (p a).toReal))) =
        2 * ((p a).toReal - Real.sqrt ((p a).toReal * (q a).toReal)) := by
      have hsq : (p a).toReal * Real.sqrt ((q a).toReal / (p a).toReal) =
          Real.sqrt ((p a).toReal * (q a).toReal) := by
        rw [Real.sqrt_div ENNReal.toReal_nonneg, Real.sqrt_mul ENNReal.toReal_nonneg]
        have hs : Real.sqrt (p a).toReal ≠ 0 := (Real.sqrt_pos.mpr hppos).ne'
        calc (p a).toReal * (Real.sqrt (q a).toReal / Real.sqrt (p a).toReal)
          _ = (Real.sqrt (p a).toReal * Real.sqrt (p a).toReal) *
                (Real.sqrt (q a).toReal / Real.sqrt (p a).toReal) := by
              rw [Real.mul_self_sqrt ENNReal.toReal_nonneg]
          _ = Real.sqrt (p a).toReal * Real.sqrt (q a).toReal := by
              field_simp [hs]
      linarith
    have hmul2 :
        2 * ((p a).toReal * ((1 / 2 : ℝ) * (Real.log (q a).toReal - Real.log (p a).toReal))) =
          -((p a).toReal * Real.log ((p a).toReal / (q a).toReal)) := by
      rw [Real.log_div hppos.ne' hqpos.ne']
      ring
    nlinarith [hppos]

/-- KL divergence is bounded by `log (1 + χ²)`:
`(klDiv p.toMeasure q.toMeasure).toReal ≤ Real.log (1 + chiSquare p q)`. -/
theorem toReal_klDiv_le_log_one_add_chiSquare [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {p q : PMF α} (h : p.support ⊆ q.support) :
    (klDiv p.toMeasure q.toMeasure).toReal ≤ Real.log (1 + chiSquare p q) := by
  let := Fintype.ofFinite α
  rw [toReal_klDiv_toMeasure h]
  set c : ℝ := 1 + chiSquare p q
  have hcpos : 0 < c := by linarith [chiSquare_nonneg p q]
  have hpt (a : α) :
      (p a).toReal * Real.log ((p a).toReal / (q a).toReal) - (p a).toReal * Real.log c ≤
        (p a).toReal ^ 2 / (q a).toReal / c - (p a).toReal := by
    by_cases hpa : p a = 0
    · simp [hpa]
    · obtain ⟨hppos, hqpos⟩ := support_toReal_pos h hpa
      have hrpos : 0 < (p a).toReal / (q a).toReal / c :=
        div_pos (div_pos hppos hqpos) hcpos
      have hlog := Real.log_le_sub_one_of_pos hrpos
      rw [Real.log_div (div_pos hppos hqpos).ne' hcpos.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hppos.le
      have hlhs : (p a).toReal * (Real.log ((p a).toReal / (q a).toReal) - Real.log c) =
          (p a).toReal * Real.log ((p a).toReal / (q a).toReal) - (p a).toReal * Real.log c := by
        ring
      have hrhs : (p a).toReal * ((p a).toReal / (q a).toReal / c - 1) =
          (p a).toReal ^ 2 / (q a).toReal / c - (p a).toReal := by ring
      linarith
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hpt a
  simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_toReal, one_mul,
    ← Finset.sum_div] at hsum
  have hchi : ∑ a, (p a).toReal ^ 2 / (q a).toReal = c := (one_add_chiSquare_eq_sum h).symm
  rw [hchi, div_self hcpos.ne', sub_self] at hsum
  linarith

/-- KL divergence (natural log) is at most Pearson `χ²` divergence:
`(klDiv p.toMeasure q.toMeasure).toReal ≤ chiSquare p q`. -/
theorem toReal_klDiv_le_chiSquare [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {p q : PMF α} (h : p.support ⊆ q.support) :
    (klDiv p.toMeasure q.toMeasure).toReal ≤ chiSquare p q := by
  refine (toReal_klDiv_le_log_one_add_chiSquare h).trans ?_
  have hpos : 0 < 1 + chiSquare p q := by linarith [chiSquare_nonneg p q]
  linarith [Real.log_le_sub_one_of_pos hpos]

/-- Comparison between squared Hellinger distance and `χ²` divergence:
`2 * hellingerSq p q ≤ chiSquare p q` when `p.support ⊆ q.support`. -/
theorem two_mul_hellingerSq_le_chiSquare [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) :
    2 * hellingerSq p q ≤ chiSquare p q := by
  let : MeasurableSpace α := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  exact (two_mul_hellingerSq_le_toReal_klDiv h).trans (toReal_klDiv_le_chiSquare h)

end Cslib.Probability.PMF
