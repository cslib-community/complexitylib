/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Tactic
public import CslibFrontier.Foundations.Data.Finset.Median
public import CslibFrontier.Probability.MedianTrick
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.KWiseIndependent.SecondMoment
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The median-of-means estimator

Given an estimator `g : Ω → ℝ` of its mean `𝔼 g`, with sample `x` drawn uniformly from a finite
type `Ω`, the **median-of-means** estimator `Cslib.Probability.medianOfMeans g ω` draws `2 r`
groups of `k` independent samples `ω i l`, averages each group, and reports the median of the
`2 r` averages. An average of `k` samples has `k` times smaller variance
(`Cslib.Probability.expect_expect_sub_sq`), so by Chebyshev's inequality at most a third of the
groups miss `𝔼 g` by more than `t` once the variance of `g` is at most `k t² / 3`; the median
misses only when at least half of the groups do, which happens for at most an `(8 / 9) ^ r`
fraction of the samples (`Cslib.Probability.dens_abs_medianOfMeans_sub_gt_le`). This is the
amplification step of the frequency moment estimators of Alon, Matias and Szegedy
[AlonMatiasSzegedy1999, Theorem 2.2]. Probabilities over the samples are densities `Finset.dens`.

The last step is the **median trick** [Chakrabarti2025, Section 2.4]
(`Cslib.Probability.dens_abs_median_sub_gt_le`, in `CslibFrontier.Probability.MedianTrick`), which
holds for any estimate that misses by more than `t` with probability at most `1 / 3`, whatever its
distribution; the Count-Sketch uses it for estimates that are not averages.

`blockMedianOfMeans` is the separate measure-valued statistic used by adaptive
auditing. It takes explicit block sizes `m`, `k` and uses the total lower median,
expressed by finite maxima and minima. It is Borel measurable, including ties and
even block counts. Its sample experiment is the actual rectangular independent
product of the sample law; no concentration conclusion is a model field.

Its API includes `lowerMedian`, `blockMean`, `blockSampleLaw`,
`blockMedianOfMeans_confidence` and `blockMedianOfMeans_zero_length`.

## Main definitions

* `Cslib.Probability.medianOfMeans`: the median of `2 r` averages of `k` samples.

## Main results

* `Cslib.Probability.expect_expect_sub_sq`: the variance of an average of `k` independent samples.
* `Cslib.Probability.dens_abs_medianOfMeans_sub_gt_le`: the median of means misses the mean by
  more than `t` with probability at most `(8 / 9) ^ r`.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Theorem 2.2][AlonMatiasSzegedy1999]
* [A. Chakrabarti, *Data Stream Algorithms*, Section 2.4][Chakrabarti2025]
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace Cslib.Probability

private def subsetMinimum {k : ℕ} (s : Finset (Fin k)) (v : Fin k → ℝ) : ℝ :=
  if h : s.Nonempty then s.inf' h v else 0

private theorem medianSets_nonempty {k : ℕ} (hk : 0 < k) :
    (univ.powersetCard (k / 2 + 1) : Finset (Finset (Fin k))).Nonempty := by
  apply powersetCard_nonempty.mpr
  simp only [card_univ, Fintype.card_fin]
  omega

/-- The lower median, computed as the maximum of all minima over subsets of
size `k / 2 + 1`. Empty input has value zero. -/
def lowerMedian {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  if hk : 0 < k then
    (univ.powersetCard (k / 2 + 1)).sup' (medianSets_nonempty hk)
      (fun s => subsetMinimum s v)
  else 0

/-- The median depends measurably on all its entries. -/
@[fun_prop] theorem measurable_lowerMedian (k : ℕ) :
    Measurable (@lowerMedian k) := by
  classical
  unfold lowerMedian
  by_cases hk : 0 < k
  · simp only [dite_eq_left hk]
    have hmin (s : Finset (Fin k)) : Measurable (subsetMinimum s) := by
      unfold subsetMinimum
      split_ifs with hs
      · have h := @Finset.measurable_sup' ℝᵒᵈ _ (Fin k → ℝ) _ _ _ (Fin k) s hs
          (fun i v => v i) (fun i _ => measurable_pi_apply i)
        have heq : (fun v : Fin k → ℝ => s.inf' hs v) =
            s.inf' hs (fun i v => v i) := by
          funext v
          exact (Finset.inf'_apply hs (fun i (w : Fin k → ℝ) => w i) v).symm
        rw [heq]
        exact h
      · exact measurable_const
    have h := Finset.measurable_sup' (medianSets_nonempty hk)
      (fun s _ => hmin s)
    have heq : (fun v : Fin k → ℝ => (univ.powersetCard (k / 2 + 1)).sup'
        (medianSets_nonempty hk) (fun s => subsetMinimum s v)) =
        (univ.powersetCard (k / 2 + 1)).sup' (medianSets_nonempty hk) subsetMinimum := by
      funext v
      exact (Finset.sup'_apply (medianSets_nonempty hk) subsetMinimum v).symm
    rw [heq]
    exact h
  · simpa only [dite_eq_right hk] using
      (measurable_const : Measurable (fun _ : Fin k → ℝ => (0 : ℝ)))

/-- Fewer than half bad entries force the median into the same open error interval.
The strict interval matches the usual strict-accuracy convention. -/
theorem abs_lowerMedian_sub_lt {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ)
    (θ δ : ℝ) (hbad : 2 * (univ.filter (fun i => δ ≤ |v i - θ|)).card < k) :
    |lowerMedian v - θ| < δ := by
  classical
  let bad := univ.filter (fun i => δ ≤ |v i - θ|)
  let good := univ.filter (fun i => |v i - θ| < δ)
  have hcard : good.card + bad.card = k := by
    simpa only [good, bad, not_lt, card_univ, Fintype.card_fin] using
      card_filter_add_card_filter_not (s := (univ : Finset (Fin k)))
        (p := fun i => |v i - θ| < δ)
  have hr : k / 2 + 1 ≤ good.card := by dsimp only [bad] at *; omega
  obtain ⟨s, hs⟩ := powersetCard_nonempty.mpr hr
  obtain ⟨hsg, hsc⟩ := mem_powersetCard.mp hs
  have hsn : s.Nonempty := card_pos.mp (by omega)
  have hsall : s ∈ (univ.powersetCard (k / 2 + 1)) :=
    mem_powersetCard.mpr ⟨subset_univ _, hsc⟩
  have hlo : θ - δ < subsetMinimum s v := by
    rw [subsetMinimum, dite_eq_left hsn, lt_inf'_iff]
    intro i hi
    have := (abs_lt.mp (mem_filter.mp (hsg hi)).2).1
    linarith
  have hlow : θ - δ < lowerMedian v := by
    rw [lowerMedian, dite_eq_left hk]
    exact hlo.trans_le (le_sup' (fun s => subsetMinimum s v) hsall)
  have hhigh : lowerMedian v < θ + δ := by
    rw [lowerMedian, dite_eq_left hk, sup'_lt_iff]
    intro t ht
    have htc := (mem_powersetCard.mp ht).2
    have htn : t.Nonempty := card_pos.mp (by omega)
    have hex : ∃ i ∈ t, |v i - θ| < δ := by
      by_contra h
      push Not at h
      have hsub : t ⊆ bad := by
        intro i hi
        exact mem_filter.mpr ⟨mem_univ _, h i hi⟩
      have := card_le_card hsub
      dsimp only [bad] at *
      omega
    obtain ⟨i, hi, hg⟩ := hex
    rw [subsetMinimum, dite_eq_left htn]
    exact (inf'_le _ hi).trans_lt (by linarith [(abs_lt.mp hg).2])
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A nonempty constant vector has that constant as its median. -/
theorem lowerMedian_const {k : ℕ} (hk : 0 < k) (c : ℝ) :
    lowerMedian (fun _ : Fin k => c) = c := by
  classical
  rw [lowerMedian, dite_eq_left hk]
  apply sup'_eq_of_forall
  intro s hs
  have hc := (mem_powersetCard.mp hs).2
  have hn : s.Nonempty := card_pos.mp (by omega)
  simp only [subsetMinimum, dite_eq_left hn, inf'_const]

/-- Zero input has zero median, including the empty vector. -/
theorem lowerMedian_zero (k : ℕ) : lowerMedian (fun _ : Fin k => (0 : ℝ)) = 0 := by
  by_cases hk : 0 < k
  · exact lowerMedian_const hk 0
  · simp only [lowerMedian, dite_eq_right hk]

/-- Arithmetic mean of a block. Division by zero is totalized to zero; statistical
bounds below require a positive block size. -/
@[expose] def blockMean {Ω : Type*} (Y : Ω → ℝ) (m : ℕ) (z : Fin m → Ω) : ℝ :=
  (∑ i, Y (z i)) / m

/-- The mean of an independent block is unbiased. -/
theorem integral_blockMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Integrable Y μ) {m : ℕ} (hm : 0 < m) :
    ∫ z, blockMean Y m z ∂Measure.pi (fun _ : Fin m => μ) = ∫ z, Y z ∂μ := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [blockMean, div_eq_mul_inv]
  rw [integral_mul_const, integral_finsetSum]
  · simp only [integral_comp_eval (μ := fun _ : Fin m => μ) hY.aestronglyMeasurable,
      sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro i _
    exact integrable_comp_eval hY

/-- Independent block means have variance equal to the one-sample variance
 divided by the block size. -/
theorem variance_blockMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) {m : ℕ} (hm : 0 < m) :
    variance (blockMean Y m) (Measure.pi (fun _ : Fin m => μ)) = variance Y μ / m := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  change variance (fun z : Fin m → Ω => (∑ i, Y (z i)) * (m : ℝ)⁻¹) _ = _
  rw [variance_mul_const]
  have hvar := variance_sum_pi (fun _ : Fin m => hY)
  have hvar' : variance (fun z : Fin m → Ω => ∑ i, Y (z i))
      (Measure.pi (fun _ : Fin m => μ)) = ∑ _ : Fin m, variance Y μ := by
    have heq : (fun z : Fin m → Ω => ∑ i, Y (z i)) =
        ∑ i : Fin m, (fun z : Fin m → Ω => Y (z i)) := by
      ext z
      simp only [Finset.sum_apply]
    rw [heq]
    exact hvar
  rw [hvar']
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Median aggregation of independent blocks whose individual failure probability
is at most one quarter. The bound includes even block counts and ties. -/
theorem median_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {B : Ω → ℝ} (hB : Measurable B)
    {θ δ : ℝ} (hbad : ν.real {z | δ ≤ |B z - θ|} ≤ 1 / 4)
    {k : ℕ} (hk : 0 < k) :
    (Measure.pi (fun _ : Fin k => ν)).real
      {z | δ ≤ |lowerMedian (fun i => B (z i)) - θ|} ≤ Real.exp (-(k : ℝ) / 8) := by
  classical
  let E := {z | δ ≤ |B z - θ|}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (by simpa only [Real.norm_eq_abs] using (hB.sub_const θ).norm)
  let I : Ω → ℝ := E.indicator (fun _ => 1)
  have hI : Measurable I := measurable_const.indicator hE
  have hIint : Integrable I ν := (integrable_const 1).indicator hE
  have hmean : ∫ z, I z ∂ν = ν.real E := by
    simp only [I, integral_indicator_const _ hE, smul_eq_mul, mul_one]
  let P := Measure.pi (fun _ : Fin k => ν)
  have hind : iIndepFun (fun i (z : Fin k → Ω) => I (z i) - ν.real E) P :=
    iIndepFun_pi (fun _ => (hI.sub_const _).aemeasurable)
  have hsub (i : Fin k) : HasSubgaussianMGF
      (fun z : Fin k → Ω => I (z i) - ν.real E) (1 / 4) P := by
    have h := hasSubgaussianMGF_of_mem_Icc
      ((hI.comp (measurable_pi_apply i)).aemeasurable :
        AEMeasurable (fun z : Fin k → Ω => I (z i)) P)
      (ae_of_all P fun z => show I (z i) ∈ Set.Icc (0 : ℝ) 1 by
        simp only [I, Set.indicator_apply]; split_ifs <;> norm_num)
    have hi : ∫ z : Fin k → Ω, I (z i) ∂P = ν.real E :=
      (integral_comp_eval hI.aestronglyMeasurable).trans hmean
    change HasSubgaussianMGF (fun z : Fin k → Ω =>
      I (z i) - ∫ z : Fin k → Ω, I (z i) ∂P) _ P at h
    rw [hi] at h
    norm_num at h ⊢
    exact h
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := univ) (fun i _ => hsub i) (show 0 ≤ (k : ℝ) / 4 by positivity)
  have hcontain : {z : Fin k → Ω | δ ≤ |lowerMedian (fun i => B (z i)) - θ|} ⊆
      {z | (k : ℝ) / 4 ≤ ∑ i : Fin k, (I (z i) - ν.real E)} := by
    intro z hz
    have hc : k ≤ 2 * (univ.filter (fun i => δ ≤ |B (z i) - θ|)).card := by
      by_contra h
      exact (not_lt.mpr hz) (abs_lowerMedian_sub_lt hk _ θ δ (by omega))
    have hsum : ∑ i : Fin k, I (z i) =
        ((univ.filter (fun i => δ ≤ |B (z i) - θ|)).card : ℝ) := by
      simp only [I, Set.indicator_apply, E, Set.mem_ofPred_eq]
      simp only [sum_boole]
    have hcR : (k : ℝ) ≤ 2 * ((univ.filter
        (fun i => δ ≤ |B (z i) - θ|)).card : ℝ) := by exact_mod_cast hc
    simp only [Set.mem_ofPred_eq, sum_sub_distrib, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsum]
    have hm : (k : ℝ) * ν.real E ≤ (k : ℝ) / 4 := by
      have := mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    linarith
  refine (measureReal_mono hcontain).trans (htail.trans_eq ?_)
  congr 1
  norm_num only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp
  ring

/-- The actual rectangular i.i.d. sample experiment for median of means. Each
outer coordinate is an independent block of `m` independent samples. -/
@[expose] def blockSampleLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m k : ℕ) : Measure (Fin k → Fin m → Ω) :=
  Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin m => μ))

/-- The deterministic median-of-means estimator, applied to the recorded scores. -/
@[expose] def blockMedianOfMeans {Ω : Type*} (Y : Ω → ℝ) (m k : ℕ)
    (z : Fin k → Fin m → Ω) : ℝ := lowerMedian (fun i => blockMean Y m (z i))

/-- Median-of-means concentration with the exact constants `4` and `8`.
Only the ordinary second moment of the one-sample score is required. -/
theorem blockMedianOfMeans_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hYm : Measurable Y) (hY : MemLp Y 2 μ) {v δ : ℝ}
    (hv : variance Y μ ≤ v) (hδ : 0 < δ) {m k : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hsize : 4 * v ≤ m * δ ^ 2) :
    (blockSampleLaw μ m k).real
      {z | δ ≤ |blockMedianOfMeans Y m k z - ∫ x, Y x ∂μ|} ≤
        Real.exp (-(k : ℝ) / 8) := by
  have hBm : Measurable (blockMean Y m) := by unfold blockMean; fun_prop
  have hB : MemLp (blockMean Y m) 2 (Measure.pi (fun _ : Fin m => μ)) := by
    have h := (memLp_finsetSum' univ (fun i _ =>
      hY.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => μ) i))).mul_const
        ((m : ℝ)⁻¹)
    convert h using 1
    ext z
    simp only [blockMean, Finset.sum_apply, div_eq_mul_inv, Function.comp_apply, Function.eval]
  apply median_failure_le _ hBm (k := k) ?_ hk
  have hc := meas_ge_le_variance_div_sq hB hδ
  rw [integral_blockMean μ (hY.integrable (by norm_num)) hm, variance_blockMean μ hY hm] at hc
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : variance Y μ / m / δ ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
    apply (div_le_iff₀ hmR).mpr
    nlinarith
  have hcR := ENNReal.toReal_mono (by finiteness) hc
  rw [ENNReal.toReal_ofReal (div_nonneg
    (div_nonneg (variance_nonneg Y μ) hmR.le) (sq_nonneg δ))] at hcR
  exact hcR.trans hb

/-- A logarithmic number of blocks gives the prescribed failure probability. -/
theorem blockMedianOfMeans_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hYm : Measurable Y) (hY : MemLp Y 2 μ) {v δ η : ℝ}
    (hv : variance Y μ ≤ v) (hδ : 0 < δ) (hη : 0 < η) {m k : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hsize : 4 * v ≤ m * δ ^ 2)
    (hblocks : 8 * Real.log (1 / η) ≤ k) :
    (blockSampleLaw μ m k).real
      {z | δ ≤ |blockMedianOfMeans Y m k z - ∫ x, Y x ∂μ|} ≤ η := by
  refine (blockMedianOfMeans_failure_le μ hYm hY hv hδ hm hk hsize).trans ?_
  calc Real.exp (-(k : ℝ) / 8) ≤ Real.exp (Real.log η) := by
         apply Real.exp_le_exp.mpr
         rw [one_div, Real.log_inv] at hblocks
         linarith
       _ = η := Real.exp_log hη

/-- Median of means is a measurable function of its observed samples. -/
@[fun_prop] theorem measurable_blockMedianOfMeans {Ω : Type*} [MeasurableSpace Ω]
    {Y : Ω → ℝ} (hY : Measurable Y) (m k : ℕ) : Measurable (blockMedianOfMeans Y m k) := by
  unfold blockMedianOfMeans
  apply (measurable_lowerMedian k).comp
  apply Measurable.of_eval
  intro i
  unfold blockMean
  fun_prop

/-- Independently sampling mapped observations agrees with mapping each entry
of the latent rectangular experiment. -/
theorem blockSampleLaw_map {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → Z} (hf : Measurable f) (m k : ℕ) :
    (blockSampleLaw μ m k).map (fun z i j => f (z i j)) =
      blockSampleLaw (μ.map f) m k := by
  have hi : (Measure.pi (fun _ : Fin m => μ)).map (fun z j => f (z j)) =
      Measure.pi (fun _ : Fin m => μ.map f) :=
    Measure.pi_map_pi (fun _ => hf.aemeasurable)
  have h := Measure.pi_map_pi (μ := fun _ : Fin k => Measure.pi (fun _ : Fin m => μ))
    (fun _ => (show Measurable (fun z : Fin m → Ω => fun j => f (z j)) by fun_prop).aemeasurable)
  simpa only [blockSampleLaw, hi] using h

/-- Any failure bound for a score that factors through the observed record is
also a bound in the actual i.i.d. observation experiment. -/
theorem blockMedianOfMeans_observation_failure {Ω Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → Z} (hf : Measurable f) {g : Z → ℝ} (hg : Measurable g)
    (m k : ℕ) (θ δ : ℝ) :
    (blockSampleLaw (μ.map f) m k).real {z | δ ≤ |blockMedianOfMeans g m k z - θ|} =
      (blockSampleLaw μ m k).real {z | δ ≤ |blockMedianOfMeans (g ∘ f) m k z - θ|} := by
  rw [← blockSampleLaw_map μ hf m k, measureReal_def, Measure.map_apply]
  · rfl
  · fun_prop
  · exact measurableSet_le measurable_const
      (by simpa only [Real.norm_eq_abs] using
        ((measurable_blockMedianOfMeans hg m k).sub_const θ).norm)

/-- The zero-sample branch is explicitly totalized to zero. Together with a
zero-divergence target theorem this gives exact, sample-free accuracy. -/
theorem blockMedianOfMeans_zero_length {Ω : Type*} (Y : Ω → ℝ) (k : ℕ)
    (z : Fin k → Fin 0 → Ω) : blockMedianOfMeans Y 0 k z = 0 := by
  simp only [blockMedianOfMeans, blockMean, Nat.cast_zero, div_zero, lowerMedian_zero]

end Cslib.Probability

end

end

public section

namespace Cslib.Probability

open Finset Fintype
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The **median-of-means** estimate from `2 r` groups of `k` samples of `g`: the median of the
`2 r` group averages. -/
@[expose] noncomputable def medianOfMeans {r k : ℕ} (g : Ω → ℝ) (ω : Fin (2 * r) → Fin k → Ω) : ℝ :=
  median fun i => 𝔼 l, g (ω i l)

/-- The average of `k` independent samples of `g` has `k` times smaller variance. -/
theorem expect_expect_sub_sq [Nonempty Ω] {k : ℕ} [NeZero k] (g : Ω → ℝ) :
    𝔼 ω : Fin k → Ω, (𝔼 l, g (ω l) - 𝔼 x, g x) ^ 2 = (𝔼 x, (g x - 𝔼 y, g y) ^ 2) / k := by
  classical
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne k)
  have key := (isKWiseIndependentHash_id (X := Fin k) (Y := Ω) 2).expect_sq_sum univ
    (fun _ y => (g y - 𝔼 x, g x) / k) fun l _ => by
      simp only [← expect_div, expect_sub_distrib, Fintype.expect_const, sub_self, zero_div]
  simp only [id] at key
  have hrw (ω : Fin k → Ω) : 𝔼 l, g (ω l) - 𝔼 x, g x = ∑ l, (g (ω l) - 𝔼 x, g x) / k := by
    rw [← sum_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Fintype.expect_eq_sum_div_card (fun l => g (ω l)), Fintype.card_fin]
    field_simp
  simp only [hrw, key, div_pow, ← expect_div, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Median of means** [AlonMatiasSzegedy1999, Theorem 2.2]: if `g` has variance at most
`k t² / 3`, the median of `2 r` averages of `k` independent samples of `g` is farther than `t` from
the mean of `g` for at most an `(8 / 9) ^ r` fraction of the samples. -/
theorem dens_abs_medianOfMeans_sub_gt_le [Nonempty Ω] {r k : ℕ} [NeZero k] (g : Ω → ℝ) {t : ℝ}
    (ht : 0 < t) (hvar : 3 * 𝔼 x, (g x - 𝔼 y, g y) ^ 2 ≤ k * t ^ 2) :
    (dens {ω : Fin (2 * r) → Fin k → Ω | t < |medianOfMeans g ω - 𝔼 x, g x|} : ℝ) ≤
      (8 / 9) ^ r := by
  classical
  set μ := 𝔼 x, g x
  have hk : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne k))
  -- Chebyshev: at most a third of the groups are bad.
  have hcheb : (dens {ω : Fin k → Ω | t ^ 2 ≤ (𝔼 l, g (ω l) - μ) ^ 2} : ℝ) * t ^ 2 ≤ t ^ 2 / 3 := by
    have := Fintype.mul_dens_filter_le_expect (f := fun ω : Fin k → Ω => (𝔼 l, g (ω l) - μ) ^ 2)
      (fun _ => sq_nonneg _) (t ^ 2)
    rw [expect_expect_sub_sq] at this
    calc _ = t ^ 2 * (dens {ω : Fin k → Ω | t ^ 2 ≤ (𝔼 l, g (ω l) - μ) ^ 2} : ℝ) := mul_comm _ _
      _ ≤ _ := this
      _ ≤ t ^ 2 / 3 := by
        rw [div_le_div_iff₀ hk (by norm_num)]
        linarith
  have hbad : (dens {ω : Fin k → Ω | t < |𝔼 l, g (ω l) - μ|} : ℝ) ≤ 1 / 3 := by
    have hsub : ({ω : Fin k → Ω | t < |𝔼 l, g (ω l) - μ|} : Finset _) ⊆
        ({ω : Fin k → Ω | t ^ 2 ≤ (𝔼 l, g (ω l) - μ) ^ 2} : Finset _) := fun ω hω => by
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      rw [← sq_abs (𝔼 l, g (ω l) - μ)]
      exact pow_le_pow_left₀ ht.le hω.le 2
    have h2 : (dens {ω : Fin k → Ω | t < |𝔼 l, g (ω l) - μ|} : ℝ) * t ^ 2 ≤ t ^ 2 / 3 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast dens_le_dens hsub) (sq_nonneg t)).trans hcheb
    have ht2 : 0 < t ^ 2 := by positivity
    rw [div_eq_mul_one_div (t ^ 2), mul_comm (t ^ 2)] at h2
    exact le_of_mul_le_mul_right h2 ht2
  exact dens_abs_median_sub_gt_le (fun ω : Fin k → Ω => 𝔼 l, g (ω l)) hbad r

end Cslib.Probability
