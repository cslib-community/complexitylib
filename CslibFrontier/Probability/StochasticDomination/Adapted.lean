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
public import CslibFrontier.Probability.StochasticDomination.PoissonBinomial
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Process.Filtration
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Adapted

/-!
# Stochastic domination for adapted Bernoulli event counts

First-order stochastic domination between adapted event counts `adaptedCount A n` under a
general filtration `ℱ : Filtration ℕ m` (and specifically under `ProbabilityTheory.Kernel.traj` /
`ProbabilityTheory.Kernel.trajMeasure`, as well as finite-horizon sequential `PMF` processes) and
the Poisson-binomial distribution `Cslib.Probability.PMF.poissonBinomial` (or Mathlib's
`ProbabilityTheory.binomial` in the uniform-envelope case).

Both lower-envelope domination (`ps[t] ≤ P[A t | ℱ t]`, giving `adaptedCount ≥_st poissonBinomial`)
and upper-envelope domination (`P[A t | ℱ t] ≤ ps[t]`, giving `poissonBinomial ≥_st adaptedCount`)
are proved, together with active-before-target variants requiring the conditional probability
bound only on `{ω | adaptedCount A t ω < r}`.

## Main definitions

* `Cslib.Probability.adaptedCount`: cumulative number of events among `A 0, ..., A (n - 1)`.
* `Cslib.Probability.shiftFiltration`: filtration shifted forward by a starting index `a`.
* `Cslib.Probability.PMF.seqProcess`, `Cslib.Probability.PMF.seqCount`: finite-horizon sequential
  `PMF` processes and their success counts.

## Main results

* `Cslib.Probability.adaptedCount_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.poissonBinomial_stochasticallyDominates_adaptedCount`: unconditional adapted
  domination over a general filtration.
* `Cslib.Probability.adaptedCount_min_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.adaptedCount_real_Iio_le_binomial`: active-before-target (`count < r`)
  domination and uniform binomial tail bounds.
* `Cslib.Probability.traj_adaptedCount_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.poissonBinomial_stochasticallyDominates_traj_adaptedCount`,
  `Cslib.Probability.trajMeasure_adaptedCount_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.poissonBinomial_stochasticallyDominates_trajMeasure_adaptedCount`:
  lower- and upper-envelope specializations to `ProbabilityTheory.Kernel.traj` and
  `Kernel.trajMeasure`.
* `Cslib.Probability.PMF.seqCount_stochasticallyDominates_poissonBinomial`,
  `Cslib.Probability.PMF.seqCount_active_toReal_Iio_le`: sequential finite-horizon `PMF`
  domination.
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal unitInterval

section AdaptedCount

/-- Number of events among `A 0, ..., A (n - 1)` occurring at outcome `ω`. -/
@[expose]
noncomputable def adaptedCount {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℕ :=
  ∑ t ∈ Finset.range n, (A t).indicator (fun _ => 1) ω

@[simp]
theorem adaptedCount_zero {Ω : Type*} (A : ℕ → Set Ω) (ω : Ω) :
    adaptedCount A 0 ω = 0 := by
  simp [adaptedCount]

theorem adaptedCount_succ {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    adaptedCount A (n + 1) ω = adaptedCount A n ω + (A n).indicator (fun _ => 1) ω := by
  simp [adaptedCount, Finset.sum_range_succ]

theorem adaptedCount_le {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    adaptedCount A n ω ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [adaptedCount_succ]
    by_cases h : ω ∈ A n
    · simp only [Set.indicator_of_mem h]
      omega
    · simp only [Set.indicator_of_notMem h]
      omega

theorem adaptedCount_mono {Ω : Type*} (A : ℕ → Set Ω) (ω : Ω) :
    Monotone fun n => adaptedCount A n ω := by
  intro m n hmn
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hmn
    exact le_rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · exact le_rfl
    · dsimp only
      rw [adaptedCount_succ]
      exact (ih (Nat.lt_succ_iff.mp hlt)).trans (Nat.le_add_right _ _)

theorem measurable_adaptedCount {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℕ m) {A : ℕ → Set Ω} (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (n : ℕ) :
    Measurable[ℱ n] (adaptedCount A n) := by
  induction n with
  | zero =>
    have heq : adaptedCount A 0 = fun _ => 0 := funext (adaptedCount_zero A)
    rw [heq]
    exact measurable_const
  | succ n ih =>
    have heq : adaptedCount A (n + 1) = fun ω =>
        adaptedCount A n ω + (A n).indicator (fun _ => 1) ω := by
      ext ω
      exact adaptedCount_succ A n ω
    rw [heq]
    refine (ih.mono (ℱ.mono n.le_succ) le_rfl).add ?_
    exact measurable_const.indicator (hA n)

theorem adapted_adaptedCount {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℕ m) {A : ℕ → Set Ω} (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) :
    Adapted ℱ (adaptedCount A) :=
  fun n => measurable_adaptedCount ℱ hA n

end AdaptedCount

section BackwardInduction

private noncomputable def pbValue (ps : List I) (f : ℕ → ℝ) (k m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range ((ps.drop k).length + 1),
    (PMF.poissonBinomial (ps.drop k) j).toReal * f (m + j)

private theorem pbValue_mono {ps : List I} {f : ℕ → ℝ} (hf : Monotone f) (k : ℕ) :
    Monotone (pbValue ps f k) := by
  intro m₁ m₂ hm
  refine Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul_of_nonneg_left (hf (Nat.add_le_add_right hm j)) ENNReal.toReal_nonneg

private theorem pbValue_length (ps : List I) (f : ℕ → ℝ) (m : ℕ) :
    pbValue ps f ps.length m = f m := by
  simp [pbValue]

private theorem pbValue_zero (ps : List I) (f : ℕ → ℝ) :
    pbValue ps f 0 0 =
      ∑ j ∈ Finset.range (ps.length + 1), (PMF.poissonBinomial ps j).toReal * f j := by
  simp [pbValue]

private theorem pbValue_step (ps : List I) (f : ℕ → ℝ) {k : ℕ} (hk : k < ps.length)
    (m : ℕ) :
    pbValue ps f k m =
      pbValue ps f (k + 1) m +
        (ps[k] : ℝ) * (pbValue ps f (k + 1) (m + 1) - pbValue ps f (k + 1) m) := by
  let qs := ps.drop (k + 1)
  have hdrop : ps.drop k = ps[k] :: qs := List.drop_eq_getElem_cons hk
  have hlen : (ps.drop k).length = qs.length + 1 := by
    rw [hdrop, List.length_cons]
  have hpb0 :
      pbValue ps f (k + 1) m =
        (PMF.poissonBinomial qs 0).toReal * f (m + 0) +
          ∑ x ∈ Finset.range (qs.length + 1),
            (PMF.poissonBinomial qs (x + 1)).toReal * f (m + (x + 1)) := by
    have hpb2 :
        pbValue ps f (k + 1) m =
          ∑ j ∈ Finset.range (qs.length + 2),
            (PMF.poissonBinomial qs j).toReal * f (m + j) := by
      symm
      rw [Finset.sum_range_succ,
        PMF.poissonBinomial_eq_zero_of_lt (ps := qs) (Nat.lt_succ_self _)]
      simp [pbValue, qs]
    rw [hpb2, Finset.sum_range_succ' (fun j => (PMF.poissonBinomial qs j).toReal * f (m + j)),
      add_comm]
  have hpb1 :
      pbValue ps f (k + 1) (m + 1) =
        ∑ x ∈ Finset.range (qs.length + 1),
          (PMF.poissonBinomial qs x).toReal * f (m + (x + 1)) := by
    change (∑ x ∈ Finset.range (qs.length + 1),
      (PMF.poissonBinomial qs x).toReal * f ((m + 1) + x)) = _
    refine Finset.sum_congr rfl fun x _ => ?_
    have hidx : m + 1 + x = m + (x + 1) := by omega
    rw [hidx]
  rw [pbValue, hlen, Finset.sum_range_succ']
  simp_rw [hdrop, PMF.poissonBinomial_cons_zero_toReal, PMF.poissonBinomial_cons_succ_toReal]
  have hsum_add :
      (∑ x ∈ Finset.range (qs.length + 1),
          ((1 - (ps[k] : ℝ)) * (PMF.poissonBinomial qs (x + 1)).toReal +
              (ps[k] : ℝ) * (PMF.poissonBinomial qs x).toReal) * f (m + (x + 1))) =
        (1 - (ps[k] : ℝ)) *
            ∑ x ∈ Finset.range (qs.length + 1),
              (PMF.poissonBinomial qs (x + 1)).toReal * f (m + (x + 1)) +
          (ps[k] : ℝ) *
            ∑ x ∈ Finset.range (qs.length + 1),
              (PMF.poissonBinomial qs x).toReal * f (m + (x + 1)) := by
    have hterm (x : ℕ) :
        ((1 - (ps[k] : ℝ)) * (PMF.poissonBinomial qs (x + 1)).toReal +
            (ps[k] : ℝ) * (PMF.poissonBinomial qs x).toReal) * f (m + (x + 1)) =
          (1 - (ps[k] : ℝ)) * ((PMF.poissonBinomial qs (x + 1)).toReal * f (m + (x + 1))) +
            (ps[k] : ℝ) * ((PMF.poissonBinomial qs x).toReal * f (m + (x + 1))) := by
      ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum_add]
  have hlin :
      (1 - (ps[k] : ℝ)) * pbValue ps f (k + 1) m +
          (ps[k] : ℝ) * pbValue ps f (k + 1) (m + 1) =
        pbValue ps f (k + 1) m +
          (ps[k] : ℝ) * (pbValue ps f (k + 1) (m + 1) - pbValue ps f (k + 1) m) := by
    ring
  rw [← hlin, hpb0, hpb1]
  ring

private theorem pbValue_abs_le {ps : List I} {f : ℕ → ℝ} {C : ℝ} (hC : ∀ j, |f j| ≤ C)
    (k m : ℕ) :
    |pbValue ps f k m| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  calc
    |pbValue ps f k m|
      ≤ ∑ j ∈ Finset.range ((ps.drop k).length + 1),
          |(PMF.poissonBinomial (ps.drop k) j).toReal * f (m + j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range ((ps.drop k).length + 1),
          (PMF.poissonBinomial (ps.drop k) j).toReal * C := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (hC (m + j)) ENNReal.toReal_nonneg
    _ = (∑ j ∈ Finset.range ((ps.drop k).length + 1),
          (PMF.poissonBinomial (ps.drop k) j).toReal) * C :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * C := by
        refine mul_le_mul_of_nonneg_right ?_ hC0
        have hsum :
            ∑ j ∈ Finset.range ((ps.drop k).length + 1),
              (PMF.poissonBinomial (ps.drop k) j).toReal = 1 := by
          have ht : ∑' j : ℕ, (PMF.poissonBinomial (ps.drop k) j).toReal = 1 := by
            simp [PMF.tsum_toReal]
          rw [← ht]
          refine (tsum_eq_sum fun j hj => ?_).symm
          simp only [Finset.mem_range, not_lt] at hj
          rw [PMF.poissonBinomial_eq_zero_of_lt (by omega), ENNReal.toReal_zero]
        exact hsum.le
    _ = C := one_mul C

end BackwardInduction

section FiltrationComparison

private theorem integrable_pbValue {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (ps : List I) {f : ℕ → ℝ} {C : ℝ} (hC : ∀ j, |f j| ≤ C) (k n : ℕ) :
    Integrable (fun ω => pbValue ps f k (adaptedCount A n ω)) P := by
  have hm : Measurable (fun ω => pbValue ps f k (adaptedCount A n ω)) :=
    (measurable_from_top : Measurable (pbValue ps f k)).comp
      ((measurable_adaptedCount ℱ hA n).mono (ℱ.le n) le_rfl)
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun ω => pbValue_abs_le hC k _)

private theorem integral_pbValue_step_diff {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (ps : List I) {f : ℕ → ℝ} (hf : Monotone f) {C : ℝ} (hC : ∀ j, |f j| ≤ C)
    {k : ℕ} (hk : k < ps.length) :
    ∃ D : Ω → ℝ, (∀ ω, 0 ≤ D ω) ∧
      Integrable (fun ω => (ps[k] : ℝ) * D ω) P ∧
      Integrable (fun ω => D ω * P[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω) P ∧
      ∃ base : ℝ,
        ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P = base + ∫ ω, (ps[k] : ℝ) * D ω ∂P ∧
        ∫ ω, pbValue ps f (k + 1) (adaptedCount A (k + 1) ω) ∂P =
          base + ∫ ω, D ω * P[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω ∂P := by
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  let D : Ω → ℝ := fun ω =>
    pbValue ps f (k + 1) (adaptedCount A k ω + 1) - pbValue ps f (k + 1) (adaptedCount A k ω)
  let Iₖ : Ω → ℝ := (A k).indicator (fun _ => 1)
  have hD_sm : StronglyMeasurable[ℱ k] D :=
    ((measurable_from_top :
        Measurable fun m => pbValue ps f (k + 1) (m + 1) - pbValue ps f (k + 1) m).comp
      (measurable_adaptedCount ℱ hA k)).stronglyMeasurable
  have hD_nn : ∀ ω, 0 ≤ D ω := fun ω =>
    sub_nonneg.mpr (pbValue_mono hf (k + 1) (Nat.le_succ _))
  have hI_int : Integrable Iₖ P :=
    (integrable_const (1 : ℝ)).indicator (ℱ.le (k + 1) _ (hA k))
  have hD_bd (ω : Ω) : |D ω| ≤ 2 * C := by
    have h1 := pbValue_abs_le (ps := ps) hC (k + 1) (adaptedCount A k ω + 1)
    have h2 := pbValue_abs_le (ps := ps) hC (k + 1) (adaptedCount A k ω)
    exact (abs_sub _ _).trans (by linarith)
  have hDI_int : Integrable (fun ω => D ω * Iₖ ω) P := by
    refine Integrable.of_bound
      ((hD_sm.mono (ℱ.le k)).aestronglyMeasurable.mul hI_int.aestronglyMeasurable)
      (2 * C) (ae_of_all _ fun ω => ?_)
    have hI_bd : |Iₖ ω| ≤ 1 := by
      by_cases hω : ω ∈ A k <;> simp [Iₖ, hω]
    simpa [abs_mul] using mul_le_mul (hD_bd ω) hI_bd (abs_nonneg _) (by positivity)
  have hbase_int : Integrable (fun ω => pbValue ps f (k + 1) (adaptedCount A k ω)) P :=
    integrable_pbValue ℱ hA ps hC (k + 1) k
  have hD_int : Integrable D P := by
    have hm1 : Measurable fun ω => pbValue ps f (k + 1) (adaptedCount A k ω + 1) :=
      (measurable_from_top : Measurable fun m => pbValue ps f (k + 1) (m + 1)).comp
        ((measurable_adaptedCount ℱ hA k).mono (ℱ.le k) le_rfl)
    exact (Integrable.of_bound hm1.aestronglyMeasurable C
      (ae_of_all _ fun ω => pbValue_abs_le (ps := ps) hC (k + 1) _)).sub hbase_int
  have hDp_int : Integrable (fun ω => (ps[k] : ℝ) * D ω) P := hD_int.const_mul _
  have hDce_int : Integrable (fun ω => D ω * P[Iₖ | ℱ k] ω) P := by
    have hce_bd : ∀ᵐ ω ∂P, |P[Iₖ | ℱ k] ω| ≤ 1 := by
      have h0 : (fun _ : Ω => (0 : ℝ)) ≤ᵐ[P] P[Iₖ | ℱ k] :=
        condExp_nonneg (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
      have hI_le : Iₖ ≤ᵐ[P] fun _ => (1 : ℝ) := ae_of_all _ fun ω => by
        by_cases hω : ω ∈ A k <;> simp [Iₖ, hω]
      have h1 : P[Iₖ | ℱ k] ≤ᵐ[P] fun _ => (1 : ℝ) := by
        calc
          P[Iₖ | ℱ k] ≤ᵐ[P] P[fun _ : Ω => (1 : ℝ) | ℱ k] :=
            condExp_mono hI_int (integrable_const 1) hI_le
          _ =ᵐ[P] fun _ => (1 : ℝ) := by rw [condExp_const (ℱ.le k) (1 : ℝ)]
      filter_upwards [h0, h1] with ω hω0 hω1
      exact abs_le.mpr ⟨by linarith, hω1⟩
    refine Integrable.of_bound
      ((hD_sm.mono (ℱ.le k)).aestronglyMeasurable.mul
        (stronglyMeasurable_condExp.mono (ℱ.le k)).aestronglyMeasurable)
      (2 * C) ?_
    filter_upwards [hce_bd] with ω hω
    simpa [Real.norm_eq_abs, abs_mul] using
      mul_le_mul (hD_bd ω) hω (abs_nonneg _) (by positivity)
  have hsplit_lhs :
      (fun ω => pbValue ps f k (adaptedCount A k ω)) =
        fun ω => pbValue ps f (k + 1) (adaptedCount A k ω) + (ps[k] : ℝ) * D ω := by
    ext ω
    exact pbValue_step ps f hk (adaptedCount A k ω)
  have hsplit_rhs :
      (fun ω => pbValue ps f (k + 1) (adaptedCount A (k + 1) ω)) =
        fun ω => pbValue ps f (k + 1) (adaptedCount A k ω) + D ω * Iₖ ω := by
    ext ω
    rw [adaptedCount_succ]
    by_cases hω : ω ∈ A k <;> simp [Iₖ, D, hω]
  have hpull : ∫ ω, D ω * Iₖ ω ∂P = ∫ ω, D ω * P[Iₖ | ℱ k] ω ∂P := by
    calc
      ∫ ω, D ω * Iₖ ω ∂P
        = ∫ ω, P[fun ω => D ω * Iₖ ω | ℱ k] ω ∂P := (integral_condExp (ℱ.le k)).symm
      _ = ∫ ω, D ω * P[Iₖ | ℱ k] ω ∂P :=
          integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hD_sm hDI_int hI_int)
  refine ⟨D, hD_nn, hDp_int, hDce_int,
    ∫ ω, pbValue ps f (k + 1) (adaptedCount A k ω) ∂P, ?_, ?_⟩
  · rw [hsplit_lhs, integral_add hbase_int hDp_int]
  · rw [hsplit_rhs, integral_add hbase_int hDI_int, hpull]

private theorem integral_pbValue_le_succ {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (ps : List I) {f : ℕ → ℝ} (hf : Monotone f) {C : ℝ} (hC : ∀ j, |f j| ≤ C)
    {k : ℕ} (hk : k < ps.length)
    (hp : (fun _ => (ps[k] : ℝ)) ≤ᵐ[P] P[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k]) :
    ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P ≤
      ∫ ω, pbValue ps f (k + 1) (adaptedCount A (k + 1) ω) ∂P := by
  rcases integral_pbValue_step_diff P ℱ hA ps hf hC hk with
    ⟨D, hD_nn, hDp_int, hDce_int, base, h1, h2⟩
  rw [h1, h2]
  refine add_le_add_right (integral_mono_ae hDp_int hDce_int ?_) base
  filter_upwards [hp] with ω hω
  rw [mul_comm (ps[k] : ℝ) (D ω)]
  exact mul_le_mul_of_nonneg_left hω (hD_nn ω)

private theorem integral_pbValue_succ_le {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (ps : List I) {f : ℕ → ℝ} (hf : Monotone f) {C : ℝ} (hC : ∀ j, |f j| ≤ C)
    {k : ℕ} (hk : k < ps.length)
    (hp : P[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ≤ᵐ[P] fun _ => (ps[k] : ℝ)) :
    ∫ ω, pbValue ps f (k + 1) (adaptedCount A (k + 1) ω) ∂P ≤
      ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P := by
  rcases integral_pbValue_step_diff P ℱ hA ps hf hC hk with
    ⟨D, hD_nn, hDp_int, hDce_int, base, h1, h2⟩
  rw [h1, h2]
  refine add_le_add_right (integral_mono_ae hDce_int hDp_int ?_) base
  filter_upwards [hp] with ω hω
  rw [mul_comm (ps[k] : ℝ) (D ω)]
  exact mul_le_mul_of_nonneg_left hω (hD_nn ω)

private theorem pbValue_zero_Ici_eq_real (ps : List I) (r : ℕ) :
    pbValue ps ((Set.Ici r).indicator (fun _ => (1 : ℝ))) 0 0 =
      (PMF.poissonBinomial ps).toMeasure.real (Set.Ici r) := by
  rw [pbValue_zero, measureReal_def]
  have hsum :
      (PMF.poissonBinomial ps).toMeasure (Set.Ici r) =
        ∑ j ∈ Finset.range (ps.length + 1),
          if r ≤ j then PMF.poissonBinomial ps j else 0 := by
    rw [PMF.toMeasure_apply _ measurableSet_Ici]
    have hfin :
        (∑' j : ℕ, (Set.Ici r).indicator (⇑(PMF.poissonBinomial ps)) j) =
          ∑ j ∈ Finset.range (ps.length + 1),
            (Set.Ici r).indicator (⇑(PMF.poissonBinomial ps)) j := by
      refine tsum_eq_sum fun j hj => ?_
      simp only [Finset.mem_range, not_lt] at hj
      have hz := PMF.poissonBinomial_eq_zero_of_lt (ps := ps) (by omega : ps.length < j)
      by_cases hrj : r ≤ j <;> simp [hrj, hz]
    rw [hfin]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : r ≤ j <;> simp [hj]
  rw [hsum, ENNReal.toReal_sum fun j _ => by split_ifs <;> simp [PMF.apply_ne_top]]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j <;> simp [hj]

private theorem monotone_indicator_Ici (r : ℕ) :
    Monotone ((Set.Ici r).indicator (fun _ => (1 : ℝ))) := by
  intro a b hab
  by_cases ha : r ≤ a
  · have hb : r ≤ b := ha.trans hab
    simp [ha, hb]
  · by_cases hb : r ≤ b <;> simp [ha, hb]

private theorem abs_indicator_Ici_le_one (r j : ℕ) :
    |(Set.Ici r).indicator (fun _ => (1 : ℝ)) j| ≤ 1 := by
  by_cases hj : r ≤ j <;> simp [hj]

private theorem integral_indicator_Ici_adaptedCount {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (n r : ℕ) :
    ∫ ω, (Set.Ici r).indicator (fun _ => (1 : ℝ)) (adaptedCount A n ω) ∂P =
      (P.map (adaptedCount A n)).real (Set.Ici r) := by
  have hm : Measurable (adaptedCount A n) :=
    (measurable_adaptedCount ℱ hA n).mono (ℱ.le _) le_rfl
  rw [measureReal_def, Measure.map_apply hm measurableSet_Ici, ← measureReal_def,
    ← integral_indicator_one (hm measurableSet_Ici)]
  rfl

private theorem Ici_le_of_measureReal_le {μ ν : Measure ℕ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {r : ℕ} (h : μ.real (Set.Ici r) ≤ ν.real (Set.Ici r)) :
    μ (Set.Ici r) ≤ ν (Set.Ici r) := by
  rw [measureReal_def, measureReal_def] at h
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm.trans_le
    ((ENNReal.ofReal_le_ofReal h).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _)))

/-- **Adapted Poisson-binomial domination (lower envelope)**: if `A t` is `ℱ (t + 1)`-measurable
and `P[A t | ℱ t] ≥ ps[t]` a.e. for all `t < ps.length`, then the law of `adaptedCount A ps.length`
stochastically dominates `PMF.poissonBinomial ps`. -/
theorem adaptedCount_stochasticallyDominates_poissonBinomial {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length),
      (fun _ => (ps[t] : ℝ)) ≤ᵐ[P] P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    StochasticallyDominates (P.map (adaptedCount A ps.length))
      (PMF.poissonBinomial ps).toMeasure := by
  rw [stochasticallyDominates_nat_iff_Ici]
  intro r
  let f : ℕ → ℝ := (Set.Ici r).indicator (fun _ => 1)
  have hchain (k : ℕ) (hk : k ≤ ps.length) :
      pbValue ps f 0 0 ≤ ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P := by
    induction k with
    | zero => simp
    | succ k ih =>
      exact (ih (Nat.le_of_succ_le hk)).trans
        (integral_pbValue_le_succ ℱ hA ps (monotone_indicator_Ici r)
          (abs_indicator_Ici_le_one r) hk (hp k hk))
  have hmain : pbValue ps f 0 0 ≤ ∫ ω, f (adaptedCount A ps.length ω) ∂P := by
    simpa [pbValue_length] using hchain ps.length le_rfl
  rw [pbValue_zero_Ici_eq_real, integral_indicator_Ici_adaptedCount ℱ hA] at hmain
  exact Ici_le_of_measureReal_le hmain

/-- **Adapted Poisson-binomial domination (upper envelope)**: if `A t` is `ℱ (t + 1)`-measurable
and `P[A t | ℱ t] ≤ ps[t]` a.e. for all `t < ps.length`, then `PMF.poissonBinomial ps`
stochastically dominates the law of `adaptedCount A ps.length`. -/
theorem poissonBinomial_stochasticallyDominates_adaptedCount {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length),
      P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P] fun _ => (ps[t] : ℝ)) :
    StochasticallyDominates (PMF.poissonBinomial ps).toMeasure
      (P.map (adaptedCount A ps.length)) := by
  rw [stochasticallyDominates_nat_iff_Ici]
  intro r
  let f : ℕ → ℝ := (Set.Ici r).indicator (fun _ => 1)
  have hchain (k : ℕ) (hk : k ≤ ps.length) :
      ∫ ω, pbValue ps f k (adaptedCount A k ω) ∂P ≤ pbValue ps f 0 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      exact (integral_pbValue_succ_le ℱ hA ps (monotone_indicator_Ici r)
        (abs_indicator_Ici_le_one r) hk (hp k hk)).trans (ih (Nat.le_of_succ_le hk))
  have hmain : ∫ ω, f (adaptedCount A ps.length ω) ∂P ≤ pbValue ps f 0 0 := by
    simpa [pbValue_length] using hchain ps.length le_rfl
  rw [pbValue_zero_Ici_eq_real, integral_indicator_Ici_adaptedCount ℱ hA] at hmain
  exact Ici_le_of_measureReal_le hmain

/-- If `adaptedCount A n ω < r` and `B t` agrees with `A t` at `ω` for every `t < n` where
`adaptedCount A t ω < r`, then `adaptedCount B n ω = adaptedCount A n ω`. -/
theorem adaptedCount_congr_of_lt {Ω : Type*} {A B : ℕ → Set Ω} {r n : ℕ} {ω : Ω}
    (hlt : adaptedCount A n ω < r)
    (hiff : ∀ t < n, adaptedCount A t ω < r → (ω ∈ B t ↔ ω ∈ A t)) :
    adaptedCount B n ω = adaptedCount A n ω := by
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  have ht_lt : adaptedCount A t ω < r := (adaptedCount_mono A ω ht.le).trans_lt hlt
  by_cases hmem : ω ∈ A t <;> simp [hiff t ht ht_lt, hmem]

private theorem adaptedCount_min_eq_of_union {Ω : Type*} (A : ℕ → Set Ω) (r n : ℕ) (ω : Ω) :
    min (adaptedCount A n ω) r =
      min (adaptedCount (fun t => A t ∪ {ω' | r ≤ adaptedCount A t ω'}) n ω) r := by
  let A' := fun t => A t ∪ {ω' | r ≤ adaptedCount A t ω'}
  have hle : adaptedCount A n ω ≤ adaptedCount A' n ω := by
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases ht : ω ∈ A t
    · simp [A', ht]
    · simp [ht]
  by_cases hreach : r ≤ adaptedCount A n ω
  · have hreach' : r ≤ adaptedCount A' n ω := hreach.trans hle
    rw [min_eq_right hreach, min_eq_right hreach']
  · have hlt : adaptedCount A n ω < r := not_le.mp hreach
    have heq : adaptedCount A' n ω = adaptedCount A n ω :=
      adaptedCount_congr_of_lt hlt fun t _ ht => by simp [A', not_le.mpr ht]
    rw [heq]

private theorem adaptedCount_min_eq_of_inter {Ω : Type*} (A : ℕ → Set Ω) (r n : ℕ) (ω : Ω) :
    min (adaptedCount A n ω) r =
      min (adaptedCount (fun t => A t ∩ {ω' | adaptedCount A t ω' < r}) n ω) r := by
  let A'' := fun t => A t ∩ {ω' | adaptedCount A t ω' < r}
  have hle : adaptedCount A'' n ω ≤ adaptedCount A n ω := by
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases ht : ω ∈ A'' t
    · simp [A'', ht, ht.1]
    · simp [ht]
  by_cases hreach : r ≤ adaptedCount A'' n ω
  · have hreach' : r ≤ adaptedCount A n ω := hreach.trans hle
    rw [min_eq_right hreach', min_eq_right hreach]
  · have hnot : adaptedCount A n ω < r := by
      by_contra hc
      have hge : r ≤ adaptedCount A n ω := not_lt.mp hc
      have heq_lt (t : ℕ) (htr : adaptedCount A t ω < r) :
          adaptedCount A'' t ω = adaptedCount A t ω :=
        adaptedCount_congr_of_lt htr fun s _ hs => by simp [A'', hs]
      have hex : ∃ t ≤ n, r ≤ adaptedCount A t ω := ⟨n, le_rfl, hge⟩
      have ht₀_spec := Nat.find_spec hex
      cases hfind : Nat.find hex with
      | zero =>
        rw [hfind, adaptedCount_zero] at ht₀_spec
        have hr0 : r = 0 := Nat.le_zero.mp ht₀_spec.2
        subst hr0
        exact hreach (Nat.zero_le _)
      | succ t₁ =>
        rw [hfind] at ht₀_spec
        have ht₁_lt : adaptedCount A t₁ ω < r := by
          by_contra hc₁
          have hmin : ¬ (t₁ ≤ n ∧ r ≤ adaptedCount A t₁ ω) :=
            Nat.find_min hex (by rw [hfind]; exact Nat.lt_succ_self t₁)
          exact hmin ⟨Nat.le_of_succ_le ht₀_spec.1, not_lt.mp hc₁⟩
        have hA''t₁ : adaptedCount A'' t₁ ω = adaptedCount A t₁ ω := heq_lt t₁ ht₁_lt
        have hstep : adaptedCount A'' (t₁ + 1) ω = adaptedCount A (t₁ + 1) ω := by
          rw [adaptedCount_succ, adaptedCount_succ, hA''t₁]
          by_cases hmem : ω ∈ A t₁ <;> simp [A'', hmem, ht₁_lt]
        have hr_A'' : r ≤ adaptedCount A'' n ω := by
          calc
            r ≤ adaptedCount A (t₁ + 1) ω := ht₀_spec.2
            _ = adaptedCount A'' (t₁ + 1) ω := hstep.symm
            _ ≤ adaptedCount A'' n ω := adaptedCount_mono A'' ω ht₀_spec.1
        exact absurd hr_A'' hreach
    have heq : adaptedCount A'' n ω = adaptedCount A n ω :=
      adaptedCount_congr_of_lt hnot fun t _ ht => by simp [A'', ht]
    rw [heq]

/-- Extending an `ℱ (t + 1)`-measurable event `E` by `Sᶜ` (`S` `ℱ t`-measurable) lifts an
a.e. conditional lower bound `p ≤ P[E | ℱ t]` on `P.restrict S` to all of `P`. -/
theorem ae_le_condExp_union_compl {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {t : ℕ}
    {E S : Set Ω} (hE : MeasurableSet[ℱ (t + 1)] E) (hS_ℱ : MeasurableSet[ℱ t] S) {p : I}
    (hp : (fun _ => (p : ℝ)) ≤ᵐ[P.restrict S] P[E.indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    (fun _ => (p : ℝ)) ≤ᵐ[P] P[(E ∪ Sᶜ).indicator (fun _ => (1 : ℝ)) | ℱ t] := by
  have hS : MeasurableSet S := ℱ.le t _ hS_ℱ
  have hind_eq :
      (E ∪ Sᶜ).indicator (fun _ => (1 : ℝ)) =
        S.indicator (E.indicator (fun _ => 1)) + Sᶜ.indicator (fun _ => 1) := by
    ext ω
    by_cases hωS : ω ∈ S
    · by_cases hωE : ω ∈ E <;> simp [hωS, hωE]
    · simp [hωS]
  have hI_int : Integrable (E.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (ℱ.le (t + 1) _ hE)
  have hSI_int : Integrable (S.indicator (E.indicator (fun _ => (1 : ℝ)))) P :=
    hI_int.indicator hS
  have hSc_int : Integrable (Sᶜ.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator hS.compl
  have hce :
      P[(E ∪ Sᶜ).indicator (fun _ => (1 : ℝ)) | ℱ t] =ᵐ[P]
        S.indicator (P[E.indicator (fun _ => (1 : ℝ)) | ℱ t]) + Sᶜ.indicator (fun _ => 1) := by
    rw [hind_eq]
    calc
      P[S.indicator (E.indicator (fun _ => (1 : ℝ))) + Sᶜ.indicator (fun _ => (1 : ℝ)) | ℱ t]
        =ᵐ[P] P[S.indicator (E.indicator (fun _ => (1 : ℝ))) | ℱ t] +
            P[Sᶜ.indicator (fun _ => (1 : ℝ)) | ℱ t] :=
          condExp_add hSI_int hSc_int (ℱ t)
      _ =ᵐ[P] S.indicator (P[E.indicator (fun _ => (1 : ℝ)) | ℱ t]) +
            Sᶜ.indicator (P[fun _ : Ω => (1 : ℝ) | ℱ t]) :=
          (condExp_indicator hI_int hS_ℱ).add
            (condExp_indicator (integrable_const (1 : ℝ)) hS_ℱ.compl)
      _ =ᵐ[P] S.indicator (P[E.indicator (fun _ => (1 : ℝ)) | ℱ t]) +
            Sᶜ.indicator (fun _ => 1) := by
          rw [condExp_const (ℱ.le t) (1 : ℝ)]
  have hrest : ∀ᵐ ω ∂P, ω ∈ S → (p : ℝ) ≤ P[E.indicator (fun _ => (1 : ℝ)) | ℱ t] ω :=
    (ae_restrict_iff' hS).mp hp
  filter_upwards [hce, hrest] with ω hω hSω
  rw [hω]
  by_cases hmem : ω ∈ S
  · simp [hmem, hSω hmem]
  · simp [hmem, p.2.2]

private theorem map_min_adaptedCount_eq {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    (ℱ : Filtration ℕ m) {A B : ℕ → Set Ω} (hB : ∀ t, MeasurableSet[ℱ (t + 1)] (B t))
    (n r : ℕ) (heq : ∀ ω, min (adaptedCount A n ω) r = min (adaptedCount B n ω) r) :
    (P.map (adaptedCount B n)).map (fun k => min k r) =
      P.map (fun ω => min (adaptedCount A n ω) r) := by
  have hm : Measurable (adaptedCount B n) := (measurable_adaptedCount ℱ hB n).mono (ℱ.le _) le_rfl
  rw [Measure.map_map measurable_from_top hm]
  congr 1
  ext ω
  exact (heq ω).symm

/-- **Active-before-target adapted domination (lower envelope)**: if `P[A t | ℱ t] ≥ ps[t]`
holds a.e. on the active event `{ω | adaptedCount A t ω < r}`, then the capped count
`min (adaptedCount A ps.length) r` dominates `min · r` of `PMF.poissonBinomial ps`. -/
theorem adaptedCount_min_stochasticallyDominates_poissonBinomial {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (ps : List I) (r : ℕ)
    (hp : ∀ t (ht : t < ps.length),
      (fun _ => (ps[t] : ℝ)) ≤ᵐ[P.restrict {ω | adaptedCount A t ω < r}]
        P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    StochasticallyDominates (P.map fun ω => min (adaptedCount A ps.length ω) r)
      ((PMF.poissonBinomial ps).map fun k => min k r).toMeasure := by
  let A' : ℕ → Set Ω := fun t => A t ∪ ({ω | adaptedCount A t ω < r})ᶜ
  have hA'eq (t : ℕ) : A' t = A t ∪ {ω | r ≤ adaptedCount A t ω} := by
    ext ω
    simp [A', not_lt]
  have hA' : ∀ t, MeasurableSet[ℱ (t + 1)] (A' t) := fun t =>
    (hA t).union ((measurable_adaptedCount ℱ hA t).mono (ℱ.mono t.le_succ) le_rfl
      measurableSet_Iio).compl
  have hp' : ∀ t (ht : t < ps.length),
      (fun _ => (ps[t] : ℝ)) ≤ᵐ[P] P[(A' t).indicator (fun _ => (1 : ℝ)) | ℱ t] := fun t ht =>
    ae_le_condExp_union_compl ℱ (hA t) ((measurable_adaptedCount ℱ hA t) measurableSet_Iio)
      (hp t ht)
  have hdom' := adaptedCount_stochasticallyDominates_poissonBinomial ℱ hA' ps hp'
  have hmap := hdom'.map measurable_from_top (fun _ _ h => min_le_min_right r h)
  rw [map_min_adaptedCount_eq (A := A) ℱ hA' ps.length r (fun ω => by
      have heq := adaptedCount_min_eq_of_union A r ps.length ω
      simpa only [← hA'eq] using heq),
    PMF.toMeasure_map _ _ measurable_from_top] at hmap
  exact hmap

/-- **Active-before-target binomial tail bound**: if `P[A t | ℱ t] ≥ p` a.e. on
`{adaptedCount A t < r}` for every `t < n`, then
`P.real {ω | adaptedCount A n ω < r} ≤ (binomial n p).real (Set.Iio r)`. -/
theorem adaptedCount_real_Iio_le_binomial {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (n r : ℕ) (p : I)
    (hp : ∀ t, t < n →
      (fun _ => (p : ℝ)) ≤ᵐ[P.restrict {ω | adaptedCount A t ω < r}]
        P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    P.real {ω | adaptedCount A n ω < r} ≤ (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
  let ps := List.replicate n p
  have hps : ps.length = n := List.length_replicate
  have hdom := adaptedCount_min_stochasticallyDominates_poissonBinomial ℱ hA ps r fun t ht => by
    have ht' : t < n := by simpa [ps] using ht
    simpa [ps] using hp t ht'
  rw [hps] at hdom
  have hm : Measurable (adaptedCount A n) :=
    (measurable_adaptedCount ℱ hA n).mono (ℱ.le _) le_rfl
  have hm_min : Measurable (fun ω => min (adaptedCount A n ω) r) :=
    (measurable_from_top : Measurable fun k => min k r).comp hm
  have hle := hdom.le_real_Iio r
  have hset₁ :
      (fun ω => min (adaptedCount A n ω) r) ⁻¹' Set.Iio r = {ω | adaptedCount A n ω < r} := by
    ext ω
    simp [min_lt_iff]
  have hset₂ : (fun k => min k r) ⁻¹' Set.Iio r = Set.Iio r := by
    ext k
    simp [min_lt_iff]
  have hL : (P.map fun ω => min (adaptedCount A n ω) r).real (Set.Iio r) =
      P.real {ω | adaptedCount A n ω < r} := by
    rw [measureReal_def, Measure.map_apply hm_min measurableSet_Iio, ← measureReal_def, hset₁]
  have hR : ((PMF.poissonBinomial ps).map fun k => min k r).toMeasure.real (Set.Iio r) =
      (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
    rw [measureReal_def, ← PMF.toMeasure_map (fun k => min k r) _ measurable_from_top,
      Measure.map_apply measurable_from_top measurableSet_Iio, hset₂,
      PMF.toMeasure_poissonBinomial_replicate, ← measureReal_def]
  rw [← hL, ← hR]
  exact hle

/-- **Active-before-target adapted domination (upper envelope)**: if `P[A t | ℱ t] ≤ ps[t]` a.e.
on `{ω | adaptedCount A t ω < r}`, then `min · r` of `PMF.poissonBinomial ps` stochastically
dominates `min (adaptedCount A ps.length) r`. -/
theorem poissonBinomial_stochasticallyDominates_adaptedCount_min {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) (ps : List I) (r : ℕ)
    (hp : ∀ t (ht : t < ps.length),
      P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P.restrict {ω | adaptedCount A t ω < r}]
        fun _ => (ps[t] : ℝ)) :
    StochasticallyDominates ((PMF.poissonBinomial ps).map fun k => min k r).toMeasure
      (P.map fun ω => min (adaptedCount A ps.length ω) r) := by
  let A'' : ℕ → Set Ω := fun t => A t ∩ {ω | adaptedCount A t ω < r}
  have hA'' : ∀ t, MeasurableSet[ℱ (t + 1)] (A'' t) := by
    intro t
    refine (hA t).inter ?_
    exact ((measurable_adaptedCount ℱ hA t).mono (ℱ.mono t.le_succ) le_rfl) measurableSet_Iio
  have hp'' : ∀ t (ht : t < ps.length),
      P[(A'' t).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P] fun _ => (ps[t] : ℝ) := by
    intro t ht
    let S : Set Ω := {ω | adaptedCount A t ω < r}
    have hSm_ℱ : MeasurableSet[ℱ t] S :=
      (measurable_adaptedCount ℱ hA t) measurableSet_Iio
    have hSm : MeasurableSet S := ℱ.le t _ hSm_ℱ
    have hind_eq :
        (A'' t).indicator (fun _ => (1 : ℝ)) =
          S.indicator ((A t).indicator (fun _ => 1)) := by
      ext ω
      by_cases hS : ω ∈ S
      · by_cases hAt : ω ∈ A t <;> simp [A'', S, hS, hAt]
      · simp [A'', S, hS]
    have hI_int : Integrable ((A t).indicator (fun _ => (1 : ℝ))) P :=
      (integrable_const 1).indicator (ℱ.le (t + 1) _ (hA t))
    have hce :
        P[(A'' t).indicator (fun _ => (1 : ℝ)) | ℱ t] =ᵐ[P]
          S.indicator (P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) := by
      rw [hind_eq]
      exact condExp_indicator hI_int hSm_ℱ
    have hrest : ∀ᵐ ω ∂P, ω ∈ S → P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t] ω ≤ (ps[t] : ℝ) :=
      (ae_restrict_iff' hSm).mp (hp t ht)
    filter_upwards [hce, hrest] with ω hω hSω
    rw [hω]
    by_cases hmem : ω ∈ S
    · simp only [Set.indicator_of_mem hmem]
      exact hSω hmem
    · simp only [Set.indicator_of_notMem hmem]
      exact (ps[t]).2.1
  have hdom'' := poissonBinomial_stochasticallyDominates_adaptedCount ℱ hA'' ps hp''
  have hmap := hdom''.map measurable_from_top (fun _ _ h => min_le_min_right r h)
  rw [map_min_adaptedCount_eq ℱ hA'' ps.length r (adaptedCount_min_eq_of_inter A r ps.length),
    PMF.toMeasure_map _ _ measurable_from_top] at hmap
  exact hmap

end FiltrationComparison

section KernelTraj

/-- Shift a `ℕ`-indexed filtration forward by `a` steps. -/
@[expose]
def shiftFiltration {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m) (a : ℕ) :
    Filtration ℕ m where
  seq t := ℱ (a + t)
  mono' _ _ hij := ℱ.mono (Nat.add_le_add_left hij a)
  le' t := ℱ.le (a + t)

@[simp]
theorem shiftFiltration_apply {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m)
    (a t : ℕ) :
    shiftFiltration ℱ a t = ℱ (a + t) :=
  rfl

/-- Conditional expectation of a measurable event indicator under `Kernel.traj κ a x₀` at time
`b ≥ a` equals the `Kernel.traj κ b` real probability at `Preorder.frestrictLe b x`. -/
theorem traj_condExp_indicator_eq
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {a b : ℕ} (hab : a ≤ b) (x₀ : Π i : Finset.Iic a, X i)
    {E : Set (Π n, X n)} (hE : MeasurableSet E) :
    (Kernel.traj κ a x₀)[E.indicator (fun _ => (1 : ℝ)) | Filtration.piLE b] =ᵐ[
        Kernel.traj κ a x₀]
      fun x => (Kernel.traj κ b (Preorder.frestrictLe b x)).real E := by
  have hint : Integrable (E.indicator (1 : (Π n, X n) → ℝ)) (Kernel.traj κ a x₀) :=
    (integrable_const 1).indicator hE
  have htraj := Kernel.condExp_traj (κ := κ) (a := a) (b := b) hab (x₀ := x₀) hint
  filter_upwards [htraj] with x hx
  rw [integral_indicator_one hE] at hx
  exact hx

private theorem hA_shiftFiltration {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    {a : ℕ} {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (a + t + 1)] (A t)) :
    ∀ t, MeasurableSet[shiftFiltration Filtration.piLE a (t + 1)] (A t) := fun t => by
  change MeasurableSet[Filtration.piLE (a + (t + 1))] (A t)
  rw [← add_assoc]
  exact hA t

/-- Specialization of `adaptedCount_stochasticallyDominates_poissonBinomial` to Ionescu-Tulcea
trajectories `ProbabilityTheory.Kernel.traj κ a x₀`. -/
theorem traj_adaptedCount_stochasticallyDominates_poissonBinomial
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {a : ℕ} (x₀ : Π i : Finset.Iic a, X i)
    {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (a + t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length), ∀ᵐ x ∂Kernel.traj κ a x₀,
      (ps[t] : ℝ) ≤ (Kernel.traj κ (a + t) (Preorder.frestrictLe (a + t) x)).real (A t)) :
    StochasticallyDominates ((Kernel.traj κ a x₀).map (adaptedCount A ps.length))
      (PMF.poissonBinomial ps).toMeasure := by
  refine adaptedCount_stochasticallyDominates_poissonBinomial
    (shiftFiltration Filtration.piLE a) (hA_shiftFiltration hA) ps ?_
  intro t ht
  have hce := traj_condExp_indicator_eq κ (Nat.le_add_right a t) x₀
    (Filtration.piLE.le (a + t + 1) _ (hA t))
  filter_upwards [hce, hp t ht] with x hx hpx
  exact hpx.trans_eq hx.symm

/-- Upper-envelope specialization of `poissonBinomial_stochasticallyDominates_adaptedCount` to
`ProbabilityTheory.Kernel.traj κ a x₀`. -/
theorem poissonBinomial_stochasticallyDominates_traj_adaptedCount
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {a : ℕ} (x₀ : Π i : Finset.Iic a, X i)
    {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (a + t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length), ∀ᵐ x ∂Kernel.traj κ a x₀,
      (Kernel.traj κ (a + t) (Preorder.frestrictLe (a + t) x)).real (A t) ≤ (ps[t] : ℝ)) :
    StochasticallyDominates (PMF.poissonBinomial ps).toMeasure
      ((Kernel.traj κ a x₀).map (adaptedCount A ps.length)) := by
  refine poissonBinomial_stochasticallyDominates_adaptedCount
    (shiftFiltration Filtration.piLE a) (hA_shiftFiltration hA) ps ?_
  intro t ht
  have hce := traj_condExp_indicator_eq κ (Nat.le_add_right a t) x₀
    (Filtration.piLE.le (a + t + 1) _ (hA t))
  filter_upwards [hce, hp t ht] with x hx hpx
  exact hx.trans_le hpx

private theorem measurable_traj_real {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (t + 1)] (A t)) (t : ℕ) :
    Measurable fun x => (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A t) :=
  ENNReal.measurable_toReal.comp
    ((Kernel.measurable_coe _ (Filtration.piLE.le (t + 1) _ (hA t))).comp
      (Preorder.measurable_frestrictLe t))

private noncomputable abbrev trajInitMeasure {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) : Measure (Π i : Finset.Iic 0, X i) :=
  μ₀.map (MeasurableEquiv.piUnique fun i : Finset.Iic 0 => X i).symm

private instance trajInitMeasure_isProbability {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (trajInitMeasure μ₀) :=
  ⟨by
    rw [trajInitMeasure, Measure.map_apply (MeasurableEquiv.measurable _) MeasurableSet.univ,
      Set.preimage_univ, measure_univ]⟩

private theorem trajMeasure_ae_traj {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) {Q : (t : ℕ) → t < n → (Π n, X n) → Prop}
    (hQm : ∀ t (ht : t < n), MeasurableSet {x | ¬ Q t ht x})
    (hq : ∀ t (ht : t < n), ∀ᵐ x ∂Kernel.trajMeasure μ₀ κ, Q t ht x) :
    ∀ᵐ x₀ ∂trajInitMeasure μ₀,
      ∀ t (ht : t < n), ∀ᵐ x ∂Kernel.traj κ 0 x₀, Q t ht x := by
  rw [ae_all_iff]
  intro t
  rw [ae_all_iff]
  intro ht
  have hzero : (Kernel.trajMeasure μ₀ κ) {x | ¬ Q t ht x} = 0 := ae_iff.mp (hq t ht)
  change ((Kernel.traj κ 0) ∘ₘ trajInitMeasure μ₀) {x | ¬ Q t ht x} = 0 at hzero
  rw [Measure.bind_apply (hQm t ht) (Kernel.traj κ 0).measurable.aemeasurable,
    lintegral_eq_zero_iff (Kernel.measurable_coe (Kernel.traj κ 0) (hQm t ht))] at hzero
  filter_upwards [hzero] with x₀ hx₀
  exact ae_iff.mpr hx₀

private theorem trajMeasure_map_apply {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {f : (Π n, X n) → ℕ} (hf : Measurable f)
    {U : Set ℕ} (hU : MeasurableSet U) :
    ((Kernel.trajMeasure μ₀ κ).map f) U =
      ∫⁻ x₀, ((Kernel.traj κ 0 x₀).map f) U ∂trajInitMeasure μ₀ := by
  rw [Measure.map_apply hf hU]
  have hbind : (Kernel.trajMeasure μ₀ κ) (f ⁻¹' U) =
      ∫⁻ x₀, (Kernel.traj κ 0 x₀) (f ⁻¹' U) ∂trajInitMeasure μ₀ := by
    change ((Kernel.traj κ 0) ∘ₘ trajInitMeasure μ₀) (f ⁻¹' U) = _
    exact Measure.bind_apply (hf hU) (Kernel.traj κ 0).measurable.aemeasurable
  rw [hbind]
  exact lintegral_congr fun x₀ => (Measure.map_apply hf hU).symm

/-- Specialization of `adaptedCount_stochasticallyDominates_poissonBinomial` to
`ProbabilityTheory.Kernel.trajMeasure μ₀ κ` for events measurable at step `t + 1`. -/
theorem trajMeasure_adaptedCount_stochasticallyDominates_poissonBinomial
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)]
    {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length), ∀ᵐ x ∂Kernel.trajMeasure μ₀ κ,
      (ps[t] : ℝ) ≤ (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A t)) :
    StochasticallyDominates ((Kernel.trajMeasure μ₀ κ).map (adaptedCount A ps.length))
      (PMF.poissonBinomial ps).toMeasure := by
  have hm : Measurable (adaptedCount A ps.length) :=
    (measurable_adaptedCount Filtration.piLE hA ps.length).mono (Filtration.piLE.le _) le_rfl
  have hae_x₀ := trajMeasure_ae_traj μ₀ κ ps.length
    (fun t _ => (measurableSet_le measurable_const (measurable_traj_real κ hA t)).compl) hp
  intro U hUm hU
  rw [trajMeasure_map_apply μ₀ κ hm hUm]
  calc
    (PMF.poissonBinomial ps).toMeasure U
      = ∫⁻ _ : Π i : Finset.Iic 0, X i,
          (PMF.poissonBinomial ps).toMeasure U ∂trajInitMeasure μ₀ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ x₀, ((Kernel.traj κ 0 x₀).map (adaptedCount A ps.length)) U ∂trajInitMeasure μ₀ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae_x₀] with x₀ hx₀
        refine (adaptedCount_stochasticallyDominates_poissonBinomial Filtration.piLE hA ps
          fun t ht => ?_) U hUm hU
        have hce := traj_condExp_indicator_eq κ (Nat.zero_le t) x₀
          (Filtration.piLE.le (t + 1) _ (hA t))
        filter_upwards [hce, hx₀ t ht] with x hx hpx
        exact hpx.trans_eq hx.symm

/-- Upper-envelope specialization of `poissonBinomial_stochasticallyDominates_adaptedCount` to
`ProbabilityTheory.Kernel.trajMeasure μ₀ κ` for events measurable at step `t + 1`. -/
theorem poissonBinomial_stochasticallyDominates_trajMeasure_adaptedCount
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)]
    {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (t + 1)] (A t)) (ps : List I)
    (hp : ∀ t (ht : t < ps.length), ∀ᵐ x ∂Kernel.trajMeasure μ₀ κ,
      (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A t) ≤ (ps[t] : ℝ)) :
    StochasticallyDominates (PMF.poissonBinomial ps).toMeasure
      ((Kernel.trajMeasure μ₀ κ).map (adaptedCount A ps.length)) := by
  have hm : Measurable (adaptedCount A ps.length) :=
    (measurable_adaptedCount Filtration.piLE hA ps.length).mono (Filtration.piLE.le _) le_rfl
  have hae_x₀ := trajMeasure_ae_traj μ₀ κ ps.length
    (fun t _ => (measurableSet_le (measurable_traj_real κ hA t) measurable_const).compl) hp
  intro U hUm hU
  rw [trajMeasure_map_apply μ₀ κ hm hUm]
  calc
    ∫⁻ x₀, ((Kernel.traj κ 0 x₀).map (adaptedCount A ps.length)) U ∂trajInitMeasure μ₀
      ≤ ∫⁻ _ : Π i : Finset.Iic 0, X i,
          (PMF.poissonBinomial ps).toMeasure U ∂trajInitMeasure μ₀ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae_x₀] with x₀ hx₀
        refine (poissonBinomial_stochasticallyDominates_adaptedCount Filtration.piLE hA ps
          fun t ht => ?_) U hUm hU
        have hce := traj_condExp_indicator_eq κ (Nat.zero_le t) x₀
          (Filtration.piLE.le (t + 1) _ (hA t))
        filter_upwards [hce, hx₀ t ht] with x hx hpx
        exact hx.trans_le hpx
    _ = (PMF.poissonBinomial ps).toMeasure U := by
        rw [lintegral_const, measure_univ, mul_one]

end KernelTraj

end Cslib.Probability

namespace Cslib.Probability.PMF

open MeasureTheory
open scoped BigOperators ENNReal unitInterval

/-- Finite-horizon sequential `PMF` process generated by history-dependent transition distributions
`step t : (Fin t → α) → PMF α`. -/
@[expose]
noncomputable def seqProcess {α : Type*} (step : ∀ t : ℕ, (Fin t → α) → PMF α) :
    (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure Fin.elim0
  | n + 1 => (seqProcess step n).bind fun h => (step n h).map fun a => Fin.snoc h a

/-- Cumulative number of successes along a history `h : Fin n → α` for predicates
`E t : (Fin t → α) → Set α`. -/
@[expose]
noncomputable def seqCount {α : Type*} (E : ∀ t : ℕ, (Fin t → α) → Set α) (n : ℕ)
    (h : Fin n → α) : ℕ := by
  classical
  exact ∑ t : Fin n,
    if h t ∈ E t.1 (fun j : Fin t.1 => h (Fin.castLT j (lt_trans j.isLt t.isLt))) then 1 else 0

@[simp]
theorem seqCount_zero {α : Type*} (E : ∀ t : ℕ, (Fin t → α) → Set α) (h : Fin 0 → α) :
    seqCount E 0 h = 0 := by
  simp [seqCount]

private theorem snoc_castLT {α : Type*} {n : ℕ} (h : Fin n → α) (a : α)
    (k : ℕ) (hk : k < n) (hk' : k < n + 1) :
    Fin.snoc (α := fun _ => α) h a ⟨k, hk'⟩ = h ⟨k, hk⟩ := by
  simp [Fin.snoc, hk]

theorem seqCount_snoc {α : Type*} (E : ∀ t : ℕ, (Fin t → α) → Set α) (n : ℕ)
    (h : Fin n → α) (a : α) :
    seqCount E (n + 1) (Fin.snoc h a) =
      seqCount E n h + by classical exact if a ∈ E n h then 1 else 0 := by
  classical
  simp only [seqCount]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, Fin.val_last]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    have hcast : Fin.snoc (α := fun _ => α) h a t.castSucc = h t :=
      snoc_castLT h a t.1 t.isLt _
    have hhist :
        (fun j : Fin t.1 =>
            Fin.snoc (α := fun _ => α) h a
              (Fin.castLT j
                (lt_trans j.isLt (Nat.lt_trans t.isLt (Nat.lt_succ_self n))))) =
          fun j : Fin t.1 => h (Fin.castLT j (lt_trans j.isLt t.isLt)) := by
      ext j
      exact snoc_castLT h a j.1 (lt_trans j.isLt t.isLt) _
    simp only [Fin.val_castSucc]
    simp_rw [hcast, hhist]
  · have heq :
        (fun j : Fin n =>
            Fin.snoc (α := fun _ => α) h a
              (Fin.castLT j (lt_trans j.isLt (Nat.lt_succ_self n)))) =
          h := by
      ext j
      exact snoc_castLT h a j.1 j.isLt _
    rw [heq]

private theorem seqProcess_tsum_toReal {α : Type*} (p : PMF α) (f : α → ℝ)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Summable fun x => (p x).toReal * f x := by
  refine Summable.of_norm_bounded ((PMF.summable_toReal p).mul_right C) fun x => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hC x) ENNReal.toReal_nonneg

private theorem abs_tsum_pmf_mul_le_one {α : Type*} (p : PMF α) (F : α → ℝ)
    (hF : ∀ a, |F a| ≤ 1) :
    |∑' a, (p a).toReal * F a| ≤ 1 := by
  have hs : Summable fun a => (p a).toReal * F a := seqProcess_tsum_toReal p F hF
  have hg : Summable fun a => (p a).toReal := PMF.summable_toReal p
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hlow : -1 ≤ ∑' a, (p a).toReal * F a := by
      have hneg : ∑' a, -(p a).toReal = -1 := by rw [tsum_neg, PMF.tsum_toReal p]
      rw [← hneg]
      refine hg.neg.tsum_le_tsum (fun a => ?_) hs
      have ha := (abs_le.mp (hF a)).1
      calc
        -(p a).toReal = (p a).toReal * (-1) := by ring
        _ ≤ (p a).toReal * F a := mul_le_mul_of_nonneg_left ha ENNReal.toReal_nonneg
    exact hlow
  · calc
      ∑' a, (p a).toReal * F a ≤ ∑' a, (p a).toReal := by
        refine hs.tsum_le_tsum (fun a => ?_) hg
        exact mul_le_of_le_one_right ENNReal.toReal_nonneg (abs_le.mp (hF a)).2
      _ = 1 := PMF.tsum_toReal p

private def snocEquiv (α : Type*) (n : ℕ) : (Fin n → α) × α ≃ (Fin (n + 1) → α) :=
  (Equiv.prodComm (Fin n → α) α).trans (Fin.snocEquiv fun _ => α)

private theorem seqProcess_snoc {α : Type*} (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (n : ℕ) (h₀ : Fin n → α) (a : α) :
    seqProcess step (n + 1) (Fin.snoc (α := fun _ => α) h₀ a) =
      seqProcess step n h₀ * step n h₀ a := by
  rw [seqProcess, PMF.bind_apply]
  rw [tsum_eq_single h₀]
  · rw [PMF.map_apply, tsum_eq_single a]
    · simp
    · intro b hb
      have hne : Fin.snoc (α := fun _ => α) h₀ a ≠ Fin.snoc (α := fun _ => α) h₀ b := fun heq =>
        hb (Fin.snoc_right_injective (α := fun _ => α) h₀ heq).symm
      simp [hne]
  · intro h hh
    have hmap0 :
        ((step n h).map fun b => Fin.snoc (α := fun _ => α) h b)
          (Fin.snoc (α := fun _ => α) h₀ a) = 0 := by
      rw [PMF.map_apply]
      refine (tsum_congr fun b => ?_).trans tsum_zero
      have hne : Fin.snoc (α := fun _ => α) h₀ a ≠ Fin.snoc (α := fun _ => α) h b := fun heq =>
        hh (Fin.snoc_injective2 (α := fun _ => α) heq).1.symm
      simp [hne]
    simp [hmap0]

private theorem tsum_toReal_seqProcess_step {α : Type*} (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (n : ℕ) (g : (Fin (n + 1) → α) → ℝ) {C : ℝ} (hC : ∀ h, |g h| ≤ C) :
    ∑' h : Fin (n + 1) → α, ((seqProcess step (n + 1)) h).toReal * g h =
      ∑' h : Fin n → α, ((seqProcess step n) h).toReal *
        ∑' a : α, ((step n h) a).toReal * g (Fin.snoc h a) := by
  by_cases hα : Nonempty α
  · have hC0 : 0 ≤ C := (abs_nonneg (g fun _ => Classical.arbitrary α)).trans (hC _)
    let F : (Fin n → α) × α → ℝ := fun p =>
      ((seqProcess step n) p.1).toReal * (((step n p.1) p.2).toReal * g (Fin.snoc p.1 p.2))
    let G : (Fin n → α) × α → ℝ := fun p =>
      ((seqProcess step n) p.1).toReal * ((step n p.1) p.2).toReal * C
    have hs_G : Summable G := by
      refine (summable_prod_of_nonneg (f := G) fun _ =>
        mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hC0).mpr ?_
      have h1 : Summable fun h₀ : Fin n → α => ((seqProcess step n) h₀).toReal * C :=
        (PMF.summable_toReal _).mul_right C
      have h2 (h₀ : Fin n → α) :
          HasSum (fun a : α => G (h₀, a)) (((seqProcess step n) h₀).toReal * C) := by
        have hsum := (PMF.summable_toReal (step n h₀)).hasSum
        have hmul := (hsum.mul_left ((seqProcess step n) h₀).toReal).mul_right C
        simpa [G, PMF.tsum_toReal, mul_assoc] using hmul
      refine ⟨fun h₀ => (h2 h₀).summable, ?_⟩
      have heq : (fun h₀ => ∑' a, G (h₀, a)) = fun h₀ => ((seqProcess step n) h₀).toReal * C := by
        ext h₀
        exact (h2 h₀).tsum_eq
      rw [heq]
      exact h1
    have hs_prod : Summable F := by
      refine Summable.of_norm_bounded hs_G fun p => ?_
      simp only [F, G, Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hC _) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    calc
      ∑' h : Fin (n + 1) → α, ((seqProcess step (n + 1)) h).toReal * g h
        = ∑' p : (Fin n → α) × α,
            ((seqProcess step (n + 1)) (snocEquiv α n p)).toReal * g (snocEquiv α n p) :=
          (Equiv.tsum_eq (snocEquiv α n) fun h =>
            ((seqProcess step (n + 1)) h).toReal * g h).symm
      _ = ∑' p : (Fin n → α) × α, F p := by
          refine tsum_congr fun p => ?_
          simp only [snocEquiv, Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply,
            Prod.fst_swap, Prod.snd_swap, F]
          rw [seqProcess_snoc, ENNReal.toReal_mul, mul_assoc]
      _ = ∑' h : Fin n → α, ∑' a : α, F (h, a) := hs_prod.tsum_prod
      _ = ∑' h : Fin n → α, ((seqProcess step n) h).toReal *
            ∑' a : α, ((step n h) a).toReal * g (Fin.snoc h a) := by
          refine tsum_congr fun h => ?_
          dsimp only [F]
          exact tsum_mul_left
  · rw [not_nonempty_iff] at hα
    have : IsEmpty (Fin (n + 1) → α) := ⟨fun h => hα.false (h (Fin.last n))⟩
    simp [tsum_empty]

private theorem seqCount_stochasticallyDominates_poissonBinomial_of_length {α : Type*}
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (E : ∀ t : ℕ, (Fin t → α) → Set α)
    (n : ℕ) (ps : List I) (hlen : ps.length = n)
    (hp : ∀ t (ht : t < ps.length) (h : Fin t → α),
      (ps[t] : ℝ) ≤ ((step t h).toOuterMeasure (E t h)).toReal) :
    StochasticallyDominates ((seqProcess step n).map (seqCount E n))
      (poissonBinomial ps) := by
  subst hlen
  rw [stochasticallyDominates_nat_iff_Ici]
  intro r
  rw [← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top (poissonBinomial ps) (Set.Ici r)),
    ← ENNReal.ofReal_toReal
      (PMF.toOuterMeasure_ne_top ((seqProcess step ps.length).map (seqCount E ps.length))
        (Set.Ici r))]
  refine ENNReal.ofReal_le_ofReal ?_
  let f : ℕ → ℝ := (Set.Ici r).indicator (fun _ => 1)
  have hf_mono : Monotone f := Cslib.Probability.monotone_indicator_Ici r
  have hC : ∀ j, |f j| ≤ 1 := Cslib.Probability.abs_indicator_Ici_le_one r
  have hchain (k : ℕ) (hk : k ≤ ps.length) :
      Cslib.Probability.pbValue ps f 0 0 ≤
        ∑' h : Fin k → α,
          ((seqProcess step k) h).toReal * Cslib.Probability.pbValue ps f k (seqCount E k h) := by
    induction k with
    | zero =>
      have hsub : Subsingleton (Fin 0 → α) := ⟨fun a b => funext fun i => Fin.elim0 i⟩
      rw [tsum_eq_single (Fin.elim0 : Fin 0 → α) fun g hg => absurd (Subsingleton.elim g _) hg]
      simp [seqProcess, Cslib.Probability.pbValue]
    | succ k ih =>
      refine (ih (Nat.le_of_succ_le hk)).trans ?_
      rw [tsum_toReal_seqProcess_step step k _ fun h =>
        Cslib.Probability.pbValue_abs_le hC (k + 1) _]
      refine Summable.tsum_le_tsum ?_
        (seqProcess_tsum_toReal _ _ fun h => Cslib.Probability.pbValue_abs_le (ps := ps) hC k _)
        (seqProcess_tsum_toReal (C := 1) _ _ fun h => ?_)
      · intro h
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        let D : ℝ :=
          Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h + 1) -
            Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h)
        have hD_nn : 0 ≤ D := by
          refine sub_nonneg.mpr ?_
          exact Cslib.Probability.pbValue_mono hf_mono (k + 1) (Nat.le_succ _)
        have hstep :
            Cslib.Probability.pbValue ps f k (seqCount E k h) =
              Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h) + (ps[k] : ℝ) * D :=
          Cslib.Probability.pbValue_step ps f hk (seqCount E k h)
        have hinner :
            ∑' a : α, ((step k h) a).toReal *
                Cslib.Probability.pbValue ps f (k + 1) (seqCount E (k + 1) (Fin.snoc h a)) =
              Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h) +
                ((step k h).toOuterMeasure (E k h)).toReal * D := by
          classical
          have heq (a : α) :
              ((step k h) a).toReal *
                  Cslib.Probability.pbValue ps f (k + 1) (seqCount E (k + 1) (Fin.snoc h a)) =
                ((step k h) a).toReal * Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h) +
                  ((E k h).indicator (fun a => ((step k h) a).toReal) a) * D := by
            rw [seqCount_snoc]
            by_cases ha : a ∈ E k h
            · simp [D, ha]
              ring
            · simp [D, ha]
          simp_rw [heq]
          have hs1 : Summable fun a : α =>
              ((step k h) a).toReal * Cslib.Probability.pbValue ps f (k + 1) (seqCount E k h) :=
            (PMF.summable_toReal _).mul_right _
          have hs2 : Summable fun a : α =>
              ((E k h).indicator (fun a => ((step k h) a).toReal) a) * D := by
            refine Summable.of_norm_bounded ((PMF.summable_toReal (step k h)).mul_right |D|)
              fun a => ?_
            rw [Real.norm_eq_abs, abs_mul]
            by_cases ha : a ∈ E k h
            · simp [ha, abs_of_nonneg ENNReal.toReal_nonneg]
            · simp only [ha, not_false_eq_true, Set.indicator_of_notMem, abs_zero, zero_mul]
              exact mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
          rw [hs1.tsum_add hs2, tsum_mul_right, PMF.tsum_toReal, one_mul, tsum_mul_right]
          have hprob :
              ∑' a : α, (E k h).indicator (fun a => ((step k h) a).toReal) a =
                ((step k h).toOuterMeasure (E k h)).toReal := by
            rw [PMF.toOuterMeasure_apply]
            conv_rhs =>
              rw [ENNReal.tsum_toReal_eq (f := (E k h).indicator (step k h)) fun a => by
                by_cases ha : a ∈ E k h
                · simp [ha, PMF.apply_ne_top]
                · simp [ha]]
            refine tsum_congr fun a => ?_
            by_cases ha : a ∈ E k h <;> simp [ha]
          rw [hprob]
        rw [hstep, hinner]
        exact add_le_add_right (mul_le_mul_of_nonneg_right (hp k hk h) hD_nn) _
      · exact abs_tsum_pmf_mul_le_one (step k h) _ fun a =>
          Cslib.Probability.pbValue_abs_le (ps := ps) hC (k + 1) _
  have hmain := hchain ps.length le_rfl
  have hlhs :
      Cslib.Probability.pbValue ps f 0 0 =
        ((poissonBinomial ps).toOuterMeasure (Set.Ici r)).toReal := by
    rw [Cslib.Probability.pbValue_zero_Ici_eq_real ps r, measureReal_def,
      PMF.toMeasure_apply_eq_toOuterMeasure_apply _ measurableSet_Ici]
  have hrhs :
      (∑' h : Fin ps.length → α,
          ((seqProcess step ps.length) h).toReal *
            Cslib.Probability.pbValue ps f ps.length (seqCount E ps.length h)) =
        (((seqProcess step ps.length).map (seqCount E ps.length)).toOuterMeasure
          (Set.Ici r)).toReal := by
    have hpb (h : Fin ps.length → α) :
        Cslib.Probability.pbValue ps f ps.length (seqCount E ps.length h) =
          if r ≤ seqCount E ps.length h then 1 else 0 := by
      simp only [Cslib.Probability.pbValue, List.drop_length, List.length_nil, zero_add,
        Finset.range_one, Finset.sum_singleton, poissonBinomial_nil, PMF.pure_apply, ↓reduceIte,
        ENNReal.toReal_one, one_mul, add_zero]
      by_cases hh : r ≤ seqCount E ps.length h <;> simp [f, hh]
    simp_rw [hpb]
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
    conv_rhs =>
      rw [ENNReal.tsum_toReal_eq fun h => by
        by_cases hh : seqCount E ps.length h ∈ Set.Ici r
        · simp [hh, PMF.apply_ne_top]
        · simp [hh]]
    refine tsum_congr fun h => ?_
    by_cases hh : r ≤ seqCount E ps.length h
    · simp [hh]
    · simp [hh]
  rw [← hlhs, ← hrhs]
  exact hmain

/-- **Sequential finite-horizon Poisson-binomial domination**: if at every step `t < ps.length` and
every prefix `h`, the conditional event probability `((step t h).toOuterMeasure (E t h)).toReal` is
at least `ps[t]`, then `seqCount E ps.length` under `seqProcess step ps.length` stochastically
dominates `poissonBinomial ps`. -/
theorem seqCount_stochasticallyDominates_poissonBinomial {α : Type*}
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (E : ∀ t : ℕ, (Fin t → α) → Set α) (ps : List I)
    (hp : ∀ t (ht : t < ps.length) (h : Fin t → α),
      (ps[t] : ℝ) ≤ ((step t h).toOuterMeasure (E t h)).toReal) :
    StochasticallyDominates ((seqProcess step ps.length).map (seqCount E ps.length))
      (poissonBinomial ps) :=
  seqCount_stochasticallyDominates_poissonBinomial_of_length step E ps.length ps rfl hp

/-- **Active-before-target sequential `PMF` bound**: if `((step t h).toOuterMeasure (E t h)).toReal`
is at least `p` whenever `t < n` and `seqCount E t h < r`, then the probability of strictly fewer
than `r` successes after `n` steps is at most
`(ProbabilityTheory.binomial n p).real (Set.Iio r)`. -/
theorem seqCount_active_toReal_Iio_le {α : Type*}
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (E : ∀ t : ℕ, (Fin t → α) → Set α)
    (n r : ℕ) (p : I)
    (hp : ∀ t, t < n → ∀ h : Fin t → α,
      seqCount E t h < r → (p : ℝ) ≤ ((step t h).toOuterMeasure (E t h)).toReal) :
    (((seqProcess step n).map (seqCount E n)).toOuterMeasure (Set.Iio r)).toReal ≤
      (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
  let E' : ∀ t : ℕ, (Fin t → α) → Set α :=
    fun t h => if r ≤ seqCount E t h then Set.univ else E t h
  let ps := List.replicate n p
  have hp' : ∀ t (ht : t < ps.length) (h : Fin t → α),
      (ps[t] : ℝ) ≤ ((step t h).toOuterMeasure (E' t h)).toReal := by
    intro t ht h
    have ht' : t < n := by simpa [ps] using ht
    by_cases hreach : r ≤ seqCount E t h
    · have huniv : (step t h).toOuterMeasure Set.univ = 1 := by
        let _ : MeasurableSpace α := ⊤
        rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply (step t h) MeasurableSet.univ,
          measure_univ]
      simpa [ps, E', hreach, huniv] using p.2.2
    · simpa [ps, E', hreach] using hp t ht' h (not_le.mp hreach)
  have hdom := seqCount_stochasticallyDominates_poissonBinomial_of_length step E' n ps
    (List.length_replicate) hp'
  have hIio := ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top (poissonBinomial ps) (Set.Iio r))
    (hdom.le_Iio r)
  have hL :
      ((seqProcess step n).map (seqCount E n)).toOuterMeasure (Set.Iio r) =
        ((seqProcess step n).map (seqCount E' n)).toOuterMeasure (Set.Iio r) := by
    simp only [PMF.toOuterMeasure_map_apply]
    congr 1
    ext h
    have hmono (k : ℕ) (hk : k ≤ n) (h₀ : Fin k → α) :
        min (seqCount E k h₀) r = min (seqCount E' k h₀) r := by
      induction k with
      | zero => simp
      | succ k ih =>
        obtain ⟨hprev, a, rfl⟩ : ∃ hprev a, h₀ = Fin.snoc hprev a :=
          ⟨Fin.init h₀, h₀ (Fin.last k), (Fin.snoc_init_self h₀).symm⟩
        rw [seqCount_snoc, seqCount_snoc]
        by_cases hk_lt : seqCount E k hprev < r
        · have hk_eq : seqCount E k hprev = seqCount E' k hprev := by
            have hm := ih (Nat.le_of_succ_le hk) hprev
            have hlt' : seqCount E' k hprev < r := by
              by_contra hge
              have := min_eq_right (not_lt.mp hge)
              rw [← this, ← hm, min_eq_left hk_lt.le] at *
              omega
            rw [min_eq_left hk_lt.le, min_eq_left hlt'.le] at hm
            exact hm
          have hE' : E' k hprev = E k hprev := by simp [E', not_le.mpr hk_lt]
          rw [hk_eq, hE']
        · have hge : r ≤ seqCount E k hprev := not_lt.mp hk_lt
          have hk'_ge : r ≤ seqCount E' k hprev := by
            have hm := ih (Nat.le_of_succ_le hk) hprev
            rw [min_eq_right hge] at hm
            exact le_trans (le_of_eq hm) (min_le_left _ _)
          rw [min_eq_right (hge.trans (Nat.le_add_right _ _)),
            min_eq_right (hk'_ge.trans (Nat.le_add_right _ _))]
    have hm := hmono n le_rfl h
    rw [Set.mem_preimage, Set.mem_preimage, Set.mem_Iio, Set.mem_Iio]
    have hiff (x : ℕ) : x < r ↔ min x r < r :=
      (min_lt_iff.trans (or_iff_left (lt_irrefl r))).symm
    rw [hiff (seqCount E n h), hm, ← hiff (seqCount E' n h)]
  have hR :
      ((poissonBinomial ps).toOuterMeasure (Set.Iio r)).toReal =
        (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
    rw [← PMF.toMeasure_poissonBinomial_replicate n p, measureReal_def,
      PMF.toMeasure_apply_eq_toOuterMeasure_apply _ measurableSet_Iio]
  rw [← hL, hR] at hIio
  exact hIio

end Cslib.Probability.PMF
