/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.CDF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToMeasure
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# First-order stochastic domination

First-order stochastic domination on preordered measurable spaces and on probability mass
functions, with characterizations via upper sets, intervals, `ProbabilityTheory.cdf`, monotone
Lebesgue integrals, and monotone Bochner integrals, plus pushforward, monadic bind, addition,
and coupling closure properties.

## Main definitions

* `Cslib.Probability.StochasticallyDominates`: first-order stochastic order on `Measure α`,
  requiring `ν U ≤ μ U` for every measurable upper set `U`.
* `Cslib.Probability.PMF.StochasticallyDominates`: first-order stochastic order on `PMF α`,
  requiring `q.toOuterMeasure U ≤ p.toOuterMeasure U` for every upper set `U`.

## Main results

* `Cslib.Probability.StochasticallyDominates.lintegral_le`,
  `Cslib.Probability.stochasticallyDominates_iff_lintegral`: characterization by monotone
  Lebesgue integrals.
* `Cslib.Probability.StochasticallyDominates.integral_le`,
  `Cslib.Probability.stochasticallyDominates_iff_integral`: characterization by integrable
  monotone real functions on probability measures.
* `Cslib.Probability.stochasticallyDominates_nat_iff_Ici`,
  `Cslib.Probability.stochasticallyDominates_nat_iff_Iio`,
  `Cslib.Probability.stochasticallyDominates_real_iff_cdf`: specializations to `ℕ` and `ℝ`.
* `Cslib.Probability.StochasticallyDominates.map`,
  `Cslib.Probability.StochasticallyDominates.bind`,
  `Cslib.Probability.StochasticallyDominates.add_prod`,
  `Cslib.Probability.StochasticallyDominates.of_ae_le`: functorial, monadic, additive, and
  coupling closure.
-/

public section

namespace Cslib.Probability

open MeasureTheory
open scoped BigOperators ENNReal

section MeasureOrder

/-- First-order stochastic domination on `Measure α`: `μ` stochastically dominates `ν` when every
measurable upper set has at least as much `μ`-measure as `ν`-measure. -/
@[expose]
def StochasticallyDominates {α : Type*} [MeasurableSpace α] [Preorder α]
    (μ ν : Measure α) : Prop :=
  ∀ U : Set α, MeasurableSet U → IsUpperSet U → ν U ≤ μ U

private theorem lintegral_eq_lintegral_ennreal_lt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} := by
  let S : Set (α × ℝ) := {p | 0 < p.2 ∧ ENNReal.ofReal p.2 < f p.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hf.comp measurable_fst))
  have hpoint (x : α) :
      f x = ∫⁻ t : ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (x, t) ∂volume := by
    let Tx : Set ℝ := {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f x}
    have hTxm : MeasurableSet Tx :=
      (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
    have hslice : (fun t : ℝ => S.indicator (fun _ => (1 : ℝ≥0∞)) (x, t)) =
        Tx.indicator (1 : ℝ → ℝ≥0∞) := by
      ext t
      by_cases ht : 0 < t ∧ ENNReal.ofReal t < f x
      · simp [S, Tx, ht]
      · simp [S, Tx, ht]
    rw [hslice, lintegral_indicator hTxm]
    simp only [Pi.one_apply, lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, one_mul]
    by_cases htop : f x = ⊤
    · have hset : Tx = Set.Ioi 0 := by
        ext t
        simp [Tx, htop]
      rw [hset, Real.volume_Ioi, htop]
    · have hset : Tx = Set.Ioo 0 (f x).toReal := by
        ext t
        simp only [Tx, Set.mem_ofPred_eq, Set.mem_Ioo, and_congr_right_iff]
        intro ht0
        rw [ENNReal.ofReal_lt_iff_lt_toReal ht0.le htop]
      rw [hset, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal htop]
  calc
    ∫⁻ x, f x ∂μ
      = ∫⁻ x, ∫⁻ t : ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (x, t) ∂volume ∂μ := by
          simp_rw [← hpoint]
    _ = ∫⁻ t : ℝ, ∫⁻ x, S.indicator (fun _ => (1 : ℝ≥0∞)) (x, t) ∂μ ∂volume :=
          lintegral_lintegral_swap (measurable_const.indicator hS).aemeasurable
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} := by
          rw [← lintegral_indicator measurableSet_Ioi]
          congr 1
          ext t
          by_cases ht : 0 < t
          · have hslice : (fun x => S.indicator (fun _ => (1 : ℝ≥0∞)) (x, t)) =
                {x | ENNReal.ofReal t < f x}.indicator (1 : α → ℝ≥0∞) := by
              ext x
              by_cases hx : ENNReal.ofReal t < f x <;> simp [S, ht, hx]
            rw [Set.indicator_of_mem ht, hslice,
              lintegral_indicator (measurableSet_lt measurable_const hf)]
            simp
          · have hzero : (fun x => S.indicator (fun _ => (1 : ℝ≥0∞)) (x, t)) = 0 := by
              ext x
              simp [S, ht]
            rw [Set.indicator_of_notMem ht, hzero]
            change ∫⁻ _ : α, (0 : ℝ≥0∞) ∂μ = 0
            simp

namespace StochasticallyDominates

section Preorder

variable {α : Type*} [MeasurableSpace α] [Preorder α] {μ ν ρ : Measure α}

/-- Unfold stochastic domination on a measurable upper set. -/
theorem measure_le (h : StochasticallyDominates μ ν) {U : Set α}
    (hUm : MeasurableSet U) (hU : IsUpperSet U) : ν U ≤ μ U :=
  h U hUm hU

/-- Reflexivity of stochastic domination. -/
@[refl]
theorem refl (μ : Measure α) : StochasticallyDominates μ μ :=
  fun _ _ _ => le_rfl

/-- Transitivity of stochastic domination. -/
theorem trans (h₁ : StochasticallyDominates μ ν) (h₂ : StochasticallyDominates ν ρ) :
    StochasticallyDominates μ ρ :=
  fun U hUm hU => (h₂ U hUm hU).trans (h₁ U hUm hU)

instance : Trans (StochasticallyDominates (α := α)) (StochasticallyDominates (α := α))
    (StochasticallyDominates (α := α)) where
  trans h₁ h₂ := h₁.trans h₂

/-- Closed upper rays `Set.Ici a` have larger measure under a dominating measure. -/
theorem Ici_le [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
    (h : StochasticallyDominates μ ν) (a : α) :
    ν (Set.Ici a) ≤ μ (Set.Ici a) :=
  h _ measurableSet_Ici (IsUpperSet.Ici a)

/-- Open upper rays `Set.Ioi a` have larger measure under a dominating measure. -/
theorem Ioi_le {α : Type*} [MeasurableSpace α] [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [OpensMeasurableSpace α] {μ ν : Measure α}
    (h : StochasticallyDominates μ ν) (a : α) :
    ν (Set.Ioi a) ≤ μ (Set.Ioi a) :=
  h _ measurableSet_Ioi (IsUpperSet.Ioi a)

/-- Finite-measure `.real` inequality on any measurable upper set. -/
theorem real_le [IsFiniteMeasure μ] (h : StochasticallyDominates μ ν) {U : Set α}
    (hUm : MeasurableSet U) (hU : IsUpperSet U) :
    ν.real U ≤ μ.real U :=
  ENNReal.toReal_mono (measure_ne_top μ U) (h U hUm hU)

/-- Finite-measure `.real` inequality on `Set.Ici a`. -/
theorem real_Ici_le [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
    [IsFiniteMeasure μ] (h : StochasticallyDominates μ ν) (a : α) :
    ν.real (Set.Ici a) ≤ μ.real (Set.Ici a) :=
  h.real_le measurableSet_Ici (IsUpperSet.Ici a)

/-- Finite-measure `.real` inequality on `Set.Ioi a`. -/
theorem real_Ioi_le {α : Type*} [MeasurableSpace α] [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [OpensMeasurableSpace α] {μ ν : Measure α}
    [IsFiniteMeasure μ] (h : StochasticallyDominates μ ν) (a : α) :
    ν.real (Set.Ioi a) ≤ μ.real (Set.Ioi a) :=
  h.real_le measurableSet_Ioi (IsUpperSet.Ioi a)

private theorem measure_Iic_eq_one_sub_Ioi {α : Type*} [MeasurableSpace α] [LinearOrder α]
    [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (a : α) :
    μ (Set.Iic a) = 1 - μ (Set.Ioi a) := by
  rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi]

private theorem measure_Ioi_eq_one_sub_Iic {α : Type*} [MeasurableSpace α] [LinearOrder α]
    [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (a : α) :
    μ (Set.Ioi a) = 1 - μ (Set.Iic a) := by
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]

private theorem forall_Ioi_le_iff_Iic_le {α : Type*} [MeasurableSpace α] [LinearOrder α]
    [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ x : α, ν (Set.Ioi x) ≤ μ (Set.Ioi x)) ↔ ∀ x : α, μ (Set.Iic x) ≤ ν (Set.Iic x) := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rw [measure_Iic_eq_one_sub_Ioi μ x, measure_Iic_eq_one_sub_Ioi ν x]
    exact tsub_le_tsub_left (h x) 1
  · rw [measure_Ioi_eq_one_sub_Iic μ x, measure_Ioi_eq_one_sub_Iic ν x]
    exact tsub_le_tsub_left (h x) 1

/-- A dominating probability measure assigns no more mass to `Set.Iic a` than the dominated
probability measure. -/
theorem le_Iic {α : Type*} [MeasurableSpace α] [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [OpensMeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : StochasticallyDominates μ ν)
    (a : α) :
    μ (Set.Iic a) ≤ ν (Set.Iic a) := by
  rw [measure_Iic_eq_one_sub_Ioi μ a, measure_Iic_eq_one_sub_Ioi ν a]
  exact tsub_le_tsub_left (h.Ioi_le a) 1

/-- Real-valued version of `StochasticallyDominates.le_Iic`. -/
theorem le_real_Iic {α : Type*} [MeasurableSpace α] [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [OpensMeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : StochasticallyDominates μ ν)
    (a : α) :
    μ.real (Set.Iic a) ≤ ν.real (Set.Iic a) :=
  ENNReal.toReal_mono (measure_ne_top ν (Set.Iic a)) (h.le_Iic a)

private theorem measure_compl_le_of_le {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {s : Set α} (hs : MeasurableSet s)
    (h : ν s ≤ μ s) : μ sᶜ ≤ ν sᶜ := by
  rw [prob_compl_eq_one_sub hs, prob_compl_eq_one_sub hs]
  exact tsub_le_tsub_left h 1

/-- A dominating probability measure assigns no more mass to `Set.Iio a` than the dominated
probability measure. -/
theorem le_Iio {α : Type*} [MeasurableSpace α] [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [OpensMeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : StochasticallyDominates μ ν)
    (a : α) :
    μ (Set.Iio a) ≤ ν (Set.Iio a) := by
  rw [← Set.compl_Ici]
  exact measure_compl_le_of_le measurableSet_Ici (h.Ici_le a)

/-- Real-valued version of `StochasticallyDominates.le_Iio`. -/
theorem le_real_Iio {α : Type*} [MeasurableSpace α] [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [OpensMeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : StochasticallyDominates μ ν)
    (a : α) :
    μ.real (Set.Iio a) ≤ ν.real (Set.Iio a) :=
  ENNReal.toReal_mono (measure_ne_top ν (Set.Iio a)) (h.le_Iio a)

/-- First-order stochastic domination implies `∫⁻ x, f x ∂ν ≤ ∫⁻ x, f x ∂μ` for every
measurable monotone function `f : α → ℝ≥0∞`. -/
theorem lintegral_le [SFinite μ] [SFinite ν] (h : StochasticallyDominates μ ν)
    {f : α → ℝ≥0∞} (hf : Measurable f) (hf_mono : Monotone f) :
    ∫⁻ x, f x ∂ν ≤ ∫⁻ x, f x ∂μ := by
  rw [lintegral_eq_lintegral_ennreal_lt ν hf, lintegral_eq_lintegral_ennreal_lt μ hf]
  refine lintegral_mono fun t => ?_
  refine h _ (measurableSet_lt measurable_const hf) ?_
  intro x y hxy hx
  exact lt_of_lt_of_le hx (hf_mono hxy)

/-- Reverse inequality for measurable antitone functions `g : α → ℝ≥0∞` when `μ` and `ν` have
equal finite total mass (for instance, probability measures). -/
theorem lintegral_le_of_antitone [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : StochasticallyDominates μ ν) (huniv : μ Set.univ = ν Set.univ)
    {g : α → ℝ≥0∞} (hg : Measurable g) (hg_anti : Antitone g) :
    ∫⁻ x, g x ∂μ ≤ ∫⁻ x, g x ∂ν := by
  rw [lintegral_eq_lintegral_ennreal_lt μ hg, lintegral_eq_lintegral_ennreal_lt ν hg]
  refine lintegral_mono fun t => ?_
  let L : Set α := {x | ENNReal.ofReal t < g x}
  have hLm : MeasurableSet L := measurableSet_lt measurable_const hg
  have hU : IsUpperSet Lᶜ := by
    intro x y hxy hx hy
    exact hx (lt_of_lt_of_le hy (hg_anti hxy))
  have hcompl : ν Lᶜ ≤ μ Lᶜ := h Lᶜ hLm.compl hU
  have hsum : μ L + μ Lᶜ = ν L + ν Lᶜ := by
    rw [measure_add_measure_compl hLm, measure_add_measure_compl hLm, huniv]
  have hle : μ L + ν Lᶜ ≤ ν L + ν Lᶜ := by
    calc
      μ L + ν Lᶜ ≤ μ L + μ Lᶜ := by gcongr
      _ = ν L + ν Lᶜ := hsum
  exact (ENNReal.add_le_add_iff_right (measure_ne_top ν Lᶜ)).mp hle

private theorem lintegral_ofReal_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ :=
  ((lintegral_ofReal_le_lintegral_enorm f).trans_lt hf.2).ne

/-- First-order stochastic domination on probability measures implies `∫ x, f x ∂ν ≤ ∫ x, f x ∂μ`
for every integrable measurable monotone function `f : α → ℝ`. -/
theorem integral_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : StochasticallyDominates μ ν) {f : α → ℝ} (hf : Measurable f) (hf_mono : Monotone f)
    (hfiμ : Integrable f μ) (hfiν : Integrable f ν) :
    ∫ x, f x ∂ν ≤ ∫ x, f x ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfiν,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfiμ]
  have hpos_mono : Monotone (fun x => ENNReal.ofReal (f x)) :=
    fun _ _ hxy => ENNReal.ofReal_le_ofReal (hf_mono hxy)
  have hneg_anti : Antitone (fun x => ENNReal.ofReal (-f x)) :=
    fun _ _ hxy => ENNReal.ofReal_le_ofReal (neg_le_neg (hf_mono hxy))
  have hpos : ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
    h.lintegral_le (ENNReal.measurable_ofReal.comp hf) hpos_mono
  have hneg : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (-f x) ∂ν :=
    h.lintegral_le_of_antitone (by simp) (ENNReal.measurable_ofReal.comp hf.neg) hneg_anti
  exact sub_le_sub
    (ENNReal.toReal_mono (lintegral_ofReal_ne_top hfiμ) hpos)
    (ENNReal.toReal_mono (lintegral_ofReal_ne_top hfiν.neg) hneg)

/-- Nonnegative measurable monotone functions satisfy `∫ x, f x ∂ν ≤ ∫ x, f x ∂μ` under
`SFinite` measures without requiring `μ univ = ν univ`. -/
theorem integral_le_of_nonneg [SFinite μ] [SFinite ν] (h : StochasticallyDominates μ ν)
    {f : α → ℝ} (hf : Measurable f) (hf_mono : Monotone f) (hf0 : ∀ x, 0 ≤ f x)
    (hfiμ : Integrable f μ) (hfiν : Integrable f ν) :
    ∫ x, f x ∂ν ≤ ∫ x, f x ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfiν,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfiμ]
  have hneg_zero (x : α) : ENNReal.ofReal (-f x) = 0 :=
    ENNReal.ofReal_of_nonpos (neg_nonpos.mpr (hf0 x))
  simp only [hneg_zero, lintegral_zero, ENNReal.toReal_zero, sub_zero]
  exact ENNReal.toReal_mono (lintegral_ofReal_ne_top hfiμ)
    (h.lintegral_le (ENNReal.measurable_ofReal.comp hf)
      (fun _ _ hxy => ENNReal.ofReal_le_ofReal (hf_mono hxy)))

/-- Pointwise a.e. ordering `Y ≤ᵐ[π] X` induces stochastic domination of pushforward laws. -/
theorem of_ae_le {γ : Type*} [MeasurableSpace γ] {π : Measure γ} {X Y : γ → α}
    (hX : Measurable X) (hY : Measurable Y) (hle : ∀ᵐ ω ∂π, Y ω ≤ X ω) :
    StochasticallyDominates (π.map X) (π.map Y) := by
  intro U hUm hU
  rw [Measure.map_apply hY hUm, Measure.map_apply hX hUm]
  refine measure_mono_ae ?_
  filter_upwards [hle] with ω hω hmem
  exact hU hω hmem

/-- A monotone coupling `π` on `α × α` (`p.2 ≤ p.1` a.e.) induces stochastic domination of the
first marginal over the second marginal. -/
theorem of_coupling {π : Measure (α × α)} (hle : ∀ᵐ p ∂π, p.2 ≤ p.1) :
    StochasticallyDominates (π.map Prod.fst) (π.map Prod.snd) :=
  of_ae_le measurable_fst measurable_snd hle

/-- Monotone pushforward preserves stochastic domination. -/
theorem map {β : Type*} [MeasurableSpace β] [Preorder β] (h : StochasticallyDominates μ ν)
    {f : α → β} (hf : Measurable f) (hf_mono : Monotone f) :
    StochasticallyDominates (μ.map f) (ν.map f) := by
  intro U hUm hU
  rw [Measure.map_apply hf hUm, Measure.map_apply hf hUm]
  exact h (f ⁻¹' U) (hf hUm) (fun _ _ hxy hx => hU (hf_mono hxy) hx)

/-- Pushing forward along `Nat.cast : ℕ → ℝ` preserves stochastic domination. -/
theorem map_natCast {μ ν : Measure ℕ} (h : StochasticallyDominates μ ν) :
    StochasticallyDominates (μ.map (Nat.cast : ℕ → ℝ)) (ν.map Nat.cast) :=
  h.map measurable_from_top Nat.mono_cast

/-- Monadic bind preserves stochastic domination when the dominating kernel is pointwise larger and
monotone in the conditioning state. -/
theorem bind {β : Type*} [MeasurableSpace β] [Preorder β] [SFinite μ] [SFinite ν]
    (hμν : StochasticallyDominates μ ν) {κ η : α → Measure β}
    (hκ : Measurable κ) (hη : Measurable η)
    (hpt : ∀ a, StochasticallyDominates (κ a) (η a))
    (hmono : ∀ ⦃a₁ a₂ : α⦄, a₁ ≤ a₂ → StochasticallyDominates (κ a₂) (κ a₁)) :
    StochasticallyDominates (μ.bind κ) (ν.bind η) := by
  intro U hUm hU
  rw [Measure.bind_apply hUm hη.aemeasurable, Measure.bind_apply hUm hκ.aemeasurable]
  calc
    ∫⁻ a, η a U ∂ν ≤ ∫⁻ a, κ a U ∂ν :=
      lintegral_mono fun a => hpt a U hUm hU
    _ ≤ ∫⁻ a, κ a U ∂μ :=
      hμν.lintegral_le ((Measure.measurable_coe hUm).comp hκ)
        fun _ _ hle => hmono hle U hUm hU

/-- Variant of `StochasticallyDominates.bind` where the dominated kernel `η` is monotone in the
conditioning state. -/
theorem bind_of_snd_monotone {β : Type*} [MeasurableSpace β] [Preorder β] [SFinite μ] [SFinite ν]
    (hμν : StochasticallyDominates μ ν) {κ η : α → Measure β}
    (hκ : Measurable κ) (hη : Measurable η)
    (hpt : ∀ a, StochasticallyDominates (κ a) (η a))
    (hmono : ∀ ⦃a₁ a₂ : α⦄, a₁ ≤ a₂ → StochasticallyDominates (η a₂) (η a₁)) :
    StochasticallyDominates (μ.bind κ) (ν.bind η) := by
  intro U hUm hU
  rw [Measure.bind_apply hUm hη.aemeasurable, Measure.bind_apply hUm hκ.aemeasurable]
  calc
    ∫⁻ a, η a U ∂ν ≤ ∫⁻ a, η a U ∂μ :=
      hμν.lintegral_le ((Measure.measurable_coe hUm).comp hη)
        fun _ _ hle => hmono hle U hUm hU
    _ ≤ ∫⁻ a, κ a U ∂μ :=
      lintegral_mono fun a => hpt a U hUm hU

/-- Independent addition preserves stochastic domination on ordered additive monoids. -/
theorem add_prod {α : Type*} [MeasurableSpace α] [Preorder α] [AddCommMonoid α]
    [AddLeftMono α] [AddRightMono α] [MeasurableAdd₂ α]
    {μ₁ μ₂ ν₁ ν₂ : Measure α} [SFinite μ₁] [SFinite μ₂] [SFinite ν₁] [SFinite ν₂]
    (h₁ : StochasticallyDominates μ₁ ν₁) (h₂ : StochasticallyDominates μ₂ ν₂) :
    StochasticallyDominates ((μ₁.prod μ₂).map fun p => p.1 + p.2)
      ((ν₁.prod ν₂).map fun p => p.1 + p.2) := by
  intro U hUm hU
  have hpre : MeasurableSet {p : α × α | p.1 + p.2 ∈ U} := measurable_add hUm
  rw [Measure.map_apply measurable_add hUm, Measure.map_apply measurable_add hUm]
  change (ν₁.prod ν₂) {p : α × α | p.1 + p.2 ∈ U} ≤ (μ₁.prod μ₂) {p : α × α | p.1 + p.2 ∈ U}
  rw [Measure.prod_apply hpre, Measure.prod_apply hpre]
  have hmeas_sec (m : Measure α) [SFinite m] :
      Measurable fun x => m (Prod.mk x ⁻¹' {p : α × α | p.1 + p.2 ∈ U}) :=
    measurable_measure_prodMk_left hpre
  calc
    ∫⁻ x, ν₂ (Prod.mk x ⁻¹' {p : α × α | p.1 + p.2 ∈ U}) ∂ν₁
      ≤ ∫⁻ x, μ₂ (Prod.mk x ⁻¹' {p : α × α | p.1 + p.2 ∈ U}) ∂ν₁ := by
        refine lintegral_mono fun x => h₂ _ (measurable_prodMk_left hpre) ?_
        intro y₁ y₂ hy hmem
        exact hU (by gcongr : x + y₁ ≤ x + y₂) hmem
    _ ≤ ∫⁻ x, μ₂ (Prod.mk x ⁻¹' {p : α × α | p.1 + p.2 ∈ U}) ∂μ₁ := by
        refine h₁.lintegral_le (hmeas_sec μ₂) ?_
        intro x₁ x₂ hx
        refine measure_mono fun y hmem => ?_
        exact hU (by gcongr : x₁ + y ≤ x₂ + y) hmem

end Preorder

end StochasticallyDominates

section Characterizations

/-- Stochastic domination of `SFinite` measures is equivalent to domination of all measurable
monotone Lebesgue integrals. -/
theorem stochasticallyDominates_iff_lintegral {α : Type*} [MeasurableSpace α] [Preorder α]
    {μ ν : Measure α} [SFinite μ] [SFinite ν] :
    StochasticallyDominates μ ν ↔
      ∀ f : α → ℝ≥0∞, Measurable f → Monotone f → ∫⁻ x, f x ∂ν ≤ ∫⁻ x, f x ∂μ := by
  refine ⟨fun h _ hf hf_mono => h.lintegral_le hf hf_mono, fun h U hUm hU => ?_⟩
  have hind_mono : Monotone (U.indicator (1 : α → ℝ≥0∞)) := by
    intro x y hxy
    by_cases hx : x ∈ U
    · simp [hx, hU hxy hx]
    · simp [hx]
  simpa [lintegral_indicator hUm] using h (U.indicator 1) (measurable_one.indicator hUm) hind_mono

/-- Stochastic domination of probability measures is equivalent to domination of all integrable
measurable monotone real expectations. -/
theorem stochasticallyDominates_iff_integral {α : Type*} [MeasurableSpace α] [Preorder α]
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticallyDominates μ ν ↔
      ∀ f : α → ℝ, Measurable f → Monotone f → Integrable f μ → Integrable f ν →
        ∫ x, f x ∂ν ≤ ∫ x, f x ∂μ := by
  refine ⟨fun h _ hf hf_mono hfiμ hfiν => h.integral_le hf hf_mono hfiμ hfiν, fun h U hUm hU => ?_⟩
  have hind_mono : Monotone (U.indicator (1 : α → ℝ)) := by
    intro x y hxy
    by_cases hx : x ∈ U
    · simp [hx, hU hxy hx]
    · rw [Set.indicator_of_notMem hx]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) y
  have hint (m : Measure α) [IsProbabilityMeasure m] :
      Integrable (U.indicator (1 : α → ℝ)) m :=
    (integrable_const (1 : ℝ)).indicator hUm
  have hreal : ν.real U ≤ μ.real U := by
    simpa [integral_indicator_one hUm] using
      h (U.indicator 1) (measurable_one.indicator hUm) hind_mono (hint μ) (hint ν)
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν U),
    ← ENNReal.ofReal_toReal (measure_ne_top μ U)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Stochastic domination on `ℕ` is equivalent to upper-tail comparison on `Set.Ici n`. -/
theorem stochasticallyDominates_nat_iff_Ici {μ ν : Measure ℕ} :
    StochasticallyDominates μ ν ↔ ∀ n : ℕ, ν (Set.Ici n) ≤ μ (Set.Ici n) := by
  refine ⟨fun h n => h.Ici_le n, fun h U _ hU => ?_⟩
  rcases hU.eq_empty_or_Ici with rfl | ⟨n, rfl⟩
  · simp
  · exact h n

/-- Stochastic domination of probability measures on `ℕ` is equivalent to strict upper-tail
comparison on `Set.Ioi n`. -/
theorem stochasticallyDominates_nat_iff_Ioi {μ ν : Measure ℕ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticallyDominates μ ν ↔ ∀ n : ℕ, ν (Set.Ioi n) ≤ μ (Set.Ioi n) := by
  rw [stochasticallyDominates_nat_iff_Ici]
  have hIoi (n : ℕ) : Set.Ioi n = Set.Ici (n + 1) := by
    ext k
    simp
  have hIci0 : Set.Ici (0 : ℕ) = Set.univ := by
    ext k
    simp
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · rw [hIoi n]
    exact h (n + 1)
  · cases n with
    | zero =>
      simp [hIci0]
    | succ n =>
      rw [← hIoi n]
      exact h n

/-- Stochastic domination of probability measures on `ℕ` is equivalent to lower-tail comparison on
`Set.Iic n`. -/
theorem stochasticallyDominates_nat_iff_Iic {μ ν : Measure ℕ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticallyDominates μ ν ↔ ∀ n : ℕ, μ (Set.Iic n) ≤ ν (Set.Iic n) :=
  stochasticallyDominates_nat_iff_Ioi.trans StochasticallyDominates.forall_Ioi_le_iff_Iic_le

/-- Stochastic domination of probability measures on `ℕ` is equivalent to strict lower-tail
comparison on `Set.Iio n`. -/
theorem stochasticallyDominates_nat_iff_Iio {μ ν : Measure ℕ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticallyDominates μ ν ↔ ∀ n : ℕ, μ (Set.Iio n) ≤ ν (Set.Iio n) := by
  rw [stochasticallyDominates_nat_iff_Ici]
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · rw [← Set.compl_Ici]
    exact StochasticallyDominates.measure_compl_le_of_le measurableSet_Ici (h n)
  · rw [← Set.compl_Iio]
    exact StochasticallyDominates.measure_compl_le_of_le measurableSet_Iio (h n)

/-- Mutual stochastic domination of finite measures on `ℕ` implies equality. -/
theorem StochasticallyDominates.antisymm_nat {μ ν : Measure ℕ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h₁ : StochasticallyDominates μ ν) (h₂ : StochasticallyDominates ν μ) :
    μ = ν := by
  refine Measure.ext_of_singleton fun n => ?_
  have hIci (m : ℕ) : μ (Set.Ici m) = ν (Set.Ici m) :=
    le_antisymm (h₂.Ici_le m) (h₁.Ici_le m)
  have hset : ({n} : Set ℕ) = Set.Ici n \ Set.Ici (n + 1) := by
    ext k
    simp only [Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_Ici, not_le]
    omega
  have hsub : Set.Ici (n + 1) ⊆ Set.Ici n := Set.Ici_subset_Ici.mpr (Nat.le_succ n)
  rw [hset, measure_sdiff hsub measurableSet_Ici.nullMeasurableSet (measure_ne_top μ _),
    measure_sdiff hsub measurableSet_Ici.nullMeasurableSet (measure_ne_top ν _),
    hIci n, hIci (n + 1)]

private theorem isUpperSet_real_eq {U : Set ℝ} (hU : IsUpperSet U) :
    U = ∅ ∨ U = Set.univ ∨ ∃ a : ℝ, U = Set.Ici a ∨ U = Set.Ioi a := by
  by_cases hne : U.Nonempty
  · by_cases huniv : U = Set.univ
    · exact Or.inr (Or.inl huniv)
    · obtain ⟨b, hb⟩ := Set.ne_univ_iff_exists_notMem U |>.mp huniv
      have hbb : BddBelow U := by
        refine ⟨b, fun x hx => ?_⟩
        by_contra hlt
        exact hb (hU (not_le.mp hlt).le hx)
      let a := sInf U
      have hIoi : Set.Ioi a ⊆ U := by
        intro x hx
        obtain ⟨u, hu, hux⟩ := (csInf_lt_iff hbb hne).mp hx
        exact hU hux.le hu
      have hIci : U ⊆ Set.Ici a := fun x hx => csInf_le hbb hx
      by_cases ha : a ∈ U
      · refine Or.inr (Or.inr ⟨a, Or.inl (le_antisymm hIci ?_)⟩)
        intro x hx
        rcases eq_or_lt_of_le hx with rfl | hlt
        · exact ha
        · exact hIoi hlt
      · refine Or.inr (Or.inr ⟨a, Or.inr (le_antisymm ?_ hIoi)⟩)
        intro x hx
        rcases eq_or_lt_of_le (hIci hx) with hEq | hlt
        · exfalso
          exact ha (hEq ▸ hx)
        · exact hlt
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact Or.inl hne

/-- Stochastic domination of probability measures on `ℝ` is equivalent to upper-tail comparison on
`Set.Ici x`. -/
theorem stochasticallyDominates_real_iff_Ici {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticallyDominates μ ν ↔ ∀ x : ℝ, ν (Set.Ici x) ≤ μ (Set.Ici x) := by
  refine ⟨fun h x => h.Ici_le x, fun h U _ hU => ?_⟩
  have hIoi (a : ℝ) : ν (Set.Ioi a) ≤ μ (Set.Ioi a) := by
    have hEq (m : Measure ℝ) :
        m (Set.Ioi a) = ⨆ n : ℕ, m (Set.Ici (a + 1 / ((n : ℝ) + 1))) := by
      have hUeq : Set.Ioi a = ⋃ n : ℕ, Set.Ici (a + 1 / ((n : ℝ) + 1)) := by
        ext y
        simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
        refine ⟨fun hy => ?_, fun ⟨n, hn⟩ => ?_⟩
        · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
          exact ⟨n, by linarith⟩
        · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith
      have hmono : Monotone fun n : ℕ => Set.Ici (a + 1 / ((n : ℝ) + 1)) := by
        intro i j hij
        refine Set.Ici_subset_Ici.mpr ?_
        gcongr
      rw [hUeq, hmono.measure_iUnion]
    rw [hEq ν, hEq μ]
    exact iSup_mono fun n => h _
  rcases isUpperSet_real_eq hU with rfl | rfl | ⟨a, rfl | rfl⟩
  · simp
  · simp
  · exact h a
  · exact hIoi a

/-- Stochastic domination of probability measures on `ℝ` is equivalent to strict upper-tail
comparison on `Set.Ioi x`. -/
theorem stochasticallyDominates_real_iff_Ioi {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticallyDominates μ ν ↔ ∀ x : ℝ, ν (Set.Ioi x) ≤ μ (Set.Ioi x) := by
  refine ⟨fun h x => h.Ioi_le x, fun h => ?_⟩
  rw [stochasticallyDominates_real_iff_Ici]
  intro a
  have hEq (m : Measure ℝ) [IsFiniteMeasure m] :
      m (Set.Ici a) = ⨅ n : ℕ, m (Set.Ioi (a - 1 / ((n : ℝ) + 1))) := by
    have hIeq : Set.Ici a = ⋂ n : ℕ, Set.Ioi (a - 1 / ((n : ℝ) + 1)) := by
      ext y
      simp only [Set.mem_Ici, Set.mem_iInter, Set.mem_Ioi]
      refine ⟨fun hy n => ?_, fun hy => ?_⟩
      · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · refine le_of_forall_pos_lt_add fun ε hε => ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        linarith [hy n]
    have hanti : Antitone fun n : ℕ => Set.Ioi (a - 1 / ((n : ℝ) + 1)) := by
      intro i j hij
      refine Set.Ioi_subset_Ioi ?_
      gcongr
    rw [hIeq, hanti.measure_iInter (fun _ => measurableSet_Ioi.nullMeasurableSet)
      ⟨0, measure_ne_top m _⟩]
  rw [hEq ν, hEq μ]
  exact iInf_mono fun n => h _

/-- Stochastic domination of probability measures on `ℝ` is equivalent to lower-tail comparison on
`Set.Iic x`. -/
theorem stochasticallyDominates_real_iff_Iic {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticallyDominates μ ν ↔ ∀ x : ℝ, μ (Set.Iic x) ≤ ν (Set.Iic x) :=
  stochasticallyDominates_real_iff_Ioi.trans StochasticallyDominates.forall_Ioi_le_iff_Iic_le

/-- Stochastic domination of probability measures on `ℝ` is equivalent to pointwise comparison of
cumulative distribution functions. -/
theorem stochasticallyDominates_real_iff_cdf {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticallyDominates μ ν ↔
      ∀ x : ℝ, ProbabilityTheory.cdf μ x ≤ ProbabilityTheory.cdf ν x := by
  rw [stochasticallyDominates_real_iff_Iic]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
    exact ENNReal.toReal_mono (measure_ne_top ν (Set.Iic x)) (h x)
  · rw [← ProbabilityTheory.ofReal_cdf μ x, ← ProbabilityTheory.ofReal_cdf ν x]
    exact ENNReal.ofReal_le_ofReal (h x)

/-- Mutual stochastic domination of probability measures on `ℝ` implies equality. -/
theorem StochasticallyDominates.antisymm_real {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h₁ : StochasticallyDominates μ ν) (h₂ : StochasticallyDominates ν μ) :
    μ = ν := by
  refine Measure.eq_of_cdf μ ν ?_
  ext x
  exact le_antisymm
    (stochasticallyDominates_real_iff_cdf.mp h₁ x)
    (stochasticallyDominates_real_iff_cdf.mp h₂ x)

end Characterizations

end MeasureOrder

end Cslib.Probability

namespace Cslib.Probability.PMF

open MeasureTheory
open scoped BigOperators ENNReal

/-- First-order stochastic domination on `PMF α`: `p` stochastically dominates `q` when every
upper set `U` satisfies `q.toOuterMeasure U ≤ p.toOuterMeasure U`. -/
@[expose]
def StochasticallyDominates {α : Type*} [Preorder α] (p q : PMF α) : Prop :=
  ∀ U : Set α, IsUpperSet U → q.toOuterMeasure U ≤ p.toOuterMeasure U

private theorem integrable_toMeasure_of_summable {α : Type*} [MeasurableSpace α]
    (p : PMF α) {f : α → ℝ} (hf_meas : Measurable f)
    (hf : Summable fun x => (p x).toReal * |f x|) :
    Integrable f p.toMeasure := by
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, PMF.lintegral_toMeasure p
    (f := fun a => ENNReal.ofReal ‖f a‖) (ENNReal.measurable_ofReal.comp hf_meas.norm)]
  have heq : (fun x => p x * ENNReal.ofReal ‖f x‖) =
      fun x => (Real.toNNReal ((p x).toReal * |f x|) : ℝ≥0∞) := by
    ext x
    conv_lhs => rw [Real.norm_eq_abs, ← ENNReal.ofReal_toReal (PMF.apply_ne_top p x),
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    rfl
  change (∑' x, p x * ENNReal.ofReal ‖f x‖) < ⊤
  rw [heq, ← ENNReal.coe_tsum (Summable.toNNReal hf)]
  exact ENNReal.coe_lt_top

namespace StochasticallyDominates

section Preorder

variable {α : Type*} [Preorder α] {p q r : PMF α}

/-- Unfold `PMF.StochasticallyDominates` on an upper set. -/
theorem toOuterMeasure_le (h : StochasticallyDominates p q) {U : Set α} (hU : IsUpperSet U) :
    q.toOuterMeasure U ≤ p.toOuterMeasure U :=
  h U hU

/-- Reflexivity of stochastic domination on `PMF α`. -/
@[refl]
theorem refl (p : PMF α) : StochasticallyDominates p p :=
  fun _ _ => le_rfl

/-- Transitivity of stochastic domination on `PMF α`. -/
theorem trans (h₁ : StochasticallyDominates p q) (h₂ : StochasticallyDominates q r) :
    StochasticallyDominates p r :=
  fun U hU => (h₂ U hU).trans (h₁ U hU)

instance : Trans (StochasticallyDominates (α := α)) (StochasticallyDominates (α := α))
    (StochasticallyDominates (α := α)) where
  trans h₁ h₂ := h₁.trans h₂

/-- Upper-ray inequality `q.toOuterMeasure (Set.Ici a) ≤ p.toOuterMeasure (Set.Ici a)`. -/
theorem Ici_le (h : StochasticallyDominates p q) (a : α) :
    q.toOuterMeasure (Set.Ici a) ≤ p.toOuterMeasure (Set.Ici a) :=
  h _ (IsUpperSet.Ici a)

/-- Strict upper-ray inequality `q.toOuterMeasure (Set.Ioi a) ≤ p.toOuterMeasure (Set.Ioi a)`. -/
theorem Ioi_le (h : StochasticallyDominates p q) (a : α) :
    q.toOuterMeasure (Set.Ioi a) ≤ p.toOuterMeasure (Set.Ioi a) :=
  h _ (IsUpperSet.Ioi a)

private theorem compl_le_of_le {α : Type*} {p q : PMF α} {U : Set α}
    (hU : q.toOuterMeasure U ≤ p.toOuterMeasure U) :
    p.toOuterMeasure Uᶜ ≤ q.toOuterMeasure Uᶜ := by
  have hcompl (r : PMF α) : r.toOuterMeasure Uᶜ = 1 - r.toOuterMeasure U := by
    rw [← toOuterMeasure_add_compl_ennreal r U,
      ENNReal.add_sub_cancel_left (toOuterMeasure_ne_top r U)]
  rw [hcompl p, hcompl q]
  exact tsub_le_tsub_left hU 1

/-- Lower-ray inequality `p.toOuterMeasure (Set.Iic a) ≤ q.toOuterMeasure (Set.Iic a)` on a
linear order. -/
theorem le_Iic {α : Type*} [LinearOrder α] {p q : PMF α} (h : StochasticallyDominates p q)
    (a : α) :
    p.toOuterMeasure (Set.Iic a) ≤ q.toOuterMeasure (Set.Iic a) := by
  rw [← Set.compl_Ioi]
  exact compl_le_of_le (h.Ioi_le a)

/-- Strict lower-ray inequality `p.toOuterMeasure (Set.Iio a) ≤ q.toOuterMeasure (Set.Iio a)` on
a linear order. -/
theorem le_Iio {α : Type*} [LinearOrder α] {p q : PMF α} (h : StochasticallyDominates p q)
    (a : α) :
    p.toOuterMeasure (Set.Iio a) ≤ q.toOuterMeasure (Set.Iio a) := by
  rw [← Set.compl_Ici]
  exact compl_le_of_le (h.Ici_le a)

/-- Bridge from `PMF.StochasticallyDominates` to `Measure`-level stochastic domination. -/
theorem toMeasure [MeasurableSpace α] (h : StochasticallyDominates p q) :
    Cslib.Probability.StochasticallyDominates p.toMeasure q.toMeasure := by
  intro U hUm hU
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply p hUm,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply q hUm]
  exact h U hU

/-- `ℝ≥0∞`-weighted monotone series inequality for stochastically ordered `PMF`s. -/
theorem tsum_mul_le (h : StochasticallyDominates p q) {f : α → ℝ≥0∞} (hf : Monotone f) :
    ∑' x, q x * f x ≤ ∑' x, p x * f x := by
  let _ : MeasurableSpace α := ⊤
  have hmeas : Cslib.Probability.StochasticallyDominates p.toMeasure q.toMeasure := h.toMeasure
  have hl := hmeas.lintegral_le measurable_from_top hf
  rwa [PMF.lintegral_toMeasure p measurable_from_top,
    PMF.lintegral_toMeasure q measurable_from_top] at hl

/-- Real-valued expectation inequality for stochastically ordered `PMF`s and integrable monotone
functions. -/
theorem tsum_toReal_mul_le (h : StochasticallyDominates p q) {f : α → ℝ} (hf : Monotone f)
    (hp : Summable fun x => (p x).toReal * |f x|)
    (hq : Summable fun x => (q x).toReal * |f x|) :
    ∑' x, (q x).toReal * f x ≤ ∑' x, (p x).toReal * f x := by
  let _ : MeasurableSpace α := ⊤
  have hmeas : Cslib.Probability.StochasticallyDominates p.toMeasure q.toMeasure := h.toMeasure
  have hintp : Integrable f p.toMeasure := integrable_toMeasure_of_summable p measurable_from_top hp
  have hintq : Integrable f q.toMeasure := integrable_toMeasure_of_summable q measurable_from_top hq
  have hinteg := hmeas.integral_le measurable_from_top hf hintp hintq
  simpa [PMF.integral_eq_tsum _ _ hintp, PMF.integral_eq_tsum _ _ hintq, smul_eq_mul] using hinteg

/-- Real-valued expectation inequality for bounded monotone functions under stochastically ordered
`PMF`s. -/
theorem tsum_toReal_mul_le_of_bdd (h : StochasticallyDominates p q) {f : α → ℝ} (hf : Monotone f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∑' x, (q x).toReal * f x ≤ ∑' x, (p x).toReal * f x := by
  refine h.tsum_toReal_mul_le hf ?_ ?_
  · refine Summable.of_nonneg_of_le (fun x => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
      (fun x => mul_le_mul_of_nonneg_left (hC x) ENNReal.toReal_nonneg) ?_
    exact (PMF.summable_toReal p).mul_right C
  · refine Summable.of_nonneg_of_le (fun x => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
      (fun x => mul_le_mul_of_nonneg_left (hC x) ENNReal.toReal_nonneg) ?_
    exact (PMF.summable_toReal q).mul_right C

/-- Finite-sum expectation inequality for monotone functions on `[Fintype α]`. -/
theorem sum_toReal_mul_le [Fintype α] (h : StochasticallyDominates p q) {f : α → ℝ}
    (hf : Monotone f) :
    ∑ x, (q x).toReal * f x ≤ ∑ x, (p x).toReal * f x := by
  simpa [tsum_fintype] using
    h.tsum_toReal_mul_le hf (Summable.of_finite) (Summable.of_finite)

/-- Monotone map preserves `PMF.StochasticallyDominates`. -/
theorem map {β : Type*} [Preorder β] (h : StochasticallyDominates p q) {f : α → β}
    (hf : Monotone f) :
    StochasticallyDominates (p.map f) (q.map f) := by
  intro U hU
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact h (f ⁻¹' U) (fun _ _ hxy hx => hU (hf hxy) hx)

/-- Monadic bind preserves `PMF.StochasticallyDominates` when the dominating kernel is pointwise
larger and monotone in its parameter. -/
theorem bind {β : Type*} [Preorder β] (hpq : StochasticallyDominates p q) {κ η : α → PMF β}
    (hpt : ∀ a, StochasticallyDominates (κ a) (η a))
    (hmono : ∀ ⦃a₁ a₂ : α⦄, a₁ ≤ a₂ → StochasticallyDominates (κ a₂) (κ a₁)) :
    StochasticallyDominates (p.bind κ) (q.bind η) := by
  intro U hU
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  calc
    ∑' a, q a * (η a).toOuterMeasure U ≤ ∑' a, q a * (κ a).toOuterMeasure U :=
      tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (hpt a U hU) (zero_le : 0 ≤ q a)
    _ ≤ ∑' a, p a * (κ a).toOuterMeasure U :=
      hpq.tsum_mul_le fun _ _ hle => hmono hle U hU

/-- Variant of `PMF.StochasticallyDominates.bind` where the dominated kernel `η` is monotone. -/
theorem bind_of_snd_monotone {β : Type*} [Preorder β] (hpq : StochasticallyDominates p q)
    {κ η : α → PMF β} (hpt : ∀ a, StochasticallyDominates (κ a) (η a))
    (hmono : ∀ ⦃a₁ a₂ : α⦄, a₁ ≤ a₂ → StochasticallyDominates (η a₂) (η a₁)) :
    StochasticallyDominates (p.bind κ) (q.bind η) := by
  intro U hU
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  calc
    ∑' a, q a * (η a).toOuterMeasure U ≤ ∑' a, p a * (η a).toOuterMeasure U :=
      hpq.tsum_mul_le fun _ _ hle => hmono hle U hU
    _ ≤ ∑' a, p a * (κ a).toOuterMeasure U :=
      tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (hpt a U hU) (zero_le : 0 ≤ p a)

/-- Addition convolution of `PMF`s preserves stochastic domination. -/
theorem bind_add {α : Type*} [Preorder α] [AddCommMonoid α] [AddLeftMono α] [AddRightMono α]
    {p₁ p₂ q₁ q₂ : PMF α} (h₁ : StochasticallyDominates p₁ q₁)
    (h₂ : StochasticallyDominates p₂ q₂) :
    StochasticallyDominates (p₁.bind fun a => p₂.map (a + ·))
      (q₁.bind fun a => q₂.map (a + ·)) := by
  refine h₁.bind (fun a => h₂.map fun _ _ hy => by gcongr) ?_
  intro a₁ a₂ ha U hU
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  refine OuterMeasure.mono _ fun b hb => ?_
  exact hU (by gcongr : a₁ + b ≤ a₂ + b) hb

end Preorder

end StochasticallyDominates

/-- Equivalence between `PMF.StochasticallyDominates` and `Measure`-level stochastic domination
whenever every upper set is measurable. -/
theorem stochasticallyDominates_iff_toMeasure {α : Type*} [Preorder α] [MeasurableSpace α]
    (hupper : ∀ U : Set α, IsUpperSet U → MeasurableSet U) {p q : PMF α} :
    StochasticallyDominates p q ↔
      Cslib.Probability.StochasticallyDominates p.toMeasure q.toMeasure := by
  refine ⟨StochasticallyDominates.toMeasure, fun h U hU => ?_⟩
  have hUm : MeasurableSet U := hupper U hU
  have hp := PMF.toMeasure_apply_eq_toOuterMeasure_apply p hUm
  have hq := PMF.toMeasure_apply_eq_toOuterMeasure_apply q hUm
  rw [← hp, ← hq]
  exact h U hUm hU

/-- Equivalence between `PMF.StochasticallyDominates` on `ℕ` and `Measure`-level stochastic
domination on `p.toMeasure`. -/
theorem stochasticallyDominates_iff_toMeasure_nat {p q : PMF ℕ} :
    StochasticallyDominates p q ↔
      Cslib.Probability.StochasticallyDominates p.toMeasure q.toMeasure :=
  stochasticallyDominates_iff_toMeasure (fun _ _ => MeasurableSet.of_discrete)

/-- Equivalence between `PMF.StochasticallyDominates` on `ℝ` and `Measure`-level stochastic
domination on `p.toMeasure`. -/
theorem stochasticallyDominates_iff_toMeasure_real {p q : PMF ℝ} :
    StochasticallyDominates p q ↔
      Cslib.Probability.StochasticallyDominates p.toMeasure q.toMeasure :=
  stochasticallyDominates_iff_toMeasure fun _ hU => hU.ordConnected.measurableSet

/-- Characterization of `PMF.StochasticallyDominates` on `ℕ` via `Set.Ici n`. -/
theorem stochasticallyDominates_nat_iff_Ici {p q : PMF ℕ} :
    StochasticallyDominates p q ↔
      ∀ n : ℕ, q.toOuterMeasure (Set.Ici n) ≤ p.toOuterMeasure (Set.Ici n) := by
  rw [stochasticallyDominates_iff_toMeasure_nat,
    Cslib.Probability.stochasticallyDominates_nat_iff_Ici]
  simp [PMF.toMeasure_apply_eq_toOuterMeasure]

/-- Characterization of `PMF.StochasticallyDominates` on `ℕ` via `Set.Iio n`. -/
theorem stochasticallyDominates_nat_iff_Iio {p q : PMF ℕ} :
    StochasticallyDominates p q ↔
      ∀ n : ℕ, p.toOuterMeasure (Set.Iio n) ≤ q.toOuterMeasure (Set.Iio n) := by
  rw [stochasticallyDominates_iff_toMeasure_nat,
    Cslib.Probability.stochasticallyDominates_nat_iff_Iio]
  simp [PMF.toMeasure_apply_eq_toOuterMeasure]

/-- Mutual stochastic domination of `PMF ℕ`s implies equality. -/
theorem StochasticallyDominates.antisymm_nat {p q : PMF ℕ}
    (h₁ : StochasticallyDominates p q) (h₂ : StochasticallyDominates q p) :
    p = q := by
  apply PMF.toMeasure_injective
  exact (stochasticallyDominates_iff_toMeasure_nat.mp h₁).antisymm_nat
    (stochasticallyDominates_iff_toMeasure_nat.mp h₂)

/-- Stochastic domination on `Bool` (with `false < true`) is equivalent to `q true ≤ p true`. -/
theorem stochasticallyDominates_bool_iff {p q : PMF Bool} :
    StochasticallyDominates p q ↔ q true ≤ p true := by
  refine ⟨fun h => ?_, fun h U hU => ?_⟩
  · have hIci : Set.Ici true = ({true} : Set Bool) := by
      ext b
      cases b <;> simp
    simpa [hIci, PMF.toOuterMeasure_apply_singleton] using h (Set.Ici true) (IsUpperSet.Ici true)
  · by_cases ht : true ∈ U
    · by_cases hf : false ∈ U
      · have hUuniv : U = Set.univ :=
          Set.eq_univ_iff_forall.mpr fun b => by cases b <;> assumption
        have hp : p.toOuterMeasure Set.univ = 1 := by
          let _ : MeasurableSpace Bool := ⊤
          rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply p MeasurableSet.univ, measure_univ]
        have hq : q.toOuterMeasure Set.univ = 1 := by
          let _ : MeasurableSpace Bool := ⊤
          rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply q MeasurableSet.univ, measure_univ]
        rw [hUuniv, hp, hq]
      · have hUs : U = {true} := by
          ext b
          cases b <;> simp [ht, hf]
        simpa [hUs, PMF.toOuterMeasure_apply_singleton] using h
    · by_cases hf : false ∈ U
      · exfalso
        exact ht (hU (by decide : false ≤ true) hf)
      · have hUe : U = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr fun b => by cases b <;> assumption
        simp [hUe]

end Cslib.Probability.PMF
