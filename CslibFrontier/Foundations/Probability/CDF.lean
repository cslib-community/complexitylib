/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/CDF.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.CDF

/-!
# Continuity, strict monotonicity and the probability integral transform for a cdf

The cdf `cdf ν` of a probability measure `ν` on `ℝ` is measurable (`measurable_cdf`). It is
continuous when `ν` has no atoms (`continuous_cdf`), and strictly increasing when `ν` charges
every set of positive Lebesgue measure (`strictMono_cdf`). A continuous cdf maps `ν` to the uniform
law on `[0, 1]`, in the sense that `ν {x | cdf ν x ≤ α} = α` for `α ∈ [0, 1]` (the *probability
integral transform*, `measureReal_setOf_cdf_le`): the event is a closed lower set, hence a
half-line `(-∞, t]` with `cdf ν t = α`. This lets one work with quantiles without defining them.

## Main results

* `ProbabilityTheory.measurable_cdf`, `ProbabilityTheory.continuous_cdf`,
  `ProbabilityTheory.strictMono_cdf`: regularity of a cdf.
* `ProbabilityTheory.cdf_pos`, `ProbabilityTheory.cdf_lt_one`: a strictly increasing cdf takes
  values in `(0, 1)`.
* `ProbabilityTheory.measureReal_setOf_cdf_le`: the probability integral transform.
-/

public section

open MeasureTheory Set Filter Topology

namespace ProbabilityTheory

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- A cdf is measurable. -/
@[fun_prop]
theorem measurable_cdf (ν : Measure ℝ) : Measurable (cdf ν) :=
  (monotone_cdf ν).measurable

/-- The cdf of a probability measure without atoms is continuous. -/
theorem continuous_cdf [NullSingletonClass ν] : Continuous (cdf ν) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [(monotone_cdf ν).continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  refine le_antisymm ((monotone_cdf ν).leftLim_le le_rfl) ?_
  have h := (cdf ν).measure_singleton x
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h
  exact h

/-- The cdf of a probability measure charging every set of positive Lebesgue measure is strictly
increasing. -/
theorem strictMono_cdf (h : volume ≪ ν) : StrictMono (cdf ν) := by
  intro x y hxy
  rw [cdf_eq_real, cdf_eq_real, ← sub_pos, ← measureReal_sdiff (Iic_subset_Iic.2 hxy.le)
    measurableSet_Iic, Iic_sdiff_Iic]
  refine ENNReal.toReal_pos (fun h0 => ?_) (measure_ne_top _ _)
  have h1 := h h0
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h1
  linarith

/-- A strictly increasing cdf is positive. -/
theorem cdf_pos (h : volume ≪ ν) (x : ℝ) : 0 < cdf ν x :=
  (cdf_nonneg ν (x - 1)).trans_lt (strictMono_cdf h (sub_one_lt x))

/-- A strictly increasing cdf is less than `1`. -/
theorem cdf_lt_one (h : volume ≪ ν) (x : ℝ) : cdf ν x < 1 :=
  (strictMono_cdf h (lt_add_one x)).trans_le (cdf_le_one ν (x + 1))

/-- **The probability integral transform.** If `ν` has no atoms, then `cdf ν x ≤ α` has
probability `α` for `x ∼ ν` and `α ∈ [0, 1]`. -/
theorem measureReal_setOf_cdf_le [NullSingletonClass ν] {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ν.real {x | cdf ν x ≤ α} = α := by
  set S := {x | cdf ν x ≤ α}
  rcases h1.eq_or_lt with rfl | h1
  · rw [show S = univ from eq_univ_of_forall fun x => cdf_le_one ν x, probReal_univ]
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds h1)).exists
  have hbdd : BddAbove S := ⟨b, fun x (hx : cdf ν x ≤ α) => le_of_not_gt fun hbx =>
    (hx.trans_lt hb).not_ge (monotone_cdf ν hbx.le)⟩
  -- Below `α > 0` the cdf takes the value `α`, by the intermediate value theorem.
  have hval : 0 < α → ∃ t₀, cdf ν t₀ = α := fun h0 => by
    obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually (gt_mem_nhds h0)).exists
    exact mem_range_of_exists_le_of_exists_ge continuous_cdf ⟨a, ha.le⟩ ⟨b, hb.le⟩
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, measureReal_empty]
    refine (h0.eq_or_lt.resolve_right fun h0 => ?_)
    obtain ⟨t₀, ht₀⟩ := hval h0
    exact (eq_empty_iff_forall_notMem.1 hS t₀) ht₀.le
  -- `S` is a closed lower set, hence `S = (-∞, t]` for its supremum `t`.
  set t := sSup S
  have ht : t ∈ S := (isClosed_le continuous_cdf continuous_const).csSup_mem hS hbdd
  have hSt : S = Iic t :=
    ext fun x => ⟨fun hx => le_csSup hbdd hx, fun hx => (monotone_cdf ν hx).trans ht⟩
  rw [hSt, ← cdf_eq_real]
  refine le_antisymm ht ?_
  rcases h0.eq_or_lt with rfl | h0
  · exact cdf_nonneg ν t
  obtain ⟨t₀, ht₀⟩ := hval h0
  rw [← ht₀]
  exact monotone_cdf ν (le_csSup hbdd (show cdf ν t₀ ≤ α from ht₀.le))

end ProbabilityTheory
