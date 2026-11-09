/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.AdaptivePolicy.Information
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# Sharp binary information bounds

[Aldridge2027], Proposition 4.3 (PDF p. 4). The family has uniform Boolean
states, mismatch cost, and probability `(1+ε)/2` of matching the state.
The information and cost are evaluated from these actual normalized laws.
The limit is through positive ε tending to zero, in nats.

## Main results

* `sharpness_family`: actual one-step instances with span one and gap `ε/2`.
* `information_tendsto_zero`: vanishing mutual information.
* `sharp_ratio`: ratio to the information bound tends to one.
-/

public section
noncomputable section
open Finset Filter Topology
namespace Cslib.Probability.AdaptivePolicy.Sharpness

/-- Uniform binary experiment with mismatch loss. -/
@[expose] def experiment : FiniteMDP Bool Bool where
  initial _ := 1/2
  initial_nonneg _ := by norm_num
  initial_sum := by norm_num
  transition _ _ _ s := if s then 1 else 0
  transition_nonneg _ _ _ _ := by split <;> norm_num
  transition_sum _ _ _ := by simp
  cost _ s a := if a = s then 0 else 1

/-- The binary symmetric channel policy. -/
@[expose] def policy (ε : ℝ) (hε : |ε| ≤ 1) : MarkovPolicy Bool Bool where
  prob _ s a := if a = s then (1+ε)/2 else (1-ε)/2
  nonneg _ _ _ := by have := abs_le.mp hε; split <;> linarith
  sum_prob _ s := by cases s <;> simp <;> ring_nf

/-- The exact binary channel information, with natural logarithms. -/
@[expose] def information (ε : ℝ) : ℝ :=
  (1+ε)/2 * Real.log (1+ε) + (1-ε)/2 * Real.log (1-ε)

/-- The original and open-loop expected costs, evaluated independently. -/
theorem costs (ε : ℝ) (hε : |ε| ≤ 1) :
    experiment.totalCost (policy ε hε) 1 = (1-ε)/2 ∧
    experiment.totalCost (experiment.openLoop (policy ε hε)) 1 = 1/2 := by
  constructor <;> simp [FiniteMDP.totalCost, FiniteMDP.openLoop, FiniteMDP.stateLaw,
    experiment, policy] <;> ring_nf

/-- Mutual information of the actual joint law equals the binary channel formula. -/
theorem mutualInformation_eq (ε : ℝ) (hε : |ε| ≤ 1) :
    experiment.mutualInformation (policy ε hε) 0 = information ε := by
  simp only [FiniteMDP.mutualInformation, Fintype.sum_prod_type,
    FiniteMDP.jointLaw_real, FiniteMDP.productLaw_real]
  norm_num [FiniteMDP.stateLaw, experiment, policy, information]
  ring_nf

private theorem deriv_information {x : ℝ} (hx : |x| < 1) :
    HasDerivAt information ((Real.log (1+x) - Real.log (1-x))/2) x := by
  have hp : 1+x ≠ 0 := by have := abs_lt.mp hx; linarith
  have hm : 1-x ≠ 0 := by have := abs_lt.mp hx; linarith
  convert! (((hasDerivAt_const x 1).add (hasDerivAt_id x)).div_const 2).mul
    (((hasDerivAt_const x 1).add (hasDerivAt_id x)).log hp) |>.add
      ((((hasDerivAt_const x 1).sub (hasDerivAt_id x)).div_const 2).mul
        (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log hm)) using 1
  dsimp
  field_simp [hp, hm]
  ring_nf

/-- Proposition 4.3's information asymptotic, established by differentiation,
without assuming a Taylor expansion or Pinsker sharpness. -/
theorem information_asymptotic :
    Tendsto (fun ε => information ε / ε^2) (𝓝[>] 0) (𝓝 (1/2)) := by
  let d : ℝ → ℝ := fun x => (Real.log (1+x) - Real.log (1-x))/2
  have hd : HasDerivAt d 1 0 := by
    convert! ((((hasDerivAt_const (0:ℝ) 1).add (hasDerivAt_id 0)).log (by norm_num)).sub
      (((hasDerivAt_const (0:ℝ) 1).sub (hasDerivAt_id 0)).log (by norm_num))).div_const 2
      using 1
    norm_num
  have hlim : Tendsto (fun x => d x / (2*x)) (𝓝[>] 0) (𝓝 (1/2)) := by
    have h := hd.tendsto_slope_zero_right
    simp only [d, add_zero, sub_zero, Real.log_one, sub_self, zero_div] at h
    convert! h.div_const 2 using 1
    · ext x
      dsimp [d]
      simp only [zero_add, div_div]
      ring_nf
  apply HasDerivAt.lhopital_zero_right_on_Ioo (b := 1) (f' := d) (g' := fun x => 2*x)
    (by norm_num)
  · intro x hx
    exact deriv_information (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
  · intro x _
    convert! (hasDerivAt_id x).pow 2 using 1; norm_num
  · intro x hx
    nlinarith [hx.1]
  · have h := (deriv_information (x := 0) (by norm_num)).continuousAt.tendsto
    simpa [information] using h.mono_left nhdsWithin_le_nhds
  · have hi : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    convert! hi.pow 2 using 1; norm_num
  · exact hlim

/-- Every member of the family has supported action span one. -/
theorem span_eq_one (ε : ℝ) (hε : |ε| ≤ 1) :
    experiment.actionSpan (policy ε hε) 0
      (experiment.actionValue (experiment.openLoop (policy ε hε)) 1 0) = 1 := by
  have hq (s a : Bool) :
      experiment.actionValue (experiment.openLoop (policy ε hε)) 1 0 s a =
        if a = s then 0 else 1 := by
    simp [FiniteMDP.actionValue, FiniteMDP.value, experiment]
  apply le_antisymm
  · apply FiniteMDP.actionSpan_le _ _ (by norm_num : (0:ℝ) ≤ 1)
    intro s a _ _
    rw [hq]
    split <;> norm_num
  · have h := experiment.sub_le_actionSpan (policy ε hε) 0
      (experiment.actionValue (experiment.openLoop (policy ε hε)) 1 0)
      false true false
      (by norm_num [FiniteMDP.stateLaw, experiment])
      (by simp [FiniteMDP.stateLaw, experiment, policy]; linarith)
      (by simp [FiniteMDP.stateLaw, experiment, policy]; linarith)
    simpa only [hq, Bool.true_eq_false, ite_false, ite_true, sub_zero] using h

/-- The information in the sharpness family vanishes at the limiting parameter. -/
theorem information_tendsto_zero : Tendsto information (𝓝[>] 0) (𝓝 0) := by
  have h := (deriv_information (x := 0) (by norm_num)).continuousAt.tendsto
  simpa [information] using h.mono_left nhdsWithin_le_nhds

/-- Every positive parameter below one is a valid one-step instance with exactly
the numerator, information and span used in `sharp_ratio`. -/
theorem sharpness_family (ε : ℝ) (hpos : 0 < ε) (hlt : ε < 1) :
    ∃ π : MarkovPolicy Bool Bool,
      |experiment.totalCost π 1 - experiment.totalCost (experiment.openLoop π) 1| = ε/2 ∧
      experiment.actionSpan π 0 (experiment.actionValue (experiment.openLoop π) 1 0) = 1 ∧
      experiment.mutualInformation π 0 = information ε := by
  have hv : |ε| ≤ 1 := by rw [abs_of_pos hpos]; exact hlt.le
  refine ⟨policy ε hv, ?_, span_eq_one ε hv, mutualInformation_eq ε hv⟩
  rw [(costs ε hv).1, (costs ε hv).2]
  have he : (1-ε)/2 - 1/2 = -(ε/2) := by ring
  rw [he, abs_neg, abs_of_pos (half_pos hpos)]

/-- Proposition 4.3: the ratio of the actual gap to the information bound
converges to one along valid positive channel parameters. -/
theorem sharp_ratio :
    Tendsto (fun ε => (ε/2) / Real.sqrt (information ε / 2))
      (𝓝[>] 0) (𝓝 1) := by
  have hlim := (information_asymptotic.div_const 2).sqrt
  have hlim' : Tendsto (fun ε => (1/2 : ℝ) / Real.sqrt (information ε / ε^2 / 2))
      (𝓝[>] 0) (𝓝 1) := by
    convert! tendsto_const_nhds.div hlim
      (by norm_num : Real.sqrt ((1/2 : ℝ)/2) ≠ 0) using 1 ; norm_num
  apply hlim'.congr'
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsmall
  have hp : 0 < ε := hε
  have he : information ε / ε^2 / 2 = (information ε / 2) / ε^2 := by ring_nf
  have hi : 0 ≤ information ε / 2 := by
    have hv : |ε| ≤ 1 := by rw [abs_of_pos hp]; exact hsmall.le
    rw [← mutualInformation_eq ε hv]
    exact div_nonneg (experiment.mutualInformation_nonneg _ _) (by norm_num)
  rw [he, Real.sqrt_div hi, Real.sqrt_sq_eq_abs, abs_of_pos hp]
  field_simp

end Cslib.Probability.AdaptivePolicy.Sharpness
