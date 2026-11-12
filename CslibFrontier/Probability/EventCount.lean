/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.Probability.PMF.ToMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Expected counts of events indexed by a list

If every event indexed by a list entry has measure at most `B`, their occurrence count has
integral at most `l.length * B`. Repeated entries are counted with multiplicity, and the events
need not be independent. The measure theorem also provides measurability of the count; it does
not require the measure to be a probability measure or to have finite total mass.

The `PMF` corollary states the same bound as a weighted sum without a measurable-space hypothesis.
It follows from the measure theorem by giving the sample space its discrete measurable structure
and using `PMF.lintegral_toMeasure`.

## Main results

* `Cslib.Probability.measurable_and_lintegral_countP_le`: measurability and a first-moment bound
  for a list of measurable events.
* `Cslib.Probability.PMF.tsum_mul_countP_le`: the corresponding bound for a `PMF`.

Extracted from the discrete and measure-valued locality-sensitive-hashing analyses in
`CslibFrontier.DataStructure.NearNeighbor.LSH` and
`CslibFrontier.DataStructure.NearNeighbor.MeasureLSH`.
-/

public section

namespace Cslib.Probability

open MeasureTheory
open scoped ENNReal

variable {X : Type*}

/-- A list count of measurable events, each of measure at most `B`, is measurable and has
Lebesgue integral at most `l.length * B`. -/
theorem measurable_and_lintegral_countP_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Ω → X → Prop) [∀ ω x, Decidable (E ω x)] (B : ℝ≥0∞) :
    ∀ l : List X, (∀ x ∈ l, MeasurableSet {ω | E ω x}) →
      (∀ x ∈ l, μ {ω | E ω x} ≤ B) →
        Measurable (fun ω => ((l.countP fun x => decide (E ω x) : ℕ) : ℝ≥0∞)) ∧
          ∫⁻ ω, ((l.countP fun x => decide (E ω x) : ℕ) : ℝ≥0∞) ∂μ ≤ l.length * B
  | [], _, _ => by
      simp only [List.countP_nil, Nat.cast_zero, lintegral_zero, List.length_nil, zero_mul]
      exact ⟨measurable_const, le_rfl⟩
  | y :: l, hm, hl => by
      have hmy := hm y List.mem_cons_self
      have hy := hl y List.mem_cons_self
      obtain ⟨hm_ih, hi_ih⟩ := measurable_and_lintegral_countP_le μ E B l
        (fun x hx => hm x (List.mem_cons_of_mem y hx))
        (fun x hx => hl x (List.mem_cons_of_mem y hx))
      have hfun : (fun ω => (((y :: l).countP fun x => decide (E ω x) : ℕ) : ℝ≥0∞)) =
          fun ω => {ω | E ω y}.indicator 1 ω + ((l.countP fun x => decide (E ω x) : ℕ) : ℝ≥0∞) := by
        funext ω
        rw [List.countP_cons]
        by_cases hω : E ω y
        · simp only [hω, decide_true, ite_true, Nat.cast_add, Nat.cast_one,
            Set.indicator_of_mem (show ω ∈ {ω | E ω y} from hω), Pi.one_apply, add_comm]
        · simp only [hω, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero,
            Set.indicator_of_notMem (show ω ∉ {ω | E ω y} from hω), zero_add]
      rw [hfun]
      refine ⟨(measurable_one.indicator hmy).add hm_ih, ?_⟩
      rw [lintegral_add_left (measurable_one.indicator hmy), lintegral_indicator_one hmy,
        List.length_cons, Nat.cast_add, Nat.cast_one, add_comm (l.length : ℝ≥0∞) 1,
        add_mul, one_mul]
      exact add_le_add hy hi_ih

namespace PMF

/-- A list count of events, each of probability at most `B`, has expectation at most
`l.length * B`. Repeated entries are counted with multiplicity; no independence is required. -/
theorem tsum_mul_countP_le {Ω : Type*} (μ : PMF Ω) (E : Ω → X → Prop)
    [∀ ω x, Decidable (E ω x)] (B : ℝ≥0∞) (l : List X)
    (hE : ∀ x ∈ l, μ.toOuterMeasure {ω | E ω x} ≤ B) :
    ∑' ω, μ ω * ((l.countP fun x => decide (E ω x) : ℕ) : ℝ≥0∞) ≤ l.length * B := by
  let _ : MeasurableSpace Ω := ⊤
  obtain ⟨hm, hb⟩ := measurable_and_lintegral_countP_le μ.toMeasure E B l
    (fun _ _ => MeasurableSet.of_discrete) (fun x hx => by
      rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply μ MeasurableSet.of_discrete]
      exact hE x hx)
  rwa [PMF.lintegral_toMeasure μ hm] at hb

end PMF

end Cslib.Probability
