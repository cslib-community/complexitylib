/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Tail quantiles of a nonnegative discrete law

A level `q ∈ (0, 1]` has an upper quantile in every law `μ : PMF ℝ≥0`, even one with countably
infinite support and atoms: some cutoff `τ` has `P(X > τ) ≤ q ≤ P(X ≥ τ)`. Thresholds of
single-threshold stopping rules are chosen this way, for instance a median of the maximum
(`q = 1/2`) or the cutoff that accepts an i.i.d. value with probability `1/n`.

`Cslib.Probability.PMF.exists_quantile` is the analogous statement for laws on a finite type.
Mathlib's `ProbabilityTheory.cdf` concerns measures on `ℝ` and provides no quantile.

The proof takes `τ` to be the infimum of the cutoffs with `P(X > t) ≤ q`. That set is nonempty
because the tail tends to `0`. Continuity of `μ.toMeasure` from below gives `P(X > τ) ≤ q`, and
continuity from above gives `q ≤ P(X ≥ τ)`. The level `q = 0` is excluded: a law with unbounded
support has `P(X > t) > 0` for every `t`.

## Main results

* `Cslib.Probability.PMF.exists_tail_quantile`: an upper quantile exists at every
  positive level.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal NNReal
open MeasureTheory Set Filter

/-- **Tail quantiles exist.** For every level `0 < q ≤ 1` there is a cutoff `τ` with
`P(X > τ) ≤ q ≤ P(X ≥ τ)`. -/
theorem exists_tail_quantile (μ : PMF ℝ≥0) {q : ℝ≥0∞} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ τ : ℝ≥0, μ.toOuterMeasure (Ioi τ) ≤ q ∧ q ≤ μ.toOuterMeasure (Ici τ) := by
  simp only [← PMF.toMeasure_apply_eq_toOuterMeasure]
  set ν := μ.toMeasure
  have hlim : Tendsto (fun n : ℕ => ν (Ioi (n : ℝ≥0))) atTop (nhds 0) := by
    have hanti : Antitone fun n : ℕ => Ioi (n : ℝ≥0) := fun m n hmn =>
      Ioi_subset_Ioi (by exact_mod_cast hmn)
    have hinter : (⋂ n : ℕ, Ioi (n : ℝ≥0)) = ∅ := by
      ext x
      simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
      exact exists_nat_ge x
    have := tendsto_measure_iInter_atTop (μ := ν) (fun _ => measurableSet_Ioi.nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rwa [hinter, measure_empty] at this
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hq)).exists
  set S := {t : ℝ≥0 | ν (Ioi t) ≤ q}
  have hS : S.Nonempty := ⟨N, hN.le⟩
  refine ⟨sInf S, ?_, ?_⟩
  · -- continuity from below: `(τ, ∞)` is the increasing union of `(τ + 1/(n+1), ∞)`
    have hU : Ioi (sInf S) = ⋃ n : ℕ, Ioi (sInf S + 1 / (n + 1)) := by
      ext x
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hx)
        refine ⟨n, ?_⟩
        calc sInf S + 1 / (n + 1) < sInf S + (x - sInf S) := by gcongr
          _ = x := add_tsub_cancel_of_le hx.le
      · rintro ⟨n, hn⟩
        exact lt_of_le_of_lt le_self_add hn
    have hmono : Monotone fun n : ℕ => Ioi (sInf S + 1 / ((n : ℝ≥0) + 1)) := fun m n hmn =>
      Ioi_subset_Ioi (by gcongr)
    rw [hU, hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt hS
      (lt_add_of_pos_right (sInf S) (by positivity : (0 : ℝ≥0) < 1 / ((n : ℝ≥0) + 1)))
    exact (measure_mono fun x hx => lt_of_le_of_lt htlt.le hx).trans ht
  · rcases eq_or_ne (sInf S) 0 with h0 | h0
    · have huniv : Ici (0 : ℝ≥0) = univ := eq_univ_of_forall fun x => by simp
      rw [h0, huniv, measure_univ]
      exact hq1
    -- continuity from above: `[τ, ∞)` is the decreasing intersection of `(τ - 1/(n+1), ∞)`
    have hpos : 0 < sInf S := pos_iff_ne_zero.mpr h0
    have hI : Ici (sInf S) = ⋂ n : ℕ, Ioi (sInf S - 1 / (n + 1)) := by
      ext x
      simp only [mem_Ici, mem_iInter, mem_Ioi]
      constructor
      · intro hx n
        exact lt_of_lt_of_le (tsub_lt_self hpos (by positivity)) hx
      · intro hx
        by_contra hlt
        push Not at hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hlt)
        have h2 : x + 1 / ((n : ℝ≥0) + 1) < sInf S := by
          calc x + 1 / ((n : ℝ≥0) + 1) < x + (sInf S - x) := by gcongr
            _ = sInf S := add_tsub_cancel_of_le hlt.le
        exact absurd (hx n) (not_lt.mpr (lt_tsub_iff_right.mpr h2).le)
    have hanti : Antitone fun n : ℕ => Ioi (sInf S - 1 / ((n : ℝ≥0) + 1)) := fun m n hmn =>
      Ioi_subset_Ioi (by gcongr)
    rw [hI, hanti.measure_iInter (fun _ => measurableSet_Ioi.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    refine le_iInf fun n => ?_
    have hlt : sInf S - 1 / ((n : ℝ≥0) + 1) < sInf S := tsub_lt_self hpos (by positivity)
    have := notMem_of_lt_csInf hlt (OrderBot.bddBelow S)
    simp only [S, mem_ofPred_eq, not_le] at this
    exact this.le

end Cslib.Probability.PMF
