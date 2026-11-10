/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import Mathlib.Data.Finset.Max

/-!
# Lower tails of a finite distribution

A lower tail of mass `δ` contains every point strictly below its cutoff and no point strictly
above it. Fractional inclusion of the points at the cutoff gives exactly the requested mass,
even when the distribution has atoms or unequal probabilities.

The cutoff is an analysis witness. Existence does not assert that a program can compute a
distribution's quantile, and it supplies no computational advice.

## Main results

* `Cslib.Probability.PMF.exists_quantile`: bracket a prescribed mass by a score cutoff.
* `Cslib.Probability.PMF.exists_lowerTail`: fill the cutoff level fractionally to attain that mass.

## References

[Holenstein2005], Lemma 2.4 and Claim 2.15, uses the lower tail in hard-core boosting.
Fractional boundary weights extend prescribed-cardinality subsets to arbitrary finite distributions.
Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

public section

namespace Cslib.Probability.PMF

variable {α : Type*} [Fintype α]

/-- A finite score distribution has a cutoff bracketing every probability level. -/
theorem exists_quantile (source : PMF α) (score : α → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) :
    ∃ cutoff ∈ Set.range score,
      (∑ x, if score x < cutoff then (source x).toReal else 0) ≤ δ ∧
      δ ≤ ∑ x, if score x ≤ cutoff then (source x).toReal else 0 := by
  classical
  let cumulative := fun cutoff => ∑ x, if score x ≤ cutoff then (source x).toReal else 0
  let candidates := Finset.univ.filter (fun x => δ ≤ cumulative (score x))
  have hnonempty : (Finset.univ : Finset α).Nonempty := by
    obtain ⟨x, _⟩ := source.support_nonempty
    exact ⟨x, Finset.mem_univ _⟩
  have hcandidates : candidates.Nonempty := by
    obtain ⟨x, _, hx⟩ := Finset.exists_max_image Finset.univ score hnonempty
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa only [cumulative, ite_eq_left (hx _ (Finset.mem_univ _)), sum_toReal] using hδone
  obtain ⟨cut, hcut, hmin⟩ := Finset.exists_min_image candidates score hcandidates
  refine ⟨score cut, ⟨cut, rfl⟩, ?_, (Finset.mem_filter.mp hcut).2⟩
  let below := Finset.univ.filter (fun x => score x < score cut)
  by_cases hbelow : below.Nonempty
  · obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image below score hbelow
    have hxc : score x < score cut := (Finset.mem_filter.mp hx).2
    have hxnot : x ∉ candidates := fun hmem => (not_le.mpr hxc) (hmin x hmem)
    have hsmall : cumulative (score x) < δ := by
      simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hxnot
    have hevent (y : α) : score y < score cut ↔ score y ≤ score x :=
      ⟨fun hy => hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩),
        fun hy => hy.trans_lt hxc⟩
    simpa only [cumulative, hevent] using hsmall.le
  · have hnone (x : α) : ¬ score x < score cut := by
      intro hx
      exact hbelow ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    simpa only [ite_eq_right (hnone _), Finset.sum_const_zero] using hδ

/-- A lower tail has the prescribed mass, filling only the boundary level fractionally. -/
theorem exists_lowerTail (source : PMF α) (score : α → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) :
    ∃ cutoff ∈ Set.range score, ∃ softSet : α → ℝ,
      (∀ x, softSet x ∈ Set.Icc 0 1) ∧
      (∀ x, score x < cutoff → softSet x = 1) ∧
      (∀ x, cutoff < score x → softSet x = 0) ∧
      (∑ x, (source x).toReal * softSet x) = δ := by
  classical
  obtain ⟨cutoff, hcutoff, hlower, hupper⟩ := exists_quantile source score hδ hδone
  let lower := ∑ x, if score x < cutoff then (source x).toReal else 0
  let boundary := ∑ x, if score x = cutoff then (source x).toReal else 0
  have hboundary : 0 ≤ boundary := Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  have hsplit : (∑ x, if score x ≤ cutoff then (source x).toReal else 0) =
      lower + boundary := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases lt_trichotomy (score x) cutoff with hlt | heq | hgt
    · simp [hlt.le, hlt, hlt.ne]
    · simp [heq]
    · simp [not_le_of_gt hgt, hgt.not_gt, hgt.ne']
  rw [hsplit] at hupper
  let fraction := (δ - lower) / boundary
  have hfraction : fraction ∈ Set.Icc 0 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hlower) hboundary, ?_⟩
    by_cases hz : boundary = 0
    · simp [fraction, hz]
    · exact (div_le_one (lt_of_le_of_ne hboundary (Ne.symm hz))).mpr (by linarith)
  have hmass : lower + boundary * fraction = δ := by
    by_cases hz : boundary = 0
    · have heq : lower = δ := by linarith
      simp [hz, heq]
    · dsimp only [fraction]
      rw [mul_div_cancel₀ _ hz]
      ring
  let softSet := fun x => if score x < cutoff then (1 : ℝ)
    else if score x = cutoff then fraction else 0
  refine ⟨cutoff, hcutoff, softSet, ?_, ?_, ?_, ?_⟩
  · intro x
    dsimp only [softSet]
    split_ifs <;> simp_all
  · intro x hx
    simp [softSet, hx]
  · intro x hx
    simp [softSet, hx.not_gt, hx.ne']
  · calc
      _ = lower + boundary * fraction := by
        dsimp only [lower, boundary]
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hlt : score x < cutoff
        · simp [softSet, hlt, hlt.ne]
        · simp [softSet, hlt, mul_ite]
      _ = δ := hmass

end Cslib.Probability.PMF
