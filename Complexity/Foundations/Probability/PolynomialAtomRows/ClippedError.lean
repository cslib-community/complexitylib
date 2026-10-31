/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PolynomialAtomRows.RootError
public import Complexity.Foundations.Probability.PolynomialAtomRows.Saturation
public import Complexity.Foundations.Analysis.RowCompression.ClippedError
import Complexity.Foundations.Data.Finset.KthLargest.Truncation
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Static polynomial row comparison from clipped raw error

Compare a raw row and the true row after adding the same bounded first-coordinate loss and
using the same arbitrary default. Their actual polynomial fourth-root outputs differ by at
most a fixed coefficient times the clipped raw-error envelope. The coefficient depends only
on the concrete function and support scale, independently of the largest true entry.

Upper entry saturation and gate closure let us cap entries and padded ranks at `θ` without
changing any output. For error at most `1/2`, entries with true first coordinate above
`4 * (θ + 1)` cap to the same value; every other capped discrepancy is at most
`(4 * θ + 5) * ε`. Capping commutes with the zero-padded order statistic, so the same bound
controls the capped rank. Larger errors are handled by the proved output range.

This is the static final-prefix comparison used in the no-overflow bound following Lemma 8.2
of [OpenAI2026LogSpace, Section 8.3]. No threshold bound, count branch, compression schedule, or
assumed final-output estimate occurs in this module.

## Main results

* `Cslib.PolynomialAtomRow.eval_eq_upperCapped`: actual output is invariant under upper caps
  on its entry and rank arguments.
* `Cslib.PolynomialAtomRow.exists_commonLoss_root_bound`: actual clipped raw error controls
  output-root error after a common bounded first-coordinate loss and arbitrary common default.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, the no-overflow comparison following Lemma 8.2
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.PolynomialAtomRow

open Finset RowCompression

variable (kind : PolynomialAtomRow) {θ : ℝ}

/-- Capping either scalar argument at the support scale leaves the actual output unchanged. -/
theorem eval_eq_upperCapped (hθ : 0 < θ) (v r : ℝ) :
    kind.eval θ v r = kind.eval θ (min θ v) (min θ r) := by
  have hentry : kind.eval θ v r = kind.eval θ (min θ v) r := by
    by_cases hv : v ≤ θ
    · rw [min_eq_right hv]
    · rw [min_eq_left (not_le.mp hv).le]
      exact kind.eval_eq_of_entry_ge hθ (not_le.mp hv).le le_rfl
  apply hentry.trans
  by_cases hr : r ≤ θ
  · rw [min_eq_right hr]
  · rw [min_eq_left (not_le.mp hr).le]
    exact (kind.eval_eq_zero_of_rank_ge hθ
      ((kind.gateThreshold_le_scale hθ).trans (not_le.mp hr).le)).trans
        (kind.eval_eq_zero_of_rank_ge hθ (kind.gateThreshold_le_scale hθ)).symm

private theorem abs_min_add_sub_min_add_le {d raw loss ε : ℝ} (hθ : 0 < θ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 2)
    (hraw : |raw - d| ≤ (1 + d) * ε) (hloss : |loss| ≤ θ) :
    |min θ (raw + loss) - min θ (d + loss)| ≤ (4 * θ + 5) * ε := by
  have hδ : 0 ≤ (4 * θ + 5) * ε := by positivity
  by_cases hdlarge : d ≤ 4 * (θ + 1)
  · apply (abs_min_sub_min_le_max _ _ _ _).trans
    refine max_le (by simpa only [sub_self, abs_zero] using hδ) ?_
    simp only [add_sub_add_right_eq_sub]
    exact hraw.trans (mul_le_mul_of_nonneg_right (by linarith) hε)
  · have hproduct := mul_le_mul_of_nonneg_left hεsmall (by linarith [not_le.mp hdlarge] : 0 ≤ 1 + d)
    have hrawlo := (abs_le.mp hraw).1
    have hlosslo := (abs_le.mp hloss).1
    have hcapraw : θ ≤ raw + loss := by nlinarith [not_le.mp hdlarge]
    have hcaptruth : θ ≤ d + loss := by linarith [not_le.mp hdlarge]
    simpa only [min_eq_left hcapraw, min_eq_left hcaptruth, sub_self, abs_zero] using hδ

/-- A clipped raw-error envelope controls the actual polynomial root outputs after a common
loss. Only the first loss coordinate is bounded; second coordinates and the common default
are unrestricted. The final coefficient is independent of all row data and entry magnitudes. -/
theorem exists_commonLoss_root_bound (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (s : Finset ι) (K : ℕ) (z : ℝ)
      (truth raw loss : ι → Fin 2 → ℝ), 0 < K →
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |loss y 0| ≤ θ) →
      ∀ (ε : ℝ), 0 ≤ ε →
      (∀ y ∈ s, clippedError (truth y 0) (truth y 1) (raw y) ≤ ε) →
      ∀ y ∈ s,
      |kind.stateRootError θ s K ⟨z, raw + loss⟩ ⟨z, truth + loss⟩ y| ≤ C * ε := by
  obtain ⟨A, hA, hroot⟩ := kind.exists_abs_eval_root_sub_le θ
  let B := 4 * θ + 5
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨2 + 2 * A * B, by positivity, ?_⟩
  intro ι s K z truth raw loss hK hfirst hloss ε hε herr y hy
  by_cases hsmall : ε ≤ 1 / 2
  · have hcap (x : ι) (hx : x ∈ s) :
        |min θ ((raw + loss) x 0) - min θ ((truth + loss) x 0)| ≤ B * ε :=
      abs_min_add_sub_min_add_le hθ hε hsmall
        (abs_sub_le_of_clippedError_le (hfirst x hx) (by linarith : ε < 1) (herr x hx)).1
        (hloss x hx)
    have hq : |min θ (firstRank s K z (raw + loss)) -
        min θ (firstRank s K z (truth + loss))| ≤ B * ε := by
      simp only [firstRank, min_max_distrib_left]
      rw [← kthLargest_min (f := fun x => (raw + loss) x 0) hK hθ.le,
        ← kthLargest_min (f := fun x => (truth + loss) x 0) hK hθ.le]
      exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le
        (by simpa only [sub_self, abs_zero] using mul_nonneg hB hε)
        (abs_kthLargest_sub_kthLargest_le hK (mul_nonneg hB hε) hcap))
    unfold stateRootError
    rw [kind.eval_eq_upperCapped hθ ((raw + loss) y 0) (firstRank s K z (raw + loss)),
      kind.eval_eq_upperCapped hθ ((truth + loss) y 0) (firstRank s K z (truth + loss))]
    calc
      _ ≤ A * (|min θ ((raw + loss) y 0) - min θ ((truth + loss) y 0)| +
          |min θ (firstRank s K z (raw + loss)) -
            min θ (firstRank s K z (truth + loss))|) := hroot _ _ _ _
      _ ≤ A * (B * ε + B * ε) := mul_le_mul_of_nonneg_left (add_le_add (hcap y hy) hq) hA
      _ ≤ (2 + 2 * A * B) * ε := by nlinarith
  · apply (kind.abs_stateRootError_le_one θ s K ⟨z, raw + loss⟩ ⟨z, truth + loss⟩ y).trans
    have hlarge : 1 / 2 < ε := not_le.mp hsmall
    nlinarith [mul_nonneg (mul_nonneg hA hB) hε]

end Cslib.PolynomialAtomRow
