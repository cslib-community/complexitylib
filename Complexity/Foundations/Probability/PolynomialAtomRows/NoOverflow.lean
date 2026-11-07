/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PolynomialAtomRows.ClippedError
import Mathlib.Tactic.Linarith

/-!
# Actual polynomial row errors when no overflow occurs

For an actual dyadic compression run with no overflow, the final polynomial fourth-root error
is bounded by the weighted preloss sum plus the final raw-prefix error. The final-error
coefficient depends only on the chosen concrete row function and support scale and is fixed
before the compression scale. The preloss coefficient may also depend on that scale.

The comparison uses the actual common preloss: the final compressed row is the final raw row
plus this loss, while the stationary reference is the true row plus the same loss and has the
same actual default. The static capped comparison bounds the first discrepancy. The proved
stationary comparison, with no remaining updates, bounds the second by weighted preloss.

The result includes the empty schedule and imposes no capacity lower bound: there are no
reference continuation updates. All errors concern actual raw prefixes; no final-output bound,
small-error premise, count branch, or bound on the largest true entry is assumed.

This supplies the deterministic no-overflow comparison in [OpenAI2026LogSpace, Section 8.3]
for the concrete preparation, auxiliary-score, and witness functions with fourth roots.
Integrated probabilities, normalized atoms, and the recursive estimator remain separate.

## Main results

* `Cslib.PolynomialAtomRow.exists_noOverflow_root_bound`: the all-horizon actual-to-truth
  comparison with separate weighted-preloss and final-prefix terms.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, the no-overflow comparison following Lemma 8.2
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.PolynomialAtomRow

open Finset RowCompression

variable (kind : PolynomialAtomRow) {θ : ℝ}

/-- **No-overflow actual-to-truth comparison.** The final-prefix coefficient is fixed before
choosing `η`. Weighted preloss needs prefix envelopes only at true first targets at least
`η / 2`; the independent final-prefix envelope covers every retained endpoint. The horizon
may be zero, and no capacity lower bound or small-error premise is needed. -/
theorem exists_noOverflow_root_bound (hθ : 0 < θ) :
    ∃ Cfinal : ℝ, 0 ≤ Cfinal ∧ ∀ (η : ℝ), 0 < η → η ≤ θ / 10000 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {ι : Type*} (s : Finset ι) (n : ℕ → ℕ)
        (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (truth : ι → Fin 2 → ℝ) (K : ℕ),
        0 < K → a.defaultValue = 0 → ∀ (m : ℕ),
        (∀ i < m, stepThreshold s n (fun _ => K) (dyadicFloor η m) Δ a i ≤
          dyadicFloor η m i) →
        (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ η / 2) →
        ∀ (ε : ℕ → ℝ), (∀ i < m, 0 ≤ ε i) →
        (∀ i < m, ∀ y ∈ s, η / 2 ≤ truth y 0 →
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (i + 1) y) ≤ ε i) →
        ∀ (εfinal : ℝ), 0 ≤ εfinal →
        (∀ y ∈ s,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row m y) ≤ εfinal) →
        ∀ y ∈ s,
        |kind.stateRootError θ s K (iterate s n (fun _ => K) (dyadicFloor η m) Δ a m)
          ⟨0, truth⟩ y| ≤ Cpre * ∑ i ∈ range m, dyadicFloor η m i * ε i + Cfinal * εfinal := by
  obtain ⟨Cfinal, hCfinal, hfinal⟩ := kind.exists_commonLoss_root_bound hθ
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro η hη hmargin
  obtain ⟨Cpre, hCpre, hpre⟩ := kind.exists_stationaryContinuation_root_bound hθ hη hmargin
  refine ⟨Cpre, hCpre, ?_⟩
  intro ι s n Δ a truth K hK ha m hno hfirst hsecond ε hε herr εfinal hεfinal herrfinal y hy
  let actual := iterate s n (fun _ => K) (dyadicFloor η m) Δ a m
  let raw := uncompressedRow Δ a.row m
  let loss := fun y ν => actual.row y ν - raw y ν
  let reference := stationaryState s n (fun _ => K) (dyadicFloor η m) Δ a truth m
  have hloss (x : ι) (_hx : x ∈ s) : |loss x 0| ≤ θ := by
    have h := abs_stationaryState_row_sub_le_dyadic (truth := truth) hη.le m m (le_refl m)
      hno x 0
    rw [stationaryState_row_sub] at h
    change |loss x 0| ≤ η / 100 at h
    linarith
  have hrow : raw + loss = actual.row := by
    funext x ν
    simp [loss]
  have hactual := hfinal s K actual.defaultValue truth raw loss hK hfirst hloss
    εfinal hεfinal herrfinal y hy
  rw [hrow] at hactual
  change |kind.stateRootError θ s K actual reference y| ≤ Cfinal * εfinal at hactual
  have hreference := hpre s n Δ a truth K hK (by rw [ha]) (by rw [ha]; linarith)
    m m 0 (by omega) hno hfirst hsecond (by intro i hi hi'; omega) ε hε herr y hy
  change |kind.stateRootError θ s K reference ⟨0, truth⟩ y| ≤
    Cpre * ∑ i ∈ range m, dyadicFloor η m i * ε i at hreference
  calc
    _ ≤ |kind.stateRootError θ s K actual reference y| +
        |kind.stateRootError θ s K reference ⟨0, truth⟩ y| := abs_sub_le _ _ _
    _ ≤ Cfinal * εfinal + Cpre * ∑ i ∈ range m, dyadicFloor η m i * ε i :=
      add_le_add hactual hreference
    _ = _ := add_comm _ _

end Cslib.PolynomialAtomRow
