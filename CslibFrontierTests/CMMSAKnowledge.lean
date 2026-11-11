/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.MCSP.PartialHardness.Knowledge

/-! Tests for the knowledge sets of a circuit for the CMMSA table. -/

public section

namespace CslibFrontierTests.CMMSAKnowledge

open Cslib Cslib.Complexity Cslib.PartialMCSP.FromCMMSA Finset

/-! The form No soundness uses: a circuit that agrees with the table of a No instance makes the
function of some variable one of its candidates, since the knowledge set weighs more than
`g θ ≥ 0`. -/

example {I : CMMSAInstance} {Δ k lam P : ℕ} {g : ℝ} (hI : I ∈ (GapCMMSA Δ g 1).no)
    (f : VarFunctions I lam) (h : BooleanFunction (inputLength I Δ k lam))
    (hh : (toInstance I Δ k lam P f).AgreesWith h) :
    ∃ v : Fin I.weights.length, f v ∈ cand h v := by
  have hlt := lt_weight_cand hI P f h hh
  have hg : 0 ≤ g * I.threshold :=
    mul_nonneg (zero_le_one.trans (mem_no_GapCMMSA_one.1 hI).2.1) (Nat.cast_nonneg _)
  by_contra hnone
  push Not at hnone
  have hempty : (univ.filter fun v : Fin I.weights.length => f v ∈ cand h v) = ∅ :=
    filter_eq_empty_iff.2 fun v _ => hnone v
  simp [hempty, CMMSAInstance.weight] at hlt
  linarith

/-! The candidate count at `Δ = 1`, `k = 1` and `δ₀ = 1 / 2`, where the list-size hypothesis
`(1 - 2 δ₀) ^ k ≤ 1 / (2 Δ ^ 2)` holds trivially. -/

example {I : CMMSAInstance} {lam : ℕ} (h : BooleanFunction (inputLength I 1 1 lam))
    (v : Fin I.weights.length) :
    (#(cand h v) : ℝ) ≤ 4 * 2 ^ inputLength I 1 1 lam *
      Real.exp (2 ^ varLength I lam v * Real.binEntropy (1 / 2)) := by
  simpa using card_cand_le (Δ := 1) odd_one one_pos (by norm_num) le_rfl (by norm_num) h v

end CslibFrontierTests.CMMSAKnowledge
