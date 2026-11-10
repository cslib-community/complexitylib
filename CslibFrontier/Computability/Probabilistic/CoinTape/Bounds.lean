/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.CoinTape

/-!
# A common envelope for saved coins and supported outputs

A strict-PPT program has one polynomial envelope that bounds both the coins required by its
total replay and the encoded length of every supported result. Combining the two bounds once
lets callers budget a continuation from the same envelope used to replay its predecessor.

## Main results

* `Cslib.Probability.IsPPTOn.exists_total_seeded_evaluator_with_length`: a native total replay,
  its exact law for any sufficiently long uniform tape, and a common supported-output bound.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- One polynomial envelope bounds both required coins and every supported encoded output.
The evaluator is supported even on short or malformed tapes, inherited from the total replay
construction. Only its exact uniform distribution law requires the stated minimum length. -/
theorem IsPPTOn.exists_total_seeded_evaluator_with_length
    {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ (c d : ℕ) (evaluate : α → List Bool → β),
      ComputableInPolyTime (fun (a, coins) => evaluate a coins)
        (encPair input encBits) output ∧
      (∀ a coins, evaluate a coins ∈ (ProbComp.eval (program a)).support) ∧
      (∀ a length, c * ((input a).length + 1) ^ d ≤ length →
        ProbComp.eval (program a) = (BitString.uniformList length).map (evaluate a)) ∧
      ∀ a result, result ∈ (ProbComp.eval (program a)).support →
        (output result).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨c₁, d₁, evaluate, hevaluate, hsupported, hlaw⟩ := h.exists_total_seeded_evaluator
  obtain ⟨c₂, d₂, hlength⟩ := h.length_le
  have hfirst (a : α) : c₁ * ((input a).length + 1) ^ d₁ ≤
      max c₁ c₂ * ((input a).length + 1) ^ max d₁ d₂ :=
    Nat.mul_le_mul (Nat.le_max_left _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
  have hsecond (a : α) : c₂ * ((input a).length + 1) ^ d₂ ≤
      max c₁ c₂ * ((input a).length + 1) ^ max d₁ d₂ :=
    Nat.mul_le_mul (Nat.le_max_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
  exact ⟨max c₁ c₂, max d₁ d₂, evaluate, hevaluate, hsupported,
    fun a length hle => hlaw a length ((hfirst a).trans hle),
    fun a result hresult => (hlength a result hresult).trans (hsecond a)⟩

end Cslib.Probability
