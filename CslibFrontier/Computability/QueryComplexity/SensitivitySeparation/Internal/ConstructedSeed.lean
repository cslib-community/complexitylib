/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Construction
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Labeling
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.ParameterBounds
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Iterates
import Mathlib.Tactic.Positivity

/-!
# Superquadratic sensitivity separation: constructed seed

Instantiates the construction with concrete parameters: the regular cyclic tournament on
`2 * M ^ 2 + 1` vertices, `Nat.ceil (Real.sqrt M)` labels, and a good labeling coming from the union
bound. For `1 ≤ d` and `9 ^ (d + 1) ≤ M` this yields, without further hypotheses, a nonconstant
Boolean function vanishing at the all-false input with sensitivity at most
`2 * (d + 2) * M ^ (d + 1)` and block sensitivity at the all-false input at least
`M ^ 2 * (2 * M ^ 2 + 1) ^ d`.

## Main results

* `construction_label_count_pos`: `0 < Nat.ceil (Real.sqrt M)` for `0 < M`.
* `exists_constructed_seed`: a nonconstant seed function with sensitivity at most
  `2 * (d + 2) * M ^ (d + 1)` and block sensitivity at least `M ^ 2 * (2 * M ^ 2 + 1) ^ d` at the
  all-false input.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/ConstructedSeed.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- For `0 < M`, the number of labels `Nat.ceil (Real.sqrt M)` is positive. -/
theorem construction_label_count_pos {M : ℕ} (hM : 0 < M) :
    0 < Nat.ceil (Real.sqrt (M : ℝ)) :=
  Nat.pos_of_ne_zero fun he => by
    have h := le_ceil_sqrt_sq M
    rw [he, zero_pow two_ne_zero] at h
    omega

/-- For `1 ≤ d` and `9 ^ (d + 1) ≤ M` there is a nonconstant Boolean function `f` on
`constructionDimension d M (Nat.ceil (Real.sqrt M)) > 0` variables with
`f (fun _ => false) = false`, `sensitivity f ≤ 2 * (d + 2) * M ^ (d + 1)` and
`M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt f (fun _ => false)`. -/
theorem exists_constructed_seed (d M : ℕ) (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ∃ f : (Fin (constructionDimension d M (Nat.ceil (Real.sqrt (M : ℝ)))) → Bool) → Bool,
      0 < constructionDimension d M (Nat.ceil (Real.sqrt (M : ℝ))) ∧
      f (fun _ => false) = false ∧ (∃ x y, f x ≠ f y) ∧
      sensitivity f ≤ 2 * (d + 2) * M ^ (d + 1) ∧
      M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt f (fun _ => false) := by
  have h81 := parameter_ge_eighty_one hd hM
  have hMp : 0 < M := by omega
  have hr := construction_label_count_pos hMp
  obtain ⟨A⟩ := regular_goodLabeling_exists (show 3 ≤ M by omega)
  let f := finalWitness d (regularCyclicTournament M) A
  have hs := finalWitness_sensitivity d (regularCyclicTournament M) A hMp hr
    (parameter_epsilon_budget hd hM)
  have hb := finalWitness_blockSensitivity d (regularCyclicTournament M) A hr
  have hbp : 0 < M ^ 2 * (2 * M ^ 2 + 1) ^ d := by positivity
  have hnc := nonconstant_of_blockSensitivityAt_pos f (fun _ => false) (hbp.trans_le hb)
  exact ⟨f, constructionDimension_pos hMp hr,
    finalWitness_zero d (regularCyclicTournament M) A hr, hnc, hs, hb⟩

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
