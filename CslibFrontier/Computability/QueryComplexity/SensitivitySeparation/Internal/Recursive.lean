/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveOne
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveZero
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveJointZero

/-!
# Superquadratic sensitivity separation: recursive

This file collects the four profile recurrences for one level of the construction, instantiated with
a regular tournament on `2 * M ^ 2 + 1` vertices and a good labeling with `0 < r` columns. The
profiles at output `true` come from `RecursiveOne`, those at output `false` from `RecursiveZero` and
`RecursiveJointZero`. Iterating these linear recurrences controls sensitivity throughout the
recursive construction.

## Main results

* `recursive_four_recurrences`: the side and joint profiles of the next-level family at both outputs
  are bounded by linear combinations of the profiles of `F`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Recursive.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- For a regular tournament `T` on `2 * M ^ 2 + 1` vertices, a good labeling `A` with `0 < r` and a
nested family `F`, the next-level family `P` satisfies: `sideSensitivity P true` is at most
`M ^ 2 * sideSensitivity F false + r * sideSensitivity F true`; `jointSensitivity P true` is at most
`M ^ 2 * jointSensitivity F false + r * sideSensitivity F true`; `sideSensitivity P false` is at
most `15 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true`; and
`jointSensitivity P false` is at most `15 * sideSensitivity F false + 3 * jointSensitivity F true`.
-/
theorem recursive_four_recurrences {M r h : ℕ} {I : Type} [Fintype I]
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    let P := recursiveFamily T.toTournament A.label F
    (sideSensitivity P true ≤ M ^ 2 * sideSensitivity F false + r * sideSensitivity F true) ∧
    (jointSensitivity P true ≤ M ^ 2 * jointSensitivity F false + r * sideSensitivity F true) ∧
    (sideSensitivity P false ≤ 15 * sideSensitivity F false + sideSensitivity F true +
      3 * jointSensitivity F true) ∧
    (jointSensitivity P false ≤ 15 * sideSensitivity F false + 3 * jointSensitivity F true) := by
  exact ⟨recursive_side_one T.toTournament A.label F (M ^ 2) T.outdegree,
    recursive_joint_one T.toTournament A.label F hF (M ^ 2) T.outdegree,
    recursive_side_zero T.toTournament A F hF hr,
    recursive_joint_zero T.toTournament A F hF hr⟩

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
