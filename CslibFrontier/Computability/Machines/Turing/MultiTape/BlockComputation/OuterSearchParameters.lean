/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# Block parameters for increasing time guesses

The increasing-guess search turns each time guess into a block width and a horizon. It needs
positive widths, horizons whose blocks cover the guess, and native certificates computing both
from the binary guess. Williams's balanced choice is `BalancedParameters.parameters`.

## Main definitions

* `OuterSearch.Parameters`: a guess-to-parameters map with native certificates.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.OuterSearch

open MultiTapeTM

/-- Block width and horizon for each time guess, covering the guess, with native
certificates on the binary guess. -/
structure Parameters where
  /-- Block width selected for a time guess. -/
  blockWidth : ℕ → ℕ
  /-- Number of blocks selected for a time guess. -/
  horizon : ℕ → ℕ
  /-- Every selected width is positive. -/
  blockWidth_pos : ∀ T, 0 < blockWidth T
  /-- The selected blocks cover every step of the guess. -/
  coverage : ∀ T, T ≤ horizon T * blockWidth T
  /-- Native block width from the binary guess. -/
  blockWidth_inSpace : ComputableInSpace blockWidth encNat encNat (fun T => (encNat T).length)
  /-- Native horizon from the binary guess. -/
  horizon_inSpace : ComputableInSpace horizon encNat encNat (fun T => (encNat T).length)

end Turing.MultiTapePTM.BlockComputation.OuterSearch
