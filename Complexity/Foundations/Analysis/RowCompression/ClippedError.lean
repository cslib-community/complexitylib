/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Preloss
import Mathlib.Tactic.Linarith

/-!
# Recovering coordinate bounds from small clipped errors

Below one, the maximum of the clipped relative first-channel error and clipped absolute
second-channel error bounds both original errors. This shared fact is used by the static
polynomial comparison and by the adjacent-prefix sentinel estimates.

## Main results

* `Cslib.RowCompression.abs_sub_le_of_clippedError_le`: small clipped error gives the actual
  relative first-coordinate and absolute second-coordinate bounds.
-/

public section

namespace Cslib.RowCompression

/-- Below one, clipping discards no information. The first target may be arbitrarily large. -/
theorem abs_sub_le_of_clippedError_le {d v ε : ℝ} {w : Fin 2 → ℝ}
    (hd : 0 ≤ d) (hε : ε < 1) (he : clippedError d v w ≤ ε) :
    |w 0 - d| ≤ (1 + d) * ε ∧ |w 1 - v| ≤ ε := by
  have hfirst : |w 0 - d| / (1 + d) ≤ ε :=
    (min_le_iff.mp ((le_max_left _ _).trans he)).resolve_left (not_le.mpr hε)
  have hsecond : |w 1 - v| ≤ ε :=
    (min_le_iff.mp ((le_max_right _ _).trans he)).resolve_left (not_le.mpr hε)
  refine ⟨?_, hsecond⟩
  simpa only [mul_comm] using (div_le_iff₀ (by linarith : 0 < 1 + d)).mp hfirst

end Cslib.RowCompression
