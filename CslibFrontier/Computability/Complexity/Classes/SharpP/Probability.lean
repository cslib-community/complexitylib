/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Map

/-!
# Acceptance counts and uniform probabilities

The count of accepted random words is exactly their probability under a uniform word source
multiplied by the number of words. This connects counting-based verifier contracts to ordinary
probability bounds without changing the verifier's behavior on malformed random strings.

## Main results

* `Cslib.Complexity.uniformList_acceptCount`: the exact uniform acceptance probability.
* `Cslib.Complexity.uniformList_acceptCount_toReal`: the same identity over the reals.
* `Cslib.Complexity.acceptCount_le_half_iff`: equivalence of the integer and probability bounds.
-/

public section

namespace Cslib.Complexity

open scoped ENNReal

variable {α : Type} (V : α × List Bool → Bool) (a : α) (n : ℕ)

/-- A counted verifier's uniform acceptance probability is its accepted fraction of all words. -/
theorem uniformList_acceptCount :
    ((BitString.uniformList n).map (fun word => V (a, word))) true =
      (acceptCount V a n : ℝ≥0∞) / 2 ^ n :=
  BitString.uniformList_map_apply (fun word => V (a, word)) n true

/-- The accepted fraction has the same ordinary real-valued interpretation. -/
theorem uniformList_acceptCount_toReal :
    (((BitString.uniformList n).map (fun word => V (a, word))) true).toReal =
      (acceptCount V a n : ℝ) / 2 ^ n := by
  rw [uniformList_acceptCount]
  simp

/-- Accepting at most half the random words is equivalent to probability at most one half. -/
theorem acceptCount_le_half_iff :
    2 * acceptCount V a n ≤ 2 ^ n ↔
      (((BitString.uniformList n).map (fun word => V (a, word))) true).toReal ≤ 1 / 2 := by
  rw [uniformList_acceptCount_toReal, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  have hcast : 2 * acceptCount V a n ≤ 2 ^ n ↔
      (2 : ℝ) * acceptCount V a n ≤ 2 ^ n := by norm_cast
  rw [hcast]
  constructor <;> intro h <;> linarith

end Cslib.Complexity
