/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.BarringtonClass
import CslibFrontier.Computability.Circuit.Boolean.Yablonskii

/-!
# Parity is in NC¹

The parity of `n` bits has a De Morgan formula of depth at most `2 ⌈log₂ n⌉`, with negations free
(`formulaDepth_parity_le_two_mul_clog`, a balanced tree of XORs). By the formula characterization
of NC¹ (`mem_NC_one_iff_formulaDepth_le`), the parity language is in nonuniform NC¹
(`parity_mem_NC_one`). This is the PARITY half of Exercise 7 of Chapter 13 of
[Arora and Barak, draft of 2007-01-08][AroraBarak07]; the MAJORITY half is
`majority_mem_NC_one`. The exercise suggests the Karchmer–Wigderson game as a proof route; this
proof uses the explicit formula instead.

## Main results

* `Cslib.Circuits.Boolean.parity_mem_NC_one`,
  `Cslib.Circuits.Boolean.parity_mem_FormulaPoly`: the parity language is in NC¹ and in
  `FormulaPoly`.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, draft of
  2007-01-08][AroraBarak07]
-/

public section

namespace Cslib.Circuits.Boolean

/-- **Parity is in NC¹** [AroraBarak07, Chapter 13, Exercise 7]: the language of bit strings with
an odd number of ones has fan-in-two circuits of depth `O(log n)` and polynomial size. -/
theorem parity_mem_NC_one : Language.ofSlices parity ∈ NC 1 := by
  refine mem_NC_one_iff_formulaDepth_le.2 ⟨2, fun n => ?_⟩
  rw [Language.slice_ofSlices]
  refine (formulaDepth_parity_le_two_mul_clog n).trans (Nat.mul_le_mul_left 2 ?_)
  exact Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self one_lt_two n).le

/-- The parity language has polynomial-size De Morgan formulas (`FormulaPoly = NC 1`). -/
theorem parity_mem_FormulaPoly : Language.ofSlices parity ∈ FormulaPoly := by
  rw [FormulaPoly_eq_NC_one]
  exact parity_mem_NC_one

end Cslib.Circuits.Boolean
