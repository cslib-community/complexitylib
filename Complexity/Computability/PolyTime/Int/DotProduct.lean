/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.List.DotProduct
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native integer padded dot products

One plain certificate computes Mathlib's public list dot product for every unary cutoff
and both complete framed signed-binary lists. Padding and truncation follow the existing
operation; discarded list entries are still charged as part of the input.

## Main results

* `ComputableInPolyTime.listDotProduct`: uniform polynomial-time implementation.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib Mathlib.Tactic.Matrix

/-- Compute the public padded dot product with unary cutoff and signed-binary coefficients. -/
@[fun_prop] theorem listDotProduct :
    ComputableInPolyTime (fun p : ℕ × List ℤ × List ℤ =>
      ListMatrix.dotProduct p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair (encList encIntBin) (encList encIntBin))) encIntBin := by
  simp only [ListMatrix.dotProduct_eq_sum_map_range]
  fun_prop

end Turing.MultiTapeTM.ComputableInPolyTime
