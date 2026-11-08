/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (tests of CslibFrontier.Foundations.Data.BitString.HalfSplit)

public import CslibFrontier.Foundations.Data.BitString.HalfSplit

/-! # Unit tests for `Cslib.BitString.halfSplitEquiv` -/

namespace ComplexityTests.BitString.HalfSplit

open Cslib Cslib.BitString

-- 1. An odd length `5` splits into its first `2` and last `3` bits.
example : halfSplitEquiv 5 ![true, false, false, true, true] =
    (![true, false], ![false, true, true]) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> revert i <;> decide

-- 2. An even length `4` splits into two `2`-bit halves, and the inverse reassembles the string.
example (x : BitString 4) :
    halfSplitEquiv 4 ![false, true, true, false] = (![false, true], ![true, false]) ∧
    (halfSplitEquiv 4).symm (halfSplitEquiv 4 x) = x :=
  ⟨by refine Prod.ext ?_ ?_ <;> funext i <;> revert i <;> decide,
    (halfSplitEquiv 4).symm_apply_apply x⟩

end ComplexityTests.BitString.HalfSplit
