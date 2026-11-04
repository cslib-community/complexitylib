/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed
public import Complexity.Foundations.Data.Code.LowDegreeExtension.Constant

/-!
# Constant packed gate extensions

A constant Boolean gate extends to its constant packed vector, including at field points
outside the encoded alphabet. This does not require the decoder to invert the encoder.

## Main results

* `Cslib.TreeEval.Ary.Packed.gateExtension_const`: constant gates have constant extensions.
-/

public section

namespace Cslib.TreeEval.Ary.Packed

/-- A constant gate extends to the encoded constant at every field point. -/
theorem gateExtension_const {K H : Type*} [Field K] [Fintype H] [DecidableEq H]
    [Nonempty H] {b d r : ℕ} (h : H ↪ K)
    (encode : (Fin b → Bool) → Fin r → H) (decode : (Fin r → H) → Fin b → Bool)
    (v : Fin b → Bool) (x : Fin d → Fin r → K) (i : Fin r) :
    gateExtension h encode decode (fun _ => v) x i = h (encode v i) := by
  exact Code.lowDegreeExtension_const h (h (encode v i)) _

end Cslib.TreeEval.Ary.Packed
