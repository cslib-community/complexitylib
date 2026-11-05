/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Plain encoding rules on the full nested input used by native replay preparation. -/

namespace ComplexityTests.PlainEncoding

open Turing.MultiTapeTM

-- The complete pair encoding is exposed; neither component is treated as free metadata.
example : ComputableInPolyTime (encPair encUnary encBits)
    (encPair encUnary encBits) encBits := by
  fun_prop

-- Compute a new parameter and concatenate words before exposing their pair encoding.
-- The input includes both source words and uses a different, nested encoding.
example : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool => encPair encUnary encBits
      (p.1 + 1, p.2.1 ++ p.2.2))
    (encPair encUnary (encPair encBits encBits)) encBits := by
  apply ComputableInPolyTime.encoded
  fun_prop

end ComplexityTests.PlainEncoding
