/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.Witness

/-! The inner-quantifier API needs only the NP witness module. -/

namespace ComplexityTests.NPExistsAppend

open Cslib.Complexity Turing.MultiTapeTM

/-! ### The inner quantifier -/

-- The words whose second bit is `true` once one more bit is appended form a problem in `NP` on
-- pairs.
example : {y : List Bool × List Bool | ∃ v : List Bool, v.length = 1 ∧
    (y.2 ++ v).getD 1 false = true} ∈ NP (encPair encBits encBits) := by
  have := mem_NP_setOf_exists_append (enc := encBits) (V := fun x => x.2.getD 1 false)
    (.of_tidy (ComputableTidilyInPolyTime.bitsGetDWithInput (.snd _ _) (.const 1) false)) 1
  simpa using this

-- A zero-length suffix is also supported; the verifier can ignore both words.
example : {y : List Bool × List Bool | ∃ v : List Bool, v.length = 0 ∧
    (fun _ : List Bool × List Bool => true) (y.1, y.2 ++ v) = true} ∈
      NP (encPair encBits encBits) := by
  have h := mem_NP_setOf_exists_append (enc := encBits) (V := fun _ => true)
    (.of_tidy (ComputableTidilyInPolyTime.const true)) 0
  simpa only [Polynomial.eval_zero] using h

end ComplexityTests.NPExistsAppend
