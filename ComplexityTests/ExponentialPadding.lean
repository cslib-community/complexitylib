/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.EXP

/-! Exponential padding needs only the exponential-time API. -/

open Cslib.Complexity Turing.MultiTapeTM

example {Ψ : List Bool × ℕ → Bool}
    (hΨ : ComputableTidilyInPolyTime Ψ (encPair encBits encUnary) encBool) :
    {y : List Bool | Ψ (y, 2 ^ y.length) = true} ∈ E encBits :=
  setOf_mem_E_of_computableInPolyTime_pad (.of_tidy hΨ)

-- The polynomial-time premise is inhabited, including at the empty input.
example : {y : List Bool | (fun _ : List Bool × ℕ => true) (y, 2 ^ y.length) = true} ∈
    E encBits :=
  setOf_mem_E_of_computableInPolyTime_pad (.of_tidy (ComputableTidilyInPolyTime.const true))
