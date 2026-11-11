/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Encoding
public import Complexity.Computability.Circuit.Encoding.Check
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Checking arithmetic gate codes

The shared gate checker applies to the existing arithmetic signature and operator encoding.
The carrier and encoding are fixed and finite; the input count and entire gate list are runtime
data. Output-wire checks remain separate.

## Main results

* `Arithmetic.computableInPolyTime_codeCheck`: uniform arithmetic gate validation.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open Turing.MultiTapeTM

/-- Arithmetic gate validation is polynomial-time for unary input count, binary wire indices
and a fixed finite scalar carrier with its supplied encoding. -/
@[fun_prop]
theorem computableInPolyTime_codeCheck {F γ : Type} [Finite F]
    {eF : F ↪ List Bool} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {gates : γ → List (ArithOp F × List ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hgates : ComputableInPolyTime gates encIn
      (encList (Circuit.encGate (ArithOp.encoding eF)))) :
    ComputableInPolyTime (fun a => codeCheck (arithSignature F) (n a) (gates a))
      encIn encBool :=
  Circuits.computableInPolyTime_codeCheck (σ := arithSignature F)
    (ComputableInPolyTime.of_finite _) hn hgates

end Cslib.Circuits.Arithmetic
