/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm

/-!
# Subtraction and comparison in binary

Truncated subtraction `b - a` iterates the predecessor `a` times, counting in binary. It takes time
linear in the value `a` and work space linear in the lengths of the binary encodings. The order
`a < b` tests whether `b - a` is zero.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInO.natSub`: truncated subtraction in binary.
* `Turing.MultiTapeTM.ComputableTidilyInO.natLt`: the strict order in binary.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace ComputableTidilyInO

/-- **Truncated subtraction in binary**, `b - a` from `(a, b)`. -/
public theorem natSub :
    ComputableTidilyInO (fun p : ℕ × ℕ => p.2 - p.1) (encPair encNat encNat) encNat
      (fun p => (p.1 + 1) * ((encPair encNat encNat p).length + 1) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 :=
  Internal.NormalForm.inO ComputableInO.natSub

/-- **The strict order in binary.** -/
public theorem natLt :
    ComputableTidilyInO (fun p : ℕ × ℕ => decide (p.1 < p.2)) (encPair encNat encNat) encBool
      (fun p => (p.1 + 1) * ((encPair encNat encNat p).length + 1) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 :=
  Internal.NormalForm.inO ComputableInO.natLt

end ComputableTidilyInO

end Turing.MultiTapeTM
