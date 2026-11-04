/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Mathlib.Tactic.Linarith

/-!
# Direct binary counter resource certificates

The successor, predecessor and zero test certificates here are weakenings of the streaming
transducer certificates `computableInTimeAndSpace_succ`, `computableInTimeAndSpace_pred` and
`computableInTimeAndSpace_isZero`.

## Main results

* `ComputableInO.natSucc`, `ComputableInO.natPred`: binary counters within the quadratic clock
  and linear charged workspace used by their clients.
* `ComputableInO.natIsZero`: linear zero testing.
-/

@[expose] public section
namespace Turing.MultiTapeTM

namespace ComputableInO

/-- Binary successor within the quadratic clock and linear charged workspace used by its
clients, weakened from the linear-time, zero-work-space transducer certificate
`computableInTimeAndSpace_succ`. -/
theorem natSucc :
    ComputableInO (· + 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      (fun n => (encNat n).length + 1) :=
  (of_linear .natSucc).mono_le (fun n => by simp only [encNat_apply]; nlinarith) fun _ => by omega

/-- Binary predecessor within the quadratic clock and linear charged workspace used by its
clients, weakened from the linear-time, zero-work-space transducer certificate
`computableInTimeAndSpace_pred`. -/
theorem natPred :
    ComputableInO (· - 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      (fun n => (encNat n).length + 1) :=
  (of_linear .natPred).mono_le (fun n => by simp only [encNat_apply]; nlinarith) fun _ => by omega

/-- Zero testing is linear in both resources, weakened from the transducer certificate
`computableInTimeAndSpace_isZero`; the output charge remains explicit. -/
theorem natIsZero :
    ComputableInO (fun n => decide (n = 0)) encNat encBool
      (fun n => (encNat n).length) (fun n => (encNat n).length) :=
  of_linear .natIsZero

end ComputableInO
end Turing.MultiTapeTM
