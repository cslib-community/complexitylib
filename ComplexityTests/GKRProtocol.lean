/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Interactive.GKR.Protocol
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-! # The GKR protocol

For a one-gate multiplication circuit over `ZMod 101`, the GKR protocol is perfectly complete and
sound with error `5 / 101`: two sumcheck challenges of error at most `2 / 101` each and one line
challenge of error at most `1 / 101`. The output step adds nothing, because the single output gate
is indexed by zero bits.
-/

namespace ComplexityTests.GKRProtocol

open Cslib Cslib.Interactive Cslib.Interactive.GKR

/-- One multiplication gate on two inputs. -/
def mulTwo : LayeredCircuit where
  depth := 1
  width := fun i => if i = 0 then 1 else 0
  gate _ _ := .mul
  left _ _ := fun _ => false
  right _ _ := fun _ => true

instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

example (x : (Fin (mulTwo.width 0) → Bool) → ZMod 101) :
    (mulTwo.protocol x).Complete World.plain (fun D _ => D = mulTwo.output x) Accept 0 :=
  mulTwo.protocol_complete x

-- The soundness error of this circuit is `5 / 101`.
example : mulTwo.width mulTwo.depth + ∑ i ∈ Finset.range mulTwo.depth, 5 * mulTwo.width i = 5 := by
  decide

example (x : (Fin (mulTwo.width 0) → Bool) → ZMod 101) :
    (mulTwo.protocol x).verifier.Sound (oP := OracleSpec.empty) World.plain {mulTwo.output x}
      Set.univ (5 / 101) := by
  have h := mulTwo.protocol_sound x
  have h5 : mulTwo.width mulTwo.depth + ∑ i ∈ Finset.range mulTwo.depth, 5 * mulTwo.width i =
      5 := by decide
  rw [h5, ZMod.card] at h
  exact_mod_cast h

end ComplexityTests.GKRProtocol
