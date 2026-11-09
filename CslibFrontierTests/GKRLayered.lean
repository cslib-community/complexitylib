/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Interactive.GKR.Layered

/-! # Layered arithmetic circuits and the GKR identity

A one-layer circuit multiplying its two inputs, its value, and an instance of the GKR identity.
-/

namespace CslibFrontierTests.GKRLayered

open Cslib.Interactive.GKR MvPolynomial Cslib.BitString

/-- One multiplication gate on two inputs: layer `0` has `2 ^ 1` gates, layer `1` has `2 ^ 0`. -/
def mulTwo : LayeredCircuit where
  depth := 1
  width := fun i => if i = 0 then 1 else 0
  gate _ _ := .mul
  left _ _ := fun _ => false
  right _ _ := fun _ => true

-- The output is the product of the two inputs.
example (x : (Fin 1 → Bool) → ℤ) :
    mulTwo.output x (fun _ => false) = x (fun _ => false) * x (fun _ => true) := rfl

-- The GKR identity for the multiplication layer, at any point.
example (W : (Fin (mulTwo.width 0) → Bool) → ℤ) (z : Fin (mulTwo.width 1) → ℤ) :
    eval z (multilinearExtension (mulTwo.step 0 W)) =
      ∑ b, ∑ c,
        (eval (Sum.elim z (Sum.elim (bitPoint b) (bitPoint c)))
            (multilinearExtension (mulTwo.addPred (R := ℤ) 0)) * (W b + W c) +
          eval (Sum.elim z (Sum.elim (bitPoint b) (bitPoint c)))
            (multilinearExtension (mulTwo.multPred (R := ℤ) 0)) * (W b * W c)) :=
  mulTwo.eval_multilinearExtension_step 0 W z

end CslibFrontierTests.GKRLayered
