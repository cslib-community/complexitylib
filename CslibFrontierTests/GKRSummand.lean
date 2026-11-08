/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Interactive.Bundle
import CslibFrontier.Computability.Interactive.GKR.Summand

/-! # The GKR summand and bundled reductions

For a one-gate multiplication circuit, the summand sums to the multilinear extension of the output
layer and has degree at most two in every variable. Bundling the identity reduction keeps it
complete.
-/

namespace ComplexityTests.GKRSummand

open Cslib Cslib.Interactive Cslib.Interactive.GKR MvPolynomial Cslib.BitString

/-- One multiplication gate on two inputs. -/
def mulTwo : LayeredCircuit where
  depth := 1
  width := fun i => if i = 0 then 1 else 0
  gate _ _ := .mul
  left _ _ := fun _ => false
  right _ _ := fun _ => true

-- The summand of the multiplication layer sums to the output's multilinear extension.
example (W : (Fin (mulTwo.width 0) → Bool) → ℚ) (z : Fin (mulTwo.width 1) → ℚ) :
    ∑ b, eval (bitPoint b) (mulTwo.summand 0 W z) =
      eval z (multilinearExtension (mulTwo.step 0 W)) :=
  mulTwo.sum_eval_summand 0 W z

-- Each variable has degree at most two, as sumcheck requires.
example (W : (Fin (mulTwo.width 0) → Bool) → ℚ) (z : Fin (mulTwo.width 1) → ℚ) (v) :
    (mulTwo.summand 0 W z).degreeOf v ≤ 2 :=
  mulTwo.degreeOf_summand_le 0 W z v

-- Bundling a family of identity reductions keeps them complete and sound.
example : (Reduction.bundle (s := []) () fun _ : Bool =>
    (Reduction.id (oP := OracleSpec.empty) (oV := OracleSpec.empty) (S := ℕ) (W := Unit))).Complete
      World.plain (fun x _ => x.2 = 0) (fun y _ => y.2 = 0) 0 :=
  Reduction.Complete.bundle (rel₁ := fun _ x _ => x = 0) (rel₂ := fun _ x _ => x = 0)
    (fun _ => rfl) fun _ => Reduction.id_complete _

example : (Reduction.bundle (s := []) () fun _ : Bool =>
    (Reduction.id (oP := OracleSpec.empty) (oV := OracleSpec.empty) (S := ℕ)
      (W := Unit))).verifier.RbrSound {x | x.2 = 0} {y | y.2 = 0} () :=
  Verifier.RbrSound.bundle (L₁ := fun _ => {0}) (L₂ := fun _ => {0}) (fun _ => rfl)
    fun _ => Reduction.id_rbrSound _

end ComplexityTests.GKRSummand
