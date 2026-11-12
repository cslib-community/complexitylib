/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.DenseRestrictionPredictor
import Mathlib.Tactic

/-! Lemma 6.2 of submission 865 on a one-row instance. -/

namespace CslibFrontierTests.CircuitDenseRestrictionPredictor
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Communication

/-- The first bit of a one-bit string. -/
def g₁ (x : BitString 1) : Bool := x 0

/-- The protocol that answers the only cell solves `R_g(X)` on the matrices of one row that
differ from each other or have equal row values: here `X` is all of `U_1`, and the answer is valid
unless the two rows are equal, where rejecting is valid. -/
private noncomputable def cellProtocol :
    Protocol (Fin 1 → BitString 1) (Fin 1 → BitString 1) (Option (Fin 1 × Fin 1)) :=
  .alice (fun A => A 0 0)
    (.bob (fun B => B 0 0) (.output none) (.output (some (0, 0))))
    (.bob (fun B => B 0 0) (.output (some (0, 0))) (.output none))

private theorem cellProtocol_solves :
    cellProtocol.Solves (composeKW g₁) Set.univ Set.univ := by
  intro A _ B _
  have hA : A = fun _ _ => A 0 0 := funext fun i => funext fun j => by fin_cases i; fin_cases j; rfl
  have hB : B = fun _ _ => B 0 0 := funext fun i => funext fun j => by fin_cases i; fin_cases j; rfl
  rw [hA, hB]
  cases A 0 0 <;> cases B 0 0 <;> simp [cellProtocol, composeKW, g₁]

/-- Lemma 6.2 at `m = 1` on the full set: the density is one, so some formula of depth at most
three predicts `g₁` under any `ν` with accuracy at least `1/2 + 1/2 = 1`. -/
example (ν : PMF (BitString 1)) : ∃ h : Formula signature 1,
    h.depthWith binaryCost ≤ cellProtocol.depth + 1 ∧
      1 / 2 + (2 ^ 1 * density (m := 1) ν Set.univ - 1) / (2 * (2 ^ 1 - 1)) ≤
        accuracy ν g₁ h :=
  exists_accuracy_ge ν cellProtocol_solves le_rfl

end CslibFrontierTests.CircuitDenseRestrictionPredictor
