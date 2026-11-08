/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.DoubleStar
import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Certificate

/-! Arbitrary-arity two-star rotations, exact forward tables, and separate nullary centers. -/

open Cslib.Complexity Graph Graph.RotationSystem

example : doubleStarGraph 0 = ([0, 1], []) := by decide

example : RotationCertificate.ofRotation (doubleStarRotation 0) = ⟨[]⟩ := by decide +kernel

example : RotationCertificate.ofRotation (doubleStarRotation 1) = ⟨[2, 1, 0, 3]⟩ := by
  decide +kernel

example : RotationCertificate.ofRotation (doubleStarRotation 2) =
    ⟨[6, 3, 4, 1, 2, 7, 0, 5]⟩ := by decide +kernel

example : RotationCertificate.ofRotation (doubleStarRotation 3) =
    ⟨[10, 3, 8, 5, 6, 1, 4, 9, 2, 11, 0, 7]⟩ := by decide +kernel

example : RotationCertificate.verifyGenusZero (doubleStarGraph 3)
    (RotationCertificate.ofRotation (doubleStarRotation 3)) = true := by decide +kernel

example : Nat.card (doubleStarRotation 31).Face = 31 := card_faces_doubleStarRotation 31

example : (doubleStarRotation 31).NumericalGenusZero := by
  generalize (31 : ℕ) = n
  exact numericalGenusZero_doubleStarRotation n

example : (doubleStarRotation 0).NumericalGenusZero := numericalGenusZero_doubleStarRotation 0
