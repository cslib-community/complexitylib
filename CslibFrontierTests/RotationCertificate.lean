/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Computability.PolyTime.Graph.RotationSystem

/-! # Finite rotation and componentwise Euler regression cases -/

open Cslib.Complexity Cslib.Complexity.Graph Turing.MultiTapeTM
open RotationCertificate

namespace RotationCertificateTests

example : verifyGenusZero ([], []) ⟨[]⟩ = true := by decide
example : verifyGenusZero ([0, 10, 10], []) ⟨[]⟩ = true := by decide

-- A bridge has one two-dart face orbit.
example : verifyGenusZero ([0, 1], [(0, 1)]) ⟨[0, 1]⟩ = true := by decide
example : faceTable ([0, 1], [(0, 1)]) ⟨[0, 1]⟩ = [1, 0] := by decide
example : (List.range 2).countP (faceRepBool 2 [1, 0]) = 1 := by decide

private def bridgeRotation : RotationSystem ([0, 1], [(0, 1)]) where
  rotate := Equiv.refl _
  sameCycle_iff := by decide

-- An ordinary-import client can apply the mathematical representative criterion.
example : ¬bridgeRotation.IsFaceRepresentative (0, true) := by
  intro h
  have hh := h (0, false) (by decide)
  have : 1 ≤ 0 := hh
  omega

-- A loop retains two darts, and both singleton face orbits must be counted.
example : verifyGenusZero ([0], [(0, 0)]) ⟨[1, 0]⟩ = true := by decide
example : faceTable ([0], [(0, 0)]) ⟨[1, 0]⟩ = [0, 1] := by decide
example : (List.range 2).countP (faceRepBool 2 [0, 1]) = 2 := by decide
example : verifyRotation ([0], [(0, 0)]) ⟨[0, 1]⟩ = false := by decide

private def parallelThree : Graph := ([0, 1], [(0, 1), (0, 1), (0, 1)])

example : verifyGenusZero parallelThree ⟨[2, 5, 4, 1, 0, 3]⟩ = true := by decide
example : verifyRotation parallelThree ⟨[2, 3, 4, 5, 0, 1]⟩ = true := by decide
-- This rejects the supplied toroidal rotation, not the underlying graph.
example : verifyGenusZero parallelThree ⟨[2, 3, 4, 5, 0, 1]⟩ = false := by decide
example : (List.range 6).countP
    (faceRepBool 6 (faceTable parallelThree ⟨[2, 5, 4, 1, 0, 3]⟩)) = 3 := by decide
example : (List.range 6).countP
    (faceRepBool 6 (faceTable parallelThree ⟨[2, 3, 4, 5, 0, 1]⟩)) = 1 := by decide

-- Each component gets its own Euler test; isolates use their point-component face convention.
example : verifyGenusZero ([0, 1, 2, 3, 99], [(0, 1), (2, 3)]) ⟨[0, 1, 2, 3]⟩ = true := by
  decide
example : verifyGenusZero ([0, 1, 2, 3], [(0, 1), (0, 1), (0, 1), (2, 3)])
    ⟨[2, 3, 4, 5, 0, 1, 6, 7]⟩ = false := by decide

example : verifyRotation ([0, 1], [(0, 1)]) ⟨[0]⟩ = false := by decide
example : verifyRotation ([0, 1], [(0, 1)]) ⟨[0, 1, 2]⟩ = false := by decide
example : verifyRotation ([0, 1], [(0, 1)]) ⟨[0, 0]⟩ = false := by decide
example : verifyRotation ([0, 1], [(0, 1)]) ⟨[0, 2 ^ 100]⟩ = false := by decide
example : verifyRotation ([0], [(0, 1)]) ⟨[0, 1]⟩ = false := by decide
example : walk [2 ^ 100] 3 (2 ^ 100) = 0 := by decide
example : verifyGenusZero ([2 ^ 100, 2 ^ 100 + 1], [(2 ^ 100, 2 ^ 100 + 1)])
    ⟨[0, 1]⟩ = true := by decide

-- A checked mathematical client decodes the finite loop certificate to the existing rotation.
private noncomputable def loopRotation : RotationSystem ([0], [(0, 0)]) :=
  decode _ ⟨[1, 0]⟩ (by decide)

example : loopRotation.NumericalGenusZero :=
  (verifyEuler_eq_true_iff (by decide : verifyRotation ([0], [(0, 0)]) ⟨[1, 0]⟩ = true)).mp
    (by decide)

example : (encRotationCertificate (ofRotation loopRotation)).length ≤
    10 * ((encGraph ([0], [(0, 0)])).length + 1) ^ 2 := length_enc_ofRotation_le _

-- Automation composes the native checker with a concrete certificate supplier.
example : ComputableInPolyTime (fun G : Graph => verifyGenusZero G ⟨[]⟩) encGraph encBool := by
  have hi : ComputableInPolyTime (fun G : Graph => (G, (⟨[]⟩ : RotationCertificate)))
      encGraph encGraphRotationCertificate :=
    ComputableInPolyTime.id'.prod (ComputableInPolyTime.const (⟨[]⟩ : RotationCertificate))
  exact computableInPolyTime_verifyGenusZero.comp hi

end RotationCertificateTests
