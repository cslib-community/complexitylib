/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Restriction

/-! Ordinary-import raw certificate lengths for decoding and a funded boundary scan. -/

namespace CslibFrontierTests.RotationCertificateLength

open Cslib.Complexity Graph Graph.RotationCertificate CSP.OrderedBoundary

private abbrev star : Graph := ⟨[0, 1, 2], [(0, 2), (1, 2)]⟩

-- The supplied table is arbitrary and accepted; it is not assumed to be generated.
-- Decoding and generating again retain the exact presentation length.
example (c : RotationCertificate) (h : verifyRotation star c = true) :
    (ofRotation (decode star c h)).successor.length = c.successor.length := by
  rw [length_ofRotation, length_of_verifyRotation h]

private theorem restricted_lookup (c : RotationCertificate) (h : verifyRotation star c = true)
    (h₁ : c.successor.getD 1 0 = 3) (h₃ : c.successor.getD 3 0 = 1) :
    (restrictPrefix 2 c).successor.getD 1 0 = 1 := by
  have hc : 2 ≤ c.successor.length := by
    rw [length_of_verifyRotation h]
    decide
  have hr := getD_restrictPrefix_two c 2 1 (by decide) hc (by rw [h₁]; decide)
    (by rw [h₁, h₃]; decide)
  simpa only [h₁, h₃] using hr

-- This actual two-argument incidence rotation has a last-argument first return 1 -> 3 -> 1.
example : (restrictPrefix 2 ⟨[0, 3, 2, 1]⟩).successor.getD 1 0 = 1 :=
  restricted_lookup _ (by decide +kernel) (by decide) (by decide)

example : (restrictPrefix 2 ⟨[0, 3, 2, 1]⟩).successor = [0, 1] := by decide +kernel

-- Numerical genus is not part of the length lemma. This accepted torus rotation has one
-- face, while a full numerical checker correctly rejects its genus.
private abbrev torus : Graph := ⟨[0], [(0, 0), (0, 0)]⟩

example : verifyRotation torus ⟨[2, 3, 1, 0]⟩ = true ∧
    verifyGenusZero torus ⟨[2, 3, 1, 0]⟩ = false := by decide +kernel

example : (⟨[2, 3, 1, 0]⟩ : RotationCertificate).successor.length = 2 * torus.2.length :=
  length_of_verifyRotation (G := torus) (by decide +kernel)

example : (⟨[]⟩ : RotationCertificate).successor.length =
    2 * (⟨[5, 5, 99], []⟩ : Graph).2.length :=
  length_of_verifyRotation (G := ⟨[5, 5, 99], []⟩) (by decide +kernel)

end CslibFrontierTests.RotationCertificateLength
