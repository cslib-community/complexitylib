/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.LastArgument
import Complexity.Logics.Propositional.CSP.Planar.Embedding.LastArgument
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.ArgumentIndices

/-! Actual CSP scope deletion with dense-name changes, repeated labels and nullaries. -/

namespace ComplexityTests.CSPLastArgument

open Cslib.Logic.PL Cslib.Complexity CSP CSP.OrderedBoundary Graph Graph.RotationSystem

private abbrev noneBefore : CSP Unit ℕ := []
private abbrev twoVars : CSP Unit ℕ := [((), [7, 99])]

private def twoVarsRotation : RotationSystem (incidenceGraph twoVars) where
  rotate := Equiv.swap ((⟨0, by decide⟩, true) : Dart (incidenceGraph twoVars))
    (⟨1, by decide⟩, true)
  sameCycle_iff := by decide +kernel

private theorem twoVarsGenus : twoVarsRotation.NumericalGenusZero := by
  have h := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation twoVarsRotation
      (incidenceVertices_declared twoVars))).mp (by decide +kernel)
  exact RotationCertificate.decode_ofRotation twoVarsRotation
    (incidenceVertices_declared twoVars) ▸ h

-- Variable 99 disappears. Its old dense vertex 1 becomes isolated in the prefix;
-- the constraint center changes from old dense name 2 to target dense name 1.
example : lastArgumentPrefixGraph noneBefore () [7] 99 = ([0, 1, 2], [(0, 2)]) := by
  decide +kernel

example : incidenceGraph (noneBefore ++ [((), [7])]) = ([0, 1], [(0, 1)]) := by decide +kernel

example : RotationCertificate.ofRotation
    (deleteLastArgumentRotation noneBefore () [7] 99 twoVarsRotation) = ⟨[0, 1]⟩ := by
  decide +kernel

example : (deleteLastArgumentRotation noneBefore () [7] 99 twoVarsRotation).NumericalGenusZero :=
  numericalGenusZero_deleteLastArgumentRotation noneBefore () [7] 99 twoVarsRotation twoVarsGenus

example : verifyRotationCertificate (noneBefore ++ [((), [7])])
    (RotationCertificate.ofRotation
      (deleteLastArgumentRotation noneBefore () [7] 99 twoVarsRotation)) = true := by decide +kernel

example : verifyRotationCertificate (noneBefore ++ [((), [7])])
    (restrictPrefix 2 ⟨[0, 3, 2, 1]⟩) = true :=
  verifyRotationCertificate_restrictPrefix_lastArgument noneBefore () [7] 99 _ (by decide +kernel)

private abbrev repeated : CSP Unit ℕ := [((), [7, 7])]

private def repeatedRotation : RotationSystem (incidenceGraph repeated) where
  rotate := Equiv.swap ((⟨0, by decide⟩, false) : Dart (incidenceGraph repeated))
    (⟨1, by decide⟩, false) *
    Equiv.swap ((⟨0, by decide⟩, true) : Dart (incidenceGraph repeated)) (⟨1, by decide⟩, true)
  sameCycle_iff := by decide +kernel

example : RotationCertificate.ofRotation
    (deleteLastArgumentRotation noneBefore () [7] 7 repeatedRotation) = ⟨[0, 1]⟩ := by
  decide +kernel

example : verifyRotationCertificate (noneBefore ++ [((), [7])])
    (RotationCertificate.ofRotation
      (deleteLastArgumentRotation noneBefore () [7] 7 repeatedRotation)) = true := by decide +kernel

private abbrev nullaryBefore : CSP Unit ℕ := [((), [])]
private abbrev unaryAfterNullary : CSP Unit ℕ := nullaryBefore ++ [((), [2 ^ 250])]

private def unaryRotation : RotationSystem (incidenceGraph unaryAfterNullary) where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

-- The remaining variable disappears entirely, and both distinct nullary constraints stay.
-- These are two point components with conventional faces, with no supplied dart.
example : incidenceGraph (nullaryBefore ++ [((), [])]) = ([0, 1], []) := by decide +kernel

example : RotationCertificate.ofRotation
    (deleteLastArgumentRotation nullaryBefore () [] (2 ^ 250) unaryRotation) = ⟨[]⟩ := by
  decide +kernel

example : verifyRotationCertificate (nullaryBefore ++ [((), [])])
    (RotationCertificate.ofRotation
      (deleteLastArgumentRotation nullaryBefore () [] (2 ^ 250) unaryRotation)) = true := by
  decide +kernel

example : verifyRotationCertificate (nullaryBefore ++ [((), [])])
    (restrictPrefix 0 ⟨[0, 1]⟩) = true :=
  verifyRotationCertificate_restrictPrefix_lastArgument nullaryBefore () [] (2 ^ 250) _
    (by decide +kernel)

example : (deleteLastArgumentRotation nullaryBefore () [] (2 ^ 250)
    unaryRotation).NumericalGenusZero :=
  numericalGenusZero_deleteLastArgumentRotation nullaryBefore () [] (2 ^ 250) unaryRotation (by
    have h := (RotationCertificate.verifyEuler_eq_true_iff
      (RotationCertificate.verifyRotation_ofRotation unaryRotation
        (incidenceVertices_declared unaryAfterNullary))).mp (by decide +kernel)
    exact RotationCertificate.decode_ofRotation unaryRotation
      (incidenceVertices_declared unaryAfterNullary) ▸ h)

-- The source star has degree five, exceeding the obsolete orthogonal model's bound.
-- Its target keeps the literal four-argument clockwise order, with no reflection.
example : restrictPrefix 8 ⟨[0, 3, 2, 5, 4, 7, 6, 9, 8, 1]⟩ =
    ⟨[0, 3, 2, 5, 4, 7, 6, 1]⟩ := by decide +kernel

example : verifyRotationCertificate (noneBefore ++ [((), [7, 8, 9, 10])])
    (restrictPrefix 8 ⟨[0, 3, 2, 5, 4, 7, 6, 9, 8, 1]⟩) = true :=
  verifyRotationCertificate_restrictPrefix_lastArgument noneBefore () [7, 8, 9, 10] 11 _
    (by decide +kernel)

example : RotationCertificate.verifyGenusZero
    (incidenceGraph (noneBefore ++ [((), [7, 8, 9, 10])])) ⟨[0, 7, 2, 1, 4, 3, 6, 5]⟩ = true ∧
    verifyRotationCertificate (noneBefore ++ [((), [7, 8, 9, 10])])
      ⟨[0, 7, 2, 1, 4, 3, 6, 5]⟩ = false := by decide +kernel

-- Argument-position arithmetic needs no equality decision on the variable domain.
example {V : Type} (v : V) : argumentNextIndex [((), [v, v, v])] 0 2 = 0 := rfl

example {V : Type} (v : V) :
    argumentNextIndex [((), [v, v, v])] 0 2 <
      (Cslib.Logic.PL.CSP.occurrences ([((), [v, v, v])] : CSP Unit V)).length :=
  argumentNextIndex_lt_occurrences
    (F := [((), [v, v, v])]) ⟨(0 : Fin 1), (2 : Fin 3)⟩

end ComplexityTests.CSPLastArgument
