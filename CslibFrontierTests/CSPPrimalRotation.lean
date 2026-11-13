/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Euler
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import CslibFrontier.Logics.Propositional.CSP.Boolean

/-! # Actual occurrence-indexed polygon regressions

The finite certificates below are kernel checked. They provide concrete incidence rotations;
none is an oracle premise of the arbitrary-size mathematical bridge.
-/

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP
open Graph.RotationCertificate

namespace CSPPrimalRotationTests

private abbrev unary : CSP Unit ℕ := [⟨(), [2 ^ 100]⟩]
private abbrev unaryOccurrence : unary.Occurrence := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
private theorem unary_unique (o : unary.Occurrence) : o = unaryOccurrence := by
  rcases o with ⟨i, j⟩
  fin_cases i
  fin_cases j
  rfl
private noncomputable def unaryRotation : Graph.RotationSystem (incidenceGraph unary) :=
  decode _ ⟨[0, 1]⟩ (by decide)
private theorem unary_order : RespectsArgumentOrder unaryRotation :=
  (verifyArgumentOrder_eq_true_iff (by decide)).mp (by decide)

-- Sparse binary names never create unused graph vertices or ranges up to their magnitude.
example : polygonGraph unary = ⟨[0], [(0, 0)]⟩ := by decide
example : (polygonRotation unaryRotation).faceNext (polygonDart unaryOccurrence false) =
    polygonDart unaryOccurrence false := by
  rw [faceNext_polygonDart_false]
  exact congrArg (fun o => polygonDart o false) (unary_unique _)
example : (polygonRotation unaryRotation).faceNext (polygonDart unaryOccurrence true) =
    polygonDart unaryOccurrence true := by
  rw [faceNext_polygonDart_true]
  congr 1
  exact unary_unique _
example : (Quotient.mk _ (polygonDart unaryOccurrence false) :
    (polygonRotation unaryRotation).Face) ≠ Quotient.mk _ (polygonDart unaryOccurrence true) :=
  polygon_edge_faces_distinct unaryRotation unary_order (by decide) unaryOccurrence
example : (polygonRotation unaryRotation).NumericalGenusZero :=
  (numericalGenusZero_polygon_iff unaryRotation unary_order (by decide)).mpr
    ((verifyEuler_eq_true_iff (by decide)).mp (by decide))

-- The construction depends on actual scopes, regardless of a malformed declared arity.
example : ¬ CSP.WellFormed (fun _ : Unit => 2) unary := by decide

private abbrev repeated : CSP Unit ℕ := [⟨(), [7, 7, 7]⟩]
private noncomputable def repeatedRotation : Graph.RotationSystem (incidenceGraph repeated) :=
  decode _ ⟨[4, 3, 0, 5, 2, 1]⟩ (by decide)
private theorem repeated_order : RespectsArgumentOrder repeatedRotation :=
  (verifyArgumentOrder_eq_true_iff (by decide)).mp (by decide)

-- Three parallel incidence positions become three different listed loops.
example : (incidenceGraph repeated).edges = [(0, 1), (0, 1), (0, 1)] := by decide
example : polygonGraph repeated = ⟨[0], [(0, 0), (0, 0), (0, 0)]⟩ := by decide
example : polygonDart (F := repeated) ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ false ≠
    polygonDart (F := repeated) ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ false := by decide
example : (polygonRotation repeatedRotation).NumericalGenusZero :=
  (numericalGenusZero_polygon_iff repeatedRotation repeated_order (by decide)).mpr
    ((verifyEuler_eq_true_iff (by decide)).mp (by decide))

private abbrev identical : CSP Unit ℕ := [⟨(), [7]⟩, ⟨(), [7]⟩]
private noncomputable def identicalRotation : Graph.RotationSystem (incidenceGraph identical) :=
  decode _ ⟨[2, 1, 0, 3]⟩ (by decide)
private theorem identical_order : RespectsArgumentOrder identicalRotation :=
  (verifyArgumentOrder_eq_true_iff (by decide)).mp (by decide)

-- Identical records have distinct indexed black faces.
example : (Quotient.mk _ (polygonDart (F := identical) ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ false) :
    (polygonRotation identicalRotation).Face) ≠
      Quotient.mk _ (polygonDart (F := identical) ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ false) := by
  intro h
  have he := congrArg (polygonFaceEquiv identicalRotation identical_order (by decide)) h
  rw [polygonFaceEquiv_black, polygonFaceEquiv_black] at he
  exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj he)

private abbrev disconnected : CSP Unit ℕ := [⟨(), [7]⟩, ⟨(), [2 ^ 100]⟩]
private noncomputable def disconnectedRotation :
    Graph.RotationSystem (incidenceGraph disconnected) :=
  decode _ ⟨[0, 1, 2, 3]⟩ (by decide)
private theorem disconnected_order : RespectsArgumentOrder disconnectedRotation :=
  (verifyArgumentOrder_eq_true_iff (by decide)).mp (by decide)

example : polygonGraph disconnected = ⟨[0, 1], [(0, 0), (1, 1)]⟩ := by decide
example : (polygonRotation disconnectedRotation).NumericalGenusZero :=
  (numericalGenusZero_polygon_iff disconnectedRotation disconnected_order (by decide)).mpr
    ((verifyEuler_eq_true_iff (by decide)).mp (by decide))
example : ¬ SameComponent (polygonGraph disconnected) 0 1 := by
  rw [← componentBool_eq_true_iff (by decide)]
  decide

private abbrev emptyBody : CSP Unit ℕ := []
private noncomputable def emptyRotation : Graph.RotationSystem (incidenceGraph emptyBody) :=
  decode _ ⟨[]⟩ (by decide)
private theorem empty_order : RespectsArgumentOrder emptyRotation :=
  (verifyArgumentOrder_eq_true_iff (by decide)).mp (by decide)

example : polygonGraph emptyBody = ⟨[], []⟩ := by decide
example : (polygonRotation emptyRotation).NumericalGenusZero :=
  (numericalGenusZero_polygon_iff emptyRotation empty_order (by decide)).mpr
    ((verifyEuler_eq_true_iff (by decide)).mp (by decide))
-- A nullary constraint is explicitly outside the positive-scope face correspondence.
example : ¬ (∀ i : Fin ([⟨(), []⟩] : CSP Unit ℕ).length,
    0 < ([⟨(), []⟩] : CSP Unit ℕ)[i.val].scope.length) := by decide

private abbrev toroidal : CSP Unit ℕ := [⟨(), [0, 1, 2]⟩, ⟨(), [0, 1, 2]⟩]
private abbrev toroidalCertificate : Graph.RotationCertificate :=
  ⟨[6, 3, 8, 5, 10, 1, 0, 9, 2, 11, 4, 7]⟩
private noncomputable def toroidalRotation : Graph.RotationSystem (incidenceGraph toroidal) :=
  decode _ toroidalCertificate (by decide)
private theorem toroidal_order : RespectsArgumentOrder toroidalRotation :=
  (verifyArgumentOrder_eq_true_iff (by decide)).mp (by decide)

-- The theorem preserves a non-spherical rotation; it does not manufacture planarity.
example : ¬ toroidalRotation.NumericalGenusZero := by
  unfold toroidalRotation
  rw [← verifyEuler_eq_true_iff (by decide)]
  decide
example : ¬ (polygonRotation toroidalRotation).NumericalGenusZero := by
  rw [numericalGenusZero_polygon_iff toroidalRotation toroidal_order (by decide),
    toroidalRotation, ← verifyEuler_eq_true_iff (by decide)]
  decide

end CSPPrimalRotationTests
