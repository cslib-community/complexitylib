/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpaceConverse
import Mathlib.Tactic.FinCases

/-!
Algebraic converse tests with explicit colors, without a numerical-genus premise. These are
not tests of a geometric converse: no such endpoint is supplied by the new modules.
-/

namespace ComplexityTests.RotationCycleSpaceConverse

open Cslib.Complexity Graph Graph.RotationSystem

private abbrev bridge : Graph := ([2 ^ 100, 7, 7, 19], [(2 ^ 100, 7)])

private def bridgeRotation : RotationSystem bridge where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

example : bridgeRotation.NumericalGenusZero := by
  apply bridgeRotation.numericalGenusZero_of_vertexEven_faceBoundary (by decide)
  intro x hx
  have hzero : x 0 = false := by
    have h := hx (2 ^ 100)
    norm_num [vertexParity, Dart, Fintype.sum_prod_type, Fintype.sum_bool,
      Dart.vertex, edgeEndpoint] at h
    change (∑ i : Fin 1, x i) = false at h
    simpa only [Fin.sum_univ_one] using h
  refine ⟨fun _ => false, funext fun i => ?_⟩
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa only [faceBoundary, Bool.false_xor] using hzero.symm

private abbrev twoLoops : Graph := ([2 ^ 100, 7, 7, 19, 23], [(2 ^ 100, 2 ^ 100), (7, 7)])

private def twoLoopRotation : RotationSystem twoLoops where
  rotate := Dart.reversal twoLoops
  sameCycle_iff := by decide +kernel

-- Each actual face is a singleton. Two distinct loop occurrences and their two ends
-- survive the dual transport; duplicate declarations and isolated points are harmless.
example : twoLoopRotation.NumericalGenusZero := by
  apply twoLoopRotation.numericalGenusZero_of_vertexEven_faceBoundary (by decide)
  intro x _
  let q : twoLoopRotation.Face → Bool := Quotient.lift
    (fun d : Dart twoLoops => if d.2 then x d.1 else false)
    (by
      intro a b h
      have hab : a = b := h.eq_of_left (by
        rcases a with ⟨i, c⟩
        cases c <;> rfl)
      exact congrArg (fun d : Dart twoLoops => if d.2 then x d.1 else false) hab)
  refine ⟨q, funext fun i => ?_⟩
  simp [faceBoundary, q]

private abbrev digon : Graph := ([7, 100, 7, 123], [(7, 100), (7, 100)])

private def digonRotation : RotationSystem digon where
  rotate := Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl Bool)
  sameCycle_iff := by decide +kernel

example : digonRotation.NumericalGenusZero := by
  apply digonRotation.numericalGenusZero_of_vertexEven_faceBoundary (by decide)
  intro x hx
  have hbits : x 0 = x 1 := by
    have h : x 0 + x 1 = false := by
      simpa [vertexParity, Dart, Fintype.sum_prod_type,
        Fin.sum_univ_two, Dart.vertex, edgeEndpoint] using hx 7
    exact (BooleanRing.add_eq_zero' _ _).mp (h.trans Bool.zero_eq_false.symm)
  let c (d : Dart digon) : Bool := decide (d.1 = 0) ^^ d.2
  have hc : ∀ a b, digonRotation.faceNext.SameCycle a b → c a = c b := by decide +kernel
  let q : digonRotation.Face → Bool := Quotient.lift
    (fun d : Dart digon => if c d then x 0 else false)
    (fun a b h => congrArg (fun b => if b then x 0 else false) (hc a b h))
  refine ⟨q, funext fun i => ?_⟩
  fin_cases i <;> simp [faceBoundary, q, c, hbits]

private def pointsRotation (vertices : List ℕ) : RotationSystem (vertices, []) where
  rotate := Equiv.refl _
  sameCycle_iff d := d.1.elim0

example (vertices : List ℕ) : (pointsRotation vertices).NumericalGenusZero := by
  apply (pointsRotation vertices).numericalGenusZero_of_vertexEven_faceBoundary
    (by simp [incidenceVertices])
  intro x _
  exact ⟨fun _ => false, funext fun i => i.elim0⟩

example : (pointsRotation []).NumericalGenusZero := by
  apply (pointsRotation []).numericalGenusZero_of_vertexEven_faceBoundary
    (by simp [incidenceVertices])
  intro x _
  exact ⟨fun _ => false, funext fun i => i.elim0⟩

private abbrev torus : Graph := ([0, 9, 9], [(0, 0), (0, 0)])

private def torusRotation : RotationSystem torus where
  rotate := ((Dart.indexEquiv torus).trans
    (Equiv.swap (1 : Fin 4) 2 * finRotate 4 * Equiv.swap (1 : Fin 4) 2)).trans
      (Dart.indexEquiv torus).symm
  sameCycle_iff := by decide +kernel

-- The wrong rotation's universal color premise fails, although its underlying graph is
-- planar. This remains an algebraic obstruction, not a geometric nonrealizability test.
example : ¬ ∀ x : Fin torus.2.length → Bool, torus.VertexEven x →
    ∃ q : torusRotation.Face → Bool, torusRotation.faceBoundary q = x := by
  intro h
  have hG : ∀ v ∈ torus.incidenceVertices, v ∈ torus.1 := by decide
  have hg := torusRotation.numericalGenusZero_of_vertexEven_faceBoundary hG h
  have he := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation torusRotation hG)).mpr
      ((RotationCertificate.decode_ofRotation torusRotation hG).symm ▸ hg)
  exact (by decide : RotationCertificate.verifyEuler torus
    (RotationCertificate.ofRotation torusRotation) ≠ true) he

end ComplexityTests.RotationCycleSpaceConverse
