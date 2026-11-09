/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.VertexFibers

/-!
# Cofacial variable corners from consecutive directed arguments

Two consecutive constraint arguments determine cofacial variable-side corners, one at the
later argument and one immediately before the earlier argument in its variable rotation.
The two literal face steps derive cofaciality from the original clockwise argument order.
Repeated variables and other boundary visits are permitted; distinctness is a separate
condition when a later operation merges the selected vertices. These identities are original.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- A predecessor in a variable's actual cyclic rotation is still on the variable side.
No injectivity of variable labels or bound on the degree is required. -/
theorem side_rotate_symm_variable (rho : RotationSystem (incidenceGraph F))
    (o : F.Occurrence) : (rho.rotate.symm (incidenceDart o false)).2 = false := by
  let d := rho.rotate.symm (incidenceDart o false)
  obtain ⟨p, hp⟩ := exists_incidenceDart d
  have hv : (incidenceDart p d.2).vertex = (incidenceDart o false).vertex := by
    rw [hp]
    exact rho.mirror.vertex_rotate (incidenceDart o false)
  exact ((vertex_incidenceDart_eq_iff p o d.2 false).mp hv).1

/-- With the existing face convention, the later argument's variable corner reaches the
earlier argument's constraint end in one face step. This uses the directed argument cycle. -/
theorem faceNext_variable_of_argumentSuccessor
    (rho : RotationSystem (incidenceGraph F)) (ho : RespectsArgumentOrder rho)
    (o p : F.Occurrence) (hp : argumentSuccessor p = o) :
    rho.faceNext (incidenceDart o false) = incidenceDart p true := by
  change rho.rotate.symm (incidenceDart o true) = incidenceDart p true
  apply rho.rotate.injective
  rw [Equiv.apply_symm_apply, ho p, hp]

/-- Consecutive ordered arguments supply cofacial variable corners internally: the later
argument end and the predecessor of the earlier variable end are two face steps apart.
The theorem also covers repeated labels and coincident corners without inventing a dart. -/
theorem sameCycle_variable_corners_of_argumentSuccessor
    (rho : RotationSystem (incidenceGraph F)) (ho : RespectsArgumentOrder rho)
    (o p : F.Occurrence) (hp : argumentSuccessor p = o) :
    rho.faceNext.SameCycle (incidenceDart o false)
      (rho.rotate.symm (incidenceDart p false)) := by
  have h1 : rho.faceNext.SameCycle (incidenceDart o false)
      (rho.faceNext (incidenceDart o false)) :=
    (Equiv.Perm.sameCycle_apply_left.mpr .rfl).symm
  have h2 : rho.faceNext.SameCycle (incidenceDart p true)
      (rho.faceNext (incidenceDart p true)) :=
    (Equiv.Perm.sameCycle_apply_left.mpr .rfl).symm
  rw [faceNext_variable_of_argumentSuccessor rho ho o p hp] at h1
  exact h1.trans h2

end Cslib.Complexity.CSP
