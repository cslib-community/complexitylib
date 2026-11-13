/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Table
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ListedVariables
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateLookup

/-!
# The emitted table is the canonical certificate of its positional rotation

Once the variable-word partition and its endpoint fibers are proved, the executed even/odd
successor table is literally `ofRotation` for the constructed rotation. The comparison uses
the existing certificate length and dart-lookup characterization. It introduces no alternative
checker, body or semantics and does not supply a numerical-genus premise.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph

variable {Rel : Type}

/-- The actual bounded table equals the canonical generated certificate of the constructed
rotation, including empty bodies. No table extensionality or inverse lookup is reimplemented. -/
theorem ofRotation_rotationOfVariableCycles_eq (F : CSP Rel ℕ) (cycles : List (List ℕ))
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < (incidenceGraph F).edges.length)
    (hfibers : ∀ o p : F.Occurrence,
      (List.cyclePermutation cycles).SameCycle (incidenceEdgeIndex o) (incidenceEdgeIndex p) ↔
        o.var = p.var) (hn : cycles.flatten.Nodup) :
    RotationCertificate.ofRotation (rotationOfVariableCycles F cycles hcover hfibers) =
      certificate F cycles := by
  apply (RotationCertificate.ofRotation_eq_iff _ _).mpr
  refine ⟨?_, ?_⟩
  · simpa only [incidenceGraph_edges, List.length_map] using length_certificate F cycles
  · intro d
    obtain ⟨o, ho⟩ := exists_incidenceDart d
    rw [← ho, getD_certificate_incidenceDart]
    cases hside : d.2
    · simp only [Bool.false_eq_true, ite_false]
      rw [rotate_rotationOfVariableCycles_false]
      change _ = 2 * (List.finiteCyclePermutation cycles hcover
        ⟨incidenceEdgeIndex o, incidenceEdgeIndex_lt o⟩).val + 0
      rw [List.val_finiteCyclePermutation_eq_nextInCycles cycles hcover hn, Nat.add_zero]
    · simp only [ite_true]
      rw [rotate_rotationOfVariableCycles_true]
      rfl

/-- The complete original raw rotation checker accepts this table once its actual
positional partition and endpoint fibers have been established. Genus is a separate theorem. -/
theorem verifyRotation_certificate (F : CSP Rel ℕ) (cycles : List (List ℕ))
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < (incidenceGraph F).edges.length)
    (hfibers : ∀ o p : F.Occurrence,
      (List.cyclePermutation cycles).SameCycle (incidenceEdgeIndex o) (incidenceEdgeIndex p) ↔
        o.var = p.var) (hn : cycles.flatten.Nodup) :
    RotationCertificate.verifyRotation (incidenceGraph F) (certificate F cycles) = true := by
  rw [← ofRotation_rotationOfVariableCycles_eq F cycles hcover hfibers hn]
  exact RotationCertificate.verifyRotation_ofRotation _ (incidenceVertices_declared F)

end Cslib.Complexity.CSP.GadgetRotation
