/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Declarations
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateTransport

/-!
# Raw numerical certificates under isolated-point declaration changes

With every incident endpoint declared on both graphs, changing only the declaration list
retains the exact raw numerical checker result. Extra or missing isolated points satisfy the
existing conventional Euler equation separately; they need no darts. This extends the
membership-preserving declaration transport to raw certificates and arbitrary point components.
It asserts no geometric-planarity equivalence.
-/

public section

namespace Cslib.Complexity.Graph.RotationCertificate

open RotationSystem

private theorem verifyGenusZero_redeclare_of_true (vertices newVertices : List ℕ)
    (edges : List (ℕ × ℕ))
    (hG : ∀ v ∈ Graph.incidenceVertices (vertices, edges), v ∈ vertices)
    (hH : ∀ v ∈ Graph.incidenceVertices (newVertices, edges), v ∈ newVertices)
    (c : RotationCertificate) (hc : verifyGenusZero (vertices, edges) c = true) :
    verifyGenusZero (newVertices, edges) c = true := by
  obtain ⟨hrot, hgenus⟩ := (verifyGenusZero_eq_true_iff _ _).mp hc
  let r := decode (vertices, edges) c hrot
  have hg : (r.redeclare newVertices).NumericalGenusZero := by
    exact r.numericalGenusZero_transport (H := (newVertices, edges))
      (Equiv.refl _) (by intro a b; rfl)
      (by intro a; rfl) hG hH hgenus
  have he : ofRotation (r.redeclare newVertices) = c := by
    change ofRotation r = c
    exact ofRotation_decode hrot
  rw [← he]
  apply (verifyGenusZero_eq_true_iff _ _).mpr
  refine ⟨verifyRotation_ofRotation _ hH, ?_⟩
  rw [decode_ofRotation _ hH]
  exact hg

/-- Declaring different isolated points, or repeating declarations, retains the exact raw
numerical-checker result when all actual edge endpoints are declared on both sides. -/
theorem verifyGenusZero_redeclare (vertices newVertices : List ℕ) (edges : List (ℕ × ℕ))
    (hG : ∀ v ∈ Graph.incidenceVertices (vertices, edges), v ∈ vertices)
    (hH : ∀ v ∈ Graph.incidenceVertices (newVertices, edges), v ∈ newVertices)
    (c : RotationCertificate) :
    verifyGenusZero (newVertices, edges) c = verifyGenusZero (vertices, edges) c := by
  rw [Bool.eq_iff_iff]
  exact ⟨verifyGenusZero_redeclare_of_true newVertices vertices edges hH hG c,
    verifyGenusZero_redeclare_of_true vertices newVertices edges hG hH c⟩

/-- Equal indexed edge lists retain the exact raw numerical result under any valid endpoint
declarations. Vertex declarations may differ at point components or contain duplicates. -/
theorem verifyGenusZero_eq_of_edges_eq {G H : Graph} (he : G.2 = H.2)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hH : ∀ v ∈ H.incidenceVertices, v ∈ H.1) (c : RotationCertificate) :
    verifyGenusZero H c = verifyGenusZero G c := by
  rcases G with ⟨vertices, edges⟩
  rcases H with ⟨newVertices, newEdges⟩
  cases he
  exact verifyGenusZero_redeclare vertices newVertices edges hG hH c

end Cslib.Complexity.Graph.RotationCertificate
