/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate

/-!
# Rotation transport across vertex declarations

Changing only the declared vertex list preserves indexed darts, rotations and every face.
Equal declared membership preserves componentwise numerical genus zero: vertex counts use
distinct declarations, and isolated-point components have the same roots. This applies to
repeated declarations produced by arbitrary graph contraction as well as recognition queries.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- Keep every indexed edge end and successor while changing the vertex declaration list. -/
@[expose] def redeclare {vertices : List ℕ} {edges : List (ℕ × ℕ)}
    (r : RotationSystem (vertices, edges)) (newVertices : List ℕ) :
    RotationSystem (newVertices, edges) := ⟨r.rotate, r.sameCycle_iff⟩

/-- Component membership depends on declared membership, not repeated declaration positions. -/
theorem sameComponent_redeclare {vertices newVertices : List ℕ} {edges : List (ℕ × ℕ)}
    (hm : ∀ v, v ∈ vertices ↔ v ∈ newVertices) (u v : ℕ) :
    RotationCertificate.SameComponent (vertices, edges) u v ↔
      RotationCertificate.SameComponent (newVertices, edges) u v := by
  let component (S : Set ℕ) : Prop := ∃ hu : u ∈ S, ∃ hv : v ∈ S,
    (Graph.toSimpleGraph (vertices, edges)).induce S |>.Reachable ⟨u, hu⟩ ⟨v, hv⟩
  have hs : ({x | x ∈ vertices} : Set ℕ) = {x | x ∈ newVertices} := Set.ext hm
  change component {x | x ∈ vertices} ↔ component {x | x ∈ newVertices}
  rw [hs]

/-- The numerical Euler predicate is invariant under reordering/repeating existing declared
vertices. Every face orbit and listed edge occurrence remains unchanged. -/
theorem numericalGenusZero_redeclare_iff {vertices newVertices : List ℕ}
    {edges : List (ℕ × ℕ)} (hm : ∀ v, v ∈ vertices ↔ v ∈ newVertices)
    (r : RotationSystem (vertices, edges)) :
    (redeclare r newVertices).NumericalGenusZero ↔ r.NumericalGenusZero := by
  classical
  have hp : (Graph.distinctVertices (vertices, edges)).Perm
      (Graph.distinctVertices (newVertices, edges)) :=
    (List.perm_ext_iff_of_nodup (nodup_distinctVertices (vertices, edges))
      (nodup_distinctVertices (newVertices, edges))).mpr
      (fun v => by simpa only [mem_distinctVertices] using hm v)
  have hc (root : ℕ) :
      (Graph.distinctVertices (vertices, edges)).countP
        (fun v => decide (RotationCertificate.SameComponent (newVertices, edges) root v)) =
      (Graph.distinctVertices (newVertices, edges)).countP
        (fun v => decide (RotationCertificate.SameComponent (newVertices, edges) root v)) :=
    hp.countP_eq _
  unfold RotationSystem.NumericalGenusZero
  simp_rw [hm, sameComponent_redeclare hm, hc]
  rfl

/-- Appending a duplicate declaration of an already declared vertex changes no numerical result. -/
theorem numericalGenusZero_append_duplicate_iff {vertices : List ℕ} {edges : List (ℕ × ℕ)}
    {v : ℕ} (hv : v ∈ vertices) (r : RotationSystem (vertices ++ [v], edges)) :
    (redeclare r vertices).NumericalGenusZero ↔ r.NumericalGenusZero :=
  numericalGenusZero_redeclare_iff (fun u => by
    simp only [List.mem_append, List.mem_singleton]
    exact or_iff_left_of_imp (fun h => h ▸ hv)) r

end Cslib.Complexity.Graph.RotationSystem
