/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Dual
public import Complexity.Computability.Complexity.Problems.Graph.DartConnectivity

/-!
# Edge components of indexed rotations

The source and actual indexed dual have the same edge components on identified darts.
Vertex and edge-reversal invariants connect the permutation generators to the existing
graph reachability relation. Loops and parallel positions are retained; isolated source
points have no darts in this correspondence.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.sameComponent_dual_iff`: exact edge components.
-/

public section

namespace Cslib.Complexity.Graph


namespace RotationSystem

/-- Dual and source edge components agree on the same indexed darts. Isolated source points
are excluded automatically, since this correspondence is stated at darts. -/
theorem sameComponent_dual_iff {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d e : Dart G) :
    RotationCertificate.SameComponent r.dualGraph
      (r.dualDartEquiv d).vertex (r.dualDartEquiv e).vertex ↔
      RotationCertificate.SameComponent G d.vertex e.vertex := by
  let src (d : Dart G) := G.induced.connectedComponentMk ⟨d.vertex, vertex_mem hG d⟩
  let dst (d : Dart r.dualGraph) := r.dualGraph.induced.connectedComponentMk
    ⟨d.vertex, r.dual_vertex_mem d⟩
  have hs {d e : Dart G} (h : RotationCertificate.SameComponent G d.vertex e.vertex) :
      src d = src e := by
    exact SimpleGraph.ConnectedComponent.sound h.2.2
  have ht {d e : Dart r.dualGraph}
      (h : RotationCertificate.SameComponent r.dualGraph d.vertex e.vertex) :
      dst d = dst e := by
    exact SimpleGraph.ConnectedComponent.sound h.2.2
  constructor
  · intro h
    have heq := Dart.eq_of_sameComponent (fun d => src (r.dualDartEquiv.symm d))
      (fun d e hv => by
        obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective d
        obtain ⟨e, rfl⟩ := r.dualDartEquiv.surjective e
        apply hs
        apply r.sameComponent_of_sameFace hG
        apply (r.faceId_eq_iff d e).mp
        simpa only [vertex_dualDartEquiv] using hv)
      (fun d => by
        obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective d
        simpa only [← dualDartEquiv_reverse, Equiv.symm_apply_apply] using
          hs (sameComponent_reverse hG d)) h
    exact ⟨vertex_mem hG d, vertex_mem hG e,
      SimpleGraph.ConnectedComponent.exact (by simpa only [Equiv.symm_apply_apply] using heq)⟩
  · intro h
    have hv (d e : Dart G) (hde : d.vertex = e.vertex) :
        dst (r.dualDartEquiv d) = dst (r.dualDartEquiv e) := by
      apply ht
      have hmid := r.dualRotation.sameComponent_of_sameFace r.dualGraph_endpoints_declared
        ((r.dual_sameFace_iff d.reverse e.reverse).mpr (by
          simpa only [Dart.reverse_reverse] using hde))
      have hd := sameComponent_reverse r.dualGraph_endpoints_declared (r.dualDartEquiv d)
      have he := sameComponent_reverse r.dualGraph_endpoints_declared (r.dualDartEquiv e)
      rw [dualDartEquiv_reverse, dualDartEquiv_reverse] at hmid
      exact hd.trans (hmid.trans he.symm)
    have heq := Dart.eq_of_sameComponent (fun d => dst (r.dualDartEquiv d)) hv
      (fun d => ht (by
        rw [dualDartEquiv_reverse]
        exact sameComponent_reverse r.dualGraph_endpoints_declared (r.dualDartEquiv d))) h
    exact ⟨r.dual_vertex_mem _, r.dual_vertex_mem _,
      SimpleGraph.ConnectedComponent.exact heq⟩

end RotationSystem

end Cslib.Complexity.Graph
