/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMergeGenus
import CslibFrontier.Foundations.Logic.Function.UpdateKernel

/-!
# Components after joining two incident vertices

The actual endpoint update in `mergeGraph` joins precisely the two selected old components.
All other edge components are unchanged. The correspondence is on actual indexed darts;
it requires no connectedness, degree bound or injective vertex-name map.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate

/-- The literal vertex merge joins exactly the two selected components, and no others.
The selected vertices may already belong to one component. -/
theorem sameComponent_mergeGraph_iff_join {G : Graph} (h k : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (a b : Dart G) :
    SameComponent (mergeGraph h k) (mergeDartEquiv h k a).vertex
      (mergeDartEquiv h k b).vertex ↔
      SameComponent G a.vertex b.vertex ∨
        (SameComponent G a.vertex h.vertex ∧ SameComponent G k.vertex b.vertex) ∨
        (SameComponent G a.vertex k.vertex ∧ SameComponent G h.vertex b.vertex) := by
  classical
  let e := mergeDartEquiv h k
  have hH := mergeGraph_endpoints_declared h k hG
  let key (d : Dart G) := G.induced.connectedComponentMk ⟨d.vertex, vertex_mem hG d⟩
  have hkey (d f : Dart G) : key d = key f ↔ SameComponent G d.vertex f.vertex :=
    ⟨fun he => ⟨vertex_mem hG d, vertex_mem hG f,
      SimpleGraph.ConnectedComponent.exact he⟩,
      fun hc => SimpleGraph.ConnectedComponent.sound hc.2.2⟩
  have hvertex (d f : Dart G) (he : d.vertex = f.vertex) : key d = key f :=
    congrArg G.induced.connectedComponentMk (Subtype.ext he)
  let join := Function.update id (key k) (key h)
  have hj (d f : Dart G)
      (he : (e d).vertex = (e f).vertex) : join (key d) = join (key f) := by
    rw [vertex_mergeDartEquiv, vertex_mergeDartEquiv,
      Function.update_id_apply_eq_iff] at he
    apply (Function.update_id_apply_eq_iff _ _ _ _).mpr
    rcases he with he | ⟨hd, hf⟩ | ⟨hd, hf⟩
    · exact Or.inl (hvertex d f he)
    · exact Or.inr (Or.inl ⟨hvertex d h hd, hvertex f k hf⟩)
    · exact Or.inr (Or.inr ⟨hvertex d k hd, hvertex f h hf⟩)
  have hmap {d f : Dart G} (hc : SameComponent G d.vertex f.vertex) :
      SameComponent (mergeGraph h k) (e d).vertex (e f).vertex :=
    sameComponent_map_darts e (fun _ _ he => by
      simp only [e, vertex_mergeDartEquiv, he]) (mergeDartEquiv_reverse h k) hH hc
  have hhk : SameComponent (mergeGraph h k) (e h).vertex (e k).vertex := by
    have he : (e h).vertex = (e k).vertex := by
      simp [e, Function.update_apply]
    rw [he]
    exact .refl (vertex_mem hH (e k))
  constructor
  · intro hc
    have hh := Dart.eq_of_sameComponent (fun d : Dart (mergeGraph h k) =>
      join (key (e.symm d))) (fun d f he => hj (e.symm d) (e.symm f)
        (by simpa only [e.apply_symm_apply] using he)) (fun d => by
          obtain ⟨d, rfl⟩ := e.surjective d
          simpa only [e, ← mergeDartEquiv_reverse, Equiv.symm_apply_apply] using
            congrArg join ((hkey d d.reverse).mpr (sameComponent_reverse hG d))) hc
    change join (key (e.symm (e a))) = join (key (e.symm (e b))) at hh
    simp only [e.symm_apply_apply, join, Function.update_id_apply_eq_iff, hkey] at hh
    rcases hh with hh | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl hh
    · exact Or.inr (Or.inl ⟨ha, hb.symm⟩)
    · exact Or.inr (Or.inr ⟨ha, hb.symm⟩)
  · rintro (hc | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact hmap hc
    · exact (hmap ha).trans (hhk.trans (hmap hb))
    · exact (hmap ha).trans (hhk.symm.trans (hmap hb))

/-- The component of the first merged corner is exactly the union of the two old ones. -/
theorem sameComponent_mergeGraph_left_iff {G : Graph} (h k : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (b : Dart G) :
    SameComponent (mergeGraph h k) (mergeDartEquiv h k h).vertex
      (mergeDartEquiv h k b).vertex ↔
      SameComponent G h.vertex b.vertex ∨ SameComponent G k.vertex b.vertex := by
  rw [sameComponent_mergeGraph_iff_join h k hG]
  constructor
  · rintro (hb | ⟨_, hb⟩ | ⟨_, hb⟩)
    · exact Or.inl hb
    · exact Or.inr hb
    · exact Or.inl hb
  · rintro (hb | hb)
    · exact Or.inl hb
    · exact Or.inr (Or.inl ⟨.refl (vertex_mem hG h), hb⟩)

/-- Components disjoint from both selected corners retain precisely their old darts. -/
theorem sameComponent_mergeGraph_unaffected_iff {G : Graph} (h k : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (a b : Dart G)
    (ha : ¬ SameComponent G a.vertex h.vertex)
    (hb : ¬ SameComponent G a.vertex k.vertex) :
    SameComponent (mergeGraph h k) (mergeDartEquiv h k a).vertex
      (mergeDartEquiv h k b).vertex ↔ SameComponent G a.vertex b.vertex := by
  simp only [sameComponent_mergeGraph_iff_join h k hG, ha, hb, false_and, or_false]

end Cslib.Complexity.Graph.RotationSystem
