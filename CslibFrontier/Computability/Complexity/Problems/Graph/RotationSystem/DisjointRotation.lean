/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DisjointGraph
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Transport
public import CslibFrontier.Foundations.GroupTheory.Perm.SelectedOrbitJoin

/-!
# Rotations and actual components of disjoint listed graphs

The successor is the disjoint sum of the two original rotations in exact edge/end
coordinates. Its components are precisely the original components in their tagged blocks.
All declared points, loops and parallel indexed edges are retained.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.SelectedOrbits

/-- The disjoint sum of source rotations, retaining both original directed cycles. -/
@[expose] def disjointUnion {G H : Graph} (r : RotationSystem G) (s : RotationSystem H) :
    RotationSystem (G.disjointUnion H) where
  rotate := (disjointDartEquiv G H).permCongr (Equiv.sumCongr r.rotate s.rotate)
  sameCycle_iff a b := by
    let e := disjointDartEquiv G H
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    change (e.permCongr (Equiv.sumCongr r.rotate s.rotate)).SameCycle (e a) (e b) ↔ _
    rw [Perm.sameCycle_equiv_iff e (Equiv.sumCongr r.rotate s.rotate) _ (fun d => by
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply])]
    let eq := Perm.sumOrbitEquiv r.rotate s.rotate
    have hq : Perm.SameCycle (Equiv.sumCongr r.rotate s.rotate) a b ↔
        eq (Quotient.mk _ a) = eq (Quotient.mk _ b) :=
      ⟨fun he => congrArg eq (Quotient.sound he), fun he => Quotient.exact (eq.injective he)⟩
    rw [hq]
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change Sum.inl (Quotient.mk _ a : Quotient (Perm.SameCycle.setoid r.rotate)) =
          Sum.inl (Quotient.mk _ b) ↔ _
        rw [Sum.inl.injEq, Quotient.eq_iff_equiv]
        change r.rotate.SameCycle a b ↔ _
        rw [r.sameCycle_iff]
        simp only [e, vertex_disjointDartEquiv_inl]
        omega
      | inr b =>
        change Sum.inl (Quotient.mk _ a : Quotient (Perm.SameCycle.setoid r.rotate)) =
          Sum.inr (Quotient.mk _ b) ↔ _
        simp only [e, vertex_disjointDartEquiv_inl, vertex_disjointDartEquiv_inr]
        simp only [Sum.inl_ne_inr, false_iff]
        omega
    | inr a =>
      cases b with
      | inl b =>
        change Sum.inr (Quotient.mk _ a : Quotient (Perm.SameCycle.setoid s.rotate)) =
          Sum.inl (Quotient.mk _ b) ↔ _
        simp only [e, vertex_disjointDartEquiv_inr, vertex_disjointDartEquiv_inl]
        simp only [Sum.inr_ne_inl, false_iff]
        omega
      | inr b =>
        change Sum.inr (Quotient.mk _ a : Quotient (Perm.SameCycle.setoid s.rotate)) =
          Sum.inr (Quotient.mk _ b) ↔ _
        rw [Sum.inr.injEq, Quotient.eq_iff_equiv]
        change s.rotate.SameCycle a b ↔ _
        rw [s.sameCycle_iff]
        simp only [e, vertex_disjointDartEquiv_inr]
        omega

/-- Exact forward successors in disjoint edge/end coordinates. -/
theorem rotate_disjointUnion {G H : Graph} (r : RotationSystem G) (s : RotationSystem H)
    (d : Dart G ⊕ Dart H) :
    (r.disjointUnion s).rotate (disjointDartEquiv G H d) =
      disjointDartEquiv G H (Sum.map r.rotate s.rotate d) := by
  simp only [disjointUnion, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply]

/-- The corresponding inverse-rotation face successor has the same source-block chirality. -/
theorem faceNext_disjointUnion {G H : Graph} (r : RotationSystem G) (s : RotationSystem H)
    (d : Dart G ⊕ Dart H) :
    (r.disjointUnion s).faceNext (disjointDartEquiv G H d) =
      disjointDartEquiv G H (Sum.map r.faceNext s.faceNext d) := by
  apply (r.disjointUnion s).rotate.injective
  change (r.disjointUnion s).rotate
    ((r.disjointUnion s).rotate.symm (disjointDartEquiv G H d).reverse) = _
  rw [Equiv.apply_symm_apply, rotate_disjointUnion]
  cases d with
  | inl d =>
    change _ = disjointDartEquiv G H (Sum.inl (r.rotate (r.rotate.symm d.reverse)))
    rw [Equiv.apply_symm_apply]
    rfl
  | inr d =>
    change _ = disjointDartEquiv G H (Sum.inr (s.rotate (s.rotate.symm d.reverse)))
    rw [Equiv.apply_symm_apply]
    rfl

/-- Two actual disjoint-union darts are connected exactly when they come from the same
block and were connected in that source graph. Point components are not represented as darts. -/
theorem sameComponent_disjointUnion_iff {G H : Graph}
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hH : ∀ v ∈ H.incidenceVertices, v ∈ H.1) (a b : Dart G ⊕ Dart H) :
    SameComponent (G.disjointUnion H) (disjointDartEquiv G H a).vertex
      (disjointDartEquiv G H b).vertex ↔
      match a, b with
      | Sum.inl a, Sum.inl b => SameComponent G a.vertex b.vertex
      | Sum.inr a, Sum.inr b => SameComponent H a.vertex b.vertex
      | _, _ => False := by
  let e := disjointDartEquiv G H
  have hT := endpoints_declared_disjointUnion G H hG hH
  let keyG (d : Dart G) := G.induced.connectedComponentMk ⟨d.vertex, vertex_mem hG d⟩
  let keyH (d : Dart H) := H.induced.connectedComponentMk ⟨d.vertex, vertex_mem hH d⟩
  let key := Sum.map keyG keyH
  have hv (d f : Dart G ⊕ Dart H) (he : (e d).vertex = (e f).vertex) : key d = key f := by
    cases d with
    | inl d =>
      cases f with
      | inl f =>
        simp only [e, vertex_disjointDartEquiv_inl] at he
        exact congrArg Sum.inl (congrArg G.induced.connectedComponentMk
          (Subtype.ext (by omega : d.vertex = f.vertex)))
      | inr f =>
        simp only [e, vertex_disjointDartEquiv_inl, vertex_disjointDartEquiv_inr] at he
        omega
    | inr d =>
      cases f with
      | inl f =>
        simp only [e, vertex_disjointDartEquiv_inr, vertex_disjointDartEquiv_inl] at he
        omega
      | inr f =>
        simp only [e, vertex_disjointDartEquiv_inr] at he
        exact congrArg Sum.inr (congrArg H.induced.connectedComponentMk
          (Subtype.ext (by omega : d.vertex = f.vertex)))
  constructor
  · intro hc
    have hh := Dart.eq_of_sameComponent (fun d => key (e.symm d))
      (fun d f he => hv (e.symm d) (e.symm f)
        (by simpa only [e.apply_symm_apply] using he)) (fun d => by
          obtain ⟨d, rfl⟩ := e.surjective d
          rw [← reverse_disjointDartEquiv, e.symm_apply_apply, e.symm_apply_apply]
          cases d with
          | inl d =>
            exact congrArg Sum.inl
              (SimpleGraph.ConnectedComponent.sound (sameComponent_reverse hG d).2.2)
          | inr d =>
            exact congrArg Sum.inr
              (SimpleGraph.ConnectedComponent.sound (sameComponent_reverse hH d).2.2)) hc
    change key (e.symm (e a)) = key (e.symm (e b)) at hh
    simp only [e.symm_apply_apply] at hh
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        exact ⟨vertex_mem hG a, vertex_mem hG b,
          SimpleGraph.ConnectedComponent.exact (Sum.inl.inj hh)⟩
      | inr b => cases hh
    | inr a =>
      cases b with
      | inl b => cases hh
      | inr b =>
        exact ⟨vertex_mem hH a, vertex_mem hH b,
          SimpleGraph.ConnectedComponent.exact (Sum.inr.inj hh)⟩
  · cases a with
    | inl a =>
      cases b with
      | inl b =>
        intro hc
        exact sameComponent_map_darts (fun d => e (Sum.inl d))
          (fun d f he => by simp only [e, vertex_disjointDartEquiv_inl, he])
          (fun _ => rfl) hT hc
      | inr b => exact False.elim
    | inr a =>
      cases b with
      | inl b => exact False.elim
      | inr b =>
        intro hc
        exact sameComponent_map_darts (fun d => e (Sum.inr d))
          (fun d f he => by simp only [e, vertex_disjointDartEquiv_inr, he])
          (fun _ => rfl) hT hc

end Cslib.Complexity.Graph.RotationSystem
