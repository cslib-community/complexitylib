/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.VertexFibers
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Relabel
public import Complexity.Foundations.GroupTheory.Perm.CycleSurgery

/-!
# Identifying two distinct incident vertices at specified corners

The second endpoint name is replaced by the first throughout the actual listed graph.
The successor swap joins precisely the two old vertex cycles. Complete orbit counting
proves the one-cycle-per-vertex contract, including singleton old vertex rotations. Edge
positions and ends are unchanged; this is not a higher-arity constraint reflection.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv Perm.CycleSurgery

/-- Identify the second corner's vertex with the first, retaining all listed edge positions. -/
@[expose] def mergeGraph {G : Graph} (h k : Dart G) : Graph :=
  G.relabel (Function.update id k.vertex h.vertex)

/-- Merging vertex names retains the actual indexed edge/end occurrence. -/
@[expose] def mergeDartEquiv {G : Graph} (h k : Dart G) : Dart G ≃ Dart (mergeGraph h k) :=
  Dart.relabelEquiv G (Function.update id k.vertex h.vertex)

/-- Literal endpoint renaming at each retained indexed end. -/
@[simp] theorem vertex_mergeDartEquiv {G : Graph} (h k d : Dart G) :
    (mergeDartEquiv h k d).vertex = Function.update id k.vertex h.vertex d.vertex :=
  Dart.vertex_relabelEquiv G (Function.update id k.vertex h.vertex) d

private theorem incident_merge_spec {G : Graph} (h k : Dart G) (hk : h.vertex ≠ k.vertex)
    (v : IncidentVertex (mergeGraph h k)) :
    (∃ d : Dart G, d.vertex = v.val) ∧ v.val ≠ k.vertex := by
  obtain ⟨a, ha⟩ := v.property
  obtain ⟨d, rfl⟩ := (mergeDartEquiv h k).surjective a
  rw [vertex_mergeDartEquiv] at ha
  by_cases hd : d.vertex = k.vertex
  · have he : h.vertex = v.val := by simpa only [hd, Function.update_self] using ha
    exact ⟨⟨h, he⟩, he ▸ hk⟩
  · have he : d.vertex = v.val := by simpa only [Function.update_of_ne hd, id_eq] using ha
    exact ⟨⟨d, he⟩, he ▸ hd⟩

/-- The incident vertices after merging are exactly the old incident names except the
removed second name. Declared points do not enter this dart-indexed correspondence. -/
def mergeIncidentEquiv {G : Graph} (h k : Dart G) (hk : h.vertex ≠ k.vertex) :
    {v : IncidentVertex G // v.val ≠ k.vertex} ≃ IncidentVertex (mergeGraph h k) where
  toFun v := ⟨v.val.val, by
    obtain ⟨d, hd⟩ := v.val.property
    refine ⟨mergeDartEquiv h k d, ?_⟩
    rw [vertex_mergeDartEquiv, hd, Function.update_of_ne v.property]
    rfl⟩
  invFun v := ⟨⟨v.val, (incident_merge_spec h k hk v).1⟩, (incident_merge_spec h k hk v).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exactly one nonempty vertex fiber is removed, including when either old fiber was unary. -/
theorem card_incidentVertices_mergeGraph {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h.vertex ≠ k.vertex) :
    Nat.card (IncidentVertex (mergeGraph h k)) + 1 = Nat.card (IncidentVertex G) := by
  let _ : Finite (IncidentVertex G) := Finite.of_surjective
    (r.rotateOrbitEquiv : Quotient (Perm.SameCycle.setoid r.rotate) → IncidentVertex G)
    r.rotateOrbitEquiv.surjective
  let v : IncidentVertex G := ⟨k.vertex, k, rfl⟩
  let e : {x : IncidentVertex G // x ≠ v} ≃ {x : IncidentVertex G // x.val ≠ k.vertex} :=
    Equiv.subtypeEquivRight (fun _ => not_congr Subtype.ext_iff)
  have hc : Nat.card (IncidentVertex G) = Nat.card {x : IncidentVertex G // x ≠ v} + 1 := by
    rw [← Nat.card_congr (Equiv.optionSubtypeNe v), Finite.card_option]
  rw [Nat.card_congr (e.trans (mergeIncidentEquiv h k hk))] at hc
  exact hc.symm

private theorem merge_preserves_vertex {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h.vertex ≠ k.vertex) (d : Dart (mergeGraph h k)) :
    ((mergeDartEquiv h k).permCongr (r.rotate * swap h k) d).vertex = d.vertex := by
  obtain ⟨d, rfl⟩ := (mergeDartEquiv h k).surjective d
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, vertex_mergeDartEquiv,
    Perm.coe_mul, Function.comp_apply, r.vertex_rotate]
  by_cases hd : d = h
  · subst d
    simp [hk]
  · by_cases he : d = k
    · subst d
      simp [hk]
    · rw [swap_apply_of_ne_of_ne hd he]

private theorem merge_orbit_count {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h.vertex ≠ k.vertex) :
    Nat.card (Quotient (Perm.SameCycle.setoid
      ((mergeDartEquiv h k).permCongr (r.rotate * swap h k)))) =
        Nat.card (IncidentVertex (mergeGraph h k)) := by
  rw [card_orbits_permCongr]
  have h₁ := (card_orbits_mul_swap r.rotate h k (fun he => hk (congrArg Dart.vertex he))).2
    (fun he => hk ((r.sameCycle_iff _ _).mp he))
  have h₂ := r.card_incidentVertices_mergeGraph h k hk
  have h₃ := Nat.card_congr r.rotateOrbitEquiv
  omega

/-- Join the two distinct vertex fibers at the specified oriented corners. Its successor is
computed by one outgoing swap, and all orbit/vertex facts are proved from that permutation. -/
@[expose] def mergeVertices {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h.vertex ≠ k.vertex) : RotationSystem (mergeGraph h k) :=
  ofOrbitCount ((mergeDartEquiv h k).permCongr (r.rotate * swap h k))
    (by exact merge_preserves_vertex r h k hk) (by exact merge_orbit_count r h k hk)

/-- Vertex identification preserves the original indexed edge reversal. -/
@[simp] theorem mergeDartEquiv_reverse {G : Graph} (h k d : Dart G) :
    mergeDartEquiv h k d.reverse = (mergeDartEquiv h k d).reverse := rfl

/-- Literal successor permutation of the constructed vertex identification. -/
@[simp] theorem rotate_mergeVertices {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h.vertex ≠ k.vertex) :
    (r.mergeVertices h k hk).rotate = (mergeDartEquiv h k).permCongr (r.rotate * swap h k) := rfl

/-- The first chosen corner continues with the second old forward block. -/
theorem rotate_mergeVertices_left {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h.vertex ≠ k.vertex) :
    (r.mergeVertices h k hk).rotate (mergeDartEquiv h k h) = mergeDartEquiv h k (r.rotate k) := by
  simp

/-- The second chosen corner continues with the first old forward block. -/
theorem rotate_mergeVertices_right {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h.vertex ≠ k.vertex) :
    (r.mergeVertices h k hk).rotate (mergeDartEquiv h k k) = mergeDartEquiv h k (r.rotate h) := by
  simp

/-- Every successor outside the two chosen corners is literally retained. -/
theorem rotate_mergeVertices_other {G : Graph} (r : RotationSystem G) (h k d : Dart G)
    (hk : h.vertex ≠ k.vertex) (hd : d ≠ h) (he : d ≠ k) :
    (r.mergeVertices h k hk).rotate (mergeDartEquiv h k d) = mergeDartEquiv h k (r.rotate d) := by
  simp [swap_apply_of_ne_of_ne hd he]

end Cslib.Complexity.Graph.RotationSystem
