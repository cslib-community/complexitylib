/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ComponentCounts
import Mathlib.Data.Finset.Card

/-!
# Cardinalities of component faces and dense vertex names

These facts connect actual face quotients with the existing least-index representative counts.
They include singleton face orbits and arbitrary declared root names. Dense vertex counts reuse
`Cslib.Complexity.Graph.card_componentVertexSet` rather than a separate list-count proof.

## Main definitions

* `Cslib.Complexity.Graph.RotationSystem.ComponentFace`: faces in one declared component.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.count_faceRepresentatives_eq_card_componentFace`:
  the numerical Euler face count equals the cardinality of actual component faces.
* `Cslib.Complexity.Graph.countP_vertices_range`: component counts for dense vertex names.
-/

public section

namespace Cslib.Complexity.Graph

open RotationCertificate

namespace RotationSystem

/-- Actual face classes with a dart in the declared component of `root`. -/
abbrev ComponentFace {G : Graph} (r : RotationSystem G) (root : ℕ) :=
  {f : r.Face // ∃ d : Dart G, SameComponent G root d.vertex ∧ Quotient.mk _ d = f}

/-- A face represented by a dart belongs precisely to that dart's component. -/
theorem componentFace_mk_iff {G : Graph} (r : Graph.RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (root : ℕ) (d : Graph.Dart G) :
    (∃ e : Graph.Dart G, SameComponent G root e.vertex ∧
      (Quotient.mk _ e : r.Face) = Quotient.mk _ d) ↔ SameComponent G root d.vertex := by
  constructor
  · rintro ⟨e, he, heq⟩
    exact he.trans (r.sameComponent_of_sameFace hG (Quotient.exact heq))
  · exact fun h => ⟨d, h, rfl⟩

/-- Exactly one representative in a component is counted for each actual face. -/
theorem card_componentFaceRepresentatives {G : Graph} (r : Graph.RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (root : ℕ) :
    Nat.card {d : Graph.Dart G // SameComponent G root d.vertex ∧ r.IsFaceRepresentative d} =
      Nat.card (ComponentFace r root) := by
  let f : {d : Graph.Dart G // SameComponent G root d.vertex ∧ r.IsFaceRepresentative d} →
      ComponentFace r root := fun d => ⟨Quotient.mk _ d.val, d.val, d.property.1, rfl⟩
  apply Nat.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro d e h
    apply Subtype.ext
    have hde : r.faceNext.SameCycle d.val e.val := Quotient.exact (congrArg Subtype.val h)
    exact (r.existsUnique_faceRepresentative d.val).unique
      ⟨.rfl, d.property.2⟩ ⟨hde, e.property.2⟩
  · rintro ⟨face, d, hd, rfl⟩
    obtain ⟨e, he, -⟩ := r.existsUnique_faceRepresentative d
    refine ⟨⟨e, hd.trans (r.sameComponent_of_sameFace hG he.1), he.2⟩, ?_⟩
    apply Subtype.ext
    exact Quotient.sound he.1.symm

open Classical in
/-- The numerical face count equals the cardinality of the full component face quotient. -/
theorem count_faceRepresentatives_eq_card_componentFace {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (root : ℕ) :
    ((List.finRange (2 * G.edges.length)).countP fun i =>
      decide (SameComponent G root ((Dart.indexEquiv G).symm i).vertex ∧
        r.IsFaceRepresentative ((Dart.indexEquiv G).symm i))) =
      Nat.card (ComponentFace r root) := by
  classical
  calc
    _ = (r.componentFaceIndices root).card := (r.card_componentFaceIndices root).symm
    _ = Nat.card ↥(r.componentFaceIndices root) := (Nat.card_eq_finsetCard _).symm
    _ = Nat.card {d : Dart G // SameComponent G root d.vertex ∧
        r.IsFaceRepresentative d} :=
      Nat.card_congr ((Dart.indexEquiv G).symm.subtypeEquiv (by
        intro i
        simp [componentFaceIndices]))
    _ = _ := card_componentFaceRepresentatives r hG root

/-- Old face steps preserve each declared component selection. -/
theorem component_faceNext_iff {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (root : ℕ) (d : Dart G) :
    RotationCertificate.SameComponent G root (r.faceNext d).vertex ↔
      RotationCertificate.SameComponent G root d.vertex := by
  have hs := r.sameComponent_faceNext hG d
  exact ⟨fun h => h.trans hs.symm, fun h => h.trans hs⟩

end RotationSystem

open Classical in
/-- Declared dense vertex names can be counted directly as a subtype of `Fin n`. -/
theorem countP_vertices_range (G : Graph) (n : ℕ) (hG : G.vertices = List.range n) (root : ℕ) :
    G.distinctVertices.countP (fun v => decide (SameComponent G root v)) =
      Nat.card {v : Fin n // SameComponent G root v.val} := by
  rw [← card_componentVertexSet, ← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  exact
    { toFun := fun v =>
        ⟨⟨v.val, List.mem_range.mp (hG ▸
          List.mem_toFinset.mp (Finset.mem_filter.mp v.property).1)⟩,
          (Finset.mem_filter.mp v.property).2⟩
      invFun := fun v =>
        ⟨v.val.val, Finset.mem_filter.mpr
          ⟨List.mem_toFinset.mpr (hG ▸ List.mem_range.mpr v.val.isLt), v.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Cslib.Complexity.Graph
