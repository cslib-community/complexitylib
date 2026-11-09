/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DisjointRotation

/-!
# Numerical genus of a disjoint listed union

Every incident component has exactly its source vertex, edge and complete face counts.
Genus zero follows componentwise from the two source rotations. Empty graphs, closed
components and declared points are allowed, with no target-genus provider.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.SelectedOrbits

/-- Disjoint union preserves source numerical genus zero component by component. -/
theorem numericalGenusZero_disjointUnion {G H : Graph} (r : RotationSystem G)
    (s : RotationSystem H) (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hH : ∀ v ∈ H.incidenceVertices, v ∈ H.1)
    (hr : r.NumericalGenusZero) (hs : s.NumericalGenusZero) :
    (r.disjointUnion s).NumericalGenusZero := by
  classical
  let t := r.disjointUnion s
  let e := disjointDartEquiv G H
  have hT := endpoints_declared_disjointUnion G H hG hH
  apply (t.numericalGenusZero_iff_component_cards hT).mpr
  intro d
  obtain ⟨a, rfl⟩ := e.surjective d
  let q (b : Dart (G.disjointUnion H)) := SameComponent (G.disjointUnion H) (e a).vertex b.vertex
  let p : Dart G ⊕ Dart H → Prop := match a with
    | Sum.inl a => Sum.elim (fun b => SameComponent G a.vertex b.vertex) (fun _ => False)
    | Sum.inr a => Sum.elim (fun _ => False) (fun b => SameComponent H a.vertex b.vertex)
  have hp (b : Dart G ⊕ Dart H) : p b ↔ q (e b) := by
    have he := (sameComponent_disjointUnion_iff hG hH a b).symm
    cases a <;> cases b <;> exact he
  have hcount (f : Perm (Dart G)) (g : Perm (Dart H)) (u : Perm (Dart (G.disjointUnion H)))
      (hm : ∀ b, e (Equiv.sumCongr f g b) = u (e b)) :
      Nat.card (OrbitOn u q) = match a with
        | Sum.inl a => Nat.card (OrbitOn f (fun b => SameComponent G a.vertex b.vertex))
        | Sum.inr a => Nat.card (OrbitOn g (fun b => SameComponent H a.vertex b.vertex)) := by
    rw [← Nat.card_congr (orbitOnEquiv e (Equiv.sumCongr f g) u hm p q hp)]
    cases a with
    | inl a =>
      change Nat.card (OrbitOn (Equiv.sumCongr f g)
        (Sum.elim (fun b => SameComponent G a.vertex b.vertex) (fun _ => False))) = _
      rw [card_orbitOn_sum]
      have hi : IsEmpty (OrbitOn g (fun _ => False)) := ⟨by
        rintro ⟨_, b, hb, _⟩
        exact hb⟩
      let := hi
      simp only [Nat.card_of_isEmpty, Nat.add_zero]
    | inr a =>
      change Nat.card (OrbitOn (Equiv.sumCongr f g)
        (Sum.elim (fun _ => False) (fun b => SameComponent H a.vertex b.vertex))) = _
      rw [card_orbitOn_sum]
      have hi : IsEmpty (OrbitOn f (fun _ => False)) := ⟨by
        rintro ⟨_, b, hb, _⟩
        exact hb⟩
      let := hi
      simp only [Nat.card_of_isEmpty, Nat.zero_add]
  have hv := hcount r.rotate s.rotate t.rotate (fun b =>
    (rotate_disjointUnion r s b).symm)
  have hf := hcount r.faceNext s.faceNext t.faceNext (fun b =>
    (faceNext_disjointUnion r s b).symm)
  have hε := hcount (Dart.reversal G) (Dart.reversal H) (Dart.reversal (G.disjointUnion H))
    (reverse_disjointDartEquiv G H)
  have hV := Nat.card_congr (t.vertexOrbitEquiv hT (e a))
  have hE := Nat.card_congr (edgeOrbitEquiv (G.disjointUnion H) hT (e a))
  simp only [Nat.card_eq_finsetCard] at hV hE
  rw [← hV, ← hE, card_componentFaceIndices,
    t.count_faceRepresentatives_eq_card_componentFace hT]
  change Nat.card (OrbitOn t.rotate q) + Nat.card (OrbitOn t.faceNext q) =
    Nat.card (OrbitOn (Dart.reversal (G.disjointUnion H)) q) + 2
  rw [hv, hf, hε]
  cases a with
  | inl a =>
    have he := (r.numericalGenusZero_iff_component_cards hG).mp hr a
    rw [card_componentFaceIndices, r.count_faceRepresentatives_eq_card_componentFace hG] at he
    have hv := Nat.card_congr (r.vertexOrbitEquiv hG a)
    have hε := Nat.card_congr (edgeOrbitEquiv G hG a)
    simp only [Nat.card_eq_finsetCard] at hv hε
    simpa only [hv, hε] using he
  | inr a =>
    have he := (s.numericalGenusZero_iff_component_cards hH).mp hs a
    rw [card_componentFaceIndices, s.count_faceRepresentatives_eq_card_componentFace hH] at he
    have hv := Nat.card_congr (s.vertexOrbitEquiv hH a)
    have hε := Nat.card_congr (edgeOrbitEquiv H hH a)
    simp only [Nat.card_eq_finsetCard] at hv hε
    simpa only [hv, hε] using he

end Cslib.Complexity.Graph.RotationSystem
