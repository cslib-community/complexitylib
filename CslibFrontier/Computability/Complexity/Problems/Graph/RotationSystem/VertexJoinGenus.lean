/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinComponents
import CslibFrontier.Foundations.GroupTheory.Perm.InvariantPredicate
import CslibFrontier.Foundations.GroupTheory.Perm.SelectedOrbitJoin

/-!
# Joining different components preserves numerical genus zero

The literal `mergeVertices` successor swap joins two different old vertex components.
Its vertex and face orbit counts each decrease by one in their union, and every indexed
edge is retained. The argument counts all permutation orbits, including fixed points.
Declared point components require no darts and retain their conventional Euler equation.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.SelectedOrbits Perm.CycleSurgery

private theorem card_orbitOn_component_union {G : Graph} (h k : Dart G)
    (hc : ¬ SameComponent G h.vertex k.vertex) (f : Perm (Dart G))
    (hf : ∀ a b, f.SameCycle a b → SameComponent G a.vertex b.vertex) :
    Nat.card (OrbitOn f (fun a => SameComponent G h.vertex a.vertex ∨
      SameComponent G k.vertex a.vertex)) =
      Nat.card (OrbitOn f (fun a => SameComponent G h.vertex a.vertex)) +
        Nat.card (OrbitOn f (fun a => SameComponent G k.vertex a.vertex)) := by
  apply card_orbitOn_union
  · intro a
    have he := hf (f a) a (Perm.sameCycle_apply_left.mpr .rfl)
    exact ⟨fun ha => ha.trans he, fun ha => ha.trans he.symm⟩
  · intro t ht hs a ha
    exact hc ((ht a ha).trans (hs a ha).symm)

/-- Different actual edge components cannot share a face orbit. -/
theorem not_sameFace_of_not_sameComponent {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (h k : Dart G)
    (hc : ¬ SameComponent G h.vertex k.vertex) : ¬ r.faceNext.SameCycle h k :=
  fun hf => hc (r.sameComponent_of_sameFace hG hf)

/-- Joining corners in different components preserves the existing componentwise numerical
genus-zero predicate for the actual vertex merge. No target Euler or embedding premise is
required. Unselected closed components and all declared points are retained. -/
theorem numericalGenusZero_mergeVertices_of_not_sameComponent {G : Graph}
    (r : RotationSystem G) (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hr : r.NumericalGenusZero) (h k : Dart G) (hk : h.vertex ≠ k.vertex)
    (hc : ¬ SameComponent G h.vertex k.vertex) :
    (r.mergeVertices h k hk).NumericalGenusZero := by
  classical
  let e := mergeDartEquiv h k
  let s := r.mergeVertices h k hk
  have hH := mergeGraph_endpoints_declared h k hG
  have hrot (a b : Dart G) (he : r.rotate.SameCycle a b) :
      SameComponent G a.vertex b.vertex := by
    rw [(r.sameCycle_iff a b).mp he]
    exact .refl (vertex_mem hG b)
  have hedge (a b : Dart G) (he : (Dart.reversal G).SameCycle a b) :
      SameComponent G a.vertex b.vertex := by
    have he' := (sameCycle_reversal_iff a b).mp he
    rcases a with ⟨i, u⟩
    rcases b with ⟨j, v⟩
    change i = j at he'
    subst j
    cases u <;> cases v
    · exact .refl (vertex_mem hG _)
    · exact sameComponent_reverse hG (i, false)
    · exact sameComponent_reverse hG (i, true)
    · exact .refl (vertex_mem hG _)
  have heuler (a : Dart G) :
      Nat.card (OrbitOn r.rotate (fun b => SameComponent G a.vertex b.vertex)) +
          Nat.card (OrbitOn r.faceNext (fun b => SameComponent G a.vertex b.vertex)) =
        Nat.card (OrbitOn (Dart.reversal G) (fun b =>
          SameComponent G a.vertex b.vertex)) + 2 := by
    have he := (r.numericalGenusZero_iff_component_cards hG).mp hr a
    rw [card_componentFaceIndices, r.count_faceRepresentatives_eq_card_componentFace hG] at he
    have hv := Nat.card_congr (r.vertexOrbitEquiv hG a)
    have hε := Nat.card_congr (edgeOrbitEquiv G hG a)
    simp only [Nat.card_eq_finsetCard] at hv hε
    exact hv ▸ hε ▸ he
  apply (s.numericalGenusZero_iff_component_cards hH).mpr
  intro d
  obtain ⟨a, rfl⟩ := e.surjective d
  let hit := SameComponent G a.vertex h.vertex ∨ SameComponent G a.vertex k.vertex
  let p (b : Dart G) := if hit then
    SameComponent G h.vertex b.vertex ∨ SameComponent G k.vertex b.vertex else
      SameComponent G a.vertex b.vertex
  let q (b : Dart (mergeGraph h k)) := SameComponent (mergeGraph h k) (e a).vertex b.vertex
  have hpmap (b : Dart G) : p b ↔ q (e b) := by
    by_cases hh : hit
    · have hroot : SameComponent (mergeGraph h k) (e a).vertex (e h).vertex := by
        apply (sameComponent_mergeGraph_iff_join h k hG a h).mpr
        rcases hh with hh | hh
        · exact Or.inl hh
        · exact Or.inr (Or.inr ⟨hh, .refl (vertex_mem hG h)⟩)
      have he : SameComponent (mergeGraph h k) (e a).vertex (e b).vertex ↔
          SameComponent (mergeGraph h k) (e h).vertex (e b).vertex :=
        ⟨fun hb => hroot.symm.trans hb, fun hb => hroot.trans hb⟩
      simpa only [p, hh, ite_true, q, he] using
        (sameComponent_mergeGraph_left_iff h k hG b).symm
    · simpa only [p, hh, ite_false, q] using
        (sameComponent_mergeGraph_unaffected_iff h k hG a b
          (fun he => hh (Or.inl he)) (fun he => hh (Or.inr he))).symm
  have hph : p h ↔ hit := by
    by_cases hh : hit
    · simp only [p, hh, ite_true, iff_true]
      exact Or.inl (.refl (vertex_mem hG h))
    · simp only [p, hh, ite_false, iff_false]
      exact fun he => hh (Or.inl he)
  have hpk : p k ↔ hit := by
    by_cases hh : hit
    · simp only [p, hh, ite_true, iff_true]
      exact Or.inr (.refl (vertex_mem hG k))
    · simp only [p, hh, ite_false, iff_false]
      exact fun he => hh (Or.inr he)
  have hp (f : Perm (Dart G))
      (hf : ∀ b, SameComponent G b.vertex (f b).vertex) : ∀ b, p (f b) ↔ p b := by
    intro b
    have ht (v : ℕ) : SameComponent G v (f b).vertex ↔ SameComponent G v b.vertex :=
      ⟨fun he => he.trans (hf b).symm, fun he => he.trans (hf b)⟩
    simp only [p, ht]
  have hpr := hp r.rotate (fun b => by
    rw [r.vertex_rotate]
    exact .refl (vertex_mem hG b))
  have hpf := hp r.faceNext (r.sameComponent_faceNext hG)
  have hsource : Nat.card (OrbitOn r.rotate p) + Nat.card (OrbitOn r.faceNext p) =
      Nat.card (OrbitOn (Dart.reversal G) p) + if hit then 4 else 2 := by
    by_cases hh : hit
    · simp only [p, hh, ite_true]
      rw [card_orbitOn_component_union h k hc r.rotate hrot,
        card_orbitOn_component_union h k hc r.faceNext (fun _ _ he =>
          r.sameComponent_of_sameFace hG he),
        card_orbitOn_component_union h k hc (Dart.reversal G) hedge]
      have h₁ := heuler h
      have h₂ := heuler k
      omega
    · simpa only [p, hh, ite_false] using heuler a
  have hv := card_orbitOn_mul_swap_of_not_sameCycle r.rotate p hpr h k (hph.trans hpk.symm)
    (fun he => hc (hrot h k he))
  have hf := card_orbitOn_swap_mul_of_not_sameCycle r.faceNext p hpf h k (hph.trans hpk.symm)
    (r.not_sameFace_of_not_sameComponent hG h k hc)
  have hvc := Nat.card_congr (orbitOnEquiv e (r.rotate * swap h k) s.rotate
    (fun b => by simp [s, e]) p q hpmap)
  have hfc := Nat.card_congr (orbitOnEquiv e (swap h k * r.faceNext) s.faceNext
    (fun b => (r.faceNext_mergeVertices h k hk b).symm) p q hpmap)
  have hεc := Nat.card_congr (orbitOnEquiv e (Dart.reversal G)
    (Dart.reversal (mergeGraph h k)) (mergeDartEquiv_reverse h k) p q hpmap)
  have hV := Nat.card_congr (s.vertexOrbitEquiv hH (e a))
  have hE := Nat.card_congr (edgeOrbitEquiv (mergeGraph h k) hH (e a))
  simp only [Nat.card_eq_finsetCard] at hV hE
  change Nat.card (OrbitOn s.rotate q) = _ at hV
  change Nat.card (OrbitOn (Dart.reversal (mergeGraph h k)) q) = _ at hE
  change Nat.card (OrbitOn (swap h k * r.faceNext) p) =
    Nat.card (ComponentFace s (e a).vertex) at hfc
  simp only [hph] at hv hf
  rw [card_componentFaceIndices, s.count_faceRepresentatives_eq_card_componentFace hH]
  split_ifs at hsource hv hf <;> omega

end Cslib.Complexity.Graph.RotationSystem
