/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.SimpleGraph.Crown

/-!
# Tests: crown decompositions and the vertex cover kernel

Crowns of a star, a triangle and two disjoint edges, decided through Hall's criterion
(`SimpleGraph.isCrown_iff_forall_card_le`); the vertex cover number of a star computed by the
crown reduction rule; the crown lemma applied to a star; and the `2k` bound for the triangle.
-/

namespace ComplexityTests.VertexCoverCrown

open SimpleGraph

/-- The star `K_{1,3}` with centre `0` and leaves `1, 2, 3`. -/
def star : SimpleGraph (Fin 4) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel star.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (u = 0 ∨ v = 0)))

/-- The leaves of a star form a crown with the centre as head. -/
example : star.IsCrown {1, 2, 3} {0} := by decide

/-- The centre alone is not a crown: its three neighbours do not match into one vertex. -/
example : ¬ star.IsCrown {0} {1, 2, 3} := by decide

/-- The head must be the whole neighbourhood. -/
example : ¬ star.IsCrown {1} ∅ := by decide

/-- The crown must be independent. -/
example : ¬ star.IsCrown {0, 1} {0, 1, 2, 3} := by decide

/-- An explicit matching of the centre into the leaves. -/
theorem star_isMatchingInto : star.IsMatchingInto {0} {1, 2, 3} fun _ => 1 :=
  ⟨by decide, by decide, fun a ha b hb _ => by
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    rw [ha, hb]⟩

/-- The Mathlib matching it gives covers the centre and its partner `1`. -/
example : ∃ M : star.Subgraph, M.verts = {0, 1} ∧ M.IsMatching := by
  obtain ⟨M, hM, hMm⟩ := star_isMatchingInto.exists_isMatching (by decide)
  refine ⟨M, ?_, hMm⟩
  rw [hM, Finset.coe_singleton, Set.image_singleton, Set.singleton_union]

/-- The reduction rule computes the vertex cover number of the star: removing the crown
`({1, 2, 3}, {0})` leaves no vertex, so `τ = 0 + |{0}| = 1`. -/
theorem star_vertexCoverNum : star.vertexCoverNum = 1 := by
  have h : star.IsCrown {1, 2, 3} {0} := by decide
  have hall : ∀ v : Fin 4, v ∈ ({1, 2, 3} : Finset (Fin 4)) ∪ {0} := by decide
  have : IsEmpty ↥((↑({1, 2, 3} : Finset (Fin 4)) ∪ ↑({0} : Finset (Fin 4)) : Set (Fin 4))ᶜ) :=
    ⟨fun ⟨v, hv⟩ => hv (by rw [← Finset.coe_union, Finset.mem_coe]; exact hall v)⟩
  rw [h.vertexCoverNum_eq, vertexCoverNum_of_subsingleton, Finset.card_singleton, zero_add,
    Nat.cast_one]

/-- The crown lemma applied to the star with `k = 1`: the star has no isolated vertex and more
than `3` vertices, but no matching of two edges since `τ = 1`, so it has a crown with nonempty
crown and head. -/
example : ∃ C H : Finset (Fin 4), C.Nonempty ∧ H.Nonempty ∧ star.IsCrown C H := by
  have hadj : ∀ v : Fin 4, star.Adj v (if v = 0 then 1 else 0) := by decide
  rcases star.exists_isMatchingInto_or_exists_isCrown_of_forall_exists_adj (k := 1)
      (fun v => ⟨_, hadj v⟩) (by decide) with ⟨A, B, m, hAB, hm, hA⟩ | h
  · have := hm.card_le_vertexCoverNum hAB
    rw [star_vertexCoverNum] at this
    have h1 : A.card ≤ 1 := by exact_mod_cast this
    omega
  · exact h

/-- The triangle has only the empty crown. -/
theorem triangle_isCrown_eq_empty :
    ∀ C H : Finset (Fin 3), (⊤ : SimpleGraph (Fin 3)).IsCrown C H → C = ∅ := by
  decide

/-- The `2k` bound applied to the triangle: every vertex cover has at least two vertices. -/
example {S : Finset (Fin 3)} (hS : (⊤ : SimpleGraph (Fin 3)).IsVertexCover S) : 2 ≤ S.card := by
  have := card_le_two_mul_card_of_forall_isCrown_eq_empty triangle_isCrown_eq_empty hS
  rw [Fintype.card_fin] at this
  omega

/-- Two disjoint edges `0 - 1` and `2 - 3`: `({0}, {1})` is a crown and the residual graph is the
edge `2 - 3`. -/
def twoEdges : SimpleGraph (Fin 4) where
  Adj u v := u ≠ v ∧ u / 2 = v / 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel twoEdges.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ u / 2 = v / 2))

example : twoEdges.IsCrown {0} {1} ∧ twoEdges.IsCrown {0, 2} {1, 3} ∧
    ¬ twoEdges.IsCrown {0, 1} {0, 1} := by
  decide

end ComplexityTests.VertexCoverCrown
