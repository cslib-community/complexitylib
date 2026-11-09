/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CornerInsertion
public import CslibFrontier.Foundations.GroupTheory.Perm.CycleSurgery
import Mathlib.Data.List.GetD

/-!
# Deleting the last indexed edge of a rotation

The two ends of the last listed edge are removed from their actual vertex cycles, retaining
the direction of every remaining successor. Vertex declarations are retained, including
endpoints that become isolated points. The face successor is obtained by swapping the two
deleted ends in the old face permutation and then deleting both ends. No connectedness or
genus assertion is part of the constructor.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv Perm.CycleSurgery

/-- The actual graph before deleting its last edge; no corner darts are required at points. -/
@[expose] def lastEdgeGraph (G : Graph) (u v : ℕ) : Graph := (G.1, G.2 ++ [(u, v)])

/-- Old darts and the last two ends, in their original edge/end positions. -/
@[expose] def lastEdgeDartEquiv (G : Graph) (u v : ℕ) :
    Dart (lastEdgeGraph G u v) ≃ Option (Option (Dart G)) :=
  (Equiv.prodCongr
    (finCongr (show (lastEdgeGraph G u v).2.length = G.2.length + 1 by
      simp [lastEdgeGraph])) (Equiv.refl Bool)).trans (appendedDartEquiv G.2.length)

/-- The two indexed ends of the last listed edge, including when the old graph has no darts. -/
@[expose] def lastEdgeDart (G : Graph) (u v : ℕ) (b : Bool) : Dart (lastEdgeGraph G u v) :=
  (lastEdgeDartEquiv G u v).symm (if b then none else some none)

/-- The last two actual endpoints are exactly the supplied names. -/
@[simp] theorem vertex_lastEdgeDart (G : Graph) (u v : ℕ) (b : Bool) :
    (lastEdgeDart G u v b).vertex = if b then v else u := by
  cases b
  · change ((G.2 ++ [(u, v)]).getD G.2.length (0, 0)).1 = u
    simp
  · change ((G.2 ++ [(u, v)]).getD G.2.length (0, 0)).2 = v
    simp

/-- Reversal interchanges the two last indexed ends. -/
theorem reverse_lastEdgeDart (G : Graph) (u v : ℕ) (b : Bool) :
    (lastEdgeDart G u v b).reverse = lastEdgeDart G u v (!b) := by
  cases b <;> rfl

/-- Retain an old dart, without changing its edge-list index or end. -/
@[expose] def retainedLastEdgeDart (G : Graph) (u v : ℕ) (d : Dart G) :
    Dart (lastEdgeGraph G u v) := (lastEdgeDartEquiv G u v).symm (some (some d))

/-- Retained indexed ends keep their original endpoint names. -/
@[simp] theorem vertex_retainedLastEdgeDart (G : Graph) (u v : ℕ) (d : Dart G) :
    (retainedLastEdgeDart G u v d).vertex = d.vertex := by
  rcases d with ⟨⟨i, hi⟩, b⟩
  change (if b then ((G.2 ++ [(u, v)]).getD i (0, 0)).2
    else ((G.2 ++ [(u, v)]).getD i (0, 0)).1) = _
  have he : (G.2 ++ [(u, v)]).getD i (0, 0) = G.2[i] := by
    rw [List.getD_eq_getElem _ _ (show i < (G.2 ++ [(u, v)]).length by
      simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt hi)]
    exact List.getElem_append_left hi
  rw [he]
  change _ = (if b then (G.2.getD i (0, 0)).2 else (G.2.getD i (0, 0)).1)
  rw [List.getD_eq_getElem _ _ hi]

/-- Delete the last two indexed ends from their vertex cycles. The construction works when
either endpoint becomes isolated and when there are no remaining edges. -/
@[expose] def deleteLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) : RotationSystem G where
  rotate := removeNone (removeNone ((lastEdgeDartEquiv G u v).permCongr r.rotate))
  sameCycle_iff a b := by
    rw [sameCycle_removeNone, sameCycle_removeNone]
    have he := Perm.sameCycle_equiv_iff (lastEdgeDartEquiv G u v) r.rotate
      ((lastEdgeDartEquiv G u v).permCongr r.rotate) (fun d => by simp)
      (retainedLastEdgeDart G u v a) (retainedLastEdgeDart G u v b)
    simp only [retainedLastEdgeDart, Equiv.apply_symm_apply] at he
    rw [he, r.sameCycle_iff]
    change (retainedLastEdgeDart G u v a).vertex = (retainedLastEdgeDart G u v b).vertex ↔ _
    rw [vertex_retainedLastEdgeDart, vertex_retainedLastEdgeDart]

/-- Exact reversal in the retained-plus-two-deleted coordinates. -/
theorem lastEdgeDartEquiv_reversal (G : Graph) (u v : ℕ) :
    (lastEdgeDartEquiv G u v).permCongr (Dart.reversal (lastEdgeGraph G u v)) =
      (Dart.reversal G).optionCongr.optionCongr * swap (some none) none := by
  ext z
  rcases z with _ | (_ | ⟨i, b⟩)
  · simp [lastEdgeDartEquiv, appendedDartEquiv, Dart.reverse, Dart.reversal]
  · simp [lastEdgeDartEquiv, appendedDartEquiv, Dart.reverse, Dart.reversal]
  · cases b <;> simp [lastEdgeDartEquiv, appendedDartEquiv, Dart.reverse, i.isLt,
      swap_apply_def, Dart.reversal]

/-- Deletion splices face successors with the original chirality. The preliminary outgoing
swap cancels reversal on the two deleted ends; it is essential even for a loop. -/
theorem faceNext_deleteLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) :
    r.deleteLastEdge.faceNext = removeNone (removeNone
      ((lastEdgeDartEquiv G u v).permCongr r.faceNext * swap (some none) none)) := by
  have hf : r.faceNext = r.rotate⁻¹ * Dart.reversal (lastEdgeGraph G u v) := rfl
  have hi : (lastEdgeDartEquiv G u v).permCongr (r.rotate⁻¹) =
      ((lastEdgeDartEquiv G u v).permCongr r.rotate)⁻¹ :=
    map_inv (lastEdgeDartEquiv G u v).permCongrHom _
  rw [hf, Equiv.permCongr_mul, hi, lastEdgeDartEquiv_reversal]
  rw [mul_assoc, mul_assoc, swap_mul_self, mul_one]
  rw [removeNone_mul_optionCongr, removeNone_mul_optionCongr]
  change _ = (removeNone (removeNone
    (((lastEdgeDartEquiv G u v).permCongr r.rotate).symm))) * Dart.reversal G
  rw [← Equiv.removeNone_symm, ← Equiv.removeNone_symm]
  rfl

/-- Exact accounting for faces lost at endpoints that become isolated. The old vertex
orbit count exceeds the retained one by precisely the number of deleted singleton cycles
in the preliminary face swap. This identity includes deletion of the only edge or loop. -/
theorem card_faces_deleteLastEdge_balance {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) :
    Nat.card r.deleteLastEdge.Face + Nat.card (Quotient (Perm.SameCycle.setoid r.rotate)) =
      Nat.card (Quotient (Perm.SameCycle.setoid
        ((lastEdgeDartEquiv G u v).permCongr r.faceNext * swap (some none) none))) +
          Nat.card (Quotient (Perm.SameCycle.setoid r.deleteLastEdge.rotate)) := by
  let f := ((lastEdgeDartEquiv G u v).permCongr r.rotate)⁻¹
  let a := Dart.reversal G
  have h₁ := card_orbits_removeNone_balance f a.optionCongr
  have h₂ := card_orbits_removeNone_balance (removeNone f) a
  rw [removeNone_mul_optionCongr] at h₁
  have hf : (lastEdgeDartEquiv G u v).permCongr r.faceNext * swap (some none) none =
      f * a.optionCongr.optionCongr := by
    change (lastEdgeDartEquiv G u v).permCongr
      (r.rotate⁻¹ * Dart.reversal (lastEdgeGraph G u v)) * _ = _
    have hi : (lastEdgeDartEquiv G u v).permCongr (r.rotate⁻¹) = f :=
      map_inv (lastEdgeDartEquiv G u v).permCongrHom _
    rw [Equiv.permCongr_mul, hi, lastEdgeDartEquiv_reversal]
    simp only [a, mul_assoc, swap_mul_self, mul_one]
  have hφ : r.deleteLastEdge.faceNext = removeNone (removeNone (f * a.optionCongr.optionCongr)) :=
    r.faceNext_deleteLastEdge.trans (congrArg (fun q => removeNone (removeNone q)) hf)
  have hσ : removeNone (removeNone f) = r.deleteLastEdge.rotate⁻¹ := rfl
  rw [← hf] at h₁
  rw [← removeNone_mul_optionCongr, ← hφ, hσ, card_orbits_inv] at h₂
  have hc : Nat.card (Quotient (Perm.SameCycle.setoid f)) =
      Nat.card (Quotient (Perm.SameCycle.setoid r.rotate)) := by
    dsimp only [f]
    rw [card_orbits_inv, card_orbits_permCongr]
  rw [hc] at h₁
  rw [removeNone_mul_optionCongr] at h₂
  change Nat.card (Quotient (Perm.SameCycle.setoid r.deleteLastEdge.faceNext)) + _ = _
  omega

end Cslib.Complexity.Graph.RotationSystem
