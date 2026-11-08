/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.DartInsertion
import Complexity.Foundations.GroupTheory.Perm.Doubled
import Mathlib.Data.List.GetD

/-!
# Indexed edge insertion at two dart corners

A new edge is appended to the actual listed graph. Its two ends are inserted immediately
after the two specified old darts. Corners may coincide, and their vertices may coincide:
loops and repeated boundary visits do not identify dart occurrences. The result proves the
full vertex-fiber rotation contract and gives literal successor equations. Numerical genus
requires an additional face-location argument; arbitrary corner insertion need not preserve it.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv
open DartInsertion

/-- Append a structural edge between the vertices of two chosen dart corners. -/
@[expose] def cornerGraph {G : Graph} (h k : Dart G) : Graph :=
  (G.1, G.2 ++ [(h.vertex, k.vertex)])

/-- Appending an edge adds exactly two indexed ends to the old dart type. -/
@[expose] def appendedDartEquiv (n : ℕ) :
    Fin (n + 1) × Bool ≃ Option (Option (Fin n × Bool)) where
  toFun d := if hi : d.1.val < n then some (some (⟨d.1.val, hi⟩, d.2))
    else if d.2 then none else some none
  invFun d := match d with
    | none => (Fin.last n, true)
    | some none => (Fin.last n, false)
    | some (some (i, b)) => (i.castSucc, b)
  left_inv := by
    rintro ⟨⟨i, hi⟩, b⟩
    by_cases h : i < n
    · simp only [h, dite_true]
      rfl
    · have he : i = n := by omega
      subst i
      cases b <;> simp [Fin.last]
  right_inv := by
    rintro (_ | _ | ⟨i, b⟩)
    · simp
    · simp
    · simp [i.isLt]

/-- Target edge/end positions are the old darts plus two distinct new ends. -/
@[expose] def cornerDartEquiv {G : Graph} (h k : Dart G) :
    Dart (cornerGraph h k) ≃ Option (Option (Dart G)) :=
  (Equiv.prodCongr
    (finCongr (show (cornerGraph h k).2.length = G.2.length + 1 by simp [cornerGraph]))
    (Equiv.refl Bool)).trans
    (appendedDartEquiv G.2.length)

/-- The old edge/end occurrence in the appended graph. -/
@[expose] def oldCornerDart {G : Graph} (h k d : Dart G) : Dart (cornerGraph h k) :=
  (cornerDartEquiv h k).symm (some (some d))

/-- The first (`false`) and second (`true`) ends of the appended edge. -/
@[expose] def newCornerDart {G : Graph} (h k : Dart G) (b : Bool) :
    Dart (cornerGraph h k) :=
  (cornerDartEquiv h k).symm (if b then none else some none)

/-- Old vertices are unchanged by appending the edge. -/
@[simp] theorem vertex_oldCornerDart {G : Graph} (h k d : Dart G) :
    (oldCornerDart h k d).vertex = d.vertex := by
  rcases d with ⟨⟨i, hi⟩, b⟩
  change (if b then ((G.2 ++ [(h.vertex, k.vertex)]).getD i (0, 0)).2
    else ((G.2 ++ [(h.vertex, k.vertex)]).getD i (0, 0)).1) = _
  have he : (G.2 ++ [(h.vertex, k.vertex)]).getD i (0, 0) = G.2[i] := by
    have hlen : i < (G.2 ++ [(h.vertex, k.vertex)]).length := by
      simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt hi
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_append_left hi
  rw [he]
  change _ = (if b then (G.2.getD i (0, 0)).2 else (G.2.getD i (0, 0)).1)
  rw [List.getD_eq_getElem _ _ hi]

/-- The inserted ends have exactly their selected corner vertices. -/
@[simp] theorem vertex_newCornerDart {G : Graph} (h k : Dart G) (b : Bool) :
    (newCornerDart h k b).vertex = if b then k.vertex else h.vertex := by
  cases b
  · change ((G.2 ++ [(h.vertex, k.vertex)]).getD G.2.length (0, 0)).1 = h.vertex
    simp
  · change ((G.2 ++ [(h.vertex, k.vertex)]).getD G.2.length (0, 0)).2 = k.vertex
    simp

private theorem vertex_cornerDartEquiv {G : Graph} (h k : Dart G)
    (d : Dart (cornerGraph h k)) :
    d.vertex = (collapse h (collapse (some k) (cornerDartEquiv h k d))).vertex := by
  obtain ⟨d, rfl⟩ := (cornerDartEquiv h k).symm.surjective d
  rcases d with _ | _ | d
  · simpa only [Equiv.apply_symm_apply, collapse, Option.elim'_none,
        Option.elim'_some, id_eq, newCornerDart, Bool.false_eq_true, ↓reduceIte] using
      vertex_newCornerDart h k true
  · simpa only [Equiv.apply_symm_apply, collapse, Option.elim'_none,
        Option.elim'_some, id_eq, newCornerDart, Bool.false_eq_true, ↓reduceIte] using
      vertex_newCornerDart h k false
  · simpa only [Equiv.apply_symm_apply, collapse, Option.elim'_some, id_eq,
        oldCornerDart] using vertex_oldCornerDart h k d

/-- Insert both new edge ends at the specified old corners. If `h=k`, their cyclic order
is `h, new true, new false, old successor`; the ends of a loop remain distinct. -/
@[expose] def insertEdge {G : Graph} (r : RotationSystem G) (h k : Dart G) :
    RotationSystem (cornerGraph h k) where
  rotate := (cornerDartEquiv h k).symm.permCongr
    (insertAfter (insertAfter r.rotate h) (some k))
  sameCycle_iff d e := by
    have he := Perm.sameCycle_equiv_iff (cornerDartEquiv h k).symm
      (insertAfter (insertAfter r.rotate h) (some k))
      ((cornerDartEquiv h k).symm.permCongr
        (insertAfter (insertAfter r.rotate h) (some k)))
      (by intro a; simp) (cornerDartEquiv h k d) (cornerDartEquiv h k e)
    simp only [Equiv.symm_apply_apply] at he
    rw [he, DartInsertion.sameCycle_iff, DartInsertion.sameCycle_iff, r.sameCycle_iff]
    exact Iff.of_eq (congrArg₂ Eq (vertex_cornerDartEquiv h k d).symm
      (vertex_cornerDartEquiv h k e).symm)

/-- The second new end is followed by the first insertion's old successor at `k`. -/
theorem rotate_insertEdge_new_true {G : Graph} (r : RotationSystem G) (h k : Dart G) :
    (cornerDartEquiv h k) ((r.insertEdge h k).rotate (newCornerDart h k true)) =
      some (insertAfter r.rotate h (some k)) := by
  simp [insertEdge, newCornerDart]

/-- When the corners differ, the first selected corner leads to the first new end. -/
theorem rotate_insertEdge_at_left {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h ≠ k) :
    (r.insertEdge h k).rotate (oldCornerDart h k h) = newCornerDart h k false := by
  apply (cornerDartEquiv h k).injective
  simp [insertEdge, oldCornerDart, newCornerDart, insertAfter_other _ _ _
    (show some h ≠ some k from fun he => hk (Option.some.inj he))]

/-- The second selected corner always leads to the second new end. -/
theorem rotate_insertEdge_at_right {G : Graph} (r : RotationSystem G) (h k : Dart G) :
    (r.insertEdge h k).rotate (oldCornerDart h k k) = newCornerDart h k true := by
  apply (cornerDartEquiv h k).injective
  simp [insertEdge, oldCornerDart, newCornerDart]

end Cslib.Complexity.Graph.RotationSystem
