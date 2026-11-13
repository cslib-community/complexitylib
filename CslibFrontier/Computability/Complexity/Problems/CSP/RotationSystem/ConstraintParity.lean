/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VertexParity
import CslibFrontier.Computability.Complexity.Problems.CSP.IncidenceEnumeration
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFnGetD

/-!
# Edge-bit sums from actual constraint parity

The ordered typed occurrence scan reads the original edge-label list exactly. If all actual
constraint endpoints have even parity, its whole edge-bit sum is zero. Nullary constraints
contribute an empty scope sum and need no selected occurrence.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- The typed occurrence scan reads the literal edge-bit list in its original order. -/
theorem map_incidenceList_edgeLabels (x : Fin (incidenceGraph F).edges.length → Bool) :
    (CSP.incidenceList F).map (fun o => x (incidenceDart o false).1) = List.ofFn x := by
  calc
    _ = (CSP.incidenceList F).map (fun o => (List.ofFn x).getD (incidenceEdgeIndex o) false) := by
      apply List.map_congr_left
      intro o _
      exact (List.getD_ofFn x (incidenceDart o false).1 false).symm
    _ = (List.range F.occurrences.length).map (fun j => (List.ofFn x).getD j false) := by
      rw [← map_incidenceEdgeIndex_incidenceList, List.map_map]
      rfl
    _ = List.ofFn x := by
      rw [List.map_range_eq_ofFn]
      exact List.ofFn_getD_eq_of_length false (by
        simp only [List.length_ofFn, incidenceGraph_edges, List.length_map])

/-- The actual constraint-endpoint parity is the sum in its original ordered scope. -/
theorem vertexParity_eq_sum_scope
    (x : Fin (incidenceGraph F).edges.length → Bool) (o : F.Occurrence) :
    (incidenceGraph F).vertexParity x (incidenceDart o true).vertex =
      (List.ofFn fun j : Fin F[o.1.val].2.length =>
        x (incidenceDart (⟨o.1, j⟩ : F.Occurrence) true).1).sum := by
  let i := o.1
  let word := List.ofFn fun j : Fin F[i.val].2.length => incidenceDart (⟨i, j⟩ : F.Occurrence) true
  have hn : word.Nodup := List.nodup_ofFn.mpr (by
    intro j k hjk
    have heq : (⟨i, j⟩ : F.Occurrence) = ⟨i, k⟩ := incidenceDart_injective true hjk
    exact eq_of_heq (Sigma.mk.inj heq).2)
  have hw (d : Dart (incidenceGraph F)) : d ∈ word ↔
      d.vertex = (incidenceDart o true).vertex := by
    constructor
    · intro hd
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
      exact (vertex_incidenceDart_eq_iff _ _ true true).mpr ⟨rfl, rfl⟩
    · intro hd
      obtain ⟨p, hp⟩ := exists_incidenceDart d
      have hv := (vertex_incidenceDart_eq_iff p o d.2 true).mp (hp ▸ hd)
      have hrow : p.1 = i := by simpa only [hv.1, ite_true] using hv.2
      rcases p with ⟨k, j⟩
      change k = i at hrow
      subst k
      exact List.mem_ofFn.mpr ⟨j, hv.1 ▸ hp⟩
  rw [(incidenceGraph F).vertexParity_eq_sum_word x _ word hn hw]
  simp only [word, i, List.map_ofFn, Function.comp_def]

/-- Constraint-endpoint evenness implies zero sum in every original ordered scope,
including a nullary scope. No variable-side parity premise is used. -/
theorem sum_scope_eq_false_of_constraintParity
    (x : Fin (incidenceGraph F).edges.length → Bool)
    (hx : ∀ o : F.Occurrence,
      (incidenceGraph F).vertexParity x (incidenceDart o true).vertex = false)
    (i : Fin F.length) :
    (List.ofFn fun j : Fin F[i.val].2.length =>
      x (incidenceDart (⟨i, j⟩ : F.Occurrence) true).1).sum = false := by
  by_cases he : F[i.val].2.length = 0
  · have hn : (List.ofFn fun j : Fin F[i.val].2.length =>
        x (incidenceDart (⟨i, j⟩ : F.Occurrence) true).1) = [] :=
      List.eq_nil_iff_length_eq_zero.mpr (by simpa only [List.length_ofFn] using he)
    simp [hn, Bool.zero_eq_false]
  let o : F.Occurrence := ⟨i, ⟨0, Nat.pos_of_ne_zero he⟩⟩
  have h := hx o
  rw [vertexParity_eq_sum_scope] at h
  exact h

/-- If every actual constraint endpoint has even parity, the sum over every actual edge
is zero. Arbitrary repeated variables and nullary constraints retain their positions. -/
theorem sum_edgeLabels_eq_false_of_constraintParity
    (x : Fin (incidenceGraph F).edges.length → Bool)
    (hx : ∀ o : F.Occurrence,
      (incidenceGraph F).vertexParity x (incidenceDart o true).vertex = false) :
    (List.ofFn x).sum = false := by
  rw [← map_incidenceList_edgeLabels, CSP.incidenceList, List.map_flatten, List.map_ofFn,
    List.sum_flatten, List.map_ofFn]
  have hs (i : Fin F.length) :
      (List.ofFn fun j : Fin F[i.val].2.length =>
        x (incidenceDart (⟨i, j⟩ : F.Occurrence) false).1).sum = false := by
    simpa only [incidenceDart] using sum_scope_eq_false_of_constraintParity x hx i
  simp only [List.map_ofFn, Function.comp_def]
  have he := congrArg (fun f : Fin F.length → Bool => (List.ofFn f).sum) (funext hs)
  exact he.trans (by simp [← Bool.zero_eq_false])

end Cslib.Complexity.CSP
