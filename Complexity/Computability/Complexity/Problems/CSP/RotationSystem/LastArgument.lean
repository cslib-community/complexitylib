/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Equality
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionTransport
import Complexity.Logics.Propositional.CSP.Occurrence.AppendLast
import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionGenus
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.ArgumentIndices
import Mathlib.Data.List.GetD

/-!
# Removing the last argument of the last indexed constraint

The source and target are the actual CSP lists, with every earlier argument and constraint
position retained. The temporary graph is exactly the source incidence edge prefix, using
the source's dense names. Its explicit dart map to the actual target graph preserves the
endpoint-fiber partition even if the removed variable ceases to occur. Declared nullaries
and points require no fabricated darts. These are original positional transport facts for
boundary projection. Native cyclic-successor formulas retain the inherited directed order.
The complete computed-table acceptance theorem is in
`CSP.OrderedBoundary.verifyRotationCertificate_restrictPrefix_lastArgument`.

## Main definitions

* `Cslib.Complexity.CSP.deleteLastArgumentRotation`: explicit target incidence rotation.

## Main results

* `Cslib.Complexity.CSP.numericalGenusZero_deleteLastArgumentRotation`: target numerical genus.
* `Cslib.Complexity.CSP.argumentNextIndex_append_last_argument`: exact native successor change.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph Graph.RotationSystem Equiv

variable {Rel V : Type} [DecidableEq V]

omit [DecidableEq V] in
/-- The actual argument-position table gains precisely the last argument's indexed pair. -/
theorem argumentPositions_append_last_argument (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) :
    argumentPositions (F ++ [(r, scope ++ [v])]) =
      argumentPositions (F ++ [(r, scope)]) ++ [(F.length, scope.length)] := by
  simp only [argumentPositions, CSP.occurrences_append_last_argument, List.map_append,
    List.map_singleton]

omit [DecidableEq V] in
/-- Only the last constraint's scope length changes, including a nullary target scope.
Missing constraint indices still read zero on both actual input lists. -/
theorem scopeLength_append_last_argument (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) (i : ℕ) :
    scopeLength (F ++ [(r, scope ++ [v])]) i =
      scopeLength (F ++ [(r, scope)]) i + if i = F.length then 1 else 0 := by
  unfold scopeLength
  simp only [List.map_append, List.map_singleton, List.length_append, List.length_singleton]
  by_cases hi : i < F.length
  · rw [List.getD_append _ _ _ _ (by simpa only [List.length_map] using hi),
      List.getD_append _ _ _ _ (by simpa only [List.length_map] using hi)]
    rw [ite_eq_right (by omega)]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simpa only [List.length_map] using Nat.le_of_not_gt hi),
      List.getD_append_right _ _ _ _ (by simpa only [List.length_map] using Nat.le_of_not_gt hi)]
    simp only [List.length_map]
    by_cases he : i = F.length
    · subst i
      simp
    · have hs : 0 < i - F.length := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
      rw [hk]
      simp [he]

omit [DecidableEq V] in
/-- The last declared constraint has its literal supplied scope length, including zero. -/
theorem scopeLength_last_constraint (F : CSP Rel V) (r : Rel) (scope : List V) :
    scopeLength (F ++ [(r, scope)]) F.length = scope.length := by
  unfold scopeLength
  rw [List.map_append, List.map_singleton, List.getD_append_right _ _ _ _ (by simp)]
  simp

omit [DecidableEq V] in
/-- The only old argument whose native successor changes is the former last argument of
the last constraint. It now leads to the single appended occurrence. -/
theorem argumentNextIndex_append_last_argument (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) (o : (F ++ [(r, scope)]).Occurrence) :
    argumentNextIndex (F ++ [(r, scope ++ [v])]) o.1 o.2 =
      if o.1.val = F.length ∧ o.2.val + 1 = scope.length then
        (F ++ [(r, scope)]).occurrences.length
      else argumentNextIndex (F ++ [(r, scope)]) o.1 o.2 := by
  by_cases hlast : o.1.val = F.length ∧ o.2.val + 1 = scope.length
  · rw [ite_eq_left hlast]
    let i : ℕ := o.1.val
    let j : ℕ := o.2.val
    change argumentNextIndex (F ++ [(r, scope ++ [v])]) i j = _
    have hi : i = F.length := hlast.1
    have hj : j + 1 = scope.length := hlast.2
    have hnot : (F.length, scope.length) ∉ argumentPositions (F ++ [(r, scope)]) := by
      have h := argumentPositions_nodup (F ++ [(r, scope ++ [v])])
      rw [argumentPositions_append_last_argument] at h
      intro hm
      exact (List.nodup_append.mp h).2.2 _ hm _ (by simp) rfl
    unfold argumentNextIndex
    rw [hi, scopeLength_last_constraint]
    simp only [List.length_append, List.length_singleton]
    rw [ite_eq_left (by omega), hj, argumentPositions_append_last_argument,
      List.idxOf_append_of_notMem hnot]
    simp [argumentPositions]
  · rw [ite_eq_right hlast]
    have hn : o.1.val ≠ F.length ∨
        o.2.val + 1 < scopeLength (F ++ [(r, scope)]) o.1 := by
      by_cases hi : o.1.val = F.length
      · right
        have hj : o.2.val < scopeLength (F ++ [(r, scope)]) o.1 := by
          rw [scopeLength_occurrence]
          exact o.2.isLt
        have hlen : scopeLength (F ++ [(r, scope)]) o.1 = scope.length := by
          simpa only [hi] using scopeLength_last_constraint F r scope
        have he : o.2.val + 1 ≠ scope.length := fun he => hlast ⟨hi, he⟩
        omega
      · exact Or.inl hi
    have hq := argumentNextPosition_mem o
    unfold argumentNextIndex
    rw [argumentPositions_append_last_argument, scopeLength_append_last_argument]
    rcases hn with hi | hj
    · rw [ite_eq_right hi]
      simp only [Nat.add_zero]
      exact List.idxOf_append_of_mem hq
    · have hcmp : o.2.val + 1 < scopeLength (F ++ [(r, scope)]) o.1 +
          (if o.1.val = F.length then 1 else 0) := by split_ifs <;> omega
      rw [ite_eq_left hcmp, ite_eq_left hj]
      exact List.idxOf_append_of_mem (by simpa only [ite_eq_left hj] using hq)

omit [DecidableEq V] in
/-- The appended argument wraps to the same first argument as the former last argument.
The actual old occurrence hypothesis covers precisely the nonempty target scope case. -/
theorem argumentNextIndex_append_last_argument_wrap (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) (o : (F ++ [(r, scope)]).Occurrence)
    (hi : o.1.val = F.length) (hj : o.2.val + 1 = scope.length) :
    argumentNextIndex (F ++ [(r, scope ++ [v])]) F.length scope.length =
      argumentNextIndex (F ++ [(r, scope)]) o.1 o.2 := by
  let i : ℕ := o.1.val
  let j : ℕ := o.2.val
  change argumentNextIndex (F ++ [(r, scope ++ [v])]) F.length scope.length =
    argumentNextIndex (F ++ [(r, scope)]) i j
  change i = F.length at hi
  change j + 1 = scope.length at hj
  have hq := argumentNextPosition_mem o
  change (i, if j + 1 < scopeLength (F ++ [(r, scope)]) i then j + 1 else 0) ∈
    argumentPositions (F ++ [(r, scope)]) at hq
  have hlen := scopeLength_last_constraint F r scope
  rw [hi, hlen] at hq
  have hq0 : (F.length, 0) ∈ argumentPositions (F ++ [(r, scope)]) := by
    simpa only [hj, Nat.lt_irrefl, ite_false] using hq
  unfold argumentNextIndex
  rw [hi, scopeLength_last_constraint, scopeLength_last_constraint]
  simp only [List.length_append, List.length_singleton]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), argumentPositions_append_last_argument]
  exact List.idxOf_append_of_mem hq0

/-- The actual source incidence prefix before its last argument edge. Its declarations
and dense endpoint names are still those of the source, including a now isolated variable. -/
@[expose] def lastArgumentPrefixGraph (F : CSP Rel V) (r : Rel) (scope : List V) (v : V) : Graph :=
  ((incidenceGraph (F ++ [(r, scope ++ [v])])).1,
    (F ++ [(r, scope)]).occurrences.map fun (constraint, (_argument, varName)) =>
      ((F ++ [(r, scope ++ [v])]).distinctVars.idxOf varName,
        (F ++ [(r, scope ++ [v])]).numVars + constraint))

/-- Source incidence is literally this prefix followed by the selected final edge. -/
theorem incidenceGraph_append_last_argument (F : CSP Rel V) (r : Rel) (scope : List V) (v : V) :
    incidenceGraph (F ++ [(r, scope ++ [v])]) =
      lastEdgeGraph (lastArgumentPrefixGraph F r scope v)
        ((F ++ [(r, scope ++ [v])]).distinctVars.idxOf v)
        ((F ++ [(r, scope ++ [v])]).numVars + F.length) := by
  apply Prod.ext
  · rfl
  · rw [incidenceGraph_edges, CSP.occurrences_append_last_argument]
    simp [lastEdgeGraph, lastArgumentPrefixGraph]

/-- Retained prefix ends and target incidence ends have the same edge/end positions. -/
@[expose] def lastArgumentDartEquiv (F : CSP Rel V) (r : Rel) (scope : List V) (v : V) :
    Dart (lastArgumentPrefixGraph F r scope v) ≃ Dart (incidenceGraph (F ++ [(r, scope)])) :=
  (finCongr (by simp [lastArgumentPrefixGraph, incidenceGraph_edges])).prodCongr (Equiv.refl Bool)

/-- Literal source-dense endpoint read on an actual retained target argument occurrence. -/
theorem vertex_lastArgumentDartEquiv_symm (F : CSP Rel V) (r : Rel) (scope : List V) (v : V)
    (o : (F ++ [(r, scope)]).Occurrence) (side : Bool) :
    ((lastArgumentDartEquiv F r scope v).symm (incidenceDart o side)).vertex =
      if side then (F ++ [(r, scope ++ [v])]).numVars + o.1
      else (F ++ [(r, scope ++ [v])]).distinctVars.idxOf o.var := by
  let S := F ++ [(r, scope ++ [v])]
  let T := F ++ [(r, scope)]
  have hidx : T.occurrences.idxOf o.record < T.occurrences.length :=
    List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩)
  have hi : incidenceEdgeIndex o < T.occurrences.length := hidx
  have he : (lastArgumentPrefixGraph F r scope v).2.getD (incidenceEdgeIndex o) (0, 0) =
      (S.distinctVars.idxOf o.var, S.numVars + o.1) := by
    change (T.occurrences.map fun a => (S.distinctVars.idxOf a.2.2, S.numVars + a.1)).getD
      (incidenceEdgeIndex o) (0, 0) = _
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
    change (S.distinctVars.idxOf (T.occurrences[T.occurrences.idxOf o.record]'hidx).2.2,
      S.numVars + (T.occurrences[T.occurrences.idxOf o.record]'hidx).1) = _
    rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩))]
    rfl
  change (if side then ((lastArgumentPrefixGraph F r scope v).2.getD
    (incidenceEdgeIndex o) (0, 0)).2 else ((lastArgumentPrefixGraph F r scope v).2.getD
      (incidenceEdgeIndex o) (0, 0)).1) = _
  rw [he]

/-- The retained actual occurrences have exactly the same vertex fibers in the source
prefix and target graph. This allows repeated labels and disappearing unused variables. -/
theorem vertex_lastArgumentDartEquiv_symm_eq_iff (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) (o p : (F ++ [(r, scope)]).Occurrence) (side other : Bool) :
    ((lastArgumentDartEquiv F r scope v).symm (incidenceDart o side)).vertex =
        ((lastArgumentDartEquiv F r scope v).symm (incidenceDart p other)).vertex ↔
      (incidenceDart o side).vertex = (incidenceDart p other).vertex := by
  let S := F ++ [(r, scope ++ [v])]
  let T := F ++ [(r, scope)]
  have hvars : S.vars = T.vars ++ [v] := by
    simp [S, T, CSP.vars, List.flatMap_append, List.append_assoc]
  have hm (a : T.Occurrence) : a.var ∈ S.distinctVars := by
    apply CSP.mem_distinctVars.mpr
    rw [hvars]
    exact List.mem_append_left _ a.var_mem
  have hS (a : T.Occurrence) : S.distinctVars.idxOf a.var < S.numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (hm a)
  have hT (a : T.Occurrence) : T.distinctVars.idxOf a.var < T.numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr a.var_mem)
  rw [vertex_lastArgumentDartEquiv_symm, vertex_lastArgumentDartEquiv_symm,
    vertex_incidenceDart, vertex_incidenceDart]
  cases side <;> cases other
  · change S.distinctVars.idxOf o.var = S.distinctVars.idxOf p.var ↔
      T.distinctVars.idxOf o.var = T.distinctVars.idxOf p.var
    rw [List.idxOf_inj (hm o), List.idxOf_inj (CSP.mem_distinctVars.mpr o.var_mem)]
  · have hs := hS o
    have ht := hT o
    change S.distinctVars.idxOf o.var = S.numVars + p.1.val ↔
      T.distinctVars.idxOf o.var = T.numVars + p.1.val
    omega
  · have hs := hS p
    have ht := hT p
    change S.numVars + o.1.val = S.distinctVars.idxOf p.var ↔
      T.numVars + o.1.val = T.distinctVars.idxOf p.var
    omega
  · change S.numVars + o.1.val = S.numVars + p.1.val ↔
      T.numVars + o.1.val = T.numVars + p.1.val
    omega

/-- The positional dart equivalence has the exact endpoint-fiber contract required by
generic rotation transport. No injection on old variable labels is assumed. -/
theorem lastArgumentDartEquiv_vertex_eq_iff (F : CSP Rel V) (r : Rel) (scope : List V) (v : V)
    (a b : Dart (lastArgumentPrefixGraph F r scope v)) :
    (lastArgumentDartEquiv F r scope v a).vertex =
        (lastArgumentDartEquiv F r scope v b).vertex ↔ a.vertex = b.vertex := by
  let e := lastArgumentDartEquiv F r scope v
  obtain ⟨a, rfl⟩ := e.symm.surjective a
  obtain ⟨b, rfl⟩ := e.symm.surjective b
  obtain ⟨o, ho⟩ := exists_incidenceDart a
  obtain ⟨p, hp⟩ := exists_incidenceDart b
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← ho, ← hp]
  exact (vertex_lastArgumentDartEquiv_symm_eq_iff F r scope v o p a.2 b.2).symm

/-- Reversal is preserved literally by the retained edge/end map. -/
theorem lastArgumentDartEquiv_reverse (F : CSP Rel V) (r : Rel) (scope : List V) (v : V)
    (a : Dart (lastArgumentPrefixGraph F r scope v)) :
    lastArgumentDartEquiv F r scope v a.reverse =
      (lastArgumentDartEquiv F r scope v a).reverse := rfl

/-- Reinterpret the actual source incidence graph as its retained prefix and last edge.
The dart equivalence is literal on edge indices and end tags. -/
@[expose] def lastArgumentSourceRotation (F : CSP Rel V) (r : Rel) (scope : List V) (v : V)
    (ρ : RotationSystem (incidenceGraph (F ++ [(r, scope ++ [v])]))) :
    RotationSystem (lastEdgeGraph (lastArgumentPrefixGraph F r scope v)
      ((F ++ [(r, scope ++ [v])]).distinctVars.idxOf v)
      ((F ++ [(r, scope ++ [v])]).numVars + F.length)) :=
  ρ.transport (graphEqDartEquiv (incidenceGraph_append_last_argument F r scope v))
    (by intro a b; rw [vertex_graphEqDartEquiv, vertex_graphEqDartEquiv])

/-- Delete the final argument on the original CSP lists. The two explicit transports
retain all old edge/end positions while accounting for changed dense vertex names. -/
@[expose] def deleteLastArgumentRotation (F : CSP Rel V) (r : Rel) (scope : List V) (v : V)
    (ρ : RotationSystem (incidenceGraph (F ++ [(r, scope ++ [v])]))) :
    RotationSystem (incidenceGraph (F ++ [(r, scope)])) :=
  ((lastArgumentSourceRotation F r scope v ρ).deleteLastEdge
    (G := lastArgumentPrefixGraph F r scope v)
    (u := (F ++ [(r, scope ++ [v])]).distinctVars.idxOf v)
    (v := (F ++ [(r, scope ++ [v])]).numVars + F.length)).transport
    (lastArgumentDartEquiv F r scope v) (by exact lastArgumentDartEquiv_vertex_eq_iff F r scope v)

/-- The actual retained incidence prefix declares all of its edge endpoints. -/
theorem lastArgumentPrefixGraph_endpoints_declared (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) :
    ∀ w ∈ (lastArgumentPrefixGraph F r scope v).incidenceVertices,
      w ∈ (lastArgumentPrefixGraph F r scope v).1 := by
  apply endpoints_declared_deleteLastEdge (u := (F ++ [(r, scope ++ [v])]).distinctVars.idxOf v)
    (v := (F ++ [(r, scope ++ [v])]).numVars + F.length)
  rw [← incidenceGraph_append_last_argument]
  exact incidenceVertices_declared (F ++ [(r, scope ++ [v])])

/-- Source numerical genus is retained by its literal prefix-plus-last-edge view. -/
theorem numericalGenusZero_lastArgumentSourceRotation (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V)
    (ρ : RotationSystem (incidenceGraph (F ++ [(r, scope ++ [v])])))
    (hρ : ρ.NumericalGenusZero) :
    (lastArgumentSourceRotation F r scope v ρ).NumericalGenusZero := by
  exact (ρ.numericalGenusZero_graphEqDartEquiv
    (incidenceGraph_append_last_argument F r scope v)).mpr hρ

/-- Last-argument deletion has actual target numerical genus zero, internally supplied
by general edge deletion and positional incidence transport. The source rotation may have
repeated variable labels, repeated constraints, arbitrary other components and nullaries. -/
theorem numericalGenusZero_deleteLastArgumentRotation (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V)
    (ρ : RotationSystem (incidenceGraph (F ++ [(r, scope ++ [v])])))
    (hρ : ρ.NumericalGenusZero) :
    (deleteLastArgumentRotation F r scope v ρ).NumericalGenusZero := by
  exact numericalGenusZero_deleteLastEdge_transport
    (S := incidenceGraph (F ++ [(r, scope ++ [v])]))
    (T := incidenceGraph (F ++ [(r, scope)]))
    (G := lastArgumentPrefixGraph F r scope v)
    (u := (F ++ [(r, scope ++ [v])]).distinctVars.idxOf v)
    (v := (F ++ [(r, scope ++ [v])]).numVars + F.length)
    ρ (incidenceGraph_append_last_argument F r scope v)
    (lastArgumentDartEquiv F r scope v) (lastArgumentDartEquiv_vertex_eq_iff F r scope v)
    (lastArgumentDartEquiv_reverse F r scope v)
    (incidenceVertices_declared (F ++ [(r, scope ++ [v])]))
    (incidenceVertices_declared (F ++ [(r, scope)])) hρ

end Cslib.Complexity.CSP
