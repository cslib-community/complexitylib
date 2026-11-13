/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Labeling
import Mathlib.Data.List.GetD

/-!
# Comparison labelings for every actual matching

A comparison witness chooses the incident matching edge at a covered vertex and the private
unmatched port otherwise. Classical selection here is confined to the mathematical comparison
with arbitrary Mathlib subgraphs. The executable endpoints use only the certified optimizer.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL CSP
open Cslib.BitString

variable {G : Graph}

/-- An incident selected subgraph edge certifies that its endpoint belongs to the subgraph. -/
theorem mem_verts_of_incident_positions {M : G.induced.Subgraph} {v i : ℕ} (hv : v ∈ G.vertices)
    (hi : i ∈ positions M) (hinc : incident (G.edgeList.getD i (0, 0)) v = true) :
    (⟨v, hv⟩ : {v // v ∈ G.vertices}) ∈ M.verts := by
  obtain ⟨_, hu, hw, hadj⟩ := mem_positions.mp hi
  obtain ⟨w, he⟩ := exists_other_end hinc
  rcases he with he | he <;> simp only [he] at hu hw hadj
  · exact M.edge_vert hadj
  · exact M.edge_vert hadj.symm

/-- A Mathlib matching contains at most one incident edge position per vertex. -/
theorem positions_unique {M : G.induced.Subgraph} (hM : M.IsMatching) (v : ℕ) (hv : v ∈ G.vertices)
    (i : ℕ) (hi : i ∈ positions M) (j : ℕ) (hj : j ∈ positions M)
    (hinc : incident (G.edgeList.getD i (0, 0)) v = true)
    (hinc' : incident (G.edgeList.getD j (0, 0)) v = true) : i = j := by
  obtain ⟨k, _, hk⟩ := cover_positions hM v hv (mem_verts_of_incident_positions hv hi hinc)
  exact (hk i ⟨(mem_positions.mp hi).1, hinc, hi⟩).trans
    (hk j ⟨(mem_positions.mp hj).1, hinc', hj⟩).symm

/-- A proof-only comparison port: an incident position of `S`, or the private port at zero. -/
noncomputable def comparisonPort (G : Graph) (S : Finset ℕ) (v : ℕ) : ℕ :=
  open Classical in
  if h : ∃ i ∈ S, i < G.edgeList.length ∧ incident (G.edgeList.getD i (0, 0)) v = true then
    (G.matchingScope v).idxOf (2 * h.choose)
  else 0

/-- Every comparison port belongs to the nonempty actual choice scope. -/
theorem comparisonPort_lt (G : Graph) (S : Finset ℕ) (v : ℕ) :
    G.comparisonPort S v < (G.matchingScope v).length := by
  classical
  unfold comparisonPort
  split
  next h =>
    exact List.idxOf_lt_length_iff.mpr
      ((G.mem_matchingScope_even v h.choose).mpr h.choose_spec.2)
  next => simp [matchingScope]

/-- At an actual matching edge, uniqueness forces the comparison to choose that edge. -/
theorem comparisonPort_eq {M : G.induced.Subgraph} (hM : M.IsMatching) (v : ℕ) (hv : v ∈ G.vertices)
    (i : ℕ) (hi : i ∈ positions M)
    (hinc : incident (G.edgeList.getD i (0, 0)) v = true) :
    G.comparisonPort (positions M) v = (G.matchingScope v).idxOf (2 * i) := by
  classical
  have hex : ∃ j ∈ positions M, j < G.edgeList.length ∧
      incident (G.edgeList.getD j (0, 0)) v = true := ⟨i, hi, (mem_positions.mp hi).1, hinc⟩
  have he : hex.choose = i := positions_unique hM v hv hex.choose hex.choose_spec.1 i hi
    hex.choose_spec.2.2 hinc
  simp only [comparisonPort, dite_eq_left hex, he]

/-- A feasible proof-only labeling, choosing exactly one port per vertex and false at pins. -/
noncomputable def comparisonLabeling (G : Graph) (S : Finset ℕ) :
    OccurrenceLabeling G.matchingInstance Bool := fun o =>
  if o.1.val < G.distinctVertices.length then
    decide (o.2.val = G.comparisonPort S (G.distinctVertices.getD o.1.val 0))
  else false

/-- Every comparison labeling is feasible, independently of consistency or cardinality. -/
theorem comparisonLabeling_valid (G : Graph) (S : Finset ℕ) :
    ValidLabeling Table.sem (G.comparisonLabeling S) := by
  intro i
  change G.matchingInstance[i.val].rel.sem (localTuple (G.comparisonLabeling S) i) = true
  by_cases hi : i.val < G.distinctVertices.length
  · have ht : G.matchingInstance[i.val].rel =
        Table.exactlyOne (G.matchingScope G.distinctVertices[i.val]) := by
      simp [matchingInstance, hi]
    have hs : G.matchingInstance[i.val].scope = G.matchingScope G.distinctVertices[i.val] := by
      simp [matchingInstance, hi]
    have hr : localTuple (G.comparisonLabeling S) i =
        listSingle (G.matchingScope G.distinctVertices[i.val]).length
          (G.comparisonPort S G.distinctVertices[i.val]) := by
      apply List.ext_getElem
      · simp [localTuple, hs, listSingle]
      · intro j hj hk
        simp [localTuple, comparisonLabeling, hi, listSingle, hs, eq_comm]
    rw [ht, hr, Table.sem_eq_true]
    exact ⟨Table.wellFormed_exactlyOne _, List.mem_map.mpr
      ⟨_, List.mem_range.mpr (comparisonPort_lt G S _), rfl⟩⟩
  · have ht : G.matchingInstance[i.val].rel = Table.pinTable false := by
      simp [matchingInstance, Nat.le_of_not_gt hi]
    have hs : G.matchingInstance[i.val].scope.length = 1 := by
      simp [matchingInstance, Nat.le_of_not_gt hi]
    have hr : localTuple (G.comparisonLabeling S) i = [false] := by
      apply List.ext_getElem
      · simp [localTuple, hs]
      · intro j hj hk
        have : j = 0 := by
          have : j < 1 := by simpa only [List.length_singleton] using hk
          omega
        subst j
        simp [localTuple, comparisonLabeling, hi]
    rw [ht, hr, Table.sem_eq_true]
    simp [Table.pinTable]

/-- The comparison for a matching selects each of its original graph edges at both endpoints. -/
theorem positions_subset_comparison {M : G.induced.Subgraph} (hM : M.IsMatching) :
    positions M ⊆ G.positionsOfLabeling (G.comparisonLabeling (positions M)) := by
  intro i hi
  refine (mem_positionsOfLabeling _ i).mpr ⟨(mem_positions.mp hi).1, ?_⟩
  refine mem_selectedVariables.mpr ⟨(mem_vars_matchingInstance G).mpr
    (Or.inl ⟨i, (mem_positions.mp hi).1, rfl⟩), ?_⟩
  intro o ho
  have hv : o.var ∈ G.matchingInstance[o.1.val].scope := List.getElem_mem o.2.isLt
  by_cases hc : o.1.val < G.distinctVertices.length
  · let v := G.distinctVertices.getD o.1.val 0
    have hvm : v ∈ G.vertices := mem_distinctVertices.mp (by
      change G.distinctVertices.getD o.1.val 0 ∈ G.distinctVertices
      rw [List.getD_eq_getElem _ _ hc]
      exact List.getElem_mem hc)
    have hs : G.matchingInstance[o.1.val].scope = G.matchingScope v := by
      simp [matchingInstance, hc, v]
    have hx : 2 * i ∈ G.matchingScope v := hs ▸ ho ▸ hv
    have hinc := (mem_matchingScope_even G v i).mp hx |>.2
    have he := comparisonPort_eq hM v hvm i hi hinc
    have hget : (G.matchingScope v)[o.2.val]'(hs ▸ o.2.isLt) = 2 * i := by
      simpa only [Occurrence.var, hs] using ho
    have hidx : o.2.val = (G.matchingScope v).idxOf (2 * i) := by
      rw [← hget, (nodup_matchingScope G v).idxOf_getElem]
    change (if o.1.val < G.distinctVertices.length then
      decide (o.2.val = G.comparisonPort (positions M) v) else false) = true
    simp only [hc, ↓reduceIte, he, hidx, decide_true]
  · have hs : G.matchingInstance[o.1.val].scope =
        [2 * G.distinctVertices[o.1.val - G.distinctVertices.length]'(by
          have := o.1.isLt
          simp only [matchingInstance, List.length_append, List.length_map] at this
          omega) + 1] := by
      simp [matchingInstance, Nat.le_of_not_gt hc]
    rw [hs, ho, List.mem_singleton] at hv
    omega

end Cslib.Complexity.Graph
