/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Faces
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Certificate

/-!
# Components of the occurrence-indexed polygon graph

Replacing a positive constraint star by its indexed cyclic scope preserves connected components.
All component statements use the existing graph reachability relation on declared vertices.

## Main results

* `Cslib.Complexity.CSP.sameComponent_polygon_iff`: exact reachability correspondence.
* `Cslib.Complexity.CSP.polygonComponentEquiv`: bijection of actual graph components.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph.RotationCertificate

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

private theorem polygon_declared (o : F.Occurrence) :
    F.distinctVars.idxOf o.var ∈ (polygonGraph F).1 := by
  change F.distinctVars.idxOf o.var ∈ List.range F.numVars
  rw [List.mem_range, ← CSP.length_distinctVars]
  exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)

/-- All endpoints in the flattened polygon list are declared dense vertices. -/
theorem polygon_endpoints_declared :
    ∀ v ∈ (polygonGraph F).incidenceVertices, v ∈ (polygonGraph F).1 := by
  intro v hv
  obtain ⟨edge, he, hv⟩ := List.mem_flatMap.mp hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact (polygonGraph_endpoints he).1
  · have h := List.mem_singleton.mp hv
    subst v
    exact (polygonGraph_endpoints he).2

/-- Consecutive scope positions are connected by their actual listed polygon edge,
including when its endpoints coincide. -/
theorem polygon_sameComponent_successor (o : F.Occurrence) :
    SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf (argumentSuccessor o).var) := by
  have h := Graph.RotationSystem.sameComponent_reverse polygon_endpoints_declared
    (polygonDart o false)
  change SameComponent _ (polygonDart o false).vertex (polygonDart o true).vertex at h
  simpa only [vertex_polygonDart, Bool.false_eq_true, ↓reduceIte] using h

/-- All arguments of one constraint lie in the same polygon component. This includes unary
and repeated-variable scopes and does not identify different constraint positions. -/
theorem polygon_sameComponent_constraint (o p : F.Occurrence) (h : o.1 = p.1) :
    SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf p.var) := by
  obtain ⟨n, hn⟩ := ((sameCycle_argumentPermutation o p).mpr h).exists_nat_pow_eq
  have hi (k : ℕ) : SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf ((argumentPermutation F)^[k] o).var) := by
    induction k with
    | zero => exact .refl (polygon_declared o)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (polygon_sameComponent_successor _)
  simpa only [Equiv.Perm.iterate_eq_pow, hn] using hi n

private theorem polygon_sameComponent_incidence_vertex (o p : F.Occurrence) (b c : Bool)
    (h : (incidenceDart o b).vertex = (incidenceDart p c).vertex) :
    SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf p.var) := by
  have ho : F.distinctVars.idxOf o.var < F.numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)
  have hp : F.distinctVars.idxOf p.var < F.numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr p.var_mem)
  rw [vertex_incidenceDart, vertex_incidenceDart] at h
  cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · rw [h]
    exact .refl (polygon_declared p)
  · omega
  · omega
  · apply polygon_sameComponent_constraint
    apply Fin.ext
    omega

private theorem incidence_adj_occurrence {u v : ℕ}
    (h : (incidenceGraph F).toSimpleGraph.Adj u v) :
    ∃ o : F.Occurrence, ∃ b : Bool,
      (incidenceDart o b).vertex = u ∧ (incidenceDart o (!b)).vertex = v := by
  rcases (Graph.toSimpleGraph_adj.mp h).2 with h | h
  · rw [incidenceGraph_edges] at h
    obtain ⟨record, hr, he⟩ := List.mem_map.mp h
    obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hr
    refine ⟨o, false, ?_, ?_⟩
    · exact (vertex_incidenceDart o false).trans (congrArg Prod.fst he)
    · exact (vertex_incidenceDart o true).trans (congrArg Prod.snd he)
  · rw [incidenceGraph_edges] at h
    obtain ⟨record, hr, he⟩ := List.mem_map.mp h
    obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hr
    refine ⟨o, true, ?_, ?_⟩
    · exact (vertex_incidenceDart o true).trans (congrArg Prod.snd he)
    · exact (vertex_incidenceDart o false).trans (congrArg Prod.fst he)

/-- Every incidence path between occurring variables becomes a polygon path. -/
theorem polygon_sameComponent_of_incidence (o p : F.Occurrence)
    (h : SameComponent (incidenceGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf p.var)) :
    SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf p.var) := by
  let P (v : ℕ) : Prop := ∃ q : F.Occurrence, ∃ b : Bool,
    (incidenceDart q b).vertex = v ∧ SameComponent (polygonGraph F)
      (F.distinctVars.idxOf o.var) (F.distinctVars.idxOf q.var)
  have step {u v : {v // v ∈ (incidenceGraph F).1}}
      (hadj : (incidenceGraph F).induced.Adj u v) (hu : P u.val) : P v.val := by
    obtain ⟨q, b, hq, hu⟩ := hu
    obtain ⟨t, c, ht, hv⟩ := incidence_adj_occurrence hadj
    exact ⟨t, !c, hv, hu.trans
      (polygon_sameComponent_incidence_vertex q t b c (hq.trans ht.symm))⟩
  obtain ⟨hu, hv, ⟨w⟩⟩ := h
  have transport {u v : {v // v ∈ (incidenceGraph F).1}}
      (w : (incidenceGraph F).induced.Walk u v) : P u.val → P v.val := by
    induction w with
    | nil => exact id
    | cons hadj w ih => exact fun h => ih (step hadj h)
  obtain ⟨q, b, hq, hconn⟩ := transport w
    ⟨o, false, vertex_incidenceDart o false, .refl (polygon_declared o)⟩
  exact hconn.trans (polygon_sameComponent_incidence_vertex q p b false
    (hq.trans (vertex_incidenceDart p false).symm))

/-- The two variables of a polygon edge are connected through its original constraint star. -/
theorem incidence_sameComponent_polygonEdge (o : F.Occurrence) :
    SameComponent (incidenceGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf (argumentSuccessor o).var) := by
  have h (p : F.Occurrence) : SameComponent (incidenceGraph F)
      (F.distinctVars.idxOf p.var) (F.numVars + p.1) := by
    have h := Graph.RotationSystem.sameComponent_reverse (incidenceVertices_declared F)
      (incidenceDart p false)
    change SameComponent _ (incidenceDart p false).vertex (incidenceDart p true).vertex at h
    simpa only [vertex_incidenceDart, Bool.false_eq_true, ↓reduceIte] using h
  exact (h o).trans (h (argumentSuccessor o)).symm

private theorem polygon_vertex_incidence_declared {v : ℕ} (h : v ∈ (polygonGraph F).1) :
    v ∈ (incidenceGraph F).1 := by
  rw [incidenceGraph_vertices, List.mem_range]
  have hv : v < F.numVars := List.mem_range.mp h
  omega

/-- Every polygon path lifts to an incidence path, using the two original star edges for
each listed polygon edge. -/
theorem incidence_sameComponent_of_polygon {u v : ℕ}
    (h : SameComponent (polygonGraph F) u v) : SameComponent (incidenceGraph F) u v := by
  have step {u v : {v // v ∈ (polygonGraph F).1}}
      (hadj : (polygonGraph F).induced.Adj u v) :
      SameComponent (incidenceGraph F) u.val v.val := by
    rcases (Graph.toSimpleGraph_adj.mp hadj).2 with he | he
    · obtain ⟨record, hr, he⟩ := List.mem_map.mp he
      obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hr
      have hu := congrArg Prod.fst he
      have hv := congrArg Prod.snd he
      change F.distinctVars.idxOf o.var = u.val at hu
      change polygonNext F o.1 o.2 o.var = v.val at hv
      rw [polygonNext_occurrence] at hv
      rw [← hu, ← hv]
      exact incidence_sameComponent_polygonEdge o
    · obtain ⟨record, hr, he⟩ := List.mem_map.mp he
      obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hr
      have hu := congrArg Prod.fst he
      have hv := congrArg Prod.snd he
      change F.distinctVars.idxOf o.var = v.val at hu
      change polygonNext F o.1 o.2 o.var = u.val at hv
      rw [polygonNext_occurrence] at hv
      rw [← hu, ← hv]
      exact (incidence_sameComponent_polygonEdge o).symm
  obtain ⟨hu, hv, ⟨w⟩⟩ := h
  have lift {u v : {v // v ∈ (polygonGraph F).1}}
      (w : (polygonGraph F).induced.Walk u v) :
      SameComponent (incidenceGraph F) u.val v.val := by
    induction w with
    | @nil v => exact .refl (polygon_vertex_incidence_declared v.property)
    | cons hadj w ih => exact (step hadj).trans ih
  exact lift w

/-- Every dense variable vertex has an actual occurrence, even with enormous sparse source
names. No finite universe of source variables is required. -/
theorem exists_occurrence_dense (v : ℕ) (hv : v < F.numVars) :
    ∃ o : F.Occurrence, F.distinctVars.idxOf o.var = v := by
  have hv' : v < F.distinctVars.length := by rwa [CSP.length_distinctVars]
  obtain ⟨o, ho⟩ := CSP.exists_occurrence_iff (F.distinctVars[v]) |>.mpr
    (CSP.mem_distinctVars.mp (List.getElem_mem hv'))
  refine ⟨o, ?_⟩
  rw [ho]
  have hn : F.distinctVars.Nodup := nodup_selectDistinct _ _
  exact hn.idxOf_getElem v hv'

/-- Exact component correspondence on all dense variable vertices. -/
theorem sameComponent_polygon_iff {u v : ℕ} (hu : u < F.numVars) (hv : v < F.numVars) :
    SameComponent (polygonGraph F) u v ↔ SameComponent (incidenceGraph F) u v := by
  constructor
  · exact incidence_sameComponent_of_polygon
  · obtain ⟨o, rfl⟩ := exists_occurrence_dense u hu
    obtain ⟨p, rfl⟩ := exists_occurrence_dense v hv
    exact polygon_sameComponent_of_incidence o p

/-- The inclusion of dense variable vertices induces the actual map of graph components. -/
noncomputable def polygonComponentMap (F : CSP Rel V) :
    (polygonGraph F).induced.ConnectedComponent → (incidenceGraph F).induced.ConnectedComponent :=
  Quot.map (fun v => ⟨v.val, polygon_vertex_incidence_declared v.property⟩)
    (fun u v h => (incidence_sameComponent_of_polygon ⟨u.property, v.property, h⟩).2.2)

/-- Distinct polygon components remain distinct incidence components. -/
theorem polygonComponentMap_injective (F : CSP Rel V) :
    Function.Injective (polygonComponentMap F) := by
  intro x y
  induction x using SimpleGraph.ConnectedComponent.ind with
  | h u =>
    induction y using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      intro h
      apply SimpleGraph.ConnectedComponent.sound
      have h' := SimpleGraph.ConnectedComponent.exact h
      exact ((sameComponent_polygon_iff (F := F) (List.mem_range.mp u.property)
        (List.mem_range.mp v.property)).mpr ⟨_, _, h'⟩).2.2

/-- Positive scopes ensure that no incidence component consists of a deleted nullary
constraint vertex. Thus every incidence component contains a polygon vertex. -/
theorem polygonComponentMap_surjective (F : CSP Rel V)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].2.length) :
    Function.Surjective (polygonComponentMap F) := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    by_cases hv : v.val < F.numVars
    · exact ⟨(polygonGraph F).induced.connectedComponentMk ⟨v.val, List.mem_range.mpr hv⟩, rfl⟩
    · have hb : v.val < F.numVars + F.length := by
        exact List.mem_range.mp (incidenceGraph_vertices F ▸ v.property)
      let i : Fin F.length := ⟨v.val - F.numVars, by omega⟩
      let o : F.Occurrence := ⟨i, ⟨0, hPos i⟩⟩
      refine ⟨(polygonGraph F).induced.connectedComponentMk
        ⟨F.distinctVars.idxOf o.var, polygon_declared o⟩, ?_⟩
      apply SimpleGraph.ConnectedComponent.sound
      have hc := Graph.RotationSystem.sameComponent_reverse (incidenceVertices_declared F)
        (incidenceDart o false)
      have hvo : (incidenceDart o true).vertex = v.val := by
        rw [vertex_incidenceDart]
        dsimp [o, i]
        omega
      change SameComponent _ (incidenceDart o false).vertex (incidenceDart o true).vertex at hc
      rw [vertex_incidenceDart, hvo] at hc
      exact hc.2.2

/-- Exact component bijection for positive scopes, including disconnected and empty bodies. -/
noncomputable def polygonComponentEquiv (F : CSP Rel V)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].2.length) :
    (polygonGraph F).induced.ConnectedComponent ≃ (incidenceGraph F).induced.ConnectedComponent :=
  Equiv.ofBijective (polygonComponentMap F)
    ⟨polygonComponentMap_injective F, polygonComponentMap_surjective F hPos⟩

end Cslib.Complexity.CSP
