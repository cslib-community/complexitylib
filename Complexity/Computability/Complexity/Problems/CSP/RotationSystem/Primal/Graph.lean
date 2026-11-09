/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Darts
public import Complexity.Foundations.GroupTheory.Perm.Fin
import Mathlib.Data.List.GetD

/-!
# The occurrence-indexed polygon graph of an ordered CSP

There is one edge per actual argument occurrence, from that variable to the next variable in
the same cyclic scope. The edge list uses the existing incidence occurrence order. Unary scopes
give loops; repeated names and duplicate constraints retain separate edge positions. No relation
arity or bound on the variable universe is used. Nullary constraints contribute no edge.

This is an explicit finite-list construction of the primal face model of [DvorakKupec2015],
printed p. 434. The exact occurrence maps and permutation formulas are original reconstruction.
The graph alone does not establish geometric realizability or a native time bound.

## Main definitions

* `Cslib.Complexity.CSP.polygonGraph`: explicit occurrence-ordered cyclic-scope edges.
* `Cslib.Complexity.CSP.polygonEdgeEquiv`: exact occurrence-to-edge-position map.
* `Cslib.Complexity.CSP.polygonDart`: the two indexed ends of each occurrence edge.

## Main results

* `Cslib.Complexity.CSP.vertex_polygonDart`: exact dense endpoints.
* `Cslib.Complexity.CSP.polygon_scope_word`: original scope order after dense naming.
* `Cslib.Complexity.CSP.length_vertices_polygonGraph_le`: vertices bounded by occurrences.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- Argument succession, with an explicit inverse at each constraint position. -/
@[expose] def argumentPermutation (F : CSP Rel V) : Equiv.Perm F.Occurrence where
  toFun := argumentSuccessor
  invFun o := ⟨o.1, (finRotate _).symm o.2⟩
  left_inv := by
    rintro ⟨i, j⟩
    exact congrArg (fun k : Fin F[i.val].2.length => (⟨i, k⟩ : F.Occurrence))
      ((finRotate _).symm_apply_apply j)
  right_inv := by
    rintro ⟨i, j⟩
    exact congrArg (fun k : Fin F[i.val].2.length => (⟨i, k⟩ : F.Occurrence))
      ((finRotate _).apply_symm_apply j)

/-- The next dense variable, computed from an occurrence record by bounded list lookups.
Invalid records return the supplied variable's dense name; actual occurrences never use it. -/
@[expose] def polygonNext (F : CSP Rel V) (i j : ℕ) (v : V) : ℕ :=
  if hi : i < F.length then
    if hj : j < F[i].2.length then
      F.distinctVars.idxOf (argumentSuccessor (F := F) ⟨⟨i, hi⟩, ⟨j, hj⟩⟩).var
    else F.distinctVars.idxOf v
  else F.distinctVars.idxOf v

/-- Actual ordered occurrences read the next scope variable, with cyclic wraparound. -/
@[simp] theorem polygonNext_occurrence (o : F.Occurrence) :
    polygonNext F o.1 o.2 o.var = F.distinctVars.idxOf (argumentSuccessor o).var := by
  simp [polygonNext]

/-- Dense occurring variables and one listed cyclic-scope edge per occurrence. -/
@[expose] def polygonGraph (F : CSP Rel V) : Graph :=
  (List.range F.numVars, F.occurrences.map fun (i, j, v) =>
    (F.distinctVars.idxOf v, polygonNext F i j v))

/-- The polygon construction keeps exactly the incidence edge positions. -/
@[simp] theorem length_edges_polygonGraph (F : CSP Rel V) :
    (polygonGraph F).2.length = (incidenceGraph F).2.length := by
  simp [polygonGraph, incidenceGraph_edges]

/-- Every argument occurrence retains its own listed polygon edge. -/
@[expose] def polygonDart (o : F.Occurrence) (side : Bool) : Graph.Dart (polygonGraph F) :=
  (⟨incidenceEdgeIndex o, by rw [length_edges_polygonGraph]; exact incidenceEdgeIndex_lt o⟩,
    side)

/-- The listed edge at an occurrence has its two prescribed dense endpoints. -/
theorem getElem_polygonEdge (o : F.Occurrence) :
    (polygonGraph F).2[incidenceEdgeIndex o]'((polygonDart o false).1.isLt) =
      (F.distinctVars.idxOf o.var, F.distinctVars.idxOf (argumentSuccessor o).var) := by
  simp only [polygonGraph, List.getElem_map, incidenceEdgeIndex]
  rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩))]
  exact congrArg (Prod.mk (F.distinctVars.idxOf o.var)) (polygonNext_occurrence o)

/-- Both endpoint choices retain the cyclic scope order, even when the edge is a loop. -/
@[simp] theorem vertex_polygonDart (o : F.Occurrence) (side : Bool) :
    (polygonDart o side).vertex =
      if side then F.distinctVars.idxOf (argumentSuccessor o).var
      else F.distinctVars.idxOf o.var := by
  change (if side then ((polygonGraph F).2.getD (incidenceEdgeIndex o) (0, 0)).2
    else ((polygonGraph F).2.getD (incidenceEdgeIndex o) (0, 0)).1) = _
  rw [List.getD_eq_getElem _ _ (by
    rw [length_edges_polygonGraph]; exact incidenceEdgeIndex_lt o)]
  exact congrArg (fun edge : ℕ × ℕ => if side then edge.2 else edge.1)
    (getElem_polygonEdge o)

/-- No two occurrence/end pairs are collapsed by equal endpoint labels. -/
theorem polygonDart_injective :
    Function.Injective (fun x : F.Occurrence × Bool => polygonDart x.1 x.2) := by
  rintro ⟨o, b⟩ ⟨p, c⟩ h
  exact Prod.ext (incidenceEdgeIndex_injective (congrArg (fun d => d.1.val) h))
    (congrArg (fun d : Graph.Dart (polygonGraph F) => d.2) h)

/-- Every polygon dart has an occurrence and an end; no additional darts are introduced. -/
theorem exists_polygonDart (d : Graph.Dart (polygonGraph F)) :
    ∃ o : F.Occurrence, polygonDart o d.2 = d := by
  obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := F) d.1 (by
    rw [← length_edges_polygonGraph]; exact d.1.isLt)
  exact ⟨o, Prod.ext (Fin.ext ho) rfl⟩

/-- Occurrence/end coordinates on the actual listed polygon graph. The inverse only recovers
indices from the existing occurrence enumeration; it chooses no graph or rotation. -/
@[expose] noncomputable def polygonDartEquiv (F : CSP Rel V) :
    F.Occurrence × Bool ≃ Graph.Dart (polygonGraph F) :=
  Equiv.ofBijective (fun x => polygonDart x.1 x.2)
    ⟨polygonDart_injective, fun d => by
      obtain ⟨o, ho⟩ := exists_polygonDart d
      exact ⟨(o, d.2), ho⟩⟩

/-- The exact edge-position map: one edge for each actual argument occurrence. -/
@[expose] noncomputable def polygonEdgeEquiv (F : CSP Rel V) :
    F.Occurrence ≃ Fin (polygonGraph F).2.length :=
  Equiv.ofBijective (fun o => (polygonDart o false).1) ⟨by
    intro o p h
    exact incidenceEdgeIndex_injective (congrArg Fin.val h), fun i => by
    obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := F) i.val (by
      rw [← length_edges_polygonGraph]; exact i.isLt)
    exact ⟨o, Fin.ext ho⟩⟩

/-- Edge count is exactly the number of ordered occurrences, rather than distinct pairs. -/
theorem length_edges_polygonGraph_eq_card (F : CSP Rel V) :
    (polygonGraph F).2.length = Fintype.card F.Occurrence := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (polygonEdgeEquiv F)).symm

/-- The forward polygon coordinate map is the explicit occurrence/end map. -/
@[simp] theorem polygonDartEquiv_apply (x : F.Occurrence × Bool) :
    polygonDartEquiv F x = polygonDart x.1 x.2 := rfl

omit [DecidableEq V] in
/-- The scope permutation has exactly one orbit per nonempty constraint position. -/
theorem sameCycle_argumentPermutation (o p : F.Occurrence) :
    (argumentPermutation F).SameCycle o p ↔ o.1 = p.1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hi (k : ℕ) : ((argumentPermutation F)^[k] o).1 = o.1 := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact ih
    simpa only [Equiv.Perm.iterate_eq_pow, hn] using (hi n).symm
  · rcases o with ⟨i, j⟩
    rcases p with ⟨k, l⟩
    intro h
    change i = k at h
    subst k
    obtain ⟨n, hn⟩ := (Equiv.Perm.sameCycle_finRotate j l).exists_nat_pow_eq
    have hi (k : ℕ) : (argumentPermutation F)^[k] ⟨i, j⟩ =
        ⟨i, (finRotate _)^[k] j⟩ := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        rfl
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, ← Equiv.Perm.iterate_eq_pow, hi, Equiv.Perm.iterate_eq_pow, hn]

/-- Both ends of every polygon edge are declared dense occurring variables. -/
theorem polygonGraph_endpoints {edge : ℕ × ℕ} (he : edge ∈ (polygonGraph F).2) :
    edge.1 ∈ (polygonGraph F).1 ∧ edge.2 ∈ (polygonGraph F).1 := by
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp he
  obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hrecord
  simp only [CSP.Occurrence.record, polygonNext_occurrence, polygonGraph, List.mem_range]
  constructor
  · rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)
  · rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem
      (CSP.mem_distinctVars.mpr (argumentSuccessor o).var_mem)

/-- Dense vertex count is bounded by actual scope occurrences, independent of label sizes. -/
theorem length_vertices_polygonGraph_le (F : CSP Rel V) :
    (polygonGraph F).1.length ≤ (polygonGraph F).2.length := by
  have h := F.vars.toFinset_card_le
  simpa only [polygonGraph, List.length_range, List.length_map, CSP.length_occurrences,
    CSP.numVars, CSP.vars, List.length_flatMap] using h

/-- The forward-dart word at a constraint is its exact original scope after dense naming. -/
theorem polygon_scope_word (i : Fin F.length) :
    (List.ofFn fun j : Fin F[i.val].2.length => (polygonDart (⟨i, j⟩ : F.Occurrence)
      false).vertex) = F[i.val].2.map (F.distinctVars.idxOf ·) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp [CSP.Occurrence.var]

/-- With positive actual scopes, constraint positions are also bounded by occurrences. -/
theorem length_constraints_le_polygon_edges
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].2.length) :
    F.length ≤ (polygonGraph F).2.length := by
  have h := CSP.length_le_length_vars (F := F) (fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    exact hPos ⟨i, hi⟩)
  simpa only [polygonGraph, List.length_map, CSP.length_occurrences,
    CSP.vars, List.length_flatMap] using h

end Cslib.Complexity.CSP
