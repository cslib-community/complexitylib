/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingFits
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingRoutes
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingCounts
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesPrefix
import Complexity.Logics.Propositional.CNF.Occurrence
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Linarith

/-!
# Constant-factor costs of the actual positive drawing compiler

Costs are counted on the actual emitted route lists. The source-slot sequence of every fixed
profile contains each source occurrence once. Consequently inherited exteriors are charged
once, while every original clause receives only a fixed local route, segment and wire budget.

## Main results

* `clauseGeometry_local_costs`: fixed segment and wire budgets for the actual local replacements.
* `positiveDrawing_costs`: constant-factor actual vertex, route, segment and wire bounds.

## References

The exact finite-list accounting and cost estimates are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

private def sourceSlot (p : ClauseProfile) (e : LocalIncidence) : Option ℕ :=
  match (profileVariables p).getD e.2.1 (.inl (.inl 0)) with
  | .inl (.inl j) => some j
  | _ => none

private theorem prefix_sourceSlots (p : ClauseProfile) :
    ((profilePrefixGeometry p).incidenceRoutes.filterMap (sourceSlot p)) =
      (profileSource p).zipIdx.map Prod.snd := by
  fin_cases p <;> decide +kernel

private theorem prefix_routes_grouped (p : ClauseProfile) :
    (profileFormula p).zipIdx.flatMap (fun a =>
      (profilePrefixGeometry p).incidenceRoutes.filter fun e => e.1 == a.2) =
        (profilePrefixGeometry p).incidenceRoutes := by
  fin_cases p <;> decide +kernel

private theorem clause_sourceSlots (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) :
    ((clauseGeometry φ d i c).incidenceRoutes.filterMap (sourceSlot (clauseProfile c))) =
      (profileSource (clauseProfile c)).zipIdx.map Prod.snd := by
  simp only [clauseGeometry, collaredPrefixGeometry, List.filterMap_map]
  change ((profilePrefixGeometry (clauseProfile c)).incidenceRoutes.filterMap
    (sourceSlot (clauseProfile c))) = _
  exact prefix_sourceSlots (clauseProfile c)

private theorem clause_routes_grouped (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) :
    (profileFormula (clauseProfile c)).zipIdx.flatMap (fun a =>
      (clauseGeometry φ d i c).incidenceRoutes.filter fun e => e.1 == a.2) =
        (clauseGeometry φ d i c).incidenceRoutes := by
  let g := profilePrefixGeometry (clauseProfile c)
  let s := clausePorts φ d i
  let f (e : LocalIncidence) : LocalIncidence :=
    (e.1, e.2.1, if e.2.1 ∈ g.terminalVariables then
      collarPrefixRoute s (terminalIndex g e.2.1) e.2.2
      else collarRoute (collarReflected s) e.2.2)
  simpa only [clauseGeometry, collaredPrefixGeometry, List.map_flatMap, List.filter_map,
    Function.comp_def] using congrArg (List.map f) (prefix_routes_grouped (clauseProfile c))

private theorem sum_option_weights {A : Type*} (xs : List A) (slot : A → Option ℕ)
    (f : ℕ → ℕ) :
    (xs.map fun a => (slot a).elim 0 f).sum = ((xs.filterMap slot).map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : slot a <;> simp [h, ih]

private theorem clause_source_weight (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) (hw : c.length ≤ 3) (f : ℕ → ℕ) :
    ((clauseGeometry φ d i c).incidenceRoutes.map fun e =>
      (sourceSlot (clauseProfile c) e).elim 0 f).sum =
        (c.zipIdx.map fun a => f a.2).sum := by
  rw [sum_option_weights, clause_sourceSlots]
  have he : (profileSource (clauseProfile c)).zipIdx.map Prod.snd = c.zipIdx.map Prod.snd := by
    simp only [List.zipIdx_map_snd, profileSource_length c hw]
  rw [he, List.map_map]
  rfl

private theorem positiveDrawing_weight (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (weight : Route → ℕ) :
    (((positiveDrawing φ d).2).map weight).sum =
      (φ.zipIdx.map fun a => ((clauseGeometry φ d a.2 a.1).incidenceRoutes.map fun e =>
        weight (positiveIncidenceRoute φ d a.2 a.1 e)).sum).sum := by
  have hlocal (c : Clause ℕ) (i : ℕ) :
      (((positiveClauseBlock φ d i c).flatMap fun a => a.2.2).map weight).sum =
        ((clauseGeometry φ d i c).incidenceRoutes.map fun e =>
          weight (positiveIncidenceRoute φ d i c e)).sum := by
    have he := congrArg (fun es => (es.map fun e =>
      weight (positiveIncidenceRoute φ d i c e)).sum) (clause_routes_grouped φ d i c)
    simpa only [positiveClauseBlock, List.flatMap_map, List.map_flatMap, List.map_map,
      Function.comp_def] using he
  change (((positivePlacedClauses φ d).flatMap fun c => c.2.2).map weight).sum = _
  rw [positivePlacedClauses, List.flatMap_assoc, List.map_flatMap]
  rw [List.flatMap_def, List.sum_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  exact hlocal a.1 a.2

private theorem segmentCount_eq (r : Route) : r.consecutivePairs.length = r.length - 1 := by
  simp only [List.consecutivePairs, List.length_zip, List.length_tail]
  omega

/-- The actual collared local template has bounded total segment and Manhattan-wire costs.
The conservative collar allowance is charged once per local incidence. -/
theorem clauseGeometry_local_costs {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (c : Clause ℕ) :
    (((clauseGeometry φ d i c).incidenceRoutes.map fun e => e.2.2.consecutivePairs.length).sum ≤
      575) ∧
      (((clauseGeometry φ d i c).incidenceRoutes.map fun e => wireLength e.2.2).sum ≤
        40252600) := by
  let p := clauseProfile c
  let g := profilePrefixGeometry p
  let s := clausePorts φ d i
  have hs := (clausePorts_spec hd hi).1
  have hg := profilePrefixGeometry_check p
  have hmeta := profilePrefixGeometry_costs p
  have hseg (e : LocalIncidence) (he : e ∈ g.incidenceRoutes) :
      (profileCollarRoute p s e).consecutivePairs.length ≤ e.2.2.consecutivePairs.length + 7 := by
    unfold profileCollarRoute
    split_ifs with ht
    · have hend := (LocalGeometry.prefix_incidence_endpoints hg he).2.2.2
      rw [profile_prefix_terminal_endpoint p e.2.1 ht] at hend
      rw [consecutivePairs_length_collarPrefixRoute hs hend]
      exact Nat.add_le_add_left ((collar_route_costs s hs _).1) _
    · rw [consecutivePairs_length_collarRoute]
      omega
  have hwire (e : LocalIncidence) (he : e ∈ g.incidenceRoutes) :
      wireLength (profileCollarRoute p s e) ≤ wireLength e.2.2 + 600000 := by
    unfold profileCollarRoute
    split_ifs with ht
    · have hend := (LocalGeometry.prefix_incidence_endpoints hg he).2.2.2
      rw [profile_prefix_terminal_endpoint p e.2.1 ht] at hend
      rw [wireLength_collarPrefixRoute hs hend]
      exact Nat.add_le_add_left ((collar_route_costs s hs _).2) _
    · rw [wireLength_collarRoute]
      omega
  have hsc : ((g.incidenceRoutes.map fun e => e.2.2.consecutivePairs.length).sum) ≤ 113 := by
    simpa only [segmentCount_eq] using hmeta.2.2.2.1
  have hlen : g.incidenceRoutes.length ≤ 66 := hmeta.2.2.1
  have hwc : (g.incidenceRoutes.map fun e => wireLength e.2.2).sum ≤ 652600 := hmeta.2.2.2.2.1
  have hs' := List.sum_le_sum hseg
  have hw' := List.sum_le_sum hwire
  have hconst (n : ℕ) : (g.incidenceRoutes.map fun _ => n).sum =
      g.incidenceRoutes.length * n := by
    rw [show g.incidenceRoutes.map (fun _ => n) =
      List.replicate g.incidenceRoutes.length n from List.map_const, List.sum_replicate]
    rfl
  rw [List.sum_map_add, hconst] at hs' hw'
  constructor
  · simp only [clauseGeometry, collaredPrefixGeometry, List.map_map, Function.comp_def]
    change (g.incidenceRoutes.map fun e => (profileCollarRoute p s e).consecutivePairs.length).sum
      ≤ _
    nlinarith
  · simp only [clauseGeometry, collaredPrefixGeometry, List.map_map, Function.comp_def]
    change (g.incidenceRoutes.map fun e => wireLength (profileCollarRoute p s e)).sum ≤ _
    nlinarith

private theorem positiveIncidenceRoute_wireLength {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) {e : LocalIncidence}
    (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) :
    wireLength (positiveIncidenceRoute φ d i φ[i] e) = wireLength e.2.2 +
      (sourceSlot (clauseProfile φ[i]) e).elim 0
        (fun j => wireLength (positiveExterior φ d i j)) := by
  unfold positiveIncidenceRoute sourceSlot
  generalize hget : (profileVariables (clauseProfile φ[i])).getD e.2.1 (.inl (.inl 0)) = v
  rcases v with (j | _) | _
  · obtain ⟨q, hlast, hhead⟩ := positiveIncidenceRoute_join_endpoints hd hi
      (profilePrefixGeometry_check _) he hget
    change wireLength (positiveStem φ d i e ++ (positiveExterior φ d i j).tail) =
      wireLength e.2.2 + wireLength (positiveExterior φ d i j)
    rw [wireLength_join hlast hhead]
    simp only [positiveStem, wireLength_translate]
  all_goals simp [wireLength_translate]

private theorem positiveIncidenceRoute_segmentCount {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) {e : LocalIncidence}
    (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) :
    (positiveIncidenceRoute φ d i φ[i] e).consecutivePairs.length =
      e.2.2.consecutivePairs.length + (sourceSlot (clauseProfile φ[i]) e).elim 0
        (fun j => (positiveExterior φ d i j).consecutivePairs.length) := by
  unfold positiveIncidenceRoute sourceSlot
  generalize hget : (profileVariables (clauseProfile φ[i])).getD e.2.1 (.inl (.inl 0)) = v
  rcases v with (j | _) | _
  · obtain ⟨q, hlast, hhead⟩ := positiveIncidenceRoute_join_endpoints hd hi
      (profilePrefixGeometry_check _) he hget
    change (positiveStem φ d i e ++ (positiveExterior φ d i j).tail).consecutivePairs.length =
      e.2.2.consecutivePairs.length + (positiveExterior φ d i j).consecutivePairs.length
    rw [consecutivePairs_join hlast hhead, List.length_append]
    simp only [positiveStem, segmentCount_eq, translate, List.length_map]
  all_goals simp [translate]

private theorem sourceEdgeIndex_occurrence (φ : CNF ℕ) {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    sourceEdgeIndex φ o.1 o.2.1 = (Cslib.Logic.PL.occurrences φ).idxOf o := by
  obtain ⟨hi, hj, he⟩ := Cslib.Logic.PL.mem_occurrences.mp ho
  unfold sourceEdgeIndex
  congr 1
  unfold sourceOccurrence
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, ← he]

private theorem source_edge_weight_sum {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) (weight : Route → ℕ) :
    (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
      weight (d.2.getD (sourceEdgeIndex φ a.2 l.2) [])).sum).sum = (d.2.map weight).sum := by
  have hlen : (Cslib.Logic.PL.occurrences φ).length = d.2.length := by
    simpa only [SAT.incidenceGraph, List.length_map] using hd.edgeCount.symm
  have hlist : ((Cslib.Logic.PL.occurrences φ).map fun o =>
      weight (d.2.getD ((Cslib.Logic.PL.occurrences φ).idxOf o) [])) = d.2.map weight := by
    apply List.ext_getElem (by simp only [List.length_map, hlen])
    intro i hi hj
    have hi' : i < (Cslib.Logic.PL.occurrences φ).length := by simpa only [List.length_map] using hi
    have hj' : i < d.2.length := by simpa only [List.length_map] using hj
    rw [List.getElem_map, (Cslib.Logic.PL.occurrences_nodup φ).idxOf_getElem i hi',
      List.getD_eq_getElem _ _ hj', List.getElem_map]
  calc
    _ = ((Cslib.Logic.PL.occurrences φ).map fun o =>
        weight (d.2.getD (sourceEdgeIndex φ o.1 o.2.1) [])).sum := by
      rw [Cslib.Logic.PL.occurrences, List.map_flatMap, List.flatMap_def,
        List.sum_flatten, List.map_map]
      simp only [List.map_map, Function.comp_def]
    _ = ((Cslib.Logic.PL.occurrences φ).map fun o =>
        weight (d.2.getD ((Cslib.Logic.PL.occurrences φ).idxOf o) [])).sum := by
      apply congrArg List.sum
      exact List.map_congr_left fun o ho => by rw [sourceEdgeIndex_occurrence φ ho]
    _ = _ := congrArg List.sum hlist

private theorem segmentCount_translate (v : Point) (r : Route) :
    (translate v r).consecutivePairs.length = r.consecutivePairs.length := by
  simp only [segmentCount_eq, translate, List.length_map]

private theorem exterior_segment_sum {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) :
    (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
      (positiveExterior φ d a.2 l.2).consecutivePairs.length).sum).sum =
        Graph.drawingSegmentCount d := by
  simp only [positiveExterior, segmentCount_translate, exteriorRoute_segmentCount]
  exact source_edge_weight_sum hd (fun r : Route => r.consecutivePairs.length)

private theorem exterior_wire_sum_le {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) :
    (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
      wireLength (positiveExterior φ d a.2 l.2)).sum).sum ≤
        1080000 * Graph.drawingWireLength d := by
  calc
    _ ≤ (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
        1080000 * wireLength (d.2.getD (sourceEdgeIndex φ a.2 l.2) [])).sum).sum := by
      apply List.sum_le_sum
      intro ⟨c, i⟩ hci
      obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hci)
      change φ[i] = c at hget
      rw [← hget]
      apply List.sum_le_sum
      intro ⟨l, j⟩ hlj
      have hj : j < φ[i].length :=
        (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hlj)).choose
      have he := exteriorRoute_wireLength hd (sourceEdgeIndex_lt φ hi hj)
        (by decide : positiveRadius < positiveScale)
      have hw : wireLength (positiveExterior φ d i j) + positiveRadius =
          1080000 * wireLength (d.2.getD (sourceEdgeIndex φ i j) []) := by
        simpa only [positiveExterior, wireLength_translate, positiveScale] using he
      change wireLength (positiveExterior φ d i j) ≤
        1080000 * wireLength (d.2.getD (sourceEdgeIndex φ i j) [])
      omega
    _ = 1080000 * (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
        wireLength (d.2.getD (sourceEdgeIndex φ a.2 l.2) [])).sum).sum := by
      simp only [List.sum_map_mul_left]
    _ = _ := by rw [source_edge_weight_sum hd]; rfl

private theorem sum_map_constant {A : Type*} (xs : List A) (n : ℕ) :
    (xs.map fun _ => n).sum = xs.length * n := by
  rw [show xs.map (fun _ => n) = List.replicate xs.length n from List.map_const,
    List.sum_replicate]
  rfl

/-- The actual route list has at most 507 incidences per original clause. -/
theorem positiveDrawing_routeCount (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positiveDrawing φ d).2.length ≤ 507 * φ.length := by
  rw [positiveDrawing_edgeCount, SAT.length_edges_incidenceGraph]
  exact CNF.PositiveExactOneCompile.length_vars_formula_le φ

/-- The actual vertex list has at most 676 vertices per original clause. -/
theorem positiveDrawing_vertexCount_le (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positiveDrawing φ d).1.length ≤ 676 * φ.length := by
  rw [positiveDrawing_vertexCount, SAT.length_vertices_incidenceGraph]
  have hv := (CNF.PositiveExactOneCompile.formula φ).numVars_le_length_vars
  have hl := CNF.PositiveExactOneCompile.length_vars_formula_le φ
  have hc := CNF.PositiveExactOneCompile.length_formula_le φ
  omega

/-- Each original source segment is retained once; every original clause contributes only
a fixed local segment allowance. -/
theorem positiveDrawing_segmentCount {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    Graph.drawingSegmentCount (positiveDrawing φ d) ≤
      575 * φ.length + Graph.drawingSegmentCount d := by
  rw [Graph.drawingSegmentCount, positiveDrawing_weight]
  calc
    _ ≤ (φ.zipIdx.map fun a => 575 + (a.1.zipIdx.map fun l =>
        (positiveExterior φ d a.2 l.2).consecutivePairs.length).sum).sum := by
      apply List.sum_le_sum
      intro ⟨c, i⟩ hci
      obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hci)
      change φ[i] = c at hget
      rw [← hget]
      have heq := List.map_congr_left fun e
        (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) =>
          positiveIncidenceRoute_segmentCount hd hi he
      rw [heq, List.sum_map_add,
        clause_source_weight φ d i φ[i] (hw _ (List.getElem_mem hi))]
      exact Nat.add_le_add_right (clauseGeometry_local_costs hd hi φ[i]).1 _
    _ = 575 * φ.length + (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
        (positiveExterior φ d a.2 l.2).consecutivePairs.length).sum).sum := by
      rw [List.sum_map_add, sum_map_constant]
      simp only [List.length_zipIdx, Nat.mul_comm]
    _ = _ := by rw [exterior_segment_sum hd]

/-- Each inherited source wire is charged once after the fixed dilation. The rest is a
constant local wire allowance per original clause. -/
theorem positiveDrawing_wireLength {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    Graph.drawingWireLength (positiveDrawing φ d) ≤
      40252600 * φ.length + 1080000 * Graph.drawingWireLength d := by
  rw [Graph.drawingWireLength, positiveDrawing_weight]
  calc
    _ ≤ (φ.zipIdx.map fun a => 40252600 + (a.1.zipIdx.map fun l =>
        wireLength (positiveExterior φ d a.2 l.2)).sum).sum := by
      apply List.sum_le_sum
      intro ⟨c, i⟩ hci
      obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hci)
      change φ[i] = c at hget
      rw [← hget]
      have heq := List.map_congr_left fun e
        (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) =>
          positiveIncidenceRoute_wireLength hd hi he
      rw [heq, List.sum_map_add,
        clause_source_weight φ d i φ[i] (hw _ (List.getElem_mem hi))]
      exact Nat.add_le_add_right (clauseGeometry_local_costs hd hi φ[i]).2 _
    _ = 40252600 * φ.length + (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
        wireLength (positiveExterior φ d a.2 l.2)).sum).sum := by
      rw [List.sum_map_add, sum_map_constant]
      simp only [List.length_zipIdx, Nat.mul_comm]
    _ ≤ _ := Nat.add_le_add_left (exterior_wire_sum_le hd) _

/-- All actual emitted drawing costs grow by only fixed factors. Inherited exterior incidences
are counted exactly once, independently of source variable repetitions. -/
theorem positiveDrawing_costs {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    (positiveDrawing φ d).1.length ≤ 676 * φ.length ∧
      (positiveDrawing φ d).2.length ≤ 507 * φ.length ∧
      Graph.drawingSegmentCount (positiveDrawing φ d) ≤
        575 * φ.length + Graph.drawingSegmentCount d ∧
      Graph.drawingWireLength (positiveDrawing φ d) ≤
        40252600 * φ.length + 1080000 * Graph.drawingWireLength d :=
  ⟨positiveDrawing_vertexCount_le φ d, positiveDrawing_routeCount φ d,
    positiveDrawing_segmentCount hd hw, positiveDrawing_wireLength hd hw⟩

end Cslib.Complexity.SAT.ExactOne
