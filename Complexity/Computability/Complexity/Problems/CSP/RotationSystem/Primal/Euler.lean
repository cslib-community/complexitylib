/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Components
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.FaceCounts
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Sum

/-!
# Componentwise Euler preservation for CSP polygons

Counts refer to the actual listed graphs and every face orbit, including singleton orbits.
The target predicate is the existing componentwise `NumericalGenusZero`, with no change of
model and no geometric, native-computation or recognition claim.

## Main results

* `Cslib.Complexity.CSP.polygon_component_vertex_count`: exact variable/constraint split.
* `Cslib.Complexity.CSP.polygon_component_edge_count`: preserves indexed edge counts.
* `Cslib.Complexity.CSP.polygon_component_face_card`: complete component face counts.
* `Cslib.Complexity.CSP.numericalGenusZero_polygon_iff`: componentwise Euler equivalence.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph.RotationCertificate Graph.RotationSystem

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- In a component rooted at a dense variable, polygon faces are exactly its constraint
positions together with its original incidence faces. All face orbits are counted. -/
theorem polygon_component_face_card (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].2.length) (root : ℕ) (hr : root < F.numVars) :
    Nat.card {f : (polygonRotation r).Face // ∃ d : Graph.Dart (polygonGraph F),
      SameComponent (polygonGraph F) root d.vertex ∧ Quotient.mk _ d = f} =
    Nat.card {i : Fin F.length // SameComponent (incidenceGraph F) root (F.numVars + i.val)} +
      Nat.card {f : r.Face // ∃ d : Graph.Dart (incidenceGraph F),
        SameComponent (incidenceGraph F) root d.vertex ∧ Quotient.mk _ d = f} := by
  let Q : Fin F.length ⊕ r.Face → Prop := Sum.elim
    (fun i => SameComponent (incidenceGraph F) root (F.numVars + i.val))
    (fun f => ∃ d : Graph.Dart (incidenceGraph F),
      SameComponent (incidenceGraph F) root d.vertex ∧ Quotient.mk _ d = f)
  have hmem (f : (polygonRotation r).Face) :
      (∃ d : Graph.Dart (polygonGraph F), SameComponent (polygonGraph F) root d.vertex ∧
        Quotient.mk _ d = f) ↔ Q (polygonFaceEquiv r hOrder hPos f) := by
    induction f using Quotient.inductionOn with
    | h d =>
      rcases d with ⟨edge, b⟩
      obtain ⟨o, ho⟩ := exists_polygonDart (F := F) (edge, b)
      cases b
      · rw [← ho, polygonFaceEquiv_black,
          componentFace_mk_iff _ polygon_endpoints_declared, vertex_polygonDart]
        have hd : F.distinctVars.idxOf o.var < F.numVars := by
          rw [← CSP.length_distinctVars]
          exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)
        have hc := Graph.RotationSystem.sameComponent_reverse (incidenceVertices_declared F)
          (incidenceDart o false)
        change SameComponent _ (incidenceDart o false).vertex (incidenceDart o true).vertex at hc
        simp only [vertex_incidenceDart, Bool.false_eq_true, ↓reduceIte] at hc ⊢
        rw [sameComponent_polygon_iff hr hd]
        exact ⟨fun h => h.trans hc, fun h => h.trans hc.symm⟩
      · have hw := polygonFaceEquiv_white r hOrder hPos (argumentPermutation F o)
        rw [Equiv.symm_apply_apply] at hw
        rw [← ho, hw, componentFace_mk_iff _ polygon_endpoints_declared]
        change SameComponent _ root (polygonDart o true).vertex ↔
          ∃ d : Graph.Dart (incidenceGraph F), SameComponent _ root d.vertex ∧
            (Quotient.mk _ d : r.Face) =
              Quotient.mk _ (incidenceDart (argumentPermutation F o) false)
        rw [componentFace_mk_iff _ (incidenceVertices_declared F),
          vertex_polygonDart, vertex_incidenceDart]
        have hd : F.distinctVars.idxOf (argumentSuccessor o).var < F.numVars := by
          rw [← CSP.length_distinctVars]
          exact List.idxOf_lt_length_of_mem
            (CSP.mem_distinctVars.mpr (argumentSuccessor o).var_mem)
        exact sameComponent_polygon_iff hr hd
  calc
    _ = Nat.card {s // Q s} :=
      Nat.card_congr ((polygonFaceEquiv r hOrder hPos).subtypeEquiv hmem)
    _ = Nat.card {i : Fin F.length // Q (.inl i)} + Nat.card {f : r.Face // Q (.inr f)} := by
      rw [Nat.card_congr (Equiv.subtypeSum (p := Q)), Nat.card_sum]
    _ = _ := rfl

open Classical in
/-- The incidence component has the polygon's variable vertices plus its indexed positive
constraint vertices. Vertex names are counted once, while constraint positions stay distinct. -/
theorem polygon_component_vertex_count (root : ℕ) (hr : root < F.numVars) :
    (incidenceGraph F).distinctVertices.countP
      (fun v => decide (SameComponent (incidenceGraph F) root v)) =
    (polygonGraph F).distinctVertices.countP
      (fun v => decide (SameComponent (polygonGraph F) root v)) +
      Nat.card {i : Fin F.length // SameComponent (incidenceGraph F) root (F.numVars + i.val)} := by
  classical
  rw [Graph.countP_vertices_range _ _ (incidenceGraph_vertices F),
    Graph.countP_vertices_range _ F.numVars rfl]
  have h := Nat.card_congr
    (finSumFinEquiv.subtypeEquivOfSubtype
      (p := fun v : Fin (F.numVars + F.length) => SameComponent (incidenceGraph F) root v.val))
  rw [← h, Nat.card_congr (Equiv.subtypeSum), Nat.card_sum]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun v => (sameComponent_polygon_iff hr v.isLt).symm)

open Classical in
/-- The component edge counts agree exactly: both lists retain one edge position per
occurrence, and its first endpoint is the same dense variable. -/
theorem polygon_component_edge_count (root : ℕ) (hr : root < F.numVars) :
    (polygonGraph F).2.countP
      (fun e => decide (SameComponent (polygonGraph F) root e.1)) =
    (incidenceGraph F).2.countP
      (fun e => decide (SameComponent (incidenceGraph F) root e.1)) := by
  classical
  rw [incidenceGraph_edges]
  change (F.occurrences.map _).countP _ = _
  rw [List.countP_map, List.countP_map]
  apply List.countP_congr
  intro record hrecord
  obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hrecord
  simp only [Function.comp_apply, decide_eq_true_eq]
  apply sameComponent_polygon_iff hr
  rw [← CSP.length_distinctVars]
  exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)

/-- Replacing every positive ordered incidence star by its actual occurrence-indexed polygon
preserves the existing componentwise numerical genus-zero predicate in both directions.
This includes disconnected and empty instances. It asserts no geometric realization. -/
theorem numericalGenusZero_polygon_iff (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].2.length) :
    (polygonRotation r).NumericalGenusZero ↔ r.NumericalGenusZero := by
  classical
  let Euler (G : Graph) (s : Graph.RotationSystem G) (root : ℕ) : Prop :=
    G.distinctVertices.countP (fun v => decide (SameComponent G root v)) +
      ((List.finRange (2 * G.2.length)).countP fun i =>
        decide (SameComponent G root ((Graph.Dart.indexEquiv G).symm i).vertex ∧
          s.IsFaceRepresentative ((Graph.Dart.indexEquiv G).symm i))) =
      G.2.countP (fun e => decide (SameComponent G root e.1)) + 2
  have hdense (o : F.Occurrence) : F.distinctVars.idxOf o.var < F.numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)
  have hEuler (root : ℕ) (hr : root < F.numVars) :
      Euler (polygonGraph F) (polygonRotation r) root ↔ Euler (incidenceGraph F) r root := by
    dsimp only [Euler]
    rw [count_faceRepresentatives_eq_card_componentFace _ polygon_endpoints_declared,
      count_faceRepresentatives_eq_card_componentFace _ (incidenceVertices_declared F)]
    have hV := polygon_component_vertex_count root hr
    have hF := polygon_component_face_card r hOrder hPos root hr
    have hE := polygon_component_edge_count root hr
    dsimp only [ComponentFace] at *
    omega
  have hPdart (root : ℕ) (hr : root ∈ (polygonGraph F).1) :
      ∃ d : Graph.Dart (polygonGraph F), d.vertex = root := by
    obtain ⟨o, ho⟩ := exists_occurrence_dense root (List.mem_range.mp hr)
    exact ⟨polygonDart o false, (vertex_polygonDart o false).trans ho⟩
  have hIdart (root : ℕ) (hr : root ∈ (incidenceGraph F).1) :
      ∃ o : F.Occurrence, ∃ b : Bool, (incidenceDart o b).vertex = root := by
    by_cases hv : root < F.numVars
    · obtain ⟨o, ho⟩ := exists_occurrence_dense root hv
      exact ⟨o, false, (vertex_incidenceDart o false).trans ho⟩
    · have hb : root < F.numVars + F.length := by
        rw [incidenceGraph_vertices, List.mem_range] at hr
        exact hr
      let i : Fin F.length := ⟨root - F.numVars, by omega⟩
      let o : F.Occurrence := ⟨i, ⟨0, hPos i⟩⟩
      refine ⟨o, true, ?_⟩
      rw [vertex_incidenceDart]
      dsimp [o, i]
      omega
  constructor
  · intro hP
    unfold Graph.RotationSystem.NumericalGenusZero at hP ⊢
    intro root hr
    obtain ⟨o, b, ho⟩ := hIdart root hr
    rw [ite_eq_left ⟨incidenceDart o b, ho⟩]
    have hp := hP (F.distinctVars.idxOf o.var) (List.mem_range.mpr (hdense o))
    rw [ite_eq_left (hPdart _ (List.mem_range.mpr (hdense o)))] at hp
    have hi := (hEuler _ (hdense o)).mp hp
    have hc : SameComponent (incidenceGraph F) root (F.distinctVars.idxOf o.var) := by
      cases b
      · rw [vertex_incidenceDart] at ho
        rw [← ho]
        exact .refl (by
          simpa only [vertex_incidenceDart] using
            Graph.RotationSystem.vertex_mem (incidenceVertices_declared F) (incidenceDart o false))
      · have h := Graph.RotationSystem.sameComponent_reverse (incidenceVertices_declared F)
          (incidenceDart o false)
        change SameComponent _ (incidenceDart o false).vertex (incidenceDart o true).vertex at h
        rw [ho, vertex_incidenceDart] at h
        exact h.symm
    have hrel (v : ℕ) : SameComponent (incidenceGraph F) root v ↔
        SameComponent (incidenceGraph F) (F.distinctVars.idxOf o.var) v :=
      ⟨fun h => hc.symm.trans h, fun h => hc.trans h⟩
    simpa only [Euler, hrel] using hi
  · intro hI
    unfold Graph.RotationSystem.NumericalGenusZero at hI ⊢
    intro root hr
    rw [ite_eq_left (hPdart root hr)]
    have hroot : root ∈ (incidenceGraph F).1 := by
      rw [incidenceGraph_vertices, List.mem_range]
      have := List.mem_range.mp hr
      omega
    obtain ⟨o, b, ho⟩ := hIdart root hroot
    have hi := hI root hroot
    rw [ite_eq_left ⟨incidenceDart o b, ho⟩] at hi
    exact (hEuler root (List.mem_range.mp hr)).mpr hi

end Cslib.Complexity.CSP
