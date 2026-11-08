/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Euler
import all Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Faces

/-!
# Polygon Euler transport with nullary constraints

Nullary constraint vertices are isolated points in the original incidence graph. They add no
polygon edge or face. Restricting the black face index to positive actual scopes extends the
existing orbit correspondence without deleting or renumbering the original CSP. The numerical
Euler transport below therefore applies to the original supplied certificate, even when true
nullaries occur between positive constraints. Their truth is a separate semantic guard.
No geometric embedding or recognition theorem is asserted.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph.RotationCertificate Graph.RotationSystem

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- Indexed constraints having an actual argument; nullary positions have no black dart. -/
abbrev PositiveConstraint (F : CSP Rel V) := {i : Fin F.length // 0 < F[i.val].2.length}

/-- The argument orbits are exactly the positive constraint positions, retaining duplicates. -/
noncomputable def argumentOrbitPositiveEquiv (F : CSP Rel V) :
    Quotient (Equiv.Perm.SameCycle.setoid (argumentPermutation F)) ≃ PositiveConstraint F where
  toFun := Quotient.lift (fun o => ⟨o.1, Nat.zero_lt_of_lt o.2.isLt⟩)
    (fun _ _ h => Subtype.ext ((sameCycle_argumentPermutation _ _).mp h))
  invFun i := Quotient.mk _ ⟨i.val, ⟨0, i.property⟩⟩
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h o => exact Quotient.sound ((sameCycle_argumentPermutation _ _).mpr rfl)
  right_inv _ := rfl

/-- Complete face decomposition, with no positivity premise on the original CSP. -/
noncomputable def polygonFacePositiveEquiv (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r) :
    (polygonRotation r).Face ≃ PositiveConstraint F ⊕ r.Face :=
  (polygonFaceOrbitEquiv r).trans
    (Equiv.sumCongr (argumentOrbitPositiveEquiv F) (incidenceFaceOrbitEquiv r hOrder).symm)

/-- The black face still has its exact original positive constraint index. -/
theorem polygonFacePositiveEquiv_black (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r) (o : F.Occurrence) :
    polygonFacePositiveEquiv r hOrder (Quotient.mk _ (polygonDart o false)) =
      .inl ⟨o.1, Nat.zero_lt_of_lt o.2.isLt⟩ := by
  let e : Quotient (Equiv.Perm.SameCycle.setoid
      (Equiv.sumCongr (argumentPermutation F) (incidenceSquarePermutation r))) ≃
      (polygonRotation r).Face := Quotient.congr (polygonSumEquiv F) (fun x y =>
    (Equiv.Perm.sameCycle_equiv_iff (polygonSumEquiv F) _ _
      (fun z => (faceNext_polygonSum r z).symm) x y).symm)
  have h : e.symm (Quotient.mk _ (polygonDart o false)) = Quotient.mk _ (.inl o) :=
    e.symm_apply_apply (Quotient.mk _ (.inl o))
  unfold polygonFacePositiveEquiv polygonFaceOrbitEquiv
  dsimp only [Equiv.trans_apply]
  change (Equiv.sumCongr _ _) ((Equiv.Perm.sumOrbitEquiv _ _) (e.symm _)) = _
  rw [h]
  rfl

/-- The white correspondence is unchanged by isolated nullary constraint vertices. -/
theorem polygonFacePositiveEquiv_white (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r) (o : F.Occurrence) :
    polygonFacePositiveEquiv r hOrder
      (Quotient.mk _ (polygonDart ((argumentPermutation F).symm o) true)) =
      .inr (Quotient.mk _ (incidenceDart o false)) := by
  let e : Quotient (Equiv.Perm.SameCycle.setoid
      (Equiv.sumCongr (argumentPermutation F) (incidenceSquarePermutation r))) ≃
      (polygonRotation r).Face := Quotient.congr (polygonSumEquiv F) (fun x y =>
    (Equiv.Perm.sameCycle_equiv_iff (polygonSumEquiv F) _ _
      (fun z => (faceNext_polygonSum r z).symm) x y).symm)
  have h : e.symm (Quotient.mk _ (polygonDart ((argumentPermutation F).symm o) true)) =
      Quotient.mk _ (.inr o) := e.symm_apply_apply (Quotient.mk _ (.inr o))
  unfold polygonFacePositiveEquiv polygonFaceOrbitEquiv
  dsimp only [Equiv.trans_apply]
  change (Equiv.sumCongr _ _) ((Equiv.Perm.sumOrbitEquiv _ _) (e.symm _)) = _
  rw [h]
  change Sum.inr ((incidenceFaceOrbitEquiv r hOrder).symm (Quotient.mk _ o)) = _
  apply congrArg Sum.inr
  rw [Equiv.symm_apply_eq]
  exact (incidenceFaceOrbitEquiv_mk_false r hOrder o).symm

/-- An edge always separates a black face from a distinct white face, regardless of nullaries. -/
theorem polygon_edge_faces_distinct_of_occurrence
    (r : Graph.RotationSystem (incidenceGraph F)) (hOrder : RespectsArgumentOrder r)
    (o : F.Occurrence) :
    (Quotient.mk _ (polygonDart o false) : (polygonRotation r).Face) ≠
      Quotient.mk _ (polygonDart o true) := by
  have hw := polygonFacePositiveEquiv_white r hOrder (argumentPermutation F o)
  rw [Equiv.symm_apply_apply] at hw
  intro h
  have he := congrArg (polygonFacePositiveEquiv r hOrder) h
  rw [polygonFacePositiveEquiv_black, hw] at he
  cases he

private theorem positive_of_sameComponent (root : ℕ) (hr : root < F.numVars)
    (i : Fin F.length) (hi : SameComponent (incidenceGraph F) root (F.numVars + i.val)) :
    0 < F[i.val].2.length := by
  obtain ⟨o, ho⟩ := exists_occurrence_dense root hr
  have hroot : (incidenceDart o false).vertex = root := by
    simpa only [vertex_incidenceDart, Bool.false_eq_true, ↓reduceIte] using ho
  obtain ⟨d, hd⟩ := Graph.Dart.exists_of_sameComponent (incidenceDart o false)
    (F.numVars + i.val) (by rwa [hroot])
  obtain ⟨p, hp⟩ := exists_incidenceDart d
  have hvertex := vertex_incidenceDart p d.2
  rw [hp, hd] at hvertex
  have hv : F.distinctVars.idxOf p.var < F.numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr p.var_mem)
  cases hb : d.2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hvertex
    omega
  · simp only [hb, ↓reduceIte] at hvertex
    have he : p.1 = i := Fin.ext (by omega)
    have := Nat.zero_lt_of_lt p.2.isLt
    simpa only [he] using this

/-- Nullary vertices are absent from every component rooted at an occurring variable. -/
theorem polygon_component_face_card_with_nullaries
    (r : Graph.RotationSystem (incidenceGraph F)) (hOrder : RespectsArgumentOrder r)
    (root : ℕ) (hr : root < F.numVars) :
    Nat.card {f : (polygonRotation r).Face // ∃ d : Graph.Dart (polygonGraph F),
      SameComponent (polygonGraph F) root d.vertex ∧ Quotient.mk _ d = f} =
    Nat.card {i : Fin F.length // SameComponent (incidenceGraph F) root (F.numVars + i.val)} +
      Nat.card {f : r.Face // ∃ d : Graph.Dart (incidenceGraph F),
        SameComponent (incidenceGraph F) root d.vertex ∧ Quotient.mk _ d = f} := by
  classical
  let Q : PositiveConstraint F ⊕ r.Face → Prop := Sum.elim
    (fun i => SameComponent (incidenceGraph F) root (F.numVars + i.val.val))
    (fun f => ∃ d : Graph.Dart (incidenceGraph F),
      SameComponent (incidenceGraph F) root d.vertex ∧ Quotient.mk _ d = f)
  have hmem (f : (polygonRotation r).Face) :
      (∃ d : Graph.Dart (polygonGraph F), SameComponent (polygonGraph F) root d.vertex ∧
        Quotient.mk _ d = f) ↔ Q (polygonFacePositiveEquiv r hOrder f) := by
    induction f using Quotient.inductionOn with
    | h d =>
      rcases d with ⟨edge, b⟩
      obtain ⟨o, ho⟩ := exists_polygonDart (F := F) (edge, b)
      cases b
      · rw [← ho, polygonFacePositiveEquiv_black,
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
      · have hw := polygonFacePositiveEquiv_white r hOrder (argumentPermutation F o)
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
  let e : {i : PositiveConstraint F //
      SameComponent (incidenceGraph F) root (F.numVars + i.val.val)} ≃
      {i : Fin F.length // SameComponent (incidenceGraph F) root (F.numVars + i.val)} :=
    { toFun := fun i => ⟨i.val.val, i.property⟩
      invFun := fun i => ⟨⟨i.val, positive_of_sameComponent root hr i.val i.property⟩, i.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  calc
    _ = Nat.card {s // Q s} :=
      Nat.card_congr ((polygonFacePositiveEquiv r hOrder).subtypeEquiv hmem)
    _ = Nat.card {i : PositiveConstraint F // Q (.inl i)} +
        Nat.card {f : r.Face // Q (.inr f)} := by
      rw [Nat.card_congr (Equiv.subtypeSum (p := Q)), Nat.card_sum]
    _ = _ := congrArg (fun n => n + Nat.card {f : r.Face // Q (.inr f)}) (Nat.card_congr e)

/-- Forward numerical Euler transport on the original instance, including every nullary
constraint as an isolated incidence point. No deletion or supplied transport is assumed. -/
theorem numericalGenusZero_polygon_with_nullaries
    (r : Graph.RotationSystem (incidenceGraph F)) (hOrder : RespectsArgumentOrder r)
    (hgenus : r.NumericalGenusZero) : (polygonRotation r).NumericalGenusZero := by
  classical
  intro root hr
  have hdense : root < F.numVars := List.mem_range.mp hr
  obtain ⟨o, ho⟩ := exists_occurrence_dense root hdense
  have hPdart : ∃ d : Graph.Dart (polygonGraph F), d.vertex = root :=
    ⟨polygonDart o false, (vertex_polygonDart o false).trans ho⟩
  have hIdart : ∃ d : Graph.Dart (incidenceGraph F), d.vertex = root :=
    ⟨incidenceDart o false, (vertex_incidenceDart o false).trans ho⟩
  rw [ite_eq_left hPdart]
  have hi := hgenus root (by rw [incidenceGraph_vertices, List.mem_range]; omega)
  rw [ite_eq_left hIdart] at hi
  rw [count_faceRepresentatives_eq_card_componentFace _ polygon_endpoints_declared]
  rw [count_faceRepresentatives_eq_card_componentFace _ (incidenceVertices_declared F)] at hi
  have hV := polygon_component_vertex_count (F := F) root hdense
  have hE := polygon_component_edge_count (F := F) root hdense
  have hF := polygon_component_face_card_with_nullaries r hOrder root hdense
  dsimp only [ComponentFace] at *
  omega

end Cslib.Complexity.CSP
