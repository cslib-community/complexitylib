/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Lifting
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FaceCounts
public import CslibFrontier.Foundations.GroupTheory.Perm.Doubled
import Mathlib.Data.List.GetD

/-!
# Listed cycles of a finite permutation

The edge indexed by `i` joins `i` to `f i`. The actual two-incidence vertex rotation and
its two opposite face directions retain singleton loops and parallel positions. These
graphs provide finite Boolean face potentials through the existing incidence lifting
theorem; they are auxiliary listed graphs, not a replacement CSP or plane-map model.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv

/-- One actual listed edge from each index to its image under the finite permutation. -/
@[expose] def permutationGraph {n : ℕ} (f : Perm (Fin n)) : Graph :=
  (List.range n, (List.finRange n).map fun i => (i.val, (f i).val))

/-- Edge positions are exactly the original permutation indices. -/
@[expose] def permutationEdgeEquiv {n : ℕ} (f : Perm (Fin n)) :
    Fin n ≃ Fin (permutationGraph f).2.length := finCongr (by simp [permutationGraph])

/-- Original index/end coordinates on the actual graph. -/
@[expose] def permutationDartEquiv {n : ℕ} (f : Perm (Fin n)) :
    Fin n × Bool ≃ Dart (permutationGraph f) :=
  (permutationEdgeEquiv f).prodCongr (Equiv.refl Bool)

/-- The first end has name `i`, the second name `f i`, including fixed-point loops. -/
@[simp] theorem vertex_permutationDartEquiv {n : ℕ} (f : Perm (Fin n)) (i : Fin n) (b : Bool) :
    (permutationDartEquiv f (i, b)).vertex = if b then (f i).val else i.val := by
  change (if b then ((permutationGraph f).2.getD i.val (0, 0)).2
    else ((permutationGraph f).2.getD i.val (0, 0)).1) = _
  rw [List.getD_eq_getElem _ _ (by simp [permutationGraph])]
  simp [permutationGraph]

/-- Reversal keeps its original edge position. -/
@[simp] theorem reverse_permutationDartEquiv {n : ℕ} (f : Perm (Fin n)) (i : Fin n) (b : Bool) :
    (permutationDartEquiv f (i, b)).reverse = permutationDartEquiv f (i, !b) := rfl

/-- Index a vertex's outgoing and incoming incidences, in that order. -/
@[expose] def permutationVertexDartEquiv {n : ℕ} (f : Perm (Fin n)) :
    Fin n × Bool ≃ Dart (permutationGraph f) :=
  ({ toFun := fun d => (if d.2 then f.symm d.1 else d.1, d.2)
     invFun := fun d => (if d.2 then f d.1 else d.1, d.2)
     left_inv := by rintro ⟨i, b⟩; cases b <;> simp
     right_inv := by rintro ⟨i, b⟩; cases b <;> simp } :
    Fin n × Bool ≃ Fin n × Bool).trans (permutationDartEquiv f)

private theorem vertex_permutationVertexDartEquiv {n : ℕ} (f : Perm (Fin n))
    (i : Fin n) (b : Bool) :
    (permutationVertexDartEquiv f (i, b)).vertex = i.val := by
  cases b <;> simp [permutationVertexDartEquiv]

/-- Every listed vertex has exactly the two indexed incidences of its permutation cycle. -/
@[expose] def permutationRotation {n : ℕ} (f : Perm (Fin n)) :
    RotationSystem (permutationGraph f) where
  rotate := (permutationVertexDartEquiv f).permCongr (Perm.doubled (1 : Perm (Fin n)))
  sameCycle_iff a b := by
    obtain ⟨⟨i, s⟩, rfl⟩ := (permutationVertexDartEquiv f).surjective a
    obtain ⟨⟨j, t⟩, rfl⟩ := (permutationVertexDartEquiv f).surjective b
    rw [Perm.sameCycle_equiv_iff (permutationVertexDartEquiv f) (Perm.doubled 1) _
      (by intro d; simp), Perm.sameCycle_doubled, Perm.sameCycle_one,
      vertex_permutationVertexDartEquiv, vertex_permutationVertexDartEquiv]
    exact Fin.ext_iff

/-- Exact directed vertex splice, in the original edge/end coordinates. -/
theorem rotate_permutationDartEquiv {n : ℕ} (f : Perm (Fin n)) (i : Fin n) (b : Bool) :
    (permutationRotation f).rotate (permutationDartEquiv f (i, b)) =
      permutationDartEquiv f (if b then f i else f.symm i, !b) := by
  cases b <;> simp [permutationRotation, permutationVertexDartEquiv, Perm.doubled]

/-- The two face directions follow `f` and its inverse separately. -/
theorem faceNext_permutationDartEquiv {n : ℕ} (f : Perm (Fin n)) (i : Fin n) (b : Bool) :
    (permutationRotation f).faceNext (permutationDartEquiv f (i, b)) =
      permutationDartEquiv f (if b then f.symm i else f i, b) := by
  apply (permutationRotation f).rotate.injective
  change (permutationRotation f).rotate ((permutationRotation f).rotate.symm
    (permutationDartEquiv f (i, b)).reverse) = _
  rw [Equiv.apply_symm_apply, reverse_permutationDartEquiv, rotate_permutationDartEquiv]
  cases b <;> simp

/-- All endpoints are actual declared permutation indices. -/
theorem permutationGraph_endpoints_declared {n : ℕ} (f : Perm (Fin n)) :
    ∀ v ∈ (permutationGraph f).incidenceVertices, v ∈ (permutationGraph f).1 := by
  intro v hv
  obtain ⟨edge, he, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> simp [permutationGraph]

private theorem vertex_false {n : ℕ} (f : Perm (Fin n))
    (i : Fin (permutationGraph f).2.length) :
    Dart.vertex (G := permutationGraph f) (i, false) = i.val := by
  obtain ⟨j, rfl⟩ := (permutationEdgeEquiv f).surjective i
  simpa [permutationDartEquiv, permutationEdgeEquiv] using vertex_permutationDartEquiv f j false

open Classical in
private noncomputable def componentEdgeVertexEquiv {n : ℕ} (f : Perm (Fin n)) (root : ℕ) :
    ↥((permutationGraph f).componentEdgeSet root) ≃
      ↥((permutationGraph f).componentVertexSet root) where
  toFun i := ⟨i.val.val, by
    rw [← vertex_false f i.val]
    exact (mem_componentEdgeSet_iff root (permutationGraph_endpoints_declared f) i.val false).mp
      i.property⟩
  invFun v :=
    let i : Fin (permutationGraph f).2.length := ⟨v.val, by
      have h := List.mem_range.mp (List.mem_toFinset.mp (Finset.mem_filter.mp v.property).1)
      simpa only [permutationGraph, List.length_map, List.length_finRange] using h⟩
    ⟨i, (mem_componentEdgeSet_iff root (permutationGraph_endpoints_declared f) i false).mpr
      (by rw [vertex_false]; exact v.property)⟩
  left_inv _ := Subtype.ext (Fin.ext rfl)
  right_inv _ := Subtype.ext rfl

private theorem sameFace_side_eq {n : ℕ} (f : Perm (Fin n)) (i j : Fin n) (b c : Bool)
    (h : (permutationRotation f).faceNext.SameCycle
      (permutationDartEquiv f (i, b)) (permutationDartEquiv f (j, c))) : b = c := by
  let side (d : Dart (permutationGraph f)) := ((permutationDartEquiv f).symm d).2
  have hs : Function.Semiconj side (permutationRotation f).faceNext (1 : Perm Bool) := by
    intro d
    obtain ⟨⟨k, s⟩, rfl⟩ := (permutationDartEquiv f).surjective d
    simp only [faceNext_permutationDartEquiv, side, Equiv.symm_apply_apply, Perm.one_apply]
  simpa only [side, Equiv.symm_apply_apply] using Perm.sameCycle_one.mp (h.map_of_semiconj hs)

/-- Each permutation-cycle component has equally many vertices and indexed edges, and its
two face directions are distinct. The universal matrix Euler bound supplies equality.
Fixed points produce ordinary sphere loops; the empty permutation graph has no components. -/
theorem numericalGenusZero_permutationRotation {n : ℕ} (f : Perm (Fin n)) :
    (permutationRotation f).NumericalGenusZero := by
  classical
  let r := permutationRotation f
  have hG := permutationGraph_endpoints_declared f
  apply (r.numericalGenusZero_iff_component_cards hG).mpr
  intro d
  obtain ⟨⟨i, s⟩, rfl⟩ := (permutationDartEquiv f).surjective d
  have hcomp (b : Bool) : RotationCertificate.SameComponent (permutationGraph f)
      (permutationDartEquiv f (i, s)).vertex (permutationDartEquiv f (i, b)).vertex := by
    have he := sameComponent_reverse hG (permutationDartEquiv f (i, false))
    rw [reverse_permutationDartEquiv] at he
    cases s <;> cases b
    · exact .refl (vertex_mem hG _)
    · exact he
    · exact he.symm
    · exact .refl (vertex_mem hG _)
  let toFace (b : Bool) : ComponentFace r (permutationDartEquiv f (i, s)).vertex :=
    ⟨Quotient.mk _ (permutationDartEquiv f (i, b)),
      permutationDartEquiv f (i, b), hcomp b, rfl⟩
  have hi : Function.Injective toFace := by
    intro b c h
    exact sameFace_side_eq f i i b c (Quotient.exact (congrArg Subtype.val h))
  have hF : 2 ≤ Nat.card (ComponentFace r (permutationDartEquiv f (i, s)).vertex) := by
    simpa using Nat.card_le_card_of_injective toFace hi
  have hVE := Nat.card_congr
    (componentEdgeVertexEquiv f (permutationDartEquiv f (i, s)).vertex)
  simp only [Nat.card_eq_finsetCard] at hVE
  have hEuler := r.component_euler_le hG (permutationDartEquiv f (i, s))
  rw [card_componentFaceIndices, r.count_faceRepresentatives_eq_card_componentFace hG] at hEuler ⊢
  omega

/-- The complete face classes are the two oriented copies of the original permutation
orbits, including fixed points. -/
theorem sameFace_permutationDartEquiv_iff {n : ℕ} (f : Perm (Fin n))
    (i j : Fin n) (b c : Bool) :
    (permutationRotation f).faceNext.SameCycle
      (permutationDartEquiv f (i, b)) (permutationDartEquiv f (j, c)) ↔
        b = c ∧ f.SameCycle i j := by
  constructor
  · intro h
    refine ⟨sameFace_side_eq f i j b c h, ?_⟩
    let q : Fin n → Quotient (Perm.SameCycle.setoid f) := Quotient.mk _
    let qd (d : Dart (permutationGraph f)) := q ((permutationDartEquiv f).symm d).1
    have hq : Function.Semiconj qd (permutationRotation f).faceNext
        (1 : Perm (Quotient (Perm.SameCycle.setoid f))) := by
      intro d
      obtain ⟨⟨k, s⟩, rfl⟩ := (permutationDartEquiv f).surjective d
      simp only [faceNext_permutationDartEquiv, qd, Equiv.symm_apply_apply, Perm.one_apply]
      apply Quotient.sound
      change f.SameCycle (if s then f.symm k else f k) k
      cases s
      · exact Perm.sameCycle_apply_left.mpr .rfl
      · simpa only [Equiv.apply_symm_apply, ↓reduceIte] using
          (Perm.SameCycle.rfl : f.SameCycle (f.symm k) (f.symm k)).apply_right
    have hh := Perm.sameCycle_one.mp (h.map_of_semiconj hq)
    have heq : (Quotient.mk (Perm.SameCycle.setoid f) i :
        Quotient (Perm.SameCycle.setoid f)) = Quotient.mk _ j := by
      simpa only [qd, q, Equiv.symm_apply_apply] using hh
    exact Quotient.exact heq
  · rintro ⟨rfl, hij⟩
    cases b
    · exact hij.map_of_semiconj (u := fun j => permutationDartEquiv f (j, false))
        (g := (permutationRotation f).faceNext)
        (fun j => (faceNext_permutationDartEquiv f j false).symm)
    · exact hij.inv.map_of_semiconj (u := fun j => permutationDartEquiv f (j, true))
        (g := (permutationRotation f).faceNext)
        (fun j => (faceNext_permutationDartEquiv f j true).symm)

open Classical in
/-- A Boolean labeling with zero sum on every full finite permutation orbit is a difference
of a Boolean potential at consecutive points. The proof constructs actual listed cycle graphs
and discharges their numerical genus internally before invoking existing incidence lifting. -/
theorem exists_potential_of_cycleSum_zero {n : ℕ} (f : Perm (Fin n)) (x : Fin n → Bool)
    (h : ∀ i, (∑ j : Fin n, if f.SameCycle i j then x j else 0) = 0) :
    ∃ p : Fin n → Bool, ∀ i, x i = (p i ^^ p (f i)) := by
  let r := permutationRotation f
  let xe (j : Fin (permutationGraph f).2.length) := x ((permutationEdgeEquiv f).symm j)
  have hxcoord (j : Fin n) (b : Bool) : xe (permutationDartEquiv f (j, b)).1 = x j := by
    change x ((permutationEdgeEquiv f).symm (permutationEdgeEquiv f j)) = x j
    rw [Equiv.symm_apply_apply]
  have hparity (i : Fin n) (b : Bool) :
      r.faceParity xe (Quotient.mk _ (permutationDartEquiv f (i, b))) =
        ∑ j : Fin n, if f.SameCycle i j then x j else 0 := by
    rw [r.faceParity_mk, parityOn_eq_sum, Finset.sum_filter]
    rw [← Equiv.sum_comp (permutationDartEquiv f)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [r, sameFace_permutationDartEquiv_iff, hxcoord]
    cases b <;> simp
  have hx : r.FaceEven xe := by
    apply (r.faceEven_iff_dart xe).mpr
    intro d
    obtain ⟨⟨i, b⟩, rfl⟩ := (permutationDartEquiv f).surjective d
    rw [hparity]
    simpa only [Bool.zero_eq_false] using h i
  obtain ⟨spin, hspin⟩ := r.exists_vertexSpins_of_faceEven
    (permutationGraph_endpoints_declared f) (numericalGenusZero_permutationRotation f) xe hx
  refine ⟨fun i => spin i.val, ?_⟩
  intro i
  have he := congrFun hspin (permutationEdgeEquiv f i)
  have hd := Graph.edgeGradient_dart (permutationGraph f) spin (permutationDartEquiv f (i, false))
  rw [reverse_permutationDartEquiv, vertex_permutationDartEquiv, vertex_permutationDartEquiv] at hd
  simp only [Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hd
  have hxedge : xe (permutationEdgeEquiv f i) = x i := by
    simp only [xe, Equiv.symm_apply_apply]
  exact hxedge.symm.trans (he.symm.trans hd)

end Cslib.Complexity.Graph.RotationSystem
