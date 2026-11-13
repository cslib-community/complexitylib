/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Rotation
import Mathlib.Logic.Equiv.Prod

/-!
# Complete black and white face correspondence

For positive actual scopes, every constraint position is one black face. Every remaining
face is white and corresponds to exactly one incidence face. Singleton orbits are retained.
These are combinatorial orbit correspondences; no geometric or algorithmic premise is used.

## Main definitions

* `Cslib.Complexity.CSP.polygonFaceEquiv`: full black/white face decomposition.
* `Cslib.Complexity.CSP.blackFace`, `Cslib.Complexity.CSP.whiteFace`: its indexed inclusions.

## Main results

* `Cslib.Complexity.CSP.polygonFaceEquiv_black`: exact constraint-position map.
* `Cslib.Complexity.CSP.polygonFaceEquiv_white`: exact incidence-face conjugation.
* `Cslib.Complexity.CSP.polygon_edge_faces_distinct`: two different faces at each edge.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- The square of the incidence face successor, expressed on variable occurrences: `A⁻¹ B⁻¹`. -/
@[expose] noncomputable def incidenceSquarePermutation
    (r : Graph.RotationSystem (incidenceGraph F)) : Equiv.Perm F.Occurrence :=
  (argumentPermutation F).symm.trans (variablePermutation r).symm

/-- The incidence face successor leaves a variable end through the previous argument end. -/
@[simp] theorem faceNext_incidenceDart_false (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r) (o : F.Occurrence) :
    r.faceNext (incidenceDart o false) =
      incidenceDart ((argumentPermutation F).symm o) true := by
  change r.rotate.symm (incidenceDart o true) = _
  rw [Equiv.symm_apply_eq]
  rw [hOrder]
  exact congrArg (fun p : F.Occurrence => incidenceDart p true)
    ((argumentPermutation F).apply_symm_apply o).symm

/-- From a constraint end, the face successor uses the inverse recovered variable cycle. -/
@[simp] theorem faceNext_incidenceDart_true (r : Graph.RotationSystem (incidenceGraph F))
    (o : F.Occurrence) :
    r.faceNext (incidenceDart o true) =
      incidenceDart ((variablePermutation r).symm o) false := by
  change r.rotate.symm (incidenceDart o false) = _
  rw [Equiv.symm_apply_eq]
  rw [rotate_incidenceDart_false, Equiv.apply_symm_apply]

/-- Coordinates pairing each variable dart with its following incidence-face dart. -/
@[expose] noncomputable def incidenceBlockEquiv (F : CSP Rel V) :
    F.Occurrence × Bool ≃ Graph.Dart (incidenceGraph F) :=
  ((polygonBlockEquiv F).trans (polygonDartEquiv F).symm).trans (incidenceDartEquiv F)

/-- The first member is the original variable dart. -/
@[simp] theorem incidenceBlockEquiv_false (o : F.Occurrence) :
    incidenceBlockEquiv F (o, false) = incidenceDart o false := by
  simp [incidenceBlockEquiv, polygonBlockEquiv, polygonDartEquiv]

/-- The second member is the preceding argument's constraint dart. -/
@[simp] theorem incidenceBlockEquiv_true (o : F.Occurrence) :
    incidenceBlockEquiv F (o, true) =
      incidenceDart ((argumentPermutation F).symm o) true := by
  simp [incidenceBlockEquiv, polygonBlockEquiv, polygonDartEquiv]

/-- Every incidence face alternates the two endpoint sides. Its full permutation is the
explicit doubled square permutation, after changing to these coordinates. -/
theorem faceNext_incidenceBlock (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r) (x : F.Occurrence × Bool) :
    r.faceNext (incidenceBlockEquiv F x) = incidenceBlockEquiv F
      (Equiv.Perm.doubled (incidenceSquarePermutation r) x) := by
  rcases x with ⟨o, b⟩
  cases b <;> simp [Equiv.Perm.doubled, incidenceSquarePermutation, hOrder]

/-- Complete incidence-face correspondence with the square permutation, including fixed
points of the square. There is no selection of favorable face cycles. -/
noncomputable def incidenceFaceOrbitEquiv (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r) :
    r.Face ≃ Quotient (Equiv.Perm.SameCycle.setoid (incidenceSquarePermutation r)) :=
  (Quotient.congr (incidenceBlockEquiv F) (fun x y =>
    (Equiv.Perm.sameCycle_equiv_iff (incidenceBlockEquiv F) _ _
      (fun z => (faceNext_incidenceBlock r hOrder z).symm) x y).symm)).symm.trans
    (Equiv.Perm.doubledOrbitEquiv (incidenceSquarePermutation r))

/-- Sum coordinates distinguish every forward black dart from every backward white dart. -/
@[expose] noncomputable def polygonSumEquiv (F : CSP Rel V) :
    F.Occurrence ⊕ F.Occurrence ≃ Graph.Dart (polygonGraph F) :=
  (((Equiv.boolProdEquivSum F.Occurrence).symm.trans (Equiv.prodComm _ _)).trans
    (polygonBlockEquiv F))

/-- Black coordinates are forward edge ends. -/
@[simp] theorem polygonSumEquiv_inl (o : F.Occurrence) :
    polygonSumEquiv F (.inl o) = polygonDart o false := rfl

/-- White coordinates use the preceding scope edge. -/
@[simp] theorem polygonSumEquiv_inr (o : F.Occurrence) :
    polygonSumEquiv F (.inr o) =
      polygonDart ((argumentPermutation F).symm o) true := rfl

/-- The polygon face permutation splits completely into black scope cycles and white
incidence-square cycles. -/
theorem faceNext_polygonSum (r : Graph.RotationSystem (incidenceGraph F))
    (x : F.Occurrence ⊕ F.Occurrence) :
    (polygonRotation r).faceNext (polygonSumEquiv F x) = polygonSumEquiv F
      (Equiv.sumCongr (argumentPermutation F) (incidenceSquarePermutation r) x) := by
  cases x with
  | inl o => simp
  | inr o => simp [incidenceSquarePermutation]

/-- The full polygon face quotient is the disjoint sum of its black and white orbit
quotients. In particular, no singleton or white face is omitted. -/
noncomputable def polygonFaceOrbitEquiv (r : Graph.RotationSystem (incidenceGraph F)) :
    (polygonRotation r).Face ≃
      Quotient (Equiv.Perm.SameCycle.setoid (argumentPermutation F)) ⊕
        Quotient (Equiv.Perm.SameCycle.setoid (incidenceSquarePermutation r)) :=
  (Quotient.congr (polygonSumEquiv F) (fun x y =>
    (Equiv.Perm.sameCycle_equiv_iff (polygonSumEquiv F) _ _
      (fun z => (faceNext_polygonSum r z).symm) x y).symm)).symm.trans
    (Equiv.Perm.sumOrbitEquiv _ _)

/-- Every positive constraint position, including duplicate constraint records, has exactly
one scope orbit. Nullary constraints are explicitly excluded by the hypothesis. -/
noncomputable def argumentOrbitEquiv (F : CSP Rel V)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) :
    Quotient (Equiv.Perm.SameCycle.setoid (argumentPermutation F)) ≃ Fin F.length where
  toFun := Quotient.lift Sigma.fst (fun _ _ h => sameCycle_argumentPermutation _ _ |>.mp h)
  invFun i := Quotient.mk _ ⟨i, ⟨0, hPos i⟩⟩
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h o => exact Quotient.sound ((sameCycle_argumentPermutation _ _).mpr rfl)
  right_inv _ := rfl

/-- Full face decomposition of the actual constructed rotation: one black face per indexed
positive scope, and one white face per incidence face. -/
noncomputable def polygonFaceEquiv (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) :
    (polygonRotation r).Face ≃ Fin F.length ⊕ r.Face :=
  (polygonFaceOrbitEquiv r).trans
    (Equiv.sumCongr (argumentOrbitEquiv F hPos) (incidenceFaceOrbitEquiv r hOrder).symm)

/-- The black face of an occurrence is indexed by its actual constraint position. -/
theorem polygonFaceEquiv_black (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) (o : F.Occurrence) :
    polygonFaceEquiv r hOrder hPos (Quotient.mk _ (polygonDart o false)) = .inl o.1 := by
  let e : Quotient (Equiv.Perm.SameCycle.setoid
      (Equiv.sumCongr (argumentPermutation F) (incidenceSquarePermutation r))) ≃
      (polygonRotation r).Face := Quotient.congr (polygonSumEquiv F) (fun x y =>
    (Equiv.Perm.sameCycle_equiv_iff (polygonSumEquiv F) _ _
      (fun z => (faceNext_polygonSum r z).symm) x y).symm)
  have h : e.symm (Quotient.mk _ (polygonDart o false)) = Quotient.mk _ (.inl o) :=
    e.symm_apply_apply (Quotient.mk _ (.inl o))
  unfold polygonFaceEquiv polygonFaceOrbitEquiv
  dsimp only [Equiv.trans_apply]
  change (Equiv.sumCongr _ _) ((Equiv.Perm.sumOrbitEquiv _ _) (e.symm _)) = _
  rw [h]
  rfl

/-- The variable dart represents its own square orbit in the incidence-face correspondence. -/
theorem incidenceFaceOrbitEquiv_mk_false (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r) (o : F.Occurrence) :
    incidenceFaceOrbitEquiv r hOrder (Quotient.mk _ (incidenceDart o false)) =
      Quotient.mk _ o := by
  let e : Quotient (Equiv.Perm.SameCycle.setoid
      (Equiv.Perm.doubled (incidenceSquarePermutation r))) ≃ r.Face :=
    Quotient.congr (incidenceBlockEquiv F) (fun x y =>
      (Equiv.Perm.sameCycle_equiv_iff (incidenceBlockEquiv F) _ _
        (fun z => (faceNext_incidenceBlock r hOrder z).symm) x y).symm)
  have h : e.symm (Quotient.mk _ (incidenceDart o false)) = Quotient.mk _ (o, false) := by
    convert e.symm_apply_apply (Quotient.mk _ (o, false)) using 1
    exact congrArg (fun d => e.symm (Quotient.mk _ d)) (incidenceBlockEquiv_false o).symm
  unfold incidenceFaceOrbitEquiv
  dsimp only [Equiv.trans_apply]
  change (Equiv.Perm.doubledOrbitEquiv _) (e.symm _) = _
  rw [h]
  rfl

/-- The exact white correspondence sends `q_(B⁻¹ o)` to the face of the original variable
dart `o`. This states the conjugation, not merely an equality of face counts. -/
theorem polygonFaceEquiv_white (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) (o : F.Occurrence) :
    polygonFaceEquiv r hOrder hPos
      (Quotient.mk _ (polygonDart ((argumentPermutation F).symm o) true)) =
      .inr (Quotient.mk _ (incidenceDart o false)) := by
  let e : Quotient (Equiv.Perm.SameCycle.setoid
      (Equiv.sumCongr (argumentPermutation F) (incidenceSquarePermutation r))) ≃
      (polygonRotation r).Face := Quotient.congr (polygonSumEquiv F) (fun x y =>
    (Equiv.Perm.sameCycle_equiv_iff (polygonSumEquiv F) _ _
      (fun z => (faceNext_polygonSum r z).symm) x y).symm)
  have h : e.symm (Quotient.mk _ (polygonDart ((argumentPermutation F).symm o) true)) =
      Quotient.mk _ (.inr o) := e.symm_apply_apply (Quotient.mk _ (.inr o))
  unfold polygonFaceEquiv polygonFaceOrbitEquiv
  dsimp only [Equiv.trans_apply]
  change (Equiv.sumCongr _ _) ((Equiv.Perm.sumOrbitEquiv _ _) (e.symm _)) = _
  rw [h]
  change Sum.inr ((incidenceFaceOrbitEquiv r hOrder).symm (Quotient.mk _ o)) = _
  apply congrArg Sum.inr
  rw [Equiv.symm_apply_eq]
  exact (incidenceFaceOrbitEquiv_mk_false r hOrder o).symm

/-- Each edge has distinct black and white incident faces, even for a listed loop. -/
theorem polygon_edge_faces_distinct (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) (o : F.Occurrence) :
    (Quotient.mk _ (polygonDart o false) : (polygonRotation r).Face) ≠
      Quotient.mk _ (polygonDart o true) := by
  have hw := polygonFaceEquiv_white r hOrder hPos (argumentPermutation F o)
  rw [Equiv.symm_apply_apply] at hw
  intro h
  have he := congrArg (polygonFaceEquiv r hOrder hPos) h
  rw [polygonFaceEquiv_black, hw] at he
  cases he

/-- The black face at an actual constraint position. Positive scopes provide its darts. -/
@[expose] noncomputable def blackFace (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) (i : Fin F.length) :
    (polygonRotation r).Face := (polygonFaceEquiv r hOrder hPos).symm (.inl i)

/-- The white face corresponding to an original incidence face. -/
@[expose] noncomputable def whiteFace (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) (f : r.Face) :
    (polygonRotation r).Face := (polygonFaceEquiv r hOrder hPos).symm (.inr f)

/-- Every argument dart of a constraint represents its indexed black face. -/
theorem blackFace_eq_mk (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) (o : F.Occurrence) :
    blackFace r hOrder hPos o.1 = Quotient.mk _ (polygonDart o false) := by
  unfold blackFace
  rw [Equiv.symm_apply_eq]
  exact (polygonFaceEquiv_black r hOrder hPos o).symm

/-- A variable dart's incidence face gives the white face on the preceding polygon edge. -/
theorem whiteFace_eq_mk (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) (o : F.Occurrence) :
    whiteFace r hOrder hPos (Quotient.mk _ (incidenceDart o false)) =
      Quotient.mk _ (polygonDart ((argumentPermutation F).symm o) true) := by
  unfold whiteFace
  rw [Equiv.symm_apply_eq]
  exact (polygonFaceEquiv_white r hOrder hPos o).symm

/-- Every face is covered by the indexed black or white map. -/
theorem exists_blackFace_or_whiteFace (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) (f : (polygonRotation r).Face) :
    (∃ i, blackFace r hOrder hPos i = f) ∨ (∃ w, whiteFace r hOrder hPos w = f) := by
  obtain ⟨i | w, h⟩ := (polygonFaceEquiv r hOrder hPos).symm.surjective f
  · exact .inl ⟨i, h⟩
  · exact .inr ⟨w, h⟩

end Cslib.Complexity.CSP
