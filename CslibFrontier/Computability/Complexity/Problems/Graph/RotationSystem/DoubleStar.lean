/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Star
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Prod

/-!
# Two ordered stars on the same distinct leaves

The two centers see opposite cyclic orders on their common leaves. The second edge block
lists the leaves in reverse, so both center rotations follow their literal edge-list order.
This is the arbitrary-arity skeleton of an atom with its structural exterior probe. Its
numerical proof counts all four-dart faces, including the unary case. At arity zero the two
centers are separate declared points and there are no dart faces.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv

/-- Two centers attached to the same indexed leaves, with the second scope reversed. -/
@[expose] def doubleStarGraph (n : ℕ) : Graph :=
  (List.range (n + 2), (List.finRange n).map (fun i => (i.val, n)) ++
    (List.finRange n).map (fun i => (i.rev.val, n + 1)))

/-- A leaf and a center-block bit identify an actual edge position. -/
@[expose] def doubleStarEdgeEquiv (n : ℕ) : Fin n × Bool ≃ Fin (doubleStarGraph n).2.length :=
  ((Equiv.prodComm _ _).trans (Equiv.boolProdEquivSum (Fin n))).trans
    ((Equiv.sumCongr (Equiv.refl _) (Fin.revPerm : Perm (Fin n))).trans
      (finSumFinEquiv.trans (finCongr (by simp [doubleStarGraph]))))

/-- Leaf/block/end coordinates retain every actual edge occurrence. -/
@[expose] def doubleStarDartEquiv (n : ℕ) : (Fin n × Bool) × Bool ≃ Dart (doubleStarGraph n) :=
  (doubleStarEdgeEquiv n).prodCongr (Equiv.refl Bool)

/-- The first block is in ascending leaf order and the second in descending leaf order. -/
theorem val_doubleStarEdgeEquiv {n : ℕ} (i : Fin n) (b : Bool) :
    (doubleStarEdgeEquiv n (i, b)).val = if b then n + i.rev.val else i.val := by
  cases b <;> rfl

/-- Center names are `n` and `n+1`; both variable ends use the original leaf name. -/
@[simp] theorem vertex_doubleStarDartEquiv {n : ℕ} (i : Fin n) (b s : Bool) :
    (doubleStarDartEquiv n ((i, b), s)).vertex = if s then (if b then n + 1 else n) else i.val := by
  have hlen : (doubleStarGraph n).2.length = n + n := by simp [doubleStarGraph]
  cases b
  · change (if s then ((doubleStarGraph n).2.getD i.val (0, 0)).2
      else ((doubleStarGraph n).2.getD i.val (0, 0)).1) = _
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
    simp [doubleStarGraph, i.isLt]
  · change (if s then ((doubleStarGraph n).2.getD (n + i.rev.val) (0, 0)).2
      else ((doubleStarGraph n).2.getD (n + i.rev.val) (0, 0)).1) = _
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
    have hi := i.isLt
    cases s <;> simp [doubleStarGraph, List.getElem_append_right]; omega

/-- Leaf rotations exchange their two incidences. The first center turns forwards in leaf
coordinates and the second backwards, hence forwards in its reversed scope positions. -/
@[expose] def doubleStarRotor (n : ℕ) : Perm ((Fin n × Bool) × Bool) where
  toFun d := if d.2 then
      ((if d.1.2 then (finRotate n).symm d.1.1 else finRotate n d.1.1, d.1.2), true)
    else ((d.1.1, !d.1.2), false)
  invFun d := if d.2 then
      ((if d.1.2 then finRotate n d.1.1 else (finRotate n).symm d.1.1, d.1.2), true)
    else ((d.1.1, !d.1.2), false)
  left_inv := by
    rintro ⟨⟨i, b⟩, s⟩
    cases b <;> cases s <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv := by
    rintro ⟨⟨i, b⟩, s⟩
    cases b <;> cases s <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply]

private def coordinateVertex {n : ℕ} (d : (Fin n × Bool) × Bool) : ℕ :=
  if d.2 then (if d.1.2 then n + 1 else n) else d.1.1.val

private theorem sameCycle_doubleStarRotor {n : ℕ} (x y : (Fin n × Bool) × Bool) :
    (doubleStarRotor n).SameCycle x y ↔ coordinateVertex x = coordinateVertex y := by
  constructor
  · intro h
    have hm : Function.Semiconj coordinateVertex (doubleStarRotor n) (1 : Perm ℕ) := by
      rintro ⟨⟨i, b⟩, s⟩
      cases b <;> cases s <;> rfl
    exact Perm.sameCycle_one.mp (h.map_of_semiconj hm)
  · rcases x with ⟨⟨i, b⟩, s⟩
    rcases y with ⟨⟨j, c⟩, t⟩
    cases s <;> cases t
    · intro h
      have hij : i = j := Fin.ext h
      subst j
      cases b <;> cases c
      · exact .rfl
      · exact Perm.sameCycle_apply_right.mpr (.rfl : (doubleStarRotor n).SameCycle
          ((i, false), false) ((i, false), false))
      · exact Perm.sameCycle_apply_left.mpr (.rfl : (doubleStarRotor n).SameCycle
          ((i, false), false) ((i, false), false))
      · exact .rfl
    · intro h
      cases c <;> simp only [coordinateVertex, Bool.false_eq_true, ↓reduceIte] at h <;> omega
    · intro h
      cases b <;> simp only [coordinateVertex, Bool.false_eq_true, ↓reduceIte] at h <;> omega
    · intro h
      cases b <;> cases c
      · exact (Perm.sameCycle_finRotate i j).map_of_semiconj
          (u := fun i => ((i, false), true)) (g := doubleStarRotor n) (by intro i; rfl)
      · exact False.elim (by simp [coordinateVertex] at h)
      · exact False.elim (by simp [coordinateVertex] at h)
      · exact (Perm.sameCycle_finRotate i j).inv.map_of_semiconj
          (u := fun i => ((i, true), true)) (g := doubleStarRotor n) (by intro i; rfl)

/-- Actual two-center rotation, preserving the direction of both ordered scopes. -/
@[expose] def doubleStarRotation (n : ℕ) : RotationSystem (doubleStarGraph n) where
  rotate := (doubleStarDartEquiv n).permCongr (doubleStarRotor n)
  sameCycle_iff a b := by
    obtain ⟨⟨⟨i, p⟩, s⟩, rfl⟩ := (doubleStarDartEquiv n).surjective a
    obtain ⟨⟨⟨j, q⟩, t⟩, rfl⟩ := (doubleStarDartEquiv n).surjective b
    rw [Perm.sameCycle_equiv_iff (doubleStarDartEquiv n) (doubleStarRotor n) _
      (by intro a; simp), sameCycle_doubleStarRotor,
      vertex_doubleStarDartEquiv, vertex_doubleStarDartEquiv]
    rfl

/-- Reversal changes only the end bit. -/
@[simp] theorem reverse_doubleStarDartEquiv {n : ℕ} (i : Fin n) (b s : Bool) :
    (doubleStarDartEquiv n ((i, b), s)).reverse = doubleStarDartEquiv n ((i, b), !s) := rfl

private def faceCoordinates (n : ℕ) : (Fin n × Bool) × Bool ≃ (Fin n × Bool) × Bool where
  toFun d := ((if d.1.2 = d.2 then d.1.1 else (finRotate n).symm d.1.1, d.1.2), d.2)
  invFun d := ((if d.1.2 = d.2 then d.1.1 else finRotate n d.1.1, d.1.2), d.2)
  left_inv := by
    rintro ⟨⟨i, b⟩, s⟩
    cases b <;> cases s <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        Equiv.apply_symm_apply]
  right_inv := by
    rintro ⟨⟨i, b⟩, s⟩
    cases b <;> cases s <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        Equiv.symm_apply_apply]

private def faceDartEquiv (n : ℕ) : (Fin n × Bool) × Bool ≃ Dart (doubleStarGraph n) :=
  (faceCoordinates n).trans (doubleStarDartEquiv n)

private theorem face_semiconj (n : ℕ) : Function.Semiconj (faceDartEquiv n)
    (Perm.doubled (Perm.doubled (1 : Perm (Fin n)))) (doubleStarRotation n).faceNext := by
  rintro ⟨⟨i, b⟩, s⟩
  apply (doubleStarRotation n).rotate.injective
  change _ = (doubleStarRotation n).rotate ((doubleStarRotation n).rotate.symm
    (faceDartEquiv n ((i, b), s)).reverse)
  rw [Equiv.apply_symm_apply]
  cases b <;> cases s <;>
    simp only [faceDartEquiv, faceCoordinates, doubleStarRotation, doubleStarRotor,
      Perm.doubled, Equiv.trans_apply, Equiv.permCongr_apply, Equiv.coe_fn_mk,
      Perm.one_apply, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Bool.not_false,
      Bool.not_true, reverse_doubleStarDartEquiv]

/-- Each leaf contributes one four-dart face, with no exceptional degree bound. The nullary
graph has no dart face, although its two point components have conventional faces. -/
theorem card_faces_doubleStarRotation (n : ℕ) : Nat.card (doubleStarRotation n).Face = n := by
  have eqv : Quotient (Perm.SameCycle.setoid
      (Perm.doubled (Perm.doubled (1 : Perm (Fin n))))) ≃ (doubleStarRotation n).Face :=
    Quotient.congr (faceDartEquiv n)
      (fun x y => (Perm.sameCycle_equiv_iff (faceDartEquiv n) _ _ (face_semiconj n) x y).symm)
  have he := Nat.card_congr eqv
  rw [← he, Nat.card_congr (Perm.doubledOrbitEquiv _),
    Nat.card_congr (Perm.doubledOrbitEquiv _)]
  have e : Fin n ≃ Quotient (Perm.SameCycle.setoid (1 : Perm (Fin n))) :=
    Equiv.ofBijective (Quotient.mk _) ⟨fun _ _ h => Perm.sameCycle_one.mp (Quotient.exact h),
      Quotient.mk_surjective⟩
  rw [← Nat.card_congr e, Nat.card_fin]

/-- Both centers and every leaf are declared, also at zero arity. -/
theorem doubleStarGraph_endpoints_declared (n : ℕ) :
    ∀ v ∈ (doubleStarGraph n).incidenceVertices, v ∈ (doubleStarGraph n).1 := by
  intro v hv
  obtain ⟨edge, he, hv⟩ := List.mem_flatMap.mp hv
  rcases List.mem_append.mp he with he | he
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> simp [doubleStarGraph, i.isLt, Nat.lt_add_right]
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · simpa only [doubleStarGraph, List.mem_range] using
        lt_trans i.rev.isLt (by omega : n < n + 2)
    · simp [doubleStarGraph]

/-- At positive arity the two centers are joined through a real leaf. The nullary centers
remain separate points and are deliberately excluded from this connectedness statement. -/
theorem doubleStarGraph_connected {n : ℕ} (hn : 0 < n) :
    ∀ u ∈ (doubleStarGraph n).1, ∀ v ∈ (doubleStarGraph n).1,
      Graph.RotationCertificate.SameComponent (doubleStarGraph n) u v := by
  let i : Fin n := ⟨0, hn⟩
  have hG := doubleStarGraph_endpoints_declared n
  have ha := sameComponent_reverse hG (doubleStarDartEquiv n ((i, false), false))
  have hb := sameComponent_reverse hG (doubleStarDartEquiv n ((i, true), false))
  simp only [reverse_doubleStarDartEquiv, vertex_doubleStarDartEquiv, Bool.not_false,
    Bool.false_eq_true, ↓reduceIte] at ha hb
  have hc := ha.symm.trans hb
  have connect (u : ℕ) (hu : u ∈ (doubleStarGraph n).1) :
      Graph.RotationCertificate.SameComponent (doubleStarGraph n) u n := by
    by_cases h : u < n
    · have hh := sameComponent_reverse hG
        (doubleStarDartEquiv n ((⟨u, h⟩, false), false))
      simpa only [reverse_doubleStarDartEquiv, vertex_doubleStarDartEquiv, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte] using hh
    · have hu' : u < n + 2 := by simpa only [doubleStarGraph, List.mem_range] using hu
      have he : u = n ∨ u = n + 1 := by omega
      rcases he with rfl | rfl
      · exact .refl (by simp [doubleStarGraph])
      · exact hc.symm
  intro u hu v hv
  exact (connect u hu).trans (connect v hv).symm

/-- The literal two-star rotation has componentwise numerical genus zero at every arity.
At zero arity the conventional faces belong to the two point components, not the dart quotient. -/
theorem numericalGenusZero_doubleStarRotation (n : ℕ) :
    (doubleStarRotation n).NumericalGenusZero := by
  by_cases hn : 0 < n
  · rw [numericalGenusZero_iff_connected_euler (doubleStarRotation n)
      (doubleStarGraph_endpoints_declared n) (doubleStarGraph_connected hn)
      (doubleStarDartEquiv n ((⟨0, hn⟩, false), false)), card_faces_doubleStarRotation]
    simp only [doubleStarGraph, List.length_append, List.length_map, List.length_finRange]
    rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
    omega
  · have he : n = 0 := by omega
    subst n
    intro root _
    have hd : ¬ ∃ d : Dart (doubleStarGraph 0), d.vertex = root := by
      rintro ⟨d, -⟩
      exact d.1.elim0
    simp only [hd, ite_false]

end Cslib.Complexity.Graph.RotationSystem
