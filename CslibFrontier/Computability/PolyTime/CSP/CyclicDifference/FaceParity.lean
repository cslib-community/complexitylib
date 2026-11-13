/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.WhiteFaces
import all CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate

/-!
# Parity of the actual compiled black and white scopes

Finite sums retain each indexed edge/dart occurrence. White scopes may be listed in increasing
position order because parity is commutative; black scopes retain the original argument order.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table Cslib.BitString
open Graph.RotationCertificate Graph.RotationSystem

variable {Rel : Type} {F : CSP Rel ℕ}

/-- Exact original ordered scope after replacing its ports by indexed edge positions. -/
theorem blackScope_eq_ofFn (i : Fin F.length) :
    blackScope F i F[i.val].scope =
      List.ofFn (fun j : Fin F[i.val].scope.length => incidenceEdgeIndex (F := F) ⟨i, j⟩) := by
  apply List.ext_getElem
  · simp [blackScope]
  · intro j hj hk
    simp only [blackScope, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [← getElem_argumentPositions (F := F) ⟨i, ⟨j, by simpa using hk⟩⟩]
    exact (argumentPositions_nodup F).idxOf_getElem _ _

/-- Names in a black scope are distinct actual edge positions. -/
theorem blackScope_bounds (i : Fin F.length) :
    (blackScope F i F[i.val].scope).Nodup ∧
      ∀ v ∈ blackScope F i F[i.val].scope, v < F.occurrences.length := by
  rw [blackScope_eq_ofFn]
  refine ⟨List.nodup_ofFn.mpr ?_, ?_⟩
  · intro a b hab
    have he := incidenceEdgeIndex_injective hab
    exact Fin.ext (congrArg (fun o => o.2.val) he)
  · intro v hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    simpa only [incidenceGraph_edges, List.length_map] using
      incidenceEdgeIndex_lt (F := F) ⟨i, j⟩

private theorem faceParity_side (r : Graph.RotationSystem (incidenceGraph F))
    (σ : ℕ → Bool) (o : F.Occurrence) (side : Bool) :
    (polygonRotation r).faceParity (fun i => σ i.val) (Quotient.mk _ (polygonDart o side)) =
      ∑ p : F.Occurrence, if (polygonRotation r).faceNext.SameCycle
        (polygonDart o side) (polygonDart p side) then σ (incidenceEdgeIndex p) else 0 := by
  classical
  rw [faceParity_mk, parityOn_eq_sum, Finset.sum_filter]
  calc
    _ = ∑ a : F.Occurrence × Bool, if (polygonRotation r).faceNext.SameCycle
        (polygonDart o side) (polygonDart a.1 a.2) then σ (incidenceEdgeIndex a.1) else 0 :=
      ((polygonDartEquiv F).sum_comp
        (fun d : Graph.Dart (polygonGraph F) => if (polygonRotation r).faceNext.SameCycle
          (polygonDart o side) d then σ d.1.val else 0)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p _
      rw [Fintype.sum_bool]
      have hcross : ¬ (polygonRotation r).faceNext.SameCycle
          (polygonDart o side) (polygonDart p (!side)) := by
        intro h
        have he := sameCycle_polygon_side r _ _ h
        change side = !side at he
        cases side <;> contradiction
      cases side <;> simp only [Bool.not_false, Bool.not_true] at hcross ⊢ <;>
        simp only [hcross, ↓reduceIte, zero_add, add_zero]

/-- Black face parity is exactly parity of its original cyclic scope. -/
theorem faceParity_black (r : Graph.RotationSystem (incidenceGraph F)) (σ : ℕ → Bool)
    (o : F.Occurrence) :
    (polygonRotation r).faceParity (fun i => σ i.val) (Quotient.mk _ (polygonDart o false)) =
      wordParity ((blackScope F o.1 F[o.1.val].scope).map σ) := by
  classical
  rw [faceParity_side, blackScope_eq_ofFn, List.map_ofFn, wordParity_ofFn, parityOn_eq_sum]
  simp only [sameCycle_black_iff]
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ j : Fin F[o.1.val].scope.length,
        if o.1 = o.1 then σ (incidenceEdgeIndex (F := F) ⟨o.1, j⟩) else 0 := by
      apply Finset.sum_eq_single o.1
      · intro i _ hne
        simp only [Ne.symm hne, ↓reduceIte, Finset.sum_const_zero]
      · simp
    _ = _ := by simp only [↓reduceIte, Function.comp_apply]

/-- White face parity is exactly parity of the complete executable boundary scan. -/
theorem faceParity_white (cert : Graph.RotationCertificate)
    (h : verifyRotation (incidenceGraph F) cert = true) (σ : ℕ → Bool) (o : F.Occurrence) :
    (polygonRotation (decode _ cert h)).faceParity (fun i => σ i.val)
      (Quotient.mk _ (polygonDart o true)) =
        wordParity ((whiteScope F cert (incidenceEdgeIndex o)).map σ) := by
  classical
  rw [faceParity_side, wordParity_eq_sum,
    ← List.sum_toFinset σ (whiteScope_bounds F cert _).1]
  simp only [whiteScope, List.toFinset_filter, List.toFinset_range, Finset.sum_filter]
  apply Finset.sum_bij (fun p _ => incidenceEdgeIndex p)
  · intro p _
    exact Finset.mem_range.mpr (by
      simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt p)
  · intro p _ q _ hpq
    exact incidenceEdgeIndex_injective hpq
  · intro j hj
    obtain ⟨p, hp⟩ := exists_incidenceEdgeIndex (F := F) j (by
      simpa only [incidenceGraph_edges, List.length_map] using Finset.mem_range.mp hj)
    exact ⟨p, Finset.mem_univ _, hp⟩
  · intro p _
    simp only [← sameCycle_white_iff, orbitBool_white cert h]

end Cslib.Complexity.CSP.CyclicCompiler
