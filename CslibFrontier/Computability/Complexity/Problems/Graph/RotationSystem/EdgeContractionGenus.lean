/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContraction
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Differences
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FacePotential
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Lifting
import CslibFrontier.Foundations.GroupTheory.Perm.RemoveNoneExtension
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionGenus

/-!
# Numerical genus under arbitrary nonloop contraction

The literal incoming/outgoing face swaps permit extension of every retained face-even
label with zero on the contracted edge. Vertex-spin lifting then descends through the
actual endpoint identification. This original algebraic proof uses neither a bridge nor
a cofacial hypothesis and includes empty residual dart sets and isolated declarations.
It concerns the existing componentwise numerical predicate, without a geometric claim.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv

/-- Face-even labels extend across directed nonloop contraction with zero on the selected
edge and the original labels on all retained indexed occurrences. -/
theorem exists_faceEven_extension_contractLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (x : Fin (contractLastEdgeGraph G u v).2.length → Bool)
    (hx : (r.contractLastEdge huv).FaceEven x) :
    ∃ y : Fin (lastEdgeGraph G u v).2.length → Bool, r.FaceEven y ∧
      y (lastEdgeDart G u v false).1 = false ∧
      ∀ d : Dart (contractLastEdgeGraph G u v),
        y (((contractLastEdgeDartEquiv G u v).trans
          (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)).symm
            (some (some d))).1 = x d.1 := by
  obtain ⟨p, hp⟩ := (r.contractLastEdge huv).exists_facePotential_of_faceEven x hx
  let e := (contractLastEdgeDartEquiv G u v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)
  let A : Perm (Option (Option (Dart (contractLastEdgeGraph G u v)))) := swap (some none) none
  let f := e.permCongr r.faceNext
  let g := A * f * A
  let q := Perm.extendRemoveNone (removeNone g) p false
  let P := Perm.extendRemoveNone g q false
  have houter : P (g none) = P none := (Perm.extendRemoveNone_none g q false).symm
  have hinner : P (g (some none)) = P (some none) := by
    calc
      P (g (some none)) = q (removeNone g none) :=
        Perm.extendRemoveNone_apply_some g q false none
      _ = q none := (Perm.extendRemoveNone_none (removeNone g) p false).symm
      _ = P (some none) := (Perm.extendRemoveNone_some g q false none).symm
  have hold (a : Dart (contractLastEdgeGraph G u v)) : P (some (some a)) = p a := by
    simp only [P, q, Perm.extendRemoveNone_some]
  have hnext (a : Dart (contractLastEdgeGraph G u v)) :
      P (g (some (some a))) = p ((r.contractLastEdge huv).faceNext a) := by
    calc
      P (g (some (some a))) = q (removeNone g (some a)) :=
        Perm.extendRemoveNone_apply_some g q false (some a)
      _ = p (removeNone (removeNone g) a) :=
        Perm.extendRemoveNone_apply_some (removeNone g) p false a
      _ = p ((r.contractLastEdge huv).faceNext a) :=
        congrArg (fun h : Perm (Dart (contractLastEdgeGraph G u v)) => p (h a))
          (r.faceNext_contractLastEdge huv).symm
  have hrestore (z : Option (Option (Dart (contractLastEdgeGraph G u v)))) :
      A (f z) = g (A z) := by
    simp only [g, Perm.coe_mul, Function.comp_apply, A, swap_apply_self]
  let y (i : Fin (lastEdgeGraph G u v).2.length) : Bool :=
    if h : i.val < (contractLastEdgeGraph G u v).2.length then x ⟨i.val, h⟩ else false
  have hyOuter : y (e.symm none).1 = false := by
    change (if h : (contractLastEdgeGraph G u v).2.length <
      (contractLastEdgeGraph G u v).2.length then _ else false) = false
    rw [dite_eq_right (Nat.lt_irrefl _)]
  have hyInner : y (e.symm (some none)).1 = false := by
    change (if h : (contractLastEdgeGraph G u v).2.length <
      (contractLastEdgeGraph G u v).2.length then _ else false) = false
    rw [dite_eq_right (Nat.lt_irrefl _)]
  have hyOld (a : Dart (contractLastEdgeGraph G u v)) :
      y (e.symm (some (some a))).1 = x a.1 := by
    change (if h : a.1.val < (contractLastEdgeGraph G u v).2.length then x ⟨a.1.val, h⟩
      else false) = x a.1
    rw [dite_eq_left a.1.isLt]
  refine ⟨y, ?_, ?_, hyOld⟩
  · apply r.faceEven_of_facePotential y (fun d => P (A (e d)))
    intro d
    obtain ⟨z, rfl⟩ := e.symm.surjective d
    rw [Equiv.apply_symm_apply]
    change y (e.symm z).1 = (P (A z) ^^ P (A (f z)))
    rw [hrestore]
    rcases z with _ | (_ | a)
    · rw [show A none = some none from swap_apply_right _ _, hinner, hyOuter]
      exact (Bool.xor_self _).symm
    · rw [show A (some none) = none from swap_apply_left _ _, houter, hyInner]
      exact (Bool.xor_self _).symm
    · rw [show A (some (some a)) = some (some a) from
        swap_apply_of_ne_of_ne (by simp) (by simp), hnext, hold, hyOld]
      exact hp a
  · change (if h : G.2.length < (contractLastEdgeGraph G u v).2.length then _ else false) = false
    rw [dite_eq_right (by simp [contractLastEdgeGraph, Graph.relabel])]

/-- All retained endpoints remain declared after contracting an actual nonloop edge. -/
theorem endpoints_declared_contractLastEdge {G : Graph} {u v : ℕ}
    (hH : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ (lastEdgeGraph G u v).1) :
    ∀ w ∈ (contractLastEdgeGraph G u v).incidenceVertices,
      w ∈ (contractLastEdgeGraph G u v).1 :=
  G.endpoints_declared_relabel (Function.update id u v) (endpoints_declared_deleteLastEdge hH)

/-- Contracting any actual indexed nonloop edge preserves componentwise numerical genus
zero. No bridge, cofacial, connectedness or face-even lifting provider is a premise. The
point convention is handled by the existing algebraic characterization, without new darts. -/
theorem numericalGenusZero_contractLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (hH : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ (lastEdgeGraph G u v).1)
    (hr : r.NumericalGenusZero) : (r.contractLastEdge huv).NumericalGenusZero := by
  apply (r.contractLastEdge huv).numericalGenusZero_of_faceEven_lifts
    (endpoints_declared_contractLastEdge hH)
  intro x hx
  obtain ⟨y, hy, hy0, hxy⟩ := r.exists_faceEven_extension_contractLastEdge huv x hx
  obtain ⟨spin, hspin⟩ := r.exists_vertexSpins_of_faceEven hH hr y hy
  have hzero := Graph.edgeGradient_dart (lastEdgeGraph G u v) spin (lastEdgeDart G u v false)
  rw [reverse_lastEdgeDart, vertex_lastEdgeDart, vertex_lastEdgeDart,
    hspin, hy0] at hzero
  change false = (spin u ^^ spin v) at hzero
  have huvSpin : spin u = spin v := by
    cases hu : spin u <;> cases hv : spin v
    · rfl
    · rw [hu, hv] at hzero
      contradiction
    · rw [hu, hv] at hzero
      contradiction
    · rfl
  have hmap (w : ℕ) : spin (Function.update id u v w) = spin w := by
    by_cases hw : w = u
    · subst w
      simpa only [Function.update_self] using huvSpin.symm
    · rw [Function.update_of_ne hw]
      rfl
  refine ⟨spin, funext fun i => ?_⟩
  let d : Dart (contractLastEdgeGraph G u v) := (i, false)
  let e := (contractLastEdgeDartEquiv G u v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)
  let a := e.symm (some (some d))
  have he : contractLastEdgeDartEquiv G u v a =
      retainedLastEdgeDart (contractLastEdgeGraph G u v) v v d := by
    apply (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v).injective
    rw [retainedLastEdgeDart, Equiv.apply_symm_apply]
    exact e.apply_symm_apply (some (some d))
  have hv : Function.update id u v a.vertex = d.vertex := by
    rw [← vertex_contractLastEdgeDartEquiv, he, vertex_retainedLastEdgeDart]
  have heRev : contractLastEdgeDartEquiv G u v a.reverse =
      retainedLastEdgeDart (contractLastEdgeGraph G u v) v v d.reverse := by
    rw [reverse_contractLastEdgeDartEquiv, he, ← retainedLastEdgeDart_reverse]
  have hvRev : Function.update id u v a.reverse.vertex = d.reverse.vertex := by
    rw [← vertex_contractLastEdgeDartEquiv, heRev, vertex_retainedLastEdgeDart]
  have hs := Graph.edgeGradient_dart (lastEdgeGraph G u v) spin a
  have ht := Graph.edgeGradient_dart (contractLastEdgeGraph G u v) spin d
  rw [← hv, ← hvRev, hmap, hmap] at ht
  exact ht.trans (hs.symm.trans ((congrFun hspin a.1).trans (hxy d)))

end Cslib.Complexity.Graph.RotationSystem
