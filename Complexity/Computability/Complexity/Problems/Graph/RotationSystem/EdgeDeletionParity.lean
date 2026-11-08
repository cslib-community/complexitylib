/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletion
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.FacePotential
import Complexity.Foundations.GroupTheory.Perm.RemoveNoneExtension

/-!
# Extending face-even labels across an edge deletion

The actual deleted rotation supplies a potential on its face darts. Extend that potential
over both removed points with zero differences, then undo the literal face-successor swap.
The two restored edge ends receive the same bit. This works for bridge splits, pendant
endpoints, loops, disconnected components and empty residual dart sets. No face-location,
connectedness, endpoint-declaration or genus premise is required for the parity extension.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv

/-- Every face-even labeling of the actual deleted graph extends to a face-even labeling
of the original graph, retaining every old edge position. The bit on the removed edge is
constructed from face-dart potentials; no lifting or embedding provider is a premise. -/
theorem exists_faceEven_extension_deleteLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (x : Fin G.2.length → Bool)
    (hx : r.deleteLastEdge.FaceEven x) :
    ∃ y : Fin (lastEdgeGraph G u v).2.length → Bool, r.FaceEven y ∧
      ∀ i : Fin G.2.length, y (retainedLastEdgeDart G u v (i, false)).1 = x i := by
  obtain ⟨p, hp⟩ := r.deleteLastEdge.exists_facePotential_of_faceEven x hx
  let e := lastEdgeDartEquiv G u v
  let f := e.permCongr r.faceNext
  let g := f * swap (some none) none
  let q := Perm.extendRemoveNone (removeNone g) p false
  let P := Perm.extendRemoveNone g q false
  have houter : P (g none) = P none := (Perm.extendRemoveNone_none g q false).symm
  have hinner : P (g (some none)) = P (some none) := by
    calc
      P (g (some none)) = q (removeNone g none) :=
        Perm.extendRemoveNone_apply_some g q false none
      _ = q none := (Perm.extendRemoveNone_none (removeNone g) p false).symm
      _ = P (some none) := (Perm.extendRemoveNone_some g q false none).symm
  have hold (a : Dart G) : P (some (some a)) = p a := by
    simp only [P, q, Perm.extendRemoveNone_some]
  have hnext (a : Dart G) : P (g (some (some a))) = p (r.deleteLastEdge.faceNext a) := by
    calc
      P (g (some (some a))) = q (removeNone g (some a)) :=
        Perm.extendRemoveNone_apply_some g q false (some a)
      _ = p (removeNone (removeNone g) a) :=
        Perm.extendRemoveNone_apply_some (removeNone g) p false a
      _ = p (r.deleteLastEdge.faceNext a) :=
        congrArg (fun h : Perm (Dart G) => p (h a)) r.faceNext_deleteLastEdge.symm
  have hrestore (z : Option (Option (Dart G))) : f z = g (swap (some none) none z) := by
    simp only [g, Perm.coe_mul, Function.comp_apply, swap_apply_self]
  let bit := P (some none) ^^ P none
  let y (i : Fin (lastEdgeGraph G u v).2.length) : Bool :=
    if h : i.val < G.2.length then x ⟨i.val, h⟩ else bit
  have hyOuter : y (e.symm none).1 = bit := by
    change (if _ : G.2.length < G.2.length then _ else bit) = bit
    rw [dite_eq_right (Nat.lt_irrefl _)]
  have hyInner : y (e.symm (some none)).1 = bit := by
    change (if _ : G.2.length < G.2.length then _ else bit) = bit
    rw [dite_eq_right (Nat.lt_irrefl _)]
  have hyOld (a : Dart G) : y (e.symm (some (some a))).1 = x a.1 := by
    change (if h : a.1.val < G.2.length then x ⟨a.1.val, h⟩ else bit) = x a.1
    rw [dite_eq_left a.1.isLt]
  refine ⟨y, ?_, fun i => hyOld (i, false)⟩
  apply r.faceEven_of_facePotential y (fun d => P (e d))
  intro d
  obtain ⟨z, rfl⟩ := e.symm.surjective d
  rw [Equiv.apply_symm_apply]
  change y (e.symm z).1 = (P z ^^ P (f z))
  rw [hrestore]
  rcases z with _ | (_ | a)
  · rw [swap_apply_right, hinner, hyOuter]
    exact Bool.xor_comm _ _
  · rw [swap_apply_left, houter, hyInner]
  · rw [swap_apply_of_ne_of_ne (by simp) (by simp), hnext, hold, hyOld]
    exact hp a

end Cslib.Complexity.Graph.RotationSystem
