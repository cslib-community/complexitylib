/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Planar.Embedding.Restriction
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionGenus
import Complexity.Foundations.GroupTheory.Perm.RemoveTwo
import Mathlib.Data.List.GetD

/-!
# Executable boundary restriction across one actual edge deletion

The boundary's list-funded first-return program gives exactly the certificate of the
generic directed last-edge deletion. Permutation injectivity bounds each retained first
return by three steps, including loops, cutvertices and empty retained dart sets. Thus the
numerical genus theorem applies to this literal computed table, not an assumed embedding.
This original program-correctness lemma is a prerequisite for actual-body port projection.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Graph Graph.RotationSystem Equiv

/-- The bounded boundary scan reads the exact directed successor after deleting the last
two actual edge ends. A retained dart needs at most three list-funded successor steps. -/
theorem getD_restrictPrefix_deleteLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (d : Dart G) :
    (restrictPrefix (2 * G.2.length) (RotationCertificate.ofRotation r)).successor.getD d.index 0 =
      (r.deleteLastEdge.rotate d).index := by
  let c := RotationCertificate.ofRotation r
  let e := lastEdgeDartEquiv G u v
  let f := e.permCongr r.rotate
  let b := r.deleteLastEdge.rotate d
  have hi : d.index < 2 * G.2.length := (Dart.indexEquiv G d).isLt
  have hb : b.index < 2 * G.2.length := (Dart.indexEquiv G b).isLt
  have hc : 3 ≤ c.successor.length := by
    have := d.1.isLt
    change 3 ≤ (RotationCertificate.ofRotation r).successor.length
    rw [RotationCertificate.length_ofRotation]
    change 3 ≤ 2 * (G.2 ++ [(u, v)]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hold (a : Dart G) : (e.symm (some (some a))).index = a.index := rfl
  have hnone : 2 * G.2.length ≤ (e.symm none).index := by
    change 2 * G.2.length ≤ 2 * G.2.length + 1
    omega
  have hsome : 2 * G.2.length ≤ (e.symm (some none)).index := by
    change 2 * G.2.length ≤ 2 * G.2.length + 0
    omega
  have hstep (z : Option (Option (Dart G))) :
      c.successor.getD (e.symm z).index 0 = (e.symm (f z)).index := by
    rw [RotationCertificate.getD_ofRotation]
    simp only [f, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  have one (h : f (some (some d)) = some (some b)) :
      (restrictPrefix (2 * G.2.length) c).successor.getD d.index 0 = b.index := by
    have hs : c.successor.getD d.index 0 = b.index := by
      simpa only [hold, h] using hstep (some (some d))
    rw [getD_restrictPrefix_one c _ _ hi (by omega) (by rw [hs]; exact hb), hs]
  have two (z : Option (Option (Dart G))) (hz : 2 * G.2.length ≤ (e.symm z).index)
      (h₁ : f (some (some d)) = z) (h₂ : f z = some (some b)) :
      (restrictPrefix (2 * G.2.length) c).successor.getD d.index 0 = b.index := by
    have hs : c.successor.getD d.index 0 = (e.symm z).index := by
      simpa only [hold, h₁] using hstep (some (some d))
    have ht : c.successor.getD (c.successor.getD d.index 0) 0 = b.index := by
      rw [hs]
      simpa only [h₂, hold] using hstep z
    rw [getD_restrictPrefix_two c _ _ hi (by omega) (by rw [hs]; exact hz)
      (by rw [ht]; exact hb), ht]
  have three (z w : Option (Option (Dart G)))
      (hz : 2 * G.2.length ≤ (e.symm z).index)
      (hw : 2 * G.2.length ≤ (e.symm w).index)
      (h₁ : f (some (some d)) = z) (h₂ : f z = w) (h₃ : f w = some (some b)) :
      (restrictPrefix (2 * G.2.length) c).successor.getD d.index 0 = b.index := by
    have hs : c.successor.getD d.index 0 = (e.symm z).index := by
      simpa only [hold, h₁] using hstep (some (some d))
    have ht : c.successor.getD (c.successor.getD d.index 0) 0 = (e.symm w).index := by
      rw [hs]
      exact (hstep z).trans (congrArg (fun a => (e.symm a).index) h₂)
    have hu : c.successor.getD (c.successor.getD (c.successor.getD d.index 0) 0) 0 =
        b.index := by
      rw [ht]
      simpa only [h₃, hold] using hstep w
    rw [getD_restrictPrefix_three c _ _ hi hc (by rw [hs]; exact hz)
      (by rw [ht]; exact hw) (by rw [hu]; exact hb), hu]
  rcases Perm.removeNone_removeNone_paths f d with h | ⟨h, k⟩ | ⟨h, k⟩ |
    ⟨h, k, l⟩ | ⟨h, k, l⟩
  · exact one h
  · exact two none hnone h k
  · exact two (some none) hsome h k
  · exact three none (some none) hnone hsome h k l
  · exact three (some none) none hsome hnone h k l

/-- Exact generated certificates agree, including the empty retained table. The scan's
clock is the original certificate length, independent of binary labels and table values. -/
theorem restrictPrefix_ofRotation_deleteLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) :
    restrictPrefix (2 * G.2.length) (RotationCertificate.ofRotation r) =
      RotationCertificate.ofRotation r.deleteLastEdge := by
  apply congrArg RotationCertificate.mk
  refine List.ext_getElem (by
    change (restrictPrefix (2 * G.2.length) (RotationCertificate.ofRotation r)).successor.length =
      (RotationCertificate.ofRotation r.deleteLastEdge).successor.length
    rw [length_restrictPrefix, RotationCertificate.length_ofRotation]) ?_
  intro i hi hj
  change i <
    (restrictPrefix (2 * G.2.length) (RotationCertificate.ofRotation r)).successor.length at hi
  change i < (RotationCertificate.ofRotation r.deleteLastEdge).successor.length at hj
  change (restrictPrefix (2 * G.2.length) (RotationCertificate.ofRotation r)).successor[i] =
    (RotationCertificate.ofRotation r.deleteLastEdge).successor[i]
  rw [← List.getD_eq_getElem
    (restrictPrefix (2 * G.2.length) (RotationCertificate.ofRotation r)).successor 0 hi,
    ← List.getD_eq_getElem (RotationCertificate.ofRotation r.deleteLastEdge).successor 0 hj]
  have hbound : i < 2 * G.2.length := by rwa [length_restrictPrefix] at hi
  let d := (Dart.indexEquiv G).symm ⟨i, hbound⟩
  have hd : d.index = i := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨i, hbound⟩)
  rw [← hd, getD_restrictPrefix_deleteLastEdge, RotationCertificate.getD_ofRotation]

/-- The actual computed restriction passes the full numerical rotation checker. Source
endpoint declaration and numerical genus suffice, including bridge splits and points. -/
theorem verifyGenusZero_restrictPrefix_deleteLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v))
    (hH : ∀ w ∈ (lastEdgeGraph G u v).incidenceVertices, w ∈ (lastEdgeGraph G u v).1)
    (hr : r.NumericalGenusZero) :
    RotationCertificate.verifyGenusZero G
      (restrictPrefix (2 * G.2.length) (RotationCertificate.ofRotation r)) = true := by
  rw [restrictPrefix_ofRotation_deleteLastEdge]
  apply (RotationCertificate.verifyGenusZero_eq_true_iff _ _).mpr
  refine ⟨RotationCertificate.verifyRotation_ofRotation r.deleteLastEdge
    (endpoints_declared_deleteLastEdge hH), ?_⟩
  rw [RotationCertificate.decode_ofRotation _ (endpoints_declared_deleteLastEdge hH)]
  exact r.numericalGenusZero_deleteLastEdge hH hr

end Cslib.Complexity.CSP.OrderedBoundary
