/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CornerInsertion
public import Complexity.Foundations.GroupTheory.Perm.CycleSurgery

/-!
# Face cycles of insertion at specified corners

These original permutation identities count all face cycles, including singleton faces.
Inserting an edge between two corners on the same face increases the face count by one;
insertion between different faces decreases it by one. Cofaciality is essential, even when
both corners belong to the same vertex. Coincident corners are treated explicitly.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv Perm.Insertion Perm.CycleSurgery


/-- Appending an indexed edge preserves reversal on old ends and interchanges exactly the
new two ends. The equation uses the same edge/end coordinates as `insertEdge`. -/
theorem cornerDartEquiv_reverse {G : Graph} (h k : Dart G) (d : Dart (cornerGraph h k)) :
    cornerDartEquiv h k d.reverse =
      (((Dart.reversal G).optionCongr.optionCongr * swap (some none) none) :
        Perm (Option (Option (Dart G))))
        (cornerDartEquiv h k d) := by
  obtain ⟨z, rfl⟩ := (cornerDartEquiv h k).symm.surjective d
  rcases z with _ | (_ | ⟨i, b⟩)
  · simp [cornerDartEquiv, appendedDartEquiv, Dart.reverse]
  · simp [cornerDartEquiv, appendedDartEquiv, Dart.reverse]
  · cases b <;> simp [cornerDartEquiv, appendedDartEquiv, Dart.reverse, i.isLt,
      swap_apply_def, Dart.reversal]

/-- The actual generated rotation in the old-plus-two-new-darts coordinates. -/
theorem cornerDartEquiv_rotate {G : Graph} (r : RotationSystem G) (h k : Dart G) :
    (cornerDartEquiv h k).permCongr (r.insertEdge h k).rotate =
      insertAfter (insertAfter r.rotate h) (some k) := by
  apply Equiv.ext
  intro z
  simp [insertEdge]

/-- Exact reversal conjugacy for the appended listed edge. -/
theorem cornerDartEquiv_reversal {G : Graph} (h k : Dart G) :
    (cornerDartEquiv h k).permCongr (Dart.reversal (cornerGraph h k)) =
      (Dart.reversal G).optionCongr.optionCongr * swap (some none) none := by
  apply Equiv.ext
  intro z
  change cornerDartEquiv h k ((cornerDartEquiv h k).symm z).reverse = _
  simpa only [Equiv.apply_symm_apply] using
    cornerDartEquiv_reverse h k ((cornerDartEquiv h k).symm z)

private theorem optionFaceNext {G : Graph} (r : RotationSystem G) :
    r.faceNext.optionCongr.optionCongr =
      (r.rotate.optionCongr.optionCongr : Perm (Option (Option (Dart G))))⁻¹ *
        (Dart.reversal G).optionCongr.optionCongr := by
  apply Equiv.ext
  intro z
  rcases z with _ | (_ | a) <;> rfl

private theorem faceNext_eq_mul {G : Graph} (r : RotationSystem G) :
    r.faceNext = r.rotate⁻¹ * Dart.reversal G := rfl

/-- Exact conjugacy of the generated face permutation, with the original chirality.
No same-face or same-vertex hypothesis is used in this successor identity. -/
theorem faceNext_insertEdge {G : Graph} (r : RotationSystem G) (h k : Dart G) :
    (cornerDartEquiv h k).permCongr (r.insertEdge h k).faceNext =
      Equiv.Perm.CycleSurgery.splice r.faceNext h k := by
  have hi : (cornerDartEquiv h k).permCongr ((r.insertEdge h k).rotate⁻¹) =
      ((cornerDartEquiv h k).permCongr (r.insertEdge h k).rotate)⁻¹ :=
    map_inv (cornerDartEquiv h k).permCongrHom _
  rw [faceNext_eq_mul (r.insertEdge h k)]
  rw [Equiv.permCongr_mul, hi, cornerDartEquiv_rotate, cornerDartEquiv_reversal,
    insertAfter_twice, Equiv.Perm.CycleSurgery.splice, optionFaceNext]
  simp only [mul_inv_rev, swap_inv, mul_assoc]

/-- Inserting an edge at cofacial existing dart corners adds exactly one face, including
when the selected corners are identical. -/
theorem card_faces_insertEdge_cofacial {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hc : r.faceNext.SameCycle h k) :
    Nat.card (r.insertEdge h k).Face = Nat.card r.Face + 1 := by
  have he := card_orbits_permCongr (cornerDartEquiv h k) (r.insertEdge h k).faceNext
  rw [faceNext_insertEdge] at he
  rw [← he]
  exact Equiv.Perm.CycleSurgery.card_orbits_splice_sameCycle r.faceNext h k hc

/-- Inserting between different face cycles merges them. This includes joining components;
in one component it is the count responsible for increasing the numerical genus. -/
theorem card_faces_insertEdge_different_faces {G : Graph} (r : RotationSystem G)
    (h k : Dart G) (hc : ¬ r.faceNext.SameCycle h k) :
    Nat.card (r.insertEdge h k).Face + 1 = Nat.card r.Face := by
  have he := card_orbits_permCongr (cornerDartEquiv h k) (r.insertEdge h k).faceNext
  rw [faceNext_insertEdge] at he
  rw [← he]
  exact Equiv.Perm.CycleSurgery.card_orbits_splice_of_not_sameCycle r.faceNext h k hc

end Cslib.Complexity.Graph.RotationSystem
