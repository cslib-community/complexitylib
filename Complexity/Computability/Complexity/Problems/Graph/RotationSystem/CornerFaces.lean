/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CornerInsertion
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CycleSplice

/-!
# Face cycles of insertion at specified corners

These original permutation identities count all face cycles, including singleton faces.
Inserting an edge between two corners on the same face increases the face count by one;
insertion between different faces decreases it by one. Cofaciality is essential, even when
both corners belong to the same vertex. Coincident corners are treated explicitly.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv DartInsertion CycleSplice

namespace CornerFaces

variable {α : Type} [DecidableEq α]

/-- The literal face successor after inserting the two edge ends. `some none` is the first
new end and `none` the second; the remaining points are old indexed darts. -/
@[expose] def splice (f : Perm α) (h k : α) : Perm (Option (Option α)) :=
  swap (some (some k)) none * swap (some (some h)) (some none) *
    f.optionCongr.optionCongr * swap (some none) none

/-- Deleting the second new end leaves the first inserted before `k`, in the permutation
whose incoming successors at `h` and `k` have been interchanged. This holds also for `h=k`. -/
theorem removeNone_splice (f : Perm α) (h k : α) :
    removeNone (splice f h k) =
      swap (some k) none * (swap h k * f).optionCongr := by
  apply Equiv.optionCongr_injective
  rw [map_equiv_removeNone]
  apply Equiv.ext
  intro z
  rcases z with _ | (_ | a)
  · simp [splice, swap_apply_def]
  · by_cases hk : h = k
    · simp [splice, swap_apply_def, hk]
    · simpa [splice, swap_apply_def, hk] using Ne.symm hk
  · by_cases hah : f a = h
    · by_cases hk : h = k <;> simp [splice, swap_apply_def, hah, hk]
    · by_cases hak : f a = k
      · have hkh : k ≠ h := by intro he; exact hah (hak.trans he)
        simp [splice, swap_apply_def, hak, hkh, hkh.symm]
      · simp [splice, swap_apply_def, hah, hak]

/-- The first inserted end is never a singleton face after deleting the second end. -/
theorem removeNone_splice_none (f : Perm α) (h k : α) :
    removeNone (splice f h k) none = some k := by
  rw [removeNone_splice]
  simp

/-- The second inserted end is a singleton face exactly for coincident corners. -/
theorem splice_none_fixed_iff (f : Perm α) (h k : α) :
    splice f h k none = none ↔ h = k := by
  by_cases hk : h = k
  · subst k; simp [splice]
  · simp [splice, swap_apply_def, hk]

/-- Removing both inserted ends leaves precisely the incoming-successor swap. -/
theorem removeNone_removeNone_splice (f : Perm α) (h k : α) :
    removeNone (removeNone (splice f h k)) = swap h k * f := by
  apply Equiv.optionCongr_injective
  rw [map_equiv_removeNone, removeNone_splice_none, removeNone_splice]
  rw [← mul_assoc, swap_comm none (some k), swap_mul_self, one_mul]

/-- Exact face count before distinguishing the equal-corner and two-corner cases. -/
theorem card_orbits_splice [Finite α] (f : Perm α) (h k : α) :
    Nat.card (Quotient (Perm.SameCycle.setoid (splice f h k))) =
      Nat.card (Quotient (Perm.SameCycle.setoid (swap h k * f))) +
        if h = k then 1 else 0 := by
  have h₁ := card_orbits_removeNone_add (splice f h k)
  have h₂ := card_orbits_removeNone (removeNone (splice f h k))
    (by rw [removeNone_splice_none]; simp)
  rw [removeNone_removeNone_splice] at h₂
  rw [← h₂] at h₁
  simpa only [splice_none_fixed_iff] using h₁

/-- Cofacial corners, including coincident corners, gain exactly one face. -/
theorem card_orbits_splice_cofacial [Finite α] (f : Perm α) (h k : α)
    (hc : f.SameCycle h k) :
    Nat.card (Quotient (Perm.SameCycle.setoid (splice f h k))) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) + 1 := by
  rw [card_orbits_splice]
  by_cases hk : h = k
  · subst k; rw [swap_self]; simp only [↓reduceIte]; rfl
  · have he := (card_orbits_swap_mul f h k hk).1 hc
    simp only [hk, ite_false, Nat.add_zero, he]

/-- Different face cycles merge, so the total face count decreases by one. -/
theorem card_orbits_splice_different_faces [Finite α] (f : Perm α) (h k : α)
    (hc : ¬ f.SameCycle h k) :
    Nat.card (Quotient (Perm.SameCycle.setoid (splice f h k))) + 1 =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) := by
  have hk : h ≠ k := fun he => hc (he ▸ Perm.SameCycle.rfl)
  rw [card_orbits_splice]
  simp only [hk, ite_false, Nat.add_zero]
  exact (card_orbits_swap_mul f h k hk).2 hc

end CornerFaces

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

private theorem insertAfter_twice {α : Type} [DecidableEq α] (f : Perm α) (h k : α) :
    insertAfter (insertAfter f h) (some k) = f.optionCongr.optionCongr *
      swap (some (some h)) (some none) * swap (some (some k)) none := by
  have hm : (f.optionCongr * swap (some h) none).optionCongr =
      f.optionCongr.optionCongr * (swap (some h) none).optionCongr := by
    apply Equiv.ext
    rintro (_ | z) <;> rfl
  dsimp only [insertAfter]
  rw [hm, Equiv.optionCongr_swap]

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
      CornerFaces.splice r.faceNext h k := by
  have hi : (cornerDartEquiv h k).permCongr ((r.insertEdge h k).rotate⁻¹) =
      ((cornerDartEquiv h k).permCongr (r.insertEdge h k).rotate)⁻¹ :=
    map_inv (cornerDartEquiv h k).permCongrHom _
  rw [faceNext_eq_mul (r.insertEdge h k)]
  rw [Equiv.permCongr_mul, hi, cornerDartEquiv_rotate, cornerDartEquiv_reversal,
    insertAfter_twice, CornerFaces.splice, optionFaceNext]
  simp only [mul_inv_rev, swap_inv, mul_assoc]

/-- Inserting an edge at cofacial existing dart corners adds exactly one face, including
when the selected corners are identical. -/
theorem card_faces_insertEdge_cofacial {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hc : r.faceNext.SameCycle h k) :
    Nat.card (r.insertEdge h k).Face = Nat.card r.Face + 1 := by
  have he := card_orbits_permCongr (cornerDartEquiv h k) (r.insertEdge h k).faceNext
  rw [faceNext_insertEdge] at he
  rw [← he]
  exact CornerFaces.card_orbits_splice_cofacial r.faceNext h k hc

/-- Inserting between different face cycles merges them. This includes joining components;
in one component it is the count responsible for increasing the numerical genus. -/
theorem card_faces_insertEdge_different_faces {G : Graph} (r : RotationSystem G)
    (h k : Dart G) (hc : ¬ r.faceNext.SameCycle h k) :
    Nat.card (r.insertEdge h k).Face + 1 = Nat.card r.Face := by
  have he := card_orbits_permCongr (cornerDartEquiv h k) (r.insertEdge h k).faceNext
  rw [faceNext_insertEdge] at he
  rw [← he]
  exact CornerFaces.card_orbits_splice_different_faces r.faceNext h k hc

end Cslib.Complexity.Graph.RotationSystem
