/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveSets
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Superquadratic sensitivity separation: recursive one

This file proves the recurrences for the profiles of the next-level family at output `true`. At an
accepted input some row clause holds, and only flips inside its `r` target children or its `o`
labeled gate children (one per out-neighbour) can make the next-level predicate reject. Counting the
sensitive coordinates of these children bounds the side profile by
`o * sideSensitivity F false + r * sideSensitivity F true`, and the joint profile by the same
expression with `jointSensitivity F false` in place of `sideSensitivity F false`.

## Main results

* `recursive_sensitivity_one_at`: pointwise sensitivity bound at an accepted input.
* `recursive_side_one`: the side profile of the next-level family at `true` is at most
  `o * sideSensitivity F false + r * sideSensitivity F true`.
* `recursive_joint_one_at`: pointwise joint sensitivity bound at an input accepted at two indices.
* `recursive_joint_one`: for nested `F`, the joint profile of the next-level family at `true` is at
  most `o * jointSensitivity F false + r * sideSensitivity F true`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveOne.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

open scoped Classical in
/-- Counting step shared by the bounds at output `true`. Let every target child of row `i` accept,
and let each coordinate satisfying `P` either change the target value of a target child of row `i`
or lie in the set `S j` of an out-neighbour `j` of `i`, where each such `S j` has at most `s`
elements. Then at most `o * s + r * sideSensitivity F true` coordinates satisfy `P`. -/
private theorem card_filter_le_of_acceptedRow {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (F : Fin (h + 1) → (I → Bool) → Bool) (o s : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (htarget : ∀ c, F (Fin.last h) (recursiveChild x i c) = true)
    (S : Fin k → Finset ((Fin k × Fin r) × I)) (hS : ∀ j, T.Adj i j → (S j).card ≤ s)
    (P : ((Fin k × Fin r) × I) → Prop) [DecidablePred P]
    (hP : ∀ j c a, P ((j, c), a) →
      (j = i ∧ F (Fin.last h) (BitString.flipOn {a} (recursiveChild x j c)) ≠
        F (Fin.last h) (recursiveChild x j c)) ∨ (T.Adj i j ∧ ((j, c), a) ∈ S j)) :
    (Finset.univ.filter P).card ≤ o * s + r * sideSensitivity F true := by
  let U := Finset.univ.biUnion fun c => childChanges F (Fin.last h) x i c
  let V := (Finset.univ.filter (T.Adj i)).biUnion S
  have hsub : Finset.univ.filter P ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    rcases hP j c a (Finset.mem_filter.mp hp).2 with ⟨rfl, ht⟩ | ⟨hij, hjS⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨c, Finset.mem_univ _, by simpa [childChanges] using ht⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, hjS⟩)
  have hU : U.card ≤ r * sideSensitivity F true := by
    simpa [U] using Finset.card_biUnion_le_card_mul Finset.univ
      (fun c => childChanges F (Fin.last h) x i c) (sideSensitivity F true)
      (fun c _ => by
        rw [childChanges_card]
        exact sensitivityAt_le_sideSensitivity F true _ _ (htarget c))
  have hV : V.card ≤ o * s := by
    simpa only [V, ho i] using Finset.card_biUnion_le_card_mul (Finset.univ.filter (T.Adj i)) S s
      (fun j hj => hS j (Finset.mem_filter.mp hj).2)
  calc (Finset.univ.filter P).card ≤ (U ∪ V).card := Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ o * s + r * sideSensitivity F true := by omega

open scoped Classical in
/-- If every vertex of `T` has outdegree `o` and the next-level predicate at index `q` accepts `x`,
then its sensitivity at `x` is at most `o * sideSensitivity F false + r * sideSensitivity F true`.
-/
theorem recursive_sensitivity_one_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true) :
    sensitivityAt (recursiveFamily T label F q) x ≤
      o * sideSensitivity F false + r * sideSensitivity F true := by
  obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff T label F q x).mp hx
  have hcond := (rowClause_eq_true_iff T label F q x i).mp hi
  refine card_filter_le_of_acceptedRow T F o _ ho x i hcond.1
    (fun j => childChanges F (gateIndex q) x j (label i j)) (fun j hij => by
      rw [childChanges_card]
      exact sensitivityAt_le_sideSensitivity F false _ _ (hcond.2 j hij)) _ ?_
  intro j c a hchange
  have hf : recursiveFamily T label F q (BitString.flipOn {((j, c), a)} x) = false := by grind
  have hif := (recursiveFamily_eq_false_iff T label F q _).mp hf i
  have hic : rowClause T label F q (BitString.flipOn {((j, c), a)} x) i ≠
      rowClause T label F q x i := by
    simp [hi, hif]
  rcases rowClause_flip_change T label F q x i j c a hic with ht | ⟨hij, rfl, hg⟩
  · exact Or.inl ht
  · exact Or.inr ⟨hij, by simpa [childChanges] using hg⟩

open scoped Classical in
/-- If every vertex of `T` has outdegree `o`, then the side profile of the next-level family at
`true` is at most `o * sideSensitivity F false + r * sideSensitivity F true`. -/
theorem recursive_side_one {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o) :
    sideSensitivity (recursiveFamily T label F) true ≤
      o * sideSensitivity F false + r * sideSensitivity F true := by
  apply sideSensitivity_le
  exact fun q x hx => recursive_sensitivity_one_at T label F o ho q x hx

open scoped Classical in
/-- Let `F` be nested and every vertex of `T` have outdegree `o`. If `q < q'` and the next-level
predicates at `q` and `q'` both accept `x`, then their joint sensitivity at `x` is at most
`o * jointSensitivity F false + r * sideSensitivity F true`. -/
theorem recursive_joint_one_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (q q' : Fin h) (hqq : q < q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true)
    (hx' : recursiveFamily T label F q' x = true) :
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
      o * jointSensitivity F false + r * sideSensitivity F true := by
  obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx'
  have hi := rowClause_nested T label F hF hqq.le x i hi'
  have hcond := (rowClause_eq_true_iff T label F q x i).mp hi
  have hcond' := (rowClause_eq_true_iff T label F q' x i).mp hi'
  refine card_filter_le_of_acceptedRow T F o _ ho x i hcond.1
    (fun j => childJointChanges F (gateIndex q') (gateIndex q) x j (label i j)) (fun j hij => by
      rw [childJointChanges_card]
      exact jointSensitivityAt_le_jointSensitivity F false _ _ _
        (gateIndex_strictAnti hqq) (hcond'.2 j hij) (hcond.2 j hij)) _ ?_
  intro j c a hchange
  have hf : recursiveFamily T label F q (BitString.flipOn {((j, c), a)} x) = false := by grind
  have hf' : recursiveFamily T label F q' (BitString.flipOn {((j, c), a)} x) = false := by grind
  have hif := (recursiveFamily_eq_false_iff T label F q _).mp hf i
  have hif' := (recursiveFamily_eq_false_iff T label F q' _).mp hf' i
  have hic : rowClause T label F q (BitString.flipOn {((j, c), a)} x) i ≠
      rowClause T label F q x i := by
    simp [hi, hif]
  have hic' : rowClause T label F q' (BitString.flipOn {((j, c), a)} x) i ≠
      rowClause T label F q' x i := by
    simp [hi', hif']
  rcases rowClause_joint_flip_change T label F q q' x i j c a hic hic' with
    ht | ⟨hij, rfl, hg, hg'⟩
  · exact Or.inl ht
  · exact Or.inr ⟨hij, by simpa [childJointChanges] using And.intro hg' hg⟩

open scoped Classical in
/-- If `F` is nested and every vertex of `T` has outdegree `o`, then the joint profile of the
next-level family at `true` is at most `o * jointSensitivity F false + r * sideSensitivity F true`.
-/
theorem recursive_joint_one {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o) :
    jointSensitivity (recursiveFamily T label F) true ≤
      o * jointSensitivity F false + r * sideSensitivity F true := by
  apply jointSensitivity_le
  exact fun q q' x hqq hx hx' => recursive_joint_one_at T label F hF o ho q q' hqq x hx hx'

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
