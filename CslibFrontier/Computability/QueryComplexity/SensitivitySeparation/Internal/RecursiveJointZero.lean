/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveCandidates
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveRepair
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveSets

/-!
# Superquadratic sensitivity separation: recursive joint zero

Bounds the joint sensitivity of two indices `q < q'` of the recursive family at an input where both
are `false`. A bit changing both outputs makes some row clause true at the stronger index `q'`,
hence also at the weaker index `q`, so it repairs a failed condition with respect to the candidate
lists of `q`: either of a target candidate (at most `15`) or of a gate candidate (at most `3`),
in which case the flip changes both gate predicates `F (gateIndex q')` and `F (gateIndex q)` on a
single child.

## Main results

* `recursive_joint_zero_at`: at an input where both indices give `false`, the joint sensitivity is
  at most `15 * sideSensitivity F false + 3 * jointSensitivity F true`.
* `recursive_joint_zero`: the same bound for the `false`-side joint sensitivity of the recursive
  family.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveJointZero.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

open scoped Classical in
/-- For a good labeling `A`, a nested family `F`, `0 < r` and indices `q < q'` at which
`recursiveFamily T A.label F` is `false` on `x`, the joint sensitivity of the two predicates at `x`
is at most `15 * sideSensitivity F false + 3 * jointSensitivity F true`. -/
theorem recursive_joint_zero_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (q q' : Fin h) (hqq : q < q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false)
    (hx' : recursiveFamily T A.label F q' x = false) :
    jointSensitivityAt (recursiveFamily T A.label F q) (recursiveFamily T A.label F q') x ≤
      15 * sideSensitivity F false + 3 * jointSensitivity F true := by
  let TC := targetCandidates T A.label F q x
  let GC := gateCandidates T A.label F q x
  let w := gateWitness T A.label F q x
  let U := TC.biUnion fun i => childChanges F (Fin.last h) x i (targetWitness F x hr i)
  let V := GC.biUnion fun i =>
    childJointChanges F (gateIndex q') (gateIndex q) x (w i) (A.label i (w i))
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T A.label F q (BitString.flipOn {p} x) ≠ recursiveFamily T A.label F q x ∧
      recursiveFamily T A.label F q' (BitString.flipOn {p} x) ≠
        recursiveFamily T A.label F q' x) ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hon' : recursiveFamily T A.label F q' (BitString.flipOn {((j, c), a)} x) = true := by grind
    obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T A.label F q' _).mp hon'
    have hi := rowClause_nested T A.label F hF hqq.le _ i hi'
    have hioff := (recursiveFamily_eq_false_iff T A.label F q x).mp hx i
    rcases rowClause_repair_cases T A.label F q x i j c a hioff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      have hc := targetWitness_unique T A.label F q x hr i hit c htoff
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F (Fin.last h) (BitString.flipOn {a} (recursiveChild x i c)) ≠
          F (Fin.last h) (recursiveChild x i c) := by simp [hton, htoff]
      simpa [childChanges, hc] using hn
    · have hj := gateWitness_unique T A.label F q x i hig j hij hgon
      have hgon' := hF.accepts_of_le (gateIndex_strictAnti hqq).le hgon
      have hgoff' := ((rowClause_eq_true_iff T A.label F q' _ i).mp hi').2 j hij
      rw [recursiveChild_flip_same] at hgoff'
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hig, ?_⟩
      have hn :
          F (gateIndex q') (BitString.flipOn {a} (recursiveChild x j (A.label i j))) ≠
            F (gateIndex q') (recursiveChild x j (A.label i j)) ∧
          F (gateIndex q) (BitString.flipOn {a} (recursiveChild x j (A.label i j))) ≠
            F (gateIndex q) (recursiveChild x j (A.label i j)) := by
        simp [hgon, hgoff, hgon', hgoff']
      simpa [childJointChanges, w, hj] using hn
  have hU : U.card ≤ 15 * sideSensitivity F false :=
    targetCandidates_biUnion_card_le T A F hF hr q x
  have hV : V.card ≤ 3 * jointSensitivity F true := by
    calc
      V.card ≤ GC.card * jointSensitivity F true :=
        Finset.card_biUnion_le_card_mul GC _ _ (fun i hi => by
          rw [childJointChanges_card]
          have hg := (gateWitness_spec T A.label F q x i hi).2
          exact jointSensitivityAt_le_jointSensitivity F true _ _ _
            (gateIndex_strictAnti hqq) (hF.accepts_of_le (gateIndex_strictAnti hqq).le hg) hg)
      _ ≤ 3 * jointSensitivity F true :=
        Nat.mul_le_mul_right _ (gateCandidates_card T A.label F hF q x)
  calc
    jointSensitivityAt (recursiveFamily T A.label F q) (recursiveFamily T A.label F q') x ≤
        (U ∪ V).card := by
      unfold jointSensitivityAt
      convert Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add hU hV

/-- Joint zero-side recurrence: for a good labeling, a nested family `F` and `0 < r`,
`jointSensitivity (recursiveFamily T A.label F) false` is at most
`15 * sideSensitivity F false + 3 * jointSensitivity F true`. -/
theorem recursive_joint_zero {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    jointSensitivity (recursiveFamily T A.label F) false ≤
      15 * sideSensitivity F false + 3 * jointSensitivity F true := by
  apply jointSensitivity_le
  exact fun q q' x hqq hx hx' => recursive_joint_zero_at T A F hF hr q q' hqq x hx hx'

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
