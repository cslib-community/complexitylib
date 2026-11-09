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
# Superquadratic sensitivity separation: recursive zero

Bounds the sensitivity of the recursive family at inputs where it is `false`. A sensitive bit must
repair the unique failed condition of some row clause: of a target candidate (at most `15`), of
the gate sink (at most one), or of a non-sink gate candidate (at most `3`). In the last case the
gate witness is itself a gate candidate, so the flip changes both the gate and the final predicate
on a single child, which is charged to the joint sensitivity.

## Main results

* `recursive_sensitivity_zero_at`: at an input with output `false`, the sensitivity is at most
  `15 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true`.
* `recursive_side_zero`: the same bound for the `false`-side sensitivity of the recursive family.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveZero.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

open scoped Classical in
/-- For a good labeling `A`, a nested family `F` and `0 < r`, at an input `x` where
`recursiveFamily T A.label F q` is `false`, its sensitivity at `x` is at most
`15 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true`. -/
theorem recursive_sensitivity_zero_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false) :
    sensitivityAt (recursiveFamily T A.label F q) x ≤
      15 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true := by
  let TC := targetCandidates T A.label F q x
  let GC := gateCandidates T A.label F q x
  let SC := gateSinks T A.label F q x
  let NC := GC \ SC
  let w := gateWitness T A.label F q x
  let U := TC.biUnion fun i => childChanges F (Fin.last h) x i (targetWitness F x hr i)
  let V := NC.biUnion fun i =>
    childJointChanges F (gateIndex q) (Fin.last h) x (w i) (A.label i (w i))
  let W := SC.biUnion fun i => childChanges F (gateIndex q) x (w i) (A.label i (w i))
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T A.label F q (BitString.flipOn {p} x) ≠
        recursiveFamily T A.label F q x) ⊆
      U ∪ (V ∪ W) := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hon : recursiveFamily T A.label F q (BitString.flipOn {((j, c), a)} x) = true := by grind
    obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff T A.label F q _).mp hon
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
      apply Finset.mem_union_right
      by_cases hs : i ∈ SC
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, hs, ?_⟩
        have hn : F (gateIndex q) (BitString.flipOn {a} (recursiveChild x j (A.label i j))) ≠
            F (gateIndex q) (recursiveChild x j (A.label i j)) := by simp [hgon, hgoff]
        simpa [childChanges, w, hj] using hn
      · have hwg := nonsink_gateWitness_mem T A.label F hF q x i hig hs
        have hjg : j ∈ gateCandidates T A.label F q x := by simpa [hj] using hwg
        have hton :=
          (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hjg).2.1 (A.label i j)
        have htoff := hF.rejects_of_le (gateIndex_lt_last q).le hgoff
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_sdiff.mpr ⟨hig, hs⟩, ?_⟩
        have hn :
            F (gateIndex q) (BitString.flipOn {a} (recursiveChild x j (A.label i j))) ≠
              F (gateIndex q) (recursiveChild x j (A.label i j)) ∧
            F (Fin.last h) (BitString.flipOn {a} (recursiveChild x j (A.label i j))) ≠
              F (Fin.last h) (recursiveChild x j (A.label i j)) := by
          simp [hgon, hgoff, hton, htoff]
        simpa [childJointChanges, w, hj] using hn
  have hU : U.card ≤ 15 * sideSensitivity F false :=
    targetCandidates_biUnion_card_le T A F hF hr q x
  have hV : V.card ≤ 3 * jointSensitivity F true := by
    calc
      V.card ≤ NC.card * jointSensitivity F true :=
        card_biUnion_le_mul NC _ _ (fun i hi => by
          have hg := Finset.mem_sdiff.mp hi
          have hw := nonsink_gateWitness_mem T A.label F hF q x i hg.1 hg.2
          have hgate := (gateWitness_spec T A.label F q x i hg.1).2
          have htarget := (targetFailures_empty_iff F x _).mp (Finset.mem_filter.mp hw).2.1
            (A.label i (w i))
          rw [childJointChanges_card]
          exact jointSensitivityAt_le_jointSensitivity F true _ _ _
            (gateIndex_lt_last q) hgate htarget)
      _ ≤ GC.card * jointSensitivity F true :=
        Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
      _ ≤ 3 * jointSensitivity F true :=
        Nat.mul_le_mul_right _ (gateCandidates_card T A.label F hF q x)
  have hW : W.card ≤ sideSensitivity F true := by
    calc
      W.card ≤ SC.card * sideSensitivity F true :=
        card_biUnion_le_mul SC _ _ (fun i hi => by
          rw [childChanges_card]
          exact sensitivityAt_le_sideSensitivity F true _ _
            (gateWitness_spec T A.label F q x i (Finset.mem_filter.mp hi).1).2)
      _ ≤ 1 * sideSensitivity F true := Nat.mul_le_mul_right _ (gateSinks_card T A.label F q x)
      _ = _ := Nat.one_mul _
  calc
    sensitivityAt (recursiveFamily T A.label F q) x ≤ (U ∪ (V ∪ W)).card := by
      unfold sensitivityAt
      convert Finset.card_le_card hsub
    _ ≤ U.card + (V ∪ W).card := Finset.card_union_le _ _
    _ ≤ U.card + (V.card + W.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ 15 * sideSensitivity F false + (3 * jointSensitivity F true + sideSensitivity F true) :=
      Nat.add_le_add hU (Nat.add_le_add hV hW)
    _ = _ := by omega

/-- Zero-side recurrence: for a good labeling, a nested family `F` and `0 < r`,
`sideSensitivity (recursiveFamily T A.label F) false` is at most
`15 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true`. -/
theorem recursive_side_zero {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    sideSensitivity (recursiveFamily T A.label F) false ≤
      15 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true := by
  apply sideSensitivity_le
  exact fun q x hx => recursive_sensitivity_zero_at T A F hF hr q x hx

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
