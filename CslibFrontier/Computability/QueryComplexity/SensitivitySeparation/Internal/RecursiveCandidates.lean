/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveFailures
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveSets

/-!
# Superquadratic sensitivity separation: recursive candidates

Characterizes the witnesses chosen for candidate rows: the target witness of a target candidate is
its unique rejected target column, and the gate witness of a gate candidate is its unique outgoing
neighbor whose labeled gate child is accepted. It also introduces the sinks of the set of gate
candidates, shows that there is at most one, and proves that the gate witness of a non-sink gate
candidate is itself a gate candidate. Finally, it bounds the raw coordinates that can repair the
target condition of a target candidate.

## Main definitions

* `gateSinks`: gate candidates with no outgoing edge to another gate candidate.

## Main results

* `targetWitness_unique`: the target witness is the unique rejected target column of a target
  candidate.
* `gateWitness_spec`: the gate witness is an outgoing neighbor with accepted gate child.
* `gateWitness_unique`: the gate witness is the unique such neighbor.
* `gateSinks_card`: there is at most one gate sink.
* `nonsink_gateWitness_mem`: the gate witness of a non-sink gate candidate is a gate candidate.
* `targetCandidates_biUnion_card_le`: the coordinates that change the final predicate on the target
  witness child of some target candidate number at most `15 * sideSensitivity F false`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveCandidates.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- For a target candidate `i`, the final predicate rejects the child of row `i` at the column
`targetWitness F x hr i`. -/
private theorem targetWitness_false {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) :
    F (Fin.last h) (recursiveChild x i (targetWitness F x hr i)) = false := by
  have hm : targetWitness F x hr i ∈ targetFailures F x i := by
    rw [targetFailures_singleton T label F q x hr i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

/-- For a target candidate `i`, every column `c` whose target child is rejected by the final
predicate equals `targetWitness F x hr i`. -/
theorem targetWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) (c : Fin r)
    (hc : F (Fin.last h) (recursiveChild x i c) = false) : c = targetWitness F x hr i := by
  have hm : c ∈ targetFailures F x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  rwa [targetFailures_singleton T label F q x hr i hi, Finset.mem_singleton] at hm

open scoped Classical in
/-- For a gate candidate `i`, the gate witness is an outgoing neighbor of `i`, and the gate
predicate `F (gateIndex q)` accepts its child labeled by the edge from `i`. -/
theorem gateWitness_spec {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) :
    T.Adj i (gateWitness T label F q x i) ∧
      F (gateIndex q) (recursiveChild x (gateWitness T label F q x i)
        (label i (gateWitness T label F q x i))) = true := by
  have hm : gateWitness T label F q x i ∈ gateFailures T label F q x i := by
    rw [gateFailures_singleton T label F q x i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

open scoped Classical in
/-- For a gate candidate `i`, every outgoing neighbor `j` whose child `(j, label i j)` is accepted
by the gate predicate equals the gate witness of `i`. -/
theorem gateWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) (j : Fin k) (hij : T.Adj i j)
    (hj : F (gateIndex q) (recursiveChild x j (label i j)) = true) :
    j = gateWitness T label F q x i := by
  have hm : j ∈ gateFailures T label F q x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hj⟩
  rwa [gateFailures_singleton T label F q x i hi, Finset.mem_singleton] at hm

open scoped Classical in
/-- Gate candidates with no outgoing edge to another gate candidate. -/
def gateSinks {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  (gateCandidates T label F q x).filter fun i =>
    ∀ j ∈ gateCandidates T label F q x, ¬ T.Adj i j

open scoped Classical in
/-- There is at most one gate sink. -/
theorem gateSinks_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    (gateSinks T label F q x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact T.internal_sink_unique (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

open scoped Classical in
/-- If `F` is nested, the gate witness of a gate candidate that is not a gate sink is again a gate
candidate. -/
theorem nonsink_gateWitness_mem {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i : Fin k) (hi : i ∈ gateCandidates T label F q x)
    (hs : i ∉ gateSinks T label F q x) :
    gateWitness T label F q x i ∈ gateCandidates T label F q x := by
  have he : ∃ j ∈ gateCandidates T label F q x, T.Adj i j := by
    by_contra hn
    apply hs
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    intro j hj hij
    exact hn ⟨j, hj, hij⟩
  obtain ⟨j, hj, hij⟩ := he
  rwa [← gateCandidates_neighbor T label F hF q x i j hi hj hij]

open scoped Classical in
/-- For a good labeling `A`, a nested family `F` and `0 < r`, the raw coordinates whose flip changes
the final predicate on the target witness child of some target candidate number at most
`15 * sideSensitivity F false`: there are at most `15` target candidates (`targetCandidates_card`),
and each target witness child is rejected by the final predicate. -/
theorem targetCandidates_biUnion_card_le {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    ((targetCandidates T A.label F q x).biUnion fun i =>
        childChanges F (Fin.last h) x i (targetWitness F x hr i)).card ≤
      15 * sideSensitivity F false :=
  calc
    _ ≤ (targetCandidates T A.label F q x).card * sideSensitivity F false :=
      card_biUnion_le_mul _ _ _ fun i hi => by
        rw [childChanges_card]
        exact sensitivityAt_le_sideSensitivity F false _ _
          (targetWitness_false T A.label F q x hr i hi)
    _ ≤ 15 * sideSensitivity F false :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (targetCandidates_card T A F hF q x hr))

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
