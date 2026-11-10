/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.LabelingConstraints
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.FixedCoordinates
public import Mathlib.Data.Fintype.EquivFin

/-!
# Superquadratic sensitivity separation: labeling events

For a tournament `T` on `k` vertices, an injective `v : Fin n → Fin k` and target labels
`m : Fin n → Fin r`, the labeling event consists of the edge labelings giving every directed edge
`v i → v j` the label `m j`. Such an event fixes exactly `n.choose 2` coordinates, so it has
`r ^ (k * k - n.choose 2)` elements, and a union bound over all `v` and `m` bounds the number of bad
labelings. The case `n = 16` is used to produce good labelings.

## Main definitions

* `Tournament.labelingEvent`: labelings whose edges among the injected vertices carry the labels of
  their targets.
* `Tournament.badLabelings`: union of all labeling events for `n` vertices and `r` labels.

## Main results

* `Tournament.mem_labelingEvent_iff`: membership in a labeling event for an injective vertex map.
* `Tournament.card_labelingEvent`: for injective `v` the event has exactly
  `r ^ (k * k - n.choose 2)` elements.
* `Tournament.card_badLabelings_le`:
  `(T.badLabelings n r).card ≤ k ^ n * r ^ n * r ^ (k * k - n.choose 2)`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/LabelingEvents.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal.Tournament
variable {k r n : ℕ} (T : Tournament k)

open scoped Classical in
/-- Labelings whose edges between injected vertices have the prescribed target labels. -/
def labelingEvent (v : Fin n → Fin k) (m : Fin n → Fin r) :
    Finset ((Fin k × Fin k) → Fin r) :=
  if Function.Injective v then
    Finset.univ.filter fun A => ∀ i j, T.Adj (v i) (v j) → A (v i, v j) = m j
  else ∅

open scoped Classical in
/-- For injective `v`, `A ∈ T.labelingEvent v m` iff `A (v i, v j) = m j` whenever
`T.Adj (v i) (v j)`. -/
theorem mem_labelingEvent_iff {v : Fin n → Fin k} {m : Fin n → Fin r}
    {A : (Fin k × Fin k) → Fin r} (hv : Function.Injective v) :
    A ∈ T.labelingEvent v m ↔ ∀ i j, T.Adj (v i) (v j) → A (v i,v j) = m j := by
  simp only [labelingEvent, ite_eq_left hv, Finset.mem_filter, Finset.mem_univ, true_and]

open scoped Classical in
/-- For injective `v`, the labeling event is the set of labelings taking the value
`m (Function.invFun v p.2)` on every internal edge `p` of the image of `v`. -/
private theorem labelingEvent_eq [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    T.labelingEvent v m = Finset.univ.filter fun A =>
      ∀ p ∈ T.internalEdges (Finset.univ.image v), A p = m (Function.invFun v p.2) := by
  rw [labelingEvent, ite_eq_left hv]
  apply Finset.filter_congr
  intro A _
  simpa only [Finset.mem_univ, forall_const] using
    T.labelingConstraint_iff Finset.univ v m hv A

open scoped Classical in
/-- For injective `v`, the labeling event has exactly `r ^ (k * k - n.choose 2)` elements. -/
theorem card_labelingEvent [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    (T.labelingEvent v m).card = r ^ (k * k-n.choose 2) := by
  rw [T.labelingEvent_eq v m hv]
  have hc := card_fixedCoordinates (T.internalEdges (Finset.univ.image v))
    (fun p => m (Function.invFun v p.2))
  rw [T.card_internalEdges] at hc
  have hi : (Finset.univ.image v).card = n := by
    rw [Finset.card_image_of_injective _ hv]
    exact Fintype.card_fin n
  rw [hi] at hc
  simpa only [Fintype.card_fin, Fintype.card_prod] using hc

open scoped Classical in
/-- Every labeling event has at most `r ^ (k * k - n.choose 2)` elements; it is empty when `v` is
not injective. -/
private theorem card_labelingEvent_le [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r) :
    (T.labelingEvent v m).card ≤ r ^ (k * k-n.choose 2) := by
  by_cases hv : Function.Injective v
  · exact (T.card_labelingEvent v m hv).le
  · simp only [labelingEvent, ite_eq_right hv, Finset.card_empty, Nat.zero_le]

open scoped Classical in
/-- Union of labeling events over all vertex maps and target-label assignments. -/
def badLabelings (n r : ℕ) : Finset ((Fin k × Fin k) → Fin r) :=
  Finset.univ.biUnion fun v : Fin n → Fin k =>
    Finset.univ.biUnion fun m : Fin n → Fin r => T.labelingEvent v m

open scoped Classical in
/-- Every labeling event is contained in `T.badLabelings n r`. -/
theorem labelingEvent_subset_bad {v : Fin n → Fin k} {m : Fin n → Fin r} :
    T.labelingEvent v m ⊆ T.badLabelings n r := by
  intro A hA
  exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨m,Finset.mem_univ _,hA⟩⟩

open scoped Classical in
/-- Union bound: `(T.badLabelings n r).card ≤ k ^ n * r ^ n * r ^ (k * k - n.choose 2)`. -/
theorem card_badLabelings_le [NeZero n] :
    (T.badLabelings n r).card ≤ k ^ n * r ^ n * r ^ (k * k-n.choose 2) := by
  calc
    (T.badLabelings n r).card ≤ ∑ v : Fin n → Fin k,
        (Finset.univ.biUnion fun m : Fin n → Fin r => T.labelingEvent v m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n → Fin k, ∑ _m : Fin n → Fin r, r ^ (k * k-n.choose 2) := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun m _ =>
        T.card_labelingEvent_le v m)
    _ = k ^ n * r ^ n * r ^ (k * k-n.choose 2) := by
      simp [Nat.mul_assoc]

end Internal.Tournament

end

end Cslib.QueryComplexity.SensitivitySeparation
