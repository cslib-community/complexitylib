/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Basic

/-!
# Superquadratic sensitivity separation: reindex

Transport `reindex e f` of a Boolean function `f` along an equivalence `e : I ≃ J` of coordinate
types. Global sensitivity and pointwise block sensitivity are invariant under reindexing, which
allows functions on structured coordinate types to be moved onto an ordinary finite Boolean cube.

## Main definitions

* `reindex`: the function `x ↦ f (fun i => x (e i))` on `J → Bool`.

## Main results

* `sensitivity_reindex`: `sensitivity (reindex e f) = sensitivity f`.
* `blockSensitivityAt_reindex`: the block sensitivity of `reindex e f` at `x` equals the block
  sensitivity of `f` at `fun i => x (e i)`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Reindex.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

variable {I J : Type}

/-- Transport a Boolean function along an equivalence of its coordinate types. -/
def reindex (e : I ≃ J) (f : (I → Bool) → Bool) : (J → Bool) → Bool :=
  fun x => f (fun i => x (e i))

/-- Reindexing along `e` and then along `e.symm` recovers the original function. -/
private theorem reindex_symm (e : I ≃ J) (f : (I → Bool) → Bool) :
    reindex e.symm (reindex e f) = f := by
  funext x
  simp [reindex]

section Finite
variable [Fintype I] [Fintype J]

/-- The sensitivity of `reindex e f` at `x` equals the sensitivity of `f` at the pullback
`fun i => x (e i)`. -/
private theorem sensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool) (x : J → Bool) :
    sensitivityAt (reindex e f) x = sensitivityAt f (fun i => x (e i)) := by
  classical
  have hs : (Finset.univ.filter fun j =>
      reindex e f (BitString.flipOn {j} x) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (BitString.flipOn {i} (fun a => x (e a))) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => BitString.flipOn {e i} x (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [BitString.flipOn_reindex_singleton]
  simpa only [sensitivityAt, Finset.card_map] using congrArg Finset.card hs

/-- Reindexing preserves sensitivity: `sensitivity (reindex e f) = sensitivity f`. -/
theorem sensitivity_reindex (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by
  apply Nat.le_antisymm
  · apply sensitivity_le
    intro x
    rw [sensitivityAt_reindex]
    exact sensitivityAt_le_sensitivity f _
  · apply sensitivity_le
    intro x
    have h := sensitivityAt_le_sensitivity (reindex e f) (fun j => x (e.symm j))
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

/-- The block sensitivity of `f` at the pullback `fun i => x (e i)` is at most the block sensitivity
of `reindex e f` at `x`. -/
private theorem blockSensitivityAt_le_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt f (fun i => x (e i)) ≤ blockSensitivityAt (reindex e f) x := by
  classical
  apply blockSensitivityAt_le
  intro blocks hd hb
  have h := le_blockSensitivityAt_of_family (reindex e f) x
    (fun B : blocks => B.val.map e.toEmbedding)
    (fun B => (hb B.val B.property).1.map (f := e.toEmbedding))
    (by
      intro A B hAB
      apply (Finset.disjoint_map e.toEmbedding).mpr
      exact hd A.val A.property B.val B.property (fun h => hAB (Subtype.ext h)))
    (by
      intro B
      change f (fun i => BitString.flipOn (B.val.map e.toEmbedding) x (e i)) ≠ _
      rw [BitString.flipOn_reindex]
      exact (hb B.val B.property).2)
  simpa only [Fintype.card_coe] using h

/-- The block sensitivity of `reindex e f` at `x` equals the block sensitivity of `f` at the
pullback `fun i => x (e i)`. -/
theorem blockSensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt (reindex e f) x = blockSensitivityAt f (fun i => x (e i)) := by
  apply Nat.le_antisymm
  · have h := blockSensitivityAt_le_reindex e.symm (reindex e f) (fun i => x (e i))
    simpa only [Equiv.apply_symm_apply, reindex_symm] using h
  · exact blockSensitivityAt_le_reindex e f x

end Finite
end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
