/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Composition
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Reindex

/-!
# Superquadratic sensitivity separation: iterates

Repeated disjoint composition `iterateCompose f m` of a Boolean function with itself, on the
explicit coordinate type `IterateCoord I m` with `Fintype.card I ^ m` elements, and its reindexing
`iterateFin f m` onto `Fin (Fintype.card I ^ m)`. The sensitivity of the `m`-fold iterate is at most
`sensitivity f ^ m`, while its block sensitivity at the all-false input is at least the `m`-th power
of that of `f`.

## Main definitions

* `IterateCoord`: coordinates `I × (I × (⋯ × Unit))` of the `m`-fold iterate.
* `iterateCompose`: the `m`-fold block composition of `f` with itself.
* `iterateFin`: `iterateCompose f m` reindexed onto `Fin (Fintype.card I ^ m)`.

## Main results

* `iterateCoord_card`: `IterateCoord I m` has `Fintype.card I ^ m` elements.
* `sensitivity_iterateFin_le`: `sensitivity (iterateFin f m) ≤ sensitivity f ^ m`.
* `blockSensitivityAt_iterateFin_zero`: the block sensitivity of `iterateFin f m` at the all-false
  input is at least the `m`-th power of that of `f`.
* `iterateFin_nonconstant`: every iterate of a function with positive block sensitivity at the
  all-false input is nonconstant.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Iterates.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Coordinates of an iterated block composition, starting with a singleton. -/
abbrev IterateCoord (I : Type) : ℕ → Type
  | 0 => Unit
  | m + 1 => I × IterateCoord I m

/-- `IterateCoord I m` is finite whenever `I` is. -/
instance iterateCoordFintype {I : Type} [Fintype I] :
    (m : ℕ) → Fintype (IterateCoord I m)
  | 0 => inferInstanceAs (Fintype Unit)
  | m + 1 =>
    letI : Fintype (IterateCoord I m) := iterateCoordFintype (I := I) m
    inferInstanceAs (Fintype (I × IterateCoord I m))

/-- Repeated block composition of a Boolean function. -/
def iterateCompose {I : Type} (f : (I → Bool) → Bool) :
    (m : ℕ) → (IterateCoord I m → Bool) → Bool
  | 0 => fun x => x ()
  | m + 1 => compose f (iterateCompose f m)

/-- If `f` rejects the all-false input, then so does every iterate `iterateCompose f m`. -/
private theorem iterateCompose_zero {I : Type} (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    iterateCompose f m (fun _ => false) = false := by
  induction m with
  | zero => rfl
  | succ m ih => exact (compose_zero f (iterateCompose f m) ih).trans hf

variable {I : Type} [Fintype I]

/-- `IterateCoord I m` has `Fintype.card I ^ m` elements. -/
theorem iterateCoord_card (m : ℕ) :
    Fintype.card (IterateCoord I m) = Fintype.card I ^ m := by
  induction m with
  | zero => exact Fintype.card_unique
  | succ m ih =>
    change Fintype.card (I × IterateCoord I m) = _
    rw [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

/-- Sensitivity of iterates: `sensitivity (iterateCompose f m) ≤ sensitivity f ^ m`. -/
private theorem sensitivity_iterateCompose_le (f : (I → Bool) → Bool) (m : ℕ) :
    sensitivity (iterateCompose f m) ≤ sensitivity f ^ m := by
  induction m with
  | zero =>
    apply sensitivity_le
    intro x
    exact (sensitivityAt_le_card (iterateCompose f 0) x).trans_eq (iterateCoord_card 0)
  | succ m ih =>
    change sensitivity (compose f (iterateCompose f m)) ≤ _
    calc
      _ ≤ sensitivity f * sensitivity (iterateCompose f m) := sensitivity_compose_le _ _
      _ ≤ sensitivity f * sensitivity f ^ m := Nat.mul_le_mul_left _ ih
      _ = sensitivity f ^ (m + 1) := by rw [pow_succ, Nat.mul_comm]

/-- If `f` rejects the all-false input, then the `m`-th power of its block sensitivity at the
all-false input is at most the block sensitivity of `iterateCompose f m` there. -/
private theorem blockSensitivityAt_iterateCompose_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    blockSensitivityAt f (fun _ => false) ^ m ≤
      blockSensitivityAt (iterateCompose f m) (fun _ => false) := by
  induction m with
  | zero =>
    have h := le_blockSensitivityAt (iterateCompose f 0) (fun _ => false)
      ({{()}} : Finset (Finset Unit))
      (by
        intro A hA B hB hne
        exact (hne ((Finset.mem_singleton.mp hA).trans (Finset.mem_singleton.mp hB).symm)).elim)
      (by
        intro B hB
        have hB' : B = {()} := Finset.mem_singleton.mp hB
        subst B
        exact ⟨Finset.singleton_nonempty _, by simp [iterateCompose, BitString.flipOn_apply]⟩)
    simpa only [Finset.card_singleton, pow_zero] using h
  | succ m ih =>
    change _ ≤ blockSensitivityAt (compose f (iterateCompose f m)) (fun _ => false)
    calc
      _ = blockSensitivityAt f (fun _ => false) *
          blockSensitivityAt f (fun _ => false) ^ m := by rw [pow_succ, Nat.mul_comm]
      _ ≤ blockSensitivityAt f (fun _ => false) *
          blockSensitivityAt (iterateCompose f m) (fun _ => false) := Nat.mul_le_mul_left _ ih
      _ ≤ _ := blockSensitivityAt_compose_zero_le f (iterateCompose f m)
        (iterateCompose_zero f hf m)

/-- Reindex the iterated composition onto a finite ordinal. -/
def iterateFin (f : (I → Bool) → Bool) (m : ℕ) :
    (Fin (Fintype.card I ^ m) → Bool) → Bool :=
  reindex (Fintype.equivFinOfCardEq (iterateCoord_card (I := I) m)) (iterateCompose f m)

/-- If `f` rejects the all-false input, then so does `iterateFin f m`. -/
theorem iterateFin_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    iterateFin f m (fun _ => false) = false :=
  iterateCompose_zero f hf m

/-- Sensitivity of reindexed iterates: `sensitivity (iterateFin f m) ≤ sensitivity f ^ m`. -/
theorem sensitivity_iterateFin_le (f : (I → Bool) → Bool) (m : ℕ) :
    sensitivity (iterateFin f m) ≤ sensitivity f ^ m := by
  rw [iterateFin, sensitivity_reindex]
  exact sensitivity_iterateCompose_le f m

/-- If `f` rejects the all-false input, then the `m`-th power of its block sensitivity at the
all-false input is at most the block sensitivity of `iterateFin f m` there. -/
theorem blockSensitivityAt_iterateFin_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    blockSensitivityAt f (fun _ => false) ^ m ≤
      blockSensitivityAt (iterateFin f m) (fun _ => false) := by
  rw [iterateFin, blockSensitivityAt_reindex]
  exact blockSensitivityAt_iterateCompose_zero f hf m

open scoped Classical in
/-- A Boolean function with positive block sensitivity at some input takes two distinct values. -/
theorem nonconstant_of_blockSensitivityAt_pos (f : (I → Bool) → Bool) (x : I → Bool)
    (h : 0 < blockSensitivityAt f x) : ∃ y z, f y ≠ f z := by
  obtain ⟨blocks, hc, _, hb⟩ := exists_blockSensitivityAt_family f x
  have hn : blocks.Nonempty := Finset.card_pos.mp (hc.symm ▸ h)
  obtain ⟨B, hB⟩ := hn
  exact ⟨BitString.flipOn B x, x, (hb B hB).2⟩

/-- If `f` rejects the all-false input and has positive block sensitivity there, then every
`iterateFin f m` takes two distinct values. -/
theorem iterateFin_nonconstant (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false)
    (h : 0 < blockSensitivityAt f (fun _ => false)) (m : ℕ) :
    ∃ x y, iterateFin f m x ≠ iterateFin f m y := by
  exact nonconstant_of_blockSensitivityAt_pos _ _
    ((Nat.pow_pos h).trans_le (blockSensitivityAt_iterateFin_zero f hf m))

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
