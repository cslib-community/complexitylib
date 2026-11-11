/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Defs

/-!
# Superquadratic sensitivity separation: recursive profiles

This file introduces the quantitative profiles tracked through the recursive construction. For a
family `F : Fin h → (I → Bool) → Bool` of predicates, the side profile at `b` is the maximal
sensitivity of a member of `F` at an input where it outputs `b`, and the joint profile at `b` is the
maximal number of single-bit flips of one input that change two distinct members `F q`, `F q'` (with
`q < q'`) simultaneously while both output `b`.

## Main definitions

* `NestedFamily`: a family of predicates whose acceptance sets shrink as the index grows.
* `jointSensitivityAt`: the number of coordinates whose flip changes both of two predicates.
* `sideSensitivity`: the maximal sensitivity over all indices and inputs with output `b`.
* `jointSensitivity`: the maximal joint sensitivity of `F q` and `F q'` over `q < q'` and inputs on
  which both output `b`.

## Main results

* `sideSensitivity_le`: a uniform bound on sensitivities at inputs with output `b` bounds
  `sideSensitivity F b`.
* `jointSensitivity_le`: a uniform bound on the relevant joint sensitivities bounds
  `jointSensitivity F b`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveProfiles.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Acceptance at a stronger index implies acceptance at every weaker index. -/
structure NestedFamily {h : ℕ} {I : Type}
    (F : Fin h → (I → Bool) → Bool) : Prop where
  /-- Weaker indices accept every input accepted at a stronger index. -/
  accepts_of_le : ∀ {q q' : Fin h} {x}, q ≤ q' → F q' x = true → F q x = true

/-- In a nested family, rejection at index `q` implies rejection at every index `q' ≥ q`. -/
theorem NestedFamily.rejects_of_le {h : ℕ} {I : Type}
    {F : Fin h → (I → Bool) → Bool} (hF : NestedFamily F)
    {q q' : Fin h} {x} (hqq : q ≤ q') (hx : F q x = false) :
    F q' x = false := by
  cases h' : F q' x
  · rfl
  · have := hF.accepts_of_le hqq h'
    simp [hx] at this

open scoped Classical in
/-- The number of coordinates whose one-bit flip changes both predicates. -/
def jointSensitivityAt {I : Type} [Fintype I]
    (f g : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i =>
    f (BitString.flipOn {i} x) ≠ f x ∧ g (BitString.flipOn {i} x) ≠ g x).card

open scoped Classical in
/-- Maximum sensitivity over all indices and inputs with the indicated output. -/
def sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) : ℕ :=
  Finset.univ.sup fun q => Finset.univ.sup fun x =>
    if F q x = b then sensitivityAt (F q) x else 0

open scoped Classical in
/-- Maximum same-input, same-bit joint sensitivity over two distinct ordered indices. -/
def jointSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) : ℕ :=
  Finset.univ.sup fun q => Finset.univ.sup fun q' => Finset.univ.sup fun x =>
    if q < q' ∧ F q x = b ∧ F q' x = b then
      jointSensitivityAt (F q) (F q') x else 0

open scoped Classical in
/-- If `F q x = b`, then `sensitivityAt (F q) x ≤ sideSensitivity F b`. -/
theorem sensitivityAt_le_sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q : Fin h) (x : I → Bool)
    (hx : F q x = b) : sensitivityAt (F q) x ≤ sideSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hx]

open scoped Classical in
/-- If `sensitivityAt (F q) x ≤ B` whenever `F q x = b`, then `sideSensitivity F b ≤ B`. -/
theorem sideSensitivity_le {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (B : ℕ)
    (hB : ∀ q x, F q x = b → sensitivityAt (F q) x ≤ B) :
    sideSensitivity F b ≤ B := by
  apply Finset.sup_le
  intro q _
  apply Finset.sup_le
  intro x _
  split_ifs with hx
  · exact hB q x hx
  · exact Nat.zero_le _

open scoped Classical in
/-- If `q < q'` and `F q x = F q' x = b`, then
`jointSensitivityAt (F q) (F q') x ≤ jointSensitivity F b`. -/
theorem jointSensitivityAt_le_jointSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q q' : Fin h) (x : I → Bool)
    (hqq : q < q') (hx : F q x = b) (hx' : F q' x = b) :
    jointSensitivityAt (F q) (F q') x ≤ jointSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ q')
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hqq, hx, hx']

open scoped Classical in
/-- If `jointSensitivityAt (F q) (F q') x ≤ B` whenever `q < q'` and `F q x = F q' x = b`, then
`jointSensitivity F b ≤ B`. -/
theorem jointSensitivity_le {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (B : ℕ)
    (hB : ∀ q q' x, q < q' → F q x = b → F q' x = b →
      jointSensitivityAt (F q) (F q') x ≤ B) : jointSensitivity F b ≤ B := by
  apply Finset.sup_le
  intro q _
  apply Finset.sup_le
  intro q' _
  apply Finset.sup_le
  intro x _
  split_ifs with hx
  · exact hB q q' x hx.1 hx.2.1 hx.2.2
  · exact Nat.zero_le _

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
