/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Support
public import CslibFrontier.Foundations.Data.BitString.Weight
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.Finset.Fin

/-!
# Fixed-cardinality supports and fixed-weight bit strings

A subset of `range n` is represented as its Boolean indicator on `Fin n`. This identifies the
`w`-element subsets of `range n` with the bit strings of length `n` and weight `w`.

## Main definitions

* `Cslib.BitString.indicatorVector`: the indicator of a finite set of natural-number positions.
* `Cslib.BitString.natSupport`: the natural-number positions set in a bit string.
* `Cslib.BitString.fixedSupportEquiv`: the equivalence between fixed-cardinality supports and
  fixed-weight bit strings.

## Main results

* `Cslib.BitString.weight_indicatorVector`: the indicator has the cardinality of an in-range set.
* `Cslib.BitString.natSupport_indicatorVector`,
  `Cslib.BitString.indicatorVector_natSupport`: the conversions are inverse on in-range sets.
-/

public section

namespace Cslib.BitString

open Finset

/-- The `n`-bit indicator of a finite set of natural-number positions. Positions outside
`range n` are ignored. -/
@[expose] def indicatorVector (n : ℕ) (S : Finset ℕ) : BitString n :=
  fun i => decide (i.val ∈ S)

@[simp] theorem indicatorVector_apply (n : ℕ) (S : Finset ℕ) (i : Fin n) :
    indicatorVector n S i = decide (i.val ∈ S) :=
  rfl

/-- The natural-number positions set in an `n`-bit string. -/
@[expose] def natSupport {n : ℕ} (x : BitString n) : Finset ℕ :=
  (supportOfList n (List.ofFn x)).map Fin.valEmbedding

/-- A coordinate belongs to the natural support exactly when its bit is set. -/
@[simp] theorem mem_natSupport {n : ℕ} (x : BitString n) (i : Fin n) :
    i.val ∈ natSupport x ↔ x i = true := by
  constructor
  · intro hi
    rw [natSupport, mem_map] at hi
    obtain ⟨j, hj, hji⟩ := hi
    have hji' : j = i := Fin.ext hji
    subst j
    simpa only [mem_supportOfList, List.getD_ofFn] using hj
  · intro hi
    rw [natSupport, mem_map]
    refine ⟨i, ?_, rfl⟩
    simpa only [mem_supportOfList, List.getD_ofFn] using hi

/-- The natural support of an `n`-bit string lies in `range n`. -/
theorem natSupport_subset_range {n : ℕ} (x : BitString n) : natSupport x ⊆ range n := by
  intro j hj
  rw [natSupport, mem_map] at hj
  obtain ⟨i, _, rfl⟩ := hj
  exact mem_range.mpr i.isLt

/-- The natural support has cardinality equal to the Hamming weight. -/
@[simp] theorem card_natSupport {n : ℕ} (x : BitString n) : (natSupport x).card = weight x := by
  rw [natSupport, card_map, card_supportOfList_of_length List.length_ofFn, count_true_ofFn]

/-- The indicator of an in-range set has weight equal to the set's cardinality. -/
theorem weight_indicatorVector {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) :
    weight (indicatorVector n S) = S.card := by
  have hrange : ∀ j ∈ S, j < n := fun j hj => mem_range.mp (hS hj)
  rw [weight]
  change (univ.filter fun i : Fin n => indicatorVector n S i = true).card = S.card
  rw [show univ.filter (fun i : Fin n => indicatorVector n S i = true) =
      S.attachFin hrange by ext i; simp [indicatorVector], card_attachFin]

/-- Taking the natural support of an in-range indicator returns the original set. -/
@[simp] theorem natSupport_indicatorVector {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) :
    natSupport (indicatorVector n S) = S := by
  ext j
  constructor
  · intro hj
    rw [natSupport, mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    simpa [indicatorVector] using hi
  · intro hj
    have hjn : j < n := mem_range.mp (hS hj)
    rw [natSupport, mem_map]
    refine ⟨⟨j, hjn⟩, ?_, rfl⟩
    simp [indicatorVector, hj, hjn]

/-- The indicator of the natural support is the original bit string. -/
@[simp] theorem indicatorVector_natSupport {n : ℕ} (x : BitString n) :
    indicatorVector n (natSupport x) = x := by
  funext i
  simp only [indicatorVector, mem_natSupport]
  cases x i <;> rfl

/-- Fixed-cardinality subsets of `range n` are exactly fixed-weight `n`-bit strings. Its body is
exposed so downstream proofs can reduce the forward map to `indicatorVector`. -/
@[expose] def fixedSupportEquiv (n w : ℕ) :
    ↥((range n).powersetCard w) ≃ ↥(weightLayer n w) where
  toFun S := by
    refine ⟨indicatorVector n S.1, mem_weightLayer.mpr ?_⟩
    exact (weight_indicatorVector (mem_powersetCard.mp S.property).1).trans
      (mem_powersetCard.mp S.property).2
  invFun x := by
    refine ⟨natSupport x.1, mem_powersetCard.mpr ⟨natSupport_subset_range x.1, ?_⟩⟩
    exact (card_natSupport x.1).trans (mem_weightLayer.mp x.property)
  left_inv S := by
    apply Subtype.ext
    exact natSupport_indicatorVector (mem_powersetCard.mp S.property).1
  right_inv x := by
    apply Subtype.ext
    exact indicatorVector_natSupport x.1

@[simp] theorem fixedSupportEquiv_apply (n w : ℕ) (S : ↥((range n).powersetCard w)) :
    (fixedSupportEquiv n w S).1 = indicatorVector n S.1 :=
  rfl

end Cslib.BitString
