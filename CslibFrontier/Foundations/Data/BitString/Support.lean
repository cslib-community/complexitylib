/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.List
public import Mathlib.Data.Finset.Card
import CslibFrontier.Foundations.Data.BitString.Weight

/-!
# Support subsets of list-represented bit strings

Views `word : List Bool` as its support subset `{i : Fin n | ofList n word i = true}` via
`Cslib.BitString.ofList`, padding short lists with `false` and ignoring indices `≥ n`.

Conversely, `Cslib.BitString.indicatorList` is the word of `n` bits that sets bit `i` exactly
when `i ∈ S`; on words of length `n` the two conversions are inverse.

## Main definitions

* `Cslib.BitString.supportOfList`: support subset `{i : Fin n | ofList n word i = true}`.
* `Cslib.BitString.indicatorList`: the indicator word of a subset of `Fin n`.

## Main results

* `Cslib.BitString.mem_supportOfList`, `Cslib.BitString.supportOfList_ofFn_decide`,
  `Cslib.BitString.ofFn_decide_mem_supportOfList`,
  `Cslib.BitString.supportOfList_injective_of_length`,
  `Cslib.BitString.card_supportOfList_of_length`: membership, round-trips, injectivity, and card.
* `Cslib.BitString.supportOfList_indicatorList`, `Cslib.BitString.indicatorList_supportOfList`,
  `Cslib.BitString.indicatorList_injective`, `Cslib.BitString.count_true_indicatorList`: the same
  facts for the indicator word.
* `Cslib.BitString.indicatorList_insert`, `Cslib.BitString.indicatorList_erase`: adding or
  removing an element sets or clears its bit.
-/

@[expose] public section

namespace Cslib.BitString

/-- Convert a Boolean indicator list to its support subset in `Fin n` via `BitString.ofList`. -/
def supportOfList (n : ℕ) (word : List Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ofList n word i = true

/-- Coordinate `i : Fin n` lies in `supportOfList n word` iff `word.getD i.val false = true`. -/
@[simp] theorem mem_supportOfList {n : ℕ} {word : List Bool} {i : Fin n} :
    i ∈ supportOfList n word ↔ word.getD i.val false = true := by simp [supportOfList, ofList]

/-- Round-trip from `S : Finset (Fin n)` through `List.ofFn (fun i => decide (i ∈ S))`. -/
@[simp] theorem supportOfList_ofFn_decide {n : ℕ} (S : Finset (Fin n)) :
    supportOfList n (List.ofFn fun i => decide (i ∈ S)) = S := by ext i; simp [supportOfList]

/-- On words of length `n`, `List.ofFn (fun i => decide (i ∈ supportOfList n word))` is `word`. -/
theorem ofFn_decide_mem_supportOfList {n : ℕ} {word : List Bool} (hw : word.length = n) :
    (List.ofFn fun i : Fin n => decide (i ∈ supportOfList n word)) = word := by
  have hfun : (fun i : Fin n => decide (i ∈ supportOfList n word)) = ofList n word := by
    funext i; simp only [mem_supportOfList, ofList, Bool.decide_coe]
  rw [hfun, ofFn_ofList hw]

/-- On words of exact length `n`, `supportOfList n` is injective. -/
theorem supportOfList_injective_of_length {n : ℕ} {w₁ w₂ : List Bool}
    (hw₁ : w₁.length = n) (hw₂ : w₂.length = n)
    (heq : supportOfList n w₁ = supportOfList n w₂) : w₁ = w₂ := by
  rw [← ofFn_decide_mem_supportOfList hw₁, ← ofFn_decide_mem_supportOfList hw₂, heq]

/-- On words of exact length `n`, `#(supportOfList n word) = word.count true`. -/
theorem card_supportOfList_of_length {n : ℕ} {word : List Bool} (hw : word.length = n) :
    (supportOfList n word).card = word.count true := by
  change weight (ofList n word) = word.count true
  simpa only [ofFn_ofList hw] using (count_true_ofFn (ofList n word)).symm

/-- The indicator list of a `k`-element subset of `Fin m` has `k` entries `true`. -/
theorem count_true_ofFn_decide_mem {m k : ℕ} {S : Finset (Fin m)} (hS : S.card = k) :
    (List.ofFn fun u : Fin m => decide (u ∈ S)).count true = k := by
  rw [← card_supportOfList_of_length List.length_ofFn, supportOfList_ofFn_decide, hS]

/-! ### Indicator words -/

/-- The indicator word of `S : Finset (Fin n)`: bit `i` records whether `i ∈ S`. -/
def indicatorList {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  List.ofFn fun i => decide (i ∈ S)

variable {n : ℕ}

@[simp] theorem length_indicatorList (S : Finset (Fin n)) : (indicatorList S).length = n := by
  rw [indicatorList, List.length_ofFn]

@[simp] theorem supportOfList_indicatorList (S : Finset (Fin n)) :
    supportOfList n (indicatorList S) = S :=
  supportOfList_ofFn_decide S

/-- Every word of length `n` is the indicator word of its support. -/
theorem indicatorList_supportOfList {word : List Bool} (hw : word.length = n) :
    indicatorList (supportOfList n word) = word :=
  ofFn_decide_mem_supportOfList hw

theorem indicatorList_injective : Function.Injective (indicatorList (n := n)) := fun S T h => by
  rw [← supportOfList_indicatorList S, h, supportOfList_indicatorList]

@[simp] theorem indicatorList_inj {S T : Finset (Fin n)} :
    indicatorList S = indicatorList T ↔ S = T :=
  indicatorList_injective.eq_iff

theorem count_true_indicatorList (S : Finset (Fin n)) : (indicatorList S).count true = S.card :=
  count_true_ofFn_decide_mem rfl

theorem getD_indicatorList (S : Finset (Fin n)) (i : Fin n) :
    (indicatorList S).getD i false = decide (i ∈ S) := by
  simp [indicatorList]

/-- Adding an element sets its bit. -/
theorem indicatorList_insert (S : Finset (Fin n)) (i : Fin n) :
    indicatorList (insert i S) = (indicatorList S).set i true := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [indicatorList, List.getElem_ofFn, List.getElem_set, Finset.mem_insert]
  by_cases h : (i : ℕ) = j
  · simp [h, Fin.ext_iff]
  · simp [h, Fin.ext_iff, Ne.symm h]

/-- Removing an element clears its bit. -/
theorem indicatorList_erase (S : Finset (Fin n)) (i : Fin n) :
    indicatorList (S.erase i) = (indicatorList S).set i false := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [indicatorList, List.getElem_ofFn, List.getElem_set, Finset.mem_erase]
  by_cases h : (i : ℕ) = j
  · simp [h, Fin.ext_iff]
  · simp [h, Fin.ext_iff, Ne.symm h]

@[simp] theorem indicatorList_empty :
    indicatorList (∅ : Finset (Fin n)) = List.replicate n false := by
  simp [indicatorList, List.ofFn_const]

/-- The indicator word of `{i}` is the zero word with bit `i` set. -/
theorem indicatorList_singleton (i : Fin n) :
    indicatorList {i} = (List.replicate n false).set i true := by
  rw [← indicatorList_empty, ← indicatorList_insert, insert_empty_eq]

end Cslib.BitString
