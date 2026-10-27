/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.List
public import Mathlib.Data.Finset.Card
import Complexity.Foundations.Data.BitString.Weight

/-!
# Support subsets of list-represented bit strings

Views `word : List Bool` as its support subset `{i : Fin n | ofList n word i = true}` via
`Cslib.BitString.ofList`, padding short lists with `false` and ignoring indices `≥ n`.

## Main definitions

* `Cslib.BitString.supportOfList`: support subset `{i : Fin n | ofList n word i = true}`.

## Main results

* `Cslib.BitString.mem_supportOfList`, `Cslib.BitString.supportOfList_ofFn_decide`,
  `Cslib.BitString.ofFn_decide_mem_supportOfList`,
  `Cslib.BitString.supportOfList_injective_of_length`,
  `Cslib.BitString.card_supportOfList_of_length`: membership, round-trips, injectivity, and card.
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

end Cslib.BitString
