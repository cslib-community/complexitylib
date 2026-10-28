/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Codes
public import Complexity.Computability.WordRAM.ArrayAppend

/-!
# Finite-set invariant of the native deduplicating scan

## Main definitions

* `PrunedQuery.scanSet`: the selected, shortened codes among a processed input prefix.

## Main results

* `PrunedQuery.scanSet_succ`: the exact insertion made by one scan step.
* `PrunedQuery.scanSet_child`: agreement of the child scan with `childCodes`.

These describe the native loop's mathematical invariant; they do not assume its execution.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Finset

/-- Root scans retain every query; child scans retain exactly contributing first digits. -/
def selected (child : Bool) (term code : ℕ) : Prop :=
  if child then code % 10 = 9 ∨ code % 10 = term else True

instance (child : Bool) (term code : ℕ) : Decidable (selected child term code) :=
  inferInstanceAs (Decidable (if child then code % 10 = 9 ∨ code % 10 = term else True))

/-- Child requests discard one digit; root requests keep the supplied complete code. -/
def shortened (child : Bool) (code : ℕ) : ℕ := if child then code / 10 else code

/-- The deduplicated codes selected from the first `k` actual input entries. -/
def scanSet (child : Bool) (term : ℕ) (input : ℕ → ℕ) (k : ℕ) : Finset ℕ :=
  ((range k).filter fun i => selected child term (input i)).image
    fun i => shortened child (input i)

/-- No input positions have been visited initially. -/
@[simp]
theorem scanSet_zero (child : Bool) (term : ℕ) (input : ℕ → ℕ) :
    scanSet child term input 0 = ∅ := by simp [scanSet]

/-- A scan step inserts one selected suffix, leaving any previous occurrence deduplicated. -/
theorem scanSet_succ (child : Bool) (term : ℕ) (input : ℕ → ℕ) (k : ℕ) :
    scanSet child term input (k + 1) =
      if selected child term (input k) then
        insert (shortened child (input k)) (scanSet child term input k)
      else scanSet child term input k := by
  by_cases h : selected child term (input k) <;> simp [scanSet, range_add_one, filter_insert, h]

/-- At most one new distinct code is emitted for each processed input word. -/
theorem card_scanSet_le (child : Bool) (term : ℕ) (input : ℕ → ℕ) (k : ℕ) :
    (scanSet child term input k).card ≤ k :=
  (card_image_le.trans (card_filter_le _ _)).trans_eq (card_range k)

/-- Root deduplication computes exactly the image of the input prefix. -/
theorem scanSet_root (term : ℕ) (input : ℕ → ℕ) (k : ℕ) :
    scanSet false term input k = (range k).image input := by
  simp [scanSet, selected, shortened]

/-- A child scan uses the same selected quotient image as the finite pruning specification. -/
theorem scanSet_child (term : ℕ) (input : ℕ → ℕ) (k : ℕ) :
    scanSet true term input k = childCodes ((range k).image input) term := by
  ext q
  simp only [scanSet, selected, ↓reduceIte, shortened, mem_image,
    mem_filter, childCodes]
  constructor
  · rintro ⟨i, ⟨hi, hm⟩, he⟩
    exact ⟨input i, ⟨⟨i, hi, rfl⟩, hm⟩, he⟩
  · rintro ⟨v, ⟨⟨i, hi, rfl⟩, hm⟩, he⟩
    exact ⟨i, ⟨hi, hm⟩, he⟩

/-- Every stored code lies in the concrete destination capacity when each selected source does. -/
theorem scanSet_bounded {child : Bool} {term k capacity : ℕ} {input : ℕ → ℕ}
    (h : ∀ i < k, selected child term (input i) → shortened child (input i) < capacity) :
    ∀ q ∈ scanSet child term input k, q < capacity := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
  exact h i (mem_range.mp (mem_filter.mp hi).1) (mem_filter.mp hi).2

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
