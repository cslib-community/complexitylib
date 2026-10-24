/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.Bitwise.Projection

/-!
# Significant bits and perfect sketches

The perfect sketch used in fusion trees retains the most significant differing bit of each
adjacent pair of stored keys. Packing these selected bits preserves strict order on the stored
keys. It need not preserve the position of an arbitrary query among those keys: query correction
is a separate step. This module makes no claim about word-RAM running time.

## Main definitions

* `relevantBits`: the bits selected by adjacent pairs of keys.

## Main results

* `relevantBits_card_le`: at most one bit is selected per adjacent pair.
* `strictMono_sketch`: perfect sketches preserve strict order on the stored keys.

## References

See [FredmanWillard1993] and MIT 6.851, Spring 2021, Lecture 12, sections 4–5.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.FusionTree

open Cslib.BitString

/-- Select the highest differing bit of each adjacent pair of keys. Equal adjacent keys select
the default position zero; the order-preservation theorem assumes strictly increasing keys. -/
def relevantBits {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) : Finset ℕ :=
  Finset.univ.image fun i : Fin (n - 1) =>
    highestDiff w (keys ⟨i, by omega⟩) (keys ⟨i + 1, by omega⟩)

/-- There are at most `n - 1` relevant positions for `n` keys, including the empty case. -/
theorem relevantBits_card_le {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) :
    (relevantBits w keys).card ≤ n - 1 := by
  exact (Finset.card_image_le).trans_eq (by simp)

/-- For strictly increasing bounded keys, every relevant bit lies within the word width. -/
theorem relevantBits_subset_range {n w : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) :
    relevantBits w keys ⊆ Finset.range w := by
  intro b hb
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_range.mpr
  exact (highestDiff_spec (hbound _) (hbound _)
    (Nat.ne_of_lt (hsorted (by exact Nat.lt_succ_self i.val)))).1

/-- The significant bit of any adjacent pair is selected. -/
private theorem highestDiff_mem_relevantBits {n : ℕ} (w : ℕ) (keys : Fin (n + 1) → ℕ)
    (i : Fin n) : highestDiff w (keys i.castSucc) (keys i.succ) ∈ relevantBits w keys := by
  apply Finset.mem_image.mpr
  refine ⟨⟨i, by omega⟩, Finset.mem_univ _, ?_⟩
  rfl

/-- Perfect sketches preserve strict order on all stored keys. This statement concerns stored
keys only, and does not justify locating an arbitrary query by its sketch alone. -/
theorem strictMono_sketch {n w : ℕ} {keys : Fin n → ℕ} (hsorted : StrictMono keys)
    (hbound : ∀ i, keys i < 2 ^ w) :
    StrictMono fun i => sketch (relevantBits w keys) (keys i) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact sketch_lt_of_highestDiff_mem (hbound _) (hbound _)
      (hsorted Fin.castSucc_lt_succ) (highestDiff_mem_relevantBits w keys i)

/-- In particular, the stored keys have distinct perfect sketches. -/
theorem sketch_injective {n w : ℕ} {keys : Fin n → ℕ} (hsorted : StrictMono keys)
    (hbound : ∀ i, keys i < 2 ^ w) :
    Function.Injective fun i => sketch (relevantBits w keys) (keys i) :=
  (strictMono_sketch hsorted hbound).injective

/-- The sketch of any word, including a query, uses at most `n - 1` bits. -/
theorem sketch_relevantBits_lt_two_pow {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (x : ℕ) :
    sketch (relevantBits w keys) x < 2 ^ (n - 1) :=
  (sketch_lt_two_pow _ _).trans_le
    (Nat.pow_le_pow_right (by decide) (relevantBits_card_le w keys))

end Cslib.Algorithms.Lean.FusionTree
