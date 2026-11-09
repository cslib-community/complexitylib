/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `InformationTheory/Hamming.lean`)

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Finset.Density
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Relative Hamming distance and Hamming distance one

The coordinates where two functions agree and those where they differ make up all the coordinates
(`card_filter_eq_add_hammingDist`), so the Hamming distance is the number of coordinates times one
minus the density of the coordinates of agreement (`hammingDist_eq_card_mul_one_sub_dens`). The
relative Hamming distance is the probability that the two functions differ at a uniformly random
coordinate (`hammingDist_div_eq_expect`). A distance of at most `r + s` splits into one of at
most `r` followed by one of at most `s` (`exists_hammingDist_le_and_hammingDist_le`).

Two functions are at Hamming distance one when they differ at exactly one coordinate
(`hammingDist_eq_one_iff`); changing one coordinate of a function to a new value moves it to
distance one (`hammingDist_update_of_ne`), and two functions at distance at most one that differ
at a coordinate differ only there (`update_eq_of_hammingDist_le_one`). Updating two functions at
the same coordinate changes their distance only through that coordinate
(`hammingDist_update_update`). The pairs of `A × B` at Hamming distance one are the edges of the
Hamming graph between `A` and `B` (`hammingEdges`); counting them from either side gives the same
number (`card_hammingEdges_comm`, `card_hammingEdges_eq_sum_card_filter`).

## Main definitions

* `hammingEdges`: the pairs of `A × B` at Hamming distance one.

## Main results

* `card_filter_eq_add_hammingDist`, `hammingDist_eq_card_mul_one_sub_dens`: the coordinates of
  agreement and of disagreement.
* `hammingDist_div_eq_expect`: the relative Hamming distance is a probability.
* `exists_hammingDist_le_and_hammingDist_le`: splitting a distance.
* `hammingDist_eq_one_iff`: Hamming distance one.
* `update_eq_of_hammingDist_le_one`, `update_not_eq_of_hammingDist_le_one`: functions at distance
  at most one differ at most at one coordinate.
* `hammingDist_update_update`: updating two functions at the same coordinate.
* `card_hammingEdges_eq_sum_card_filter`: counting the edges of the Hamming graph.
-/

@[expose] public section

open Finset Function
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, DecidableEq (β i)]

/-! ### Relative Hamming distance -/

/-- The coordinates where two functions agree and those where they differ make up all the
coordinates. -/
theorem card_filter_eq_add_hammingDist (x y : ∀ i, β i) :
    #{i | x i = y i} + hammingDist x y = Fintype.card ι := by
  rw [hammingDist, ← card_univ]
  exact card_filter_add_card_filter_not _

/-- The Hamming distance is the number of coordinates times one minus the density of the
coordinates where the functions agree. -/
theorem hammingDist_eq_card_mul_one_sub_dens {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (x y : ∀ i, β i) : (hammingDist x y : 𝕜) = Fintype.card ι * (1 - dens {i | x i = y i}) := by
  rw [mul_sub, mul_one, natCast_card_mul_nnratCast_dens, ← card_filter_eq_add_hammingDist x y]
  push_cast
  ring

/-- **The relative Hamming distance is a probability**: that of the two functions differing at a
uniformly random coordinate. -/
theorem hammingDist_div_eq_expect {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜] (x y : ∀ i, β i) :
    (hammingDist x y : 𝕜) / Fintype.card ι = 𝔼 i, if x i ≠ y i then 1 else 0 := by
  rw [Fintype.expect_boole, nnratCast_dens, hammingDist]

/-- **Splitting a distance**: between two functions at Hamming distance at most `r + s` lies a
function at distance at most `r` from the first and at most `s` from the second. It takes the
values of the second on at most `r` of the coordinates where the two differ, and the values of the
first elsewhere. -/
theorem exists_hammingDist_le_and_hammingDist_le {x y : ∀ i, β i} {r s : ℕ}
    (h : hammingDist x y ≤ r + s) : ∃ z, hammingDist x z ≤ r ∧ hammingDist z y ≤ s := by
  classical
  set D := univ.filter fun i => x i ≠ y i
  obtain ⟨A, hAD, hA⟩ := exists_subset_card_eq (min_le_right r #D)
  refine ⟨fun i => if i ∈ A then y i else x i, ?_, ?_⟩
  · have hfilter : (univ.filter fun i => x i ≠ if i ∈ A then y i else x i) = A := by
      ext i
      by_cases hi : i ∈ A
      · simpa [hi] using (mem_filter.1 (hAD hi)).2
      · simp [hi]
    rw [hammingDist, hfilter, hA]
    exact min_le_left _ _
  · have hfilter : (univ.filter fun i => (if i ∈ A then y i else x i) ≠ y i) = D \ A := by
      ext i
      by_cases hi : i ∈ A <;> simp [hi, D]
    have hD : #D ≤ r + s := h
    rw [hammingDist, hfilter, card_sdiff_of_subset hAD, hA]
    omega

/-! ### Hamming distance one -/

/-- Two functions are at Hamming distance one when they differ at exactly one coordinate. -/
theorem hammingDist_eq_one_iff {x y : ∀ i, β i} :
    hammingDist x y = 1 ↔ ∃ i, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j := by
  rw [hammingDist, card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    have hmem (j : ι) : x j ≠ y j ↔ j = i := by simpa using Finset.ext_iff.1 hi j
    exact ⟨i, (hmem i).2 rfl, fun j hj => not_not.1 fun h => hj ((hmem j).1 h)⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨i, Finset.ext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simpa using hi
    · simpa [hj] using h j hj

/-- Changing one coordinate to a new value moves to Hamming distance one. -/
theorem hammingDist_update_of_ne [DecidableEq ι] {x : ∀ i, β i} {i : ι} {v : β i}
    (h : x i ≠ v) : hammingDist x (update x i v) = 1 :=
  hammingDist_eq_one_iff.2 ⟨i, by simpa using h, fun j hj => (update_of_ne hj _ _).symm⟩

/-- Two functions at Hamming distance at most one that differ at `i` differ only at `i`: changing
the `i`-th coordinate of the first to that of the second gives the second. -/
theorem update_eq_of_hammingDist_le_one [DecidableEq ι] {x y : ∀ i, β i}
    (h : hammingDist x y ≤ 1) {i : ι} (hi : x i ≠ y i) : update x i (y i) = y := by
  funext j
  by_cases hj : j = i
  · subst hj
    exact update_self _ _ _
  · rw [update_of_ne hj]
    by_contra hne
    exact hj (card_le_one.1 h j (by simpa using hne) i (by simpa using hi))

/-- Two Boolean functions at Hamming distance at most one that differ at `i` differ only at `i`:
the second is the first with its `i`-th bit flipped. -/
theorem update_not_eq_of_hammingDist_le_one [DecidableEq ι] {x y : ι → Bool}
    (h : hammingDist x y ≤ 1) {i : ι} (hi : x i ≠ y i) : update x i (!x i) = y := by
  rw [← Bool.eq_not_of_ne (Ne.symm hi), update_eq_of_hammingDist_le_one h hi]

/-- Updating two functions at the same coordinate changes their Hamming distance only through
that coordinate. -/
theorem hammingDist_update_update [DecidableEq ι] (x y : ∀ i, β i) (i : ι) (a b : β i) :
    hammingDist (update x i a) (update y i b) + (if x i ≠ y i then 1 else 0) =
      hammingDist x y + (if a ≠ b then 1 else 0) := by
  have h (u v : ∀ i, β i) : hammingDist u v =
      (if u i ≠ v i then 1 else 0) + ∑ j ∈ univ.erase i, if u j ≠ v j then 1 else 0 := by
    rw [hammingDist, card_filter]
    exact (add_sum_erase _ _ (mem_univ i)).symm
  have hrest : ∑ j ∈ univ.erase i, (if update x i a j ≠ update y i b j then 1 else 0) =
      ∑ j ∈ univ.erase i, if x j ≠ y j then 1 else 0 :=
    sum_congr rfl fun j hj => by
      rw [update_of_ne (ne_of_mem_erase hj), update_of_ne (ne_of_mem_erase hj)]
  rw [h (update x i a) (update y i b), h x y, hrest, update_self, update_self]
  ring

/-- The pairs of `A × B` at Hamming distance one: the edges of the Hamming graph between `A` and
`B`. -/
def hammingEdges (A B : Finset (∀ i, β i)) : Finset ((∀ i, β i) × ∀ i, β i) :=
  (A ×ˢ B).filter fun e => hammingDist e.1 e.2 = 1

variable {A B : Finset (∀ i, β i)}

/-- A pair is an edge between `A` and `B` exactly when its first entry is in `A`, its second entry
is in `B`, and they are at Hamming distance one. -/
@[simp] theorem mem_hammingEdges {e : (∀ i, β i) × ∀ i, β i} :
    e ∈ hammingEdges A B ↔ e.1 ∈ A ∧ e.2 ∈ B ∧ hammingDist e.1 e.2 = 1 := by
  simp [hammingEdges, and_assoc]

/-- There are as many edges from `A` to `B` as from `B` to `A`. -/
theorem card_hammingEdges_comm (A B : Finset (∀ i, β i)) :
    #(hammingEdges A B) = #(hammingEdges B A) :=
  card_bij (fun e _ => e.swap) (fun e he => by simp_all [hammingDist_comm])
    (fun _ _ _ _ h => Prod.swap_injective h)
    fun e he => ⟨e.swap, by simp_all [hammingDist_comm]⟩

/-- Splitting `B` splits the edges. -/
theorem card_hammingEdges_filter_add_card_hammingEdges_filter_not (p : (∀ i, β i) → Prop)
    [DecidablePred p] :
    #(hammingEdges A (B.filter p)) + #(hammingEdges A (B.filter fun b => ¬p b)) =
      #(hammingEdges A B) := by
  have h (q : (∀ i, β i) → Prop) [DecidablePred q] :
      hammingEdges A (B.filter q) = (hammingEdges A B).filter fun e => q e.2 := by
    ext e
    simp only [mem_hammingEdges, mem_filter]
    tauto
  rw [h, h, card_filter_add_card_filter_not]

/-- The number of edges is the sum over `A` of the numbers of neighbors in `B`. -/
theorem card_hammingEdges_eq_sum_card_filter (A B : Finset (∀ i, β i)) :
    #(hammingEdges A B) = ∑ a ∈ A, #{b ∈ B | hammingDist a b = 1} := by
  simp only [hammingEdges, card_filter, sum_product]
