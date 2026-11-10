/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod

/-!
# Concatenated codes

Given an *outer* word `c : ι → A` over a large alphabet `A` and an *inner* encoding
`inner : A → κ → B` of the letters of `A` as words over a small alphabet `B`, the *concatenated*
word `Cslib.Code.concat inner c : ι × κ → B` replaces every letter `c i` by the inner codeword
`inner (c i)` [Forney1966], [GuruswamiRudraSudan2019]. The distance between two concatenated
words is the sum of the distances between their blocks (`Cslib.Code.hammingDist_concat`). If
distinct letters have inner codewords at distance at least `d_in`, every coordinate where the
outer words differ contributes at least `d_in`, so concatenating a code of minimum distance at
least `d_out` gives a code of minimum distance at least `d_out * d_in`
(`Cslib.Code.le_minDist_image_concat`).

## Main definitions

* `Cslib.Code.concat`: the concatenation of an outer word with an inner encoding.

## Main results

* `Cslib.Code.hammingDist_concat`: the distance of concatenated words is the sum over the blocks.
* `Cslib.Code.mul_hammingDist_le_hammingDist_concat`: each outer disagreement costs `d_in`.
* `Cslib.Code.le_minDist_image_concat`: the minimum distance of a concatenated code is at least
  the product of the minimum distances.

## References

* [G. D. Forney, *Concatenated Codes*][Forney1966]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset

variable {ι κ A B : Type*}

/-- The *concatenation* of the outer word `c : ι → A` with the inner encoding
`inner : A → κ → B`: the word on `ι × κ` whose block at `i` is the inner codeword of `c i`. -/
def concat (inner : A → κ → B) (c : ι → A) : ι × κ → B :=
  fun x => inner (c x.1) x.2

/-- The concatenated word at `(i, j)` is the letter at `j` of the inner codeword of `c i`. -/
@[simp]
theorem concat_apply (inner : A → κ → B) (c : ι → A) (i : ι) (j : κ) :
    concat inner c (i, j) = inner (c i) j :=
  rfl

/-- With an injective inner encoding, concatenation is injective. -/
theorem concat_injective {inner : A → κ → B} (hinner : Function.Injective inner) :
    Function.Injective (concat (ι := ι) inner) := fun _ _ h =>
  funext fun i => hinner (funext fun j => congrFun h (i, j))

variable [Fintype ι] [Fintype κ] [DecidableEq B]

/-- The distance between two concatenated words is the sum of the distances between their
blocks. -/
theorem hammingDist_concat (inner : A → κ → B) (c c' : ι → A) :
    hammingDist (concat inner c) (concat inner c') =
      ∑ i, hammingDist (inner (c i)) (inner (c' i)) := by
  simp only [hammingDist, card_filter]
  exact Fintype.sum_prod_type _

variable [DecidableEq A]

/-- If distinct letters have inner codewords at distance at least `d_in`, concatenated words are
at distance at least `d_in` times the distance of the outer words. -/
theorem mul_hammingDist_le_hammingDist_concat {inner : A → κ → B} {dIn : ℕ}
    (hinner : ∀ a b, a ≠ b → dIn ≤ hammingDist (inner a) (inner b)) (c c' : ι → A) :
    dIn * hammingDist c c' ≤ hammingDist (concat inner c) (concat inner c') := by
  rw [hammingDist_concat]
  calc dIn * hammingDist c c' = ∑ _i ∈ {i | c i ≠ c' i}, dIn := by
        rw [sum_const, smul_eq_mul, mul_comm]
        rfl
    _ ≤ ∑ i ∈ {i | c i ≠ c' i}, hammingDist (inner (c i)) (inner (c' i)) :=
        sum_le_sum fun i hi => hinner _ _ (mem_filter.1 hi).2
    _ ≤ ∑ i, hammingDist (inner (c i)) (inner (c' i)) := sum_le_sum_of_subset (subset_univ _)

/-- **The distance of concatenated codes** [Forney1966]. Concatenating an outer code of minimum
distance at least `d_out` with an inner encoding whose codewords for distinct letters are at
distance at least `d_in` gives a code of minimum distance at least `d_out * d_in`. -/
theorem le_minDist_image_concat {C : Set (ι → A)} {dOut dIn : ℕ}
    (hC : (dOut : ℕ∞) ≤ minDist C) {inner : A → κ → B}
    (hinner : ∀ a b, a ≠ b → dIn ≤ hammingDist (inner a) (inner b)) :
    ((dOut * dIn : ℕ) : ℕ∞) ≤ minDist (concat inner '' C) := by
  refine le_minDist_iff.2 ?_
  rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hne
  have hcc' : c ≠ c' := fun h => hne (h ▸ rfl)
  have h := Nat.cast_le.1 (le_minDist_iff.1 hC c hc c' hc' hcc')
  exact Nat.cast_le.2 ((Nat.mul_le_mul_right dIn h).trans
    (by rw [mul_comm]; exact mul_hammingDist_le_hammingDist_concat hinner c c'))

end Cslib.Code
