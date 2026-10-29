/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Group.Int

/-!
# Words

The words of Limaye, Srinivasan and Tavenas [LimayeSrinivasanTavenas2021, §2, p. 6]. A *word* is
a tuple `w : Fin d → ℤ`. Its variables `X(w)` (`WordVar w`) form `d` blocks, block `i` having
`2 ^ |w i|` variables labelled by the bit strings of length `|w i|`, here the numbers below
`2 ^ |w i|`; a choice of one variable in every block (`WordChoice w`) is a set-multilinear
monomial on all blocks. The blocks with `0 ≤ w i` are *positive* (`wordPos w`, LST's `P_w`), the
others *negative* (`wordNeg w`, LST's `N_w`). A word is *`b`-unbiased* (`IsUnbiased w b`) when
every prefix sum has absolute value at most `b`.

The proof of LST Lemma 13 (§4, p. 10) builds an unbiased word greedily over an alphabet `{a, -k}`:
the next letter is `a` when the sum of the letters so far is at most `0`, and `-k` otherwise
(`greedyWord`). It is `k`-unbiased when `0 ≤ a ≤ k` (`isUnbiased_greedyWord`). The proof of LST
Lemma 15 (§5, p. 12) uses this word with `a = ⌊k / √2⌋`.

## Main definitions

* `Cslib.Circuits.Arithmetic.WordVar`, `Cslib.Circuits.Arithmetic.WordChoice`: the variables
  `X(w)` and the set-multilinear monomials on all blocks.
* `Cslib.Circuits.Arithmetic.wordBlocks`, `Cslib.Circuits.Arithmetic.wordPos`,
  `Cslib.Circuits.Arithmetic.wordNeg`: the positive and negative blocks.
* `Cslib.Circuits.Arithmetic.IsUnbiased`: `b`-unbiased words.
* `Cslib.Circuits.Arithmetic.greedyWord`: the greedy word of the proof of LST Lemma 13.

## Main results

* `Cslib.Circuits.Arithmetic.sum_filter_greedyWord`: the prefix sums of the greedy word.
* `Cslib.Circuits.Arithmetic.isUnbiased_greedyWord`: the greedy word is `k`-unbiased.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1, §2 (words, unbiasedness,
  p. 6) and the proof of Lemma 13 (§4, p. 10). The encoding of bit strings by numbers is original.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

variable {d : ℕ}

/-! ### Variables and blocks -/

/-- The variables `X(w)` of a word `w`: block `i` has `2 ^ |w i|` variables, labelled by the
numbers below `2 ^ |w i|`, that is, by the bit strings of length `|w i|`. -/
abbrev WordVar (w : Fin d → ℤ) : Type :=
  Σ i : Fin d, Fin (2 ^ (w i).natAbs)

/-- A choice of one variable in every block of `X(w)`: a set-multilinear monomial. -/
abbrev WordChoice (w : Fin d → ℤ) : Type :=
  (i : Fin d) → Fin (2 ^ (w i).natAbs)

/-- The blocks of `w` whose signed length satisfies `p`. -/
def wordBlocks (w : Fin d → ℤ) (p : ℤ → Prop) [DecidablePred p] : Finset (Fin d) :=
  {i | p (w i)}

/-- The positive blocks `P_w = {i | 0 ≤ w i}` of a word. -/
abbrev wordPos (w : Fin d → ℤ) : Finset (Fin d) :=
  wordBlocks w (0 ≤ ·)

/-- The negative blocks `N_w = {i | w i < 0}` of a word. -/
abbrev wordNeg (w : Fin d → ℤ) : Finset (Fin d) :=
  wordBlocks w (· < 0)

variable {w : Fin d → ℤ}

/-- A block belongs to `wordBlocks w p` exactly when its signed length satisfies `p`. -/
@[simp]
theorem mem_wordBlocks {p : ℤ → Prop} [DecidablePred p] {i : Fin d} :
    i ∈ wordBlocks w p ↔ p (w i) := by
  simp [wordBlocks]

/-- The negative blocks are the blocks that are not positive. -/
theorem compl_wordPos : (wordPos w)ᶜ = wordNeg w := by
  ext i
  simp

/-! ### Unbiased words -/

variable (w) in
/-- A word is *`b`-unbiased* when every prefix sum `∑ i < t, w i` has absolute value at most
`b` (LST §2, p. 6). -/
def IsUnbiased (b : ℕ) : Prop :=
  ∀ t ≤ d, (∑ i : Fin d with i.val < t, w i).natAbs ≤ b

/-! ### The greedy word (LST, proof of Lemma 13) -/

/-- The prefix sums of the greedy word over the alphabet `{a, -k}`: start at `0`, then add `a`
when the current sum is at most `0`, and add `-k` otherwise. -/
def greedyPrefix (a k : ℤ) : ℕ → ℤ
  | 0 => 0
  | t + 1 => if greedyPrefix a k t ≤ 0 then greedyPrefix a k t + a else greedyPrefix a k t - k

/-- The greedy word of length `d` over the alphabet `{a, -k}` (LST, proof of Lemma 13, p. 10;
used with `a = ⌊k / √2⌋` in the proof of Lemma 15, p. 12): its `i`-th letter is `a` if the sum
of the earlier letters is at most `0`, and `-k` otherwise. -/
def greedyWord (a k : ℤ) (d : ℕ) (i : Fin d) : ℤ :=
  greedyPrefix a k ((i : ℕ) + 1) - greedyPrefix a k i

/-- Every letter of the greedy word is `a` or `-k`. -/
theorem greedyWord_eq_or (a k : ℤ) (i : Fin d) :
    greedyWord a k d i = a ∨ greedyWord a k d i = -k := by
  rw [greedyWord, greedyPrefix]
  split_ifs
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- The prefix sums of the greedy word are the values of `greedyPrefix`. -/
theorem sum_filter_greedyWord (a k : ℤ) {t : ℕ} (ht : t ≤ d) :
    ∑ i : Fin d with i.val < t, greedyWord a k d i = greedyPrefix a k t := by
  rw [Finset.sum_filter]
  simp only [greedyWord]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if j < t then greedyPrefix a k (j + 1) - greedyPrefix a k j else 0) d,
    ← Finset.sum_filter]
  have hr : (Finset.range d).filter (· < t) = Finset.range t := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hr, Finset.sum_range_sub, greedyPrefix, sub_zero]

/-- The prefix sums of the greedy word stay in `[-k, a]` when `0 ≤ a` and `0 ≤ k`. -/
theorem greedyPrefix_mem_Icc {a k : ℤ} (ha : 0 ≤ a) (hk : 0 ≤ k) (t : ℕ) :
    -k ≤ greedyPrefix a k t ∧ greedyPrefix a k t ≤ a := by
  induction t with
  | zero => exact ⟨by rw [greedyPrefix]; omega, by rw [greedyPrefix]; omega⟩
  | succ t ih =>
    rw [greedyPrefix]
    split_ifs <;> omega

/-- **The greedy word is `k`-unbiased** (LST, proof of Lemma 13): if `0 ≤ a ≤ k`, every prefix
sum of the greedy word over `{a, -k}` has absolute value at most `k`. -/
theorem isUnbiased_greedyWord {a : ℤ} {k : ℕ} (ha : 0 ≤ a) (hak : a ≤ k) :
    IsUnbiased (greedyWord a k d) k := by
  intro t ht
  rw [sum_filter_greedyWord _ _ ht]
  obtain ⟨h₁, h₂⟩ := greedyPrefix_mem_Icc ha (Int.natCast_nonneg k) t
  omega

end Cslib.Circuits.Arithmetic
