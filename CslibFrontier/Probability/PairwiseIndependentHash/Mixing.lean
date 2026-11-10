/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PairwiseIndependentHash
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.PairwiseIndependentHash.Retention
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The hash mixing lemma

Let `h i : X → X` be a pairwise independent family of functions of a finite set `X` to itself and
let `A` and `B` be subsets of `X`, of densities `α` and `β`. For a uniformly random seed `i`, the
density of `{x ∈ A | h i x ∈ B}` has mean `α β`, the density of `A × B`, and variance exactly
`α β (1 - β) / |X|` (`IsPairwiseIndependentHash.expect_dens_filter_apply_mem_sub_sq`). Hence its
mean absolute deviation from `α β` is at most `√(α β / |X|)`
(`IsPairwiseIndependentHash.expect_abs_dens_filter_apply_mem_sub_le`): a random member of the
family mixes every rectangle `A × B` up to an error that is small when `|X|` is large. This is the
hash mixing lemma of Nisan's generator for space-bounded computation [Nisan1992], in expectation
form. Its proof rescales the variance of the number of retained points
(`IsPairwiseIndependentHash.expect_card_filter_apply_mem_sub_sq`).

## Main results

* `Cslib.Probability.IsPairwiseIndependentHash.expect_dens_filter_apply_mem_sub_sq`: the variance
  of the density of `{x ∈ A | h i x ∈ B}`.
* `Cslib.Probability.IsPairwiseIndependentHash.expect_abs_dens_filter_apply_mem_sub_le`: the hash
  mixing lemma.

## References

* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
-/

public section

namespace Cslib.Probability.IsPairwiseIndependentHash

open Finset
open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [Fintype X] [DecidableEq X] {h : ι → X → X}

/-- **The variance of a hashed rectangle**: for a pairwise independent family `h i : X → X`, the
density of `{x ∈ A | h i x ∈ B}` has variance `α β (1 - β) / |X|` about `α β`, where `α` and `β`
are the densities of `A` and `B`. -/
theorem expect_dens_filter_apply_mem_sub_sq (hh : IsPairwiseIndependentHash h) (A B : Finset X) :
    𝔼 i, ((dens {x ∈ A | h i x ∈ B} : ℝ) - A.dens * B.dens) ^ 2 =
      A.dens * B.dens * (1 - B.dens) / Fintype.card X := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp [Finset.eq_empty_of_isEmpty A]
  have hcard : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hvar := hh.expect_card_filter_apply_mem_sub_sq (𝕜 := ℝ) A B
  have hpt (i : ι) : ((dens {x ∈ A | h i x ∈ B} : ℝ) - A.dens * B.dens) ^ 2 =
      ((#{x ∈ A | h i x ∈ B} : ℝ) - #A * (#B / Fintype.card X)) ^ 2 / Fintype.card X ^ 2 := by
    simp only [dens, NNRat.cast_div, NNRat.cast_natCast]
    field_simp
  rw [Finset.expect_congr rfl fun i _ => hpt i, ← expect_div, hvar]
  simp only [dens, NNRat.cast_div, NNRat.cast_natCast]
  field_simp

/-- **The hash mixing lemma** [Nisan1992]: for a pairwise independent family `h i : X → X` and
sets `A` and `B` of densities `α` and `β`, the density of `{x ∈ A | h i x ∈ B}` differs from
`α β` on average by at most `√(α β / |X|)`. -/
theorem expect_abs_dens_filter_apply_mem_sub_le (hh : IsPairwiseIndependentHash h)
    (A B : Finset X) :
    𝔼 i, |(dens {x ∈ A | h i x ∈ B} : ℝ) - A.dens * B.dens| ≤
      √(A.dens * B.dens / Fintype.card X) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [univ_eq_empty, expect_empty]
    positivity
  calc 𝔼 i, |(dens {x ∈ A | h i x ∈ B} : ℝ) - A.dens * B.dens|
      ≤ √(𝔼 i, |(dens {x ∈ A | h i x ∈ B} : ℝ) - A.dens * B.dens| ^ 2) :=
        Real.le_sqrt_of_sq_le (sq_expect_le_expect_sq _ _)
    _ = √(A.dens * B.dens * (1 - B.dens) / Fintype.card X) := by
        simp only [sq_abs, hh.expect_dens_filter_apply_mem_sub_sq]
    _ ≤ √(A.dens * B.dens / Fintype.card X) := by
        gcongr √(?_ / _)
        exact mul_le_of_le_one_right (by positivity) (sub_le_self 1 (by positivity))

end Cslib.Probability.IsPairwiseIndependentHash
