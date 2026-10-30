/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.PairwiseIndependentHash
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Retention by pairwise independent hashing

Fix a target set `B ⊆ Y` and a pairwise independent family `h i : X → Y`. A point `x` is
*retained* by the seed `i` when its hash `h i x` lies in `B`. Each point is then retained with
probability exactly `p = #B / |Y|`, and the retention events of two distinct points are
independent: both are retained with probability exactly `p ^ 2`
(`IsPairwiseIndependentHash.expect_boole_apply_mem_and_apply_mem`). This is sampling at rate `p`
with pairwise independence, the technique of Chor and Goldreich [ChorGoldreich1989] built on the
hash families of Carter and Wegman [CarterWegman1979], [WegmanCarter1981]. For polynomial or affine
hashing over a finite field with a box `B`, the rate `p` ranges over the ratios of box size to
field size.

The number `N i = #{x ∈ S | h i x ∈ B}` of retained points of a finite set `S` therefore has mean
`#S p`, second factorial moment `#S (#S - 1) p ^ 2` and variance `#S p (1 - p)`, and Chebyshev's
inequality bounds its deviations. In particular fewer than half of the expected number of points
are retained with probability at most `4 / (#S p)`. For a single target, `B = {y}`, these are the
cell-size moments of `Complexity.Probability.PairwiseIndependentHash`.

## Main results

* `Cslib.Probability.IsPairwiseIndependentHash.expect_boole_apply_mem`,
  `Cslib.Probability.IsPairwiseIndependentHash.dens_filter_apply_mem`: a point is retained with
  probability `#B / |Y|`.
* `Cslib.Probability.IsPairwiseIndependentHash.expect_boole_apply_mem_and_apply_mem`,
  `Cslib.Probability.IsPairwiseIndependentHash.dens_filter_apply_mem_and_apply_mem`: two distinct
  points are retained independently.
* `Cslib.Probability.IsPairwiseIndependentHash.expect_card_filter_apply_mem`,
  `Cslib.Probability.IsPairwiseIndependentHash.expect_card_filter_apply_mem_mul_sub_one`,
  `Cslib.Probability.IsPairwiseIndependentHash.expect_card_filter_apply_mem_sub_sq`: the mean,
  second factorial moment and variance of the number of retained points.
* `Cslib.Probability.IsPairwiseIndependentHash.dens_le_abs_card_filter_apply_mem_sub_le`:
  Chebyshev's inequality for it.
* `Cslib.Probability.IsPairwiseIndependentHash.dens_two_mul_card_filter_apply_mem_lt_le`: fewer
  than half of the expected number of points are retained with probability at most `4 / (#S p)`.

## References

* [B. Chor, O. Goldreich, *On the power of two-point based sampling*][ChorGoldreich1989]
* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

public section

namespace Cslib.Probability.IsPairwiseIndependentHash

open Finset
open scoped BigOperators

variable {ι X Y 𝕜 : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y] {h : ι → X → Y}

/-- **Retention probability**: a point is retained, its hash lying in `B`, with probability
`#B / |Y|`. -/
theorem expect_boole_apply_mem [Semifield 𝕜] [CharZero 𝕜] (hh : IsPairwiseIndependentHash h)
    (x : X) (B : Finset Y) :
    𝔼 i, (if h i x ∈ B then 1 else 0 : 𝕜) = #B / Fintype.card Y := by
  have hpt (i : ι) : (if h i x ∈ B then 1 else 0 : 𝕜) = ∑ y ∈ B, if h i x = y then 1 else 0 :=
    (sum_ite_eq B (h i x) fun _ ↦ (1 : 𝕜)).symm
  simp only [hpt]
  rw [expect_sum_comm]
  simp only [Fintype.expect_boole, hh.dens_filter_apply_eq, NNRat.cast_inv, NNRat.cast_natCast,
    sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Retention probability**: a point is retained, its hash lying in `B`, with probability
`#B / |Y|`. -/
theorem dens_filter_apply_mem (hh : IsPairwiseIndependentHash h) (x : X) (B : Finset Y) :
    dens {i | h i x ∈ B} = #B / Fintype.card Y := by
  have := hh.expect_boole_apply_mem (𝕜 := ℚ≥0) x B
  rwa [Fintype.expect_boole, NNRat.cast_id] at this

/-- **Pairwise independent retention**: two distinct points are retained by `B₁` and `B₂` with
probability `#B₁ / |Y| * (#B₂ / |Y|)`. -/
theorem expect_boole_apply_mem_and_apply_mem [Semifield 𝕜] [CharZero 𝕜]
    (hh : IsPairwiseIndependentHash h) {x₁ x₂ : X} (hx : x₁ ≠ x₂) (B₁ B₂ : Finset Y) :
    𝔼 i, (if h i x₁ ∈ B₁ ∧ h i x₂ ∈ B₂ then 1 else 0 : 𝕜) =
      #B₁ / Fintype.card Y * (#B₂ / Fintype.card Y) := by
  have hpt (i : ι) : (if h i x₁ ∈ B₁ ∧ h i x₂ ∈ B₂ then 1 else 0 : 𝕜) =
      ∑ y₁ ∈ B₁, ∑ y₂ ∈ B₂, if h i x₁ = y₁ ∧ h i x₂ = y₂ then 1 else 0 := by
    have e₂ : (if h i x₂ ∈ B₂ then 1 else 0 : 𝕜) =
        ∑ y₂ ∈ B₂, if h i x₂ = y₂ then 1 else 0 :=
      (sum_ite_eq B₂ (h i x₂) fun _ ↦ (1 : 𝕜)).symm
    rw [ite_and, ← sum_ite_eq B₁ (h i x₁) fun _ ↦ (if h i x₂ ∈ B₂ then 1 else 0 : 𝕜)]
    refine sum_congr rfl fun y₁ _ ↦ ?_
    by_cases hy : h i x₁ = y₁
    · simp only [hy, true_and, ite_true]
      exact e₂
    · simp [hy]
  simp only [hpt]
  rw [expect_sum_comm]
  simp only [expect_sum_comm, Fintype.expect_boole, hh.dens_filter_apply_eq_and_apply_eq hx,
    NNRat.cast_inv, NNRat.cast_pow, NNRat.cast_natCast, sum_const, nsmul_eq_mul]
  ring

/-- **Pairwise independent retention**: two distinct points are retained by `B₁` and `B₂` with
probability `#B₁ / |Y| * (#B₂ / |Y|)`. -/
theorem dens_filter_apply_mem_and_apply_mem (hh : IsPairwiseIndependentHash h) {x₁ x₂ : X}
    (hx : x₁ ≠ x₂) (B₁ B₂ : Finset Y) :
    dens {i | h i x₁ ∈ B₁ ∧ h i x₂ ∈ B₂} = #B₁ / Fintype.card Y * (#B₂ / Fintype.card Y) := by
  have := hh.expect_boole_apply_mem_and_apply_mem (𝕜 := ℚ≥0) hx B₁ B₂
  rwa [Fintype.expect_boole, NNRat.cast_id] at this

/-- **The mean number of retained points** of `S` is `#S * (#B / |Y|)`. -/
theorem expect_card_filter_apply_mem [Semifield 𝕜] [CharZero 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y) :
    𝔼 i, (#{x ∈ S | h i x ∈ B} : 𝕜) = #S * (#B / Fintype.card Y) := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [expect_sum_comm]
  simp only [hh.expect_boole_apply_mem, sum_const, nsmul_eq_mul]

/-- **The second factorial moment of the number of retained points**: the number of ordered
pairs of distinct retained points of `S` has expectation `#S (#S - 1) (#B / |Y|) ^ 2`. -/
theorem expect_card_filter_apply_mem_mul_sub_one [Field 𝕜] [CharZero 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y) :
    𝔼 i, (#{x ∈ S | h i x ∈ B} : 𝕜) * (#{x ∈ S | h i x ∈ B} - 1) =
      #S * (#S - 1) * (#B / Fintype.card Y) ^ 2 := by
  classical
  have hcount (i : ι) : (#{x ∈ S | h i x ∈ B} : 𝕜) * (#{x ∈ S | h i x ∈ B} - 1) =
      ∑ q ∈ S.offDiag, if h i q.1 ∈ B ∧ h i q.2 ∈ B then 1 else 0 := by
    have hoff : {x ∈ S | h i x ∈ B}.offDiag = {q ∈ S.offDiag | h i q.1 ∈ B ∧ h i q.2 ∈ B} := by
      ext q
      simp only [mem_offDiag, mem_filter]
      tauto
    rw [sum_boole, ← hoff, offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  have hpair (q : X × X) (hq : q ∈ S.offDiag) :
      𝔼 i, (if h i q.1 ∈ B ∧ h i q.2 ∈ B then 1 else 0 : 𝕜) = (#B / Fintype.card Y) ^ 2 := by
    rw [hh.expect_boole_apply_mem_and_apply_mem (mem_offDiag.1 hq).2.2, sq]
  simp only [hcount]
  rw [expect_sum_comm, sum_congr rfl hpair, sum_const, nsmul_eq_mul, offDiag_card,
    Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
  ring

/-- **The variance of the number of retained points** is `#S p (1 - p)` with `p = #B / |Y|`. -/
theorem expect_card_filter_apply_mem_sub_sq [Field 𝕜] [CharZero 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y) :
    𝔼 i, ((#{x ∈ S | h i x ∈ B} : 𝕜) - #S * (#B / Fintype.card Y)) ^ 2 =
      #S * (#B / Fintype.card Y) * (1 - #B / Fintype.card Y) := by
  have hsq (i : ι) : ((#{x ∈ S | h i x ∈ B} : 𝕜) - #S * (#B / Fintype.card Y)) ^ 2 =
      (#{x ∈ S | h i x ∈ B} : 𝕜) * (#{x ∈ S | h i x ∈ B} - 1) +
        (1 - 2 * (#S * (#B / Fintype.card Y))) * #{x ∈ S | h i x ∈ B} +
        (#S * (#B / Fintype.card Y)) ^ 2 := by
    ring
  rcases isEmpty_or_nonempty ι with hι | hι
  · rcases S.eq_empty_or_nonempty with rfl | ⟨x, -⟩
    · simp
    rcases B.eq_empty_or_nonempty with rfl | ⟨y, -⟩
    · simp
    exact absurd (hh.nonempty x y) (not_nonempty_iff.2 hι)
  simp only [hsq, expect_add_distrib, ← mul_expect, hh.expect_card_filter_apply_mem_mul_sub_one,
    hh.expect_card_filter_apply_mem, Fintype.expect_const]
  ring

/-- **Chebyshev's inequality for the number of retained points**: it is at distance at least
`ε > 0` from its mean `#S p`, with `p = #B / |Y|`, with probability at most `#S p / ε²`. -/
theorem dens_le_abs_card_filter_apply_mem_sub_le [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y)
    {ε : 𝕜} (hε : 0 < ε) :
    (dens {i | ε ≤ |(#{x ∈ S | h i x ∈ B} : 𝕜) - #S * (#B / Fintype.card Y)|} : 𝕜) ≤
      #S * (#B / Fintype.card Y) / ε ^ 2 := by
  have hmarkov := Fintype.mul_dens_filter_le_expect
    (f := fun i ↦ ((#{x ∈ S | h i x ∈ B} : 𝕜) - #S * (#B / Fintype.card Y)) ^ 2)
    (fun _ ↦ sq_nonneg _) (ε ^ 2)
  simp only [sq_le_sq, abs_of_pos hε] at hmarkov
  rw [le_div_iff₀ (by positivity), mul_comm]
  refine hmarkov.trans ?_
  rw [hh.expect_card_filter_apply_mem_sub_sq]
  have hp : (#B : 𝕜) / Fintype.card Y ≥ 0 := by positivity
  exact mul_le_of_le_one_right (by positivity) (sub_le_self _ hp)

/-- **Lower tail of the number of retained points**: fewer than half of the expected number
`#S p`, with `p = #B / |Y|`, are retained with probability at most `4 / (#S p)`. -/
theorem dens_two_mul_card_filter_apply_mem_lt_le [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (hh : IsPairwiseIndependentHash h) (S : Finset X) (B : Finset Y)
    (hpos : 0 < (#S : 𝕜) * (#B / Fintype.card Y)) :
    (dens {i | 2 * (#{x ∈ S | h i x ∈ B} : 𝕜) < #S * (#B / Fintype.card Y)} : 𝕜) ≤
      4 / (#S * (#B / Fintype.card Y)) := by
  set μ : 𝕜 := #S * (#B / Fintype.card Y)
  have hsub : ({i | 2 * (#{x ∈ S | h i x ∈ B} : 𝕜) < μ} : Finset ι) ⊆
      ({i | μ / 2 ≤ |(#{x ∈ S | h i x ∈ B} : 𝕜) - μ|} : Finset ι) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  calc (dens {i | 2 * (#{x ∈ S | h i x ∈ B} : 𝕜) < μ} : 𝕜)
      ≤ (dens {i | μ / 2 ≤ |(#{x ∈ S | h i x ∈ B} : 𝕜) - μ|} : 𝕜) := by
        exact_mod_cast dens_le_dens hsub
    _ ≤ μ / (μ / 2) ^ 2 := hh.dens_le_abs_card_filter_apply_mem_sub_le S B (by positivity)
    _ = 4 / μ := by
        field_simp
        ring

end Cslib.Probability.IsPairwiseIndependentHash
