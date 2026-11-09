/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Density
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pairwise independent hash families

A family of functions `h i : X → Y`, indexed by a seed `i` drawn uniformly from a finite type `ι`,
is *pairwise independent* (`Cslib.Probability.IsPairwiseIndependentHash`) if each value `h i x` is
uniformly distributed on `Y` and the values at any two distinct points are independent
[Arora and Barak, Definition 8.14][AroraBarak09]. Wegman and Carter call such families *strongly
universal₂* [WegmanCarter1981], after the universal families of [CarterWegman1979]. Probabilities
over the seed are densities `Finset.dens` of sets of seeds, and averages are uniform expectations
`𝔼 i`.

Fix a finite set `S ⊆ X` and a target `y : Y`. The size `N i = #{x ∈ S | h i x = y}` of the
*cell* of `y` has mean `μ = #S / |Y|` and second factorial moment
`𝔼 N (N - 1) = #S (#S - 1) / |Y|²`, so its variance is `μ (1 - 1 / |Y|) ≤ μ`, and Chebyshev's
inequality bounds its deviations. For the probability that `S` hits `y`:

* it is at most `μ` (`IsPairwiseIndependentHash.dens_filter_mem_image_le`), so at most `1 / k`
  when `k #S ≤ |Y|`;
* `S` misses `y` with probability at most `1 / μ`
  (`IsPairwiseIndependentHash.dens_filter_notMem_image_le`), so `S` hits `y` with probability at
  least `1 - 1 / k` when `#S ≥ k |Y|`;
* it is at least `μ - #S (#S - 1) / (2 |Y|²)` by inclusion–exclusion, hence at least `3 μ / 4` when
  `2 #S ≤ |Y|`: the analysis of the set lower bound protocol of Goldwasser and Sipser
  [GoldwasserSipser1986] in [Arora and Barak, Section 8.2][AroraBarak09].

The same argument shows that exactly one element of `S` hits `y` with probability at least
`μ - #S (#S - 1) / |Y|²`, hence at least `3 / 16` when `|Y| ≤ 4 #S ≤ 2 |Y|`: the lemma of Valiant
and Vazirani [ValiantVazirani1986] in [Arora and Barak, Section 17.4][AroraBarak09], where the bound
is `1 / 8`.

## Main definitions

* `Cslib.Probability.IsPairwiseIndependentHash`: pairwise independent hash families.

## Main results

* `Cslib.Probability.IsPairwiseIndependentHash.expect_card_filter_apply_eq`,
  `Cslib.Probability.IsPairwiseIndependentHash.expect_card_filter_mul_card_filter_sub_one`: the
  first two factorial moments of the size of a cell.
* `Cslib.Probability.IsPairwiseIndependentHash.expect_card_filter_sub_sq`: its variance.
* `Cslib.Probability.IsPairwiseIndependentHash.dens_filter_le_abs_sub_le`: Chebyshev's inequality.
* `Cslib.Probability.IsPairwiseIndependentHash.dens_filter_mem_image_le`,
  `Cslib.Probability.IsPairwiseIndependentHash.dens_filter_notMem_image_le`: the probability that
  `S` hits a target is at most `μ`, and that it misses it at most `1 / μ`.
* `Cslib.Probability.IsPairwiseIndependentHash.three_quarters_mul_le_dens_filter_mem_image`: the
  set lower bound protocol.
* `Cslib.Probability.IsPairwiseIndependentHash.card_filter_mem_image_mul_le`,
  `Cslib.Probability.IsPairwiseIndependentHash.card_filter_notMem_image_mul_le`: the same two
  bounds in counts.
* `Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_notMem_image_le`,
  `Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_mem_image_le`: in counts, a
  target is missed by at most a quarter of the seeds when `#S ≥ 4 |Y|`, and hit by at most a
  quarter when `4 #S ≤ |Y|`.
* `Cslib.Probability.IsPairwiseIndependentHash.comp_seedEquiv`: relabelling seeds.
* `Cslib.Probability.IsPairwiseIndependentHash.three_sixteenths_le_dens_filter_card_filter_eq_one`:
  the Valiant–Vazirani lemma.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [L. G. Valiant, V. V. Vazirani, *NP is as easy as detecting unique
  solutions*][ValiantVazirani1986]
-/

@[expose] public section

namespace Cslib.Probability

open Finset
open scoped BigOperators

variable {ι X Y 𝕜 : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]

/-- A family of functions `h i : X → Y`, indexed by a seed `i : ι` drawn uniformly at random, is
*pairwise independent* if every value `h i x` is uniformly distributed on `Y`, and the values
`h i x₁` and `h i x₂` at distinct points are independent: a `1 / |Y|` fraction of the seeds sends
`x` to `y`, and a `1 / |Y|²` fraction sends `x₁ ≠ x₂` to `y₁` and `y₂`. The first condition
follows from the second unless `X` has exactly one element. -/
structure IsPairwiseIndependentHash (h : ι → X → Y) : Prop where
  /-- Every value is uniformly distributed. -/
  dens_filter_apply_eq (x : X) (y : Y) : dens {i | h i x = y} = (Fintype.card Y : ℚ≥0)⁻¹
  /-- The values at two distinct points are independent. -/
  dens_filter_apply_eq_and_apply_eq {x₁ x₂ : X} (hx : x₁ ≠ x₂) (y₁ y₂ : Y) :
    dens {i | h i x₁ = y₁ ∧ h i x₂ = y₂} = ((Fintype.card Y : ℚ≥0) ^ 2)⁻¹

omit [Fintype Y] in
/-- `S` hits `y` exactly when the cell of `y` is nonempty. -/
private theorem mem_image_iff_card_filter_pos (f : X → Y) (S : Finset X) (y : Y) :
    y ∈ S.image f ↔ 0 < #{x ∈ S | f x = y} := by
  rw [mem_image, card_pos, filter_nonempty_iff]

/-- Inclusion–exclusion for a count `n`: `n - n (n - 1) / 2` is at most the indicator of `n ≠ 0`. -/
private theorem natCast_sub_mul_sub_one_div_two_le [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (n : ℕ) :
    (n : 𝕜) - n * (n - 1) / 2 ≤ if 0 < n then 1 else 0 := by
  rcases n with _ | _ | n
  · simp
  · simp
  · rw [ite_eq_left (Nat.succ_pos _)]
    push_cast
    nlinarith

/-- `n - n (n - 1)` is at most the indicator of `n = 1`. -/
private theorem natCast_sub_mul_sub_one_le [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (n : ℕ) : (n : 𝕜) - n * (n - 1) ≤ if n = 1 then 1 else 0 := by
  rcases n with _ | _ | n
  · simp
  · simp
  · rw [ite_eq_right (by omega)]
    push_cast
    nlinarith

namespace IsPairwiseIndependentHash

variable {h : ι → X → Y}

/-- A pairwise independent family with a point `x : X` and a value `y : Y` has a seed. -/
theorem nonempty (hh : IsPairwiseIndependentHash h) (x : X) (y : Y) : Nonempty ι := by
  have : Nonempty Y := ⟨y⟩
  obtain ⟨i, -⟩ : ({i | h i x = y} : Finset ι).Nonempty := by
    rw [← dens_ne_zero, hh.dens_filter_apply_eq]
    simp [Fintype.card_ne_zero]
  exact ⟨i⟩

/-- Restricting a pairwise independent family along an injective map keeps it pairwise
independent. -/
theorem comp (hh : IsPairwiseIndependentHash h) {X' : Type*} {e : X' → X}
    (he : Function.Injective e) : IsPairwiseIndependentHash fun i => h i ∘ e where
  dens_filter_apply_eq x y := hh.dens_filter_apply_eq (e x) y
  dens_filter_apply_eq_and_apply_eq hx y₁ y₂ :=
    hh.dens_filter_apply_eq_and_apply_eq (he.ne hx) y₁ y₂

omit [Fintype Y] [DecidableEq Y] in
/-- Relabelling the seeds by an equivalence does not change densities. -/
theorem dens_filter_comp_equiv {ι' : Type*} [Fintype ι'] (e : ι' ≃ ι) (P : ι → Prop)
    [DecidablePred P] : dens {i' | P (e i')} = dens {i | P i} := by
  rw [dens_eq_card_div_card, dens_eq_card_div_card, Fintype.card_congr e]
  congr 2
  exact card_equiv e fun i' => by simp

/-- **Relabelling seeds**: precomposing the seeds of a pairwise independent family with an
equivalence keeps it pairwise independent. -/
theorem comp_seedEquiv {ι' : Type*} [Fintype ι'] (hh : IsPairwiseIndependentHash h)
    (e : ι' ≃ ι) : IsPairwiseIndependentHash fun i => h (e i) where
  dens_filter_apply_eq x y := by
    rw [dens_filter_comp_equiv e fun i => h i x = y]
    exact hh.dens_filter_apply_eq x y
  dens_filter_apply_eq_and_apply_eq hx y₁ y₂ := by
    rw [dens_filter_comp_equiv e fun i => h i _ = y₁ ∧ h i _ = y₂]
    exact hh.dens_filter_apply_eq_and_apply_eq hx y₁ y₂

/-- **The mean cell size**: `#{x ∈ S | h i x = y}` has expectation `#S / |Y|`. -/
theorem expect_card_filter_apply_eq [Semifield 𝕜] [CharZero 𝕜] (hh : IsPairwiseIndependentHash h)
    (S : Finset X) (y : Y) :
    𝔼 i, (#{x ∈ S | h i x = y} : 𝕜) = #S / Fintype.card Y := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [expect_sum_comm]
  simp only [Fintype.expect_boole, hh.dens_filter_apply_eq, NNRat.cast_inv, NNRat.cast_natCast,
    sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **The second factorial moment of the cell size**: `N (N - 1)`, the number of ordered pairs of
distinct elements of the cell `N = #{x ∈ S | h i x = y}`, has expectation `#S (#S - 1) / |Y|²`. -/
theorem expect_card_filter_mul_card_filter_sub_one [Field 𝕜] [CharZero 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (y : Y) :
    𝔼 i, (#{x ∈ S | h i x = y} : 𝕜) * (#{x ∈ S | h i x = y} - 1) =
      #S * (#S - 1) / Fintype.card Y ^ 2 := by
  classical
  have hcell : ∀ i, (#{x ∈ S | h i x = y} : 𝕜) * (#{x ∈ S | h i x = y} - 1) =
      ∑ p ∈ S.offDiag, if h i p.1 = y ∧ h i p.2 = y then 1 else 0 := by
    intro i
    have hoff : {x ∈ S | h i x = y}.offDiag = {p ∈ S.offDiag | h i p.1 = y ∧ h i p.2 = y} := by
      ext p
      simp only [mem_offDiag, mem_filter]
      tauto
    rw [sum_boole, ← hoff, offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  have hpair : ∀ p ∈ S.offDiag, 𝔼 i, (if h i p.1 = y ∧ h i p.2 = y then 1 else 0 : 𝕜) =
      ((Fintype.card Y : 𝕜) ^ 2)⁻¹ := by
    intro p hp
    rw [Fintype.expect_boole, hh.dens_filter_apply_eq_and_apply_eq (mem_offDiag.1 hp).2.2,
      NNRat.cast_inv, NNRat.cast_pow, NNRat.cast_natCast]
  simp only [hcell]
  rw [expect_sum_comm, sum_congr rfl hpair, sum_const, nsmul_eq_mul, offDiag_card,
    Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
  ring

/-- **The variance of the cell size**: `#{x ∈ S | h i x = y}` has variance
`#S / |Y| * (1 - 1 / |Y|)`. -/
theorem expect_card_filter_sub_sq [Field 𝕜] [CharZero 𝕜] (hh : IsPairwiseIndependentHash h)
    (S : Finset X) (y : Y) :
    𝔼 i, ((#{x ∈ S | h i x = y} : 𝕜) - #S / Fintype.card Y) ^ 2 =
      #S / Fintype.card Y * (1 - 1 / Fintype.card Y) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, -⟩
  · simp
  have := hh.nonempty x y
  have : Nonempty Y := ⟨y⟩
  have hq : (Fintype.card Y : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsq : ∀ i, ((#{x ∈ S | h i x = y} : 𝕜) - #S / Fintype.card Y) ^ 2 =
      (#{x ∈ S | h i x = y} : 𝕜) * (#{x ∈ S | h i x = y} - 1) +
        (1 - 2 * (#S / Fintype.card Y)) * #{x ∈ S | h i x = y} +
        (#S / Fintype.card Y) ^ 2 := fun i => by ring
  simp only [hsq]
  rw [expect_add_distrib, expect_add_distrib, ← mul_expect, Fintype.expect_const,
    hh.expect_card_filter_mul_card_filter_sub_one, hh.expect_card_filter_apply_eq]
  field_simp
  ring

/-- **The variance of the cell size is at most its mean** `#S / |Y|`. -/
theorem expect_card_filter_sub_sq_le [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (y : Y) :
    𝔼 i, ((#{x ∈ S | h i x = y} : 𝕜) - #S / Fintype.card Y) ^ 2 ≤ #S / Fintype.card Y := by
  rw [hh.expect_card_filter_sub_sq]
  exact mul_le_of_le_one_right (by positivity) (sub_le_self _ (by positivity))

/-- **Chebyshev's inequality for the cell size**: `#{x ∈ S | h i x = y}` is at distance at least
`ε > 0` from its mean `μ = #S / |Y|` with probability at most `μ / ε²`. -/
theorem dens_filter_le_abs_sub_le [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (y : Y) {ε : 𝕜} (hε : 0 < ε) :
    (dens {i | ε ≤ |(#{x ∈ S | h i x = y} : 𝕜) - #S / Fintype.card Y|} : 𝕜) ≤
      #S / Fintype.card Y / ε ^ 2 := by
  have hmarkov := Fintype.mul_dens_filter_le_expect
    (f := fun i => ((#{x ∈ S | h i x = y} : 𝕜) - #S / Fintype.card Y) ^ 2)
    (fun _ => sq_nonneg _) (ε ^ 2)
  simp only [sq_le_sq, abs_of_pos hε] at hmarkov
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact hmarkov.trans (hh.expect_card_filter_sub_sq_le S y)

/-- **First moment bound**: `S` hits `y` with probability at most the mean cell size
`#S / |Y|`. -/
theorem dens_filter_mem_image_le (hh : IsPairwiseIndependentHash h) (S : Finset X) (y : Y) :
    dens {i | y ∈ S.image (h i)} ≤ #S / Fintype.card Y := by
  calc dens {i | y ∈ S.image (h i)} = 𝔼 i, (if y ∈ S.image (h i) then 1 else 0 : ℚ≥0) := by
        rw [Fintype.expect_boole, NNRat.cast_id]
    _ ≤ 𝔼 i, (#{x ∈ S | h i x = y} : ℚ≥0) := by
        refine expect_le_expect fun i _ => ?_
        split_ifs with hi
        · exact Nat.one_le_cast.2 ((mem_image_iff_card_filter_pos _ _ _).1 hi)
        · positivity
    _ = #S / Fintype.card Y := hh.expect_card_filter_apply_eq S y

/-- **Second moment bound**: a nonempty `S` misses `y` with probability at most the inverse
`|Y| / #S` of the mean cell size. -/
theorem dens_filter_notMem_image_le (hh : IsPairwiseIndependentHash h) {S : Finset X}
    (hS : S.Nonempty) (y : Y) :
    dens {i | y ∉ S.image (h i)} ≤ Fintype.card Y / #S := by
  have : Nonempty Y := ⟨y⟩
  have hμ : (0 : ℚ) < #S / Fintype.card Y := by
    have := hS.card_pos
    have := Fintype.card_pos (α := Y)
    positivity
  have hsub : ({i | y ∉ S.image (h i)} : Finset ι) ⊆
      ({i | (#S / Fintype.card Y : ℚ) ≤ |(#{x ∈ S | h i x = y} : ℚ) - #S / Fintype.card Y|} :
        Finset ι) := by
    intro i hi
    rw [mem_filter, mem_image_iff_card_filter_pos, not_lt, Nat.le_zero] at hi
    rw [mem_filter, hi.2, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hμ]
    exact ⟨mem_univ _, le_rfl⟩
  rw [← NNRat.cast_le (K := ℚ)]
  calc ((dens {i | y ∉ S.image (h i)} : ℚ≥0) : ℚ) ≤
        dens {i | (#S / Fintype.card Y : ℚ) ≤
          |(#{x ∈ S | h i x = y} : ℚ) - #S / Fintype.card Y|} :=
        NNRat.cast_le.2 (dens_le_dens hsub)
    _ ≤ #S / Fintype.card Y / (#S / Fintype.card Y) ^ 2 := hh.dens_filter_le_abs_sub_le S y hμ
    _ = ((Fintype.card Y / #S : ℚ≥0) : ℚ) := by
        rw [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast]
        field_simp

/-- A nonempty `S` hits `y` with probability at least `1 - |Y| / #S`. -/
theorem one_sub_le_dens_filter_mem_image (hh : IsPairwiseIndependentHash h) {S : Finset X}
    (hS : S.Nonempty) (y : Y) :
    1 - Fintype.card Y / #S ≤ dens {i | y ∈ S.image (h i)} := by
  obtain ⟨x, -⟩ := id hS
  have := hh.nonempty x y
  have hsplit := dens_filter_add_dens_filter_not_eq_dens (s := (univ : Finset ι))
    (fun i => y ∈ S.image (h i))
  rw [dens_univ] at hsplit
  rw [tsub_le_iff_right, ← hsplit]
  gcongr
  exact hh.dens_filter_notMem_image_le hS y

/-- **First moment bound, in counts**: the seeds for which `S` hits `y`, times `|Y|`, number at
most `#S` times all seeds. -/
theorem card_filter_mem_image_mul_le (hh : IsPairwiseIndependentHash h) (S : Finset X) (y : Y) :
    #{i | y ∈ S.image (h i)} * Fintype.card Y ≤ #S * Fintype.card ι := by
  have hY : 0 < Fintype.card Y := Fintype.card_pos_iff.2 ⟨y⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hι : 0 < Fintype.card ι := by
    obtain ⟨x, -⟩ := hne
    have := hh.nonempty x y
    exact Fintype.card_pos
  have hd := hh.dens_filter_mem_image_le S y
  rw [dens_eq_card_div_card, div_le_div_iff₀ (by exact_mod_cast hι) (by exact_mod_cast hY)] at hd
  exact_mod_cast hd

/-- **Second moment bound, in counts**: for a nonempty `S`, the seeds for which `S` misses `y`,
times `#S`, number at most `|Y|` times all seeds. -/
theorem card_filter_notMem_image_mul_le (hh : IsPairwiseIndependentHash h) {S : Finset X}
    (hS : S.Nonempty) (y : Y) :
    #{i | y ∉ S.image (h i)} * #S ≤ Fintype.card Y * Fintype.card ι := by
  have hι : 0 < Fintype.card ι := by
    obtain ⟨x, -⟩ := hS
    have := hh.nonempty x y
    exact Fintype.card_pos
  have hd := hh.dens_filter_notMem_image_le hS y
  rw [dens_eq_card_div_card, div_le_div_iff₀ (by exact_mod_cast hι)
    (by exact_mod_cast hS.card_pos)] at hd
  exact_mod_cast hd

/-- **Large sets are hit**: if `#S ≥ 4 |Y|`, at most a quarter of the seeds miss a target, in
counts. -/
theorem four_mul_card_filter_notMem_image_le (hh : IsPairwiseIndependentHash h) {S : Finset X}
    (hS : 4 * Fintype.card Y ≤ #S) (y : Y) :
    4 * #{i | y ∉ S.image (h i)} ≤ Fintype.card ι := by
  have hY : 0 < Fintype.card Y := Fintype.card_pos_iff.2 ⟨y⟩
  have hd' := hh.card_filter_notMem_image_mul_le (S := S) (card_pos.1 (by omega)) y
  nlinarith

/-- **Small sets are missed**: if `4 #S ≤ |Y|`, at most a quarter of the seeds hit a target, in
counts. -/
theorem four_mul_card_filter_mem_image_le (hh : IsPairwiseIndependentHash h) {S : Finset X}
    (hS : 4 * #S ≤ Fintype.card Y) (y : Y) :
    4 * #{i | y ∈ S.image (h i)} ≤ Fintype.card ι := by
  have hY : 0 < Fintype.card Y := Fintype.card_pos_iff.2 ⟨y⟩
  have hd' := hh.card_filter_mem_image_mul_le S y
  nlinarith

/-- **Inclusion–exclusion for hitting a target**: `S` hits `y` with probability at least
`#S / |Y| - #S (#S - 1) / (2 |Y|²)`. -/
theorem sub_le_dens_filter_mem_image [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (y : Y) :
    (#S : 𝕜) / Fintype.card Y - #S * (#S - 1) / (2 * Fintype.card Y ^ 2) ≤
      (dens {i | y ∈ S.image (h i)} : 𝕜) := by
  calc (#S : 𝕜) / Fintype.card Y - #S * (#S - 1) / (2 * Fintype.card Y ^ 2)
      = 𝔼 i, ((#{x ∈ S | h i x = y} : 𝕜) -
          #{x ∈ S | h i x = y} * (#{x ∈ S | h i x = y} - 1) / 2) := by
        rw [expect_sub_distrib, ← expect_div, hh.expect_card_filter_apply_eq,
          hh.expect_card_filter_mul_card_filter_sub_one]
        ring
    _ ≤ 𝔼 i, (if y ∈ S.image (h i) then 1 else 0 : 𝕜) := by
        refine expect_le_expect fun i _ => ?_
        simp only [mem_image_iff_card_filter_pos]
        exact natCast_sub_mul_sub_one_div_two_le _
    _ = _ := Fintype.expect_boole _

/-- **The set lower bound protocol** of Goldwasser and Sipser: if `2 #S ≤ |Y|`, then `S` hits `y`
with probability at least three quarters of the mean cell size `#S / |Y|`
[Arora and Barak, Section 8.2][AroraBarak09]. -/
theorem three_quarters_mul_le_dens_filter_mem_image (hh : IsPairwiseIndependentHash h)
    {S : Finset X} (y : Y) (hS : 2 * #S ≤ Fintype.card Y) :
    3 / 4 * (#S / Fintype.card Y : ℚ≥0) ≤ dens {i | y ∈ S.image (h i)} := by
  have : Nonempty Y := ⟨y⟩
  rw [← NNRat.cast_le (K := ℚ)]
  refine le_trans ?_ (hh.sub_le_dens_filter_mem_image S y)
  have hq : (0 : ℚ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  have hS' : 2 * (#S : ℚ) ≤ Fintype.card Y := by exact_mod_cast hS
  push_cast
  rw [div_sub_div _ _ hq.ne' (by positivity), mul_div_assoc', div_le_div_iff₀ (by positivity)
    (by positivity)]
  have hs : (0 : ℚ) ≤ #S := (#S).cast_nonneg
  nlinarith [mul_nonneg (mul_nonneg hs (sq_nonneg (Fintype.card Y : ℚ))) (sub_nonneg.2 hS'),
    mul_nonneg hs (sq_nonneg (Fintype.card Y : ℚ))]

/-- **Inclusion–exclusion for a unique preimage**: exactly one element of `S` hits `y` with
probability at least `#S / |Y| - #S (#S - 1) / |Y|²`. -/
theorem sub_le_dens_filter_card_filter_eq_one [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (hh : IsPairwiseIndependentHash h) (S : Finset X) (y : Y) :
    (#S : 𝕜) / Fintype.card Y - #S * (#S - 1) / Fintype.card Y ^ 2 ≤
      (dens {i | #{x ∈ S | h i x = y} = 1} : 𝕜) := by
  calc (#S : 𝕜) / Fintype.card Y - #S * (#S - 1) / Fintype.card Y ^ 2
      = 𝔼 i, ((#{x ∈ S | h i x = y} : 𝕜) -
          #{x ∈ S | h i x = y} * (#{x ∈ S | h i x = y} - 1)) := by
        rw [expect_sub_distrib, hh.expect_card_filter_apply_eq,
          hh.expect_card_filter_mul_card_filter_sub_one]
    _ ≤ 𝔼 i, (if #{x ∈ S | h i x = y} = 1 then 1 else 0 : 𝕜) :=
        expect_le_expect fun i _ => natCast_sub_mul_sub_one_le _
    _ = _ := Fintype.expect_boole _

/-- **The Valiant–Vazirani lemma**: if `|Y| ≤ 4 #S ≤ 2 |Y|`, then exactly one element of `S` hits
`y` with probability at least `3 / 16` [Arora and Barak, Section 17.4][AroraBarak09]. -/
theorem three_sixteenths_le_dens_filter_card_filter_eq_one (hh : IsPairwiseIndependentHash h)
    {S : Finset X} (y : Y) (hS₁ : Fintype.card Y ≤ 4 * #S) (hS₂ : 2 * #S ≤ Fintype.card Y) :
    3 / 16 ≤ dens {i | #{x ∈ S | h i x = y} = 1} := by
  have : Nonempty Y := ⟨y⟩
  rw [← NNRat.cast_le (K := ℚ)]
  refine le_trans ?_ (hh.sub_le_dens_filter_card_filter_eq_one S y)
  have hq : (0 : ℚ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  have hS₁' : (Fintype.card Y : ℚ) ≤ 4 * #S := by exact_mod_cast hS₁
  have hS₂' : 2 * (#S : ℚ) ≤ Fintype.card Y := by exact_mod_cast hS₂
  push_cast
  rw [div_sub_div _ _ hq.ne' (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hS₁') (sub_nonneg.2 hS₂')]

end IsPairwiseIndependentHash

end Cslib.Probability
