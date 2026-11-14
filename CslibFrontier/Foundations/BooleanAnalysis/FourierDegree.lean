/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import Mathlib.Data.Finset.Density
import CslibFrontier.Foundations.BooleanAnalysis.Decomposition
import CslibFrontier.Foundations.BooleanAnalysis.MaximalSupport
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Functions of low degree: influence and Schwartz–Zippel on the cube

A real function `g` on the cube has *degree at most `d`* when `g ∈ BitString.lowDegree ℝ ι d`,
equivalently when its Fourier coefficients vanish on the sets of more than `d` coordinates
(`BitString.mem_lowDegree_iff_fourierCoeff_eq_zero`), as in
`DecisionTree.comp_eval_mem_lowDegree` and `DecisionTree.fourierCoeff_eq_zero_of_depth_lt`.

By the spectral formula for the total influence, such a function has total influence at most `d`
times its mean square (`BitString.totalInfluence_le_mul_expect_sq_of_degree`), so a Boolean
function of degree at most `d`, read as signs, has total influence at most `d`
(`BitString.totalInfluence_signVal_le_of_degree`) [O'Donnell, Chapter 3][ODonnell2014]. In degree
one, equality holds in the Poincaré inequality if and only if the function has degree at most one
(`BitString.totalInfluence_eq_expect_sub_expect_sq_iff_mem_lowDegree`), and a Boolean function has
degree at most one (equivalently, total influence equal to its variance) if and only if it is
constant or a literal `x ↦ b ^^ x i` (`BitString.mem_lowDegree_one_signVal_iff`,
`BitString.totalInfluence_signVal_eq_expect_sub_expect_sq_iff`); for balanced Boolean functions
this characterizes average sensitivity one
(`BitString.totalInfluence_signVal_eq_one_iff_of_expect_eq_zero`)
[O'Donnell, Exercise 1.19 and Proposition 2.40][ODonnell2014]
[Arora–Barak, Chapter 19, Exercise 5(b)][AroraBarak07].

**Schwartz–Zippel on the cube**: a nonzero function of degree at most `k` is nonzero on at least a
`2 ^ (-k)` fraction of the cube (`BitString.one_le_two_pow_mul_dens_ne_zero`,
`BitString.two_pow_card_le_two_pow_mul_card_ne_zero`) [O'Donnell, Chapter 3][ODonnell2014]. Take a
set `S` of the Fourier support that is maximal for inclusion. Differentiating in a coordinate of
`S` keeps `S` minus that coordinate maximal in the support of the derivative, while a derivative is
nonzero on at most twice as many points as the function (averaging over one bit); after
differentiating in every coordinate of `S`, the derivative is a nonzero constant.

## Main results

* `Cslib.BitString.totalInfluence_le_mul_expect_sq_of_degree`,
  `Cslib.BitString.totalInfluence_le_mul_expect_sq_of_fourierCoeff_eq_zero`,
  `Cslib.BitString.totalInfluence_signVal_le_of_degree`,
  `Cslib.BitString.totalInfluence_signVal_le_of_fourierCoeff_eq_zero`: the total influence is at
  most the degree times the mean square; a Boolean function has total influence at most its degree.
* `Cslib.BitString.totalInfluence_le_expect_sub_expect_sq_iff_fourierCoeff_eq_zero`,
  `Cslib.BitString.totalInfluence_eq_expect_sub_expect_sq_iff_fourierCoeff_eq_zero`,
  `Cslib.BitString.totalInfluence_le_expect_sub_expect_sq_iff_mem_lowDegree`,
  `Cslib.BitString.totalInfluence_eq_expect_sub_expect_sq_iff_mem_lowDegree`: equality in the
  Poincaré inequality holds if and only if the function has degree at most one.
* `Cslib.BitString.mem_lowDegree_one_signVal_iff`,
  `Cslib.BitString.totalInfluence_signVal_le_expect_sub_expect_sq_iff`,
  `Cslib.BitString.totalInfluence_signVal_eq_expect_sub_expect_sq_iff`,
  `Cslib.BitString.totalInfluence_signVal_le_one_iff_of_expect_eq_zero`,
  `Cslib.BitString.totalInfluence_signVal_eq_one_iff_of_expect_eq_zero`: a Boolean function of
  degree at most one (or with equality in the Poincaré inequality) is constant or a literal; a
  balanced Boolean function has average sensitivity at most one (or equal to one) if and only if it
  is a literal.
* `Cslib.BitString.dens_derivative_ne_zero_le`: a derivative is nonzero at most twice as often as
  the function.
* `Cslib.BitString.one_le_two_pow_mul_dens_ne_zero`,
  `Cslib.BitString.one_le_two_pow_mul_dens_ne_zero_of_fourierCoeff_eq_zero`,
  `Cslib.BitString.two_pow_card_le_two_pow_mul_card_ne_zero`,
  `Cslib.BitString.two_pow_card_le_two_pow_mul_card_ne_zero_of_fourierCoeff_eq_zero`:
  Schwartz–Zippel on the cube.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach* (2007 draft)][AroraBarak07]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Total influence at most the degree times the mean square**, Fourier-coefficient form: a real
function whose Fourier coefficients vanish above degree `d` has total influence at most `d` times
its mean square. -/
theorem totalInfluence_le_mul_expect_sq_of_fourierCoeff_eq_zero (g : (ι → Bool) → ℝ) {d : ℕ}
    (hdeg : ∀ S : Finset ι, d < #S → fourierCoeff g S = 0) :
    totalInfluence g ≤ d * 𝔼 x, g x ^ 2 := by
  rw [totalInfluence_eq_sum_card_mul_fourierCoeff_sq, expect_sq_eq_sum_fourierCoeff_sq, mul_sum]
  refine sum_le_sum fun S _ => ?_
  rcases le_or_gt #S d with h | h
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (sq_nonneg _)
  · rw [hdeg S h]
    simp

/-- **Total influence at most the degree times the mean square**: a real function of degree at most
`d` has total influence at most `d` times its mean square. -/
theorem totalInfluence_le_mul_expect_sq_of_degree (g : (ι → Bool) → ℝ) {d : ℕ}
    (hdeg : g ∈ lowDegree ℝ ι d) :
    totalInfluence g ≤ d * 𝔼 x, g x ^ 2 :=
  totalInfluence_le_mul_expect_sq_of_fourierCoeff_eq_zero g
    (mem_lowDegree_iff_fourierCoeff_eq_zero.1 hdeg)

/-- **Total influence at most the degree**, Fourier-coefficient form: a Boolean function whose
Fourier coefficients, read as signs, vanish above degree `d` has total influence at most `d`
[O'Donnell, Chapter 3][ODonnell2014]. -/
theorem totalInfluence_signVal_le_of_fourierCoeff_eq_zero (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : ∀ S : Finset ι, d < #S → fourierCoeff (fun x => signVal (f x)) S = 0) :
    totalInfluence (fun x => signVal (f x)) ≤ d := by
  have h := totalInfluence_le_mul_expect_sq_of_fourierCoeff_eq_zero _ hdeg
  rwa [expect_sq_eq_sum_fourierCoeff_sq, sum_fourierCoeff_sq_signVal, mul_one] at h

/-- **Total influence at most the degree**: a Boolean function of degree at most `d`, read as
signs, has total influence at most `d` [O'Donnell, Chapter 3][ODonnell2014]. -/
theorem totalInfluence_signVal_le_of_degree (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : (fun x => signVal (f x)) ∈ lowDegree ℝ ι d) :
    totalInfluence (fun x => signVal (f x)) ≤ d :=
  totalInfluence_signVal_le_of_fourierCoeff_eq_zero f
    (mem_lowDegree_iff_fourierCoeff_eq_zero.1 hdeg)

/-- Half a difference is nonzero only where one of the two terms is nonzero. -/
private theorem indicator_half_sub_ne_zero_le (a b : ℝ) :
    (if (a - b) / 2 ≠ 0 then (1 : ℝ) else 0) ≤
      (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) := by
  by_cases hab : a = 0 ∧ b = 0
  · simp [hab.1, hab.2]
  · have h₁ : (if (a - b) / 2 ≠ 0 then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have h₂ : (1 : ℝ) ≤ (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) := by
      split_ifs <;> simp_all
    exact h₁.trans h₂

/-- **A derivative is nonzero at most twice as often as the function**: the density of the points
where the derivative of `h` in `i` is nonzero is at most twice the density of the points where `h`
is nonzero. -/
theorem dens_derivative_ne_zero_le (h : (ι → Bool) → ℝ) (i : ι) :
    (dens {x | derivative i h x ≠ 0} : ℝ) ≤ 2 * (dens {x | h x ≠ 0} : ℝ) := by
  rw [← Fintype.expect_boole, ← Fintype.expect_boole,
    ← expect_update_false_add_update_true (fun x => if h x ≠ 0 then (1 : ℝ) else 0) i]
  exact expect_le_expect fun x _ => indicator_half_sub_ne_zero_le _ _

/-- Iterated differentiation along a set `S` of the Fourier support of `h`, maximal for inclusion:
`h` is nonzero on at least a `2 ^ (-#S)` fraction of the cube. -/
private theorem one_le_two_pow_card_mul_dens_ne_zero (S : Finset ι) :
    ∀ h : (ι → Bool) → ℝ, fourierCoeff h S ≠ 0 → (∀ T, S ⊂ T → fourierCoeff h T = 0) →
      1 ≤ 2 ^ #S * (dens {x | h x ≠ 0} : ℝ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro h hS hT
    have hall : ({x | h x ≠ 0} : Finset (ι → Bool)) = univ :=
      filter_true_of_mem fun x _ => by rwa [apply_eq_fourierCoeff_empty_of_maximal hT x]
    rw [hall, dens_univ, card_empty, pow_zero, one_mul, NNRat.cast_one]
  | insert i S hi ih =>
    intro h hS hT
    have h₁ : fourierCoeff (derivative i h) S ≠ 0 := by
      rwa [fourierCoeff_derivative, ite_eq_right hi]
    have h₂ (T : Finset ι) (hST : S ⊂ T) : fourierCoeff (derivative i h) T = 0 := by
      rw [fourierCoeff_derivative]
      split_ifs with hiT
      · rfl
      · refine hT _ (Finset.ssubset_iff_subset_ne.2
          ⟨insert_subset_insert i hST.1, fun heq => hST.ne ?_⟩)
        rw [← erase_insert hi, heq, erase_insert hiT]
    have hpow : (0 : ℝ) ≤ 2 ^ #S := by positivity
    calc (1 : ℝ) ≤ 2 ^ #S * (dens {x | derivative i h x ≠ 0} : ℝ) := ih _ h₁ h₂
      _ ≤ 2 ^ #S * (2 * (dens {x | h x ≠ 0} : ℝ)) :=
          mul_le_mul_of_nonneg_left (dens_derivative_ne_zero_le h i) hpow
      _ = 2 ^ #(insert i S) * (dens {x | h x ≠ 0} : ℝ) := by
          rw [card_insert_of_notMem hi, pow_succ, mul_assoc]

/-- **Schwartz–Zippel on the cube**, Fourier-coefficient form: a nonzero real function whose
Fourier coefficients vanish above degree `k` is nonzero on at least a `2 ^ (-k)` fraction of the
cube. -/
theorem one_le_two_pow_mul_dens_ne_zero_of_fourierCoeff_eq_zero (g : (ι → Bool) → ℝ) {k : ℕ}
    (hdeg : ∀ S : Finset ι, k < #S → fourierCoeff g S = 0) (hg : g ≠ 0) :
    1 ≤ 2 ^ k * (dens {x | g x ≠ 0} : ℝ) := by
  set A : Finset (Finset ι) := {S | fourierCoeff g S ≠ 0}
  have hA : A.Nonempty := by
    by_contra hA
    refine hg (funext fun x => ?_)
    rw [← sum_fourierCoeff_mul_chi g x, Pi.zero_apply]
    refine sum_eq_zero fun S _ => ?_
    have hS : fourierCoeff g S = 0 := by
      by_contra hS
      exact hA ⟨S, mem_filter.2 ⟨mem_univ S, hS⟩⟩
    rw [hS, zero_mul]
  obtain ⟨S, hSA, hSmax⟩ := exists_max_image A Finset.card hA
  have hS : fourierCoeff g S ≠ 0 := (mem_filter.1 hSA).2
  have hT (T : Finset ι) (hST : S ⊂ T) : fourierCoeff g T = 0 := by
    by_contra hTne
    exact (card_lt_card hST).not_ge (hSmax T (mem_filter.2 ⟨mem_univ T, hTne⟩))
  have hSk : #S ≤ k := le_of_not_gt fun hk => hS (hdeg S hk)
  calc (1 : ℝ) ≤ 2 ^ #S * (dens {x | g x ≠ 0} : ℝ) :=
        one_le_two_pow_card_mul_dens_ne_zero S g hS hT
    _ ≤ 2 ^ k * (dens {x | g x ≠ 0} : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hSk) (NNRat.cast_nonneg _)

/-- **Schwartz–Zippel on the cube**: a nonzero real function of degree at most `k` is nonzero on at
least a `2 ^ (-k)` fraction of the cube. -/
theorem one_le_two_pow_mul_dens_ne_zero (g : (ι → Bool) → ℝ) {k : ℕ}
    (hdeg : g ∈ lowDegree ℝ ι k) (hg : g ≠ 0) :
    1 ≤ 2 ^ k * (dens {x | g x ≠ 0} : ℝ) :=
  one_le_two_pow_mul_dens_ne_zero_of_fourierCoeff_eq_zero g
    (mem_lowDegree_iff_fourierCoeff_eq_zero.1 hdeg) hg

/-- **Schwartz–Zippel on the cube**, counting and Fourier-coefficient form: a nonzero real function
whose Fourier coefficients vanish above degree `k` on `n` coordinates is nonzero on at least
`2 ^ (n - k)` points of the cube. -/
theorem two_pow_card_le_two_pow_mul_card_ne_zero_of_fourierCoeff_eq_zero (g : (ι → Bool) → ℝ)
    {k : ℕ} (hdeg : ∀ S : Finset ι, k < #S → fourierCoeff g S = 0) (hg : g ≠ 0) :
    2 ^ Fintype.card ι ≤ 2 ^ k * #{x | g x ≠ 0} := by
  have h := one_le_two_pow_mul_dens_ne_zero_of_fourierCoeff_eq_zero g hdeg hg
  rw [nnratCast_dens, Fintype.card_fun, Fintype.card_bool, mul_div_assoc',
    le_div_iff₀ (by positivity), one_mul] at h
  exact_mod_cast h

/-- **Schwartz–Zippel on the cube**, counting form: a nonzero real function of degree at most `k`
on `n` coordinates is nonzero on at least `2 ^ (n - k)` points of the cube. -/
theorem two_pow_card_le_two_pow_mul_card_ne_zero (g : (ι → Bool) → ℝ) {k : ℕ}
    (hdeg : g ∈ lowDegree ℝ ι k) (hg : g ≠ 0) :
    2 ^ Fintype.card ι ≤ 2 ^ k * #{x | g x ≠ 0} :=
  two_pow_card_le_two_pow_mul_card_ne_zero_of_fourierCoeff_eq_zero g
    (mem_lowDegree_iff_fourierCoeff_eq_zero.1 hdeg) hg

/-! ### Equality in the Poincaré inequality and degree-one Boolean functions -/

/-- Two bits agree if and only if their real signs agree. -/
private theorem signVal_eq_iff (a b : Bool) : signVal a = signVal b ↔ a = b := by
  cases a <;> cases b <;> norm_num

/-- **Equality in the Poincaré inequality**, Fourier-coefficient form: the total influence equals
the variance if and only if the Fourier coefficients vanish above degree one
[O'Donnell, Proposition 2.40][ODonnell2014]. -/
theorem totalInfluence_eq_expect_sub_expect_sq_iff_fourierCoeff_eq_zero (g : (ι → Bool) → ℝ) :
    totalInfluence g = 𝔼 x, (g x - 𝔼 y, g y) ^ 2 ↔
      ∀ S : Finset ι, 1 < #S → fourierCoeff g S = 0 := by
  have hle (S : Finset ι) (_ : S ∈ (univ : Finset (Finset ι))) :
      (if S ≠ ∅ then fourierCoeff g S ^ 2 else 0) ≤ (#S : ℝ) * fourierCoeff g S ^ 2 := by
    split_ifs with hS
    · exact le_mul_of_one_le_left (sq_nonneg _)
        (Nat.one_le_cast.2 (card_pos.2 (nonempty_iff_ne_empty.2 hS)))
    · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rw [eq_comm, expect_sub_expect_sq_eq_sum_fourierCoeff_sq,
    totalInfluence_eq_sum_card_mul_fourierCoeff_sq, sum_filter, sum_eq_sum_iff_of_le hle]
  refine ⟨fun h S hS => ?_, fun hdeg S _ => ?_⟩
  · have hne : S ≠ ∅ := nonempty_iff_ne_empty.1 (card_pos.1 (by omega))
    have h1 : (1 : ℝ) < #S := Nat.one_lt_cast.2 hS
    have hS' := h S (mem_univ S)
    rw [ite_eq_left hne] at hS'
    exact sq_eq_zero_iff.1 (by nlinarith)
  · split_ifs with hS
    · rcases le_or_gt #S 1 with hle1 | hgt1
      · have hcard : #S = 1 := le_antisymm hle1 (card_pos.2 (nonempty_iff_ne_empty.2 hS))
        simp [hcard]
      · rw [hdeg S hgt1]
        simp
    · push Not at hS
      simp [hS]

/-- **Equality in the Poincaré inequality**, inequality and Fourier-coefficient form: the total
influence is at most the variance if and only if the Fourier coefficients vanish above degree one
[O'Donnell, Proposition 2.40][ODonnell2014]. -/
theorem totalInfluence_le_expect_sub_expect_sq_iff_fourierCoeff_eq_zero (g : (ι → Bool) → ℝ) :
    totalInfluence g ≤ 𝔼 x, (g x - 𝔼 y, g y) ^ 2 ↔
      ∀ S : Finset ι, 1 < #S → fourierCoeff g S = 0 := by
  rw [← totalInfluence_eq_expect_sub_expect_sq_iff_fourierCoeff_eq_zero, le_antisymm_iff,
    and_iff_left (expect_sub_expect_sq_le_totalInfluence g)]

/-- **Equality in the Poincaré inequality**: a real function has total influence equal to its
variance if and only if it has degree at most one [O'Donnell, Proposition 2.40][ODonnell2014]. -/
theorem totalInfluence_eq_expect_sub_expect_sq_iff_mem_lowDegree (g : (ι → Bool) → ℝ) :
    totalInfluence g = 𝔼 x, (g x - 𝔼 y, g y) ^ 2 ↔ g ∈ lowDegree ℝ ι 1 := by
  rw [totalInfluence_eq_expect_sub_expect_sq_iff_fourierCoeff_eq_zero,
    mem_lowDegree_iff_fourierCoeff_eq_zero]

/-- **Equality in the Poincaré inequality**, inequality form: a real function has total influence
at most its variance if and only if it has degree at most one
[O'Donnell, Proposition 2.40][ODonnell2014]. -/
theorem totalInfluence_le_expect_sub_expect_sq_iff_mem_lowDegree (g : (ι → Bool) → ℝ) :
    totalInfluence g ≤ 𝔼 x, (g x - 𝔼 y, g y) ^ 2 ↔ g ∈ lowDegree ℝ ι 1 := by
  rw [totalInfluence_le_expect_sub_expect_sq_iff_fourierCoeff_eq_zero,
    mem_lowDegree_iff_fourierCoeff_eq_zero]

/-- For a function whose Fourier coefficients vanish above degree one, the derivative in `i` is the
constant `fourierCoeff g {i}`. -/
theorem derivative_eq_fourierCoeff_singleton_of_fourierCoeff_eq_zero (g : (ι → Bool) → ℝ)
    (hdeg : ∀ S : Finset ι, 1 < #S → fourierCoeff g S = 0) (i : ι) (x : ι → Bool) :
    derivative i g x = fourierCoeff g {i} := by
  rw [derivative_eq_sum, sum_eq_single {i}]
  · simp
  · intro S hS hSi
    have hlt : 1 < #S := by
      rw [← card_singleton i]
      exact card_lt_card (Finset.ssubset_iff_subset_ne.2
        ⟨singleton_subset_iff.2 (mem_filter.1 hS).2, hSi.symm⟩)
    rw [hdeg S hlt, zero_mul]
  · simp

/-- If a Boolean function read as signs has squared Fourier coefficient `1` on `S`, then all its
other Fourier coefficients vanish. -/
theorem fourierCoeff_signVal_eq_zero_of_sq_eq_one (f : (ι → Bool) → Bool) {S T : Finset ι}
    (hS : fourierCoeff (fun x => signVal (f x)) S ^ 2 = 1) (hTS : T ≠ S) :
    fourierCoeff (fun x => signVal (f x)) T = 0 := by
  set c := fourierCoeff fun x => signVal (f x)
  have hsum : ∑ U ∈ univ.erase S, c U ^ 2 = 0 := by
    have h := sum_fourierCoeff_sq_signVal f
    rw [← add_sum_erase _ (fun U => c U ^ 2) (mem_univ S), hS] at h
    linarith
  exact sq_eq_zero_iff.1 ((sum_eq_zero_iff_of_nonneg fun U _ => sq_nonneg (c U)).1 hsum T
    (mem_erase.2 ⟨hTS, mem_univ T⟩))

/-- If a Boolean function read as signs has squared Fourier coefficient `1` on `{i}`, then it is the
literal `x ↦ f 0 ^^ x i`. -/
theorem eq_xor_of_fourierCoeff_signVal_singleton_sq_eq_one (f : (ι → Bool) → Bool) {i : ι}
    (hi : fourierCoeff (fun x => signVal (f x)) {i} ^ 2 = 1) (x : ι → Bool) :
    f x = (f 0 ^^ x i) := by
  have hval (y : ι → Bool) :
      signVal (f y) = fourierCoeff (fun x => signVal (f x)) {i} * signVal (y i) := by
    rw [← sum_fourierCoeff_mul_chi (fun x => signVal (f x)) y,
      sum_eq_single {i} (fun T _ hT => by
        rw [fourierCoeff_signVal_eq_zero_of_sq_eq_one f hi hT, zero_mul]) (by simp),
      chi_singleton]
  have h0 := hval 0
  simp only [Pi.zero_apply, Bool.zero_eq_false, signVal_false, mul_one] at h0
  have hx := hval x
  rw [← h0, ← signVal_xor, signVal_eq_iff] at hx
  exact hx

/-- **Boolean functions of degree at most one are constants or literals**, Fourier-coefficient
form: the Fourier coefficients of `signVal ∘ f` vanish above degree one if and only if `f` is
constant or a literal `x ↦ b ^^ x i` [O'Donnell, Exercise 1.19][ODonnell2014]. -/
theorem fourierCoeff_signVal_eq_zero_iff_eq_const_or_exists_eq_xor (f : (ι → Bool) → Bool) :
    (∀ S : Finset ι, 1 < #S → fourierCoeff (fun x => signVal (f x)) S = 0) ↔
      (∃ b, f = Function.const _ b) ∨ ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  refine ⟨fun hdeg => ?_, ?_⟩
  · by_cases hall : ∀ i : ι, fourierCoeff F {i} = 0
    · left
      refine ⟨f 0, funext fun x => ?_⟩
      have hval (y : ι → Bool) : F y = fourierCoeff F ∅ := by
        rw [← sum_fourierCoeff_mul_chi F y, sum_eq_single ∅]
        · simp
        · intro S _ hS
          rcases le_or_gt #S 1 with hle1 | hgt1
          · obtain ⟨i, rfl⟩ := card_eq_one.1 (le_antisymm hle1
              (card_pos.2 (nonempty_iff_ne_empty.2 hS)))
            rw [hall i, zero_mul]
          · rw [hdeg S hgt1, zero_mul]
        · simp
      exact (signVal_eq_iff _ _).1 ((hval x).trans (hval 0).symm)
    · right
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      refine ⟨i, f 0, funext (eq_xor_of_fourierCoeff_signVal_singleton_sq_eq_one f ?_)⟩
      have hsq : fourierCoeff F {i} ^ 2 = |fourierCoeff F {i}| := by
        rw [← derivative_eq_fourierCoeff_singleton_of_fourierCoeff_eq_zero F hdeg i 0,
          sq_derivative_signVal]
      have habs : |fourierCoeff F {i}| = 1 :=
        mul_left_cancel₀ (abs_ne_zero.2 hi) (by rw [← sq, sq_abs, hsq, mul_one])
      rw [hsq, habs]
  · rintro (⟨b, rfl⟩ | ⟨i, b, rfl⟩) S hS
    · have hne : S ≠ ∅ := nonempty_iff_ne_empty.1 (card_pos.1 (by omega))
      exact (fourierCoeff_const (signVal b) S).trans (ite_eq_right hne)
    · have hF : F = fun x => signVal b * chi ℝ {i} x := by
        funext x
        simp [F, chi_singleton]
      have hne : {i} ≠ S := fun h => by
        have := congrArg card h
        rw [card_singleton] at this
        omega
      rw [hF, fourierCoeff_const_mul, fourierCoeff_chi, ite_eq_right hne, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- **Boolean functions of degree at most one are constants or literals**: `signVal ∘ f` has degree
at most one if and only if `f` is constant or a literal `x ↦ b ^^ x i`
[O'Donnell, Exercise 1.19][ODonnell2014]. -/
theorem mem_lowDegree_one_signVal_iff [Finite ι] (f : (ι → Bool) → Bool) :
    (fun x => signVal (f x)) ∈ lowDegree ℝ ι 1 ↔
      (∃ b, f = Function.const _ b) ∨ ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  classical
  cases nonempty_fintype ι
  rw [mem_lowDegree_iff_fourierCoeff_eq_zero,
    fourierCoeff_signVal_eq_zero_iff_eq_const_or_exists_eq_xor]

/-- **Equality in the Poincaré inequality for Boolean functions**: a Boolean function read as signs
has total influence equal to its variance if and only if it is constant or a literal
`x ↦ b ^^ x i` [O'Donnell, Proposition 2.40][ODonnell2014]. -/
theorem totalInfluence_signVal_eq_expect_sub_expect_sq_iff (f : (ι → Bool) → Bool) :
    totalInfluence (fun x => signVal (f x)) =
      𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 ↔
      (∃ b, f = Function.const _ b) ∨ ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  rw [totalInfluence_eq_expect_sub_expect_sq_iff_fourierCoeff_eq_zero,
    fourierCoeff_signVal_eq_zero_iff_eq_const_or_exists_eq_xor]

/-- **Equality in the Poincaré inequality for Boolean functions**, inequality form: a Boolean
function read as signs has total influence at most its variance if and only if it is constant or a
literal `x ↦ b ^^ x i` [O'Donnell, Proposition 2.40][ODonnell2014]. -/
theorem totalInfluence_signVal_le_expect_sub_expect_sq_iff (f : (ι → Bool) → Bool) :
    totalInfluence (fun x => signVal (f x)) ≤
      𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 ↔
      (∃ b, f = Function.const _ b) ∨ ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  rw [totalInfluence_le_expect_sub_expect_sq_iff_fourierCoeff_eq_zero,
    fourierCoeff_signVal_eq_zero_iff_eq_const_or_exists_eq_xor]

/-- **Balanced Boolean functions have variance one**. -/
theorem expect_sub_expect_sq_signVal_of_expect_eq_zero {f : (ι → Bool) → Bool}
    (hbal : 𝔼 x, signVal (f x) = 0) :
    𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 = 1 := by
  simp only [hbal, sub_zero, sq, signVal_mul_self, expect_const univ_nonempty]

/-- **Balanced Boolean functions of average sensitivity one are literals**: for a balanced Boolean
function (`𝔼 x, signVal (f x) = 0`), the total influence (average sensitivity) equals one if and
only if the function is a literal `x ↦ b ^^ x i`
[Arora–Barak, Chapter 19, Exercise 5(b)][AroraBarak07]
[O'Donnell, Proposition 2.40][ODonnell2014]. -/
theorem totalInfluence_signVal_eq_one_iff_of_expect_eq_zero {f : (ι → Bool) → Bool}
    (hbal : 𝔼 x, signVal (f x) = 0) :
    totalInfluence (fun x => signVal (f x)) = 1 ↔ ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  rw [← expect_sub_expect_sq_signVal_of_expect_eq_zero hbal,
    totalInfluence_signVal_eq_expect_sub_expect_sq_iff]
  refine or_iff_right ?_
  rintro ⟨b, rfl⟩
  have h1 : (𝔼 x : ι → Bool, signVal (Function.const _ b x)) = signVal b :=
    expect_const univ_nonempty (signVal b)
  have habs := abs_signVal b
  rw [← h1, hbal] at habs
  norm_num at habs

/-- **Balanced Boolean functions of average sensitivity at most one are literals**: for a balanced
Boolean function (`𝔼 x, signVal (f x) = 0`), the total influence (average sensitivity) is at most
one if and only if the function is a literal `x ↦ b ^^ x i`
[Arora–Barak, Chapter 19, Exercise 5(b)][AroraBarak07]
[O'Donnell, Proposition 2.40][ODonnell2014]. -/
theorem totalInfluence_signVal_le_one_iff_of_expect_eq_zero {f : (ι → Bool) → Bool}
    (hbal : 𝔼 x, signVal (f x) = 0) :
    totalInfluence (fun x => signVal (f x)) ≤ 1 ↔ ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  rw [← expect_sub_expect_sq_signVal_of_expect_eq_zero hbal,
    totalInfluence_signVal_le_expect_sub_expect_sq_iff,
    ← totalInfluence_signVal_eq_expect_sub_expect_sq_iff,
    expect_sub_expect_sq_signVal_of_expect_eq_zero hbal,
    totalInfluence_signVal_eq_one_iff_of_expect_eq_zero hbal]

end Cslib.BitString
