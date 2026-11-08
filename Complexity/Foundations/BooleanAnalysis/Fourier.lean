/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Fourier analysis on the Boolean cube

The *character* of a set `S` of coordinates is `χ_S x = ∏_{i ∈ S} (-1) ^ (x i)`
(`BitString.chi`), the sign of the parity of the bits of `x : ι → Bool` in `S`
(`BitString.chi_eq_neg_one_pow_parityOn`), with values in any commutative ring `R`; Fourier
analysis takes `R = ℝ`, where the sign of a bit is `BitString.signVal`. Bit strings add
coordinatewise modulo two, `(x + y) i = (x i ^^ y i)`, through Mathlib's Boolean ring structure on
`Bool`, and the characters turn sums into products (`BitString.chi_add`): they are additive
characters of the cube (`BitString.chiChar`), whose sums are Mathlib's `AddChar.sum_eq_ite`. The
characters are orthonormal for the uniform expectation (`BitString.expect_chi_mul_chi`), and every
real function on the cube is the sum of its *Fourier expansion* `f = ∑_S f̂(S) χ_S`, with the
*Fourier coefficients* `f̂(S) = 𝔼_x f x χ_S x` (`BitString.fourierCoeff`,
`BitString.sum_fourierCoeff_mul_chi`), which are unique
(`BitString.fourierCoeff_sum_mul_chi`), so the Fourier transform is a linear equivalence
(`BitString.fourierTransform`). The expectation of a product is the sum of products of
coefficients (**Plancherel**, `BitString.expect_mul_eq_sum_fourierCoeff_mul`), so the squared
coefficients of a function with values `±1` sum to one (`BitString.sum_fourierCoeff_sq_signVal`).
For Boolean functions read as signs, correlation is one minus twice the relative Hamming distance
(`BitString.expect_signVal_mul_signVal`), so the coefficient on `S` measures the distance to the
parity on `S` (`BitString.fourierCoeff_signVal`) [O'Donnell, Chapter 1][ODonnell2014].

The coefficients are named `BitString.fourierCoeff`; Mathlib's root `fourierCoeff` is the Fourier
coefficient on the circle, so the name is meant to be used qualified.

## Main definitions

* `Cslib.BitString.chi`: the character of a set of coordinates, with values in a commutative ring,
  and `Cslib.BitString.chiChar` the same as an additive character.
* `Cslib.BitString.fourierCoeff`: the Fourier coefficient of a real function on the cube, and
  `Cslib.BitString.fourierCoeffₗ` the same as a linear map.
* `Cslib.BitString.fourierTransform`: the Fourier transform, as a linear equivalence.

## Main results

* `Cslib.BitString.expect_chi_mul_chi`, `Cslib.BitString.fourierCoeff_chi`: the characters are
  orthonormal.
* `Cslib.BitString.chi_add`, `Cslib.BitString.chi_mul_chi`: the characters are multiplicative,
  in the input and in the set.
* `Cslib.BitString.sum_fourierCoeff_mul_chi`: the Fourier expansion.
* `Cslib.BitString.fourierCoeff_sum_mul_chi`, `Cslib.BitString.fourierCoeff_injective`:
  uniqueness of the Fourier coefficients.
* `Cslib.BitString.expect_mul_eq_sum_fourierCoeff_mul`: Plancherel's identity.
* `Cslib.BitString.sum_fourierCoeff_sq_signVal`: Parseval's identity for functions with values
  `±1`; so their coefficients have square and absolute value at most one
  (`Cslib.BitString.fourierCoeff_sq_signVal_le_one`,
  `Cslib.BitString.abs_fourierCoeff_signVal_le_one`) and their spectral norm is at least one
  (`Cslib.BitString.one_le_sum_abs_fourierCoeff_signVal`).
* `Cslib.BitString.expect_signVal_mul_signVal`, `Cslib.BitString.fourierCoeff_signVal`: the
  correlation of two Boolean functions is one minus twice their relative Hamming distance.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι R : Type*}

section CommRing

variable [CommRing R]

variable (R) in
/-- The character of a set `S` of coordinates, with values in a commutative ring `R`: the product
of the signs `(-1) ^ xᵢ` over `S`, the sign of the parity of the bits in `S`
(`chi_eq_neg_one_pow_parityOn`). The Fourier analysis of real functions uses `chi ℝ`. -/
def chi (S : Finset ι) (x : ι → Bool) : R :=
  ∏ i ∈ S, (-1) ^ (x i).toNat

/-- The character of the empty set is the constant `1`. -/
@[simp] theorem chi_empty (x : ι → Bool) : chi R ∅ x = 1 :=
  prod_empty

variable (R) in
/-- The character of `S`, as an additive character of the cube: it sends sums of bit strings,
their coordinatewise exclusive or, to products. -/
def chiChar (S : Finset ι) : AddChar (ι → Bool) R where
  toFun := chi R S
  map_zero_eq_one' := prod_eq_one fun _ _ => by simp [Bool.zero_eq_false]
  map_add_eq_mul' x y := by
    simp only [chi, Pi.add_apply, Bool.add_eq_xor, neg_one_pow_toNat_xor, prod_mul_distrib]

/-- The additive character `chiChar R S` is the character `chi R S` as a function. -/
@[simp] theorem coe_chiChar (S : Finset ι) : ⇑(chiChar R S) = chi R S :=
  rfl

/-- **Characters are multiplicative**: the character of the sum of two bit strings, their
coordinatewise exclusive or, is the product of their characters. -/
theorem chi_add (S : Finset ι) (x y : ι → Bool) : chi R S (x + y) = chi R S x * chi R S y :=
  (chiChar R S).map_add_eq_mul x y

/-- Every character is `1` at the all-`false` bit string. -/
@[simp] theorem chi_zero (S : Finset ι) : chi R S 0 = 1 :=
  (chiChar R S).map_zero_eq_one

/-- The character of `S` is the sign of the parity of the bits in `S`. -/
theorem chi_eq_neg_one_pow_parityOn (S : Finset ι) (x : ι → Bool) :
    chi R S x = (-1) ^ (parityOn S x).toNat := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [chi, prod_insert hi, ← chi, ih, parityOn_insert hi, neg_one_pow_toNat_xor]

/-- A character squares to one. -/
theorem chi_mul_self (S : Finset ι) (x : ι → Bool) : chi R S x * chi R S x = 1 := by
  rw [chi, ← prod_mul_distrib]
  exact prod_eq_one fun i _ => by cases x i <;> simp

section DecidableEq

variable [DecidableEq ι]

/-- **Characters multiply** by the symmetric difference of their sets. -/
theorem chi_mul_chi (S T : Finset ι) (x : ι → Bool) :
    chi R S x * chi R T x = chi R (symmDiff S T) x := by
  have h {S U : Finset ι} (h : S ⊆ U) :
      chi R S x = ∏ i ∈ U, if i ∈ S then (-1) ^ (x i).toNat else 1 := by
    rw [prod_ite_mem, inter_eq_right.2 h, chi]
  rw [h subset_union_left, h subset_union_right, h (symmDiff_le_sup (α := Finset ι)),
    ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, mem_symmDiff, ← pow_add]

/-- The character of a disjoint union is the product of the characters. -/
theorem chi_union {S T : Finset ι} (h : Disjoint S T) (x : ι → Bool) :
    chi R (S ∪ T) x = chi R S x * chi R T x :=
  prod_union h

variable {i : ι} {S : Finset ι}

/-- Changing a bit outside `S` leaves the character of `S` unchanged. -/
theorem chi_update_of_notMem (hi : i ∉ S) (x : ι → Bool) (b : Bool) :
    chi R S (Function.update x i b) = chi R S x :=
  prod_congr rfl fun _ hj => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]

/-- Setting a bit in `S` to `b` splits off the sign `(-1) ^ b` from the character of `S`. -/
theorem chi_update_of_mem (hi : i ∈ S) (x : ι → Bool) (b : Bool) :
    chi R S (Function.update x i b) = (-1) ^ b.toNat * chi R (S.erase i) x := by
  rw [chi, ← mul_prod_erase S _ hi, Function.update_self, ← chi,
    chi_update_of_notMem (notMem_erase i S)]

end DecidableEq

end CommRing

/-- The real character of `S` is the product of the real signs of the bits in `S`. -/
theorem chi_eq_prod_signVal (S : Finset ι) (x : ι → Bool) :
    chi ℝ S x = ∏ i ∈ S, signVal (x i) :=
  prod_congr rfl fun i _ => (signVal_eq_neg_one_pow (x i)).symm

/-- The real character of a single coordinate is the sign of that bit. -/
theorem chi_singleton (i : ι) (x : ι → Bool) : chi ℝ {i} x = signVal (x i) := by
  rw [chi_eq_prod_signVal, prod_singleton]

/-- The real character of `S` is the real sign of the parity of the bits in `S`. -/
theorem chi_eq_signVal_parityOn (S : Finset ι) (x : ι → Bool) :
    chi ℝ S x = signVal (parityOn S x) := by
  rw [chi_eq_neg_one_pow_parityOn, signVal_eq_neg_one_pow]

/-- A real character has absolute value one. -/
@[simp] theorem abs_chi (T : Finset ι) (x : ι → Bool) : |chi ℝ T x| = 1 := by
  rw [chi_eq_signVal_parityOn, abs_signVal]

/-- The character of `S` is the trivial additive character exactly when `S` is empty. -/
@[simp] theorem chiChar_eq_zero_iff {S : Finset ι} : chiChar ℝ S = 0 ↔ S = ∅ := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hS
    obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.2 hS
    have h' := DFunLike.congr_fun h (Function.update (0 : ι → Bool) i true)
    rw [coe_chiChar, chi_update_of_mem hi, chi_zero, AddChar.zero_apply] at h'
    norm_num at h'
  · rintro rfl
    exact AddChar.ext _ _ chi_empty

section Fintype

variable [Fintype ι]

/-- The characters at two points, summed over all sets, detect equality of the points. -/
theorem sum_chi_mul_chi (x y : ι → Bool) :
    ∑ S, chi ℝ S x * chi ℝ S y = if x = y then 2 ^ Fintype.card ι else 0 := by
  classical
  have h := prod_add (fun i => signVal (x i) * signVal (y i)) (fun _ => (1 : ℝ)) univ
  simp only [prod_const_one, mul_one, powerset_univ] at h
  simp only [chi_eq_prod_signVal, ← prod_mul_distrib]
  rw [← h]
  simp only [signVal_mul_signVal]
  split_ifs with hxy
  · subst hxy
    simp [one_add_one_eq_two]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    exact prod_eq_zero (mem_univ i) (by simp [hi])

variable [DecidableEq ι]

/-- The character as a product over all coordinates. -/
theorem chi_eq_prod_univ [CommRing R] (S : Finset ι) (x : ι → Bool) :
    chi R S x = ∏ i, if i ∈ S then (-1) ^ (x i).toNat else 1 := by
  rw [prod_ite_mem, univ_inter, chi]

/-- The characters of nonempty sets sum to zero. -/
theorem sum_chi (S : Finset ι) :
    ∑ x, chi ℝ S x = if S = ∅ then 2 ^ Fintype.card ι else 0 := by
  rw [← coe_chiChar, AddChar.sum_eq_ite]
  simp

/-- The characters of nonempty sets have expectation zero. -/
theorem expect_chi (S : Finset ι) : 𝔼 x, chi ℝ S x = if S = ∅ then 1 else 0 := by
  rw [← coe_chiChar, AddChar.expect_eq_ite]
  simp

/-- **The characters are orthonormal.** -/
theorem expect_chi_mul_chi (S T : Finset ι) :
    𝔼 x, chi ℝ S x * chi ℝ T x = if S = T then 1 else 0 := by
  simp only [chi_mul_chi, expect_chi, ← bot_eq_empty, symmDiff_eq_bot]

/-- The Fourier coefficient of `f` on `S`: the correlation of `f` with the character of `S`. -/
noncomputable def fourierCoeff (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  𝔼 x, f x * chi ℝ S x

/-- The Fourier coefficient as a normalised sum. -/
theorem fourierCoeff_eq_sum (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff f S = (∑ x, f x * chi ℝ S x) / 2 ^ Fintype.card ι := by
  simp [fourierCoeff, expect_eq_sum_div_card]

/-- The Fourier coefficients are additive. -/
theorem fourierCoeff_add (f g : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => f x + g x) S = fourierCoeff f S + fourierCoeff g S := by
  simp only [fourierCoeff, add_mul, expect_add_distrib]

/-- The Fourier coefficients commute with subtraction. -/
theorem fourierCoeff_sub (f g : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => f x - g x) S = fourierCoeff f S - fourierCoeff g S := by
  simp only [fourierCoeff, sub_mul, expect_sub_distrib]

/-- The Fourier coefficients commute with scaling. -/
theorem fourierCoeff_const_mul (c : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => c * f x) S = c * fourierCoeff f S := by
  simp only [fourierCoeff, mul_assoc, mul_expect]

/-- Multiplying by a character shifts the coefficients by the symmetric difference. -/
theorem fourierCoeff_chi_mul (T : Finset ι) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => chi ℝ T x * f x) S = fourierCoeff f (symmDiff T S) := by
  simp only [fourierCoeff, ← chi_mul_chi, mul_comm (chi ℝ T _), mul_assoc]

/-- A constant has all its weight on the empty set. -/
theorem fourierCoeff_const (c : ℝ) (S : Finset ι) :
    fourierCoeff (fun _ => c) S = if S = ∅ then c else 0 := by
  simp only [fourierCoeff, ← mul_expect, expect_chi, mul_ite, mul_one, mul_zero]

/-- The Fourier coefficients of a character are `1` at its own set and `0` elsewhere. -/
@[simp]
theorem fourierCoeff_chi (S T : Finset ι) :
    fourierCoeff (chi ℝ S) T = if S = T then 1 else 0 :=
  expect_chi_mul_chi S T

/-- A parity, read as `±1`, is the character of its set, so all its weight is on that set. -/
theorem fourierCoeff_signVal_parityOn (S U : Finset ι) :
    fourierCoeff (fun x => signVal (parityOn S x)) U = if U = S then 1 else 0 := by
  have h : (fun x => signVal (parityOn S x)) = chi ℝ S :=
    funext fun x => (chi_eq_signVal_parityOn S x).symm
  rw [h, fourierCoeff_chi]
  exact if_congr eq_comm rfl rfl

/-- The coefficient on the empty set is the expectation. -/
@[simp] theorem fourierCoeff_empty (f : (ι → Bool) → ℝ) : fourierCoeff f ∅ = 𝔼 x, f x := by
  simp [fourierCoeff]

/-- **The Fourier expansion**: every function is the sum of its characters weighted by its
Fourier coefficients. -/
theorem sum_fourierCoeff_mul_chi (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    ∑ S, fourierCoeff f S * chi ℝ S x = f x := by
  simp only [fourierCoeff_eq_sum, div_mul_eq_mul_div, sum_mul, ← sum_div]
  rw [sum_comm]
  simp only [mul_assoc, ← mul_sum, sum_chi_mul_chi, mul_ite, mul_zero, sum_ite_eq', mem_univ,
    ite_true]
  field_simp

/-- **The Fourier coefficients are unique**: a combination of characters has its weights as
coefficients. -/
theorem fourierCoeff_sum_mul_chi (c : Finset ι → ℝ) (T : Finset ι) :
    fourierCoeff (fun x => ∑ S, c S * chi ℝ S x) T = c T := by
  simp only [fourierCoeff, sum_mul, mul_assoc]
  rw [expect_sum_comm]
  simp only [← mul_expect, expect_chi_mul_chi, mul_ite, mul_one, mul_zero, sum_ite_eq',
    mem_univ, ite_true]

/-- A function is determined by its Fourier coefficients. -/
theorem fourierCoeff_injective : Function.Injective (fourierCoeff (ι := ι)) := fun f g h => by
  funext x
  rw [← sum_fourierCoeff_mul_chi f, ← sum_fourierCoeff_mul_chi g, h]

/-- The Fourier coefficient on `S`, as a linear map. -/
noncomputable def fourierCoeffₗ (S : Finset ι) : ((ι → Bool) → ℝ) →ₗ[ℝ] ℝ where
  toFun f := fourierCoeff f S
  map_add' f g := fourierCoeff_add f g S
  map_smul' c f := fourierCoeff_const_mul c f S

/-- The linear map `fourierCoeffₗ S` sends `f` to its Fourier coefficient on `S`. -/
@[simp] theorem fourierCoeffₗ_apply (S : Finset ι) (f : (ι → Bool) → ℝ) :
    fourierCoeffₗ S f = fourierCoeff f S :=
  rfl

/-- The Fourier transform, sending a real function on the cube to its Fourier coefficients, as a
linear equivalence: its inverse is the Fourier expansion. -/
noncomputable def fourierTransform : ((ι → Bool) → ℝ) ≃ₗ[ℝ] (Finset ι → ℝ) where
  toFun := fourierCoeff
  map_add' f g := funext (fourierCoeff_add f g)
  map_smul' c f := funext (fourierCoeff_const_mul c f)
  invFun c x := ∑ S, c S * chi ℝ S x
  left_inv f := funext (sum_fourierCoeff_mul_chi f)
  right_inv c := funext (fourierCoeff_sum_mul_chi c)

/-- The Fourier transform sends a function to its Fourier coefficients. -/
@[simp] theorem fourierTransform_apply (f : (ι → Bool) → ℝ) :
    fourierTransform f = fourierCoeff f :=
  rfl

/-- The inverse Fourier transform sends weights `c` to the combination `∑ S, c S * χ_S`. -/
@[simp] theorem fourierTransform_symm_apply (c : Finset ι → ℝ) (x : ι → Bool) :
    fourierTransform.symm c x = ∑ S, c S * chi ℝ S x :=
  rfl

/-- **Plancherel's identity**: the expectation of a product is the sum of the products of the
Fourier coefficients. -/
theorem expect_mul_eq_sum_fourierCoeff_mul (f g : (ι → Bool) → ℝ) :
    𝔼 x, f x * g x = ∑ S, fourierCoeff f S * fourierCoeff g S := by
  have h (x : ι → Bool) : f x * g x = ∑ S, fourierCoeff g S * (f x * chi ℝ S x) := by
    conv_lhs => rw [← sum_fourierCoeff_mul_chi g x]
    rw [mul_sum]
    exact sum_congr rfl fun S _ => mul_left_comm _ _ _
  simp only [h]
  rw [expect_sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [← mul_expect, mul_comm]
  rfl

/-- **Parseval's identity.** -/
theorem expect_sq_eq_sum_fourierCoeff_sq (f : (ι → Bool) → ℝ) :
    𝔼 x, f x ^ 2 = ∑ S, fourierCoeff f S ^ 2 := by
  simpa only [sq] using expect_mul_eq_sum_fourierCoeff_mul f f

/-- **Parseval's identity for functions with values `±1`**: the squared Fourier coefficients sum
to one. -/
theorem sum_fourierCoeff_sq_signVal (f : (ι → Bool) → Bool) :
    ∑ S, fourierCoeff (fun x => signVal (f x)) S ^ 2 = 1 := by
  rw [← expect_sq_eq_sum_fourierCoeff_sq]
  simp only [sq, signVal_mul_self]
  exact expect_const univ_nonempty 1

/-- A Fourier coefficient of a Boolean function, read as signs, has square at most one. -/
theorem fourierCoeff_sq_signVal_le_one (f : (ι → Bool) → Bool) (S : Finset ι) :
    fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ 1 := by
  rw [← sum_fourierCoeff_sq_signVal f]
  exact single_le_sum (f := fun S => fourierCoeff (fun x => signVal (f x)) S ^ 2)
    (fun _ _ => sq_nonneg _) (mem_univ S)

/-- A Fourier coefficient of a Boolean function, read as signs, has absolute value at most one. -/
theorem abs_fourierCoeff_signVal_le_one (f : (ι → Bool) → Bool) (S : Finset ι) :
    |fourierCoeff (fun x => signVal (f x)) S| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  exact fourierCoeff_sq_signVal_le_one f S

/-- A Boolean function, read as signs, has spectral norm `∑_S |f̂(S)|` at least one. -/
theorem one_le_sum_abs_fourierCoeff_signVal (f : (ι → Bool) → Bool) :
    1 ≤ ∑ S, |fourierCoeff (fun x => signVal (f x)) S| := by
  rw [← sum_fourierCoeff_sq_signVal f]
  refine sum_le_sum fun S _ => ?_
  rw [← sq_abs, sq]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_fourierCoeff_signVal_le_one f S)

/-! ### Distance and correlation -/

/-- **Correlation is one minus twice the distance**: the correlation of two Boolean functions,
read as signs, is one minus twice the fraction of the inputs on which they differ
[O'Donnell, Section 1.4][ODonnell2014]. -/
theorem expect_signVal_mul_signVal (f g : (ι → Bool) → Bool) :
    𝔼 x, signVal (f x) * signVal (g x) = 1 - 2 * hammingDist f g / 2 ^ Fintype.card ι := by
  have h (x : ι → Bool) :
      signVal (f x) * signVal (g x) = 1 - 2 * if f x ≠ g x then 1 else 0 := by
    rw [signVal_mul_signVal]
    by_cases hx : f x = g x <;> norm_num [hx]
  rw [hammingDist]
  simp only [h, expect_eq_sum_div_card, sum_sub_distrib, ← mul_sum, sum_boole, sum_const,
    card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [sub_div, div_self (pow_ne_zero _ two_ne_zero)]

/-- The Fourier coefficient on `S` of a Boolean function read as signs is one minus twice the
relative Hamming distance from the function to the parity on `S`. -/
theorem fourierCoeff_signVal (f : (ι → Bool) → Bool) (S : Finset ι) :
    fourierCoeff (fun x => signVal (f x)) S =
      1 - 2 * hammingDist f (parityOn S) / 2 ^ Fintype.card ι := by
  simp only [fourierCoeff, chi_eq_signVal_parityOn]
  exact expect_signVal_mul_signVal f (parityOn S)

/-! ### Character sums for the inner product -/

/-- **Character orthogonality for the inner product**, over any ring: the signs `(-1) ^ (w ⬝ᵥ y)`
cancel over all bit strings `y` unless `w = 0`, since flipping a bit `i` with `w i = true`
negates them. Over `ℝ` this is `sum_chi` for the set of positions where `w` is `true`. -/
theorem sum_ite_dotProduct [Ring R] (w : ι → Bool) :
    ∑ y : ι → Bool, (if w ⬝ᵥ y then (-1 : R) else 1) =
      if w = 0 then 2 ^ Fintype.card ι else 0 := by
  split_ifs with hw
  · subst hw
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    have hwi : w i = true := by simpa [Bool.zero_eq_false] using hi
    refine sum_involution (fun y _ => y + Pi.single i true) (fun y _ => ?_) (fun y _ _ => ?_)
      (fun y _ => mem_univ _) (fun y _ => ?_)
    · rw [dotProduct_add, dotProduct_single, hwi]
      cases w ⬝ᵥ y
      · rw [show (false + true * true : Bool) = true from rfl]
        simp
      · rw [show (true + true * true : Bool) = false from rfl]
        simp
    · intro h
      simpa using congrFun (add_eq_left.mp h) i
    · rw [add_assoc, ← Pi.single_add, BooleanRing.add_self, Pi.single_zero, add_zero]

end Fintype

end Cslib.BitString
