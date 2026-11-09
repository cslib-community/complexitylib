/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Hamming
public import CslibFrontier.Foundations.Data.Code.Basic
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Hadamard code

The *Hadamard code* (or Walsh–Hadamard code) encodes a bit string `x : ι → Bool` as the truth
table of the function `a ↦ x ⬝ᵥ a`, the dot product in the Boolean ring `Bool`, that is, the inner
product modulo two (`BitString.hadamardCode`). Bit strings add coordinatewise through the same
ring structure, and the code is bilinear (`BitString.hadamardCode_add`,
`BitString.hadamardCode_add_left`). Its codewords are exactly the parities, hence exactly the
linear Boolean functions (`BitString.exists_eq_hadamardCode_iff`). Two distinct codewords of `n`
bits differ on half of the `2 ^ n` inputs (`BitString.two_mul_hammingDist_hadamardCode`), so for
`n ≥ 1` the Hadamard code has minimum distance `2 ^ (n - 1)`
(`BitString.minDist_range_hadamardCode`).

A function `f` that is close to a parity can be *self-corrected*: to read the parity at `x`, read
`f` at a uniformly random `y` and at `x + y`, both uniformly distributed, and add the two bits
(`BitString.selfCorrect`). If `f` differs from the parity on an `ε` fraction of the inputs, this
returns the parity's value at `x` with probability at least `1 - 2ε`, whatever `x` is
(`BitString.one_sub_two_mul_le_expect_selfCorrect`). For the Hadamard code this is a two-query
*local decoder*: the `i`-th bit of the message is read off at the `i`-th unit vector
(`BitString.one_sub_two_mul_le_expect_selfCorrect_eq_apply`). A word within relative distance
`δ < 1/4` of a codeword determines the codeword (`BitString.eq_of_hammingDist_hadamardCode_le`)
[O'Donnell, Section 1.6][ODonnell2014], [Arora and Barak, Chapters 11 and 19][AroraBarak09].

## Main definitions

* `Cslib.BitString.selfCorrect`: the two-query self-corrected read of a Boolean function.
* `Cslib.BitString.hadamardCode`: the Hadamard encoding of a bit string.

## Main results

* `Cslib.BitString.hadamardCode_eq_parityOn`: a codeword is a parity.
* `Cslib.BitString.card_filter_selfCorrect_ne_le`,
  `Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect`: local correctability of parities.
* `Cslib.BitString.exists_eq_hadamardCode_iff`: the codewords are the linear functions.
* `Cslib.BitString.hadamardCode_injective`, `Cslib.BitString.two_mul_hammingDist_hadamardCode`,
  `Cslib.BitString.minDist_range_hadamardCode`: the Hadamard code is injective with relative
  distance one half and minimum distance `2 ^ (n - 1)`.
* `Cslib.BitString.two_mul_card_dotProduct_eq_true_add`: a nonzero bit string has inner product
  `true` with half of strings.
* `Cslib.BitString.two_mul_card_dotProduct_eq_true_add_two_pow`: inner product `true` count over
  all pairs.
* `Cslib.BitString.eq_of_hammingDist_hadamardCode_le`: unique decoding below distance `1/4`.
* `Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect_eq_apply`: local decoding with two
  queries.

## References

* [M. Blum, M. Luby, R. Rubinfeld, *Self-testing/correcting with applications to numerical
  problems*][BlumLubyRubinfeld1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*}

/-! ### Self-correction -/

/-- The self-corrected read of `f` at `x` with randomness `y`: the exclusive or of `f y` and
`f (x + y)`. For uniformly random `y`, both points read are uniformly random, and on a parity the
read is exact (`selfCorrect_parityOn`). -/
def selfCorrect (f : (ι → Bool) → Bool) (x y : ι → Bool) : Bool :=
  f y ^^ f (x + y)

/-- Self-correction reads a parity exactly. -/
@[simp] theorem selfCorrect_parityOn (S : Finset ι) (x y : ι → Bool) :
    selfCorrect (parityOn S) x y = parityOn S x := by
  rw [selfCorrect, parityOn_add, Bool.xor_left_comm, Bool.xor_self, Bool.xor_false]

variable [Fintype ι]

section DecidableEq

variable [DecidableEq ι]

/-- **Local correctability of parities**, counting version: the self-corrected read of `f` at `x`
differs from the parity on `S` at `x` for at most twice as many `y` as there are inputs on which
`f` differs from that parity. -/
theorem card_filter_selfCorrect_ne_le (f : (ι → Bool) → Bool) (S : Finset ι)
    (x : ι → Bool) :
    #{y | selfCorrect f x y ≠ parityOn S x} ≤ 2 * hammingDist f (parityOn S) := by
  have htrans : #{y : ι → Bool | f (x + y) ≠ parityOn S (x + y)} =
      hammingDist f (parityOn S) :=
    card_equiv (Equiv.addLeft x) fun y => by
      simp only [mem_filter, mem_univ, true_and]
      exact Iff.rfl
  calc #{y | selfCorrect f x y ≠ parityOn S x}
      ≤ #(({y | f y ≠ parityOn S y} : Finset (ι → Bool)) ∪
          ({y | f (x + y) ≠ parityOn S (x + y)} : Finset _)) := by
        refine card_le_card fun y hy => ?_
        simp only [mem_union, mem_filter, mem_univ, true_and] at hy ⊢
        by_contra h
        simp only [not_or, ne_eq, not_not] at h
        exact hy (by rw [selfCorrect, h.1, h.2]; exact selfCorrect_parityOn S x y)
    _ ≤ _ := card_union_le _ _
    _ = 2 * hammingDist f (parityOn S) := by rw [htrans, two_mul]; rfl

/-- **Local correctability of parities**: if `f` differs from the parity on `S` on at most an `ε`
fraction of the inputs, then for every `x`, self-correction at `x` returns the parity's value at
`x` with probability at least `1 - 2ε` over a uniformly random `y`
[O'Donnell, Proposition 1.31][ODonnell2014]. -/
theorem one_sub_two_mul_le_expect_selfCorrect {f : (ι → Bool) → Bool} {S : Finset ι}
    {ε : ℝ} (h : (hammingDist f (parityOn S) : ℝ) / 2 ^ Fintype.card ι ≤ ε) (x : ι → Bool) :
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f x y = parityOn S x then 1 else 0 := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hne : (#{y | selfCorrect f x y ≠ parityOn S x} : ℝ) ≤ 2 * hammingDist f (parityOn S) := by
    exact_mod_cast card_filter_selfCorrect_ne_le f S x
  have htotal : (#{y | selfCorrect f x y = parityOn S x} : ℝ) +
      #{y | selfCorrect f x y ≠ parityOn S x} = 2 ^ Fintype.card ι := by
    exact_mod_cast (card_filter_add_card_filter_not (s := univ)
      fun y : ι → Bool => selfCorrect f x y = parityOn S x).trans (by simp)
  rw [div_le_iff₀ hpos] at h
  rw [Fintype.expect_boole, nnratCast_dens, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat, le_div_iff₀ hpos]
  linarith

end DecidableEq

/-! ### The Hadamard code -/

/-- The Hadamard encoding of `x`: the Boolean function sending `a` to the dot product `x ⬝ᵥ a` in
the Boolean ring `Bool`, the inner product of `x` and `a` modulo two
[Arora and Barak, Section 11.5][AroraBarak09]. -/
def hadamardCode (x : ι → Bool) : (ι → Bool) → Bool :=
  fun a => x ⬝ᵥ a

/-- The Hadamard codeword of `x` at `a` is the dot product `x ⬝ᵥ a`. -/
@[simp] theorem hadamardCode_apply (x a : ι → Bool) : hadamardCode x a = x ⬝ᵥ a :=
  rfl

/-- A Hadamard codeword is the parity of the bits at the positions where the message is
`true`. -/
theorem hadamardCode_eq_parityOn (x : ι → Bool) :
    hadamardCode x = parityOn {i | x i = true} := by
  funext a
  rw [parityOn_eq_sum, sum_filter, hadamardCode_apply, dotProduct]
  exact sum_congr rfl fun i _ => by cases x i <;> rfl

/-- The inner product is symmetric. -/
theorem hadamardCode_comm (x a : ι → Bool) : hadamardCode x a = hadamardCode a x :=
  dotProduct_comm x a

/-- Hadamard codewords are linear. -/
theorem hadamardCode_add (x a b : ι → Bool) :
    hadamardCode x (a + b) = (hadamardCode x a ^^ hadamardCode x b) :=
  dotProduct_add x a b

/-- The Hadamard code is linear. -/
theorem hadamardCode_add_left (x y a : ι → Bool) :
    hadamardCode (x + y) a = (hadamardCode x a ^^ hadamardCode y a) :=
  add_dotProduct x y a

/-- Self-correction reads a Hadamard codeword exactly. -/
@[simp] theorem selfCorrect_hadamardCode (x a y : ι → Bool) :
    selfCorrect (hadamardCode x) a y = hadamardCode x a := by
  rw [hadamardCode_eq_parityOn, selfCorrect_parityOn]

/-- The parity on `S` is the Hadamard encoding of the indicator of `S`. -/
theorem hadamardCode_decide_mem [DecidableEq ι] (S : Finset ι) :
    hadamardCode (fun i => decide (i ∈ S)) = parityOn S := by
  simp [hadamardCode_eq_parityOn]

/-- The value of a Hadamard codeword at the `i`-th unit vector is the `i`-th bit of the
message. -/
@[simp high] theorem hadamardCode_single [DecidableEq ι] (x : ι → Bool) (i : ι) :
    hadamardCode x (Pi.single i true) = x i :=
  dotProduct_single_one x i

/-- **The Hadamard codewords are the linear Boolean functions.** -/
theorem exists_eq_hadamardCode_iff {f : (ι → Bool) → Bool} :
    (∃ x, f = hadamardCode x) ↔ ∀ x y, f (x + y) = (f x ^^ f y) := by
  classical
  rw [← exists_eq_parityOn_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hadamardCode_eq_parityOn x⟩
  · rintro ⟨S, rfl⟩
    exact ⟨_, (hadamardCode_decide_mem S).symm⟩

/-- The Hadamard code is injective. -/
theorem hadamardCode_injective : Function.Injective (hadamardCode (ι := ι)) := fun x y h => by
  classical
  exact funext fun i => by rw [← hadamardCode_single x, h, hadamardCode_single]

variable [DecidableEq ι]

/-- **The Hadamard code has relative distance one half**: the encodings of distinct bit strings
differ on exactly half of the inputs. -/
theorem two_mul_hammingDist_hadamardCode {x y : ι → Bool} (h : x ≠ y) :
    2 * hammingDist (hadamardCode x) (hadamardCode y) = 2 ^ Fintype.card ι := by
  rw [hadamardCode_eq_parityOn, hadamardCode_eq_parityOn]
  exact two_mul_hammingDist_parityOn fun hS => h <| hadamardCode_injective <| by
    rw [hadamardCode_eq_parityOn, hadamardCode_eq_parityOn, hS]

/-- A nonzero bit string has inner product `true` with exactly half of all bit strings, and the
zero string with none. -/
theorem two_mul_card_dotProduct_eq_true_add (x : ι → Bool) :
    2 * #{y | x ⬝ᵥ y = true} + (if x = 0 then 2 ^ Fintype.card ι else 0) = 2 ^ Fintype.card ι := by
  split_ifs with hx
  · subst hx
    simp [zero_dotProduct]
  · have h := two_mul_hammingDist_hadamardCode hx
    rw [hammingDist] at h
    simpa [zero_dotProduct,
      show ∀ b : Bool, ¬b = 0 ↔ b = true by decide] using h

/-- The inner product is `true` on `2 ^ (k - 1) (2 ^ k - 1)` pairs of `k`-bit strings, in the form
`2 c + 2 ^ k = 2 ^ k 2 ^ k`. -/
theorem two_mul_card_dotProduct_eq_true_add_two_pow :
    2 * #{q : (ι → Bool) × (ι → Bool) | q.1 ⬝ᵥ q.2 = true} + 2 ^ Fintype.card ι =
      2 ^ Fintype.card ι * 2 ^ Fintype.card ι := by
  have hrow : #{q : (ι → Bool) × (ι → Bool) | q.1 ⬝ᵥ q.2 = true} =
      ∑ x : ι → Bool, #{y | x ⬝ᵥ y = true} := by
    rw [card_filter, Fintype.sum_prod_type]
    exact sum_congr rfl fun x _ => (card_filter _ _).symm
  have hsum := sum_congr rfl fun x (_ : x ∈ (univ : Finset (ι → Bool))) =>
    two_mul_card_dotProduct_eq_true_add x
  rw [sum_add_distrib, ← mul_sum, sum_ite_eq', sum_const, card_univ] at hsum
  simpa [hrow, Fintype.card_fun] using hsum

/-- **Unique decoding**: a Boolean function within relative distance `δ < 1/4` of the encodings
of `x` and of `y` forces `x = y`. -/
theorem eq_of_hammingDist_hadamardCode_le {f : (ι → Bool) → Bool} {x y : ι → Bool} {δ : ℝ}
    (hδ : δ < 1 / 4) (hx : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ δ)
    (hy : (hammingDist f (hadamardCode y) : ℝ) / 2 ^ Fintype.card ι ≤ δ) : x = y := by
  by_contra hxy
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hdist : (2 * hammingDist (hadamardCode x) (hadamardCode y) : ℝ) = 2 ^ Fintype.card ι := by
    exact_mod_cast two_mul_hammingDist_hadamardCode hxy
  have htri : (hammingDist (hadamardCode x) (hadamardCode y) : ℝ) ≤
      hammingDist f (hadamardCode x) + hammingDist f (hadamardCode y) := by
    exact_mod_cast hammingDist_triangle_left _ _ f
  rw [div_le_iff₀ hpos] at hx hy
  nlinarith

/-- **Local correction for the Hadamard code**: if `f` is within relative distance `ε` of the
encoding of `x`, then for every `a`, self-correction at `a` returns the codeword's value at `a`
with probability at least `1 - 2ε`. -/
theorem one_sub_two_mul_le_expect_selfCorrect_hadamardCode {f : (ι → Bool) → Bool}
    {x : ι → Bool} {ε : ℝ} (h : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε)
    (a : ι → Bool) :
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f a y = hadamardCode x a then 1 else 0 := by
  rw [hadamardCode_eq_parityOn] at h ⊢
  exact one_sub_two_mul_le_expect_selfCorrect h a

/-- **Local decoding of the Hadamard code with two queries**: if `f` is within relative distance
`ε` of the encoding of `x`, then self-correction at the `i`-th unit vector returns `x i` with
probability at least `1 - 2ε` [Arora and Barak, Section 11.5][AroraBarak09]. -/
theorem one_sub_two_mul_le_expect_selfCorrect_eq_apply {f : (ι → Bool) → Bool}
    {x : ι → Bool} {ε : ℝ} (h : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε)
    (i : ι) :
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f (Pi.single i true) y = x i then 1 else 0 := by
  simpa only [hadamardCode_single] using
    one_sub_two_mul_le_expect_selfCorrect_hadamardCode h (Pi.single i true)

/-- **The distance of the Hadamard code.** For messages of `n ≥ 1` bits, the Hadamard code has
minimum distance `2 ^ (n - 1)`: half of its length `2 ^ n`. -/
theorem minDist_range_hadamardCode [Nonempty ι] :
    Code.minDist (Set.range (hadamardCode (ι := ι))) = (2 ^ (Fintype.card ι - 1) : ℕ) := by
  have hdist {x y : ι → Bool} (h : x ≠ y) :
      hammingDist (hadamardCode x) (hadamardCode y) = 2 ^ (Fintype.card ι - 1) := by
    have := two_mul_hammingDist_hadamardCode h
    rw [← Nat.sub_add_cancel (Fintype.card_pos (α := ι)), pow_succ, mul_comm _ 2] at this
    exact Nat.eq_of_mul_eq_mul_left two_pos this
  have hne : (fun _ => false : ι → Bool) ≠ fun _ => true := fun h =>
    Bool.false_ne_true (congrFun h (Classical.arbitrary ι))
  refine le_antisymm ?_ (Code.le_minDist_iff.2 ?_)
  · rw [← hdist hne]
    exact Code.minDist_le_hammingDist ⟨_, rfl⟩ ⟨_, rfl⟩
      fun h => hne (hadamardCode_injective h)
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    rw [hdist fun h => hxy (congrArg hadamardCode h)]

end Cslib.BitString
