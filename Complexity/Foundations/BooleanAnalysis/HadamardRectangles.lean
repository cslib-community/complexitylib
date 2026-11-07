/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Foundations.Data.BitString.Sign
public import Mathlib.Data.Matrix.Mul
import Complexity.Foundations.BooleanAnalysis.Fourier
import Complexity.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Monochromatic rectangles for the inner product

Lindsey's lemma bounds the signed sum of the inner product modulo two `x ⬝ᵥ y` over a rectangle
`A × B` of bit strings indexed by `ι` by `√(|A| |B| 2 ^ |ι|)` in absolute value
(`BitString.sq_sum_signVal_dotProduct_le`). So if `x ⬝ᵥ y` is constant on `A × B`, the
rectangle has at most `2 ^ Fintype.card ι` entries. Empty sides, zero coordinates, and both
constant values are included.

The proof specializes Lindsey's bilinear bound to the identity matrix after the standard ring
equivalence between Boolean values and `ZMod 2`; it introduces no alternative inner product.

With real weights in place of sets, the sign matrix `(-1)^{x ⬝ᵥ y}` multiplies squared norms by
exactly `2 ^ |ι|` (`BitString.sum_sq_sum_mul_signVal_dotProduct`), so weighted bilinear sums obey
`(∑ₓ ∑ᵧ a(x) b(y) (-1)^{x ⬝ᵥ y})² ≤ 2 ^ |ι| ‖a‖² ‖b‖²`
(`BitString.sq_sum_mul_signVal_dotProduct_le`), by Cauchy–Schwarz and character orthogonality.
For probability weights this is the bias bound behind the Chor–Goldreich two-source extractor
[Chor and Goldreich][ChorGoldreich1988].

## Main results

* `Cslib.BitString.sq_sum_signVal_dotProduct_le`: Lindsey's lemma for signed sums of the inner
  product over rectangles.
* `Cslib.BitString.card_mul_le_two_pow_of_dotProduct_eq`: the monochromatic inner-product rectangle
  bound.
* `Cslib.BitString.sum_signVal_dotProduct_mul_signVal_dotProduct`: the rows of the sign matrix are
  orthogonal.
* `Cslib.BitString.sum_sq_sum_mul_signVal_dotProduct`: Parseval's identity for the Hadamard
  transform.
* `Cslib.BitString.sq_sum_mul_signVal_dotProduct_le`: Lindsey's lemma with real weights.

## References

* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
* [B. Chor and O. Goldreich, *Unbiased bits from sources of weak randomness and probabilistic
  communication complexity*][ChorGoldreich1988]
* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Lemma 2.4]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

open Matrix Finset

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι]

/-- **Lindsey's lemma for the inner product**: the signed sum of the inner product modulo two over
a rectangle `A × B` of bit strings indexed by `ι` is at most `√(|A| |B| 2 ^ |ι|)` in absolute
value. -/
theorem sq_sum_signVal_dotProduct_le (A B : Finset (ι → Bool)) :
    (∑ x ∈ A, ∑ y ∈ B, signVal (x ⬝ᵥ y)) ^ 2 ≤ #A * #B * 2 ^ Fintype.card ι := by
  classical
  let e : Bool ≃+* ZMod 2 := (ZMod.ringEquivOfPrime Bool Nat.prime_two (by decide)).symm
  let g : (ι → Bool) ↪ (ι → ZMod 2) :=
    ⟨fun x i => e (x i), fun _ _ h => funext fun i => e.injective (congrFun h i)⟩
  have hdot (x y : ι → Bool) : g x ⬝ᵥ g y = e (x ⬝ᵥ y) :=
    (e.toRingHom.map_dotProduct x y).symm
  have hsign (b : Bool) : (-1 : ℝ) ^ (e b).val = signVal b := by
    cases b <;> norm_num [show false = (0 : Bool) from rfl,
      show true = (1 : Bool) from rfl, show (1 : ZMod 2).val = 1 from rfl, signVal]
  have hL := Matrix.sq_sum_bilinear_mul_two_pow_rank_le
    (1 : Matrix ι ι (ZMod 2)) (A.map g) (B.map g) (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num)
  simp only [sum_map, Matrix.one_mulVec, Matrix.rank_one, card_map, one_mul, hdot,
    hsign] at hL
  have hp : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  refine (mul_le_mul_iff_left₀ hp).mp ?_
  linarith

/-- A rectangle on which the inner product modulo two is constant has at most
`2 ^ Fintype.card ι` entries. Neither side is required to be nonempty. -/
theorem card_mul_le_two_pow_of_dotProduct_eq (A B : Finset (ι → Bool)) (b : Bool)
    (h : ∀ x ∈ A, ∀ y ∈ B, x ⬝ᵥ y = b) :
    A.card * B.card ≤ 2 ^ Fintype.card ι := by
  have hs : ∑ x ∈ A, ∑ y ∈ B, signVal (x ⬝ᵥ y) = #A * #B * signVal b := by
    calc
      _ = ∑ x ∈ A, ∑ y ∈ B, signVal b := sum_congr rfl fun x hx => sum_congr rfl fun y hy => by
        rw [h x hx y hy]
      _ = _ := by simp [mul_assoc]
  have hL := sq_sum_signVal_dotProduct_le A B
  rw [hs, mul_pow, show signVal b ^ 2 = 1 by cases b <;> norm_num, mul_one, sq] at hL
  have : (#A : ℝ) * #B ≤ 2 ^ Fintype.card ι := by
    rcases (Nat.cast_nonneg (α := ℝ) (#A * #B)).eq_or_lt with h0 | h0
    · rw [Nat.cast_mul] at h0
      rw [← h0]
      positivity
    · rw [Nat.cast_mul] at h0
      exact le_of_mul_le_mul_left hL h0
  exact_mod_cast this

/-! ### Weighted sums: the Hadamard transform in `ℓ²` -/

variable [DecidableEq ι]

/-- **Orthogonality of the rows of the sign matrix** `(-1)^{x ⬝ᵥ y}`: distinct rows are orthogonal,
and every row has squared length `2 ^ |ι|`. -/
theorem sum_signVal_dotProduct_mul_signVal_dotProduct (x x' : ι → Bool) :
    ∑ y : ι → Bool, signVal (x ⬝ᵥ y) * signVal (x' ⬝ᵥ y) =
      if x = x' then 2 ^ Fintype.card ι else 0 := by
  have hsign (y : ι → Bool) : signVal (x ⬝ᵥ y) * signVal (x' ⬝ᵥ y) =
      if (x + x') ⬝ᵥ y then -1 else 1 := by
    rw [← signVal_xor, add_dotProduct]
    rfl
  by_cases hxx : x = x'
  · subst hxx
    simp [signVal_mul_self]
  · have hne : x + x' ≠ 0 := fun h => hxx (funext fun i => by
      have hi := congrFun h i
      simp only [Pi.add_apply, Pi.zero_apply] at hi
      revert hi
      cases x i <;> cases x' i <;> decide)
    simp only [hsign, sum_ite_dotProduct, hne, hxx, ite_false]

/-- **Parseval's identity for the Hadamard transform.** For real weights `a` on the bit strings
indexed by `ι`, the transform `y ↦ ∑ₓ a(x) (-1)^{x ⬝ᵥ y}` has squared norm `2 ^ |ι|` times that of
`a`: the sign matrix `(-1)^{x ⬝ᵥ y}` has orthogonal rows of squared length `2 ^ |ι|`. -/
theorem sum_sq_sum_mul_signVal_dotProduct (a : (ι → Bool) → ℝ) :
    ∑ y : ι → Bool, (∑ x, a x * signVal (x ⬝ᵥ y)) ^ 2 = 2 ^ Fintype.card ι * ∑ x, a x ^ 2 := by
  calc
    ∑ y : ι → Bool, (∑ x, a x * signVal (x ⬝ᵥ y)) ^ 2 =
        ∑ y : ι → Bool, ∑ x, ∑ x', a x * a x' * (signVal (x ⬝ᵥ y) * signVal (x' ⬝ᵥ y)) := by
      refine sum_congr rfl fun y _ => ?_
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun x _ => sum_congr rfl fun x' _ => by ring
    _ = ∑ x, ∑ x', ∑ y : ι → Bool, a x * a x' * (signVal (x ⬝ᵥ y) * signVal (x' ⬝ᵥ y)) := by
      rw [sum_comm]
      exact sum_congr rfl fun x _ => sum_comm
    _ = ∑ x, ∑ x', a x * a x' * ∑ y : ι → Bool, signVal (x ⬝ᵥ y) * signVal (x' ⬝ᵥ y) := by
      simp only [mul_sum]
    _ = 2 ^ Fintype.card ι * ∑ x, a x ^ 2 := by
      simp only [sum_signVal_dotProduct_mul_signVal_dotProduct, mul_ite, mul_zero, sum_ite_eq,
        mem_univ, ite_true, mul_sum]
      exact sum_congr rfl fun x _ => by ring

/-- **Lindsey's lemma with weights.** For real weights `a` and `b` on the bit strings indexed by
`ι`, `(∑ₓ ∑ᵧ a(x) b(y) (-1)^{x ⬝ᵥ y})² ≤ 2 ^ |ι| ‖a‖² ‖b‖²`. Indicators of `A` and `B` recover
`sq_sum_signVal_dotProduct_le`. -/
theorem sq_sum_mul_signVal_dotProduct_le (a b : (ι → Bool) → ℝ) :
    (∑ x, ∑ y, a x * b y * signVal (x ⬝ᵥ y)) ^ 2 ≤
      2 ^ Fintype.card ι * (∑ x, a x ^ 2) * ∑ y, b y ^ 2 := by
  have hswap : ∑ x, ∑ y, a x * b y * signVal (x ⬝ᵥ y) =
      ∑ y, b y * ∑ x, a x * signVal (x ⬝ᵥ y) := by
    rw [sum_comm]
    exact sum_congr rfl fun y _ => by rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
  rw [hswap]
  calc
    (∑ y, b y * ∑ x, a x * signVal (x ⬝ᵥ y)) ^ 2 ≤
        (∑ y, b y ^ 2) * ∑ y : ι → Bool, (∑ x, a x * signVal (x ⬝ᵥ y)) ^ 2 :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by rw [sum_sq_sum_mul_signVal_dotProduct]; ring

end Cslib.BitString
