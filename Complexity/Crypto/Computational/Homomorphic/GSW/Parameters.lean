/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Negligible.Dyadic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Foundations.Data.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Compatible positive-noise GSW parameters

For `k = λ + 1`, choose `n = η = k`, `w = 16 + 8 * clog 2 k`, ciphertext dimension
`N = (n + 1) * w`, and `m = N + 2 * λ` samples. This explicit family satisfies the statistical
entropy margin and the strict fresh-encryption and one-NAND noise margins simultaneously.

These are arithmetic and native-runtime facts about the parameter functions. They neither assert
decision-LWE hardness for the finite centered-binomial error nor prove bootstrappability.

## Main definitions

* `dimension`, `noise`, `width`, `rows`, `samples`, `modulus`: the numerical parameter family.

## Main results

* `entropy_margin`: twice the security parameter in surplus source bits.
* `fresh_margin`, `nand_margin`: strict decoding margins with positive noise.
* `negligible_statistical_error`: the shared-public-matrix error is negligible.
* `computableInPolyTime_dimension`, `computableInPolyTime_noise`,
  `computableInPolyTime_width`, `computableInPolyTime_rows`,
  `computableInPolyTime_samples`, `computableInPolyTime_modulus`: uniform unary
  native computation of each parameter.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Sections 3.1–3.2]
  [GentrySahaiWaters2013]

The family here supplies explicit compatible inequalities for the power-of-two specialization;
it is not a claim about the paper's hardness parameters.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW.Parameters

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped NNReal

/-- Number of secret coordinates. -/
def dimension (security : ℕ) : ℕ := security + 1

/-- Positive centered-binomial width. -/
def noise (security : ℕ) : ℕ := security + 1

/-- Number of binary digits in one modular coordinate. -/
def width (security : ℕ) : ℕ := 16 + 8 * Nat.clog 2 (security + 1)

/-- Number of ciphertext rows. -/
def rows (security : ℕ) : ℕ := (dimension security + 1) * width security

/-- Number of public samples and source bits in each encryption row. -/
def samples (security : ℕ) : ℕ := rows security + 2 * security

/-- Power-of-two modulus. -/
def modulus (security : ℕ) : ℕ := 2 ^ width security

/-- The noise is positive even at security parameter zero. -/
theorem noise_pos (security : ℕ) : 0 < noise security := by simp [noise]

/-- Every parameter uses a nonempty modular bit representation. -/
theorem width_pos (security : ℕ) : 0 < width security := by unfold width; omega

/-- Each encryption row has the surplus required by the shared-public-matrix bound. -/
theorem entropy_margin (security : ℕ) : rows security + 2 * security ≤ samples security := le_rfl

private theorem clog_le (security : ℕ) : Nat.clog 2 (security + 1) ≤ security :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := security))

/-- The digit width has a simple linear majorant. -/
theorem width_le (security : ℕ) : width security ≤ 16 * (security + 1) := by
  have := clog_le security
  unfold width
  omega

/-- The ciphertext dimension has a uniform quadratic majorant. -/
theorem rows_le (security : ℕ) : rows security ≤ 32 * (security + 1) ^ 2 := by
  calc
    rows security ≤ (security + 2) * (16 * (security + 1)) := by
      exact Nat.mul_le_mul_left _ (width_le security)
    _ ≤ 32 * (security + 1) ^ 2 := by nlinarith

/-- The number of public samples has a uniform quadratic majorant. -/
theorem samples_le (security : ℕ) : samples security ≤ 34 * (security + 1) ^ 2 := by
  have := rows_le security
  unfold samples
  nlinarith

/-- The modulus dominates the eighth power of the positive parameter. -/
theorem modulus_ge (security : ℕ) : 65536 * (security + 1) ^ 8 ≤ modulus security := by
  have h := Nat.pow_le_pow_left (Nat.le_pow_clog Nat.one_lt_two (security + 1)) 8
  calc
    _ ≤ 65536 * (2 ^ Nat.clog 2 (security + 1)) ^ 8 := Nat.mul_le_mul_left _ h
    _ = modulus security := by simp [modulus, width, pow_add, pow_mul, Nat.mul_comm]

/-- The modulus also has an explicit polynomial upper bound. -/
theorem modulus_le (security : ℕ) : modulus security ≤ 16777216 * (security + 1) ^ 8 := by
  have h := Nat.pow_le_pow_left
    (Nat.pow_clog_le_mul Nat.one_lt_two (by omega : security + 1 ≠ 0)) 8
  calc
    modulus security = 65536 * (2 ^ Nat.clog 2 (security + 1)) ^ 8 := by
      simp [modulus, width, pow_add, pow_mul, Nat.mul_comm]
    _ ≤ 65536 * (2 * (security + 1)) ^ 8 := Nat.mul_le_mul_left _ h
    _ = _ := by ring

/-- NAND of two fresh ciphertexts lies strictly inside the decoder's noise margin. -/
theorem nand_margin (security : ℕ) :
    4 * (1 + rows security) * samples security * noise security < modulus security := by
  have hk : 1 ≤ (security + 1) ^ 2 := by
    have : 0 < (security + 1) ^ 2 := by positivity
    omega
  have hrows : 1 + rows security ≤ 33 * (security + 1) ^ 2 := by
    have := rows_le security
    omega
  have hbound : 4 * (1 + rows security) * samples security * noise security ≤
      4488 * (security + 1) ^ 5 := by
    calc
      _ ≤ 4 * (33 * (security + 1) ^ 2) * (34 * (security + 1) ^ 2) * (security + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hrows) (samples_le security))
      _ = _ := by ring
  have hpow : (security + 1) ^ 5 ≤ (security + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 0 < (security + 1) ^ 5 := by positivity
  exact hbound.trans_lt ((by nlinarith : 4488 * (security + 1) ^ 5 <
    65536 * (security + 1) ^ 8).trans_le (modulus_ge security))

/-- Fresh encryption lies strictly inside the decoder's noise margin. -/
theorem fresh_margin (security : ℕ) : 4 * samples security * noise security < modulus security := by
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (by omega : 4 ≤ 4 * (1 + rows security)))).trans_lt (nand_margin security)

/-- The secret dimension is uniformly computable on unary parameters. -/
@[fun_prop]
theorem computableInPolyTime_dimension :
    ComputableInPolyTime dimension encUnary encUnary := by
  unfold dimension
  fun_prop

/-- The positive noise width is uniformly computable on unary parameters. -/
@[fun_prop]
theorem computableInPolyTime_noise :
    ComputableInPolyTime noise encUnary encUnary := by
  unfold noise
  fun_prop

/-- The logarithmic digit width is uniformly computable on unary parameters. -/
@[fun_prop]
theorem computableInPolyTime_width :
    ComputableInPolyTime width encUnary encUnary := by
  have := ComputableInPolyTime.unary_clog_const 2
  unfold width
  fun_prop

/-- The ciphertext dimension is uniformly computable on unary parameters. -/
@[fun_prop]
theorem computableInPolyTime_rows :
    ComputableInPolyTime rows encUnary encUnary := by
  unfold rows
  fun_prop

/-- The public sample count is uniformly computable on unary parameters. -/
@[fun_prop]
theorem computableInPolyTime_samples :
    ComputableInPolyTime samples encUnary encUnary := by
  unfold samples
  fun_prop

/-- Even the modulus itself has a uniform unary native certificate. This uses bounded powers
of a ceiling logarithm, rather than treating arbitrary unary exponentiation as efficient. -/
@[fun_prop]
theorem computableInPolyTime_modulus :
    ComputableInPolyTime modulus encUnary encUnary := by
  have := ComputableInPolyTime.unary_pow_clog_const (input := encUnary)
    (size := fun security => security + 1) (by fun_prop) 256 2
  have hmodulus : modulus = fun security => 65536 * 256 ^ Nat.clog 2 (security + 1) := by
    funext security
    norm_num [modulus, width, pow_add, pow_mul]
  rw [hmodulus]
  fun_prop

private theorem polynomiallyBounded_of_unary {f : ℕ → ℕ}
    (hf : ComputableInPolyTime f encUnary encUnary) : PolynomiallyBounded f :=
  (show PolyBounded (fun n : ℕ => n) f by
    simpa only [encUnary_apply, List.length_replicate] using
      hf.polyBounded_length).polynomiallyBounded

/-- Every numerical parameter, including the modulus, is polynomially bounded. -/
theorem polynomiallyBounded_parameters :
    PolynomiallyBounded dimension ∧ PolynomiallyBounded noise ∧ PolynomiallyBounded width ∧
      PolynomiallyBounded rows ∧ PolynomiallyBounded samples ∧ PolynomiallyBounded modulus :=
  ⟨polynomiallyBounded_of_unary computableInPolyTime_dimension,
    polynomiallyBounded_of_unary computableInPolyTime_noise,
    polynomiallyBounded_of_unary computableInPolyTime_width,
    polynomiallyBounded_of_unary computableInPolyTime_rows,
    polynomiallyBounded_of_unary computableInPolyTime_samples,
    polynomiallyBounded_of_unary computableInPolyTime_modulus⟩

/-- The exact shared-public-matrix error bound is negligible for this positive-noise family. -/
theorem negligible_statistical_error :
    Negligible (fun security => (rows security : ℝ≥0) *
      NNReal.sqrt ((2 : ℝ≥0) ^ rows security / 2 ^ samples security)) :=
  negligible_mul_sqrt_pow_two_div_pow_two (polynomiallyBounded_of_unary computableInPolyTime_rows)
    (Filter.Eventually.of_forall entropy_margin)

end Cslib.Crypto.Homomorphic.GSW.Parameters
