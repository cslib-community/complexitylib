/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Parameters
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# GSW parameters with a logarithmic-depth noise margin

For `t = 1 + clog 2 (λ + 2)`, choose digit width `w = 16384 * t^2`, ciphertext dimension
`N = (n + 1) * w`, sample count `m = N + 2λ`, and depth budget `L = 512 * t`. The secret and
positive-noise dimensions reuse `Parameters.dimension` and `Parameters.noise`, both `λ + 1`.
The complete margin `4 * m * η * (N + 1)^L < 2^w` holds at every security parameter.

All dimensions and the budget have uniform unary native routines. The modulus has a binary
routine; its value is not claimed polynomially bounded. Security assumes decision LWE for
exactly this family's centered-binomial law. These numerical bounds do not establish that an
actual augmented decryption circuit fits the budget, or assert lattice hardness or circular
security.

## Main definitions

* `logSize`, `width`, `rows`, `samples`, `depthBudget`, `modulus`: the numerical family.

## Main results

* `noise_margin`: the strict decoding margin after the entire declared depth budget.
* `entropy_margin`, `negligible_statistical_error`: the statistical part of the security bound.
* `polynomiallyBounded_parameters`: polynomial bounds for the unary numerical parameters.
* `computableInPolyTime_modulus`: native computation of the binary modulus.

## References

* [Gentry, Sahai and Waters, Sections 3.3–3.4][GentrySahaiWaters2013]

The constants here supply explicit compatible inequalities for the power-of-two specialization;
they are not a claim about the paper's hardness parameters.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW.DepthParameters

open Parameters (dimension noise)
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped NNReal

/-- A positive logarithmic size, at least two even at security parameter zero. -/
def logSize (security : ℕ) : ℕ := 1 + Nat.clog 2 (security + 2)

/-- Binary digits in each modular coordinate. -/
def width (security : ℕ) : ℕ := 16384 * logSize security ^ 2

/-- Ciphertext rows and columns. -/
def rows (security : ℕ) : ℕ := (dimension security + 1) * width security

/-- Public samples and independent source bits in each encryption row. -/
def samples (security : ℕ) : ℕ := rows security + 2 * security

/-- Number of NAND levels covered by the proved noise margin. -/
def depthBudget (security : ℕ) : ℕ := 512 * logSize security

/-- Modulus, represented in binary by the native routine below. -/
def modulus (security : ℕ) : ℕ := 2 ^ width security

/-- The logarithmic size is uniformly bounded away from zero. -/
theorem two_le_logSize (security : ℕ) : 2 ≤ logSize security := by
  have := Nat.clog_pos Nat.one_lt_two (by omega : 1 < security + 2)
  unfold logSize
  omega

/-- A simple linear majorant for the logarithmic size. -/
theorem logSize_le (security : ℕ) : logSize security ≤ security + 2 := by
  have hpow : security + 2 ≤ 2 ^ (security + 1) := Nat.lt_two_pow_self
  have := Nat.clog_le_of_le_pow hpow
  unfold logSize
  omega

/-- Every parameter has a nonempty modular word. -/
theorem width_pos (security : ℕ) : 0 < width security := by
  have := two_le_logSize security
  unfold width
  positivity

/-- The depth budget is positive for every security parameter. -/
theorem depthBudget_pos (security : ℕ) : 0 < depthBudget security := by
  have := two_le_logSize security
  unfold depthBudget
  positivity

/-- The number of samples has exactly the required entropy surplus. -/
theorem entropy_margin (security : ℕ) : rows security + 2 * security ≤ samples security := le_rfl

/-- The binary digit width has an explicit quadratic majorant. -/
theorem width_le (security : ℕ) : width security ≤ 16384 * (security + 2) ^ 2 :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (logSize_le security) 2)

/-- The ciphertext dimension has an explicit cubic majorant. -/
theorem rows_le (security : ℕ) : rows security ≤ 16384 * (security + 2) ^ 3 := by
  calc
    rows security ≤ (security + 2) * (16384 * (security + 2) ^ 2) :=
      Nat.mul_le_mul_left _ (width_le security)
    _ = _ := by ring

/-- The public sample count has an explicit cubic majorant. -/
theorem samples_le (security : ℕ) : samples security ≤ 16386 * (security + 2) ^ 3 := by
  have h := rows_le security
  have hpow : security + 2 ≤ (security + 2) ^ 3 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ security + 2) (by decide : 1 ≤ 3)
  unfold samples
  nlinarith

/-- The logarithmic budget also has a linear majorant. -/
theorem depthBudget_le (security : ℕ) : depthBudget security ≤ 512 * (security + 2) :=
  Nat.mul_le_mul_left _ (logSize_le security)

private theorem sizes_le_pow (security : ℕ) :
    rows security + 1 ≤ 2 ^ (11 * logSize security) ∧
      samples security ≤ 2 ^ (11 * logSize security) ∧ noise security ≤ 2 ^ logSize security := by
  let t := logSize security
  have ht : 2 ≤ t := two_le_logSize security
  have hn : security + 2 ≤ 2 ^ t :=
    (Nat.le_pow_clog Nat.one_lt_two _).trans
      (Nat.pow_le_pow_right (by decide) (by dsimp [t, logSize]; omega))
  have hlog : t ≤ 2 ^ t := (Nat.lt_two_pow_self (n := t)).le
  have hrows : rows security ≤ 2 ^ (14 + 3 * t) := by
    calc
      rows security ≤ 2 ^ t * (16384 * (2 ^ t) ^ 2) :=
        Nat.mul_le_mul hn (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlog 2))
      _ = _ := by rw [pow_add, Nat.mul_comm 3 t, pow_mul]; ring
  have hsmall : 2 * security ≤ rows security := by
    have hw : 2 ≤ width security := by unfold width; change 2 ≤ 16384 * t ^ 2; nlinarith
    unfold rows dimension
    nlinarith
  have hnext : 2 * 2 ^ (14 + 3 * t) ≤ 2 ^ (11 * t) := by
    calc
      _ = 2 ^ (15 + 3 * t) := by
        rw [show 15 + 3 * t = (14 + 3 * t) + 1 by omega, pow_succ]
        omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ (14 + 3 * t) := by positivity
  refine ⟨(by omega : rows security + 1 ≤ 2 * 2 ^ (14 + 3 * t)).trans hnext, ?_, ?_⟩
  · exact (by unfold samples; omega : samples security ≤ 2 * 2 ^ (14 + 3 * t)).trans hnext
  · change security + 1 ≤ 2 ^ t
    omega

/-- The complete declared NAND depth remains strictly inside the original decoding margin. -/
theorem noise_margin (security : ℕ) :
    4 * samples security * noise security * (rows security + 1) ^ depthBudget security <
      modulus security := by
  let t := logSize security
  have ht : 2 ≤ t := two_le_logSize security
  obtain ⟨hrows, hsamples, hnoise⟩ := sizes_le_pow security
  calc
    _ ≤ 4 * 2 ^ (11 * t) * 2 ^ t * (2 ^ (11 * t)) ^ (512 * t) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hsamples) hnoise)
        (Nat.pow_le_pow_left hrows _)
    _ = 2 ^ (5632 * t ^ 2 + 12 * t + 2) := by
      calc
        _ = 2 ^ (2 + 11 * t + t + (11 * t) * (512 * t)) := by
          rw [← pow_mul, pow_add, pow_add, pow_add]
          norm_num
        _ = _ := by congr 1; ring
    _ < modulus security := by
      apply Nat.pow_lt_pow_right (by decide)
      change 5632 * t ^ 2 + 12 * t + 2 < 16384 * t ^ 2
      nlinarith

/-- Every smaller depth also satisfies the full noise margin. -/
theorem noise_margin_of_le {security depth : ℕ} (hdepth : depth ≤ depthBudget security) :
    4 * samples security * noise security * (rows security + 1) ^ depth < modulus security :=
  (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hdepth)).trans_lt
    (noise_margin security)

/-- Fresh ciphertexts satisfy the strict decoding margin. -/
theorem fresh_margin (security : ℕ) :
    4 * samples security * noise security < modulus security := by
  simpa only [pow_zero, mul_one] using
    noise_margin_of_le (security := security) (depth := 0) (Nat.zero_le _)

/-- A NAND of two fresh ciphertexts satisfies the existing sampler theorem's margin. -/
theorem nand_margin (security : ℕ) :
    4 * ((1 + rows security) * (samples security * noise security)) < modulus security := by
  simpa only [pow_one, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    noise_margin_of_le (security := security) (depth := 1) (depthBudget_pos security)

/-- The logarithmic size is uniformly computable with unary input and output. -/
@[fun_prop]
theorem computableInPolyTime_logSize :
    ComputableInPolyTime logSize encUnary encUnary := by
  have := unary_clog_const 2
  unfold logSize
  fun_prop

/-- Compute the unary digit width, including its quadratic dependence on the logarithm. -/
@[fun_prop]
theorem computableInPolyTime_width :
    ComputableInPolyTime width encUnary encUnary := by unfold width; fun_prop

/-- Compute the unary ciphertext dimension. -/
@[fun_prop]
theorem computableInPolyTime_rows :
    ComputableInPolyTime rows encUnary encUnary := by unfold rows; fun_prop

/-- Compute the unary public sample count. -/
@[fun_prop]
theorem computableInPolyTime_samples :
    ComputableInPolyTime samples encUnary encUnary := by unfold samples; fun_prop

/-- Compute the unary logarithmic depth budget. -/
@[fun_prop]
theorem computableInPolyTime_depthBudget :
    ComputableInPolyTime depthBudget encUnary encUnary := by unfold depthBudget; fun_prop

/-- Compute the modulus in binary; this does not assert efficient unary output. -/
@[fun_prop]
theorem computableInPolyTime_modulus :
    ComputableInPolyTime modulus encUnary encNat :=
  binary_pow' (const 2) DepthParameters.computableInPolyTime_width

private theorem polynomiallyBounded_of_unary {f : ℕ → ℕ}
    (hf : ComputableInPolyTime f encUnary encUnary) : PolynomiallyBounded f :=
  (show PolyBounded (fun n : ℕ => n) f by
    simpa only [encUnary_apply, List.length_replicate] using
      hf.polyBounded_length).polynomiallyBounded

/-- All unary parameters have polynomial bounds; the modulus is deliberately excluded. -/
theorem polynomiallyBounded_parameters :
    PolynomiallyBounded dimension ∧ PolynomiallyBounded noise ∧ PolynomiallyBounded width ∧
      PolynomiallyBounded rows ∧ PolynomiallyBounded samples ∧ PolynomiallyBounded depthBudget :=
  ⟨polynomiallyBounded_of_unary Parameters.computableInPolyTime_dimension,
    polynomiallyBounded_of_unary Parameters.computableInPolyTime_noise,
    polynomiallyBounded_of_unary DepthParameters.computableInPolyTime_width,
    polynomiallyBounded_of_unary DepthParameters.computableInPolyTime_rows,
    polynomiallyBounded_of_unary DepthParameters.computableInPolyTime_samples,
    polynomiallyBounded_of_unary computableInPolyTime_depthBudget⟩

/-- The actual shared-public-matrix error bound is negligible for this new family. -/
theorem negligible_statistical_error :
    Negligible (fun security => (rows security : ℝ≥0) *
      NNReal.sqrt ((2 : ℝ≥0) ^ rows security / 2 ^ samples security)) :=
  negligible_mul_sqrt_pow_two_div_pow_two
    (polynomiallyBounded_of_unary DepthParameters.computableInPolyTime_rows)
    (Filter.Eventually.of_forall entropy_margin)

end Cslib.Crypto.Homomorphic.GSW.DepthParameters
