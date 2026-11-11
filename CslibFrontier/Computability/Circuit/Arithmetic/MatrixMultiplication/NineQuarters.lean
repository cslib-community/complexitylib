/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.Exponent
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Round

/-!
# The matrix multiplication exponent is at most `9/4`

Over every field of characteristic zero, for every `γ > 0`, `n × n` matrix multiplication has
arithmetic circuits of size `O(n ^ (9/4 + γ))` (`admissibleExponent_nine_quarters`), and so the
exponent of matrix multiplication is at most `9/4` (`omega_le_nine_quarters`). This is
[Pass][Pass2026], Theorem 1.1, the constructive form of the bound `ω ≤ 9/4` of
[OpenAI][OpenAI2026MatrixMultiplication]: the finite identity `Tensor.exists_rank_mm_lt_rpow`,
an exact bilinear algorithm for some `v × v` multiplication with fewer than `v ^ τ`
multiplications, is applied recursively to `v × v` arrays of blocks
(`admissibleExponent_of_rank`).

**Source and model.** [Pass][Pass2026], Theorem 1.1 (p. 1), states the bound for integer
arithmetic operations; here the model is cslib's arithmetic circuits over a field `K` of
characteristic zero with addition, multiplication and constant gates each of cost one, and the
circuits are exact for every pair of matrices (`ComputesMatMul`). The proof follows the paper:
the primal packing (Theorem 3.1), amplification (Lemma 3.2), separation of the left inputs
(Lemma 3.4), the round (Lemma 4.2), the finite identity (Theorem 4.3, Corollary 4.4) and block
recursion (§4.3), with Bini's conversion (Lemma 2.4) removing the formal parameter. The
restriction to characteristic zero comes from the integer interpolation nodes; the paper works
over `ℚ`.

## Main results

* `Cslib.Circuits.Arithmetic.MatrixMultiplication.admissibleExponent_nine_quarters`
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.omega_le_nine_quarters`

## References

* [R. Pass, *Matrix Multiplication from Polynomial Packings: A Constructive and Elementary
  Proof of ω ≤ 9/4*][Pass2026], Theorem 1.1
* [OpenAI, *An Upper Bound of 9/4 for the Matrix Multiplication
  Exponent*][OpenAI2026MatrixMultiplication]
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.MatrixMultiplication

open Cslib.Tensor

variable (K : Type*) [Field K] [CharZero K]

/-- **Matrix multiplication in `O(n ^ (9/4 + γ))` operations** ([Pass][Pass2026], Theorem 1.1):
over a field of characteristic zero, every `τ > 9/4` is an admissible exponent. -/
theorem admissibleExponent_nine_quarters {τ : ℝ} (hτ : 9 / 4 < τ) : AdmissibleExponent K τ := by
  obtain ⟨v, r, hv, hr, hrank⟩ := exists_rank_mm_lt_rpow (K := K) hτ
  exact admissibleExponent_of_rank hv hrank hr.le (by linarith)

/-- **`ω ≤ 9/4`** ([Pass][Pass2026], Theorem 1.1; [OpenAI][OpenAI2026MatrixMultiplication]):
the exponent of matrix multiplication over a field of characteristic zero is at most `9/4`. -/
theorem omega_le_nine_quarters : omega K ≤ 9 / 4 := by
  refine le_of_forall_pos_lt_add fun γ hγ => ?_
  exact (omega_le_of_admissibleExponent
    (admissibleExponent_nine_quarters K (τ := 9 / 4 + γ / 2) (by linarith))).trans_lt
    (by linarith)

end Cslib.Circuits.Arithmetic.MatrixMultiplication
