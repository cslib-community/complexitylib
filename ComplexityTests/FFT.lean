/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Query.Arith.FFT.Correctness
import Complexity.Algorithms.Lean.Query.Arith.FFT.Cost
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The fast Fourier transform

Number-theoretic transforms over `ZMod 17`, where `4` and `2` are principal roots of unity of
orders `4` and `8` (`4 ^ 2 = 2 ^ 4 = -1`): the transform, the inverse transform and FFT
multiplication are evaluated concretely and agree with the DFT and with polynomial
multiplication. The hypotheses of the correctness theorems hold at these parameters, so the
theorems are not vacuous. Over `ZMod 15`, where `4 ^ 2 = 1 ≠ -1`, the program and the DFT
differ, so the hypothesis `ω ^ (2 ^ k) = -1` of `eval_fft` cannot be dropped, and `4` is a root
of unity there that is not principal. Over `ℂ`, `Complex.I` gives an instance of the
primitive-root form of the theorem. The cost formulas are checked against counted queries,
including under a dishonest oracle, and the `7 N log₂ N` bound is applied at a concrete length.
-/

namespace ComplexityTests.FFT

open Cslib Cslib.Query Cslib.Query.FFT ArithQuery Polynomial

/-! ### Number-theoretic transforms over `ZMod 17` -/

/-- `4` has order `4` modulo `17`: `4 ^ 2 = 16 = -1`. -/
example : (4 : ZMod 17) ^ 2 ^ 1 = -1 := by decide

/-- `4` is a principal fourth root of unity modulo `17`. -/
example : IsPrincipalRoot (4 : ZMod 17) (2 ^ (1 + 1)) :=
  IsPrincipalRoot.of_pow_two_pow_eq_neg_one (by decide)

/-- The transform of `1 + 2X` at `1, 4, 16, 13`: `3, 9, 16, 10` modulo `17`. -/
example : (fft 2 (fun j => (4 : ZMod 17) ^ j) ![1, 2, 0, 0]).eval honest = ![3, 9, 16, 10] := by
  decide +kernel

/-- The same values from the definition of the DFT. -/
example : dft (4 : ZMod 17) ![1, 2, 0, 0] = ![3, 9, 16, 10] := by decide +kernel

/-- `eval_fft` applies: its hypotheses hold for `ω = 4` modulo `17`. -/
example (a : Fin (2 ^ (1 + 1)) → ZMod 17) :
    (fft (1 + 1) (fun j => (4 : ZMod 17) ^ j) a).eval honest = dft 4 a :=
  eval_fft (fun _ _ => rfl) (by decide) a

/-- `13 = 4⁻¹` modulo `17`: the inverse transform of `3, 9, 16, 10` recovers `1 + 2X`. -/
example : (ifft 2 (fun j => (4 : ZMod 17) ^ j) 13 ![3, 9, 16, 10]).eval honest = ![1, 2, 0, 0] := by
  decide +kernel

/-- `(1 + 2X)(3 + X) = 3 + 7X + 2X²` by FFT multiplication of length `4`. -/
example : (fftMul 1 (4 : ZMod 17) 13 ![1, 2, 0, 0] ![3, 1, 0, 0]).eval honest = ![3, 7, 2, 0] := by
  decide +kernel

/-- Length `8` with `ω = 2` (`2 ^ 4 = -1`) and `15 = 8⁻¹` modulo `17`:
`(1 + X + X² + X³)² = 1 + 2X + 3X² + 4X³ + 3X⁴ + 2X⁵ + X⁶`. -/
example : (fftMul 2 (2 : ZMod 17) 15 ![1, 1, 1, 1, 0, 0, 0, 0] ![1, 1, 1, 1, 0, 0, 0, 0]).eval
    honest = ![1, 2, 3, 4, 3, 2, 1, 0] := by
  decide +kernel

/-- Cyclic wrap-around: with degree sum `4 ≥ 4`, length-`4` FFT multiplication of
`X²` by `X²` returns `X⁴ mod (X⁴ - 1) = 1`, not the coefficients of `X⁴`. -/
example : (fftMul 1 (4 : ZMod 17) 13 ![0, 0, 1, 0] ![0, 0, 1, 0]).eval honest = ![1, 0, 0, 0] := by
  decide +kernel

/-- `eval_fftMul_coeff` applies to polynomials of degree `1` modulo `17`. -/
example (p q : (ZMod 17)[X]) (hp : p.natDegree ≤ 1) (hq : q.natDegree ≤ 1) :
    (fftMul 1 (4 : ZMod 17) 13 (fun i : Fin (2 ^ (1 + 1)) => p.coeff i)
      (fun i : Fin (2 ^ (1 + 1)) => q.coeff i)).eval honest =
      fun i : Fin (2 ^ (1 + 1)) => (p * q).coeff i :=
  eval_fftMul_coeff (by decide) (by decide) (by norm_num; omega)

/-! ### The hypothesis `ω ^ (2 ^ k) = -1` is needed -/

/-- In `ZMod 15`, `4 ^ 2 = 1`, so `4 ^ 2 ≠ -1`. -/
example : (4 : ZMod 15) ^ 2 ^ 1 ≠ -1 := by decide

/-- With `ω = 4` in `ZMod 15` the transform of length `4` does not compute the DFT. -/
example : (fft 2 (fun j => (4 : ZMod 15) ^ j) ![0, 1, 0, 0]).eval honest ≠
    dft (4 : ZMod 15) ![0, 1, 0, 0] := by
  decide +kernel

/-- `4` is a fourth root of unity in `ZMod 15` that is not principal: `1 + 4 ^ 2 + 4 ^ 4 + 4 ^ 6
= 4 ≠ 0`. -/
example : (4 : ZMod 15) ^ 4 = 1 ∧ ¬IsPrincipalRoot (4 : ZMod 15) 4 := by
  refine ⟨by decide, fun h => ?_⟩
  have := h.geom_sum_eq_zero 2 (by norm_num) (by norm_num)
  revert this
  decide

/-! ### Complex numbers -/

/-- Over `ℂ`, `Complex.I` is a primitive fourth root of unity, so the transform of length `4`
with the table `I ^ j` computes the DFT. -/
example (a : Fin (2 ^ (1 + 1)) → ℂ) :
    (fft (1 + 1) (fun j => Complex.I ^ j) a).eval honest = dft Complex.I a :=
  eval_fft_of_isPrimitiveRoot (fun _ _ => rfl) Complex.isPrimitiveRoot_I a

/-! ### Cost -/

/-- An oracle answering every query with `0`. -/
private def zeroOracle : {ι : Type} → ArithQuery (ZMod 17) ι → ι
  | _, .add _ _ => 0
  | _, .sub _ _ => 0
  | _, .mul _ _ => 0

/-- The transform of length `8` makes `4 · 3 = 12` multiplications and `8 · 3 = 24` additive
operations, so `12 + 24 = 36` queries. -/
example : (fft 3 (fun j => (2 : ZMod 17) ^ j) ![1, 2, 3, 4, 5, 6, 7, 8]).countQueries honest =
    36 := by
  decide +kernel

/-- The dishonest oracle sees the same `36` queries. -/
example : (fft 3 (fun j => (2 : ZMod 17) ^ j) ![1, 2, 3, 4, 5, 6, 7, 8]).countQueries zeroOracle =
    36 := by
  decide +kernel

/-- The general formula at length `8`, weighting multiplications `5` and additions `1`. -/
example (w : ℕ → ZMod 17) (a : Fin (2 ^ 3) → ZMod 17) :
    (fft 3 w a).cost honest (weight 1 5) = 5 * 12 + 24 := by
  rw [cost_fft]
  norm_num

/-- FFT multiplication of length `4`: three transforms (`12` multiplications, `24` additive
operations), `4 + 4` pointwise and scaling multiplications and `1` table multiplication, so
`21 + 24 = 45` queries. -/
example : (fftMul 1 (4 : ZMod 17) 13 ![1, 2, 0, 0] ![3, 1, 0, 0]).countQueries zeroOracle = 45 := by
  decide +kernel

example (o : {ι : Type} → ArithQuery (ZMod 17) ι → ι) (a b : Fin (2 ^ (1 + 1)) → ZMod 17) :
    (fftMul 1 (4 : ZMod 17) 13 a b).countQueries o = 45 := by
  rw [countQueries_fftMul]
  norm_num

/-- The `7 N log₂ N` bound at `N = 8`: at most `168` queries, under every oracle. -/
example (o : {ι : Type} → ArithQuery (ZMod 17) ι → ι) (a b : Fin (2 ^ (2 + 1)) → ZMod 17) :
    (fftMul 2 (2 : ZMod 17) 15 a b).countQueries o ≤ 168 := by
  have h := fftMul_upperBound 2 (2 : ZMod 17) 15 o _ (a, b) le_rfl
  simp only [Nat.log_pow one_lt_two] at h
  exact h.trans (by norm_num)

end ComplexityTests.FFT
