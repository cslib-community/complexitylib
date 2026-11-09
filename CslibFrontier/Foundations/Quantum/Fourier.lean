/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The quantum Fourier transform over `ZMod N`

The quantum Fourier transform over the cyclic group `ZMod N` is the unitary matrix
`F_N(j, k) = ω^{jk} / √N` with `ω = e^{2πi/N}` (`Cslib.Quantum.qft`), acting on a register whose
computational basis is `ZMod N`. Its entries are `ZMod.stdAddChar (j * k) / √N`, and its
unitarity is the orthogonality of the characters of `ZMod N` (`AddChar.sum_mulShift`). As a map on
amplitude vectors it is `√N` times Mathlib's inverse discrete Fourier transform `ZMod.dft.symm`
(`𝓕⁻`), whose sign convention it shares; it is the transform `A_q` of [Shor][Shor1997], §4,
eq. (4.1), with `q = N`, and `F_N` of [de Wolf][deWolf2019], §4.1 and §4.4. For `N = 2` it is the
Hadamard gate.

This module gives the transform as a matrix; it does not give a circuit for it. The
polynomial-size circuit for `N = 2^n` ([de Wolf][deWolf2019], §4.5) is not formalized.

## Main definitions

* `Cslib.Quantum.qft`: the quantum Fourier transform over `ZMod N`, as a unitary matrix.

## Main results

* `Cslib.Quantum.qft_apply`: its entries `stdAddChar (j * k) / √N`.
* `Cslib.Quantum.qft_apply_eq_exp`: its entries `exp(2πi · j k / N) / √N`.
* `Cslib.Quantum.qft_mulVec`: it acts on amplitude vectors as `√N • 𝓕⁻`.
* `Cslib.Quantum.sqrt_inv_mul_sqrt_inv`: the normalization identity `(√N)⁻¹ (√N)⁻¹ = N⁻¹`.

## References

* [P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a
  quantum computer*][Shor1997]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Finset ZMod

variable {N : ℕ} [NeZero N]

/-- `(√N)⁻¹ · (√N)⁻¹ = N⁻¹` in `ℂ`: the squared normalization of a uniform superposition over `N`
basis states. -/
theorem sqrt_inv_mul_sqrt_inv (N : ℕ) :
    (((Real.sqrt N)⁻¹ : ℝ) : ℂ) * (((Real.sqrt N)⁻¹ : ℝ) : ℂ) = (N : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  push_cast
  rfl

/-- The matrix `F_N(j, k) = stdAddChar (j * k) / √N`. -/
private noncomputable def qftMatrix (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun j k => ((Real.sqrt N)⁻¹ : ℝ) * stdAddChar (j * k)

/-- Unitarity of `F_N`: the rows are orthonormal by orthogonality of the characters of `ZMod N`. -/
private theorem qftMatrix_mul_star : qftMatrix N * star (qftMatrix N) = 1 := by
  ext j k
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h : ∀ l : ZMod N, qftMatrix N j l * star (qftMatrix N) l k =
      (N : ℂ)⁻¹ * stdAddChar (l * (j - k)) := by
    intro l
    simp only [star_apply, qftMatrix, of_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [← AddChar.map_neg_eq_conj, ← sqrt_inv_mul_sqrt_inv]
    have : stdAddChar (j * l) * stdAddChar (-(k * l)) = stdAddChar (N := N) (l * (j - k)) := by
      rw [← AddChar.map_add_eq_mul]; ring_nf
    rw [← this]; ring
  rw [Matrix.mul_apply, Matrix.one_apply, sum_congr rfl fun l _ => h l, ← mul_sum,
    AddChar.sum_mulShift _ (isPrimitive_stdAddChar N), ZMod.card]
  by_cases hjk : j = k
  · simp [hjk, hN]
  · simp [hjk, sub_eq_zero]

/-- The **quantum Fourier transform** over `ZMod N`: the unitary matrix with entries
`F_N(j, k) = ω^{jk} / √N`, `ω = e^{2πi/N}` ([Shor][Shor1997], §4, eq. (4.1);
[de Wolf][deWolf2019], §4.1). -/
noncomputable def qft (N : ℕ) [NeZero N] : unitaryGroup (ZMod N) ℂ :=
  ⟨qftMatrix N, mem_unitaryGroup_iff.mpr qftMatrix_mul_star⟩

theorem qft_apply (j k : ZMod N) :
    (qft N : Matrix (ZMod N) (ZMod N) ℂ) j k = ((Real.sqrt N)⁻¹ : ℝ) * stdAddChar (j * k) := by
  rfl

open scoped Real in
/-- The entries of the quantum Fourier transform are `exp(2πi · j k / N) / √N`, computed from the
canonical representatives `j.val, k.val ∈ [0, N)`. -/
theorem qft_apply_eq_exp (j k : ZMod N) :
    (qft N : Matrix (ZMod N) (ZMod N) ℂ) j k =
      Complex.exp (2 * π * Complex.I * j.val * k.val / N) / Real.sqrt N := by
  have hjk : j * k = ((j.val * k.val : ℕ) : ZMod N) := by
    rw [Nat.cast_mul, natCast_zmod_val, natCast_zmod_val]
  rw [qft_apply, stdAddChar_apply, hjk, toCircle_natCast]
  push_cast
  rw [mul_comm, div_eq_mul_inv]
  congr 2
  ring

/-- The quantum Fourier transform acts on amplitude vectors as `√N` times Mathlib's inverse
discrete Fourier transform `𝓕⁻ = ZMod.dft.symm`. -/
theorem qft_mulVec (v : ZMod N → ℂ) :
    (qft N : Matrix (ZMod N) (ZMod N) ℂ) *ᵥ v = (Real.sqrt N : ℂ) • 𝓕⁻ v := by
  ext k
  rw [Pi.smul_apply, invDFT_apply, mulVec, dotProduct, smul_smul, smul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [qft_apply, smul_eq_mul, mul_comm k j]
  have hs : (Real.sqrt N : ℂ) * (((Real.sqrt N)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀
      (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))).ne',
      Complex.ofReal_one]
  have : (Real.sqrt N : ℂ) * (N : ℂ)⁻¹ = (((Real.sqrt N)⁻¹ : ℝ) : ℂ) := by
    rw [← sqrt_inv_mul_sqrt_inv, ← mul_assoc, hs, one_mul]
  rw [this]; ring

end Cslib.Quantum
