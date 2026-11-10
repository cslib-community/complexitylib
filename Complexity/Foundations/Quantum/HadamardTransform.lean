/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Quantum.Measurement
public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Foundations.Data.BitString.Sign
public import Mathlib.Data.Matrix.Mul
import Complexity.Foundations.BooleanAnalysis.HadamardRectangles

/-!
# The Hadamard transform on a register of qubits

Let the computational basis `ι` of a quantum system split, by an equivalence
`e : ι ≃ (K → Bool) × R`, into a register of qubits indexed by `K` and a remaining part `R`. The
*Hadamard transform* on the register applies a Hadamard gate to each of its qubits:
`|a, r⟩ ↦ 2^{-|K|/2} ∑_z (-1)^{a ⬝ᵥ z} |z, r⟩` (`Cslib.Quantum.hadamardTransform`). It is an
isometry by Parseval's identity for the sign matrix `(-1)^{a ⬝ᵥ z}`
(`Cslib.BitString.sum_sq_sum_mul_signVal_dotProduct`).

The Hadamard transform is the Fourier transform of the group `(K → Bool, +)`: it is the first and
last step of the algorithms of Bernstein–Vazirani and Simon
(`Complexity/Computability/QueryComplexity/Quantum/BernsteinVazirani.lean`,
`Complexity/Computability/QueryComplexity/Quantum/Simon.lean`), [de Wolf][deWolf2019], Chapters 2
and 3.

## Main definitions

* `Cslib.Quantum.hadamardTransform`: the Hadamard transform on a register of qubits.

## Main results

* `Cslib.Quantum.hadamardTransform_apply`: its amplitudes.
* `Cslib.Quantum.hadamardTransform_ket`: its action on a basis state.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Finset BitString

variable {K ι R : Type*} [Fintype K] [DecidableEq K] [Fintype ι] [Fintype R]

/-- Parseval's identity for complex weights. -/
private theorem sum_norm_sq_sum_mul_signVal_dotProduct (f : (K → Bool) → ℂ) :
    ∑ z : K → Bool, ‖∑ a, ((signVal (a ⬝ᵥ z) : ℝ) : ℂ) * f a‖ ^ 2 =
      2 ^ Fintype.card K * ∑ a, ‖f a‖ ^ 2 := by
  have hre := sum_sq_sum_mul_signVal_dotProduct (fun a => (f a).re)
  have him := sum_sq_sum_mul_signVal_dotProduct (fun a => (f a).im)
  have hnorm : ∀ c : ℂ, ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := fun c => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [hnorm, Complex.re_sum, Complex.im_sum, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    sum_add_distrib, mul_add]
  rw [← hre, ← him]
  congr 1 <;> refine sum_congr rfl fun z _ => ?_ <;> congr 1 <;>
    exact sum_congr rfl fun a _ => mul_comm _ _

/-- The **Hadamard transform** on the register `K → Bool` of a basis `ι ≃ (K → Bool) × R`: a
Hadamard gate on each qubit of the register,
`|a, r⟩ ↦ 2^{-|K|/2} ∑_z (-1)^{a ⬝ᵥ z} |z, r⟩`. -/
noncomputable def hadamardTransform (e : ι ≃ (K → Bool) × R) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toFun ψ := WithLp.toLp 2 fun p => (((Real.sqrt (2 ^ Fintype.card K))⁻¹ : ℝ) : ℂ) *
    ∑ a : K → Bool, ((signVal (a ⬝ᵥ (e p).1) : ℝ) : ℂ) * ψ.ofLp (e.symm (a, (e p).2))
  map_add' ψ φ := by
    ext p
    simp only [PiLp.add_apply, mul_add, sum_add_distrib]
  map_smul' c ψ := by
    ext p
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun a _ => by ring
  norm_map' ψ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← e.symm.sum_comp, ← e.symm.sum_comp, Fintype.sum_prod_type_right,
      Fintype.sum_prod_type_right]
    refine sum_congr rfl fun r _ => ?_
    simp only [Equiv.apply_symm_apply, norm_mul, mul_pow, ← mul_sum]
    rw [sum_norm_sq_sum_mul_signVal_dotProduct (fun a => ψ.ofLp (e.symm (a, r))),
      Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by positivity),
      ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

theorem hadamardTransform_apply (e : ι ≃ (K → Bool) × R) (ψ : EuclideanSpace ℂ ι) (p : ι) :
    (hadamardTransform e ψ).ofLp p = (((Real.sqrt (2 ^ Fintype.card K))⁻¹ : ℝ) : ℂ) *
      ∑ a : K → Bool, ((signVal (a ⬝ᵥ (e p).1) : ℝ) : ℂ) * ψ.ofLp (e.symm (a, (e p).2)) := by
  rfl

/-- **The Hadamard transform of a basis state** `|a, r⟩` has amplitude
`2^{-|K|/2} (-1)^{a ⬝ᵥ z}` at `|z, r⟩` and `0` elsewhere. -/
theorem hadamardTransform_ket [DecidableEq ι] [DecidableEq R] (e : ι ≃ (K → Bool) × R)
    (q p : ι) :
    (hadamardTransform e (ket q)).ofLp p = if (e q).2 = (e p).2 then
      (((Real.sqrt (2 ^ Fintype.card K))⁻¹ : ℝ) : ℂ) *
        ((signVal ((e q).1 ⬝ᵥ (e p).1) : ℝ) : ℂ) else 0 := by
  rw [hadamardTransform_apply]
  simp only [ket_apply, e.symm_apply_eq, Prod.ext_iff, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [sum_eq_single (e q).1 (fun a _ ha => by simp [ha]) (by simp)]
    simp [h]
  · rw [sum_eq_zero fun a _ => by simp [Ne.symm h], mul_zero]

end Cslib.Quantum
