/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Quantum.Measurement
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Maximally entangled states and the Bell state

The **maximally entangled state** `|Φ_ι⟩ = |ι|^{-1/2} ∑_i |i, i⟩` of two copies of a system with
computational basis `ι` (`Cslib.Quantum.maxEntangled`), and its two-qubit instance, the **Bell
state** (EPR pair) `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` (`Cslib.Quantum.bell`), [de Wolf][deWolf2019],
Section 1.3. Local operators `A` and `B` on the two halves have correlation
`⟨Φ| A ⊗ B |Φ⟩ = Tr(Aᵀ B)/|ι|`
(`Cslib.Quantum.star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace`); for `B = 1` this is
[de Wolf][deWolf2019], Chapter 1, Exercise 15(a).

The Bell state is the shared resource of teleportation and superdense coding
(`Complexity/Computability/Circuit/Quantum/Teleportation.lean`,
`Complexity/Computability/Circuit/Quantum/SuperdenseCoding.lean`).

## Main definitions

* `Cslib.Quantum.maxEntangled`: the maximally entangled state `|Φ_ι⟩`.
* `Cslib.Quantum.bell`: the Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`.

## Main results

* `Cslib.Quantum.norm_maxEntangled`, `Cslib.Quantum.norm_bell`: they are unit vectors.
* `Cslib.Quantum.star_maxEntangled_dotProduct_kronecker_mulVec`:
  `⟨Φ| A ⊗ B |Φ⟩ = (∑_{i,j} A_{ij} B_{ij})/|ι|`.
* `Cslib.Quantum.star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace`: the same as
  `Tr(Aᵀ B)/|ι|`.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The **maximally entangled state** `|Φ_ι⟩ = |ι|^{-1/2} ∑_i |i, i⟩` of two copies of a system
with computational basis `ι`. -/
noncomputable def maxEntangled : EuclideanSpace ℂ (ι × ι) :=
  (((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) : ℂ) • ∑ i, ket (i, i)

variable {ι}

theorem maxEntangled_apply (p : ι × ι) :
    (maxEntangled ι).ofLp p =
      if p.1 = p.2 then (((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) : ℂ) else 0 := by
  obtain ⟨a, b⟩ := p
  simp only [maxEntangled, WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply, Finset.sum_apply,
    ket_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

@[simp] theorem maxEntangled_apply_self (i : ι) :
    (maxEntangled ι).ofLp (i, i) = (((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) : ℂ) := by
  simp [maxEntangled_apply]

theorem maxEntangled_apply_of_ne {i j : ι} (h : i ≠ j) : (maxEntangled ι).ofLp (i, j) = 0 := by
  simp [maxEntangled_apply, h]

/-- The maximally entangled state is a unit vector. -/
theorem norm_maxEntangled [Nonempty ι] : ‖maxEntangled ι‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type]
  have hc : ‖(((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) : ℂ)‖ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hsum (x : ι) : ∑ y, ‖(maxEntangled ι).ofLp (x, y)‖ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [Finset.sum_eq_single x (fun y _ hy => by rw [maxEntangled_apply_of_ne (Ne.symm hy),
      norm_zero, sq, zero_mul]) (by simp), maxEntangled_apply_self, hc]
  simp only [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/-- The correlation of local operators on the maximally entangled state:
`⟨Φ| A ⊗ B |Φ⟩ = (∑_{i,j} A_{ij} B_{ij}) / |ι|`. -/
theorem star_maxEntangled_dotProduct_kronecker_mulVec (A B : Matrix ι ι ℂ) :
    star (maxEntangled ι).ofLp ⬝ᵥ ((A ⊗ₖ B) *ᵥ (maxEntangled ι).ofLp) =
      (∑ i, ∑ j, A i j * B i j) / Fintype.card ι := by
  set c : ℂ := (((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) : ℂ) with hc_def
  have hc : star c * c = (Fintype.card ι : ℂ)⁻¹ := by
    rw [hc_def, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast
    rfl
  have hmv (p : ι × ι) :
      ((A ⊗ₖ B) *ᵥ (maxEntangled ι).ofLp) p = c * ∑ j, A p.1 j * B p.2 j := by
    rw [mulVec, dotProduct, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [maxEntangled_apply_of_ne (Ne.symm hk),
      mul_zero]) (by simp), maxEntangled_apply_self, kroneckerMap_apply]
    ring
  rw [dotProduct, Fintype.sum_prod_type, div_eq_mul_inv, ← hc, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.star_apply,
      maxEntangled_apply_of_ne (Ne.symm hk), star_zero, zero_mul]) (by simp),
    Pi.star_apply, maxEntangled_apply_self, hmv, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The correlation of local operators on the maximally entangled state as a trace:
`⟨Φ| A ⊗ B |Φ⟩ = Tr(Aᵀ B) / |ι|`. -/
theorem star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace (A B : Matrix ι ι ℂ) :
    star (maxEntangled ι).ofLp ⬝ᵥ ((A ⊗ₖ B) *ᵥ (maxEntangled ι).ofLp) =
      (Aᵀ * B).trace / Fintype.card ι := by
  rw [star_maxEntangled_dotProduct_kronecker_mulVec, Matrix.trace, Finset.sum_comm]
  simp [Matrix.mul_apply]

/-- The **Bell state** (EPR pair) `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, the maximally entangled state of
two qubits. -/
noncomputable def bell : EuclideanSpace ℂ (Bool × Bool) := maxEntangled Bool

theorem bell_eq_maxEntangled : bell = maxEntangled Bool := by
  rfl

theorem bell_apply (b c : Bool) :
    bell.ofLp (b, c) = if b = c then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0 := by
  rw [bell, maxEntangled_apply]
  simp

@[simp] theorem norm_bell : ‖bell‖ = 1 := norm_maxEntangled

end Cslib.Quantum
