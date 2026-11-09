/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Quantum.Bell
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Density matrices and the partial trace

A **density matrix** on `ℂ^ι` is a positive semidefinite matrix of trace one
(`Cslib.Quantum.IsDensityMatrix`), the general (mixed) state of a quantum system; a unit vector
`ψ` gives the pure state `|ψ⟩⟨ψ|` (`Cslib.Quantum.pureState`) ([de Wolf][deWolf2019], §15.1).
For a bipartite system `ℂ^{ι × κ}`, the **partial trace** over the first system
(`Cslib.Quantum.partialTraceLeft`) gives the reduced state of the second,
`(Tr_A ρ)_{k k'} = ∑ᵢ ρ_{(i, k), (i, k')}`, and symmetrically `Cslib.Quantum.partialTraceRight`
gives the reduced state of the first ([de Wolf][deWolf2019], §18.3, where `Tr_B` is defined on
product matrices by `Tr_B (C ⊗ D) = C · Tr D` and extended linearly).

The partial trace preserves the trace and positive semidefiniteness, so it maps density matrices
to density matrices; on a Kronecker product it is `Tr_A (A ⊗ₖ B) = tr A • B`. An operator `A` on
the traced-out system can be moved cyclically under `Tr_A`, which gives **no-signalling**
(`Cslib.Quantum.partialTraceLeft_kraus`): whatever Alice does to her system, as a Kraus family
`{Kⱼ}` with `∑ⱼ Kⱼᴴ Kⱼ = 1` (a unitary, a measurement whose outcome is discarded, ...), Bob's
reduced state is unchanged. This generalizes [de Wolf][deWolf2019], Chapter 18, Exercise 7
("Alice cannot give information to Bob by doing a unitary operation on her part of an entangled
pure state") from unitaries on pure states to Kraus families on mixed states.

## Main definitions

* `Cslib.Quantum.IsDensityMatrix`: positive semidefinite with trace one.
* `Cslib.Quantum.pureState`: the projector `|ψ⟩⟨ψ|`.
* `Cslib.Quantum.partialTraceLeft`, `Cslib.Quantum.partialTraceRight`: the partial traces over
  the first and the second system.

## Main results

* `Cslib.Quantum.isDensityMatrix_pureState`: `|ψ⟩⟨ψ|` is a density matrix for a unit vector `ψ`.
* `Cslib.Quantum.IsDensityMatrix.conj_unitary`: unitary evolution `UρUᴴ` preserves density
  matrices.
* `Cslib.Quantum.IsDensityMatrix.partialTraceLeft`,
  `Cslib.Quantum.IsDensityMatrix.partialTraceRight`: reduced states are density matrices.
* `Cslib.Quantum.partialTraceLeft_kronecker`, `Cslib.Quantum.partialTraceRight_kronecker`: the
  partial traces of a Kronecker product.
* `Cslib.Quantum.partialTraceLeft_pureState_maxEntangled`,
  `Cslib.Quantum.partialTraceRight_pureState_maxEntangled`: either half of the maximally entangled
  state is maximally mixed.
* `Cslib.Quantum.partialTraceLeft_kraus`: no-signalling for a Kraus family on the first system,
  with the special cases `Cslib.Quantum.partialTraceLeft_conj_unitary` (a unitary) and
  `Cslib.Quantum.partialTraceLeft_measure` (a computational-basis measurement whose outcome is
  discarded).

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker ComplexOrder

variable {ι κ : Type*}

/-! ### Density matrices -/

/-- A **density matrix**: positive semidefinite with trace one. -/
structure IsDensityMatrix [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop where
  /-- A density matrix is positive semidefinite. -/
  posSemidef : ρ.PosSemidef
  /-- A density matrix has trace one. -/
  trace_eq_one : ρ.trace = 1

/-- The **pure state** `|ψ⟩⟨ψ|`, with entries `ψᵢ conj ψⱼ`. -/
noncomputable def pureState (ψ : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  vecMulVec ψ.ofLp (star ψ.ofLp)

@[simp] theorem pureState_apply (ψ : EuclideanSpace ℂ ι) (i j : ι) :
    pureState ψ i j = ψ.ofLp i * star (ψ.ofLp j) := by
  rfl

theorem posSemidef_pureState [Finite ι] (ψ : EuclideanSpace ℂ ι) : (pureState ψ).PosSemidef :=
  posSemidef_vecMulVec_self_star _

theorem trace_pureState [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    (pureState ψ).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq, trace]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [diag_apply, pureState_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `|ψ⟩⟨ψ|` is a density matrix for a unit vector `ψ`. -/
theorem isDensityMatrix_pureState [Fintype ι] {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    IsDensityMatrix (pureState ψ) :=
  ⟨posSemidef_pureState ψ, by rw [trace_pureState, hψ]; norm_num⟩

/-- **Unitary evolution** `ρ ↦ U ρ Uᴴ` preserves density matrices. -/
theorem IsDensityMatrix.conj_unitary [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) {U : Matrix ι ι ℂ} (hU : U ∈ unitaryGroup ι ℂ) :
    IsDensityMatrix (U * ρ * Uᴴ) := by
  refine ⟨hρ.posSemidef.mul_mul_conjTranspose_same U, ?_⟩
  rw [trace_mul_cycle, ← star_eq_conjTranspose, (mem_unitaryGroup_iff'.mp hU), one_mul,
    hρ.trace_eq_one]

/-! ### The partial trace -/

variable {R : Type*}

/-- The **partial trace over the first system**: the reduced state `Tr_A ρ` of the second system,
`(Tr_A ρ)_{k k'} = ∑ᵢ ρ_{(i, k), (i, k')}`. -/
def partialTraceLeft [Fintype ι] [AddCommMonoid R] (ρ : Matrix (ι × κ) (ι × κ) R) :
    Matrix κ κ R :=
  fun k k' => ∑ i, ρ (i, k) (i, k')

/-- The **partial trace over the second system**: the reduced state `Tr_B ρ` of the first system,
`(Tr_B ρ)_{i i'} = ∑ₖ ρ_{(i, k), (i', k)}`. -/
def partialTraceRight [Fintype κ] [AddCommMonoid R] (ρ : Matrix (ι × κ) (ι × κ) R) :
    Matrix ι ι R :=
  fun i i' => ∑ k, ρ (i, k) (i', k)

@[simp] theorem partialTraceLeft_apply [Fintype ι] [AddCommMonoid R]
    (ρ : Matrix (ι × κ) (ι × κ) R) (k k' : κ) :
    partialTraceLeft ρ k k' = ∑ i, ρ (i, k) (i, k') := by
  rfl

@[simp] theorem partialTraceRight_apply [Fintype κ] [AddCommMonoid R]
    (ρ : Matrix (ι × κ) (ι × κ) R) (i i' : ι) :
    partialTraceRight ρ i i' = ∑ k, ρ (i, k) (i', k) := by
  rfl

theorem partialTraceLeft_add [Fintype ι] [AddCommMonoid R] (ρ σ : Matrix (ι × κ) (ι × κ) R) :
    partialTraceLeft (ρ + σ) = partialTraceLeft ρ + partialTraceLeft σ := by
  ext k k'; simp [sum_add_distrib]

theorem partialTraceLeft_sum [Fintype ι] [AddCommMonoid R] {α : Type*} (s : Finset α)
    (ρ : α → Matrix (ι × κ) (ι × κ) R) :
    partialTraceLeft (∑ a ∈ s, ρ a) = ∑ a ∈ s, partialTraceLeft (ρ a) := by
  ext k k'; simp only [partialTraceLeft_apply, Matrix.sum_apply]; exact sum_comm

theorem partialTraceLeft_smul [Fintype ι] [Semiring R] (c : R) (ρ : Matrix (ι × κ) (ι × κ) R) :
    partialTraceLeft (c • ρ) = c • partialTraceLeft ρ := by
  ext k k'; simp [mul_sum]

theorem partialTraceRight_add [Fintype κ] [AddCommMonoid R] (ρ σ : Matrix (ι × κ) (ι × κ) R) :
    partialTraceRight (ρ + σ) = partialTraceRight ρ + partialTraceRight σ := by
  ext i i'; simp [sum_add_distrib]

theorem partialTraceRight_sum [Fintype κ] [AddCommMonoid R] {α : Type*} (s : Finset α)
    (ρ : α → Matrix (ι × κ) (ι × κ) R) :
    partialTraceRight (∑ a ∈ s, ρ a) = ∑ a ∈ s, partialTraceRight (ρ a) := by
  ext i i'; simp only [partialTraceRight_apply, Matrix.sum_apply]; exact sum_comm

theorem partialTraceRight_smul [Fintype κ] [Semiring R] (c : R) (ρ : Matrix (ι × κ) (ι × κ) R) :
    partialTraceRight (c • ρ) = c • partialTraceRight ρ := by
  ext i i'; simp [mul_sum]

/-- The partial trace over the first system preserves the trace. -/
theorem trace_partialTraceLeft [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (ρ : Matrix (ι × κ) (ι × κ) R) : (partialTraceLeft ρ).trace = ρ.trace := by
  simp only [trace, diag_apply, partialTraceLeft_apply, Fintype.sum_prod_type]
  exact sum_comm

/-- The partial trace over the second system preserves the trace. -/
theorem trace_partialTraceRight [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (ρ : Matrix (ι × κ) (ι × κ) R) : (partialTraceRight ρ).trace = ρ.trace := by
  simp only [trace, diag_apply, partialTraceRight_apply, Fintype.sum_prod_type]

/-- `Tr_A (A ⊗ₖ B) = tr A • B`. -/
theorem partialTraceLeft_kronecker [Fintype ι] [CommSemiring R] (A : Matrix ι ι R)
    (B : Matrix κ κ R) : partialTraceLeft (A ⊗ₖ B) = A.trace • B := by
  ext k k'; simp [trace, sum_mul]

/-- `Tr_B (A ⊗ₖ B) = tr B • A`. -/
theorem partialTraceRight_kronecker [Fintype κ] [CommSemiring R] (A : Matrix ι ι R)
    (B : Matrix κ κ R) : partialTraceRight (A ⊗ₖ B) = B.trace • A := by
  ext i i'; simp [trace, mul_sum, mul_comm]

/-- The partial trace over the first system is a sum of compressions `ρ ↦ ρ_{(i, ·), (i, ·)}`. -/
theorem partialTraceLeft_eq_sum_submatrix [Fintype ι] [AddCommMonoid R]
    (ρ : Matrix (ι × κ) (ι × κ) R) :
    partialTraceLeft ρ = ∑ i, ρ.submatrix (fun k => (i, k)) (fun k => (i, k)) := by
  ext k k'; simp [Matrix.sum_apply]

theorem partialTraceRight_eq_sum_submatrix [Fintype κ] [AddCommMonoid R]
    (ρ : Matrix (ι × κ) (ι × κ) R) :
    partialTraceRight ρ = ∑ k, ρ.submatrix (fun i => (i, k)) (fun i => (i, k)) := by
  ext i i'; simp [Matrix.sum_apply]

/-- The partial trace over the first system preserves positive semidefiniteness. -/
theorem posSemidef_partialTraceLeft [Fintype ι] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : ρ.PosSemidef) : (partialTraceLeft ρ).PosSemidef := by
  rw [partialTraceLeft_eq_sum_submatrix]
  exact posSemidef_sum _ fun i _ => hρ.submatrix _

/-- The partial trace over the second system preserves positive semidefiniteness. -/
theorem posSemidef_partialTraceRight [Fintype κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : ρ.PosSemidef) : (partialTraceRight ρ).PosSemidef := by
  rw [partialTraceRight_eq_sum_submatrix]
  exact posSemidef_sum _ fun k _ => hρ.submatrix _

/-- The reduced state `Tr_A ρ` of a density matrix is a density matrix. -/
theorem IsDensityMatrix.partialTraceLeft [Fintype ι] [Fintype κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (partialTraceLeft ρ) :=
  ⟨posSemidef_partialTraceLeft hρ.posSemidef, by rw [trace_partialTraceLeft, hρ.trace_eq_one]⟩

/-- The reduced state `Tr_B ρ` of a density matrix is a density matrix. -/
theorem IsDensityMatrix.partialTraceRight [Fintype ι] [Fintype κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (partialTraceRight ρ) :=
  ⟨posSemidef_partialTraceRight hρ.posSemidef, by rw [trace_partialTraceRight, hρ.trace_eq_one]⟩

private theorem inv_sqrt_card_mul_inv_sqrt_card (ι : Type*) [Fintype ι] :
    ((Real.sqrt (Fintype.card ι) : ℂ))⁻¹ * ((Real.sqrt (Fintype.card ι) : ℂ))⁻¹ =
      (Fintype.card ι : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast; rfl

/-- The reduced state of either half of the maximally entangled state is maximally mixed:
`Tr_A |Φ⟩⟨Φ| = 1 / |ι|` ([de Wolf][deWolf2019], §18.3, for the EPR pair). -/
theorem partialTraceLeft_pureState_maxEntangled [Fintype ι] [DecidableEq ι] :
    partialTraceLeft (pureState (maxEntangled ι)) =
      (Fintype.card ι : ℂ)⁻¹ • (1 : Matrix ι ι ℂ) := by
  ext k k'
  simp only [partialTraceLeft_apply, pureState_apply, maxEntangled_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h : k = k'
  · subst h
    rw [sum_eq_single k (fun i _ hi => by simp [hi]) (by simp)]
    simp [inv_sqrt_card_mul_inv_sqrt_card]
  · rw [ite_eq_right_iff.mpr fun h' => absurd h' h]
    exact sum_eq_zero fun i _ => by
      by_cases hi : i = k
      · subst hi; simp [h]
      · simp [hi]

/-- `Tr_B |Φ⟩⟨Φ| = 1 / |ι|` for the maximally entangled state. -/
theorem partialTraceRight_pureState_maxEntangled [Fintype ι] [DecidableEq ι] :
    partialTraceRight (pureState (maxEntangled ι)) =
      (Fintype.card ι : ℂ)⁻¹ • (1 : Matrix ι ι ℂ) := by
  rw [← partialTraceLeft_pureState_maxEntangled]
  ext i i'
  simp only [partialTraceRight_apply, partialTraceLeft_apply, pureState_apply, maxEntangled_apply]
  refine sum_congr rfl fun k _ => ?_
  by_cases h : i = k <;> by_cases h' : i' = k <;> simp [h, h', eq_comm]

/-! ### No-signalling -/

/-- An operator `A` on the traced-out first system moves cyclically under `Tr_A`:
`Tr_A ((A ⊗ₖ 1) ρ) = Tr_A (ρ (A ⊗ₖ 1))`. -/
theorem partialTraceLeft_kronecker_one_mul [Fintype ι] [Fintype κ] [DecidableEq κ] [CommSemiring R]
    (A : Matrix ι ι R) (ρ : Matrix (ι × κ) (ι × κ) R) :
    partialTraceLeft ((A ⊗ₖ (1 : Matrix κ κ R)) * ρ) =
      partialTraceLeft (ρ * (A ⊗ₖ (1 : Matrix κ κ R))) := by
  ext k k'
  simp only [partialTraceLeft_apply, Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, sum_ite_eq',
    mem_univ, ite_true]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_comm _ _

/-- **No-signalling** for a Kraus family on the first system: if Alice applies the operation
`ρ ↦ ∑ⱼ (Kⱼ ⊗ 1) ρ (Kⱼ ⊗ 1)ᴴ` with `∑ⱼ Kⱼᴴ Kⱼ = 1`, Bob's reduced state `Tr_A ρ` is unchanged.
This generalizes [de Wolf][deWolf2019], Chapter 18, Exercise 7, from a unitary on a pure state to
a Kraus family on a mixed state. -/
theorem partialTraceLeft_kraus [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {α : Type*} (s : Finset α) (K : α → Matrix ι ι ℂ) (hK : ∑ j ∈ s, (K j)ᴴ * K j = 1)
    (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceLeft (∑ j ∈ s, (K j ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * (K j ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) =
      partialTraceLeft ρ := by
  have h (j : α) : partialTraceLeft ((K j ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ *
      (K j ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) =
      partialTraceLeft (ρ * (((K j)ᴴ * K j) ⊗ₖ (1 : Matrix κ κ ℂ))) := by
    rw [Matrix.mul_assoc, partialTraceLeft_kronecker_one_mul, conjTranspose_kronecker,
      conjTranspose_one, Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul]
  have hsum : ∑ j ∈ s, ((K j)ᴴ * K j) ⊗ₖ (1 : Matrix κ κ ℂ) = 1 := calc
    _ = (∑ j ∈ s, (K j)ᴴ * K j) ⊗ₖ (1 : Matrix κ κ ℂ) := by
      ext p q; simp only [Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul]
    _ = 1 := by rw [hK, one_kronecker_one]
  rw [partialTraceLeft_sum, sum_congr rfl fun j _ => h j, ← partialTraceLeft_sum, ← Finset.mul_sum,
    hsum, Matrix.mul_one]

/-- **No-signalling for a local unitary** ([de Wolf][deWolf2019], Chapter 18, Exercise 7, for
mixed states): a unitary `U` applied by Alice leaves Bob's reduced state unchanged. -/
theorem partialTraceLeft_conj_unitary [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {U : Matrix ι ι ℂ} (hU : U ∈ unitaryGroup ι ℂ) (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceLeft ((U ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * (U ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) =
      partialTraceLeft ρ := by
  have h := partialTraceLeft_kraus {()} (fun _ => U)
    (by rw [sum_singleton, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp hU]) ρ
  rwa [sum_singleton] at h

/-- **No-signalling for a measurement**: if Alice measures her system in the computational basis
and the outcome is discarded, `ρ ↦ ∑ᵢ (|i⟩⟨i| ⊗ 1) ρ (|i⟩⟨i| ⊗ 1)`, Bob's reduced state is
unchanged. -/
theorem partialTraceLeft_measure [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceLeft (∑ i, (single i i (1 : ℂ) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ *
      (single i i (1 : ℂ) ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) = partialTraceLeft ρ := by
  refine partialTraceLeft_kraus univ (fun i => single i i (1 : ℂ)) ?_ ρ
  simp only [conjTranspose_single, star_one, single_mul_single_same, mul_one, sum_single_one]

end Cslib.Quantum
