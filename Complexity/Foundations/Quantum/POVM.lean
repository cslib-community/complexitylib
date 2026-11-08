/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Quantum.Measurement
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Positive-operator-valued measurements

A *POVM* with outcomes `A` on a finite-dimensional system with basis `ι` is a family of positive
semidefinite matrices `E_a` summing to the identity (`Cslib.Quantum.POVM`). Measuring a unit state
`ψ` gives outcome `a` with probability `⟨ψ|E_a|ψ⟩` (`Cslib.Quantum.POVM.prob`,
`Cslib.Quantum.POVM.measure`) [Cleve, Høyer, Toner, Watrous, §2][CleveHoyerTonerWatrous2004]. The
computational-basis measurement `Cslib.Quantum.measure` is the POVM of the rank-one projections
`|x⟩⟨x|` (`Cslib.Quantum.POVM.measure_basis`).

Two parties measuring the halves of a bipartite state `ψ ∈ ℂ^ι ⊗ ℂ^κ` with POVMs `M` and `N`
jointly perform the Kronecker product POVM `E_a ⊗ F_b` (`Cslib.Quantum.POVM.kronecker`).

A *`±1` observable* is a Hermitian matrix `O` with `O² = 1`. It is the projective measurement with
outcome `false` on the `+1` eigenspace and `true` on the `-1` eigenspace, with effects `(1 ± O)/2`
(`Cslib.Quantum.POVM.ofObservable`), the convention `0 ↦ +1`, `1 ↦ -1` of
[Cleve, Høyer, Toner, Watrous, §3][CleveHoyerTonerWatrous2004]. Conversely, every two-outcome POVM
`M` has the observable `E_false - E_true` (`Cslib.Quantum.POVM.observable`), which is a contraction
even when `M` is not projective (`Cslib.Quantum.POVM.posSemidef_one_sub_observable_mul_self`).

## Main definitions

* `Cslib.Quantum.POVM`: a positive-operator-valued measurement.
* `Cslib.Quantum.POVM.prob`, `Cslib.Quantum.POVM.measure`: outcome probabilities and distribution.
* `Cslib.Quantum.POVM.basis`: the computational-basis measurement.
* `Cslib.Quantum.POVM.kronecker`: the product of two POVMs on a bipartite system.
* `Cslib.Quantum.POVM.const`: the trivial measurement with a fixed outcome.
* `Cslib.Quantum.POVM.reindex`: relabelling the basis of the system.
* `Cslib.Quantum.POVM.ofObservable`: the projective measurement of a `±1` observable.
* `Cslib.Quantum.POVM.observable`: the observable `E_false - E_true` of a two-outcome POVM.

## Main results

* `Cslib.Quantum.POVM.sum_prob`: the outcome probabilities sum to `‖ψ‖²`.
* `Cslib.Quantum.POVM.measure_basis`: the basis POVM is the computational-basis measurement.
* `Cslib.Quantum.POVM.observable_ofObservable`: `ofObservable` and `observable` are inverse on
  `±1` observables.
* `Cslib.Quantum.POVM.posSemidef_one_sub_observable_mul_self`: `O² ≤ 1` for the observable `O` of
  any two-outcome POVM.
* `Cslib.Quantum.norm_toLp_mulVec_le_of_posSemidef`: a matrix `M` with `Mᴴ M ≤ 1` does not increase
  norms.
* `Cslib.Quantum.mem_unitaryGroup_of_isHermitian_of_mul_self`: a `±1` observable is unitary.

## References

* [R. Cleve, P. Høyer, B. Toner, J. Watrous, *Consequences and limits of nonlocal
  strategies*][CleveHoyerTonerWatrous2004]
-/

@[expose] public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker ComplexOrder

variable {ι κ ι' A B : Type*}

/-- The squared norm of a state as a quadratic form: `ψ† ψ = ‖ψ‖²`. -/
theorem star_dotProduct_self_eq_norm_sq [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    star ψ.ofLp ⬝ᵥ ψ.ofLp = (‖ψ‖ : ℂ) ^ 2 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
  rfl

/-- The expectation `v† M v` of a positive semidefinite matrix is real. -/
private theorem ofReal_re_of_posSemidef [Fintype ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef)
    (v : ι → ℂ) : ((star v ⬝ᵥ (M *ᵥ v)).re : ℂ) = star v ⬝ᵥ (M *ᵥ v) := by
  have h := Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg v)
  exact Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im]; exact h.2)

/-- A Hermitian idempotent matrix is positive semidefinite. -/
private theorem posSemidef_of_isHermitian_of_mul_self [Fintype ι] {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) : P.PosSemidef := by
  have : P = Pᴴ * P := by rw [hP.eq, hPP]
  rw [this]
  exact posSemidef_conjTranspose_mul_self P

/-- A **positive-operator-valued measurement** (POVM) with outcomes `A` on the system `ℂ^ι`:
positive semidefinite effects `E_a` summing to the identity
[Cleve, Høyer, Toner, Watrous, §2][CleveHoyerTonerWatrous2004]. -/
structure POVM (A ι : Type*) [Fintype A] [Fintype ι] [DecidableEq ι] where
  /-- The effect `E_a` of the outcome `a`. -/
  effect : A → Matrix ι ι ℂ
  /-- Every effect is positive semidefinite. -/
  posSemidef : ∀ a, (effect a).PosSemidef
  /-- The effects sum to the identity. -/
  sum_effect : ∑ a, effect a = 1

namespace POVM

section Basic

variable [Fintype A] [Fintype ι] [DecidableEq ι]

/-- The probability `⟨ψ|E_a|ψ⟩` of the outcome `a` when measuring `ψ` with `M`. -/
noncomputable def prob (M : POVM A ι) (ψ : EuclideanSpace ℂ ι) (a : A) : ℝ :=
  (star ψ.ofLp ⬝ᵥ (M.effect a *ᵥ ψ.ofLp)).re

theorem ofReal_prob (M : POVM A ι) (ψ : EuclideanSpace ℂ ι) (a : A) :
    (M.prob ψ a : ℂ) = star ψ.ofLp ⬝ᵥ (M.effect a *ᵥ ψ.ofLp) :=
  ofReal_re_of_posSemidef (M.posSemidef a) _

theorem prob_nonneg (M : POVM A ι) (ψ : EuclideanSpace ℂ ι) (a : A) : 0 ≤ M.prob ψ a :=
  (Complex.nonneg_iff.mp ((M.posSemidef a).dotProduct_mulVec_nonneg ψ.ofLp)).1

/-- The outcome probabilities of a POVM sum to the squared norm of the state. -/
theorem sum_prob (M : POVM A ι) (ψ : EuclideanSpace ℂ ι) : ∑ a, M.prob ψ a = ‖ψ‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_prob]
  rw [← dotProduct_sum, ← sum_mulVec, M.sum_effect, one_mulVec, star_dotProduct_self_eq_norm_sq]

/-- The outcome distribution of measuring the unit state `ψ` with `M`. -/
noncomputable def measure (M : POVM A ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (M.prob ψ a)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => M.prob_nonneg ψ a, sum_prob, hψ, one_pow,
      ENNReal.ofReal_one]

@[simp] theorem measure_apply (M : POVM A ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (a : A) :
    M.measure ψ hψ a = ENNReal.ofReal (M.prob ψ a) :=
  rfl

/-- The trivial measurement that always reports the outcome `a`. -/
noncomputable def const [DecidableEq A] (a : A) : POVM A ι where
  effect a' := if a' = a then 1 else 0
  posSemidef a' := by
    split_ifs
    · exact PosSemidef.one
    · exact PosSemidef.zero
  sum_effect := by simp

theorem prob_const [DecidableEq A] (a : A) (ψ : EuclideanSpace ℂ ι) (a' : A) :
    (const a : POVM A ι).prob ψ a' = if a' = a then ‖ψ‖ ^ 2 else 0 := by
  simp only [prob, const]
  split_ifs
  · rw [one_mulVec, star_dotProduct_self_eq_norm_sq, ← Complex.ofReal_pow, Complex.ofReal_re]
  · rw [zero_mulVec, dotProduct_zero, Complex.zero_re]

end Basic

section Basis

variable [Fintype ι] [DecidableEq ι]

/-- The **computational-basis measurement**, with the rank-one projections `|x⟩⟨x|` as effects. -/
noncomputable def basis : POVM ι ι where
  effect x := single x x 1
  posSemidef x := by
    have : single x x (1 : ℂ) = (single x x 1)ᴴ * single x x 1 := by
      rw [conjTranspose_single, star_one, single_mul_single_same, one_mul]
    rw [this]
    exact posSemidef_conjTranspose_mul_self _
  sum_effect := sum_single_one

theorem prob_basis (ψ : EuclideanSpace ℂ ι) (x : ι) : basis.prob ψ x = ‖ψ.ofLp x‖ ^ 2 := by
  simp only [prob, basis, single_mulVec_eq, one_mul, dotProduct_smul, dotProduct_single, mul_one,
    Pi.star_apply, smul_eq_mul]
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Measuring with the basis POVM is the computational-basis measurement. -/
theorem measure_basis (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    basis.measure ψ hψ = Cslib.Quantum.measure ψ hψ := by
  ext x
  rw [measure_apply, Cslib.Quantum.measure_apply, prob_basis]

end Basis

section Kronecker

variable [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The **product POVM** `E_a ⊗ F_b` on `ℂ^ι ⊗ ℂ^κ`: the first party measures the first factor with
`M` and the second party measures the second factor with `N`. -/
noncomputable def kronecker (M : POVM A ι) (N : POVM B κ) : POVM (A × B) (ι × κ) where
  effect ab := M.effect ab.1 ⊗ₖ N.effect ab.2
  posSemidef ab := (M.posSemidef ab.1).kronecker (N.posSemidef ab.2)
  sum_effect := by
    have h : ∑ ab : A × B, M.effect ab.1 ⊗ₖ N.effect ab.2 =
        (∑ a, M.effect a) ⊗ₖ ∑ b, N.effect b := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [Matrix.sum_apply, kronecker_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]
    rw [h, M.sum_effect, N.sum_effect, one_kronecker_one]

end Kronecker

section Reindex

variable [Fintype A] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- Relabel the basis of the system along `e : ι ≃ ι'`. -/
noncomputable def reindex (M : POVM A ι) (e : ι ≃ ι') : POVM A ι' where
  effect a := (M.effect a).submatrix e.symm e.symm
  posSemidef a := (M.posSemidef a).submatrix _
  sum_effect := by
    have h := congrArg (reindexAlgEquiv ℂ ℂ e) M.sum_effect
    rwa [map_sum, map_one] at h

end Reindex

section Observable

variable [Fintype ι] [DecidableEq ι]

/-- The two-outcome projective measurement of a **`±1` observable** `O` (Hermitian, `O² = 1`): the
effects are `(1 + O)/2` for `false` (eigenvalue `+1`) and `(1 - O)/2` for `true` (eigenvalue `-1`)
[Cleve, Høyer, Toner, Watrous, §3][CleveHoyerTonerWatrous2004]. -/
noncomputable def ofObservable (O : Matrix ι ι ℂ) (hO : O.IsHermitian) (hO2 : O * O = 1) :
    POVM Bool ι where
  effect b := bif b then (2⁻¹ : ℂ) • (1 - O) else (2⁻¹ : ℂ) • (1 + O)
  posSemidef b := by
    have h2 : IsSelfAdjoint (2⁻¹ : ℂ) := by simp [IsSelfAdjoint]
    cases b
    · rw [Bool.cond_false]
      refine posSemidef_of_isHermitian_of_mul_self ((isHermitian_one.add hO).smul h2) ?_
      simp only [smul_mul_smul_comm, add_mul, mul_add, hO2, one_mul, mul_one]
      module
    · rw [Bool.cond_true]
      refine posSemidef_of_isHermitian_of_mul_self ((isHermitian_one.sub hO).smul h2) ?_
      simp only [smul_mul_smul_comm, sub_mul, mul_sub, hO2, one_mul, mul_one]
      module
  sum_effect := by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
    module

/-- The observable `E_false - E_true` of a two-outcome POVM. -/
noncomputable def observable (M : POVM Bool ι) : Matrix ι ι ℂ := M.effect false - M.effect true

theorem isHermitian_observable (M : POVM Bool ι) : M.observable.IsHermitian :=
  (M.posSemidef false).isHermitian.sub (M.posSemidef true).isHermitian

theorem observable_ofObservable (O : Matrix ι ι ℂ) (hO : O.IsHermitian) (hO2 : O * O = 1) :
    (ofObservable O hO hO2).observable = O := by
  simp only [observable, ofObservable, Bool.cond_true, Bool.cond_false]
  module

/-- The observable `O = E_false - E_true` of any two-outcome POVM satisfies `O² ≤ 1`, because
`1 - O² = 4 E (1 - E)` for `E = E_false`. -/
theorem posSemidef_one_sub_observable_mul_self (M : POVM Bool ι) :
    (1 - M.observable * M.observable).PosSemidef := by
  set E := M.effect false
  have hF : M.effect true = 1 - E := by
    rw [← M.sum_effect, Fintype.sum_bool]; abel
  have h : 1 - M.observable * M.observable = (E + E)ᴴ * (1 - E) * (E + E) +
      ((1 - E) + (1 - E))ᴴ * E * ((1 - E) + (1 - E)) := by
    rw [conjTranspose_add, (M.posSemidef false).isHermitian.eq, conjTranspose_add,
      conjTranspose_sub, conjTranspose_one, (M.posSemidef false).isHermitian.eq, observable, hF]
    noncomm_ring
  rw [h]
  refine PosSemidef.add ?_ ?_
  · exact (hF ▸ M.posSemidef true).conjTranspose_mul_mul_same _
  · exact (M.posSemidef false).conjTranspose_mul_mul_same _

end Observable

end POVM

/-- A `±1` observable (Hermitian, `O² = 1`) is unitary. -/
theorem mem_unitaryGroup_of_isHermitian_of_mul_self [Fintype ι] [DecidableEq ι]
    {O : Matrix ι ι ℂ} (hO : O.IsHermitian) (hO2 : O * O = 1) : O ∈ unitaryGroup ι ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, hO.eq, hO2]

/-- A matrix `M` with `Mᴴ M ≤ 1` does not increase norms: `‖M ψ‖ ≤ ‖ψ‖`. -/
theorem norm_toLp_mulVec_le_of_posSemidef [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : (1 - Mᴴ * M).PosSemidef) (ψ : EuclideanSpace ℂ ι) :
    ‖(WithLp.toLp 2 (M *ᵥ ψ.ofLp) : EuclideanSpace ℂ ι)‖ ≤ ‖ψ‖ := by
  have h0 := (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg ψ.ofLp)).1
  have hMv := star_dotProduct_self_eq_norm_sq (WithLp.toLp 2 (M *ᵥ ψ.ofLp))
  rw [WithLp.ofLp_toLp] at hMv
  have hMM : star ψ.ofLp ⬝ᵥ ((Mᴴ * M) *ᵥ ψ.ofLp) =
      star (M *ᵥ ψ.ofLp) ⬝ᵥ (M *ᵥ ψ.ofLp) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  rw [sub_mulVec, one_mulVec, dotProduct_sub, hMM, hMv, star_dotProduct_self_eq_norm_sq,
    ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.ofReal_re] at h0
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

/-- Relabelling the basis along `e` preserves expectations `v† M v`. -/
theorem star_dotProduct_submatrix_mulVec [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    star (v ∘ e.symm) ⬝ᵥ (M.submatrix e.symm e.symm *ᵥ (v ∘ e.symm)) =
      star v ⬝ᵥ (M *ᵥ v) := by
  rw [submatrix_mulVec_equiv, Function.comp_assoc, e.symm_symm, Equiv.symm_comp_self,
    Function.comp_id]
  exact comp_equiv_dotProduct_comp_equiv (star v) (M *ᵥ v) e.symm

end Cslib.Quantum
