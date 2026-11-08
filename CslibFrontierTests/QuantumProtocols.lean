/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Quantum.SuperdenseCoding
import CslibFrontier.Computability.Circuit.Quantum.Teleportation
import CslibFrontier.Foundations.Quantum.NoCloning

/-! Teleportation, superdense coding and no-cloning: concrete instances, and an operation that
clones some states but not all. -/

namespace CslibFrontierTests.QuantumProtocols

open Cslib.Quantum Matrix Gate
open scoped Kronecker InnerProductSpace TensorProduct

/-! ### Teleportation -/

-- Teleporting `|0⟩`: Alice's outcome is uniform and Bob ends with `|0⟩`.
example : (measure (teleportState (ket false))
      ((norm_teleportState _).trans (norm_ket false))).map Prod.fst =
    Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) :=
  measure_teleportState_map_fst _ (norm_ket false)

example (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState (ket false))) =
      ket false :=
  teleportCorrection_postMeasure _ (norm_ket false) a b

-- Teleporting `|1⟩`: for every outcome Bob's corrected qubit is `|1⟩`. Before Alice measures, the
-- amplitude of `|1, 1, 0⟩` is `-1/2`, since `X Z |1⟩ = -|0⟩`.
example (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState (ket true))) =
      ket true :=
  teleportCorrection_postMeasure _ (norm_ket true) a b

example : (teleportState (ket true)).ofLp ((true, true), false) = -(1 / 2) := by
  rw [teleportState_apply]
  norm_num

/-- The state `|+⟩ = H|0⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def plus : EuclideanSpace ℂ Bool :=
  unitaryEquiv ⟨hadamardMatrix, hadamardMatrix_mem_unitaryGroup⟩ (ket false)

theorem plus_apply (b : Bool) : plus.ofLp b = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  rw [plus, unitaryEquiv_apply, hadamardMatrix_mulVec]
  cases b <;> simp

theorem norm_plus : ‖plus‖ = 1 := by
  rw [plus, LinearIsometryEquiv.norm_map, norm_ket]

-- Teleporting `|+⟩`: for every outcome Bob's corrected qubit is `|+⟩`.
example (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState plus)) = plus :=
  teleportCorrection_postMeasure _ norm_plus a b

-- Before Alice measures, the amplitude of `|1, 1, 0⟩` in the teleportation of `|+⟩` is
-- `-1/(2√2)`.
example : (teleportState plus).ofLp ((true, true), false) =
    -(1 / 2 * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) := by
  rw [teleportState_apply, plus_apply]
  norm_num

/-! ### Superdense coding -/

-- Bob decodes each of the four messages exactly.
example : measure (superdenseState false false) (norm_superdenseState _ _) =
    PMF.pure (false, false) :=
  superdense_coding false false

example : measure (superdenseState false true) (norm_superdenseState _ _) =
    PMF.pure (false, true) :=
  superdense_coding false true

example : measure (superdenseState true false) (norm_superdenseState _ _) =
    PMF.pure (true, false) :=
  superdense_coding true false

example : measure (superdenseState true true) (norm_superdenseState _ _) =
    PMF.pure (true, true) :=
  superdense_coding true true

-- For the message `(1, 1)` Bob's state carries the global phase `-1`, which the measurement
-- does not see.
example : superdenseState true true = (-1 : ℂ) • ket (true, true) := by
  rw [superdenseState_eq]
  norm_num

/-! ### No-cloning -/

-- The CNOT clones both computational basis states, which are orthogonal: the dichotomy of
-- `inner_eq_zero_or_eq_of_unitary_clone` allows this.
example (b : Bool) :
    cnotMatrix *ᵥ (prodState (ket b) (ket false)).ofLp = (prodState (ket b) (ket b)).ofLp := by
  ext ⟨x, y⟩
  cases b <;> cases x <;> cases y <;> simp

theorem inner_ket_false_plus : ⟪ket false, plus⟫_ℂ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  rw [ket, EuclideanSpace.inner_single_left, plus_apply]
  simp

-- The CNOT does not clone `|+⟩`: `|0⟩` and `|+⟩` are neither orthogonal nor equal.
example : cnotMatrix *ᵥ (prodState plus (ket false)).ofLp ≠ (prodState plus plus).ofLp := by
  intro h
  have h0 : cnotMatrix *ᵥ (prodState (ket false) (ket false)).ofLp =
      (prodState (ket false) (ket false)).ofLp := by
    ext ⟨x, y⟩
    cases x <;> cases y <;> simp
  rcases inner_eq_zero_or_eq_of_unitary_clone cnotMatrix_mem_unitaryGroup (norm_ket false)
      norm_plus (norm_ket false) h0 h with h' | h'
  · rw [inner_ket_false_plus] at h'
    simp at h'
  · have h1 := congrArg (fun v : EuclideanSpace ℂ Bool => v.ofLp true) h'
    simp only [ket_apply, plus_apply, Bool.true_eq_false, ↓reduceIte] at h1
    exact Complex.ofReal_ne_zero.mpr (by positivity) h1.symm

-- No matrix on two qubits clones every unit qubit.
example : ¬ ∃ U : Matrix (Bool × Bool) (Bool × Bool) ℂ, ∀ ψ : EuclideanSpace ℂ Bool, ‖ψ‖ = 1 →
    U *ᵥ (prodState ψ (ket false)).ofLp = (prodState ψ ψ).ofLp :=
  not_exists_matrix_clone (ket false)

-- Not even up to a nonzero state-dependent factor.
example : ¬ ∃ (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) (c : EuclideanSpace ℂ Bool → ℂ),
    ∀ ψ : EuclideanSpace ℂ Bool, ‖ψ‖ = 1 →
      c ψ ≠ 0 ∧ U *ᵥ (prodState ψ (ket false)).ofLp = c ψ • (prodState ψ ψ).ofLp :=
  not_exists_matrix_clone_smul (ket false)

-- The hypothesis `Nontrivial ι` of `not_exists_matrix_clone_smul` is needed: in dimension 1 the
-- identity clones every unit state up to the nonzero factor `1/ψ`.
example : ∃ (U : Matrix (Unit × Unit) (Unit × Unit) ℂ) (c : EuclideanSpace ℂ Unit → ℂ),
    ∀ ψ : EuclideanSpace ℂ Unit, ‖ψ‖ = 1 →
      c ψ ≠ 0 ∧ U *ᵥ (prodState ψ (ket ())).ofLp = c ψ • (prodState ψ ψ).ofLp := by
  refine ⟨1, fun ψ => (ψ.ofLp ())⁻¹, fun ψ hψ => ?_⟩
  have h0 : ψ.ofLp () ≠ 0 := by
    intro h
    have : ψ = 0 := by ext u; cases u; simpa using h
    simp [this] at hψ
  refine ⟨inv_ne_zero h0, ?_⟩
  ext ⟨⟨⟩, ⟨⟩⟩
  simp only [one_mulVec, prodState_apply, ket_apply, ite_true, mul_one, Pi.smul_apply,
    smul_eq_mul]
  field_simp

-- No linear map on `ℂ² ⊗ ℂ²` clones every unit vector of `ℂ²`.
example : ¬ ∃ L : EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2),
    ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → L (ψ ⊗ₜ EuclideanSpace.single 0 1) = ψ ⊗ₜ ψ := by
  refine not_exists_linearMap_clone ?_ _
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
  norm_num

/-! ### Pauli matrices and the Bell state -/

-- `X` and `Z` do not commute.
example : pauliZ * pauliX ≠ pauliX * pauliZ := by
  intro h
  have := congrFun (congrFun h false) true
  norm_num [Matrix.mul_apply] at this

-- `⟨Φ⁺| Z ⊗ Z |Φ⁺⟩ = 1`: the Bell state is a `+1` eigenvector of `Z ⊗ Z`.
example : star bell.ofLp ⬝ᵥ ((pauliZ ⊗ₖ pauliZ) *ᵥ bell.ofLp) = 1 := by
  rw [bell_eq_maxEntangled, star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace]
  simp [Matrix.trace, pauliZ]

end CslibFrontierTests.QuantumProtocols
