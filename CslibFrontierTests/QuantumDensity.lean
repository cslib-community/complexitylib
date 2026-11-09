/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.Quantum.OneTimePad
import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.Pauli

/-! Density matrices, the partial trace, no-signalling and the quantum one-time pad: concrete
instances and edge cases. -/

namespace CslibFrontierTests.QuantumDensity

open Cslib.Quantum Cslib.Crypto.Protocols.Quantum.OneTimePad Matrix Finset
open scoped Kronecker

/-! ### Density matrices -/

-- A basis state is a density matrix.
example : IsDensityMatrix (pureState (ket true)) := isDensityMatrix_pureState (norm_ket true)

-- The trace-one condition is not vacuous: `|0⟩⟨0| + |1⟩⟨1|` is positive semidefinite but has
-- trace two.
example : ¬ IsDensityMatrix (pureState (ket false) + pureState (ket true)) := by
  intro h
  have h1 := h.trace_eq_one
  rw [trace_add, trace_pureState, trace_pureState, norm_ket, norm_ket] at h1
  norm_num at h1

-- Bob's half of an EPR pair is the maximally mixed qubit `1 / 2`; so is Alice's.
example : partialTraceLeft (pureState bell) = (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
  rw [bell, partialTraceLeft_pureState_maxEntangled, Fintype.card_bool, Nat.cast_ofNat]

example : partialTraceRight (pureState bell) = (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
  rw [bell, partialTraceRight_pureState_maxEntangled, Fintype.card_bool, Nat.cast_ofNat]

/-! ### No-signalling -/

-- Whatever unitary Alice applies to her half of an EPR pair, Bob's half stays `1 / 2`.
example {U : Matrix Bool Bool ℂ} (hU : U ∈ unitaryGroup Bool ℂ) :
    partialTraceLeft ((U ⊗ₖ (1 : Matrix Bool Bool ℂ)) * pureState bell *
      (U ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ) = (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
  rw [partialTraceLeft_conj_unitary hU, bell, partialTraceLeft_pureState_maxEntangled,
    Fintype.card_bool, Nat.cast_ofNat]

-- The same holds if Alice measures her half and discards the outcome.
example : partialTraceLeft (∑ i, (single i i (1 : ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ)) * pureState bell *
      (single i i (1 : ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ) =
      (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
  rw [partialTraceLeft_measure, bell, partialTraceLeft_pureState_maxEntangled, Fintype.card_bool,
    Nat.cast_ofNat]

/-! ### Pauli strings -/

-- On one qubit, `X^1` and `Z^1` are the Pauli matrices `X` and `Z`.
example : (pauliXPow (fun _ : Unit => true)).submatrix (Equiv.funUnique Unit Bool).symm
    (Equiv.funUnique Unit Bool).symm = pauliX := by
  ext b c
  cases b <;> cases c <;> simp [pauliXPow_apply, funext_iff]

example : (pauliZPow (fun _ : Unit => true)).submatrix (Equiv.funUnique Unit Bool).symm
    (Equiv.funUnique Unit Bool).symm = pauliZ := by
  ext b c
  cases b <;> cases c <;>
    simp [pauliZPow_apply, funext_iff, dotProduct, show (true * true : Bool) = true from rfl,
      show (true * false : Bool) = false from rfl]

/-! ### The quantum one-time pad -/

/-- Encrypting a basis state `|z⟩` with the key `(a, b)` gives the basis state `|z + a⟩`: the phase
flip only contributes a global sign. -/
theorem encrypt_pureState_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (a b z : ι → Bool) :
    encrypt (a, b) (pureState (ket z)) = pureState (ket (z + a)) := by
  ext y y'
  simp only [encrypt, pauliString_mul_mul_conjTranspose_apply, pureState_apply, ket_apply]
  have hz (w : ι → Bool) : (w + a = z) ↔ (w = z + a) := by
    constructor <;> rintro rfl <;> simp
  simp only [hz]
  by_cases hy : y = z + a
  · by_cases hy' : y' = z + a
    · subst hy hy'
      simp only [ite_true, Cslib.BitString.add_cancel_right, star_one, mul_one]
      rw [← Complex.ofReal_mul, Cslib.BitString.signVal_mul_self, Complex.ofReal_one]
    · simp [hy, hy']
  · simp [hy]

-- A single ciphertext is not secret: with a fixed key the ciphertext of `|z⟩` is a basis state,
-- not the maximally mixed state, so averaging over the key is essential.
example (k : (Unit → Bool) × (Unit → Bool)) (z : Unit → Bool) :
    encrypt k (pureState (ket z)) ≠ (2 : ℂ)⁻¹ • (1 : Op Unit) := by
  intro h
  rw [encrypt_pureState_ket] at h
  have h1 := congrFun (congrFun h (z + k.1)) (z + k.1)
  simp [pureState_apply, ket_apply] at h1

-- One qubit: the average ciphertext of `|0⟩⟨0|` and of `|+⟩⟨+|` is `1 / 2`, and every pure qubit
-- state has the same average ciphertext, so without the key they are indistinguishable.
example : averageCiphertext (pureState (ket (fun _ : Unit => false))) =
    (2 : ℂ)⁻¹ • (1 : Op Unit) := by
  rw [averageCiphertext_eq (isDensityMatrix_pureState (norm_ket _))]
  norm_num

/-- `|+⟩` on the one-qubit register `Unit → Bool`. -/
noncomputable def plusOne : EuclideanSpace ℂ (Unit → Bool) :=
  WithLp.toLp 2 fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

theorem norm_plusOne : ‖plusOne‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [plusOne, Complex.norm_real, Real.norm_eq_abs, sq_abs, sum_const, card_univ,
    Fintype.card_fun, Fintype.card_unit, Fintype.card_bool, inv_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

example : averageCiphertext (pureState plusOne) = (2 : ℂ)⁻¹ • (1 : Op Unit) := by
  rw [averageCiphertext_eq (isDensityMatrix_pureState norm_plusOne)]
  norm_num

example {ψ : EuclideanSpace ℂ (Unit → Bool)} (hψ : ‖ψ‖ = 1) :
    averageCiphertext (pureState ψ) = averageCiphertext (pureState (ket (fun _ : Unit => false))) :=
  averageCiphertext_eq_averageCiphertext (isDensityMatrix_pureState hψ)
    (isDensityMatrix_pureState (norm_ket _))

-- Without the trace-one hypothesis the twirl is `tr ρ / 2ⁿ • 1`: a traceless matrix twirls to zero.
example : averageCiphertext (pureState (ket (fun _ : Unit => false)) -
    pureState (ket (fun _ : Unit => true))) = 0 := by
  rw [averageCiphertext_eq_trace_smul, trace_sub, trace_pureState, trace_pureState, norm_ket,
    norm_ket, sub_self, zero_div, zero_smul]

-- Secrecy with a reference system: if Alice encrypts her half of an EPR pair, Eve's joint state
-- with Bob's half is `1 / 2 ⊗ 1 / 2`, the same as for two independent maximally mixed qubits.
example : averageCiphertextWith (pureState (maxEntangled (Unit → Bool))) =
    ((2 : ℂ)⁻¹ • (1 : Op Unit)) ⊗ₖ ((2 : ℂ)⁻¹ • (1 : Op Unit)) := by
  rw [averageCiphertextWith_eq, partialTraceLeft_pureState_maxEntangled]
  norm_num

end CslibFrontierTests.QuantumDensity
