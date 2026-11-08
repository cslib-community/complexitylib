/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Quantum.PhaseOracle
import CslibFrontier.Foundations.LinearAlgebra.PlaneRotation

/-! Controlled circuits, the reflection about zero and rotation by two reflections: the
controlled `T = H[a] Λ(σ_x)[a, b] H[a]` built from a Toffoli gate (a variant of Shi's `T_{π/4}`,
without its final `σ_x` on `b`), the reflection about `|00⟩` negating `|00⟩` and fixing `|10⟩`,
and the quarter turn of the plane `ℝ²` produced by two reflections at angle `π / 4`. -/

namespace ComplexityTests.QuantumReflection

open Cslib Cslib.Quantum Cslib.Quantum.GateCode Cslib.Quantum.Circuit

/-! ### Controlled `T` from a Toffoli gate -/

/-- **A controlled `T`**: the codes `H[1] Λ₂(σ_x)[0, 1; 2] H[1]` are `T = H[1] Λ(σ_x)[1, 2] H[1]`
controlled by qubit `0`. The Toffoli gate is the CNOT `Λ(σ_x)[1, 2]` with the extra control `0`. -/
example : IsControlled (0 : Fin 3)
    (ofCodes 3 [(true, 1, []), (false, 2, [0, 1]), (true, 1, [])])
    (ofCodes 3 [(true, 1, []), (false, 2, [1]), (true, 1, [])]) := by
  have hC : ([(true, 1, []), (false, 2, [0, 1]), (true, 1, [])] : List GateCode) =
      [(true, 1, [])] ++ [((false, 2, [1]) : GateCode)].map (addControl 0) ++
        [((true, 1, []) : GateCode)].reverse := rfl
  have hD : ([(true, 1, []), (false, 2, [1]), (true, 1, [])] : List GateCode) =
      [(true, 1, [])] ++ [(false, 2, [1])] ++ [((true, 1, []) : GateCode)].reverse := rfl
  have hA : ∀ g ∈ ([(true, 1, [])] : List GateCode), WellFormed 3 g := by
    simp [WellFormed]
  have hAc : ∀ g ∈ ([(true, 1, [])] : List GateCode), ((0 : Fin 3) : ℕ) ∉ g.2.1 :: g.2.2 := by
    simp
  have hB : IsClassical 3 ([((false, 2, [1]) : GateCode)].map (addControl 0)) := by
    simp [IsClassical, addControl, WellFormed]
  rw [hC, hD, ofCodes_append, ofCodes_append, ofCodes_append, ofCodes_append]
  exact IsControlled.conj hA hAc (isControlled_addControl hB)

/-! ### The reflection about `|00⟩` -/

/-- The basis string `|x₀ x₁⟩ ⊗ |000⟩` on qubits `0, 1` with scratch qubits `2, 3, 4`. -/
abbrev str₅ (x₀ x₁ : Bool) : Fin 5 → Bool := ![x₀, x₁, false, false, false]

/-- The reflection about the all-zero string of qubits `0, 1` negates `|x₀ x₁⟩ ⊗ |000⟩` exactly when
`x₀ = x₁ = 0`. -/
theorem eval_reflectZero_ket (x₀ x₁ : Bool) :
    eval (ofCodes 5 (reflectZeroCodes [0, 1] 2)) (ket (str₅ x₀ x₁)) =
      (if !x₀ && !x₁ then -1 else 1 : ℂ) • ket (str₅ x₀ x₁) := by
  ext y
  rw [reflectZeroCodes, eval_ofCodes_phaseOracleCodes
    (isClassical_zeroTestCodes (by decide) (by decide)) (by decide), WithLp.ofLp_smul,
    Pi.smul_apply, ket_apply]
  by_cases hy : y = str₅ x₀ x₁
  · subst hy
    have hx : ∀ i, 2 ≤ i → i ≤ 2 + [0, 1].length → readBit (str₅ x₀ x₁) i = false := by
      intro i h₁ h₂
      have h₂ : i ≤ 4 := by simpa using h₂
      interval_cases i <;> rfl
    rw [readBit_classicalRun_zeroTestCodes (by decide) (by decide) (by decide) _ hx]
    cases x₀ <;> cases x₁ <;> simp [readBit_of_lt]
  · simp [hy]

/-- **The reflection negates `|00⟩`.** -/
example : eval (ofCodes 5 (reflectZeroCodes [0, 1] 2)) (ket (str₅ false false)) =
    -ket (str₅ false false) := by
  rw [eval_reflectZero_ket]
  simp

/-- **The reflection fixes `|10⟩`.** -/
example : eval (ofCodes 5 (reflectZeroCodes [0, 1] 2)) (ket (str₅ true false)) =
    ket (str₅ true false) := by
  rw [eval_reflectZero_ket]
  simp

/-! ### A quarter turn of the plane from two reflections -/

/-- The reflection of `ℝ²` negating the first coordinate: it negates `a = (1, 0)` and fixes
`e = (0, 1)`. -/
def reflectFst : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ := (-LinearMap.fst ℝ ℝ ℝ).prod (LinearMap.snd ℝ ℝ ℝ)

/-- The reflection of `ℝ²` along the line `x + y = 0`: it negates `(1, 1)` and fixes `(1, -1)`. -/
def reflectDiag : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ := (-LinearMap.snd ℝ ℝ ℝ).prod (-LinearMap.fst ℝ ℝ ℝ)

/-- **Two reflections at angle `π / 4` turn the plane by a quarter**: the rotation lemma with
`γ = π / 4` and `φ = 0` sends `(1, 0)` to `-(cos (-π/2), sin (-π/2)) = (0, 1)`. -/
example : reflectDiag (reflectFst (1, 0)) = (0, 1) := by
  have h := LinearAlgebra.reflection_comp_reflection (K := ℝ) reflectFst reflectDiag
    (a := ((1 : ℝ), (0 : ℝ))) (e := (0, 1)) (γ := Real.pi / 4)
    (by ext <;> simp [reflectFst]) (by ext <;> simp [reflectFst])
    (by ext <;> simp [reflectDiag]) (by ext <;> simp [reflectDiag]) 0
  have hπ : (0 : ℝ) - 2 * (Real.pi / 4) = -(Real.pi / 2) := by ring
  simpa [hπ] using h

end ComplexityTests.QuantumReflection
