/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Basic

/-! Shared Hadamard circuit fixtures, exported for ordinary module clients. -/

public section

namespace CslibFrontierTests.QuantumCircuit

open Cslib.Quantum

/-- Two Hadamard gates on the same wire cancel in any register. -/
theorem hadamard_twice {n : ℕ} (A : Fin 1 ↪ Fin n) (ψ : Qubits n) :
    (PlacedGate.mk 1 Gate.hadamard A).eval ((PlacedGate.mk 1 Gate.hadamard A).eval ψ) = ψ := by
  change unitaryEquiv (place A Gate.hadamard) (unitaryEquiv (place A Gate.hadamard) ψ) = ψ
  rw [← unitaryEquiv_mul, ← map_mul, Gate.hadamard_mul_self, map_one, unitaryEquiv_one]

/-- The Hadamard gate on the only qubit of a one-qubit register. -/
@[expose] noncomputable def h₀ : PlacedGate 1 := ⟨1, Gate.hadamard, Function.Embedding.refl _⟩

/-- Qubit `0` of a two-qubit register. -/
@[expose] def w₀ : Fin 1 ↪ Fin 2 := ⟨![0], by decide⟩

/-- The Hadamard gate on qubit `0` of a two-qubit register; qubit `1` is idle. -/
@[expose] noncomputable def hq₀ : PlacedGate 2 := ⟨1, Gate.hadamard, w₀⟩

theorem hq₀_matrix_apply (y x : Fin 2 → Bool) : (hq₀.matrix : Matrix _ _ ℂ) y x =
    if y 1 = x 1 then (if y 0 && x 0 then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0 := by
  change (place w₀ Gate.hadamard : Matrix _ _ ℂ) y x = _
  rw [place_apply]
  have h1 : (∀ j, (¬∃ i, w₀ i = j) → y j = x j) ↔ y 1 = x 1 := by
    constructor
    · intro h
      exact h 1 (by rintro ⟨i, hi⟩; fin_cases i; exact absurd hi (by decide))
    · intro h j hj
      fin_cases j
      · exact absurd ⟨0, rfl⟩ hj
      · exact h
  simp only [h1]
  rfl

end CslibFrontierTests.QuantumCircuit
