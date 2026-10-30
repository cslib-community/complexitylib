/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Quantum.Basic

/-! Quantum circuits: concrete runs, and objects that fail the definitions. -/

namespace ComplexityTests.QuantumCircuit

open Cslib.Quantum Matrix

/-- The Hadamard gate on the only qubit of a one-qubit register. -/
noncomputable def h₀ : PlacedGate 1 := ⟨1, Gate.hadamard, Function.Embedding.refl _⟩

-- `H|0⟩ = (|0⟩ + |1⟩)/√2`: measuring it gives each outcome with probability `1 / 2`.
example (y : Fin 1 → Bool) : Circuit.measure [h₀] (fun _ => false) y = 1 / 2 := by
  simp only [Circuit.measure, measure_apply, Circuit.run, Circuit.eval_cons, Circuit.eval_nil,
    PlacedGate.eval_ket_apply, PlacedGate.matrix_apply, h₀, Function.Embedding.refl_apply,
    exists_eq, not_true_eq_false, IsEmpty.forall_iff, implies_true, ite_true, Gate.hadamard_apply]
  simp

-- Interference: `HH = I`, so after two Hadamard gates qubit `0` never reads `1`, although after
-- one it reads `1` with probability `1 / 2`.
example (x : Fin 1 → Bool) : Circuit.run [h₀, h₀] x = ket x := by
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, PlacedGate.eval, ← unitaryEquiv_mul,
    PlacedGate.matrix, h₀, ← map_mul, Gate.hadamard_mul_self, map_one, unitaryEquiv_one]

example : measureProb (Circuit.run [h₀, h₀] (fun _ => false)) {fun _ => true} = 0 := by
  have : Circuit.run [h₀, h₀] (fun _ => false) = ket fun _ => false := by
    simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, PlacedGate.eval,
      ← unitaryEquiv_mul, PlacedGate.matrix, h₀, ← map_mul, Gate.hadamard_mul_self, map_one,
      unitaryEquiv_one]
  have hne : (fun _ : Fin 1 => true) ≠ fun _ => false := fun h => by simpa using congrFun h 0
  simp [this, measureProb, hne]

/-- The NOT gate on the only qubit of a one-qubit register. -/
noncomputable def x₀ : PlacedGate 1 := ⟨1, Gate.not, Function.Embedding.refl _⟩

-- Gates act first to last: `run [X, H] |0⟩ = H X |0⟩ = H |1⟩ = (|0⟩ - |1⟩)/√2`, whose amplitude on
-- `|1⟩` is `-1/√2`; in the other order, `X H |0⟩ = (|0⟩ + |1⟩)/√2` would give `+1/√2`.
example : (Circuit.run [x₀, h₀] fun _ => false).ofLp (fun _ => true) =
    -((Real.sqrt 2)⁻¹ : ℝ) := by
  have hx : x₀.eval (ket fun _ => false) = ket fun _ => true := by
    simp only [x₀, Gate.not, Gate.ofInvolutive, PlacedGate.eval_ofPerm_ket]
    congr 1
    funext j
    exact (splitEquiv_symm_apply_wire (Function.Embedding.refl _) _ _ j).trans (by
      fin_cases j; rfl)
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, hx, PlacedGate.eval_ket_apply,
    PlacedGate.matrix_apply, h₀, Function.Embedding.refl_apply, exists_eq, not_true_eq_false,
    IsEmpty.forall_iff, implies_true, ite_true, Gate.hadamard_apply]
  simp

/-- The Toffoli gate on the three qubits of a three-qubit register, in order. -/
noncomputable def toffoli₀ : PlacedGate 3 := ⟨3, Gate.toffoli, Function.Embedding.refl _⟩

-- Toffoli flips the target when both controls are set: `|110⟩ ↦ |111⟩`.
example : Circuit.run [toffoli₀] ![true, true, false] = ket ![true, true, true] := by
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, toffoli₀, Gate.toffoli,
    Gate.ofInvolutive, PlacedGate.eval_ofPerm_ket]
  congr 1
  funext j
  exact (splitEquiv_symm_apply_wire (Function.Embedding.refl _) _ _ j).trans (by
    fin_cases j <;> rfl)

/-- CNOT with control qubit `2` and target qubit `0` of a three-qubit register. -/
noncomputable def cnot₂₀ : PlacedGate 3 := ⟨2, Gate.cnot, ⟨![2, 0], by decide⟩⟩

-- The wires are ordered: qubit `2` controls qubit `0`, and qubit `1` is untouched, so
-- `|001⟩ ↦ |101⟩` and `|110⟩` is fixed.
example : Circuit.run [cnot₂₀] ![false, false, true] = ket ![true, false, true] := by
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, cnot₂₀, Gate.cnot,
    Gate.ofInvolutive, PlacedGate.eval_ofPerm_ket]
  congr 1
  funext j
  fin_cases j
  · exact splitEquiv_symm_apply_wire ⟨![2, 0], _⟩ _ _ 1
  · exact (splitEquiv_symm_apply_of_not ⟨![2, 0], _⟩ _ _ 1 (by decide)).trans rfl
  · exact splitEquiv_symm_apply_wire ⟨![2, 0], _⟩ _ _ 0

example : Circuit.run [cnot₂₀] ![true, true, false] = ket ![true, true, false] := by
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, cnot₂₀, Gate.cnot,
    Gate.ofInvolutive, PlacedGate.eval_ofPerm_ket]
  congr 1
  funext j
  fin_cases j
  · exact splitEquiv_symm_apply_wire ⟨![2, 0], _⟩ _ _ 1
  · exact (splitEquiv_symm_apply_of_not ⟨![2, 0], _⟩ _ _ 1 (by decide)).trans rfl
  · exact splitEquiv_symm_apply_wire ⟨![2, 0], _⟩ _ _ 0

/-- Qubit `0` of a two-qubit register. -/
def w₀ : Fin 1 ↪ Fin 2 := ⟨![0], by decide⟩

/-- The Hadamard gate on qubit `0` of a two-qubit register; qubit `1` is idle. -/
noncomputable def hq₀ : PlacedGate 2 := ⟨1, Gate.hadamard, w₀⟩

/-- CNOT with control qubit `0` and target qubit `1` of a two-qubit register. -/
noncomputable def cx₀₁ : PlacedGate 2 := ⟨2, Gate.cnot, Function.Embedding.refl _⟩

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

-- The Bell state: a Hadamard gate next to an idle qubit followed by CNOT gives
-- `(|00⟩ + |11⟩)/√2`, so the two qubits always agree.
theorem run_bell : Circuit.run [hq₀, cx₀₁] ![false, false] =
    ((Real.sqrt 2)⁻¹ : ℂ) • (ket ![false, false] + ket ![true, true]) := by
  have step₁ : hq₀.eval (ket ![false, false]) =
      ((Real.sqrt 2)⁻¹ : ℂ) • (ket ![false, false] + ket ![true, false]) := by
    ext y
    rw [PlacedGate.eval_ket_apply, hq₀_matrix_apply]
    have hy : y = ![y 0, y 1] := by funext j; fin_cases j <;> rfl
    rw [hy]
    generalize y 0 = a
    generalize y 1 = b
    cases a <;> cases b <;> simp [funext_iff, Fin.forall_fin_two]
  have step₂ (x : Fin 2 → Bool) : cx₀₁.eval (ket x) = ket ![x 0, x 1 ^^ x 0] := by
    simp only [cx₀₁, Gate.cnot, Gate.ofInvolutive, PlacedGate.eval_ofPerm_ket]
    congr 1
    funext j
    exact (splitEquiv_symm_apply_wire (Function.Embedding.refl _) _ _ j).trans (by
      fin_cases j <;> rfl)
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, step₁, map_smul, map_add, step₂]
  simp

example : Circuit.measure [hq₀, cx₀₁] ![false, false] ![true, true] = 1 / 2 := by
  rw [Circuit.measure_apply, run_bell]
  simp [funext_iff, Fin.forall_fin_two]

example : Circuit.measure [hq₀, cx₀₁] ![false, false] ![true, false] = 0 := by
  rw [Circuit.measure_apply, run_bell]
  simp [funext_iff, Fin.forall_fin_two]

-- The circuit `H; Toffoli` is over the gate set `{H, Toffoli}`, but a circuit containing `H` is
-- not over `{Toffoli}`.
example : Circuit.IsOver {⟨1, Gate.hadamard⟩, ⟨3, Gate.toffoli⟩}
    [(⟨1, Gate.hadamard, ⟨![0], by decide⟩⟩ : PlacedGate 3), toffoli₀] := by
  simp [Circuit.IsOver, toffoli₀]

example : ¬Circuit.IsOver {⟨3, Gate.toffoli⟩} [h₀] := fun h =>
  absurd (congrArg Sigma.fst (h h₀ List.mem_cons_self)) (by decide)

-- A non-unitary matrix is not a gate: `[[1, 1], [0, 1]]` is not unitary.
example : !![(1 : ℂ), 1; 0, 1] ∉ unitaryGroup (Fin 2) ℂ := by
  intro h
  have := congrFun (congrFun (mem_unitaryGroup_iff.mp h) 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose] at this

-- A two-qubit gate cannot be placed on a one-qubit register: the wires must be distinct.
example : IsEmpty (Fin 2 ↪ Fin 1) :=
  ⟨fun f => absurd (f.injective (Subsingleton.elim (f 0) (f 1))) (by decide)⟩

end ComplexityTests.QuantumCircuit
