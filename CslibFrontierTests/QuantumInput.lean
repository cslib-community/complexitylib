/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Input
public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode
public import CslibFrontierTests.QuantumCircuitFixture

/-! A circuit acting on a displaced auxiliary qubit distinguishes the two imaginary-phase
states while preserving the classical input. -/

public section

namespace CslibFrontierTests.QuantumInput

open Cslib.Quantum
open CslibFrontierTests.QuantumCircuit

/-- The two states `(|0⟩ ± i|1⟩)/√2`. -/
@[expose] noncomputable def phaseInput (b : Bool) : Qubits 1 :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (ket (fun _ => false) + (if b then -Complex.I else Complex.I) • ket (fun _ => true))

/-- Apply `S†` and then `H` to read the imaginary phase. -/
@[expose] noncomputable def phaseDecode : Circuit 1 :=
  [PlacedGate.ctrlPhase true (Function.Embedding.refl _), h₀]

private theorem phase_cancel (b : Bool) :
    (PlacedGate.ctrlPhase true (Function.Embedding.refl (Fin 1))).eval (phaseInput b) =
      h₀.eval (ket fun _ => b) := by
  rw [phaseInput, map_smul, map_add, map_smul, PlacedGate.eval_ctrlPhase_ket,
    PlacedGate.eval_ctrlPhase_ket]
  ext y
  simp only [PlacedGate.eval_ket_apply, PlacedGate.matrix_apply, h₀,
    Function.Embedding.refl_apply, exists_eq, not_true_eq_false, IsEmpty.forall_iff,
    implies_true, ite_true, Gate.hadamard_apply, WithLp.ofLp_smul, WithLp.ofLp_add,
    Pi.smul_apply, Pi.add_apply, ket_apply, smul_eq_mul]
  have hy : y = fun _ => y 0 := funext fun i => congrArg y (Subsingleton.elim i 0)
  rw [hy]
  cases b <;> cases y 0 <;> simp [funext_iff]

/-- The two imaginary-phase states are decoded to distinct basis states. -/
theorem eval_phaseDecode (b : Bool) : phaseDecode.eval (phaseInput b) = ket (fun _ => b) := by
  simp only [phaseDecode, Circuit.eval_cons, Circuit.eval_nil, phase_cancel]
  unfold h₀
  simp only [PlacedGate.eval, ← unitaryEquiv_mul, PlacedGate.matrix, ← map_mul,
    Gate.hadamard_mul_self, map_one, unitaryEquiv_one]

/-- Both imaginary-phase inputs are unit vectors. -/
theorem norm_phaseInput (b : Bool) : ‖phaseInput b‖ = 1 := by
  rw [← Circuit.norm_eval phaseDecode (phaseInput b), eval_phaseDecode, norm_ket]

-- The auxiliary wire follows both length-dependent classical blocks. Naturality avoids any
-- coordinate-level proof about the entire growing register.
example (n ℓ : ℕ) (x : Fin (2 * n + 1 + ℓ + 1) → Bool) (b : Bool) :
    (Circuit.mapWires (blockEmb (2 * n + 1 + ℓ) (by omega)) phaseDecode).eval
      (embedState (blockEmb (2 * n + 1 + ℓ) (by omega)) x (phaseInput b)) =
        ket (glue (blockEmb (2 * n + 1 + ℓ) (by omega)) (fun _ : Fin 1 => b) x) := by
  rw [Circuit.eval_mapWires_embedState, eval_phaseDecode, embedState_ket]

end CslibFrontierTests.QuantumInput
