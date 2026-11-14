/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.PointerWalk
public import CslibFrontierTests.QuantumCircuitFixture
import CslibFrontier.Probability.PMF.Support

/-! Original three-qubit fixtures for the native adaptive pointer controller. Wire 0 retains
phase memory, wire 1 holds the selected address, and wire 2 holds the negative response state.
The calculations use the existing coded-gate and XOR-query basis laws. -/

public section

namespace CslibFrontierTests.QuantumControllerState

open Cslib Cslib.Quantum

/-- Place a one-qubit gate on the indicated wire of the three-qubit device. -/
@[expose] def wire (i : Fin 3) : Fin 1 ↪ Fin 3 :=
  ⟨![i], fun _ _ _ => Subsingleton.elim _ _⟩

/-- The Hadamard acting on the retained phase-memory qubit. -/
@[expose] noncomputable def hMemory : PlacedGate 3 := ⟨1, Gate.hadamard, wire 0⟩

/-- The Hadamard preparing the oracle response in a negative eigenstate. -/
@[expose] noncomputable def hResponse : PlacedGate 3 := ⟨1, Gate.hadamard, wire 2⟩

/-- The NOT acting on the address qubit. -/
@[expose] noncomputable def xAddress : PlacedGate 3 := ⟨1, Gate.not, wire 1⟩

/-- The NOT acting on the response qubit. -/
@[expose] noncomputable def xResponse : PlacedGate 3 := ⟨1, Gate.not, wire 2⟩

/-- The controller's address-dependent elementary code selects the appropriate NOT. -/
theorem decode_flip (H : (Fin 2 → Bool) → Fin 1 → Bool) (address : Bool) :
    (OracleGateCode.gate (false, false, if address then 1 else 2, [])).toPlacedGate? 3 H =
      some (if address then xAddress else xResponse) := by
  cases address <;> rfl

/-- The controller's query occupies its two address wires and one response wire. -/
theorem decode_query (H : (Fin 2 → Bool) → Fin 1 → Bool) :
    OracleGateCode.query.toPlacedGate? 3 H =
      some (xorQuery H (Function.Embedding.refl _)) := by rfl

/-- A stored parity bit as the relative phase of the first qubit. The address is zero and the
response is negative. The definition uses the same physical gates as the controller. -/
@[expose] noncomputable def phaseState (parity : Bool) : Qubits 3 :=
  hMemory.eval (hResponse.eval (ket ![parity, false, true]))

/-- The phase fixture is a unit vector. -/
theorem norm_phaseState (parity : Bool) : ‖phaseState parity‖ = 1 := by
  simp [phaseState]

theorem hMemory_ket (p a r : Bool) :
    hMemory.eval (ket ![p, a, r]) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket ![false, a, r] +
      ((if p then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) • ket ![true, a, r] := by
  have h := GateCode.eval_toPlacedGate_hadamard_ket
    (g := hMemory) (t := 0) (by rfl) (by decide) ![p, a, r]
  have hu (c : Bool) : Function.update ![p, a, r] (0 : Fin 3) c = ![c, a, r] := by
    ext i
    fin_cases i <;> simp
  simpa [Fintype.sum_bool, hu, add_comm] using h

theorem hResponse_ket (p a r : Bool) :
    hResponse.eval (ket ![p, a, r]) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket ![p, a, false] +
      ((if r then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) • ket ![p, a, true] := by
  have h := GateCode.eval_toPlacedGate_hadamard_ket
    (g := hResponse) (t := 2) (by rfl) (by decide) ![p, a, r]
  have hu (c : Bool) : Function.update ![p, a, r] (2 : Fin 3) c = ![p, a, c] := by
    ext i
    fin_cases i <;> simp
  simpa [Fintype.sum_bool, hu, add_comm] using h

/-- A response-wire Hadamard cannot change the memory bit of a basis input. -/
theorem hResponse_ket_apply_of_ne (p a r : Bool) (y : Fin 3 → Bool) (hp : y 0 ≠ p) :
    (hResponse.eval (ket ![p, a, r])).ofLp y = 0 := by
  have hne (c : Bool) : y ≠ ![p, a, c] := by
    intro h
    exact hp (by rw [h]; rfl)
  rw [hResponse_ket]
  cases r <;> simp [hne]

theorem xAddress_ket (p a r : Bool) :
    xAddress.eval (ket ![p, a, r]) = ket ![p, !a, r] := by
  have h := GateCode.eval_toPlacedGate_ket
    (g := xAddress) (t := 1) (cs := []) (by rfl) (by decide) ![p, a, r]
  have hu : Function.update ![p, a, r] (1 : Fin 3) (!a) = ![p, !a, r] := by
    ext i
    fin_cases i <;> simp
  simp only [List.all_nil, Bool.xor_true] at h
  change xAddress.eval (ket ![p, a, r]) = ket (Function.update ![p, a, r] 1 (!a)) at h
  exact h.trans (congrArg ket hu)

theorem xResponse_ket (p a r : Bool) :
    xResponse.eval (ket ![p, a, r]) = ket ![p, a, !r] := by
  have h := GateCode.eval_toPlacedGate_ket
    (g := xResponse) (t := 2) (cs := []) (by rfl) (by decide) ![p, a, r]
  have hu : Function.update ![p, a, r] (2 : Fin 3) (!r) = ![p, a, !r] := by
    ext i
    fin_cases i <;> simp
  simp only [List.all_nil, Bool.xor_true] at h
  change xResponse.eval (ket ![p, a, r]) = ket (Function.update ![p, a, r] 2 (!r)) at h
  exact h.trans (congrArg ket hu)

/-- The existing coherent XOR-query law in the three coordinates used by the device. -/
theorem query_ket (H : (Fin 2 → Bool) → Fin 1 → Bool) (x : Fin 3 → Bool) :
    (xorQuery H (Function.Embedding.refl _)).eval (ket x) =
      ket ![x 0, x 1, x 2 ^^ H ![x 0, x 1] 0] := by
  let A : Fin (2 + 1) ↪ Fin 3 := Function.Embedding.refl _
  let w : {j // ¬∃ i, A i = j} → Bool := fun _ => false
  have hin (r : Fin 1 → Bool) :
      (queryRegisters A).symm (![x 0, x 1], r, w) = ![x 0, x 1, r 0] := by
    funext j
    fin_cases j
    · exact queryRegisters_symm_query A _ _ w 0
    · exact queryRegisters_symm_query A _ _ w 1
    · exact queryRegisters_symm_response A _ _ w 0
  have hx : ![x 0, x 1, x 2] = x := by
    ext j
    fin_cases j <;> rfl
  simpa only [hin, hx, Pi.add_apply, Bool.add_eq_xor, A] using
    xorQuery_eval_ket H A ![x 0, x 1] (fun _ => x 2) w

/-- The three gates used by the controller's preparation produce its initial phase fixture. -/
theorem prepare_state :
    hMemory.eval (hResponse.eval (xResponse.eval (ket ![false, false, false]))) =
      phaseState false := by
  rw [xResponse_ket]
  rfl

/-- Terminal Hadamard exposes the retained parity without disturbing the response eigenstate. -/
theorem readout_state (parity : Bool) :
    hMemory.eval (phaseState parity) = hResponse.eval (ket ![parity, false, true]) :=
  CslibFrontierTests.QuantumCircuit.hadamard_twice (wire 0) _

/-- Reading only the memory wire returns its stored parity with certainty. The response qubit
retains its coherent negative state; it need not be measured by the controller. -/
theorem measure_readout (parity : Bool) :
    (Cslib.Quantum.measure (hMemory.eval (phaseState parity))
      (by simpa using norm_phaseState parity)).map (fun y => y 0) = PMF.pure parity := by
  apply Cslib.Probability.PMF.map_eq_pure_iff.mpr
  intro y hy
  by_contra hparity
  have hz : (hMemory.eval (phaseState parity)).ofLp y = 0 := by
    rw [readout_state]
    exact hResponse_ket_apply_of_ne _ _ _ _ hparity
  simp [PMF.mem_support_iff, Cslib.Quantum.measure_apply, hz] at hy

/-- One native phase round queries the same two-input-bit table at the selected classical
address. The first value contributes a global sign; the xor of both values updates memory. -/
theorem phase_state (H : (Fin 2 → Bool) → Fin 1 → Bool) (parity address : Bool) :
    (if address then xAddress else xResponse).eval
        ((xorQuery H (Function.Embedding.refl _)).eval
          ((if address then xAddress else xResponse).eval (phaseState parity))) =
      (if H ![false, address] 0 then -1 else 1 : ℂ) •
        phaseState (parity ^^ H ![false, address] 0 ^^ H ![true, address] 0) := by
  cases h₀ : H ![false, address] 0 <;> cases h₁ : H ![true, address] 0 <;>
    cases address <;> cases parity <;>
    simp only [phaseState, hResponse_ket, hMemory_ket, map_add, map_smul,
      xAddress_ket, xResponse_ket, query_ket, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h₀, h₁,
      Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, smul_add, smul_smul] <;> module

end CslibFrontierTests.QuantumControllerState
