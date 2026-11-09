/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.BQP.PhaseGates

/-! The real simulation of controlled phase gates: well-formed codes, the translation, the phase
gate moving an amplitude into the imaginary part, and a family with a phase gate deciding a
language in `BQP`. -/

namespace CslibFrontierTests.QuantumRealEncoding

open Cslib Cslib.Quantum Cslib.Complexity Turing.MultiTapeTM

/-! ### Gate codes with controlled phase gates -/

-- `S` on qubit `0` and `Λ(S)` on qubits `1, 0` are well formed on two qubits; a repeated qubit,
-- two controls, or a qubit outside the register are not.
example : PhaseGateCode.WellFormed 2 (true, false, 0, []) := by decide
example : PhaseGateCode.WellFormed 2 (true, true, 0, [1]) := by decide
example : ¬PhaseGateCode.WellFormed 2 (true, false, 0, [0]) := by decide
example : ¬PhaseGateCode.WellFormed 3 (true, false, 0, [1, 2]) := by decide
example : ¬PhaseGateCode.WellFormed 2 (true, false, 2, []) := by decide

-- The translation keeps gate codes, writes `S` as `H, CNOT, H, CNOT` on the encoding qubit, and
-- `Λ(S)⁻¹` as `Toffoli, H, Toffoli, H`.
example : PhaseGateCode.toRealCodes 2 [(false, true, 0, []), (true, false, 1, [])] =
    [(true, 0, []), (true, 2, []), (false, 2, [1]), (true, 2, []), (false, 2, [1])] := rfl
example : PhaseGateCode.toRealCodes 2 [(true, true, 0, [1])] =
    [(false, 2, [0, 1]), (true, 2, []), (false, 2, [0, 1]), (true, 2, [])] := rfl

/-! ### The phase gate and its real simulation -/

/-- `S|1⟩ = i|1⟩`. -/
theorem run_phase : Circuit.run (Circuit.ofPhaseCodes 1 [(true, false, 0, [])]) ![true] =
    Complex.I • ket ![true] := by
  obtain ⟨k, e, he, -⟩ := PhaseGateCode.exists_toPlacedGate?_eq_ctrlPhase (m := 1) (inv := false)
    (t := 0) (cs := []) (by decide)
  simp [Circuit.ofPhaseCodes, he, Circuit.run, PlacedGate.eval_ctrlPhase_ket]

-- The real simulation stores the imaginary amplitude `i` of `|1⟩` on the encoding qubit: it maps
-- `|1 0⟩` (real part one) to `|1 1⟩` (imaginary part one).
example : Circuit.run (Circuit.ofCodes 2 (PhaseGateCode.toRealCodes 1 [(true, false, 0, [])]))
    ![true, false] = ket ![true, true] := by
  have h := (PhaseGateCode.realSimulates_toRealCodes (m := 1) (gs := [(true, false, 0, [])])
    (by decide)).run_snoc_false ![true]
  have h₁ : (Fin.snoc ![true] false : Fin 2 → Bool) = ![true, false] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : (![true, true] : Fin 2 → Bool) = Fin.snoc ![true] true := by
    funext i
    fin_cases i <;> rfl
  rw [h₁] at h
  rw [h, run_phase, h₂]
  ext z
  obtain ⟨y, b, rfl⟩ : ∃ y b, z = Fin.snoc y b :=
    ⟨Fin.init z, z (Fin.last 1), (Fin.snoc_init_self z).symm⟩
  rw [realEncode_apply_snoc, ket_apply]
  simp only [eq_snoc_iff, Fin.init_snoc, Fin.snoc_last]
  by_cases hy : y = ![true] <;> cases b <;> simp [hy]

/-! ### A family with a phase gate -/

/-- The family that applies `S` to the first input bit, on one qubit more than the input. -/
def phaseFirst : UniformPhaseCircuitFamily where
  width n := n + 1
  gates _ := [(true, false, 0, [])]
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_gates := ComputableInPolyTime.const _
  le_width n := Nat.le_succ n
  width_pos n := Nat.succ_pos n
  wellFormed n g hg := by
    rw [List.mem_singleton.mp hg]
    exact ⟨by simp, by simp, by simp⟩

/-- A phase does not change measurement probabilities: the family reads the first input bit. -/
theorem acceptProb_phaseFirst (x : List Bool) :
    phaseFirst.acceptProb x = if x.headD false then 1 else 0 := by
  obtain ⟨k, e, he, -⟩ := PhaseGateCode.exists_toPlacedGate?_eq_ctrlPhase
    (m := x.length + 1) (inv := false) (t := 0) (cs := []) ⟨by simp, by simp, by simp⟩
  change measureProb (Circuit.run (Circuit.ofPhaseCodes (x.length + 1) [(true, false, 0, [])])
    (inputState _ x)) (accepting _) = _
  simp only [Circuit.ofPhaseCodes, List.filterMap_cons, he, List.filterMap_nil, Circuit.run,
    Circuit.eval_cons, Circuit.eval_nil, PlacedGate.eval_ctrlPhase_ket, measureProb_smul,
    measureProb_ket, mem_accepting (Nat.succ_pos _), Bool.cond_false]
  have hnorm : ‖(if ∀ i, inputState (x.length + 1) x (e i) = true then Complex.I else 1 : ℂ)‖ ^ 2
      = 1 := by
    split_ifs <;> simp
  rw [hnorm, one_mul]
  simp only [inputState]
  cases x <;> rfl

/-- The words whose first bit is one. -/
def FirstBit : Set (List Bool) := {x | x.headD false = true}

/-- Deciding the first bit with the family `phaseFirst`, which uses a phase gate. -/
theorem firstBit_mem_BQP : FirstBit ∈ BQP encBits := by
  refine mem_BQP_iff_phase.mpr ⟨phaseFirst, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [encBits_apply, acceptProb_phaseFirst]
    simp only [show x.headD false = true from hx, ite_true]
    norm_num
  · rw [encBits_apply, acceptProb_phaseFirst]
    simp only [show x.headD false = false from Bool.eq_false_iff.mpr hx, Bool.false_eq_true,
      ite_false]
    norm_num

-- The real simulation of `phaseFirst` accepts with the same probabilities, with four gates.
example (x : List Bool) : phaseFirst.realify.acceptProb x = if x.headD false then 1 else 0 := by
  rw [UniformPhaseCircuitFamily.acceptProb_realify, acceptProb_phaseFirst]
example (n : ℕ) : (phaseFirst.realify.gates n).length = 4 := rfl

end CslibFrontierTests.QuantumRealEncoding
