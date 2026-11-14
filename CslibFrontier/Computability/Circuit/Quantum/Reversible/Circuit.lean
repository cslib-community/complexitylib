/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Reversible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Reversible compilation with a designated output

Compile a De Morgan circuit into NOT, CNOT and Toffoli gates, then move its first output to
qubit zero. The compiler uses one fresh qubit per Boolean gate and a final zero qubit. It also
handles malformed Boolean codes using the existing default-false evaluation semantics.

This is the compiler previously placed with `P ⊆ BQP`; its implementation and correctness
statements are unchanged. The underlying gate simulation follows [Arora, Barak][AroraBarak09],
Chapter 10. Concrete bounds for the emitted code are in `Reversible.Resources`.

## Main definitions

* `Cslib.Quantum.Reversible.circuitCodes`: compilation followed by output relocation.
* `Cslib.Quantum.UniformCircuitFamily.ofBooleanCircuits`: the compiled uniform family.

## Main results

* `Cslib.Quantum.Reversible.acceptProb_circuitCodes`: exact output semantics.
* `Cslib.Quantum.Reversible.computableInPolyTime_circuitCodes`: native uniform compilation.
* `Cslib.Quantum.UniformCircuitFamily.acceptProb_ofBooleanCircuits`: family correctness.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Quantum

open Circuits Circuits.Boolean GateCode Turing.MultiTapeTM

namespace Reversible

/-- The qubit holding output wire `o` of a gate list compiled with zero qubit `z`. -/
@[expose] def outQubit (z o : ℕ) : ℕ := min z o

/-- **The quantum gate codes of a De Morgan circuit code** on `n` inputs: compile its gates onto
`n + G` qubits, with zero qubit `n + G`, and swap its first output wire into qubit `0`. -/
@[expose] def circuitCodes (n : ℕ) (code : List (Op × List ℕ) × List ℕ) : List GateCode :=
  codes n (n + code.1.length) code.1 ++
    if outQubit (n + code.1.length) (code.2.getD 0 0) = 0 then []
    else swapCodes (outQubit (n + code.1.length) (code.2.getD 0 0))

theorem isClassical_circuitCodes (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    IsClassical (n + code.1.length + 1) (circuitCodes n code) := by
  refine IsClassical.append.mpr ⟨isClassical_codes le_rfl (by omega), ?_⟩
  split_ifs with h
  · intro g hg
    simp at hg
  · exact isClassical_swapCodes (Nat.pos_of_ne_zero h) (by unfold outQubit; omega)

/-- **The compiled circuit reads the De Morgan circuit's output**: started from the input `x` of
length `n`, it accepts with probability `1` when the first output wire of the code is true on `x`,
and `0` otherwise. -/
theorem acceptProb_circuitCodes {n : ℕ} (code : List (Op × List ℕ) × List ℕ) {x : List Bool}
    (hx : x.length = n) :
    acceptProb (n + code.1.length + 1) (circuitCodes n code) x =
      if evalOutput x code.1 (code.2.getD 0 0) then 1 else 0 := by
  set W := n + code.1.length + 1
  set z := n + code.1.length
  set o := code.2.getD 0 0
  have hX (p : ℕ) : readBit (inputState W x) p = x.getD p false :=
    readBit_inputState (by omega) p
  have hcodes := readBit_classicalRun_codes (W := W) (gates := code.1) le_rfl (by omega) hx hX
  -- the compiled gates leave the output wire on `outQubit z o`
  have hout : readBit (classicalRun (codes n z code.1) (inputState W x)) (outQubit z o) =
      evalOutput x code.1 o := by
    have hlen : (evalCode interpretation false x code.1).length = z := by simp [hx, z]
    rw [hcodes, evalOutput]
    unfold outQubit
    rcases le_or_gt z o with h | h
    · rw [min_eq_left h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · rw [min_eq_right h.le]
  have h0 : 0 < W := by omega
  -- qubit `0` of the final basis state
  have hfinal : readBit (classicalRun (circuitCodes n code) (inputState W x)) 0 =
      evalOutput x code.1 o := by
    rw [circuitCodes, classicalRun_append]
    split_ifs with h
    · rw [classicalRun_nil, ← h, hout]
    · rw [readBit_classicalRun_swapCodes (Nat.pos_of_ne_zero h) (by unfold outQubit; omega), hout]
  have hmem : classicalRun (circuitCodes n code) (inputState W x) ∈ accepting W ↔
      evalOutput x code.1 o = true := by
    rw [mem_accepting h0,
      ← readBit_fin (classicalRun (circuitCodes n code) (inputState W x)) (⟨0, h0⟩ : Fin W)]
    change readBit _ 0 = true ↔ _
    rw [hfinal]
  rw [acceptProb, Circuit.run_ofCodes (isClassical_circuitCodes n code), measureProb_ket]
  exact if_congr hmem rfl rfl

variable {γ : Type} {enc : γ ↪ List Bool}

/-- **The compilation of circuit codes runs in polynomial time.** -/
theorem computableInPolyTime_circuitCodes {n : γ → ℕ}
    {code : γ → List (Op × List ℕ) × List ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hcode : ComputableInPolyTime code enc encCode) :
    ComputableInPolyTime (fun c => circuitCodes (n c) (code c)) enc (encList encGateCode) := by
  have hz : ComputableInPolyTime (fun c => n c + (code c).1.length) enc encUnary := by fun_prop
  have hgates := computableInPolyTime_codes hn hz (gates := fun c => (code c).1) (by fun_prop)
  have hout : ComputableInPolyTime (fun c => outQubit (n c + (code c).1.length)
      ((code c).2.getD 0 0)) enc encUnary := by
    unfold outQubit
    fun_prop
  simp only [circuitCodes, swapCodes]
  fun_prop

end Reversible

namespace UniformCircuitFamily

/-- **The quantum family of a polynomial-time uniform family of De Morgan circuits**: the circuit
for inputs of length `n` compiled into reversible gates. -/
@[expose] def ofBooleanCircuits (circuits : (n : ℕ) → Circuits.Circuit signature n 1)
    (hcode : ComputableInPolyTime (fun n => (circuits n).code) encUnary encCode) :
    UniformCircuitFamily where
  width n := n + (circuits n).code.1.length + 1
  gates n := Reversible.circuitCodes n (circuits n).code
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_gates := Reversible.computableInPolyTime_circuitCodes (by fun_prop) hcode
  le_width n := by omega
  width_pos n := by omega
  wellFormed n g hg := (Reversible.isClassical_circuitCodes n _ g hg).2

/-- The family of compiled circuits accepts with probability `1` or `0`, according to the output of
the De Morgan circuit for the input's length. -/
theorem acceptProb_ofBooleanCircuits (circuits : (n : ℕ) → Circuits.Circuit signature n 1)
    (hcode : ComputableInPolyTime (fun n => (circuits n).code) encUnary encCode) (x : List Bool) :
    (ofBooleanCircuits circuits hcode).acceptProb x =
      if (circuits x.length).eval interpretation (fun i => x[i]) 0 then 1 else 0 := by
  rw [acceptProb]
  change Quantum.acceptProb (x.length + (circuits x.length).code.1.length + 1)
    (Reversible.circuitCodes x.length (circuits x.length).code) x = _
  rw [Reversible.acceptProb_circuitCodes _ rfl, Circuits.Circuit.eval_eq_evalOutput,
    show (List.ofFn fun i : Fin x.length => x[i]) = x from List.ofFn_getElem]
  congr 3

end UniformCircuitFamily

end Cslib.Quantum
