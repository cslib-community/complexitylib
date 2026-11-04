/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Circuit.Quantum.Reversible
import Complexity.Computability.Complexity.Problems.CircuitValue.Completeness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Classical computation in `BQP`

Every polynomial-time Boolean function is computed **exactly** by a uniform family of quantum
circuits over the NOT, CNOT and Toffoli gates (`Cslib.Complexity.exists_uniformCircuitFamily`):
its acceptance probability is `1` on the instances where the function is true and `0` elsewhere.
Hence `P ⊆ BQP` (`Cslib.Complexity.P_subset_BQP`).

The family compiles the polynomial-time uniform Boolean circuits of
`Cslib.Complexity.CircuitValue.exists_uniformCircuits`. On inputs of length `n`, the De Morgan
circuit with `G` gates is compiled into reversible gates on `n + G + 1` qubits
(`Cslib.Quantum.Reversible.codes`): gate `j` writes the fresh qubit `n + j`, and the last qubit
stays zero. Three CNOT gates then swap the output wire into qubit `0`
(`Cslib.Quantum.Reversible.circuitCodes`). A classical circuit maps the input basis state to a basis
state, so the final measurement reads the circuit's output with certainty. This is the gate-by-gate
simulation of Boolean circuits by permutation gates in [Arora, Barak][AroraBarak09], Chapter 10
(Section 20.4 of the January 2007 web draft, used there for Theorem 20.17, `BPP ⊆ BQP`), without
the final uncomputation, which is unnecessary when only qubit `0` is measured.

## Main definitions

* `Cslib.Quantum.Reversible.circuitCodes`: the quantum gate codes of a De Morgan circuit code.
* `Cslib.Quantum.UniformCircuitFamily.ofBooleanCircuits`: the family of a polynomial-time uniform
  family of De Morgan circuits.

## Main results

* `Cslib.Quantum.Reversible.acceptProb_circuitCodes`: the compiled circuit accepts with
  probability `1` or `0`, according to the output of the De Morgan circuit.
* `Cslib.Complexity.exists_uniformCircuitFamily`: exact quantum computation of polynomial-time
  Boolean functions.
* `Cslib.Complexity.P_subset_BQP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Quantum

open Circuits Circuits.Boolean GateCode Turing.MultiTapeTM

namespace Reversible

/-- The qubit holding output wire `o` of a gate list compiled with zero qubit `z`. -/
def outQubit (z o : ℕ) : ℕ := min z o

/-- **The quantum gate codes of a De Morgan circuit code** on `n` inputs: compile its gates onto
`n + G` qubits, with zero qubit `n + G`, and swap its first output wire into qubit `0`. -/
def circuitCodes (n : ℕ) (code : List (Op × List ℕ) × List ℕ) : List GateCode :=
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
  have hX (p : ℕ) : readBit (inputState W x) p = x.getD p false := by
    by_cases hp : p < W
    · rw [readBit_of_lt _ hp]
      rfl
    · rw [readBit_of_le _ (not_lt.mp hp), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega)]
      rfl
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
def ofBooleanCircuits (circuits : (n : ℕ) → Circuits.Circuit signature n 1)
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

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Exact quantum computation of polynomial-time Boolean functions**: a polynomial-time Boolean
function is computed by a polynomial-time uniform family of NOT, CNOT and Toffoli circuits that
accepts with probability `1` where the function is true and `0` where it is false. -/
theorem exists_uniformCircuitFamily {f : α → Bool} (hf : ComputableInPolyTime f enc encBool) :
    ∃ F : UniformCircuitFamily, ∀ a, F.acceptProb (enc a) = if f a then 1 else 0 := by
  obtain ⟨circuits, hcode, hcorrect⟩ := CircuitValue.exists_uniformCircuits hf
  exact ⟨UniformCircuitFamily.ofBooleanCircuits circuits hcode, fun a => by
    rw [UniformCircuitFamily.acceptProb_ofBooleanCircuits, hcorrect]⟩

/-- **`P ⊆ BQP`**: deterministic polynomial time is contained in bounded-error quantum polynomial
time, with zero error. -/
theorem P_subset_BQP : P enc ⊆ BQP enc := by
  rintro A ⟨f, hf, hA⟩
  obtain ⟨F, hF⟩ := exists_uniformCircuitFamily hf
  refine ⟨F, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · rw [hF, (hA a).mp ha]
    norm_num
  · rw [hF, show f a = false by simpa [hA a] using ha]
    norm_num

end Cslib.Complexity
