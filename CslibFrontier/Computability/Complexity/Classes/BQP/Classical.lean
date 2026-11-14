/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BQP
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Circuit
import CslibFrontier.Computability.Complexity.Problems.CircuitValue.Completeness

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
With Hadamard gates preparing the random bits, the same compilation gives `BPP ⊆ BQP`
(`Cslib.Complexity.BPP_subset_BQP`, in `CslibFrontier.Computability.Complexity.Classes.QMA.MA`).

## Main results

* `Cslib.Complexity.exists_uniformCircuitFamily`: exact quantum computation of polynomial-time
  Boolean functions.
* `Cslib.Complexity.P_subset_BQP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

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
