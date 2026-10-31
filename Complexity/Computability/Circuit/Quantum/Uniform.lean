/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Code
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time uniform families of quantum circuits

A uniform family of quantum circuits (`Cslib.Quantum.UniformCircuitFamily`) gives, for inputs of
length `n`, an `m`-qubit register with `m = width n ≥ n` and the gate codes `gates n` of a circuit
over the Hadamard, NOT, CNOT and Toffoli gates
(`Complexity/Computability/Circuit/Quantum/Code.lean`).
Both are computed from `n`, written in unary, by a polynomial-time machine. This follows the
library's convention for uniform Boolean circuits
(`Cslib.Complexity.CircuitValue.exists_uniformCircuits`) and [Arora, Barak][AroraBarak09],
Chapter 10: a polynomial-time machine that, given `n` in unary, outputs the descriptions of the
gates. Wires and the register width are written in unary, so they are
polynomially bounded. On an input word `x` the family runs its circuit for `n = |x|` from
`|x 0^{m - n}⟩` and accepts when the final measurement finds qubit `0` in state `1`
(`Cslib.Quantum.UniformCircuitFamily.acceptProb`).

Appending a NOT gate on qubit `0` gives a family with complementary acceptance probability
(`Cslib.Quantum.UniformCircuitFamily.appendNot`).

## Main definitions

* `Cslib.Quantum.encGateCode`: the encoding of gate codes.
* `Cslib.Quantum.UniformCircuitFamily`: polynomial-time uniform families of circuits.
* `Cslib.Quantum.UniformCircuitFamily.acceptProb`: the acceptance probability on an input word.
* `Cslib.Quantum.UniformCircuitFamily.appendNot`: the family with a final NOT on qubit `0`.

## Main results

* `Cslib.Quantum.UniformCircuitFamily.acceptProb_appendNot`: the acceptance probability of
  `appendNot` is one minus that of the family.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- The encoding of gate codes `(h, t, cs)`: the Hadamard flag, then the target and the list of
controls in unary. -/
abbrev encGateCode : GateCode ↪ List Bool := encPair encBool (encPair encUnary (encList encUnary))

/-- A **polynomial-time uniform family of quantum circuits** over the Hadamard, NOT, CNOT and
Toffoli gates. On inputs of length `n` it uses a register of `width n` qubits, at least `n` and at
least one, and the well-formed gate codes `gates n`. The width and the gate codes are computed from
`n` in unary in polynomial time. -/
structure UniformCircuitFamily where
  /-- The number of qubits used on inputs of length `n`. -/
  width : ℕ → ℕ
  /-- The gate codes of the circuit used on inputs of length `n`, applied first to last. -/
  gates : ℕ → List GateCode
  computableInPolyTime_width : ComputableInPolyTime width encUnary encUnary
  computableInPolyTime_gates : ComputableInPolyTime gates encUnary (encList encGateCode)
  le_width : ∀ n, n ≤ width n
  width_pos : ∀ n, 0 < width n
  wellFormed : ∀ n, ∀ g ∈ gates n, g.WellFormed (width n)

namespace UniformCircuitFamily

/-- The **acceptance probability** of the family on the input word `x`: its circuit for inputs of
length `|x|`, started in `|x 0^{m - |x|}⟩`, ends with qubit `0` measured in state `1`. -/
noncomputable def acceptProb (F : UniformCircuitFamily) (x : List Bool) : ℝ :=
  Quantum.acceptProb (F.width x.length) (F.gates x.length) x

theorem acceptProb_nonneg (F : UniformCircuitFamily) (x : List Bool) : 0 ≤ F.acceptProb x :=
  Quantum.acceptProb_nonneg _ _ _

theorem acceptProb_le_one (F : UniformCircuitFamily) (x : List Bool) : F.acceptProb x ≤ 1 :=
  Quantum.acceptProb_le_one _ _ _

/-- The family with a final NOT gate on qubit `0`. -/
def appendNot (F : UniformCircuitFamily) : UniformCircuitFamily where
  width := F.width
  gates n := F.gates n ++ [(false, 0, [])]
  computableInPolyTime_width := F.computableInPolyTime_width
  computableInPolyTime_gates := by
    have := F.computableInPolyTime_gates
    fun_prop
  le_width := F.le_width
  width_pos := F.width_pos
  wellFormed n g hg := by
    rcases List.mem_append.mp hg with hg | hg
    · exact F.wellFormed n g hg
    · rw [List.mem_singleton.mp hg]
      simp [GateCode.WellFormed, F.width_pos n]

/-- **A final NOT on qubit `0` complements the acceptance probability.** -/
@[simp] theorem acceptProb_appendNot (F : UniformCircuitFamily) (x : List Bool) :
    F.appendNot.acceptProb x = 1 - F.acceptProb x :=
  acceptProb_append_not (F.width_pos _) _ _

end UniformCircuitFamily

end Cslib.Quantum
