/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Basic
public import Complexity.Computability.Circuit.Pi

/-!
# NAND in the De Morgan basis

One AND gate followed by one NOT gate implements NAND. The construction uses the existing
single-gate and sequential circuit constructors, so its size counts both gates.

## Main definitions

* `Cslib.Circuits.Boolean.nandCircuit`: the two-gate NAND circuit.

## Main results

* `Cslib.Circuits.Boolean.eval_nandCircuit`: Boolean NAND semantics.
* `Cslib.Circuits.Boolean.size_nandCircuit`: exactly two gates.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- NAND, implemented by one AND gate followed by one NOT gate. -/
def nandCircuit : Circuit signature 2 1 :=
  (Circuit.oneGate (σ := signature) .not (fun _ => 0)).comp (Circuit.oneGate .and id)

/-- `nandCircuit` computes the NAND of its two input bits. -/
@[simp] theorem eval_nandCircuit (x : Fin 2 → Bool) (j : Fin 1) :
    nandCircuit.eval interpretation x j = !(x 0 && x 1) := rfl

/-- `nandCircuit` has `2` gates. -/
@[simp] theorem size_nandCircuit : nandCircuit.size = 2 := rfl

end Cslib.Circuits.Boolean
