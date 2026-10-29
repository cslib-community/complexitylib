/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.CodeSubstitution
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Prefix-hardwiring clients

The example uses both fixed Boolean constants, a live input, an internal wire and repeated
designated outputs. Empty prefixes and zero live-input counts still retain two shared constants.
-/

namespace ComplexityTests.CodeSubstitution

open Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

private def exampleCode : List (Op × List ℕ) × List ℕ :=
  ([(.and, [0, 2]), (.or, [3, 1])], [4, 0, 2, 4])

private def exampleCircuit : Circuit signature 3 4 :=
  (Circuit.ofCode 3 4 exampleCode).get (by decide +kernel)

example : exampleCircuit.code = exampleCode := by decide +kernel

example : prefixCode [true, false] 1 exampleCode =
    ([(.const false, []), (.const true, []), (.and, [2, 0]), (.or, [3, 1])],
      [4, 2, 0, 4]) := by decide +kernel

example : Circuit.ofCode 1 4 (prefixCode [true, false] 1 exampleCircuit.code) =
    some (prefixCircuit (n := 1) [true, false] exampleCircuit) ∧
    (prefixCircuit (n := 1) [true, false] exampleCircuit).size = 2 + exampleCircuit.size :=
  ⟨ofCode_prefixCode _ _, size_prefixCircuit _ _⟩

example : (prefixCircuit (n := 1) [true, false] exampleCircuit).size = 4 := by decide +kernel

example : List.ofFn
    ((prefixCircuit (n := 1) [true, false] exampleCircuit).eval interpretation ![false]) =
    [false, true, false, false] := by decide +kernel

example : List.ofFn
    ((prefixCircuit (n := 1) [true, false] exampleCircuit).eval interpretation ![true]) =
    [true, true, true, true] := by decide +kernel

example (x : Fin 1 → Bool) :
    (prefixCode [true, false] 1 exampleCircuit.code).2.map
        (evalOutput (List.ofFn x) (prefixCode [true, false] 1 exampleCircuit.code).1) =
      List.ofFn
        ((prefixCircuit (n := 1) [true, false] exampleCircuit).eval interpretation x) := by
  rw [evalOutputs_prefixCode, eval_prefixCircuit]

example : prefixCode [] 0 ([], []) = ([(.const false, []), (.const true, [])], []) := rfl

example : prefixCode [false, true] 0 ([], [0, 1, 0]) =
    ([(.const false, []), (.const true, [])], [0, 1, 0]) := by decide +kernel

-- Input counts use binary encodings; the certificate does not enumerate all input wires.
example : ComputableInPolyTime
    (fun p : (List Bool × ℕ) × (List (Op × List ℕ) × List ℕ) => prefixCode p.1.1 p.1.2 p.2)
    (encPair (encPair encBits encNat) encCode) encCode := by fun_prop

end ComplexityTests.CodeSubstitution
