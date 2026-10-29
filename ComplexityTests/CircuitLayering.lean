/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Layered.Compile.Correctness
import Complexity.Computability.Circuit.Boolean.Layered.Compile.PolyTime
import Complexity.Computability.Circuit.Boolean.Layered.Compile.Size
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
These instances exercise the actual raw compiler, together with typed correctness and native
runtime certificates. Invalid codes test total runtime only; they need not preserve the fallback
semantics of a different raw interpreter.
-/

namespace ComplexityTests.CircuitLayering

open Cslib.Circuits Boolean Boolean.Layered Turing.MultiTapeTM

private def deadWiring : Circuit signature 2 3 :=
  (Circuit.ofCode (σ := signature) 2 3
    ([(.not, [0]), (.not, [2]), (.not, [3]), (.not, [4])], [1, 0, 1])).get (by decide)

-- Kernel reduction checks the concrete compiler output without trusting native evaluation.
-- Deeper unused gates do not spend a key transition. Ordering and repetitions remain free.
example : deadWiring.program.depth = 4 ∧ deadWiring.depth = 0 := by decide +kernel
example : compile 2 deadWiring.code = ([], [1, 0, 1]) := by decide +kernel
example : select (eval [false, true] (compile 2 deadWiring.code).1)
    (compile 2 deadWiring.code).2 = [true, false, true] := by decide +kernel

private def noOutputs : Circuit signature 2 0 := ⟨deadWiring.program, Fin.elim0⟩

example : noOutputs.size = 4 ∧ noOutputs.depth = 0 := by decide +kernel
example : compile 2 noOutputs.code = ([], []) := by decide +kernel

private def constants : Circuit signature 0 2 :=
  (Circuit.ofCode (σ := signature) 0 2
    ([(.const true, []), (.const false, [])], [1, 0])).get (by decide)

-- The first layer creates working slots from no inputs; no initialization level is added.
example : WellFormed 0 (compile 0 constants.code).1 ∧
    (compile 0 constants.code).1.length = 2 :=
  ⟨wellFormed_compile constants, by decide +kernel⟩
example : select (eval [] (compile 0 constants.code).1) (compile 0 constants.code).2 =
    [false, true] := by decide +kernel

private def disjunction : Circuit signature 2 1 :=
  (Circuit.ofCode (σ := signature) 2 1 ([(.or, [0, 1])], [2])).get (by decide)

-- OR needs both scratch slots and both microlevels. Check all four assignments.
example : ∀ a b : Bool,
    select (eval [a, b] (compile 2 disjunction.code).1) (compile 2 disjunction.code).2 =
      [a || b] := by decide +kernel

private def shared : Circuit signature 2 4 :=
  (Circuit.ofCode (σ := signature) 2 4
    ([(.or, [0, 1]), (.and, [2, 0]), (.not, [2]), (.or, [3, 4]), (.and, [5, 0])],
      [5, 2, 5, 6])).get (by decide)

-- A shared diamond, an edge skipping several depths, and a repeated output retain their DAG
-- semantics. Every original gate has a single persistent value slot.
example : shared.depth = 4 ∧ (compile 2 shared.code).1.length = 8 := by decide +kernel
example : ∀ a b : Bool,
    select (eval [a, b] (compile 2 shared.code).1) (compile 2 shared.code).2 =
      let t := a || b
      let u := (t && a) || !t
      [u, t, u, u && a] := by decide +kernel

example (x : Fin 2 → Bool) :
    select (eval (List.ofFn x) (compile 2 shared.code).1) (compile 2 shared.code).2 =
      List.ofFn (shared.eval interpretation x) ∧
    ∀ i ∈ (compile 2 shared.code).2,
      i < (eval (List.ofFn x) (compile 2 shared.code).1).length :=
  ⟨select_eval_compile shared x,
    by simpa only [length_eval, List.length_ofFn] using outputs_valid_compile shared⟩

-- The size bound includes the complete encoded result, including binary repeated selectors.
example :
    shared.size = 5 ∧ shared.depth = 4 ∧
    (encCompiled (compile 2 shared.code)).length ≤ 28249 := by
  have hsize : shared.size = 5 := by decide +kernel
  have hdepth : shared.depth = 4 := by decide +kernel
  refine ⟨hsize, hdepth, (length_encCompiled_compile_le shared).trans ?_⟩
  rw [hsize, hdepth]
  decide +kernel

-- Malformed huge binary references do not turn into huge unary clocks.
example : depthCode 0 ([(.or, [2 ^ 100, 2 ^ 101])], [0]) = 1 := by decide +kernel
example : (compile 0 ([(.or, [2 ^ 100, 2 ^ 101])], [0])).1.length = 2 := by decide +kernel

-- The original raw interpreter defaults a missing argument to false; the compiler's raw
-- fallback uses wire 0. Correctness is therefore intentionally stated for typed codes.
example : evalCode interpretation false [true] [(.not, [])] = [true, true] := by decide +kernel
example : select (eval [true] (compile 1 ([(.not, [])], [1])).1)
    (compile 1 ([(.not, [])], [1])).2 = [false] := by decide +kernel

-- One actual native compiler handles varying input and output counts, including invalid code.
example : ComputableInPolyTime
    (fun p : ℕ × (List (Op × List ℕ) × List ℕ) => compile p.1 p.2)
    (encPair encUnary encCode) encCompiled := by fun_prop

end ComplexityTests.CircuitLayering
