/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Flat

-- Full-program regressions intentionally evaluate the native interpreter at elaboration time.
set_option linter.hashCommand false

/-!
# Executed native shared-encoding regressions

These clients start with the actual unsigned input convention. The interpreter charges every
native arithmetic block, branch, loop and store. They compare observable memory after execution.
-/

namespace ComplexityTests.SchonhageEncoding

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

private def observe (side : Bool) (w L fuel : ℕ) (a : Fin (7 ^ L) → ℤ) :
    Option ((List ℤ × Bool) × ℕ) :=
  ((program side).eval w fuel (State.init (input L a)).data).map fun (y, time) =>
    (((List.range (10 ^ L)).map fun i => decode (y.mem (outputBase L + i)),
      decide (y.mem 0 = (input L a).length ∧ y.mem 1 = L ∧
        (∀ i : Fin (7 ^ L), y.mem (2 + i.val) = encode (a i)) ∧
        y.mem (scratchBase L + 10 ^ L) = 0)), time)

-- Kernel reduction follows the finite form dispatch and all actual signed arithmetic blocks.
-- Its nested code and loop reductions exceed the default elaborator recursion depth.
set_option maxRecDepth 16384 in
example : observe false 8 0 2 (fun _ => -3) = some (([-3], true), 31) := by
  decide +kernel

-- These checks run the actual interpreter as regression tests; the general execution
-- theorems are kernel checked separately. VM evaluation avoids quadratic kernel reduction
-- through thousands of functional register updates in each concrete full-program test.
#guard (observe false 12 1 16 (fun i => (i.val : ℤ) + 1)).map Prod.fst ==
  some ([5, 6, 1, 8, 9, 2, -7, -9, 3, -6], true)

#guard (observe true 12 1 16 (fun i => (i.val : ℤ) + 1)).map Prod.fst ==
  some ([5, 7, -6, 7, 9, -10, 1, 2, 3, 6], true)

#guard (observe false 12 1 16 (fun i => -((i.val : ℤ) + 1))).map Prod.fst ==
  some ([-5, -6, -1, -8, -9, -2, 7, 9, -3, 6], true)

-- At width four, the computed scratch address 19 overflows; width five is the first working
-- width for this zero-valued depth-one client. Every output and the adjacent frame are checked.
#guard observe false 4 1 16 (fun _ => 0) == none
#guard (observe false 5 1 16 (fun _ => 0)).map Prod.fst ==
  some (List.replicate 10 0, true)

open Cslib.Algorithms.MatrixMultiplication.Schonhage

private def signedLeft (u : LeftStr 2) : ℤ :=
  if u 0 = .x 0 then -2 else if u 1 = .p 1 0 then 3 else 1

private def signedRight (u : RightStr 2) : ℤ :=
  if u 0 = .q 0 1 then -3 else if u 1 = .y 2 then 2 else 0

private def leafAt (i : Fin (10 ^ 2)) : Leaf 2 :=
  fun ℓ => termAt (finFunctionFinEquiv.symm i ℓ)

-- Output addresses can be calculated by ordinary executable finite alphabet numberings.
#guard (leafIndex (fun _ : Fin 2 => Term.P0)).val == 99
#guard (leafIndex (fun _ : Fin 2 => Term.P 0 0)).val == 0
#guard (leftDigits.symm (.p 1 1)).val == 6

-- Two stages alternate buffers and then copy backward from scratch to output. The expected
-- values use the unchanged public mathematical encodings, including every one of the 100 leaves.
#guard (observe false 16 2 128 (fun i => signedLeft
    (fun ℓ => leftAt (finFunctionFinEquiv.symm i ℓ)))).map Prod.fst ==
  some (List.ofFn (fun i => encodingL signedLeft (leafAt i)), true)

#guard (observe true 16 2 128 (fun i => signedRight
    (fun ℓ => rightAt (finFunctionFinEquiv.symm i ℓ)))).map Prod.fst ==
  some (List.ofFn (fun i => encodingR signedRight (leafAt i)), true)

private def copyObserve (s d : ℕ) : Option (List ℕ × Bool × ℕ) :=
  let x : Data 7 := ⟨![s, d, 3, 0, 0, 0, 0],
    fun a => if s ≤ a ∧ a < s + 3 then a - s + 1 else 99⟩
  (ArrayCopy.program.eval 8 4 x).map fun (y, time) =>
    (List.ofFn (fun i : Fin 3 => y.mem (d + i.val)),
      decide ((∀ i : Fin 3, y.mem (s + i.val) = i.val + 1) ∧
        y.mem 0 = 99 ∧ y.mem 12 = 99), time)

-- Execute the generalized helper in both disjoint orders and with equal blocks. The old
-- forward-copy theorem remains available; these also check nonzero words outside the frame.
#guard copyObserve 4 8 == some ([1, 2, 3], true, 25)
#guard copyObserve 8 4 == some ([1, 2, 3], true, 25)
#guard copyObserve 4 4 == some ([1, 2, 3], true, 25)

-- Nonzero garbage immediately beyond the two work buffers survives the complete encoder.
#guard ((program false).eval 16 128
    ((State.init (input 2 (fun _ => -1)) : State 32).data.write
      (scratchBase 2 + 10 ^ 2) 91)).map
    (fun (y, _) => y.mem (scratchBase 2 + 10 ^ 2)) == some 91

#guard observe true 8 0 2 (fun _ => -4) == some (([-4], true), 31)

/-- The explicit width condition itself has a checked boundary. -/
example : ¬Fits 9 (addressBound 1) ∧ Fits 10 (addressBound 1) := by decide

/-- A kernel-checked zero-depth flat execution with a negative value, derived from the
general theorem rather than from VM evaluation. All calling/width premises are discharged. -/
example : ∃ y : Data 32, ∃ n, n ≤ 240 ∧
    Runs 8 ((program false).program output)
      (State.init (inputL (fun _ : LeftStr 0 => -3))) ⟨(program false).size, y⟩ n ∧
    Executes 8 ((program false).program output)
      (State.init (inputL (fun _ : LeftStr 0 => -3))) 3 (n + 1) ∧ y.mem 3 = 7 := by
  obtain ⟨_, y, n, hn, hr, he, hv, _⟩ := runs_left (w := 6) (by decide)
    (fun _ : LeftStr 0 => -3) 3 (by decide) (by intro u; decide) (by decide) (by decide)
  refine ⟨y, n, ?_, hr, he, ?_⟩
  · simpa only [timeBound, pow_zero, Nat.reduceAdd, Nat.mul_one] using hn
  · have hidx : (leafIndex (Fin.elim0 : Leaf 0)).val = 0 := by
      have := (leafIndex (Fin.elim0 : Leaf 0)).isLt
      norm_num at this ⊢
    have h := hv (Fin.elim0 : Leaf 0)
    have hval : encodingL (fun _ : LeftStr 0 => -3) Fin.elim0 = -3 :=
      encodeWith_zero phi _ _
    have henc : encode (-3) = 7 := by decide
    simpa only [outputBase, pow_zero, hidx, hval, henc, Nat.reduceAdd] using h

/-- A nonvacuous two-stage client of the complete flat execution theorem. The checked signed
array has a zero `P0,P0` leaf through cancellation and also many nonzero leaves in the VM test. -/
example : ∃ y : Data 32, ∃ n, n ≤ 72000 ∧
    Runs 18 ((program false).program output) (State.init (inputL signedLeft))
      ⟨(program false).size, y⟩ n ∧
    Executes 18 ((program false).program output) (State.init (inputL signedLeft)) 51 (n + 1) ∧
      y.mem (outputBase 2 + (leafIndex (fun _ : Fin 2 => Term.P0)).val) = 0 := by
  obtain ⟨_, y, n, hn, hr, he, hv, _⟩ := runs_left (w := 16) (by decide)
    signedLeft 3 (by decide) (by decide +kernel) (by decide) (by decide)
  refine ⟨y, n, ?_, hr, he, ?_⟩
  · norm_num [timeBound] at hn ⊢
    exact hn
  · have hmath : encodingL signedLeft (fun _ : Fin 2 => Term.P0) = 0 := by decide +kernel
    simpa only [hmath, show encode 0 = 0 from rfl] using hv (fun _ : Fin 2 => Term.P0)

end ComplexityTests.SchonhageEncoding
