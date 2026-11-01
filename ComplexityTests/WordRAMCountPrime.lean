/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.ExactTriangle.CountPrime
import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Program

/-!
# Complete native modular-count execution regressions

The actual initialized code computes residues, tables, padding, every Strassen product and
the coefficient sum. Triple enumeration appears only in one independent test expectation;
the tested program contains the seven-product recursive matrix multiplication instead.
These interpreter examples do not supply the general native correctness or resource theorem.
-/

-- Deliberately execute the real native interpreter for complete counter examples.
set_option linter.hashCommand false

namespace ComplexityTests.WordRAMCountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

private def weights (xs : List ℤ) : List ℕ := xs.map encode

private def initial (n p : ℕ) (a b c : List ℤ) : Data 128 :=
  .init ([n, p] ++ weights a ++ weights b ++ weights c ++ List.replicate 256 99 ++ [777])

-- A genuinely signed zero-weight triangle; the complete leaf uses modulus three.
#guard match entryProgram.eval 20 20000 (initial 1 3 [-2] [1] [1]) with
  | some (y, _) => y.regs Reg.result == 1 && y.mem 3 == encode (-2) &&
      y.mem 4 == encode 1 && y.mem 5 == encode 1 && y.mem 262 == 777
  | none => false

-- A modular false positive counts for p=3 but not p=5; the integer sum is nonzero.
#guard match entryProgram.eval 20 20000 (initial 1 3 [-2] [1] [4]) with
  | some (y, _) => y.regs Reg.result == 1
  | none => false

#guard match entryProgram.eval 20 20000 (initial 1 5 [-2] [1] [4]) with
  | some (y, _) => y.regs Reg.result == 0
  | none => false

private def a : List ℤ := [-1, 0, 2, -3]
private def b : List ℤ := [1, -2, 3, 0]
private def c : List ℤ := [0, 4, -2, 1]

private def expected : ℕ := ((List.range 2).flatMap fun i => (List.range 2).flatMap
    fun j => (List.range 2).map fun k => (a[i * 2 + j]! + b[j * 2 + k]! + c[i * 2 + k]!) % 2)
  |>.count 0

-- Independent finite semantics agree on the asymmetric signed example; neither computation
-- is an assumption passed to the native program above or below.
example : Cslib.Algorithms.ExactTriangle.CountPrime.count 2 1
      (fun i j : Fin 2 => a[i.val * 2 + j.val]!)
      (fun i j : Fin 2 => b[i.val * 2 + j.val]!)
      (fun i j : Fin 2 => c[i.val * 2 + j.val]!) = 4 ∧
    Cslib.Algorithms.ExactTriangle.countZeroMod
      (fun i j : Fin 2 => a[i.val * 2 + j.val]!)
      (fun i j : Fin 2 => b[i.val * 2 + j.val]!)
      (fun i j : Fin 2 => c[i.val * 2 + j.val]!) 2 = 4 := by decide

example : Nat.Morton.index 1 2 = 6 ∧ Nat.Morton.index 2 1 = 9 ∧
    Nat.Morton.row 15 = 3 ∧ Nat.Morton.column 15 = 3 := by decide

-- Asymmetric BC verifies that the native construction really performs the required transpose.
#guard match entryProgram.eval 20 100000 (initial 2 2 a b c) with
  | some (y, _) => y.regs Reg.result == expected &&
      y.mem 3 == encode (-1) && y.mem 14 == encode 1 && y.mem 271 == 777
  | none => false

-- Side three forces actual zero padding to side four and two explicit recursion levels.
#guard match entryProgram.eval 24 400000
    (initial 3 2 (List.replicate 9 (-1)) (List.replicate 9 1) (List.replicate 9 0)) with
  | some (y, _) => y.regs Reg.result == 27 && y.mem 286 == 777
  | none => false

-- No pairs exist for side zero; the actual power, padding and leaf paths still terminate.
#guard match entryProgram.eval 20 20000 (initial 0 2 [] [] []) with
  | some (y, _) => y.regs Reg.result == 0 && y.mem 259 == 777
  | none => false

end ComplexityTests.WordRAMCountPrime
