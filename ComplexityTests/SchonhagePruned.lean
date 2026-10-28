/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

-- Full controller regressions evaluate the actual native interpreter at elaboration time.
set_option linter.hashCommand false

/-! Actual native controller regressions, including shared and repeated query suffixes. -/

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

namespace ComplexityTests.SchonhagePruned

-- Query codes use least-significant-first digits and retain the encoder's wildcard digit nine.
example : queryAt (L := 2) (90 : Fin 100) = ![.z 0 0, .z0] := by decide +kernel
example : (requested (L := 2) ([90, 9, 90] : List (Fin 100))).card = 2 := by decide +kernel

private def observe (w L fuel : ℕ) (a b : Fin (10 ^ L) → ℤ) (qs : List (Fin (10 ^ L))) :=
  (program.eval w fuel (State.init (input L a b qs) : State registers).data).map fun (y, time) =>
    ((List.range qs.length).map fun i => decode (y.mem (outputBase L qs.length + i)), time)

private def answers (w L fuel : ℕ) (a b : Fin (10 ^ L) → ℤ) (qs : List (Fin (10 ^ L))) :=
  (observe w L fuel a b qs).map Prod.fst

-- One leaf is multiplied once and reported twice, including its negative sign.
#guard answers 16 0 64 (fun _ => -3) (fun _ => 2) [0, 0] == some [-6, -6]
#guard answers 16 0 64 (fun _ => -3) (fun _ => 2) [] == some []

-- Digit nine is the inner wildcard; the outer query uses exactly its private leaf.
#guard answers 20 1 128 (fun i => i.val + 1) (fun _ => 1) [9, 0, 9] == some [55, 1, 55]
#guard answers 20 1 128 (fun i => -(i.val + 1 : ℤ)) (fun _ => 1) [9, 0, 9] ==
  some [-55, -1, -55]
#guard answers 20 1 128 (fun _ => 5) (fun _ => 0) [] == some []

-- Mixed suffixes share work. The two wildcard positions exercise both digit orders.
#guard answers 24 2 2048 (fun i => i.val + 1) (fun _ => 1) [99, 90, 9, 0, 99] ==
  some [5050, 460, 55, 1, 5050]

-- A nonzero word at the one-past-end address survives the complete controller.
#guard ((program.eval 20 128
    (((State.init (input 1 (fun _ => -2) (fun _ => 3) [9, 0]) : State registers).data).write
      (memoryEnd 1 2) 91)).map fun (y, _) => y.mem (memoryEnd 1 2)) == some 91

end ComplexityTests.SchonhagePruned
