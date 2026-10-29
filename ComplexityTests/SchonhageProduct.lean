/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Input

-- Actual native interpreter regressions supplement the general execution proofs.
set_option linter.hashCommand false

namespace ComplexityTests.SchonhageProduct

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

private def observe {m N : ℕ} (bits : Bool) (L : ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) : Option (List ℤ × Bool) :=
  let data := (State.init (input bits L X Y qs) : State 160).data
  let sentinel := memoryEnd L m N qs.length + 17
  let start := data.write sentinel 91
  ((program bits).eval 32 4096 start).map fun (y, _) =>
    ((List.range qs.length).map (fun i => decode (y.mem (y.regs output + i))),
      decide ((∀ a < inputEnd m N qs.length, y.mem a = data.mem a) ∧ y.mem sentinel = 91))

-- The actual complete pipeline handles an empty original input without a tile division.
#guard observe false 0 (m := 0) (N := 0) (fun _ _ => 0) (fun _ _ => 0) [] ==
  some ([], true)

-- Signed operands and repeated requests survive both producer calls and reconstruction.
#guard observe false 0 (m := 0) (N := 1) (fun _ _ => -3) (fun _ _ => 2)
    [(0, 0), (0, 0), (0, 0)] == some ([-6, -6, -6], true)

-- Raw unsigned entries are doubled by real code before signed encoding, not in the input.
#guard observe true 0 (m := 0) (N := 1) (fun _ _ => 1) (fun _ _ => 1)
    [(0, 0), (0, 0)] == some ([1, 1], true)

-- Distinct tile pointers and returned epochs are reused across all four padded band pairs.
#guard observe false 1 (m := 0) (N := 4)
    (fun i _ => (i.val : ℤ) - 2) (fun _ j => (j.val : ℤ) - 1)
    [(3, 0), (0, 3), (3, 3), (1, 0), (3, 0)] == some ([-1, -4, 2, 1, -1], true)

-- A nonempty inner coordinate makes the pruned kernel visit all ten signed tensor terms.
#guard observe false 1 (m := 1) (N := 2)
    (fun i k => (i.val : ℤ) + k.val - 1) (fun k j => (k.val : ℤ) + j.val - 2)
    [(1, 0), (0, 1), (1, 1), (1, 0)] == some ([2, 6, 8, 2], true)

end ComplexityTests.SchonhageProduct
