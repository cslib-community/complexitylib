/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

import Complexity.Init
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Route
import Complexity.Algorithms.MatrixMultiplication.Schonhage.MaskTable

set_option linter.hashCommand false
set_option linter.privateModule false

open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

private def expectedCode {L m : ℕ} (hm : m ≤ L) (I J : ℕ) : ℕ :=
  (PrunedQuery.queryIndex (outStrOfPos (MaskTable.layout hm) I J)).val

-- Distinct row/column block indices use rank 1 and rank 2, not their transposes.
#guard expectedCode (by decide : 1 ≤ 4) 2 28 == 97
#guard expectedCode (by decide : 1 ≤ 4) 28 2 == 905
example : QueryDigits.pack 4 2 2 1 ≠ QueryDigits.pack 4 4 1 2 := by decide +kernel

private def packedInput : Data 16 where
  regs i := if i = depth then 4 else if i = mask then 2 else
    if i = row then 2 else if i = col then 1 else 81
  mem a := if a = 23 then 91 else 0

-- The arbitrary nonzero scratch bank is initialized by real code; the same returned state
-- carries the packed word and the unchanged memory assertion.
example : ∃ y, ExecWithin 19 packCode packedInput y 70 ∧
    y.regs code = 97 ∧ y.mem 23 = 91 := by
  obtain ⟨y, he, hv, _, hf⟩ := exec_pack (w := 19) 4 2 2 1 packedInput
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨y, he, hv, congrFun hf 23⟩

private def routingInput (L m N : ℕ) (qs : List (ℕ × ℕ)) : List ℕ :=
  [L, m, N, qs.length] ++ qs.flatMap (fun q => [q.1, q.2])

private def observe (L m N : ℕ) (qs : List (ℕ × ℕ)) :
    Option (List ℕ × List ℕ × List ℕ × Bool) :=
  let initial := (State.init (routingInput L m N qs) : State 96).data.write 100000 91
  (program.eval 25 1024 initial).map fun (y, _) =>
    ((List.range qs.length).map fun i => y.mem (y.regs codes + i),
      (List.range qs.length).map fun i => y.mem (y.regs originals + i),
      (List.range (y.regs tileCount + 1)).map fun i => y.mem (y.regs offsets + i),
      decide ((∀ a < 5 + 2 * qs.length, y.mem a = initial.mem a) ∧ y.mem 100000 = 91))

-- Actual initialized empty and zero-depth runs, including the computed tables and prefix pass.
#guard observe 0 0 0 [] == some ([], [], [0], true)
#guard observe 0 0 2 [(1, 0), (0, 1), (1, 0)] ==
  some ([0, 0, 0], [1, 0, 2], [0, 0, 1, 3, 3], true)

-- K0=2, three bands, asymmetric row/column digits and an original repeated query.
-- This exercises only routing; it never materializes a 10^4-leaf encoded array.
#guard observe 4 1 110 [(2, 28), (28, 2), (55, 109), (2, 28), (109, 55)] ==
  some ([97, 905, 97, 49, 49], [0, 1, 3, 2, 4], [0, 3, 3, 3, 3, 3, 4, 4, 5, 5], true)
