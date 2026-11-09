/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (output-sensitive streamed class join regression tests)

public import Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinStream
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinStream
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping

/-!
Actual occurrence joins preserve ordering and duplicates across collisions, empty
and one-sided groups. General machine bounds use physical width and actual input/
output volume, including control for empty groups; no class-size premise is supplied.
The original-input retention and readback clients are checked separately in full.
-/

public section
open Turing.MultiTapeTM

example : KeyJoin.join [] = [] := by decide +kernel
example : KeyJoin.join [[], [], []] = [] := by decide +kernel
example : KeyJoin.join [[(0, 0), (0, 2)], [], [(1, 1), (1, 3)]] = [] := by decide +kernel
example : KeyJoin.join [[(2, 0), (2, 0), (2, 1), (2, 1)]] =
    [(0, 0), (0, 0), (0, 0), (0, 0)] := by decide +kernel
example : KeyJoin.join [[(0, 0), (0, 3), (0, 2), (0, 1)], [], [(1, 4), (1, 7)]] =
    [(0, 1), (0, 0), (1, 1), (1, 0), (2, 3)] := by decide +kernel
example : KeyJoinStream.volume [[], [], []] = 4 := by decide +kernel
example : KeyJoinStream.volume [[(2, 0), (2, 0), (2, 1), (2, 1)]] = 10 := by decide +kernel
example : KeyJoinStream.width [] = 1 := by decide +kernel

example (groups : List (List SortedMatch.Record)) := KeyJoinStream.volume_eq groups
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO KeyJoin.join KeyGrouping.outputEncoding (encList RadixPartition.recordEncoding)
      (fun groups => KeyJoinStream.volume groups * P (KeyJoinStream.width groups))
      (fun groups => KeyJoinStream.volume groups * P (KeyJoinStream.width groups)) :=
  KeyJoinStream.join_computable
