/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.Multicover.Native
import Mathlib.Tactic

/-!
# Uniform native greedy planning clients

The overlapping three-element instance requires a cost/gain comparison, repeated
scanning, residual updates and ordered source-label output. Ties, absent/excess
mask bits, zero gains, empty ground and zero repetition demand are also checked.
-/

open Cslib.Algorithms.Lean
open Multicover
open Native Turing.MultiTapeTM

private def table : List Row :=
  [⟨7, [true, true, false], 2⟩, ⟨9, [false, true, true], 1⟩,
    ⟨11, [true], 1⟩, ⟨99, [false, false, false, true], 0⟩]

example : labels ⟨3, 1, table⟩ = [9, 11] := by
  norm_num [labels, Native.batch, advance, Native.select, consider, Native.ratio, Native.gain,
    decrement, initial, table, Function.iterate_succ_apply', List.range_succ]
example : labels ⟨3, 2, table⟩ = [9, 9, 11, 11] := by
  norm_num [labels, Native.batch, advance, Native.select, consider, Native.ratio, Native.gain,
    decrement, initial, table, Function.iterate_succ_apply', List.range_succ]
example : labels ⟨0, 4, table⟩ = [] := by
  norm_num [labels, Native.batch, advance, Native.select, consider, Native.ratio, Native.gain,
    decrement, initial, table, Function.iterate_succ_apply', List.range_succ]
example : labels ⟨3, 0, table⟩ = [] := by
  norm_num [labels, Native.batch, advance, Native.select, consider, Native.ratio, Native.gain,
    decrement, initial, table, Function.iterate_succ_apply', List.range_succ]

example : (Native.select [1] [⟨10, [true], 1⟩, ⟨20, [true], 1⟩]).map Row.label = some 10 := by
  norm_num [Native.select, consider, Native.ratio, Native.gain, List.range_succ]

-- Zero gain wins neither through a zero cost nor through a low source identifier.
example : (Native.select [0, 1] [⟨0, [true], 0⟩, ⟨42, [false, true], 3⟩]).map
    Row.label = some 42 := by
  norm_num [labels, Native.batch, advance, Native.select, consider, Native.ratio, Native.gain,
    decrement, initial, table, Function.iterate_succ_apply', List.range_succ]

example (input : Input) {row : Row} (h : row ∈ Native.batch input) : row ∈ input.rows :=
  batch_mem input h

example : ((Native.batch ⟨3, 2, table⟩).map (interpret 3)) =
    Multicover.batch (table.map (interpret 3)) 2 := batch_eq ⟨3, 2, table⟩

example : ComputableInPolyTime labels inputEncoding (encList encNat) := labels_computable
