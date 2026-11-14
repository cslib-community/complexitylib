/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointQuery

open Turing.MultiTapeTM.RootEndpointQuery

-- Two stationary intervals, one work head and one Boolean copy: eight source halves,
-- then eight target halves. The original vertices occupy numbers below ten.
example : query 1 ⟨List.replicate 8 false, 1, 0⟩ = some (0, 10) := by decide
example : query 1 ⟨List.replicate 8 false, 1, 7⟩ = some (1, 17) := by decide
example : query 1 ⟨List.replicate 8 false, 1, 8⟩ = some (1, 10) := by decide
example : query 1 ⟨List.replicate 8 false, 1, 9⟩ = some (3, 11) := by decide
example : query 1 ⟨List.replicate 8 false, 1, 10⟩ = some (1, 12) := by decide
example : query 1 ⟨List.replicate 8 false, 1, 13⟩ = some (7, 15) := by decide

-- Distinct copies have different subdivision vertices; the second half keeps that same column.
example : query 1 ⟨List.replicate 8 false, 2, 1⟩ = some (0, 11) := by decide
example : query 1 ⟨List.replicate 8 false, 2, 17⟩ = some (1, 11) := by decide

-- No work heads still leaves the control chain, including its final sink.
example : query 0 ⟨List.replicate 4 false, 1, 0⟩ = some (0, 4) := by decide
example : query 0 ⟨List.replicate 4 false, 1, 2⟩ = some (1, 4) := by decide
example : query 0 ⟨List.replicate 4 false, 1, 3⟩ = some (3, 5) := by decide

-- Exhausted work edges use their own sink rather than the final interval or a default vertex.
example : query 1
    ⟨[false, false, false, true, false, false, false, false], 1, 10⟩ =
    some (4, 12) := by decide
example : query 1
    ⟨[false, false, false, true, false, false, false, false], 1, 12⟩ =
    some (1, 14) := by decide

-- Empty universes, malformed rows, and every padded edge are rejected before lookup.
example : query 1 ⟨[], 1, 0⟩ = none := by decide
example : query 1 ⟨List.replicate 8 false, 0, 0⟩ = none := by decide
example : query 1 ⟨[false, false, true, true], 1, 0⟩ = none := by decide
example : query 1 ⟨[false, false], 1, 0⟩ = none := by decide
example : query 1 ⟨List.replicate 8 false, 1, 16⟩ = none := by decide
example : query 1 ⟨List.replicate 8 false, 1, 2 ^ 100⟩ = none := by decide
example : query 0 ⟨List.replicate 4 false, 1, 4⟩ = none := by decide

-- A generic client reads the existing graph's endpoint numbering without a graph table.
example (k q copies σ : ℕ) (e : Fin (2 * (q * (3 * k + 1) * copies))) :
    query k ⟨Turing.MultiTapeTM.ScheduleBits.rows
      (List.ofFn (Turing.MultiTapePTM.scheduleOfNat k q σ)), copies, e.val⟩ =
      some (Turing.MultiTapePTM.explicitSrcNum k q copies σ e.val,
        Turing.MultiTapePTM.explicitTgtNum k q copies e.val) := query_rows σ e
