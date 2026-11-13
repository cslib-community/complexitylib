/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import all CslibFrontier.Computability.PolyTime.CSP.Edge.Augmenting
import Mathlib.Tactic.FinCases

/-!
# Native augmentation regression examples

These examples run the finite buffer implementation on explicit tables and decode its output
into the existing occurrence walk. They retain width rejection, nullaries, malformed tables,
comparison-only defects and large sparse binary names.
-/

-- This regression module deliberately exports no declarations.
set_option linter.privateModule false

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP.EdgeAugmenting

namespace CslibFrontierTests.EdgeCSPAugmentingNative

private def equality : Table := ⟨2, [[false, false], [true, true]]⟩
private def doubled : CSP Table ℕ := [⟨equality, [0, 1]⟩, ⟨equality, [0, 1]⟩]
private def exampleInput : Input :=
  ⟨doubled, [false, false, true, true], [false, false, false, false], 0⟩

-- The public certificate composes through ordinary native `fun_prop` inference.
example : Turing.MultiTapeTM.ComputableInPolyTime (fun input => (run input).isSome)
    encInput Turing.MultiTapeTM.encBool := by fun_prop

-- The excluded start is allowed as the actual endpoint.
example : run exampleInput = some ⟨1, [(3, 2)]⟩ := by decide
example : ((run exampleInput).bind (decode doubled)).map (fun w => (w.start, w.finish)) =
    some (1, 0) := by decide

private theorem doubled_edge : EdgeInstance doubled := by
  unfold EdgeInstance
  decide

private theorem doubled_even : EdgeInstance.EvenConstraints Table.sem doubled := by
  intro i
  fin_cases i <;>
    exact {
      isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
      parity_eq := by decide }

example : ∃ w : Walk doubled,
    run exampleInput = some (code w) ∧ decode doubled (code w) = some w ∧
      w.IsAugmenting Table.sem (labeling doubled exampleInput.labels) ∧ w.start ≠ 0 := by
  obtain ⟨w, hw, hd, ha, hx, _⟩ := run_spec exampleInput (by decide) (by decide)
    doubled_edge doubled_even (by decide) (by decide) (by decide)
  exact ⟨w, hw, hd, ha, hx⟩

-- Four-argument tables retain the two fixed positions in the occurrence numbering.
private def wider : Input :=
  let table : Table := ⟨4, [[false, false, false, false], [true, true, false, false]]⟩
  ⟨[⟨table, [0, 1, 2, 3]⟩, ⟨table, [0, 1, 2, 3]⟩],
    [false, false, false, false, true, true, false, false],
    [false, false, false, false, false, false, false, false], 0⟩
example : run wider = some ⟨1, [(5, 4)]⟩ := by decide +kernel
example : decode doubled ⟨0, [(2 ^ 100, 0)]⟩ = none := by decide

-- Repair a defect present only in the comparison, without assuming improvement.
example : repair ⟨doubled, [false, false, false, false], [false, false, true, true], 0⟩ =
    ([false, false, false, false], 1) := by decide

-- Three disjoint doubled components force comparison-only repair before augmentation.
private def bothPhases : Input :=
  ⟨[⟨equality, [0, 1]⟩, ⟨equality, [0, 1]⟩,
    ⟨equality, [2, 3]⟩, ⟨equality, [2, 3]⟩,
    ⟨equality, [4, 5]⟩, ⟨equality, [4, 5]⟩],
    [false, false, true, true, false, false, false, false, false, false, true, true],
    [false, false, false, false, false, false, true, true, false, false, false, false], 0⟩
-- Direct kernel checking avoids deep elaborator reduction of the twelve-occurrence scans.
example : (repair bothPhases).2 = 1 := by decide +kernel
example : run bothPhases = some ⟨1, [(3, 2)]⟩ := by decide +kernel

-- No improvement, short buffers and long buffers are total failures.
example : run { exampleInput with comparison := exampleInput.labels } = none := by decide
example : run { exampleInput with labels := [false] } = none := by decide
example : run { exampleInput with comparison := [false, false, false, false, false] } = none := by
  decide

example : run ⟨[], [], [], 0⟩ = none := by decide
example : run ⟨[⟨⟨0, [[]]⟩, []⟩], [], [], 0⟩ = none := by decide
example : run ⟨[⟨⟨0, []⟩, []⟩], [], [], 0⟩ = none := by decide

-- Scope lengths, rather than malformed binary arities, fund every scan.
example : run ⟨[⟨⟨2 ^ 100, [[false]]⟩, [0, 1]⟩,
    ⟨⟨2 ^ 100, [[false]]⟩, [0, 1]⟩],
    [false, false, true, true], [false, false, false, false], 0⟩ = none := by decide
example : run ⟨[⟨⟨2, [[false]]⟩, [0, 1]⟩, ⟨⟨2, [[false]]⟩, [0, 1]⟩],
    [false, false, true, true], [false, false, false, false], 0⟩ = none := by decide

private def sparse : CSP Table ℕ :=
  [⟨equality, [2 ^ 100, 2 ^ 100 + 1]⟩, ⟨equality, [2 ^ 100, 2 ^ 100 + 1]⟩]
example : run ⟨sparse, [false, false, true, true],
    [false, false, false, false], 2 ^ 100⟩ = some ⟨2 ^ 100 + 1, [(3, 2)]⟩ := by decide

-- Repeated positions are retained, but the edge-instance contract excludes repeated variables
-- within one constraint, so no correctness theorem can assume such an instance is an edge CSP.
example : ¬ EdgeInstance ([⟨equality, [0, 0]⟩] : CSP Table ℕ) := by
  unfold EdgeInstance
  decide
example : run ⟨[⟨equality, [0, 0]⟩], [false, false], [true, true], 7⟩ = none := by decide

end CslibFrontierTests.EdgeCSPAugmentingNative
