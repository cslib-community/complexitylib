/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import CslibFrontier.Computability.PolyTime.CSP.Edge.Forest.Spec
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Mathlib.Tactic.FinCases

/-! Actual native forest runs and exact source/decoding agreement on raw explicit tables. -/

set_option linter.privateModule false

namespace CslibFrontierTests.EdgeCSPForestNative

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP.EdgeForest
open Cslib.Complexity.CSP.EdgeAugmenting (labeling)

private def equality : Table := ⟨2, [[false, false], [true, true]]⟩
private def inequality : Table := ⟨2, [[false, true], [true, false]]⟩
private def doubled : Input := ⟨[⟨equality, [0, 1]⟩, ⟨equality, [0, 1]⟩],
  [false, false, true, true]⟩

-- The public certificate composes through ordinary native automation.
example : Turing.MultiTapeTM.ComputableInPolyTime (fun i => (run i).isSome)
    encInput Turing.MultiTapeTM.encBool := by fun_prop

-- The first partner, rather than any arbitrary feasible meeting, is returned.
example : run doubled = some (.inr (.inl ⟨[0, 1], [], ⟨0, []⟩, 1⟩)) := by decide
example : (run doubled).bind (decode doubled.body) =
    some (Forest.search Table.sem (labeling doubled.body doubled.labels)) :=
  decode_run doubled (by decide)

private def doubledMeeting : Forest.Meeting doubled.body :=
  ⟨[0, 1], [], ⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, []⟩,
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩⟩

-- The decoded native augmentation composes with the mathematical endpoint, actually
-- producing a valid zero-defect labeling from this two-defect input.
example : ValidLabeling Table.sem
    (doubledMeeting.walk.flip (labeling doubled.body doubled.labels)) ∧
    (defects (doubledMeeting.walk.flip (labeling doubled.body doubled.labels))).card = 0 := by
  have he : EdgeInstance doubled.body := by unfold EdgeInstance; decide
  have hv : ValidLabeling Table.sem (labeling doubled.body doubled.labels) := by
    unfold ValidLabeling
    decide
  have hm : EdgeInstance.EvenConstraints Table.sem doubled.body := by
    intro i
    fin_cases i <;> exact {
      isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
      parity_eq := by decide }
  have hd : (defects (labeling doubled.body doubled.labels)).card = 2 := by decide
  have hs := run_spec doubled (by decide) he hv hm
  have hr : (run doubled).bind (decode doubled.body) = some (.augment doubledMeeting) := by
    decide
  rw [hr] at hs
  exact ⟨hs.2.1, by have := hs.2.2; omega⟩

private def triangle : Input := ⟨[⟨inequality, [0, 1]⟩, ⟨equality, [1, 2]⟩, ⟨equality, [2, 0]⟩],
  [true, false, false, false, false, false]⟩

-- A genuine three-edge blossom with its older log, current copy and meeting output.
example : run triangle = some (.inr (.inr
    ⟨[0], [⟨2, [3]⟩, ⟨0, [1]⟩], ⟨4, []⟩, 5⟩)) := by decide +kernel
example : (run triangle).bind (decode triangle.body) =
    some (Forest.search Table.sem (labeling triangle.body triangle.labels)) :=
  decode_run triangle (by decide)

-- The meeting retains a child already inserted at the current copied constraint.
private def partialMeeting : Input :=
  ⟨[⟨⟨3, [[false, false, false], [true, true, false], [true, false, true]]⟩, [0, 1, 2]⟩,
    ⟨⟨1, [[true]]⟩, [0]⟩, ⟨⟨1, [[false]]⟩, [1]⟩, ⟨⟨1, [[true]]⟩, [2]⟩],
    [false, false, false, true, false, true]⟩
example : run partialMeeting = some (.inr (.inl ⟨[0, 2], [], ⟨0, [1]⟩, 2⟩)) := by
  decide +kernel

private def repeated : Input :=
  ⟨[⟨⟨4, [[false, false, false, false], [true, true, false, false],
      [false, false, true, true], [true, true, true, true]]⟩, [0, 1, 2, 3]⟩,
    ⟨equality, [1, 2]⟩, ⟨⟨1, [[true]]⟩, [0]⟩, ⟨⟨1, [[false]]⟩, [3]⟩],
    [false, false, false, false, false, false, true, false]⟩

-- Constraint zero is expanded at two distinct times. The second copy skips the old parent.
example : run repeated = some (.inl
    [⟨7, []⟩, ⟨6, []⟩, ⟨2, [3]⟩, ⟨4, [5]⟩, ⟨0, [1]⟩]) := by decide +kernel
example : (run repeated).bind (decode repeated.body) =
    some (Forest.search Table.sem (labeling repeated.body repeated.labels)) :=
  decode_run repeated (by decide)

private def sparse : Input :=
  ⟨[⟨equality, [2 ^ 100, 2 ^ 250]⟩, ⟨equality, [2 ^ 100, 2 ^ 250]⟩],
    [false, false, true, true]⟩
example : run sparse = some (.inr (.inl ⟨[2 ^ 100, 2 ^ 250], [], ⟨0, []⟩, 1⟩)) := by
  decide +kernel

-- Empty and nullary inputs exhaust; malformed declared arities do not fund a loop.
example : run ⟨[], []⟩ = some (.inl []) := by decide
example : run ⟨[⟨⟨0, [[]]⟩, []⟩], []⟩ = some (.inl []) := by decide
example : run ⟨[⟨⟨0, []⟩, []⟩], []⟩ = some (.inl []) := by decide
example : run ⟨[⟨⟨2 ^ 250, [[false]]⟩, []⟩], []⟩ = some (.inl []) := by decide

-- An unrelated invalid constraint suppresses every partner: global validity is retained.
private def globallyInvalid : Input :=
  ⟨doubled.body ++ [Constraint.mk ⟨0, []⟩ []], doubled.labels⟩
example : partners globallyInvalid (0, 0, 0) = [] := by decide
example : run globallyInvalid = some (.inl [⟨3, []⟩, ⟨2, []⟩, ⟨1, []⟩, ⟨0, []⟩]) := by
  decide +kernel
example : (run globallyInvalid).bind (decode globallyInvalid.body) =
    some (Forest.search Table.sem (labeling globallyInvalid.body globallyInvalid.labels)) :=
  decode_run globallyInvalid (by decide)

-- Malformed row widths remain exact source behavior rather than a precondition.
example : run ⟨[⟨⟨2 ^ 100, [[false]]⟩, [0, 1]⟩,
    ⟨⟨2 ^ 100, [[false]]⟩, [0, 1]⟩], [false, false, true, true]⟩ =
      some (.inl [⟨3, []⟩, ⟨2, []⟩, ⟨1, []⟩, ⟨0, []⟩]) := by decide +kernel
example : run { doubled with labels := [false] } = none := by decide
example : run { doubled with labels := doubled.labels ++ [false] } = none := by decide

-- Step 4b compares the original constraint even when the copied expansions differ in time.
example : scan [0] [((0, 0, 0), [(0, 1, 1)])] (0, 2, 2) [] [(0, 1, 1)] =
    ([], none) := by decide
example : parentConstraint [((0, 0, 0), [(0, 1, 1)])] 1 = some 0 := by decide

-- Invalid positions reject in exhausted logs, partial current copies and meeting outputs.
example : decode doubled.body (.inl [⟨2 ^ 100, []⟩]) = none := by decide
example : decode doubled.body (.inl [⟨0, [4]⟩]) = none := by decide
example : decode doubled.body (.inr (.inl ⟨[], [], ⟨0, [4]⟩, 1⟩)) = none := by decide
example : decode doubled.body (.inr (.inr ⟨[], [], ⟨0, []⟩, 4⟩)) = none := by decide

end CslibFrontierTests.EdgeCSPForestNative
