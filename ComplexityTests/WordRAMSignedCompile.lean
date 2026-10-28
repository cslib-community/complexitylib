/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Signed.Input

/-!
# Complete signed-program compilation regressions

Execute source programs and their compiled unsigned instruction lists across all five signed
arithmetic operations, including Euclidean division and remainder, zero divisors, and the
minimum/`-1` source overflow exclusion. Larger loop clients exercise signed comparisons,
aliased arithmetic, memory reads/writes, and repeated signed quotient/remainder steps, with
checked source executions transferred by `executes_compile_input`.
-/

namespace ComplexityTests.WordRAMSignedCompile

open Cslib
open GenericRAM.Signed (model)
open GenericRAM.Signed.ToWordRAM
open WordRAM.Signed (encode decode)

private def arithmetic : GenericRAM.Program model 2 :=
  [.op (.const 0 (-3)), .op (.const 1 2), .op (.alu .add 0 ![0, 1]), .halt 0]

private def memoryBranch : GenericRAM.Program model 3 :=
  [.op (.const 0 1), .op (.load 1 0), .op (.const 2 0),
    .branch (.test .lt ![1, 2]) 6, .op (.const 1 7), .jump 7,
    .op (.alu .sub 1 ![2, 1]), .op (.store 0 1), .halt 1]

private def squareAbsSum : GenericRAM.Program model 6 :=
  [.op (.const 0 0), .op (.load 1 0), .op (.const 2 1), .op (.const 3 0),
    .op (.const 5 1),
    .branch (.test .lt ![1, 2]) 13,
    .op (.load 4 2), .branch (.test .lt ![4, 0]) 9, .jump 10,
    .op (.alu .sub 4 ![0, 4]),
    .op (.alu .add 3 ![3, 4]), .op (.alu .add 2 ![2, 5]), .jump 5,
    .op (.copy 4 3), .op (.alu .mul 3 ![3, 4]), .op (.store 0 3), .op (.load 4 0),
    .branch (.test .eq ![3, 4]) 19, .op (.const 4 (-1)), .halt 4]

/-- A negative arithmetic result is returned by both actual interpreters. The target's
twenty-nine instructions include header preparation, relocated control flow and halt. -/
example : GenericRAM.run (M := model) 3 arithmetic 10 (GenericRAM.Signed.initial []) =
    some (-1, 4) ∧ WordRAM.run 5 (compile arithmetic) 29 (WordRAM.State.init []) = some (3, 29) ∧
    WordRAM.run 5 (compile arithmetic) 28 (WordRAM.State.init []) = none := by
  decide

-- The nine source instructions occupy 576 target slots. Reducing the actual List-indexed
-- interpreter at its relocated halt needs more recursion than the default elaborator limit.
set_option maxRecDepth 2048 in
/-- Both branch directions, a relocated unconditional jump, and encoded stores execute. -/
example : WordRAM.run 6 (compile memoryBranch) 300
      (WordRAM.State.init ([-3].map encode)) = some (6, 47) ∧
    WordRAM.run 6 (compile memoryBranch) 300
      (WordRAM.State.init ([3].map encode)) = some (14, 35) := by
  decide

/-- The larger source client visits both sign branches and returns the square of 2+3+4. -/
example : GenericRAM.run (M := model) 8 squareAbsSum 200
      (GenericRAM.Signed.initial [-2, 3, -4]) = some (81, 33) ∧
    GenericRAM.run (M := model) 8 squareAbsSum 200
      (GenericRAM.Signed.initial []) = some (0, 12) := by
  decide

/-- Transfer a nontrivial loop, signed tests, memory and aliased arithmetic from a checked
source execution, with ordinary input and an explicit total native instruction bound. -/
example : ∃ n ≤ 1061, WordRAM.Executes 10 (compile squareAbsSum)
    (WordRAM.State.init ([-2, 3, -4].map encode)) 162 n := by
  have hs : GenericRAM.Executes (M := model) 8 squareAbsSum
      (GenericRAM.Signed.initial [-2, 3, -4]) 81 33 :=
    .of_run (fuel := 200) (by decide)
  exact executes_compile_input (by unfold GenericRAM.Signed.InputFits; decide) hs

/-- Empty input is an actual instance of the input/width premises and traverses the exit edge. -/
example : ∃ n ≤ 389, WordRAM.Executes 10 (compile squareAbsSum)
    (WordRAM.State.init []) 0 n := by
  have hs : GenericRAM.Executes (M := model) 8 squareAbsSum
      (GenericRAM.Signed.initial []) 0 12 := .of_run (fuel := 200) (by decide)
  exact executes_compile_input (by unfold GenericRAM.Signed.InputFits; decide) hs

private def oneBit : GenericRAM.Program model 1 := [.op (.const 0 (-1)), .halt 0]

private def storeNegative : GenericRAM.Program model 2 :=
  [.op (.const 0 1), .op (.const 1 (-3)), .op (.store 0 1), .halt 1]

/-- Memory is observable at a translated instruction boundary, before the final halt. -/
example : ∃ y k, k ≤ 101 ∧ WordRAM.Runs 6 (compile storeNegative)
    (WordRAM.State.init []) ⟨197, y⟩ k ∧ y.mem 1 = 7 := by
  let s₀ : GenericRAM.State model 2 := GenericRAM.Signed.initial []
  let s₁ : GenericRAM.State model 2 := ⟨1, s₀.data.set 0 1⟩
  let s₂ : GenericRAM.State model 2 := ⟨2, s₁.data.set 1 (-3)⟩
  let s₃ : GenericRAM.State model 2 := ⟨3, s₂.data.write 1 (-3)⟩
  have h₁ : GenericRAM.Next (M := model) 4 storeNegative s₀ s₁ := by rfl
  have h₂ : GenericRAM.Next (M := model) 4 storeNegative s₁ s₂ := by rfl
  have h₃ : GenericRAM.Next (M := model) 4 storeNegative s₂ s₃ := by rfl
  have hr : GenericRAM.Runs (M := model) 4 storeNegative s₀ s₃ 3 :=
    ((Relation.RelatesInSteps.single h₁).tail _ _ _ _ h₂).tail _ _ _ _ h₃
  obtain ⟨y, k, hk, ht, hm⟩ := runs_compile_input
    (by unfold GenericRAM.Signed.InputFits; decide) hr
  exact ⟨y, k, hk, ht, hm.mem 1⟩

/-- The smallest signed width works. Target code labels may exceed the data word range:
the relocated halt is at 69, although the physical word has only three bits. -/
example : GenericRAM.Signed.InputFits 1 [] ∧
    WordRAM.run 3 (compile oneBit) 8 (WordRAM.State.init []) = some (3, 8) := by
  constructor
  · unfold GenericRAM.Signed.InputFits
    decide
  · decide

private def onlyDiv : GenericRAM.Program model 2 :=
  [.op (.const 0 1), .op (.load 0 0), .op (.const 1 2), .op (.load 1 1),
    .op (.alu .div 0 ![0, 1]), .halt 0]

private def onlyMod : GenericRAM.Program model 2 :=
  [.op (.const 0 1), .op (.load 0 0), .op (.const 1 2), .op (.load 1 1),
    .op (.alu .mod 0 ![0, 1]), .halt 0]

-- Six source instructions occupy 389 target slots including the five-instruction prologue.
set_option maxRecDepth 2048 in
/-- Compiled `.div` and `.mod` programs agree with the signed RAM across all four sign
combinations, zero divisors (`a / 0 = 0`, `a % 0 = a`), and the minimum/`-1` boundary:
at `w = 4`, `(-8) / (-1)` faults in the source model while `(-8) % (-1) = 0` succeeds. -/
example :
    (WordRAM.run 6 (compile onlyDiv) 200 (WordRAM.State.init ([7, 3].map encode))).map Prod.fst =
      some (encode 2) ∧
    (WordRAM.run 6 (compile onlyDiv) 200 (WordRAM.State.init ([7, -3].map encode))).map Prod.fst =
      some (encode (-2)) ∧
    (WordRAM.run 6 (compile onlyDiv) 200 (WordRAM.State.init ([-7, 3].map encode))).map Prod.fst =
      some (encode (-3)) ∧
    (WordRAM.run 6 (compile onlyDiv) 200 (WordRAM.State.init ([-7, -3].map encode))).map Prod.fst =
      some (encode 3) ∧
    (WordRAM.run 6 (compile onlyDiv) 200 (WordRAM.State.init ([7, 0].map encode))).map Prod.fst =
      some (encode 0) ∧
    (WordRAM.run 6 (compile onlyDiv) 200 (WordRAM.State.init ([-8, 0].map encode))).map Prod.fst =
      some (encode 0) ∧
    (WordRAM.run 6 (compile onlyMod) 200 (WordRAM.State.init ([7, 3].map encode))).map Prod.fst =
      some (encode 1) ∧
    (WordRAM.run 6 (compile onlyMod) 200 (WordRAM.State.init ([7, -3].map encode))).map Prod.fst =
      some (encode 1) ∧
    (WordRAM.run 6 (compile onlyMod) 200 (WordRAM.State.init ([-7, 3].map encode))).map Prod.fst =
      some (encode 2) ∧
    (WordRAM.run 6 (compile onlyMod) 200 (WordRAM.State.init ([-7, -3].map encode))).map Prod.fst =
      some (encode 2) ∧
    (WordRAM.run 6 (compile onlyMod) 200 (WordRAM.State.init ([7, 0].map encode))).map Prod.fst =
      some (encode 7) ∧
    (WordRAM.run 6 (compile onlyMod) 200 (WordRAM.State.init ([-8, 0].map encode))).map Prod.fst =
      some (encode (-8)) ∧
    GenericRAM.run (M := model) 4 onlyDiv 20 (GenericRAM.Signed.initial [-8, -1]) = none ∧
    GenericRAM.run (M := model) 4 onlyMod 20 (GenericRAM.Signed.initial [-8, -1]) = some (0, 6) ∧
    (WordRAM.run 6 (compile onlyDiv) 200 (WordRAM.State.init ([-8, -1].map encode))).map Prod.fst =
      some (encode 8) := by
  decide

/-- Euclidean quotient-accumulation loop: load `[a, b]`, repeatedly accumulate `q ← a / b` and
step `(a, b) ← (b, a % b)` until `b = 0`, store the final Euclidean GCD `a` at address `0`,
and halt with the sum of signed Euclidean quotients. -/
private def euclideanQuotSum : GenericRAM.Program model 5 :=
  [.op (.const 0 1), .op (.load 1 0),
    .op (.const 0 2), .op (.load 2 0),
    .op (.const 0 0), .op (.const 3 0),
    .branch (.test .eq ![2, 0]) 13,
    .op (.alu .div 4 ![1, 2]),
    .op (.alu .add 3 ![3, 4]),
    .op (.alu .mod 4 ![1, 2]),
    .op (.copy 1 2), .op (.copy 2 4), .jump 6,
    .op (.store 0 1), .halt 3]

/-- On `[-23, -5]`, the loop visits `(--)`, `(-+)` and `(++)` division/remainder steps:
`(-23) / (-5) = 5` (rem `2`), `(-5) / 2 = -3` (rem `1`), `2 / 1 = 2` (rem `0`), returning
`5 + (-3) + 2 = 4` in `30` source instructions and transferring within `32 * 30 + 5 = 965`
unsigned instructions. -/
example : GenericRAM.run (M := model) 6 euclideanQuotSum 100
      (GenericRAM.Signed.initial [-23, -5]) = some (4, 30) ∧
    ∃ n ≤ 965, WordRAM.Executes 8 (compile euclideanQuotSum)
      (WordRAM.State.init ([-23, -5].map encode)) (encode 4) n := by
  refine ⟨by decide, ?_⟩
  have hs : GenericRAM.Executes (M := model) 6 euclideanQuotSum
      (GenericRAM.Signed.initial [-23, -5]) 4 30 :=
    .of_run (fuel := 100) (by decide)
  exact executes_compile_input (by unfold GenericRAM.Signed.InputFits; decide) hs

private def overflowing : GenericRAM.Program model 1 := [.op (.const 0 1), .halt 0]

/-- Forward correctness does not assert fault reflection. A source constant may overflow
its signed width and still execute in the wider unsigned representation. -/
example : GenericRAM.run (M := model) 1 overflowing 8 (GenericRAM.Signed.initial []) = none ∧
    WordRAM.run 3 (compile overflowing) 8 (WordRAM.State.init []) = some (2, 8) := by
  decide

end ComplexityTests.WordRAMSignedCompile
