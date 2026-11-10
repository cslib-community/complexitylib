/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic

/-! Finite storage at negative heads, blank gaps, input boundaries, and stateful oracle calls. -/

namespace CslibFrontierTests.FiniteMachine

open Cslib Turing Turing.MultiTapeMachine
open Cslib.Turing

-- Write at positions zero and minus two, then leave the head over the intervening blank.
private def gapped : BiTape Bool :=
  (((BiTape.nil.step (some (some true), .neg)).step (none, .neg)).step
    (some (some false), .pos))

example : gapped.read (-1) = some false ∧ gapped.head = none ∧
    gapped.read 1 = some true ∧ gapped.spaceUsed = 3 := by decide

-- Writing a blank really erases the cell; the more distant nonblank cell remains.
example : (gapped.moveLeft.write none).read 0 = none ∧
    (gapped.moveLeft.write none).read 2 = some true := by decide

-- The simulation relation permits negative native heads, independently of finite storage.
example : (BiTape.nil.step (some (some true), .neg)).Represents
    (Function.update (fun _ : ℤ => none) (-7) (some true)) (-8) :=
  (BiTape.represents_nil (-7)).step (some (some true), .neg)

private def inputCfg : FiniteCfg 0 Bool Unit := FiniteCfg.init () [true, false]

-- Position one is the first input symbol; both boundary cells, including empty input, are blank.
example : inputCfg.inputSymbol = some true ∧
    ({ inputCfg with inputPos := 0 } : FiniteCfg 0 Bool Unit).inputSymbol = none ∧
    ({ inputCfg with inputPos := 3 } : FiniteCfg 0 Bool Unit).inputSymbol = none ∧
    (FiniteCfg.init (k := 0) () ([] : List Bool)).inputSymbol = none := by decide

private def channels : FiniteConfig 0 Bool Unit Bool where
  tapes := FiniteCfg.init () []
  channels channel := if channel then ([true], (BiTape.mk₁ [false]).moveLeft)
    else ([false], (BiTape.mk₁ [true, false]).moveRight)

-- Submission clears one buffer and resets its reply head, retaining the other channel's head.
example :
    let next := channels.receive true () [true, false]
    ((next.channels true).1, next.answerSymbols true,
      (next.channels false).1, next.answerSymbols false) = ([], some true, [false], some false) :=
  by decide

-- A one-instruction query may install a reply longer than its clock. Storage charges its length.
example (n : ℕ) : FiniteConfig.SpaceBound 0 1 n
    ((FiniteConfig.init (k := 0) (Oracle := Bool) () ([] : List Bool)).receive true ()
      (List.replicate n true)) :=
  (FiniteConfig.spaceBound_init () [] n).receive true () _ (by simp)

private def readHead : MultiTapePTM 0 Bool Bool Unit where
  initial := false
  tr state _ _ answer _ := if state then
    .step ⟨0, Fin.elim0, answer (), none⟩ (fun _ => none) (fun _ => 0)
    else .query () true

private abbrev Request := Bool × List Bool

private def choose (choices : Bool → Action 0 Bool Bool Unit) :
    OracleComp (fun _ : Request => List Bool) (Action 0 Bool Bool Unit) := do
  let reply ← OracleComp.query (true, [])
  return choices (reply.headD false)

private def query (_ : Unit) (word : List Bool) :
    OracleComp (fun _ : Request => List Bool) (List Bool) := OracleComp.query (false, word)

private def record (request : Request) : StateT (List Request) Id (List Bool) :=
  modifyGet fun history => (if request.1 then [true] else [false, true], history ++ [request])

-- Both live instructions perform their choice effect, even though the branches agree. The
-- query occurs between them; extra halted iterations perform neither choice nor query effects.
example : (OracleComp.interpret record
    (readHead.finiteRunFrom choose query 5 (FiniteConfig.init false []))).run [(false, [true])] =
      ([false], [(false, [true]), (true, []), (false, []), (true, [])]) := by rfl

-- The native machine has exactly the same program for every clock and input word.
example (fuel : ℕ) (input : List Bool) :
    readHead.finiteRunFrom choose query fuel (FiniteConfig.init false input) =
      MultiTapeMachine.run readHead choose query fuel input :=
  finiteRunFrom_init readHead choose query fuel input

private def counter (_ : Unit) : StateT ℕ ProbComp ℕ :=
  modifyGet fun count => (count, count + 1)

private def collect (values : List ℕ) : OracleComp (fun _ : Unit => ℕ) (List ℕ) := do
  let value ← OracleComp.query ()
  return values ++ [value]

-- Stateful substitution keeps the accumulated handler state, including the final update.
example : (OracleComp.interpret counter (OracleComp.iterate 3 collect [])).run 7 =
    pure ([7, 8, 9], 10) := by
  rw [OracleComp.run_interpret_iterate]
  rfl

end CslibFrontierTests.FiniteMachine
