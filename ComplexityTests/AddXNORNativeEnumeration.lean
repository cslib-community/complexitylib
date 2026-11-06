/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Complexity.Cryptanalysis.AddXNORNativeEmit
import Mathlib.Tactic.IntervalCases

/-!
# Native quarter records, inverse filtering and hit recovery

The native pipeline below builds a dirty bucket table, computes one actual
inverse query, follows its pointers and emits full-width records. It does not
provide the complete class loop, full-state dictionary or global dissection.
-/

-- The checked examples and private fixtures export no library API.
set_option linter.privateModule false

public section

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR Native.Quarter

private def input : Data 32 :=
  { regs := fun r => if r = base then 5 else if r = count then 2
      else if r = modulus then 8 else if r = initial then 3
      else if r = keyModulus then 2 else if r = heads then 20
      else if r = frontier then 24 else 0
    mem := fun a => if a = 5 then 1 else if a = 6 then 2
      else if a = 8 then 3 else if a = 9 ∨ a = 10 ∨ a = 11 then 1
      else if 20 ≤ a ∧ a < 22 ∨ 24 ≤ a ∧ a < 36 then 99
      else if a = 100 then 17 else 0 }

private def first : List (BitVec 3) := [1#3, 2#3]

private theorem input_bounded : input.Bounded 7 := by
  constructor
  · intro r
    fin_cases r <;> decide
  · intro a
    simp only [input]
    split_ifs <;> decide

/-- Every layout and support premise is supplied, including an unread sentinel. -/
example : ∃ y n ts, n + 1 ≤ 195 ∧ TraceExec 7 prepare input y n ts ∧
    Executes 7 (prepare.program frontier) ⟨0, input⟩ 36 (n + 1) ∧
    y.mem = preparedMemory first 3#3 (clear input.mem 20 2) 20 24 2 4 ∧
    ∀ k u, Runs 7 (prepare.program frontier) ⟨0, input⟩ u k → k ≤ n →
      u.data.Bounded 7 ∧ ∃ live : Finset ℕ,
        (∀ a, u.data.mem a ≠ 0 ↔ a ∈ live) ∧
        (live.card + 32) * 7 ≤ (101 + 194 + 32) * 7 := by
  have h := prepare_resources (b := 5) (h := 20) (f := 24) (p := 1)
    first 3#3 input (Finset.range 101) input_bounded
    ?_ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ?_ ?_
  · simpa [first, preparationWidth] using h
  · intro a ha
    simp only [input] at ha
    split_ifs at ha <;> simp only [Finset.mem_range] <;> omega
  · decide
  · decide

/-- Native construction overwrites dirty heads and retains all four indices. -/
example : (prepare.eval 7 8 input).map (fun r =>
    (r.1.regs frontier, [r.1.mem 20, r.1.mem 21],
      (List.range 12).map (fun i => r.1.mem (24 + i)), r.1.mem 100)) =
    some (36, [33, 30], [0, 6, 0, 0, 7, 1, 27, 1, 2, 24, 0, 3], 17) := by
  decide +kernel

private def pipeline : Code .standard 32 :=
  .seq prepare
    (.seq (ram[ base ← #10; modulus ← keyModulus; state ← #0; operators ← #2 ])
      (.seq queryBucket
        (.seq (ram[ base ← #8; modulus ← #8; output ← #40; zero ← #0; one ← #1 ]) emitLoop)))

/-- These are actual successive native executions. Only the two matching bucket
records get their full second quarter evaluated; neither nonmatching record is emitted. -/
example : (pipeline.eval 7 8 input).map (fun r =>
    (r.1.regs link, r.1.regs output,
      (List.range 6).map (fun i => r.1.mem (40 + i)), r.1.mem 100)) =
      some (0, 46, [2, 2, 2, 4, 1, 2], 17) := by decide +kernel

/-- Zero-width states still retain all four indexed witnesses in one bucket. -/
example : (prepare.eval 7 8
    { regs := fun r => if r = base then 5 else if r = count then 2
        else if r = modulus ∨ r = keyModulus then 1
        else if r = heads then 20 else if r = frontier then 24 else 0
      mem := fun _ => 0 }).map (fun r =>
        (r.1.regs frontier, r.1.mem 20,
          (List.range 12).map (fun i => r.1.mem (24 + i)))) =
      some (36, 33, [0, 0, 0, 24, 0, 1, 27, 0, 2, 30, 0, 3]) := by decide +kernel

/-- An empty quarter emits its unique empty indexed word, rather than no word. -/
example : (prepare.eval 7 3
    { regs := fun r => if r = modulus then 8 else if r = initial then 5
        else if r = keyModulus then 2 else if r = heads then 20
        else if r = frontier then 24 else 0
      mem := fun _ => 0 }).map (fun r =>
        (r.1.regs frontier, r.1.mem 21, [r.1.mem 24, r.1.mem 25, r.1.mem 26])) =
      some (27, 24, [0, 5, 0]) := by decide +kernel

/-- All-zero and leading-zero operator words are distinct indexed objects. -/
example : decode 3 1 = [true, false, false] ∧
    encode [true, false, false] = 1 ∧ decode 3 4 = [false, false, true] := by decide

/-- Reversal preserves zero operators at both ends of a fixed-length word. -/
example : (reverseOperators.eval 7 8
    { regs := fun r => if r = count then 4 else if r = operators then 2 else 0
      mem := fun _ => 17 }).map (fun r => (r.1.regs reversed, r.1.mem 100)) =
      some (4, 17) := by decide +kernel

/-- Address/index overflow is rejected by the actual interpreter. -/
example : prepare.eval 4 8 input = none := by decide +kernel

/-- All new programs are deterministic and do not read the physical width. -/
example : prepare.IsRandFree ∧ ¬prepare.ReadsWidth ∧ queryBucket.IsRandFree ∧
    ¬queryBucket.ReadsWidth ∧ emitLoop.IsRandFree ∧ ¬emitLoop.ReadsWidth := by decide

/-- The list predicate is instantiated from actual native construction stores. -/
example : Linked (preparedMemory first 3#3 (clear input.mem 20 2) 20 24 2 4) 36
    ((preparedMemory first 3#3 (clear input.mem 20 2) 20 24 2 4) 21)
    ((bucketIndices first 3#3 2 1 4).map fun v => ((indexedState first 3#3 v).toNat, v)) :=
  preparedMemory_linked first 3#3 (clear input.mem 20 2) 20 24 2 4 1
    (by decide) (by decide) (by decide) (by decide)

private def built : Data 32 := ((prepare.eval 7 8 input).getD (input, 0)).1

private def emitInput : Data 32 :=
  built.set base 8 |>.set count 2 |>.set modulus 8 |>.set operators 2
    |>.set link 30 |>.set output 40 |>.set one 1 |>.set zero 0

private theorem actual_linked : Linked emitInput.mem 36 30 [(1, 2), (7, 1)] := by
  apply Linked.cons (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  apply Linked.cons (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hnext : emitInput.mem (emitInput.mem 30) = 0 := by decide +kernel
  rw [hnext]
  exact .nil

/-- The generic output-sensitive execution contract is nonvacuous on records
constructed by the real preparation run, with all memory/layout premises supplied. -/
example : ∃ y, ExecWithin 8 emitLoop emitInput y (2 * (11 * 2 + 20) + 2) ∧
    y.mem = emittedMemory [3#3, 1#3] 2 [(1, 2), (7, 1)] emitInput.mem 40 ∧
    y.regs output = 46 ∧ y.regs link = 0 := by
  apply emitLoop_exec (b := 8) (v := 2) (ptr := 30) (o := 40) (boundary := 36)
    [3#3, 1#3] [(1, 2), (7, 1)] emitInput
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (by decide) (by decide) (by decide) (by decide) actual_linked (by decide) (by decide)
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> decide +kernel +revert
  · simp
  · decide
