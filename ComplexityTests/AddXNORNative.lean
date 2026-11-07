/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Complexity.Cryptanalysis.AddXNORNativeResources

/-!
# Complete native Add/XNOR clients

The generic client starts with the standard input-to-memory convention and
ends with actual flat-program halting and a full memory-access transcript.
Kernel evaluations below execute the real loops, including input-header reads,
zero filling, buffer exchanges and lookup. No source-level cost oracle is used.
-/

public section

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR

/-- An arbitrary instance, not a finite-width specialization or a promise on its answer. -/
example {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    (Native.entry.program Native.answer).Answers (Native.wordWidth m as.length)
      (Native.encodeInput as s t) (Solvable as s t)
      (4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 27) :=
  Native.encoded_answers as s t

/-- The full trace footprint bounds all reused cells, not just final changed cells. -/
example {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    ∃ y n ts,
      n ≤ 4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 26 ∧
      TraceExec (Native.wordWidth m as.length) Native.entry
        (Data.init (Native.encodeInput as s t)) y n ts ∧
      Executes (Native.wordWidth m as.length) (Native.entry.program Native.answer)
        (State.init (Native.encodeInput as s t)) (y.regs Native.answer) (n + 1) ∧
      (y.regs Native.answer = 1 ↔ Solvable as s t) ∧ y.regs Native.answer < 2 ∧
      (Probe.reads ts ∪ Probe.writes ts).card ≤ 6 * 2 ^ m + 4 * as.length + 24 :=
  Native.encoded_resources as s t

/-- Modular addition wraps; the full native program accepts. -/
example : ((Native.entry.eval (Native.wordWidth 3 1) 9
    (Data.init (Native.encodeInput [1#3] 7#3 0#3))).map
      (fun result => result.1.regs Native.answer)) = some 1 := by decide +kernel

/-- The XNOR branch reaches the all-ones word. -/
example : ((Native.entry.eval (Native.wordWidth 3 1) 9
    (Data.init (Native.encodeInput [0#3] 0#3 7#3))).map
      (fun result => result.1.regs Native.answer)) = some 1 := by decide +kernel

/-- Neither branch reaches this target. -/
example : ((Native.entry.eval (Native.wordWidth 3 1) 9
    (Data.init (Native.encodeInput [0#3] 0#3 1#3))).map
      (fun result => result.1.regs Native.answer)) = some 0 := by decide +kernel

/-- The outer loop reuses both buffers over three layers. -/
example : ((Native.entry.eval (Native.wordWidth 2 3) 8
    (Data.init (Native.encodeInput [1#2, 1#2, 1#2] 0#2 3#2))).map
      (fun result => result.1.regs Native.answer)) = some 1 := by decide +kernel

/-- Width zero still has one state and two nonoverlapping one-cell buffers. -/
example : ((Native.entry.eval (Native.wordWidth 0 3) 8
    (Data.init (Native.encodeInput [0#0, 0#0, 0#0] 0#0 0#0))).map
      (fun result => result.1.regs Native.answer)) = some 1 := by decide +kernel

/-- Empty chains accept precisely equality of the actual initial and target words. -/
example : ((Native.entry.eval (Native.wordWidth 2 0) 5
    (Data.init (Native.encodeInput ([] : List (BitVec 2)) 1#2 1#2))).map
      (fun result => result.1.regs Native.answer)) = some 1 := by decide +kernel

example : ((Native.entry.eval (Native.wordWidth 2 0) 5
    (Data.init (Native.encodeInput ([] : List (BitVec 2)) 1#2 2#2))).map
      (fun result => result.1.regs Native.answer)) = some 0 := by decide +kernel

example : Native.entry.IsRandFree ∧ ¬Native.entry.ReadsWidth := Native.entry_fixed

example : (Native.entry.program Native.answer).length = 56 := Native.program_length

/-- The exponential bound follows from the actual run, including halt and stored word bits. -/
example {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    ∃ y n ts,
      n + 1 ≤ 45 * (as.length + 1) * 2 ^ m ∧
      TraceExec (Native.wordWidth m as.length) Native.entry
        (Data.init (Native.encodeInput as s t)) y n ts ∧
      Executes (Native.wordWidth m as.length) (Native.entry.program Native.answer)
        (State.init (Native.encodeInput as s t)) (y.regs Native.answer) (n + 1) ∧
      (y.regs Native.answer = 1 ↔ Solvable as s t) ∧
      ((Probe.reads ts ∪ Probe.writes ts).card + 18) * Native.wordWidth m as.length ≤
        (6 * 2 ^ m + 4 * as.length + 42) * Native.wordWidth m as.length :=
  Native.encoded_time_space as s t
