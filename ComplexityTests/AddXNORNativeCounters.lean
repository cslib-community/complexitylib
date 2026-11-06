/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Complexity.Cryptanalysis.AddXNORNativeCounters

/-!
# Native multiplicity-preserving counter preprocessing

The generic client covers every width and operand list. Kernel executions check
actual initialized array contents, including two branches with the same state,
repeated buffer reuse, empty chains and width zero. These are preprocessing
clients; they do not assert a streaming dissection resource theorem.
-/

public section

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR

example {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) :
    ∃ y n ts,
      n + 1 ≤ 43 * (q + 1) * 2 ^ m ∧
      TraceExec (Native.Counters.wordWidth m q) Native.Counters.entry
        (Data.init (Native.encodeInput (List.ofFn as) s t)) y n ts ∧
      Executes (Native.Counters.wordWidth m q) (Native.Counters.entry.program Native.source)
        (State.init (Native.encodeInput (List.ofFn as) s t)) (y.regs Native.source) (n + 1) ∧
      (∀ g : BitVec m, y.mem (y.regs Native.source + g.toNat) = solutionCount as s g) ∧
      ((Probe.reads ts ∪ Probe.writes ts).card + 18) * Native.Counters.wordWidth m q ≤
        (43 * (q + 1) * 2 ^ m + 18) * Native.Counters.wordWidth m q :=
  Native.Counters.encoded_resources as s t

/-- Width zero has one state but eight indexed operator strings, not one. -/
example : ((Native.Counters.entry.eval (Native.Counters.wordWidth 0 3) 8
    (Data.init (Native.encodeInput [0#0, 0#0, 0#0] 0#0 0#0))).map
      (fun result => result.1.mem (result.1.regs Native.source))) = some 8 := by decide +kernel

/-- Both buffers are reused; coincident states retain all four occurrences. -/
example : ((Native.Counters.entry.eval (Native.Counters.wordWidth 2 3) 8
    (Data.init (Native.encodeInput [0#2, 0#2, 0#2] 0#2 0#2))).map
      (fun result => (result.1.mem (result.1.regs Native.source),
        result.1.mem (result.1.regs Native.source + 3)))) = some (4, 4) := by decide +kernel

/-- A modular-addition hit and a separate XNOR hit both contribute. -/
example : ((Native.Counters.entry.eval (Native.Counters.wordWidth 2 1) 7
    (Data.init (Native.encodeInput [1#2] 3#2 0#2))).map
      (fun result => (result.1.mem (result.1.regs Native.source),
        result.1.mem (result.1.regs Native.source + 1)))) = some (1, 1) := by decide +kernel

/-- No operands leaves exactly the initialized singleton. -/
example : ((Native.Counters.entry.eval (Native.Counters.wordWidth 2 0) 5
    (Data.init (Native.encodeInput ([] : List (BitVec 2)) 1#2 0#2))).map
      (fun result => (result.1.mem (result.1.regs Native.source),
        result.1.mem (result.1.regs Native.source + 1)))) = some (0, 1) := by decide +kernel

example : Native.Counters.entry.IsRandFree ∧ ¬Native.Counters.entry.ReadsWidth :=
  Native.Counters.entry_fixed
