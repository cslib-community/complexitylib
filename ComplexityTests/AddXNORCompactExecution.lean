/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORCompactExecution
import all Complexity.Computability.WordRAM.Interpreter.CompactRun
import all Complexity.Computability.WordRAM.Interpreter.Compact
import all Complexity.Computability.GenericRAM.SparseMemory.Compact
import all Complexity.Computability.GenericRAM.Simulation.Run
import all Complexity.Computability.WordRAM.Turing
import all Complexity.Computability.WordRAM.Defs
import all Complexity.Cryptanalysis.AddXNORNativeClassCounts

/-!
# Actual default deletion and source-convention execution clients

Historical zero writes consume no bindings in the executed compacting loop.
Nonzero overwrites and nonzero defaults retain their semantics. One source machine
handles real non-self-inverse addition/XNOR with colliding classes and a miss;
source splitting includes every residual quarter case. Prefix bounds are general
in the execution clock, including post-halt parking, rather than sampled traces.
-/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.GenericRAM Turing.MultiTapeTM
open Cslib.Cryptanalysis.AddXNOR Native.Driver

private def zeros : Program .standard 3 :=
  [.op (.const 0 1), .op (.store 0 1), .op (.const 2 1), .op (.bin .add 0 0 2), .jump 1]

private def stored {r : ℕ} (out : FiniteState.Result Basis.standard.genericModel r) : ℕ :=
  (out.bind (fun v => v.getLeft?)).elim 0 (fun s => (SparseMemory.entries s.memory).length)

/-- The original interpreter really retains all three zero writes plus the zero input header. -/
example : stored (FiniteState.run (M := Basis.standard.genericModel) 8 zeros.toGeneric 13
    (initState .standard 3 [])) = 4 := by decide +kernel

/-- The actual new round executes filtering: none of those historical bindings survives. -/
example : stored (Interpreter.compactRound^[13]
    (Interpreter.compactLoop (Interpreter.initial
      (13, (8, zeros), initState .standard 3 [])))).2 = 0 := by decide +kernel

/-- The prefix refinement covers arbitrary runtime programs, physical widths and clocks. -/
example (x : Interpreter.RunInput 3) :
    (Interpreter.compactRound^[x.1] (Interpreter.compactLoop (Interpreter.initial x))).2 =
      Interpreter.compactResult (FiniteState.run x.2.1.1 x.2.1.2.toGeneric x.1 x.2.2) :=
  Interpreter.compact_run x

private def overwrite : SparseMemory ℕ ℕ :=
  AList.insert 4 0 (AList.insert 4 9 (AList.insert 4 3 ∅))

example : (SparseMemory.entries overwrite).length = 1 ∧
    SparseMemory.entries (SparseMemory.compact 0 overwrite) = [] := by decide +kernel

example : SparseMemory.entries (SparseMemory.compact 7
    (AList.insert 1 9 (AList.insert 0 7 (∅ : SparseMemory ℕ ℕ)))) = [(1, 9)] := by decide +kernel

example (a : ℕ) : SparseMemory.read 7 a (SparseMemory.compact 7
    (AList.insert 1 9 (AList.insert 0 7 (∅ : SparseMemory ℕ ℕ)))) =
    SparseMemory.read 7 a (AList.insert 1 9 (AList.insert 0 7 (∅ : SparseMemory ℕ ℕ))) :=
  SparseMemory.read_compact _ _ _

/-- Empty and all three residual sizes are computed by the source adapter. -/
example : (List.range 8).map (fun q =>
    let parts := Source.quarters (List.range q)
    (parts.1.1.length, parts.1.2.length, parts.2.1.length, parts.2.2.length)) =
    [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 0, 2), (0, 0, 0, 3),
      (1, 1, 1, 1), (1, 1, 1, 2), (1, 1, 1, 3), (1, 1, 1, 4)] := by decide +kernel

private def tail : List (BitVec 3) := [1#3, 2#3, 4#3, 1#3, 1#3, 1#3]
private def parts := Source.quarters tail

example : forwardCount parts.1.1 parts.1.2 1#3 0#1 = 2 ∧
    backwardCount parts.2.1 parts.2.2 0#3 0#1 = 8 := by decide +kernel

/-- The source's raw input really contains its first operand, not a separately supplied seed. -/
example : Source.prepare (Source.ofWords 1 1#3 tail) =
    ProgramGeneration.originalSource 1 [1#3] [2#3] [4#3] [1#3, 1#3, 1#3] 1#3 0#3 :=
  by decide +kernel

example : Source.prepare (Source.ofWords 100 1#3 tail) =
    Source.prepare (Source.ofWords 1 1#3 tail) := by decide +kernel

/-- Derived representation bounds hold at EVERY executed prefix, even after early exit. -/
example (j : ℕ) :
    let P := BitExecution.program 1 parts.1.1.length parts.1.2.length
      parts.2.1.length parts.2.2.length 1#3 0#3
    let W := globalWidth 3 1 parts.1.1.length parts.1.2.length parts.2.1.length parts.2.2.length
    (FiniteState.resultEncoding Basis.standard.encoding
      (Interpreter.compactResult (FiniteState.run W P.parkHalts.toGeneric j
        (initState .standard 40 (quarterInput parts.1.1 parts.1.2 parts.2.1 parts.2.2))))).length ≤
      stateBound 40 (labelBound P.parkHalts.toGeneric) W
        (CompactExecution.peak 1 parts.1.1.length parts.1.2.length parts.2.1.length parts.2.2.length
          (computedBalance (p := 1) parts.1.1 parts.1.2 parts.2.1 parts.2.2 1#3 0#3)) :=
  CompactExecution.original_compact_encoding (p := 1) (by decide)
    parts.1.1 parts.1.2 parts.2.1 parts.2.2 1#3 0#3 j

/-- One and the same source machine produces a genuine original zero-target witness with
addition and XNOR, and an exhaustive empty-tail miss. No simulator/resource premise is supplied. -/
example : ∃ (c k : ℕ) (Q : Type) (_ : Finite Q) (machine : Turing.MultiTapeTM k Bool Q),
    (∃ ops : List Bool,
      machine.ComputesInTimeAndSpace (Source.encoding (Source.ofWords 1 1#3 tail)) (true :: ops)
        (c * (Source.sourceCertificate.time (Source.ofWords 1 1#3 tail) + 1))
        (c * (Source.sourceCertificate.space (Source.ofWords 1 1#3 tail) + 1)) ∧
      ops.length = 6 ∧ eval (ops.zip tail) 1#3 = 0#3) ∧
    machine.ComputesInTimeAndSpace (Source.encoding (Source.ofWords 1 1#3 [])) []
      (c * (Source.sourceCertificate.time (Source.ofWords 1 1#3 []) + 1))
      (c * (Source.sourceCertificate.space (Source.ofWords 1 1#3 []) + 1)) := by
  obtain ⟨c, k, Q, hQ, machine, computes⟩ := Source.original_machine
  refine ⟨c, k, Q, hQ, machine, ?_, ?_⟩
  · obtain ⟨out, run, miss, sound⟩ := computes 3 1 1#3 tail
    have sol : Solvable tail 1#3 0#3 :=
      ⟨[false, false, false, false, true, false], by decide, by decide +kernel⟩
    obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp (fun h => miss.mp h sol)
    refine ⟨ops, ?_, (sound ops hout).1, (sound ops hout).2⟩
    simpa only [hout, encOption_some, encBits_apply] using run
  · obtain ⟨out, run, miss, _⟩ := computes 3 1 1#3 []
    have no : ¬Solvable [] 1#3 0#3 := by
      rintro ⟨ops, hlen, heval⟩
      have empty : ops = [] := List.length_eq_zero_iff.mp hlen
      subst ops
      exact (by decide : (1#3 : BitVec 3) ≠ 0#3) heval
    simpa only [miss.mpr no, encOption_none] using run

/-- Zero-width inputs and zero-length tails remain well-defined source-convention calls. -/
example : ∃ out : Option (List Bool),
    GeneratedRunInput.run (GeneratedRunInput.packet (Source.prepare
      (Source.ofWords 0 0#0 []))) = encOption encBits out ∧
    (out = none ↔ ¬Solvable [] 0#0 0#0) ∧
    (∀ ops, out = some ops → ops.length = 0 ∧ eval (ops.zip []) 0#0 = 0#0) :=
  Source.original_correct 0 0#0 []
