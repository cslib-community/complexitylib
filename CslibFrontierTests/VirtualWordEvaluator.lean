/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.RuntimeEvaluator

/-!
# Native virtual-input evaluator clients

An OR evaluator scans the complete virtual word twice with one saved bit. A NAND-state
consumer also checks that state survives the pass boundary. All examples use the same runtime
machine for changing cuts, suffixes and original lengths; native certificates cover unbounded
lengths, not just these small executions. The header is supplied explicitly.
-/

public section

namespace Cslib.Complexity.VirtualWordEvaluatorTest

open Turing Turing.MultiTapeTM VirtualWord

/-- The Boolean OR consumer is nonconstant in the virtual input. -/
def orStep (p : Bool × Bool) : Bool := p.1 || p.2

/-- A family with unbounded original length and changing header, with no copied prefix. -/
def family (n : ℕ) (b : Bool) : {p : Runtime.Input // Runtime.Admissible p} :=
  ⟨((n - min n (Nat.clog 2 n), List.replicate (min n (Nat.clog 2 n)) b, 0),
      List.replicate n false), by
    constructor
    · simp only [List.length_replicate]
      omega
    · constructor
      · exact Nat.zero_le _
      · simp only [List.length_replicate]
        exact min_le_right _ _⟩

-- Empty, singleton and non-power-of-two lengths; nonconstant answers at changing runtime data.
example : (List.range 6).map (fun n => (Evaluator.machine orStep).output
    (Runtime.encInput (family n true).val)
    (2 * (encData (family n true).val.1).length + 2 +
      2 * Evaluator.width (family n true).val.1)) =
    [[false], [false], [true], [true], [true], [true]] := by decide

example : (List.range 6).map (fun n => (Evaluator.machine orStep).output
    (Runtime.encInput (family n false).val)
    (2 * (encData (family n false).val.1).length + 2 +
      2 * Evaluator.width (family n false).val.1)) =
    [[false], [false], [false], [false], [false], [false]] := by decide

-- A true bit deep in the prefix is observed, despite false suffix and final original bit.
example : (Evaluator.machine orStep).output
    (Runtime.encInput ((3, [false, false], 0), [false, true, false, false, false]))
    (2 * (encData (3, [false, false], 0)).length + 2 + 2 * 5) = [true] := by decide

-- Two complete passes, retaining the evaluator state rather than restarting at the boundary.
example : Evaluator.value (fun p => !(p.1 && p.2)) ((2, [true], 0), [true, true]) 3 =
    true := by decide
example : (Evaluator.machine fun p => !(p.1 && p.2)).output
    (Runtime.encInput ((2, [true], 0), [true, true]))
    (2 * (encData (2, [true], 0)).length + 2 + 2 * 3) = [false] := by decide

-- Length one with empty suffix; the original input is read twice.
example : (Evaluator.machine orStep).output (Runtime.encInput ((1, [], 0), [true]))
    (2 * (encData (1, [], 0)).length + 2 + 2) = [true] := by decide

-- Empty prefix, oversized suffix: total behavior, with no original-log claim for these data.
example : (Evaluator.machine orStep).output (Runtime.encInput ((0, [false, true], 0), []))
    (2 * (encData (0, [false, true], 0)).length + 2 + 4) = [true] := by decide

-- Invalid cut uses the declared suffix offset, including a false gap in the original tail.
example : (Evaluator.machine orStep).output (Runtime.encInput ((3, [true], 0), [false]))
    (2 * (encData (3, [true], 0)).length + 2 + 8) = [true] := by decide

/-- One native program, not separately compiled instances for the finite test inputs. -/
theorem native_or : ∃ time c, ComputableInTimeAndSpace
    (fun p : {p : Runtime.Input // Runtime.Admissible p} => Evaluator.evaluate orStep p.val)
    ((Function.Embedding.subtype Runtime.Admissible).trans Runtime.encInput) encBool time
    (fun p => c * (Nat.log2 p.val.2.length + 1)) :=
  Evaluator.evaluate_inOriginalLogSpace orStep

/-- The exact unbounded first-halt clock applies to every length in the family. -/
theorem family_terminates (n : ℕ) (b : Bool) :
    let p := (family n b).val
    let T := 2 * (encData p.1).length + 2 + 2 * Evaluator.width p.1
    (Evaluator.machine orStep).halted
      ((Evaluator.machine orStep).run (Runtime.encInput p) T) = true ∧
    ∀ t < T, (Evaluator.machine orStep).halted
      ((Evaluator.machine orStep).run (Runtime.encInput p) t) = false :=
  Evaluator.first_halt orStep (family n b).val

/-- The complete reconstructed local query is consumed by the evaluator. -/
theorem local_query_evaluates :
    let d := localQueryAccessData 3 [false, true] 0
    (Evaluator.machine orStep).output (Runtime.encInput (d, [false, true, false]))
      (2 * (encData d).length + 2 + 2 * Evaluator.width d) = [true] := by
  have h := (show LocalSelfReductionQuery [false, true, false] [false, false, true] by decide)
    |>.runtime_evaluate orStep
  exact h

-- Original-tail preservation is independent of the number of consumer reads.
example (n : ℕ) (b : Bool) :
    dropFrame (Runtime.encInput (family n b).val) = List.replicate n false :=
  dropFrame_frame_append _ _

end Cslib.Complexity.VirtualWordEvaluatorTest
