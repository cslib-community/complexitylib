/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.RuntimeAccess

/-!
# Uniform runtime accessor clients

All runs use the same machine, including a family with unbounded changing binary parameters
and suffix lengths. Native certificates quantify over the whole admissible runtime domain.
The original word remains the literal tail of the framed input.
-/

public section

namespace Cslib.Complexity.VirtualWordRuntimeTest

open Turing Turing.MultiTapeTM VirtualWord.Runtime

/-- A nonconstant family: cut, suffix length, address and original word vary with `n`. -/
def family (n : ℕ) : {p : Input // Admissible p} :=
  ⟨((n - min n (Nat.clog 2 n), List.replicate (min n (Nat.clog 2 n)) false, n),
      List.replicate n true), by
    constructor
    · simp only [List.length_replicate]
      omega
    · constructor
      · simp
      · simp only [List.length_replicate]
        exact min_le_right _ _⟩

-- The same code serves varying data; these include empty, length-one and non-power-of-two words.
example : (List.range 6).map (fun n => machine.output (encInput (family n).val)
    (2 * (VirtualWord.encData (family n).val.1).length + 2)) =
    [[false], [false], [false], [false], [false], [false]] := by decide

-- Prefix, suffix boundary, last bit and default at length five.
example : (List.range 6).map (fun i => machine.output
    (encInput ((2, [false, true, false], i), [true, true, true, false, true]))
    (2 * (VirtualWord.encData (2, [false, true, false], i)).length + 2)) =
    [[true], [true], [false], [true], [false], [false]] := by decide

-- Empty prefix and long suffix: correct total behavior without a logarithmic-size claim.
example : machine.output (encInput ((0, [true, false, true], 2), []))
    (2 * (VirtualWord.encData (0, [true, false, true], 2)).length + 2) = [true] := by decide

-- Invalid cut: the declared cut is used literally, with false in the gap before the suffix.
example : machine.output (encInput ((10, [true], 4), [true]))
    (2 * (VirtualWord.encData (10, [true], 4)).length + 2) = [false] := by decide
example : machine.output (encInput ((10, [true], 10), [true]))
    (2 * (VirtualWord.encData (10, [true], 10)).length + 2) = [true] := by decide

-- A huge binary address does not allocate a unary counter or word of that length.
example : machine.output (encInput ((1, [true], 1000000), [true]))
    (2 * (VirtualWord.encData (1, [true], 1000000)).length + 2) = [false] := by decide
example : ¬ Admissible ((1, [true], 1000000), [true]) := by simp [Admissible]
example : ¬ Admissible ((10, [true], 0), [true]) := by simp [Admissible]
example : ¬ Admissible ((0, [true, true], 0), []) := by simp [Admissible]

/-- A local reconstruction is an actual consumer of the runtime initialization and read. -/
theorem local_query_reads (i : ℕ) :
    let d := localQueryAccessData 3 [false, true] i
    machine.output (encInput (d, [false, true, false]))
      (2 * (VirtualWord.encData d).length + 2) = [[false, false, true].getD i false] := by
  exact (show LocalSelfReductionQuery [false, true, false] [false, false, true] by decide)
    |>.runtime_output i

/-- One native certificate covers the whole nonconstant runtime family, with a bound measured
against the original-word length. It is not a separately compiled certificate for each `n`. -/
theorem native_runtime : ∃ time c, ComputableInTimeAndSpace
    (fun p : {p : Input // Admissible p} => access p.val)
    ((Function.Embedding.subtype Admissible).trans encInput) encBool time
    (fun p => c * (Nat.log2 p.val.2.length + 1)) := access_inOriginalLogSpace

example : (family 0).val.1 = (0, [], 0) := by decide
example : (family 1).val.1 = (1, [], 1) := by decide
example : (family 3).val.1 = (1, [false, false], 3) := by decide
example : (family 5).val.1 = (2, [false, false, false], 5) := by decide

-- Exact semantic query length and a checked local-reconstruction size-domain client.
example : (VirtualWord.word [false, true, false] 1 [false, true]).length = 3 := by decide
example : Admissible (localQueryAccessData 3 [false, true] 3, [false, true, false]) := by
  exact (show LocalSelfReductionQuery [false, true, false] [false, false, true] by decide)
    |>.runtime_admissible (by decide)

-- Encoding preserves the entire original tail exactly.
example (n : ℕ) : dropFrame (encInput (family n).val) = List.replicate n true := by
  exact dropFrame_frame_append _ _

end Cslib.Complexity.VirtualWordRuntimeTest
