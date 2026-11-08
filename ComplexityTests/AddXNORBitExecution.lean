/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all Complexity.Cryptanalysis.AddXNORBitExecution
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Cryptanalysis.AddXNOROutputCodec
import all Complexity.Computability.WordRAM.Turing.ClockedListOutput
import all Complexity.Cryptanalysis.AddXNORNativeGlobalLayout
import all Complexity.Cryptanalysis.AddXNORNativeClassCounts

/-!
# Source-order bit inputs and actual fixed-program simulation

Check the concrete simulator/readback on small native programs, charged input
materialization including zero bindings, and the complete dissection bit bridge
on unequal quarters, non-self-inverse addition, colliding low keys and empty
hit/miss cases. The dissection clients use the unrestricted original-input
correctness theorem rather than assuming a simulator or a returned witness.
-/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.GenericRAM Turing.MultiTapeTM
open Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter
open Cslib.Cryptanalysis.AddXNOR.Native.Driver

example : BitInput.prepare (([1, 2], [0]), ([3, 4], [5, 6])) = [1, 2, 0, 6, 5, 4, 3] := rfl

/-- Zero input words are materialized, even though they do not occupy native nonzero support. -/
example : (SparseMemory.entries
    (BitInput.initial (([0, 0], []), ([], [0]))).memory).length = 4 := by decide +kernel

/-- The concrete bit simulator parks an immediate halt and actually reads initialized memory. -/
example : Cslib.WordRAM.Program.clockedList
    ([.halt 0] : Cslib.WordRAM.Program .standard 1) 8 3 [7, 0, 2] = [7, 0, 2] :=
  by decide +kernel

/-- A fault uses the specified fallback, rather than asserting termination or valid output. -/
example : Cslib.WordRAM.Program.clockedList
    ([.op (.const 0 256), .halt 0] : Cslib.WordRAM.Program .standard 1) 8 1 [7] = [] :=
  by decide +kernel

private def first : List (BitVec 3) := [1#3, 2#3, 4#3]
private def middle : List (BitVec 3) := [1#3]

/-- The returned bits are a real original-chain solution on a non-self-inverse/collision client.
The machine starts from original-order binary operands and performs its own memory readback. -/
example : ∃ ops : List Bool,
    BitExecution.solveBits 2 3 1 1 1 1#3 2#3 (BitInput.words first middle middle middle) =
      true :: ops ∧ ops.length = 6 ∧
      eval (ops.zip ((first ++ middle) ++ (middle ++ middle))) 1#3 = 2#3 := by
  obtain ⟨out, result, absent, sound⟩ :=
    BitExecution.original_bits_correct (p := 2) (by decide) first middle middle middle 1#3 2#3
  have sol : Solvable ((first ++ middle) ++ (middle ++ middle)) 1#3 2#3 :=
    ⟨decode 3 4 ++ decode 1 0 ++ decode 1 0 ++ decode 1 0, by decide, by decide +kernel⟩
  obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp (fun h => absent.mp h sol)
  have hs := sound ops hout
  refine ⟨ops, ?_, hs.1, hs.2⟩
  simpa only [hout, encOption_some, encBits, Function.Embedding.refl_apply,
    first, middle, List.length_cons, List.length_nil] using result

example : forwardCount middle middle 0#3 0#1 = 2 ∧
    backwardCount middle middle 4#3 0#1 = 2 := by decide +kernel

/-- A nonempty tied class uses forward retention; the same encoded execution theorem applies. -/
example : ∃ ops : List Bool,
    BitExecution.solveBits 1 1 1 1 1 0#3 4#3 (BitInput.words middle middle middle middle) =
      true :: ops ∧ ops.length = 4 ∧
      eval (ops.zip ((middle ++ middle) ++ (middle ++ middle))) 0#3 = 4#3 := by
  obtain ⟨out, result, absent, sound⟩ :=
    BitExecution.original_bits_correct (p := 1) (by decide) middle middle middle middle 0#3 4#3
  have sol : Solvable ((middle ++ middle) ++ (middle ++ middle)) 0#3 4#3 :=
    ⟨[false, false, false, false], by decide, by decide +kernel⟩
  obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp (fun h => absent.mp h sol)
  have hs := sound ops hout
  refine ⟨ops, ?_, hs.1, hs.2⟩
  simpa only [hout, encOption_some, encBits, Function.Embedding.refl_apply,
    middle, List.length_cons, List.length_nil] using result

/-- A source-order input has at most linear framed operand size in the full word width. -/
example : (BitInput.encoding (BitInput.words first middle middle middle)).length ≤ 172 := by
  have h := BitInput.encoding_words_le first middle middle middle
  exact h

/-- Empty hits survive the entire input/simulation/readback/decoder composition. -/
example : BitExecution.solveBits 0 0 0 0 0 0#0 0#0
    (BitInput.words (m := 0) [] [] [] []) = [true] := by
  obtain ⟨out, result, absent, sound⟩ :=
    BitExecution.original_bits_correct (p := 0) (by decide) [] [] [] [] 0#0 0#0
  have sol : Solvable (([] ++ []) ++ ([] ++ [])) 0#0 0#0 := ⟨[], rfl, rfl⟩
  obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp (fun h => absent.mp h sol)
  have empty : ops = [] := List.length_eq_zero_iff.mp (sound ops hout).1
  simpa only [hout, empty, encOption_some, encBits, Function.Embedding.refl_apply,
    List.length_nil] using result

/-- Exhaustive misses emit the empty optional-bit encoding, distinct from the empty hit. -/
example : BitExecution.solveBits 1 0 0 0 0 0#1 1#1 (BitInput.words (m := 1) [] [] [] []) = [] := by
  obtain ⟨out, result, absent, _⟩ :=
    BitExecution.original_bits_correct (p := 1) (by decide) [] [] [] [] 0#1 1#1
  have no : ¬Solvable (([] ++ []) ++ ([] ++ [])) 0#1 1#1 := by
    rintro ⟨ops, hlen, hs⟩
    have empty : ops = [] := List.length_eq_zero_iff.mp hlen
    subst ops
    exact (by decide : (0#1 : BitVec 1) ≠ 1#1) hs
  simpa only [absent.mpr no, encOption_none, List.length_nil] using result

/-- The bit machine is obtained without any simulation, efficiency or witness premise. -/
example {m : ℕ} (p a b c d : ℕ) (s t : BitVec m) :
    ComputableInO (BitExecution.solveBits p a b c d s t) BitInput.encoding encBits
      (BitExecution.executionCertificate p a b c d s t).time
      (BitExecution.executionCertificate p a b c d s t).space :=
  (BitExecution.solveBitsCertificate p a b c d s t).computes

example {m : ℕ} (p a b c d : ℕ) (s t : BitVec m) :
    (BitExecution.program p a b c d s t).length = 1109 :=
  BitExecution.program_length p a b c d s t
