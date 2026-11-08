/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all Complexity.Cryptanalysis.AddXNORGeneratedRunInput
import all Complexity.Cryptanalysis.AddXNORProgramGeneration
import all Complexity.Cryptanalysis.AddXNORProgramTemplate
import all Complexity.Computability.WordRAM.ProgramLiterals.Encoding
import all Complexity.Computability.WordRAM.ProgramLiterals.Expressions
import all Complexity.Cryptanalysis.AddXNORNativeGlobalTime
import all Complexity.Cryptanalysis.AddXNORNativeClassCounts

/-!
# Uniform original-input program/width/clock/state generation

Check actual metadata parsing, literal computation, instruction roundtrip and
malformed row rejection. General clients construct the generated executable and
its charged packet without executable/resource premises. Original-input runs
cover strict inverse/colliding keys and non-self-inverse addition, nonempty
forward/tie classes, and empty hit/miss outcomes. These are generation plus actual
RAM-run certificates, not a claimed uniform runtime-program bit interpreter.
-/

set_option linter.privateModule false

open Turing.MultiTapeTM Cslib.WordRAM Cslib.WordRAM.ProgramLiterals
open Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native.Driver
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter
open ProgramGeneration

private def exampleMetadata := metadata 3 2 3 1 1 1 1 2

/-- Runtime metadata computes real counter/layout/immediate values, including repeated zeros. -/
example : (evaluate ProgramTemplate.literalTemplate exampleMetadata).take 12 =
    [4, 7, 4, 0, 1, 1, 11, 15, 4, 7, 11, 1] := by decide +kernel

/-- Concrete rows preserve full operation codes, register indices, labels and zero literals. -/
example : deserialize 4 [[0, 1, 0], [2, 7, 0, 1, 2], [8, 0, 2, 3], [9, 0]] =
    some [.op (.const 1 0), .op (.bin .xor 0 1 2), .branch (.lt 0 2) 3, .halt 0] :=
  by decide +kernel

example : deserialize 4 [[0, 4, 0]] = none ∧ deserialize 4 [[99, 0]] = none ∧
    deserialize 4 [[2, 10, 0, 1, 2]] = none := by decide +kernel

/-- The parser's total fallback is explicit; this is not a validity-recognition claim. -/
example : readMetadata ([3, 2], [1]) = metadata 3 2 0 0 0 0 1 0 := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- For all runtime headers, the actual serialized program decodes to the reviewed executable. -/
example (h : ProgramTemplate.Metadata) :
    deserialize 40 (serialize (generate h)) =
      some ((ProgramTemplate.nativeCode h).program Output.result) := decode_generate h

example (h : ProgramTemplate.Metadata) :
    (serialize (generate h)).length = 1109 ∧
      ∀ row ∈ serialize (generate h), row.length ≤ 5 := generated_rows h

/-- These are real uniform generation/packet machines, without a supplied compiler contract. -/
example : sourceGenerationCertificate.IsPolynomial := sourceGenerationCertificate_isPolynomial
example : GeneratedRunInput.packetCertificate.IsPolynomial :=
  GeneratedRunInput.packetCertificate_isPolynomial

private def first : List (BitVec 3) := [1#3, 2#3, 4#3]
private def middle : List (BitVec 3) := [1#3]
private def original := originalSource 2 first middle middle middle 1#3 2#3

/-- Quarter lengths come from actual original words, rather than separate semantic advice. -/
example : sourceMetadata original = rawMetadata 3 2 3 1 1 1 1 2 := by decide +kernel

example : (sourceEncoding original).length ≤ 231 :=
  GeneratedRunInput.original_input_length 2 first middle middle middle 1#3 2#3

/-- The derived physical width and clock are actually materialized from metadata. -/
example : (GeneratedRunInput.packet original).1.2 = (16, 65204) := by decide +kernel

example : (Cslib.GenericRAM.SparseMemory.entries
    (GeneratedRunInput.packet original).2.memory).length = 7 := by decide +kernel

/-- The generated executable's actual simulated run returns a valid original witness,
including unequal quarters, strict inverse retention, colliding low keys and real addition. -/
example : ∃ ops : List Bool,
    GeneratedRunInput.run (GeneratedRunInput.packet original) = true :: ops ∧
      ops.length = 6 ∧ eval (ops.zip ((first ++ middle) ++ (middle ++ middle))) 1#3 = 2#3 := by
  obtain ⟨out, result, absent, sound⟩ := GeneratedRunInput.original_correct (p := 2)
    (by decide) first middle middle middle 1#3 2#3
  have sol : Solvable ((first ++ middle) ++ (middle ++ middle)) 1#3 2#3 :=
    ⟨decode 3 4 ++ decode 1 0 ++ decode 1 0 ++ decode 1 0, by decide, by decide +kernel⟩
  obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp (fun h => absent.mp h sol)
  refine ⟨ops, ?_, (sound ops hout).1, (sound ops hout).2⟩
  simpa only [original, hout, encOption_some, encBits, Function.Embedding.refl_apply] using result

example : backwardCount middle middle 2#3 0#2 = 1 ∧
    forwardCount first middle 1#3 0#2 = 4 := by decide +kernel

/-- A nonempty forward/tie client uses the same general generated-code endpoint. -/
example : ∃ ops : List Bool,
    GeneratedRunInput.run (GeneratedRunInput.packet
      (originalSource 1 middle middle middle middle 0#3 4#3)) = true :: ops ∧
      ops.length = 4 ∧ eval (ops.zip ((middle ++ middle) ++ (middle ++ middle))) 0#3 = 4#3 := by
  obtain ⟨out, result, absent, sound⟩ := GeneratedRunInput.original_correct (p := 1)
    (by decide) middle middle middle middle 0#3 4#3
  have sol : Solvable ((middle ++ middle) ++ (middle ++ middle)) 0#3 4#3 :=
    ⟨[false, false, false, false], by decide, by decide +kernel⟩
  obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp (fun h => absent.mp h sol)
  refine ⟨ops, ?_, (sound ops hout).1, (sound ops hout).2⟩
  simpa only [hout, encOption_some, encBits, Function.Embedding.refl_apply] using result

/-- Empty hits and exhaustive empty-quarter misses remain distinct after actual generation. -/
example : GeneratedRunInput.run (GeneratedRunInput.packet
    (originalSource 0 [] [] [] [] 0#0 0#0)) = [true] := by
  obtain ⟨out, result, absent, sound⟩ := GeneratedRunInput.original_correct (p := 0)
    (by decide) [] [] [] [] 0#0 0#0
  have sol : Solvable (([] ++ []) ++ ([] ++ [])) 0#0 0#0 := ⟨[], rfl, rfl⟩
  obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp (fun h => absent.mp h sol)
  have empty : ops = [] := List.length_eq_zero_iff.mp (sound ops hout).1
  simpa only [hout, empty, encOption_some, encBits, Function.Embedding.refl_apply] using result

example : GeneratedRunInput.run (GeneratedRunInput.packet
    (originalSource 1 [] [] [] [] 0#1 1#1)) = [] := by
  obtain ⟨out, result, absent, _⟩ := GeneratedRunInput.original_correct (p := 1)
    (by decide) [] [] [] [] 0#1 1#1
  have no : ¬Solvable (([] ++ []) ++ ([] ++ [])) 0#1 1#1 := by
    rintro ⟨ops, hlen, hs⟩
    have empty : ops = [] := List.length_eq_zero_iff.mp hlen
    subst ops
    exact (by decide : (0#1 : BitVec 1) ≠ 1#1) hs
  simpa only [absent.mpr no, encOption_none] using result
