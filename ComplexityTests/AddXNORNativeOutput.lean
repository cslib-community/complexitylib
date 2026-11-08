/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all Complexity.Cryptanalysis.AddXNORNativeOutputResources
import all Complexity.Cryptanalysis.AddXNORNativeOutput
import all Complexity.Cryptanalysis.AddXNORNativeOutputBits
import all Complexity.Cryptanalysis.AddXNOROutputCodec
import all Complexity.Cryptanalysis.AddXNORNativeGlobalResources
import all Complexity.Cryptanalysis.AddXNORNativeGlobalTime
import all Complexity.Cryptanalysis.AddXNORNativeGlobalLayout
import all Complexity.Cryptanalysis.AddXNORNativeClassCounts
import all Complexity.Computability.WordRAM.Structured

/-!
# Charged native witness arrays and the actual bit-output machine

Native executions check both orientations, nonpalindromic packed words, leading
zero operators, miss status and dirty outside memory. The complete original-input
client derives an actual hit, serialized witness correctness, computed balance,
all-prefix support and the concrete linear Turing output-codec stage. Empty hits
and misses use the same unrestricted endpoint.
-/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native.Driver
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter
open Turing.MultiTapeTM

private def registers (dir : ℕ) : Data 40 where
  regs i := if i = tag then 2 else if i = orientation then dir else
    if i = bank bits ∨ i = bank Native.Quarter.operators ∨ i = bank firstOperators then 1 else
    if i = balance then 17 else 0
  mem a := if a = 99 then 13 else 0

/-- Output arrays differ in actual emitted order, with no host reversal operation. -/
example : ((Output.program 100 3 2 1 2).eval 16 16 (registers 0)).map
    (fun yn => (outputList yn.1.mem (yn.1.regs Output.result), yn.1.mem 99,
      yn.1.regs balance)) = some ([1, 1, 0, 0, 1, 0, 1, 1, 0], 13, 17) := by decide +kernel

example : ((Output.program 100 3 2 1 2).eval 16 16 (registers 1)).map
    (fun yn => (outputList yn.1.mem (yn.1.regs Output.result), yn.1.mem 99,
      yn.1.regs balance)) = some ([1, 0, 0, 1, 0, 1, 1, 0, 1], 13, 17) := by decide +kernel

example : ((Output.program 100 3 2 1 2).eval 16 16 ((registers 1).set tag 0)).map
    (fun yn => outputList yn.1.mem (yn.1.regs Output.result)) = some [0] := by decide +kernel

private def first : List (BitVec 3) := [1#3, 2#3, 4#3]
private def middle : List (BitVec 3) := [1#3]
private def L := compactSearchLayout 3 2 3 1 1 1
private def K := compactCounterLayout 3 2 3 1 1 1
private def input : Data 40 := Data.init (quarterInput first middle middle middle)

/-- Unequal quarters, non-self-inverse addition and colliding low keys lead to an
actual original-input hit. The bit machine consumes the encoded represented array. -/
example : ∃ (ops : List Bool) (y : Data 40) (n : ℕ), n + 1 ≤ 65204 ∧ ops.length = 6 ∧
    ExecutesList 16 ((dissectionOutput L K 1#3 2#3).program Output.result) ⟨0, input⟩
      (OutputCodec.encode (some ops)) (n + 1) ∧
    eval (ops.zip ((first ++ middle) ++ (middle ++ middle))) 1#3 = 2#3 ∧
    y.regs balance = 2 ∧
    (∀ k u, k ≤ n → Runs 16 ((dissectionOutput L K 1#3 2#3).program Output.result)
      ⟨0, input⟩ u k → u.data.SupportLe 14825 ∧ u.data.Bounded 16) ∧
    OutputCodec.decoder.toTM.ComputesInTimeAndSpace
      (encList encNat (outputList y.mem (y.regs Output.result))) (true :: ops) 45 0 := by
  obtain ⟨out, y, n, _, hn, _, he, _, miss, sound, mu, peak, _, codec⟩ :=
    original_output_resources (p := 2) (by decide) first middle middle middle 1#3 2#3
  have solvable : Solvable ((first ++ middle) ++ (middle ++ middle)) 1#3 2#3 :=
    ⟨decode 3 4 ++ decode 1 0 ++ decode 1 0 ++ decode 1 0, by decide, by decide +kernel⟩
  have hit : out ≠ none := fun h => miss.mp h solvable
  obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp hit
  have hs := sound ops hout
  have balance : computedBalance (p := 2) first middle middle middle 1#3 2#3 = 2 :=
    by decide +kernel
  refine ⟨ops, y, n, by change n ≤ 65203 at hn; omega, hs.1, ?_, hs.2, mu.trans balance,
    ?_, ?_⟩
  · have width : globalWidth 3 2 3 1 1 1 = 16 := by decide
    simpa only [hout, first, middle, L, K, input, List.length_cons, List.length_nil,
      width] using he
  · intro k u hk hu
    obtain ⟨support, bounded⟩ := peak k u hk hu
    rw [balance] at support
    exact ⟨support, bounded⟩
  · simpa only [hout, encOption_some, encBits, Function.Embedding.refl_apply,
      totalLength, first, middle,
      List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceMul] using codec

/-- A successful zero-operator instance returns status one, distinguished from a miss. -/
example : ∃ (y : Data 40) (n : ℕ), ExecutesList (globalWidth 0 0 0 0 0 0)
      ((dissectionOutput (compactSearchLayout 0 0 0 0 0 0)
        (compactCounterLayout 0 0 0 0 0 0) 0#0 0#0).program Output.result)
      ⟨0, Data.init (quarterInput (m := 0) [] [] [] [])⟩ [1] (n + 1) ∧
    y.regs balance = 1 := by
  obtain ⟨out, y, n, _, _, _, he, _, miss, sound, mu, _, _, _⟩ :=
    original_output_resources (p := 0) (by decide) [] [] [] [] 0#0 0#0
  have sol : Solvable (([] ++ []) ++ ([] ++ [])) 0#0 0#0 := ⟨[], rfl, rfl⟩
  obtain ⟨ops, hout⟩ := Option.ne_none_iff_exists'.mp (fun h => miss.mp h sol)
  have length := (sound ops hout).1
  have empty : ops = [] := List.length_eq_zero_iff.mp length
  refine ⟨y, n, ?_, mu.trans (by decide +kernel)⟩
  simpa only [hout, empty, OutputCodec.encode, List.map_nil, List.length_nil] using he

/-- Empty-quarter exhaustion returns the native miss array, rather than an empty hit. -/
example : ∃ (y : Data 40) (n : ℕ), ExecutesList (globalWidth 1 1 0 0 0 0)
      ((dissectionOutput (compactSearchLayout 1 1 0 0 0 0)
        (compactCounterLayout 1 1 0 0 0 0) 0#1 1#1).program Output.result)
      ⟨0, Data.init (quarterInput (m := 1) [] [] [] [])⟩ [0] (n + 1) ∧
    y.regs balance = 0 := by
  obtain ⟨out, y, n, _, _, _, he, _, miss, _, mu, _, _, _⟩ :=
    original_output_resources (p := 1) (by decide) [] [] [] [] 0#1 1#1
  have no : ¬Solvable (([] ++ []) ++ ([] ++ [])) 0#1 1#1 := by
    rintro ⟨ops, hlen, hsol⟩
    have empty : ops = [] := List.length_eq_zero_iff.mp hlen
    subst ops
    exact (by decide : (0#1 : BitVec 1) ≠ 1#1) hsol
  have hout := miss.mpr no
  refine ⟨y, n, ?_, mu.trans (by decide +kernel)⟩
  simpa only [hout, OutputCodec.encode, List.length_nil] using he

example : OutputCodec.wire none = [false] ∧
    OutputCodec.wire (some []) = [true, true, false] ∧
    OutputCodec.decoder.run 0 (OutputCodec.wire (some [false, true, false])) =
      [true, false, true, false] := by decide +kernel

example {W m p a b c d : ℕ} (layout : SearchLayout W m p a b c d)
    (counters : CounterLayout layout) (s t : BitVec m) :
    (dissectionOutput layout counters s t).size = 1108 := dissectionOutput_size _ _ _ _
