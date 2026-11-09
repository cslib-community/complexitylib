/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Cryptanalysis.AddXNORNativeProbe
import all CslibFrontier.Cryptanalysis.AddXNORNativeRetain
import all CslibFrontier.Cryptanalysis.AddXNORNativeDictionary

/-!
# Complete native backward-probe clients

The symbolic execution client supplies every precondition on a physical node,
a reversed operand array and a retained full-state slot. Kernel runs distinguish
presence from zero witness values and check an absent full key.
-/

set_option linter.privateModule false

public section

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR.Native
open Quarter Dictionary

private def input (s : ℕ) : Data 32 :=
  { regs := fun r => if r = base then 5 else if r = count then 1
      else if r = modulus then 4 else if r = link then 10
      else if r = table then 40 else if r = one then 1 else 0
    mem := fun a => if a = 5 then 1 else if a = 11 then s
      else if a = 12 then 3 else if a = 43 then 1 else if a = 30 then 17 else 0 }

/-- Inverting one addition by one at state two reaches full state one.
The retained zero witnesses are present because their encoded tag is one. -/
example : ∃ y, ExecWithin 8 probeBody (input 2) y 51 ∧
    y.mem = (input 2).mem ∧ y.regs state = 1 ∧
    y.regs firstOperators = 3 ∧ y.regs operators = 0 ∧ y.regs link = 0 ∧
    y.regs operand = 1 ∧ y.regs bits = 0 ∧ y.regs one = 1 := by
  exact probeBody_exec (W := 8) (m := 2) (b := 5) (ptr := 10)
    (D := 40) (s := 2) (u := 3) (v := 0) [1#2] (input 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

example : (probeBody.eval 8 8 (input 2)).map (fun r =>
    (r.1.regs state, r.1.regs operand, r.1.regs bits, r.1.mem 30)) =
      some (1, 1, 0, 17) := by decide +kernel

/-- A different complete state does not reuse the present key's witness. -/
example : (probeBody.eval 8 8 (input 0)).map (fun r =>
    (r.1.regs state, r.1.regs operand, r.1.regs bits)) =
      some (3, 0, 0) := by decide +kernel

private def scanInput (second : ℕ) : Data 32 :=
  { regs := (input 0).regs
    mem := fun a => if a = 10 then 14 else if a = 15 then second
      else if a = 16 then 7 else (input 0).mem a }

/-- The first node misses; the second hits with two retained zero witnesses. -/
example : ∃ y, ExecWithin 8 probeScan (scanInput 2) y 116 ∧
    y.mem = (scanInput 2).mem ∧ y.regs link = 0 ∧ y.regs one = 1 ∧ y.regs operators = 0 ∧
    (y.regs operand ≠ 0 ↔ ∃ r ∈ [(0, 3), (2, 7)],
      (scanInput 2).mem (slot 40
        (Cslib.Cryptanalysis.AddXNOR.backward
          ((decode 1 0).zip [1#2]) (BitVec.ofNat 2 r.1)).toNat) ≠ 0) ∧
    (y.regs operand ≠ 0 → ∃ r ∈ [(0, 3), (2, 7)],
      y.regs firstOperators = r.2 ∧ y.regs operators = 0 ∧
      y.regs state = (Cslib.Cryptanalysis.AddXNOR.backward
        ((decode 1 0).zip [1#2]) (BitVec.ofNat 2 r.1)).toNat ∧
      y.regs operand = (scanInput 2).mem (slot 40 (y.regs state)) ∧
      y.regs bits = (scanInput 2).mem (slot 40 (y.regs state) + 1)) := by
  exact probeScan_witness_exec (W := 8) (m := 2) (b := 5) (boundary := 20)
    (ptr := 10) (D := 40) (v := 0) [1#2] [(0, 3), (2, 7)] (scanInput 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (.cons (by decide) (by decide) (by decide) (by decide)
      (.cons (by decide) (by decide) (by decide) (by decide) .nil))
    (by decide) (by decide) (by decide)

example : (probeScan.eval 8 16 (scanInput 2)).map (fun r =>
    (r.1.regs operand, r.1.regs bits, r.1.regs firstOperators,
      r.1.regs operators, r.1.regs link, r.1.mem 30)) =
      some (1, 0, 7, 0, 0, 17) := by decide +kernel

/-- Both nodes miss, so the scan reaches the actual null pointer. -/
example : (probeScan.eval 8 16 (scanInput 0)).map (fun r =>
    (r.1.regs operand, r.1.regs link)) = some (0, 0) := by decide +kernel

/-- A successful first node does not read its deliberately invalid successor. -/
example : (probeScan.eval 8 16
    { input 2 with mem := fun a => if a = 10 then 255 else (input 2).mem a }).map
      (fun r => (r.1.regs operand, r.1.regs link)) = some (1, 0) := by decide +kernel

example : (probeScan.eval 8 16
    { input 0 with regs := fun r => if r = link then 0 else (input 0).regs r }).map
      (fun r => (r.1.regs operand, r.1.regs link)) = some (0, 0) := by decide +kernel

/-- A complete two-index class: index zero scans a miss; index one hits.
The projected array is forward-order, the full inverse array reversed. -/
private def classInput (present : Bool) : Data 32 :=
  { regs := fun r => if r = count then 1 else if r = stop then 2
      else if r = fullBase then 5 else if r = projectedBase then 6
      else if r = fullModulus then 4 else if r = projectedModulus then 2
      else if r = heads then 20 else if r = table then 40 else 0
    mem := fun a => if a = 5 ∨ a = 6 then 1 else if a = 20 then 14
      else if a = 21 then 10 else if a = 12 then 3
      else if a = 15 then 2 else if a = 16 then 7
      else if a = 40 ∧ present then 1 else 0 }

/-- Full-class success preserves the actual opposite quarter indices and
recognizes retained zero witnesses. -/
example : (probeClass.eval 8 64 (classInput true)).map (fun r =>
    (r.1.regs operand, r.1.regs bits, r.1.regs firstOperators,
      r.1.regs operators, r.1.regs stop)) = some (1, 0, 7, 1, 1) := by decide +kernel

/-- Exhaustion visits both packed words and returns an absent tag. -/
example : (probeClass.eval 8 64 (classInput false)).map (fun r =>
    (r.1.regs operand, r.1.regs operators, r.1.regs stop)) =
      some (0, 2, 2) := by decide +kernel

/-- An empty opposite bucket for every packed word terminates normally. -/
example : (probeClass.eval 8 64 { classInput false with
    mem := fun a => if a = 20 ∨ a = 21 then 0 else (classInput false).mem a }).map
      (fun r => (r.1.regs operand, r.1.regs operators)) = some (0, 2) := by decide +kernel

/-- A zero-length packed-index range does not touch operands or buckets. -/
example : (probeClass.eval 8 8 { classInput true with
    regs := fun r => if r = stop then 0 else (classInput true).regs r }).map
      (fun r => (r.1.regs operand, r.1.regs operators)) = some (0, 0) := by decide +kernel

/-- Success at index zero skips a deliberately invalid later bucket pointer. -/
example : (probeClass.eval 8 64 { classInput false with
    mem := fun a => if a = 49 then 1 else if a = 20 then 255
      else (classInput false).mem a }).map
      (fun r => (r.1.regs operand, r.1.regs operators, r.1.regs stop)) =
        some (1, 0, 0) := by decide +kernel

private def originalMemory : ℕ → ℕ :=
  fun a => if a = 5 then 1 else if a = 11 then 3 else 0

private def originalInput : Data 32 :=
  { regs := fun r => if r = base then 5 else if r = count then 1
      else if r = modulus then 4 else if r = link then 10
      else if r = table then 40 else if r = one then 1 else 0
    mem := filledMemory 40 (retainedEntries [1#2] 0 [(1, 0)]) originalMemory 0 }

/-- Four original operands, all additions: 0 + 1 + 1 + 1 + 1 = 0 modulo 4.
Every precondition is supplied; zero packed payloads are present, not absent. -/
example : ∃ y, ExecWithin 8 probeScan originalInput y 59 ∧
    y.mem = originalInput.mem ∧ y.regs link = 0 ∧
    (y.regs operand ≠ 0 →
      Cslib.Cryptanalysis.AddXNOR.eval
        (((decode 1 (y.regs operand - 1)).zip [1#2]) ++
          ((decode 1 (y.regs bits)).zip [1#2]) ++
          ((decode 1 (y.regs operators)).zip [1#2]) ++
          ((decode 1 (y.regs firstOperators)).zip [1#2])) 0 = 0) := by
  apply probeScan_original_exec (W := 8) (m := 2) (b := 5) (boundary := 20)
    (ptr := 10) (D := 40) (v := 0) [1#2] [1#2] [1#2] [1#2] 0 0
    [0] [0] 0 originalMemory 0 originalInput
  all_goals first
    | rfl
    | exact .cons (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) .nil
    | decide +kernel
    | (intro q
       have h5 : 40 + 3 * q ≠ 5 := by omega
       have h11 : 40 + 3 * q ≠ 11 := by omega
       simp [originalMemory, slot, h5, h11])

example : (probeScan.eval 8 64 originalInput).map (fun r =>
    (r.1.regs operand, r.1.regs bits, r.1.regs firstOperators,
      r.1.regs operators, r.1.regs state)) = some (1, 0, 0, 0, 2) := by
  decide +kernel

/-- Replacement keeps both words from the last actual writer, including zero. -/
example : filledMemory 40 [⟨2, 7, 9⟩, ⟨2, 0, 0⟩] (fun _ => 0) 0 46 = 1 ∧
    filledMemory 40 [⟨2, 7, 9⟩, ⟨2, 0, 0⟩] (fun _ => 0) 0 47 = 0 := by
  decide +kernel

/-- Width zero and empty operand blocks still distinguish a present zero
witness from absence; the full recovered state is the unique zero-bit word. -/
example : (probeScan.eval 8 64
    { regs := fun r => if r = modulus ∨ r = one then 1
        else if r = link then 10 else if r = table then 40 else 0
      mem := fun a => if a = 40 then 1 else 0 }).map
      (fun r => (r.1.regs operand, r.1.regs bits, r.1.regs state)) =
        some (1, 0, 0) := by decide +kernel

/-- A consecutive original-input client. The four one-word quarters are at
5..8; projection is executed with loads, remainders and stores. No bucket,
dictionary payload or projected operand is installed in the initial memory.
The fourth quarter is self-inverse in the checked instances below; using
`prepare` for that quarter is specific to those instances, not a general inverse
construction. Only retained second-quarter index zero is visited. -/
private def constructedPipeline (N P : ℕ) : Code .standard 32 :=
  .seq (ram[ modulus ← #P; address ← #5; operand ← *address;
    operand ← operand % modulus; address ← #10; *address ← operand;
    address ← #6; operand ← *address; operand ← operand % modulus;
    address ← #11; *address ← operand;
    address ← #7; operand ← *address; operand ← operand % modulus;
    address ← #12; *address ← operand;
    base ← #5; count ← #1; modulus ← #N; initial ← #0;
    keyModulus ← #P; heads ← #20; frontier ← #24 ])
    (.seq prepare
      (.seq (ram[ base ← #11; modulus ← #P; state ← #0; operators ← #0 ])
        (.seq queryBucket
          (.seq (ram[ base ← #6; modulus ← #N; table ← #100; top ← #0;
            zero ← #0; one ← #1 ])
            (.seq retainLoop
              (.seq (ram[ base ← #8; count ← #1; modulus ← #N; initial ← #0;
                keyModulus ← #P; heads ← #40; frontier ← #44 ])
                (.seq prepare
                  (.seq (ram[ fullBase ← #7; projectedBase ← #12;
                    fullModulus ← #N; projectedModulus ← #P; stop ← #2 ])
                    probeClass))))))))

private def unconstructedInput (a : ℕ) : Data 32 :=
  { regs := fun _ => 0
    mem := fun q => if 5 ≤ q ∧ q < 9 then a else if q = 90 then 17 else 0 }

/-- Width two, projection width one, all four original operands equal two.
Native stores produce the dictionary, then the actual streaming iterator hits it.
The result includes both physical payload words, both opposite indices and
an unread sentinel. No constructed-memory semantic premise is supplied. -/
example : ((constructedPipeline 4 2).eval 8 256 (unconstructedInput 2)).map
    (fun r => (r.1.regs operand, r.1.regs bits, r.1.regs firstOperators,
      r.1.regs operators, r.1.regs state, r.1.mem 90)) =
        some (1, 0, 0, 0, 0, 17) := by decide +kernel

/-- Reconstruction is checked on the actual returned payload and indices,
rather than on separately supplied decoded operators. -/
example : ((constructedPipeline 4 2).eval 8 256 (unconstructedInput 2)).map
    (fun r => Cslib.Cryptanalysis.AddXNOR.eval
      (((decode 1 (r.1.regs operand - 1)).zip [2#2]) ++
        ((decode 1 (r.1.regs bits)).zip [2#2]) ++
        ((decode 1 (r.1.regs operators)).zip [2#2]) ++
        ((decode 1 (r.1.regs firstOperators)).zip [2#2])) 0) = some 0 := by
  decide +kernel

/-- Width zero retains indexed duplicates; replacement chooses index zero
last. Projection, preparation, dictionary insertion and streaming still run. -/
example : ((constructedPipeline 1 1).eval 8 256 (unconstructedInput 0)).map
    (fun r => (r.1.regs operand, r.1.regs bits, r.1.regs firstOperators,
      r.1.regs operators, r.1.regs state, r.1.mem 90)) =
        some (1, 0, 1, 0, 0, 17) := by decide +kernel

/-- At projection width zero, distinct full states collide in the bucket;
full-state lookup still returns an actual matching four-quarter witness. -/
example : ((constructedPipeline 4 1).eval 8 256 (unconstructedInput 2)).map
    (fun r => (r.1.regs operand, r.1.regs bits, r.1.regs firstOperators,
      r.1.regs operators, r.1.regs state)) = some (2, 0, 1, 0, 3) := by
  decide +kernel
