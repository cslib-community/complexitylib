/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Complexity.Cryptanalysis.AddXNORNativeProbe

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
    y.mem = (scanInput 2).mem ∧ y.regs link = 0 ∧
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
