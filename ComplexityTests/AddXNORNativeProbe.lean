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
    y.regs operand = 1 ∧ y.regs bits = 0 := by
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
