/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import Complexity.Cryptanalysis.AddXNORNativeBackward
import Mathlib.Tactic.IntervalCases

/-! # Backward preparation from dirty memory with non-self-inverse addition -/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter

private def operands : List (BitVec 3) := [1#3, 2#3]

/-- Original operands are [1,2]; the kernel reads their reversed array [2,1].
Heads and records start dirty, and an unrelated sentinel must survive. -/
private def input : Data 32 :=
  { regs := fun r => if r = base then 5 else if r = count then 2
      else if r = modulus then 8 else if r = keyModulus then 2
      else if r = heads then 20 else if r = frontier then 24 else 0
    mem := fun a => if a = 5 then 2 else if a = 6 then 1 else 17 }

/-- All four original indices are stored. The all-addition word yields 5 from
zero by inversion, whereas forward evaluation yields 3. Both low-bit buckets
contain collisions, and the dirty sentinel is framed. -/
example : (Backward.prepare.eval 8 8 input).map (fun r =>
    (r.1.regs frontier, [r.1.mem 20, r.1.mem 21],
      (List.range 12).map (fun i => r.1.mem (24 + i)), r.1.mem 100)) =
    some (36, [30, 33], [0, 5, 0, 0, 0, 1, 27, 4, 2, 24, 3, 3], 17) := by
  decide +kernel

example : backward ((decode 2 0).zip operands) 0#3 = 5#3 ∧
    eval ((decode 2 0).zip operands) 0#3 = 3#3 := by decide

/-- Generic construction-to-linked-record theorem, instantiated without an
assumed semantic bucket. Every input/layout premise comes from concrete data. -/
example : ∃ y, ExecWithin 8 Backward.prepare input y (4 * 2 + 4 * (18 * 2 + 37) + 10) ∧
    Linked y.mem 36 (y.mem 21)
      ((Backward.bucketIndices operands 0#3 2 1 4).map
        fun v => ((backward ((decode 2 v).zip operands) 0#3).toNat, v)) ∧
    (∀ a, ¬(20 ≤ a ∧ a < 22) → ¬(24 ≤ a ∧ a < 36) → y.mem a = input.mem a) := by
  apply Backward.prepare_linked_exec (b := 5) (h := 20) (f := 24) (p := 1)
    operands 0#3 input (1 : Fin 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  · intro i hi
    simp only [operands, List.length_reverse, List.length_cons, List.length_nil] at hi
    interval_cases i <;> decide +revert
  · decide
  · decide

/-- Empty and zero-width quarters still enumerate the unique empty word. -/
example : (Backward.prepare.eval 6 2
    { regs := fun r => if r = modulus ∨ r = keyModulus then 1
        else if r = heads then 20 else if r = frontier then 24 else 0
      mem := fun _ => 0 }).map (fun r =>
        (r.1.regs frontier, r.1.mem 20, [r.1.mem 24, r.1.mem 25, r.1.mem 26])) =
    some (27, 24, [0, 0, 0]) := by decide +kernel
