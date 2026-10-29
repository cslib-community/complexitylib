/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Query

/-! # Executed native three-set collision queries -/

namespace ComplexityTests.WordRAMChanHeQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

private def input : Data 64 :=
  ⟨fun i => if i.val = 28 then 1 else if i.val = 29 then 1
    else if i.val = 30 then 2 else if i.val = 31 then 5
    else if i.val = 32 then 0 else if i.val = 33 then 10
    else if i.val = 34 then 20 else if i.val = 35 then 30
    else if i.val = 36 then encode 3 else if i.val = 42 then 3
    else if i.val = 44 then 0 else if i.val = 45 then 6
    else if i.val = 46 then 0 else if i.val = 52 then 0 else 71,
    fun a => if a = 1 then encode (-1) else if a = 2 then encode 0
      else if a = 3 then encode 1 else if a = 5 then encode (-5)
      else if a = 6 then encode (-2) else if a = 7 then encode 1
      else if a = 8 then encode 4 else if a = 10 then encode 0
      else if a = 11 then encode 3 else 79⟩

-- The three complete counting calls unfold all renamed loops and their register maps.
set_option maxRecDepth 8192 in
-- Reduce the complete interpreter run directly in the kernel, avoiding elaborator normalization.
/-- Arrays of lengths one, two and zero test setup/result copies and empty-array counting. -/
example : (Code.eval 8 3 CountTriple.program input).map
    (fun yn => [yn.1.regs (CountCall.result 0), yn.1.regs (CountCall.result 1),
      yn.1.regs (CountCall.result 2), yn.1.regs (40 : Fin 64), yn.1.mem 5]) =
        some [0, 2, 0, 71, encode (-5)] := by decide +kernel

-- The full query additionally reduces three scaled inequalities after the counting loops.
set_option maxRecDepth 8192 in
-- Reduce the complete interpreter run directly in the kernel, avoiding elaborator normalization.
/-- Equality at the scaled threshold is accepted, and caller controls and input are framed. -/
example : (Code.eval 8 3 Query.program input).map
    (fun yn => [yn.1.regs CollisionTest.good, yn.1.regs (40 : Fin 64), yn.1.mem 5]) =
      some [1, 71, encode (-5)] := by decide +kernel

-- This negative case executes the same complete native query with one smaller threshold.
set_option maxRecDepth 8192 in
-- Reduce the complete interpreter run directly in the kernel, avoiding elaborator normalization.
/-- A strict failure of one threshold rejects the three-set candidate. -/
example : (Code.eval 8 3 Query.program
    (input.set (CollisionTest.threshold 1) 5)).map (fun yn => yn.1.regs CollisionTest.good) =
      some 0 := by decide +kernel

end ComplexityTests.WordRAMChanHeQuery
