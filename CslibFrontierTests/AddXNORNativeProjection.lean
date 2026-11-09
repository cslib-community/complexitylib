/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Cryptanalysis.AddXNORNativeProjection

/-!
# Original-input native low-bit preprocessing

Kernel runs exercise both counter directions on original-width operands, reverse
order, complement addresses, modular wraparound, repeated states, empty chains
and width-zero multiplicity. The generic client uses the certified original-input
execution, not host preprocessing of a projected instance.
-/

public section

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR
open Native Native.Counters

example {m p q : ℕ} (hp : p ≤ m) (as : Fin q → BitVec m) (s t : BitVec m) :
    ∃ (y : Data 18) (n : ℕ), n + 1 ≤ 77 * (q + 1) * 2 ^ p ∧
      Executes (projectedWordWidth m p q) ((projectedEntry true).program Native.source)
        (State.init (encodeProjected p (List.ofFn as) s t)) (y.regs Native.source) (n + 1) ∧
      ∀ g : BitVec p, y.mem (y.regs Native.source + (~~~g).toNat) =
        backwardClassCount p as t g := by
  obtain ⟨y, n, _, hn, _, he, hr, _, _⟩ := encoded_projected_resources true hp as s t
  exact ⟨y, n, hn, he, hr⟩

example : InputFits (projectedWordWidth 5 2 3)
    (encodeProjected 2 [3#5, 8#5, 5#5] 10#5 7#5) :=
  encodeProjected_fits (by decide) _ _ _

/-- Actual forward counters from unprojected five-bit input words. -/
example : ((projectedEntry false).eval (projectedWordWidth 5 2 3) 9
    (Data.init (encodeProjected 2 [3#5, 8#5, 5#5] 10#5 7#5))).map
      (fun result => List.ofFn fun g : Fin 4 =>
        result.1.mem (result.1.regs Native.source + g.val)) = some [2, 0, 2, 4] := by
  decide +kernel

/-- Backward execution reads operands in reverse order and returns a conjugate table. -/
example : ((projectedEntry true).eval (projectedWordWidth 5 2 3) 9
    (Data.init (encodeProjected 2 [3#5, 8#5, 5#5] 10#5 7#5))).map
      (fun result => List.ofFn fun g : Fin 4 =>
        result.1.mem (result.1.regs Native.source + (~~~(BitVec.ofNat 2 g.val)).toNat)) =
      some [0, 2, 4, 2] := by decide +kernel

/-- Coincident branches contribute eight times even with zero projected bits. -/
example : ((projectedEntry true).eval (projectedWordWidth 5 0 3) 9
    (Data.init (encodeProjected 0 [3#5, 8#5, 5#5] 10#5 7#5))).map
      (fun result => result.1.mem (result.1.regs Native.source)) = some 8 := by
  decide +kernel

/-- Empty backward chains retain exactly the projected target. -/
example : ((projectedEntry true).eval (projectedWordWidth 5 2 0) 6
    (Data.init (encodeProjected 2 ([] : List (BitVec 5)) 10#5 7#5))).map
      (fun result => List.ofFn fun g : Fin 4 =>
        result.1.mem (result.1.regs Native.source + (~~~(BitVec.ofNat 2 g.val)).toNat)) =
      some [0, 0, 0, 1] := by decide +kernel

/-- The original width, words and appended projection width survive execution. -/
example : ((projectedEntry true).eval (projectedWordWidth 5 2 3) 9
    (Data.init (encodeProjected 2 [3#5, 8#5, 5#5] 10#5 7#5))).map
      (fun result => List.ofFn fun j : Fin 9 => result.1.mem j.val) =
      some [8, 5, 10, 7, 3, 3, 8, 5, 2] := by decide +kernel

example : (projectedEntry true).IsRandFree ∧ ¬(projectedEntry true).ReadsWidth := by decide
