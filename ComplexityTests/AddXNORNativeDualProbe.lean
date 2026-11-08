/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all Complexity.Cryptanalysis.AddXNORNativeDualProbe
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
import all Complexity.Computability.WordRAM.Allocation
import all Complexity.Cryptanalysis.AddXNORNativeForwardRetain
import all Complexity.Cryptanalysis.AddXNORNativeBackward
import all Complexity.Cryptanalysis.AddXNORNativeRetain
import all Complexity.Cryptanalysis.AddXNORNativeDictionary
import Mathlib.Tactic.IntervalCases

/-! # Complete consecutive forward-retention/inverse-preparation client -/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter

private def operands : List (BitVec 3) := [1#3, 2#3]

private def input : Data 32 :=
  { regs := fun r => if r = base then 5 else if r = count then 2
      else if r = modulus then 8 else if r = keyModulus then 2
      else if r = initial then 1 else if r = heads then 20 else if r = frontier then 24 else 0
    mem := fun a => if a = 5 then 1 else if a = 6 then 2 else if a = 8 then 0
      else if a = 10 then 2 else if a = 11 then 1 else if a < 64 then 17 else 0 }

/-- Complete raw-input native construction-to-witness soundness client.
All four quarters are nonempty; the fourth contains non-self-inverse additions. -/
example : ∃ y, ExecWithin 10 (dualProbe 8 1 0 64 20 0 10 2 8 7 40 44 2 8 1 0 0) input y
      (4 * 2 + 4 * (11 * 2 + 22) + 10 + (9 + 2 * (11 * 1 + 30) + 2) +
        (7 + (4 * 2 + 4 * (18 * 2 + 37) + 10)) +
        (10 + ((Backward.bucketIndices operands 7#3 2 0 4).length * (18 * 1 + 39) + 2))) ∧
    (y.regs operand ≠ 0 →
      eval (((decode 2 (y.regs operand - 1)).zip operands) ++
        ((decode 1 (y.regs bits)).zip [0#3]) ++
        ((decode 1 (y.regs operators)).zip [0#3]) ++
        ((decode 2 (y.regs firstOperators)).zip operands)) 1#3 = 7#3) := by
  obtain ⟨y, he, hw⟩ := dualProbe_exec
    (W := 10) (b := 5) (c := 8) (b₄ := 10) (h := 20) (f := 24)
    (h₄ := 40) (f₄ := 44) (p := 1) (D := 64) (v := 0) (b₃ := 8) (v₃ := 0)
    operands [0#3] [0#3] operands 1#3 7#3 input (0 : Fin 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by
      intro i hi
      simp only [operands, List.length_cons, List.length_nil] at hi
      interval_cases i <;> decide +revert)
    (by decide)
    (by intro i hi; have : i = 0 := by change i < 1 at hi; omega
        subst i; decide +revert)
    (by decide) (by decide)
    (by
      intro i hi
      simp only [operands, List.length_reverse, List.length_cons, List.length_nil] at hi
      interval_cases i <;> decide +revert)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a ha; simp [input, show ¬a = 5 by omega, show ¬a = 6 by omega,
      show ¬a = 8 by omega, show ¬a = 10 by omega, show ¬a = 11 by omega,
      show ¬a < 64 by omega]) (by
      intro i hi
      have hi0 : i = 0 := by change i < 1 at hi; omega
      subst i
      decide +revert)
    (by decide) (by decide) (0 : Fin 2) (by decide)
  have records : Forward.records operands 1#3 1 0 = [(2, 3), (4, 0)] := by
    unfold Forward.records bucketIndices indexedState
    decide +kernel
  refine ⟨y, ?_, hw⟩
  simp only [Fin.val_zero, records] at he
  simpa +decide [operands] using he

private def zeroInput : Data 32 :=
  { regs := fun r => if r = modulus then 1 else if r = keyModulus then 2
      else if r = heads then 4 else if r = frontier then 8 else 0
    mem := fun a => if a < 24 then 17 else 0 }

/-- An empty width-zero chain returns four actual zero words, with a nonzero
presence tag. Both native preparations and the native scan still execute. -/
example : ((dualProbe 0 0 0 24 4 0 0 0 1 0 12 16 2 0 0 0 0).eval 8 8 zeroInput).map
    (fun r => (r.1.regs operand, r.1.regs bits, r.1.regs operators,
      r.1.regs firstOperators, r.1.mem 20)) = some (1, 0, 0, 0, 17) := by
  decide +kernel

/-- Selecting the empty forward bucket leaves no dictionary entry to hit.
This is a local miss, not a proof that the original instance is unsatisfiable. -/
example : ((dualProbe 0 0 0 24 4 1 0 0 1 0 12 16 2 0 0 0 0).eval 8 8 zeroInput).map
    (fun r => r.1.regs operand) = some 0 := by
  decide +kernel
