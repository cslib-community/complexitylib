/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all CslibFrontier.Cryptanalysis.AddXNORNativeDualPreparation
import all CslibFrontier.Cryptanalysis.AddXNORNativeBuckets
import all CslibFrontier.Computability.WordRAM.Allocation
import all CslibFrontier.Cryptanalysis.AddXNORNativeForwardRetain
import all CslibFrontier.Cryptanalysis.AddXNORNativeBackward
import all CslibFrontier.Cryptanalysis.AddXNORNativeRetain
import all CslibFrontier.Cryptanalysis.AddXNORNativeDictionary
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

/-- All premises supplied on raw operands. Forward retention and inverse construction
are consecutive. The original witness tags survive; both native bucket lists and
an unread dirty sentinel are obtained from the general theorem. -/
example : ∃ y, ExecWithin 10 (dualPrepare 8 1 0 64 20 0 10 2 8 3 40 44 2) input y
      (4 * 2 + 4 * (11 * 2 + 22) + 10 + (9 + 2 * (11 * 1 + 30) + 2) +
        (7 + (4 * 2 + 4 * (18 * 2 + 37) + 10))) ∧
    y.mem 70 = 4 ∧ y.mem 76 = 1 ∧ y.mem 12 = 17 ∧
    Linked y.mem 36 (y.mem 20) [(2, 3), (4, 0)] ∧
    Linked y.mem 56 (y.mem 40)
      ((Backward.bucketIndices operands 3#3 2 0 4).map
        fun u => ((Backward.indexedState operands 3#3 u).toNat, u)) := by
  obtain ⟨y, he, ym, hd, hz, hl, hr, hf, _⟩ := dualPrepare_exec
    (W := 10) (b := 5) (c := 8) (b₄ := 10) (h := 20) (f := 24)
    (h₄ := 40) (f₄ := 44) (p := 1) (D := 64) (v := 0)
    operands [0#3] operands 1#3 3#3 input (0 : Fin 2)
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
      show ¬a < 64 by omega]) (by decide)
  have records : Forward.records operands 1#3 1 0 = [(2, 3), (4, 0)] := by
    unfold Forward.records bucketIndices indexedState
    decide +kernel
  have tags : y.mem 70 = 4 ∧ y.mem 76 = 1 := by
    rw [ym]
    unfold Backward.preparedMemory Backward.indexedState preparedMemory indexedState
      Forward.records bucketIndices insertMemory Dictionary.filledMemory Dictionary.putMemory
      retainedEntries clear
    decide +kernel
  refine ⟨y, ?_, tags.1, tags.2, ?_, ?_, ?_⟩
  · simp only [Fin.val_zero, records] at he
    simpa +decide [operands] using he
  · exact (hf 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl
  · have left := hl (0 : Fin 2)
    simp only [Fin.val_zero, records] at left
    simpa +decide [operands] using left
  · exact hr (0 : Fin 2)

/-- Zero-width inverse preparation retains both indexed collision records. -/
example : Backward.bucketIndices [0#0] 0#0 1 0 2 = [1, 0] := by
  unfold Backward.bucketIndices
  decide +kernel
