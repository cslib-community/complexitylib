/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all Complexity.Cryptanalysis.AddXNORNativeForwardRetain
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
import all Complexity.Cryptanalysis.AddXNORNativeRetain
import all Complexity.Cryptanalysis.AddXNORNativeDictionary
import Mathlib.Tactic.IntervalCases

/-! # Complete forward-preparation/retention client -/

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
      else if a < 40 then 17 else 0 }

/-- A complete use of the general theorem, with two forward additions and low-key
collisions. The other operand is zero, preserving the computed full states. -/
example : ∃ y, ExecWithin 10 (Forward.prepareRetain 8 1 0 40 20 0) input y
      (4 * 2 + 4 * (11 * 2 + 22) + 10 + (9 + 2 * (11 * 1 + 30) + 2)) ∧
    y.mem = Dictionary.filledMemory 40
      (retainedEntries [0#3] 0 [(2, 3), (4, 0)])
      (preparedMemory operands 1#3 (clear input.mem 20 2) 20 24 2 4) 0 ∧ y.mem 9 = 17 := by
  obtain ⟨y, he, hm, _, hframe, _⟩ := Forward.prepareRetain_exec
    (W := 10) (b := 5) (c := 8) (h := 20) (f := 24) (p := 1) (D := 40) (v := 0)
    operands [0#3] 1#3 input (0 : Fin 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by
      intro i hi
      simp only [operands, List.length_cons, List.length_nil] at hi
      interval_cases i <;> decide +revert)
    (by decide)
    (by intro i hi; have hi0 : i = 0 := by change i < 1 at hi; omega
        subst i; decide +revert)
    (by decide) (by decide) (by decide)
    (by intro q hq; simp [input, show ¬q = 5 by omega, show ¬q = 6 by omega,
      show ¬q = 8 by omega, show ¬q < 40 by omega]) (by decide)
  have hr : Forward.records operands 1#3 1 0 = [(2, 3), (4, 0)] := by
    unfold Forward.records bucketIndices indexedState
    decide +kernel
  simp only [Fin.val_zero, hr] at he hm
  exact ⟨y, he, hm, (hframe 9 (by decide) (by decide) (by decide)).trans rfl⟩

/-- Zero-width computed forward records collide. Retaining them replaces the
payload with packed index zero while preserving occupancy. -/
example : Forward.records [0#0] 0#0 0 0 = [(0, 1), (0, 0)] ∧
    Dictionary.filledMemory 40 (retainedEntries ([] : List (BitVec 0)) 0 [(0, 1), (0, 0)])
      (fun _ => 0) 0 40 = 1 := by
  constructor
  · unfold Forward.records bucketIndices indexedState
    decide +kernel
  · unfold retainedEntries
    decide +kernel

/-- Retention preserves a different, unconsumed bucket as a native linked list. -/
example :
    let prepared := preparedMemory operands 1#3 (clear input.mem 20 2) 20 24 2 4
    let retained := Dictionary.filledMemory 40
      (retainedEntries [0#3] 0 (Forward.records operands 1#3 1 0)) prepared 0
    Linked retained 36 (retained 21) (Forward.records operands 1#3 1 1) := by
  exact Forward.retainedMemory_linked (h := 20) (f := 24) (p := 1) (D := 40)
    operands [0#3] 1#3 input.mem 0
    (0 : Fin 2) (1 : Fin 2) (by decide) (by decide) (by decide)
