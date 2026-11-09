/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all CslibFrontier.Cryptanalysis.AddXNORNativeOppositeQuery

/-! # Actual forward query and retained bucket framing -/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter

private def input : Data 32 :=
  { regs := fun r => if r = base then 5 else if r = count then 1
      else if r = modulus then 8 else if r = heads then 20 else 0
    mem := fun a => if a = 5 then 1 else if a = 21 then 24 else 17 }

/-- Addition by one queries head 21, rather than inverse-query head 27.
An unrelated memory sentinel and all dictionary memory remain unchanged. -/
example : ∃ y, ExecWithin 10 Backward.queryBucket input y 20 ∧
    y.regs link = 24 ∧ y.regs operators = 0 ∧ y.mem = input.mem := by
  obtain ⟨y, he, hl, hv, hm, _⟩ := Backward.queryBucket_exec
    (W := 10) (b := 5) (h := 20) (v := 0) [1#3] 0#3 input
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by intro i hi; have : i = 0 := by change i < 1 at hi; omega
        subst i; rfl) (by decide)
  exact ⟨y, he, hl, hv, hm⟩

/-- Collision replacement in the dictionary leaves the original two-node
zero-width bucket linked, including its packed-index-zero node. -/
example :
    let prepared := Backward.preparedMemory [0#0] 0#0 (clear (fun _ => 0) 20 1) 20 24 1 2
    let retained := Dictionary.filledMemory 40
      (retainedEntries ([] : List (BitVec 0)) 0 (Backward.records [0#0] 0#0 0 0)) prepared 0
    Linked retained 30 (retained 20) (Backward.records [0#0] 0#0 0 0) := by
  exact Backward.retainedMemory_linked (h := 20) (f := 24) (p := 0) (D := 40)
    [0#0] [] 0#0 (fun _ => 0) 0 0 0 (by decide) (by decide) (by decide)
