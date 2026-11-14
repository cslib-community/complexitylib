/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test)

public import CslibFrontier.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Params
public import CslibFrontier.Computability.WordRAM.Resizable.Basic

public section

open Cslib.WordRAM Cslib.WordRAM.Resizable
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise

/-!
# Unit and Integration Tests for In-Epoch Resizable Succinct Operations
-/

/-- Test 1: Concrete evaluate `compactedEpochWords_le_succinctWords` on parameters. -/
theorem test_compacted_words_eval :
    compactedEpochWords 64 16 64 0 0 ≤ Dynamic.succinctWords 1355 441 64 16 64 0 := by
  have hw : 0 < 64 := by decide
  have hU : 64 ≤ 2 ^ 64 := by decide
  have hev : EpochValid 64 0 0 := Or.inl ⟨rfl, rfl⟩
  exact compactedEpochWords_le_succinctWords hw hU hev

/-- Test 2: `inEpochQueryCode` is `¬ReadsWidth`. -/
theorem test_inEpochQueryCode_readsWidth :
    ¬inEpochQueryCode.ReadsWidth :=
  inEpochQueryCode_readsWidth_false

/-- Test 3: `inEpochInsertCode` is `¬ReadsWidth`. -/
theorem test_inEpochInsertCode_readsWidth :
    ¬inEpochInsertCode.ReadsWidth :=
  inEpochInsertCode_readsWidth_false

/-- Test 4: `inEpochDeleteCode` is `¬ReadsWidth`. -/
theorem test_inEpochDeleteCode_readsWidth :
    ¬inEpochDeleteCode.ReadsWidth :=
  inEpochDeleteCode_readsWidth_false

/-- Test 5: `inEpochOpCode` is `¬ReadsWidth`. -/
theorem test_inEpochOpCode_readsWidth :
    ¬inEpochOpCode.ReadsWidth :=
  inEpochOpCode_readsWidth_false

/-- Test 6: Verify `rInEpoch` register allocation bounds. -/
theorem test_rInEpoch_ge_paramReg :
    ∀ i : Fin 36, (inEpochParamReg i).val < rInEpoch := by
  intro i
  exact (inEpochParamReg i).isLt

/-- Test 7: Verify empty dictionary compacted representation theorem. -/
theorem test_compactedRep_empty_eval {r : ℕ} {x : RData r}
    (hx : x.Bounded 64) (hfr : x.frontier = 8)
    (hhdr : RootHeaderValid 64 16 64 0 0 0 0 x.mem) :
    CompactedRep 64 16 64 0 0 0 0 (empty 64) x :=
  compactedRep_empty hx hfr hhdr
