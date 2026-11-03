/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctHash
public import Complexity.DataStructure.WordRAM.Randomized.StateTransition
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctValidHistory
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctHash

/-!
# Register Wiring and Per-Operation Native Dispatch for the Succinct Dictionary

This module wires the five `Realizes .exact` certificates from `SuccinctHash.lean`
(`realizes_extractQuot`, `realizes_queryWithHash`, `realizes_insertWithHash`,
`realizes_deletePrepWithHash`, `realizes_deleteFinishWithHash`) together with
`ReducedKWise.evalCode`, `ReducedKWise.initTableCode`, and `ReducedKWise.resampleCode` into a
single `SubroutineCode` (`subroutineCode U V w n_max`) on `rSuccinct U V w n_max` registers, and
proves the unified per-operation deterministic execution theorem (`exec_opCode`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.Probability
open Finset

/-! ## Section 1: Register layout, scratch bank, and exchange factor -/

/-- Combined scratch register bank size for the five `Realizes` certificates used in operation
dispatch. -/
@[expose]
noncomputable def scratchSuccinct (U V w n_max : ℕ) : ℕ :=
  max (1 + (realizes_extractQuot n_max).scratchSize + 1)
    (max (2 + (realizes_queryWithHash U V w n_max).scratchSize + 1)
      (max (0 + (realizes_insertWithHash U V w n_max).scratchSize + 1)
        (max (4 + (realizes_deletePrepWithHash U V w n_max).scratchSize + 1)
          (0 + (realizes_deleteFinishWithHash U V w n_max).scratchSize + 1))))

/-- Total register count `256 + scratchSuccinct U V w n_max` for the succinct dictionary
subroutine. -/
@[expose]
noncomputable def rSuccinct (U V w n_max : ℕ) : ℕ :=
  256 + scratchSuccinct U V w n_max

theorem le_rSuccinct (U V w n_max : ℕ) : 256 ≤ rSuccinct U V w n_max := by
  dsimp only [rSuccinct]
  omega

/-- Canonical embedding `Fin 256 → Fin (rSuccinct U V w n_max)` for fixed control and hash
registers. -/
@[expose]
noncomputable def sReg (U V w n_max : ℕ) : Fin 256 → Fin (rSuccinct U V w n_max) :=
  Fin.castLE (le_rSuccinct U V w n_max)

theorem sReg_injective (U V w n_max : ℕ) : Function.Injective (sReg U V w n_max) :=
  Fin.castLE_injective (le_rSuccinct U V w n_max)

@[simp]
theorem sReg_inj {U V w n_max : ℕ} {i j : Fin 256} :
    sReg U V w n_max i = sReg U V w n_max j ↔ i = j :=
  (sReg_injective U V w n_max).eq_iff

@[simp]
theorem val_sReg (U V w n_max : ℕ) (i : Fin 256) :
    (sReg U V w n_max i).val = i.val := rfl

theorem sReg_ne {U V w n_max : ℕ} {i j : Fin 256} (h : i ≠ j) :
    sReg U V w n_max i ≠ sReg U V w n_max j :=
  fun heq => h ((sReg_injective U V w n_max) heq)

@[simp]
theorem set_regs {r : ℕ} (x : Data r) (j : Fin r) (v : ℕ) (i : Fin r) :
    (x.set j v).regs i = Function.update x.regs j v i := rfl

@[simp]
theorem update_sReg {U V w n_max : ℕ} (f : Fin (rSuccinct U V w n_max) → ℕ)
    (j : Fin 256) (v : ℕ) (i : Fin 256) :
    Function.update f (sReg U V w n_max j) v (sReg U V w n_max i) =
      if i = j then v else f (sReg U V w n_max i) := by
  simp only [Function.update_apply, sReg_inj]

/-- Combined exchange factor `≥ 1` dominating the five `Realizes.factor` constants. -/
@[expose]
noncomputable def opFactor (U V w n_max : ℕ) : ℕ :=
  max 1
    (max (realizes_extractQuot n_max).factor
      (max (realizes_queryWithHash U V w n_max).factor
        (max (realizes_insertWithHash U V w n_max).factor
          (max (realizes_deletePrepWithHash U V w n_max).factor
            (realizes_deleteFinishWithHash U V w n_max).factor))))

theorem one_le_opFactor (U V w n_max : ℕ) : 1 ≤ opFactor U V w n_max :=
  le_max_left _ _

theorem factor_extractQuot_le (U V w n_max : ℕ) :
    (realizes_extractQuot n_max).factor ≤ opFactor U V w n_max := by
  unfold opFactor; omega

theorem factor_queryWithHash_le (U V w n_max : ℕ) :
    (realizes_queryWithHash U V w n_max).factor ≤ opFactor U V w n_max := by
  unfold opFactor; omega

theorem factor_insertWithHash_le (U V w n_max : ℕ) :
    (realizes_insertWithHash U V w n_max).factor ≤ opFactor U V w n_max := by
  unfold opFactor; omega

theorem factor_deletePrepWithHash_le (U V w n_max : ℕ) :
    (realizes_deletePrepWithHash U V w n_max).factor ≤ opFactor U V w n_max := by
  unfold opFactor; omega

theorem factor_deleteFinishWithHash_le (U V w n_max : ℕ) :
    (realizes_deleteFinishWithHash U V w n_max).factor ≤ opFactor U V w n_max := by
  unfold opFactor; omega

/-- Embed a `ReducedKWise` register `i : Fin 240` into `Fin (rSuccinct U V w n_max)`. -/
@[expose]
noncomputable def coreReg (U V w n_max : ℕ) : Fin 240 → Fin (rSuccinct U V w n_max) :=
  Fin.castLE (by dsimp only [rSuccinct]; omega)

theorem coreReg_injective (U V w n_max : ℕ) :
    Function.Injective (coreReg U V w n_max) :=
  Fin.castLE_injective _

@[simp]
theorem val_coreReg (U V w n_max : ℕ) (i : Fin 240) :
    (coreReg U V w n_max i).val = i.val := rfl

theorem notMem_range_coreReg {U V w n_max : ℕ} {r : Fin (rSuccinct U V w n_max)}
    (hr : 240 ≤ r.val) : r ∉ Set.range (coreReg U V w n_max) := by
  rintro ⟨i, rfl⟩
  have := i.isLt
  dsimp only [coreReg, Fin.val_castLE] at hr
  omega

/-- Persistent base-address register `0` (`sReg 0`). -/
noncomputable abbrev baseReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 0

/-- Hash input register `1` (`sReg 1`). -/
noncomputable abbrev hashKeyReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 1

/-- Hash output register `2` (`sReg 2`). -/
noncomputable abbrev hashOutReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 2

/-- Bump-pointer frontier register `240` (`sReg 240`). -/
noncomputable abbrev frontierReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 240

/-- Scratch pointer register `241` for `zeroFillCode` and `allocSpan`. -/
noncomputable abbrev curReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 241

/-- Constant-`0` scratch register `242` for `zeroFillCode` and operation dispatch. -/
noncomputable abbrev zeroReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 242

/-- Constant-`1` scratch register `243` for `zeroFillCode` and operation dispatch. -/
noncomputable abbrev oneReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 243

/-- Input operation-tag register `244` (`0` = `query`, `1` = `insert`, `2` = `delete`). -/
noncomputable abbrev tagReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 244

/-- Input key register `245` (`u.val`). -/
noncomputable abbrev argUReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 245

/-- Input value register `246` (`v` for `insert`, `0` otherwise). -/
noncomputable abbrev argVReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 246

/-- Nominal output register `247` for `SubroutineCode.output`. -/
noncomputable abbrev outReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 247

/-- Register `248` saving the first hash evaluation `h_q` across the second hash call in
`delete`. -/
noncomputable abbrev hqReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 248

/-- Register `249` storing `found` from `deletePrepWithHashProg`. -/
noncomputable abbrev foundReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 249

/-- Register `250` storing `j_del` from `deletePrepWithHashProg`. -/
noncomputable abbrev jDelReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 250

/-- Register `251` storing `phys_del` from `deletePrepWithHashProg`. -/
noncomputable abbrev physDelReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 251

/-- Register `252` storing the `Option ℕ` presence tag (`0` = `none`, `1` = `some`) from
`queryWithHashProg`. -/
noncomputable abbrev resTagReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 252

/-- Register `253` storing the `Option ℕ` payload value `v` from `queryWithHashProg`. -/
noncomputable abbrev resValReg (U V w n_max : ℕ) : Fin (rSuccinct U V w n_max) :=
  sReg U V w n_max 253

/-! ## Section 2: Register wirings (`src_*`, `tmp_*`) and emitted native code -/

/-- Source register wiring `![argUReg]` for `extractQuotProg`. -/
@[expose]
noncomputable def srcExt (U V w n_max : ℕ) : Fin 1 → Fin (rSuccinct U V w n_max) :=
  ![argUReg U V w n_max]

@[simp]
theorem val_srcExt (U V w n_max : ℕ) (i : Fin 1) :
    (srcExt U V w n_max i).val = 245 := by
  fin_cases i
  rfl

/-- Scratch/output register wiring for `extractQuotProg`, placing output `0` directly in
`hashKeyReg` (`1`) and remaining scratch registers at `256 + j.val`. -/
@[expose]
noncomputable def tmpExt (U V w n_max : ℕ)
    (j : Fin (1 + (realizes_extractQuot n_max).scratchSize + 1)) :
    Fin (rSuccinct U V w n_max) :=
  if j.val = 0 then hashKeyReg U V w n_max
  else ⟨256 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpExt (U V w n_max : ℕ)
    (j : Fin (1 + (realizes_extractQuot n_max).scratchSize + 1)) :
    (tmpExt U V w n_max j).val = if j.val = 0 then 1 else 256 + j.val := by
  dsimp only [tmpExt]
  split_ifs <;> rfl

/-- Emitted native code for `extractQuotProg`. -/
@[expose]
noncomputable def extCode (U V w n_max : ℕ) : Code .exact (rSuccinct U V w n_max) :=
  (realizes_extractQuot n_max).code (frontierReg U V w n_max)
    (srcExt U V w n_max) (tmpExt U V w n_max)

/-- Source register wiring `![baseReg, argUReg, hashOutReg]` for `queryWithHashProg`. -/
@[expose]
noncomputable def srcQry (U V w n_max : ℕ) : Fin 3 → Fin (rSuccinct U V w n_max) :=
  ![baseReg U V w n_max, argUReg U V w n_max, hashOutReg U V w n_max]

@[simp]
theorem val_srcQry (U V w n_max : ℕ) (i : Fin 3) :
    (srcQry U V w n_max i).val =
      if i.val = 0 then 0 else if i.val = 1 then 245 else 2 := by
  fin_cases i <;> rfl

/-- Scratch/output register wiring for `queryWithHashProg`, placing outputs `0, 1` in
`resTagReg` (`252`) and `resValReg` (`253`). -/
@[expose]
noncomputable def tmpQry (U V w n_max : ℕ)
    (j : Fin (2 + (realizes_queryWithHash U V w n_max).scratchSize + 1)) :
    Fin (rSuccinct U V w n_max) :=
  if j.val = 0 then resTagReg U V w n_max
  else if j.val = 1 then resValReg U V w n_max
  else ⟨256 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpQry (U V w n_max : ℕ)
    (j : Fin (2 + (realizes_queryWithHash U V w n_max).scratchSize + 1)) :
    (tmpQry U V w n_max j).val =
      if j.val = 0 then 252 else if j.val = 1 then 253 else 256 + j.val := by
  dsimp only [tmpQry]
  split_ifs <;> rfl

/-- Emitted native code for `queryWithHashProg`. -/
@[expose]
noncomputable def qryCode (U V w n_max : ℕ) : Code .exact (rSuccinct U V w n_max) :=
  (realizes_queryWithHash U V w n_max).code (frontierReg U V w n_max)
    (srcQry U V w n_max) (tmpQry U V w n_max)

/-- Source register wiring `![baseReg, argUReg, argVReg, hashOutReg]` for `insertWithHashProg`. -/
@[expose]
noncomputable def srcIns (U V w n_max : ℕ) : Fin 4 → Fin (rSuccinct U V w n_max) :=
  ![baseReg U V w n_max, argUReg U V w n_max, argVReg U V w n_max, hashOutReg U V w n_max]

@[simp]
theorem val_srcIns (U V w n_max : ℕ) (i : Fin 4) :
    (srcIns U V w n_max i).val =
      if i.val = 0 then 0 else if i.val = 1 then 245 else if i.val = 2 then 246 else 2 := by
  fin_cases i <;> rfl

/-- Scratch register wiring for `insertWithHashProg` at `256 + j.val`. -/
@[expose]
noncomputable def tmpIns (U V w n_max : ℕ)
    (j : Fin (0 + (realizes_insertWithHash U V w n_max).scratchSize + 1)) :
    Fin (rSuccinct U V w n_max) :=
  ⟨256 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpIns (U V w n_max : ℕ)
    (j : Fin (0 + (realizes_insertWithHash U V w n_max).scratchSize + 1)) :
    (tmpIns U V w n_max j).val = 256 + j.val := rfl

/-- Emitted native code for `insertWithHashProg`. -/
@[expose]
noncomputable def insCode (U V w n_max : ℕ) : Code .exact (rSuccinct U V w n_max) :=
  (realizes_insertWithHash U V w n_max).code (frontierReg U V w n_max)
    (srcIns U V w n_max) (tmpIns U V w n_max)

/-- Source register wiring `![baseReg, argUReg, hqReg]` for `deletePrepWithHashProg`. -/
@[expose]
noncomputable def srcDelPrep (U V w n_max : ℕ) : Fin 3 → Fin (rSuccinct U V w n_max) :=
  ![baseReg U V w n_max, argUReg U V w n_max, hqReg U V w n_max]

@[simp]
theorem val_srcDelPrep (U V w n_max : ℕ) (i : Fin 3) :
    (srcDelPrep U V w n_max i).val =
      if i.val = 0 then 0 else if i.val = 1 then 245 else 248 := by
  fin_cases i <;> rfl

/-- Scratch/output register wiring for `deletePrepWithHashProg`, placing outputs `0..3` in
`foundReg` (`249`), `jDelReg` (`250`), `physDelReg` (`251`), and `hashKeyReg` (`1`). -/
@[expose]
noncomputable def tmpDelPrep (U V w n_max : ℕ)
    (j : Fin (4 + (realizes_deletePrepWithHash U V w n_max).scratchSize + 1)) :
    Fin (rSuccinct U V w n_max) :=
  if j.val = 0 then foundReg U V w n_max
  else if j.val = 1 then jDelReg U V w n_max
  else if j.val = 2 then physDelReg U V w n_max
  else if j.val = 3 then hashKeyReg U V w n_max
  else ⟨256 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpDelPrep (U V w n_max : ℕ)
    (j : Fin (4 + (realizes_deletePrepWithHash U V w n_max).scratchSize + 1)) :
    (tmpDelPrep U V w n_max j).val =
      if j.val = 0 then 249
      else if j.val = 1 then 250
      else if j.val = 2 then 251
      else if j.val = 3 then 1
      else 256 + j.val := by
  dsimp only [tmpDelPrep]
  split_ifs <;> rfl

/-- Emitted native code for `deletePrepWithHashProg`. -/
@[expose]
noncomputable def delPrepCode (U V w n_max : ℕ) : Code .exact (rSuccinct U V w n_max) :=
  (realizes_deletePrepWithHash U V w n_max).code (frontierReg U V w n_max)
    (srcDelPrep U V w n_max) (tmpDelPrep U V w n_max)

/-- Source register wiring `![baseReg, argUReg, hqReg, foundReg, jDelReg, physDelReg, hashOutReg]`
for `deleteFinishWithHashProg`. -/
@[expose]
noncomputable def srcDelFin (U V w n_max : ℕ) : Fin 7 → Fin (rSuccinct U V w n_max) :=
  ![baseReg U V w n_max, argUReg U V w n_max, hqReg U V w n_max,
    foundReg U V w n_max, jDelReg U V w n_max, physDelReg U V w n_max,
    hashOutReg U V w n_max]

@[simp]
theorem val_srcDelFin (U V w n_max : ℕ) (i : Fin 7) :
    (srcDelFin U V w n_max i).val =
      if i.val = 0 then 0
      else if i.val = 1 then 245
      else if i.val = 2 then 248
      else if i.val = 3 then 249
      else if i.val = 4 then 250
      else if i.val = 5 then 251
      else 2 := by
  fin_cases i <;> rfl

/-- Scratch register wiring for `deleteFinishWithHashProg` at `256 + j.val`. -/
@[expose]
noncomputable def tmpDelFin (U V w n_max : ℕ)
    (j : Fin (0 + (realizes_deleteFinishWithHash U V w n_max).scratchSize + 1)) :
    Fin (rSuccinct U V w n_max) :=
  ⟨256 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpDelFin (U V w n_max : ℕ)
    (j : Fin (0 + (realizes_deleteFinishWithHash U V w n_max).scratchSize + 1)) :
    (tmpDelFin U V w n_max j).val = 256 + j.val := rfl

/-- Emitted native code for `deleteFinishWithHashProg`. -/
@[expose]
noncomputable def delFinCode (U V w n_max : ℕ) : Code .exact (rSuccinct U V w n_max) :=
  (realizes_deleteFinishWithHash U V w n_max).code (frontierReg U V w n_max)
    (srcDelFin U V w n_max) (tmpDelFin U V w n_max)

/-- Native quotient hash evaluation code `(ReducedKWise.evalCode ...).rename coreReg`. -/
@[expose]
noncomputable def hashEvalCode (U V w n_max : ℕ) : Code .exact (rSuccinct U V w n_max) :=
  (ReducedKWise.evalCode w (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3).rename
    (coreReg U V w n_max)

/-- Complete `delete` branch code: saves `h_q` into `hqReg`, runs `delPrepCode` (which puts `q_last`
into `hashKeyReg`), evaluates `h_q_last` via `hashEvalCode`, and runs `delFinCode`. -/
@[expose]
noncomputable def delCode (U V w n_max : ℕ) : Code .exact (rSuccinct U V w n_max) :=
  .seq (.op (.copy (hqReg U V w n_max) (hashOutReg U V w n_max)))
  (.seq (delPrepCode U V w n_max)
  (.seq (hashEvalCode U V w n_max)
        (delFinCode U V w n_max)))

/-- Complete operation dispatch code for `subroutineCode`: extracts `q`, evaluates `h_q`, and
branches on `tagReg` between `qryCode`, `insCode`, and `delCode`. -/
@[expose]
noncomputable def opCode (U V w n_max : ℕ) : Code .exact (rSuccinct U V w n_max) :=
  .seq (extCode U V w n_max)
  (.seq (hashEvalCode U V w n_max)
  (.seq (.op (.const (zeroReg U V w n_max) 0))
  (.branch (.eq (tagReg U V w n_max) (zeroReg U V w n_max))
    (qryCode U V w n_max)
    (.seq (.op (.const (oneReg U V w n_max) 1))
    (.branch (.eq (tagReg U V w n_max) (oneReg U V w n_max))
      (insCode U V w n_max)
      (delCode U V w n_max))))))

/-- Canonical `SubroutineCode` for the fixed-capacity succinct dynamic dictionary.
Note that `subroutineCode U V w n_max` depends on the static parameters `(U, V, w, n_max)` and is
independent of `base`. -/
@[expose]
noncomputable def subroutineCode (U V w n_max : ℕ) :
    SubroutineCode .exact (rSuccinct U V w n_max) 0 where
  allocSpan :=
    .seq (.op (.copy (baseReg U V w n_max) (frontierReg U V w n_max)))
    (.seq (.op (.const (curReg U V w n_max) (space U V w n_max)))
          (.op (.exactBin .add (frontierReg U V w n_max)
            (frontierReg U V w n_max) (curReg U V w n_max))))
  initSetup :=
    .seq ((ReducedKWise.initTableCode w (qBits U n_max) (hashB n_max)
            (totalMicroBits n_max) 3).rename (coreReg U V w n_max))
         ((ReducedKWise.resampleCode (qBits U n_max) (hashB n_max)
            (totalMicroBits n_max) 3).rename (coreReg U V w n_max))
  code := opCode U V w n_max
  frontierReg := frontierReg U V w n_max
  baseReg := baseReg U V w n_max
  initParams := Fin.elim0
  curReg := curReg U V w n_max
  zeroReg := zeroReg U V w n_max
  oneReg := oneReg U V w n_max
  incCur := .exactBin .add (curReg U V w n_max) (curReg U V w n_max) (oneReg U V w n_max)
  input r := decide (r = tagReg U V w n_max ∨ r = argUReg U V w n_max ∨ r = argVReg U V w n_max)
  output := outReg U V w n_max

/-! ## Section 3: Disjointness of register wirings (`src_*`, `tmp_*`) -/

theorem tmpExt_injective (U V w n_max : ℕ) :
    Function.Injective (tmpExt U V w n_max) := by
  intro a b h
  have hval := congrArg Fin.val h
  rw [val_tmpExt, val_tmpExt] at hval
  split_ifs at hval <;> exact Fin.ext (by omega)

theorem srcExt_ne_tmpExt (U V w n_max : ℕ) (i : Fin 1)
    (j : Fin (1 + (realizes_extractQuot n_max).scratchSize + 1)) :
    srcExt U V w n_max i ≠ tmpExt U V w n_max j := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcExt, val_tmpExt] at hval
  split_ifs at hval <;> omega

theorem tmpExt_ne_frontier (U V w n_max : ℕ)
    (j : Fin (1 + (realizes_extractQuot n_max).scratchSize + 1)) :
    tmpExt U V w n_max j ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_tmpExt] at hval
  change (if j.val = 0 then 1 else 256 + j.val) = 240 at hval
  split_ifs at hval <;> omega

theorem srcExt_ne_frontier (U V w n_max : ℕ) (i : Fin 1) :
    srcExt U V w n_max i ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcExt] at hval
  change 245 = 240 at hval
  omega

theorem tmpQry_injective (U V w n_max : ℕ) :
    Function.Injective (tmpQry U V w n_max) := by
  intro a b h
  have hval := congrArg Fin.val h
  rw [val_tmpQry, val_tmpQry] at hval
  split_ifs at hval <;> exact Fin.ext (by omega)

theorem srcQry_ne_tmpQry (U V w n_max : ℕ) (i : Fin 3)
    (j : Fin (2 + (realizes_queryWithHash U V w n_max).scratchSize + 1)) :
    srcQry U V w n_max i ≠ tmpQry U V w n_max j := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcQry, val_tmpQry] at hval
  split_ifs at hval <;> omega

theorem tmpQry_ne_frontier (U V w n_max : ℕ)
    (j : Fin (2 + (realizes_queryWithHash U V w n_max).scratchSize + 1)) :
    tmpQry U V w n_max j ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_tmpQry] at hval
  change (if j.val = 0 then 252 else if j.val = 1 then 253 else 256 + j.val) = 240 at hval
  split_ifs at hval <;> omega

theorem srcQry_ne_frontier (U V w n_max : ℕ) (i : Fin 3) :
    srcQry U V w n_max i ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcQry] at hval
  change (if i.val = 0 then 0 else if i.val = 1 then 245 else 2) = 240 at hval
  split_ifs at hval <;> omega

theorem tmpIns_injective (U V w n_max : ℕ) :
    Function.Injective (tmpIns U V w n_max) := by
  intro a b h
  have hval := congrArg Fin.val h
  rw [val_tmpIns, val_tmpIns] at hval
  exact Fin.ext (by omega)

theorem srcIns_ne_tmpIns (U V w n_max : ℕ) (i : Fin 4)
    (j : Fin (0 + (realizes_insertWithHash U V w n_max).scratchSize + 1)) :
    srcIns U V w n_max i ≠ tmpIns U V w n_max j := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcIns, val_tmpIns] at hval
  split_ifs at hval <;> omega

theorem tmpIns_ne_frontier (U V w n_max : ℕ)
    (j : Fin (0 + (realizes_insertWithHash U V w n_max).scratchSize + 1)) :
    tmpIns U V w n_max j ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_tmpIns] at hval
  change 256 + j.val = 240 at hval
  omega

theorem srcIns_ne_frontier (U V w n_max : ℕ) (i : Fin 4) :
    srcIns U V w n_max i ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcIns] at hval
  change (if i.val = 0 then 0 else if i.val = 1 then 245 else if i.val = 2 then 246 else 2) =
    240 at hval
  split_ifs at hval <;> omega

theorem tmpDelPrep_injective (U V w n_max : ℕ) :
    Function.Injective (tmpDelPrep U V w n_max) := by
  intro a b h
  have hval := congrArg Fin.val h
  rw [val_tmpDelPrep, val_tmpDelPrep] at hval
  split_ifs at hval <;> exact Fin.ext (by omega)

theorem srcDelPrep_ne_tmpDelPrep (U V w n_max : ℕ) (i : Fin 3)
    (j : Fin (4 + (realizes_deletePrepWithHash U V w n_max).scratchSize + 1)) :
    srcDelPrep U V w n_max i ≠ tmpDelPrep U V w n_max j := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcDelPrep, val_tmpDelPrep] at hval
  split_ifs at hval <;> omega

theorem tmpDelPrep_ne_frontier (U V w n_max : ℕ)
    (j : Fin (4 + (realizes_deletePrepWithHash U V w n_max).scratchSize + 1)) :
    tmpDelPrep U V w n_max j ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_tmpDelPrep] at hval
  change (if j.val = 0 then 249 else if j.val = 1 then 250 else if j.val = 2 then 251
    else if j.val = 3 then 1 else 256 + j.val) = 240 at hval
  split_ifs at hval <;> omega

theorem srcDelPrep_ne_frontier (U V w n_max : ℕ) (i : Fin 3) :
    srcDelPrep U V w n_max i ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcDelPrep] at hval
  change (if i.val = 0 then 0 else if i.val = 1 then 245 else 248) = 240 at hval
  split_ifs at hval <;> omega

theorem tmpDelFin_injective (U V w n_max : ℕ) :
    Function.Injective (tmpDelFin U V w n_max) := by
  intro a b h
  have hval := congrArg Fin.val h
  rw [val_tmpDelFin, val_tmpDelFin] at hval
  exact Fin.ext (by omega)

theorem srcDelFin_ne_tmpDelFin (U V w n_max : ℕ) (i : Fin 7)
    (j : Fin (0 + (realizes_deleteFinishWithHash U V w n_max).scratchSize + 1)) :
    srcDelFin U V w n_max i ≠ tmpDelFin U V w n_max j := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcDelFin, val_tmpDelFin] at hval
  split_ifs at hval <;> omega

theorem tmpDelFin_ne_frontier (U V w n_max : ℕ)
    (j : Fin (0 + (realizes_deleteFinishWithHash U V w n_max).scratchSize + 1)) :
    tmpDelFin U V w n_max j ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_tmpDelFin] at hval
  change 256 + j.val = 240 at hval
  omega

theorem srcDelFin_ne_frontier (U V w n_max : ℕ) (i : Fin 7) :
    srcDelFin U V w n_max i ≠ frontierReg U V w n_max := by
  intro h
  have hval := congrArg Fin.val h
  rw [val_srcDelFin] at hval
  change (if i.val = 0 then 0 else if i.val = 1 then 245 else if i.val = 2 then 248
    else if i.val = 3 then 249 else if i.val = 4 then 250 else if i.val = 5 then 251
    else 2) = 240 at hval
  split_ifs at hval <;> omega

/-! ## Section 4: Representation invariant, potential, charge, and ABI encoding -/

/-- Concrete Word-RAM representation invariant at `base` coupling `θ : QuotHashSeed U n_max`,
abstract dictionary state `s_abs : Dynamic.State U`, and machine state `x`. -/
@[expose]
def Rep (U V w n_max base : ℕ) (θ : QuotHashSeed U n_max)
    (s_abs : Dynamic.State U) (x : Data (rSuccinct U V w n_max)) : Prop :=
  x.Bounded w ∧
  x.regs (baseReg U V w n_max) = base ∧
  x.regs (frontierReg U V w n_max) = base + space U V w n_max ∧
  ReducedKWise.TableRep base w (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 x.mem ∧
  ReducedKWise.SeedRep base (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 θ x.mem ∧
  DictStateInv U V w n_max base θ s_abs (memoryState (frontierReg U V w n_max) x)

/-- Scaled concrete potential `(66 * opFactor U V w n_max) * slotPotential`. -/
@[expose]
noncomputable def potential (U V w n_max base : ℕ) (_θ : QuotHashSeed U n_max)
    (x : Data (rSuccinct U V w n_max)) : ℕ :=
  (66 * opFactor U V w n_max) *
    slotPotential n_max (gmAt base U V w n_max (hashSpace U w n_max) x.mem)

/-- Constant `O(1)` per-operation instruction charge `313 * opFactor U V w n_max + 284689`. -/
@[expose]
noncomputable def chargeVal (U V w n_max : ℕ) : ℕ :=
  313 * opFactor U V w n_max + 284689

/-- Per-operation amortized instruction charge (`chargeVal U V w n_max` for every operation). -/
@[expose]
noncomputable def charge (U V w n_max : ℕ) (_s : Dynamic.State U) (_o : Dynamic.Op U) : ℕ :=
  chargeVal U V w n_max

/-- Standalone register encoding for `Dynamic.Op U`:
* `.query u`: `tagReg = 0`, `argUReg = u.val`, `argVReg = 0`
* `.insert u v`: `tagReg = 1`, `argUReg = u.val`, `argVReg = v`
* `.delete u`: `tagReg = 2`, `argUReg = u.val`, `argVReg = 0` -/
@[expose]
noncomputable def encode (U V w n_max : ℕ) :
    Dynamic.Op U → Fin (rSuccinct U V w n_max) → ℕ
  | .query u, r =>
    if r = tagReg U V w n_max then 0
    else if r = argUReg U V w n_max then u.val
    else 0
  | .insert u v, r =>
    if r = tagReg U V w n_max then 1
    else if r = argUReg U V w n_max then u.val
    else if r = argVReg U V w n_max then v
    else 0
  | .delete u, r =>
    if r = tagReg U V w n_max then 2
    else if r = argUReg U V w n_max then u.val
    else 0

/-- Partial argument-matching predicate for inline callers. -/
@[expose]
noncomputable def argMatch (U V w n_max : ℕ) :
    Dynamic.Op U → (Fin (rSuccinct U V w n_max) → ℕ) → Prop
  | .query u, regs =>
    regs (tagReg U V w n_max) = 0 ∧ regs (argUReg U V w n_max) = u.val
  | .insert u v, regs =>
    regs (tagReg U V w n_max) = 1 ∧ regs (argUReg U V w n_max) = u.val ∧
      regs (argVReg U V w n_max) = v
  | .delete u, regs =>
    regs (tagReg U V w n_max) = 2 ∧ regs (argUReg U V w n_max) = u.val

/-- Output decoder reading `Option ℕ` from `(resTagReg, resValReg)` for `.query` and `()` for
`.insert`/`.delete`. -/
@[expose]
noncomputable def decode (U V w n_max : ℕ) :
    (o : Dynamic.Op U) → (Fin (rSuccinct U V w n_max) → ℕ) → Option o.Result
  | .query _, regs =>
    if regs (resTagReg U V w n_max) = 0 then some none
    else some (some (regs (resValReg U V w n_max)))
  | .insert _ _, _ => some ()
  | .delete _, _ => some ()

theorem decode_query_optionWords (U V w n_max : ℕ) (u : Fin U) (res : Option ℕ)
    (regs : Fin (rSuccinct U V w n_max) → ℕ)
    (h0 : regs (resTagReg U V w n_max) = optionWords res 0)
    (h1 : regs (resValReg U V w n_max) = optionWords res 1) :
    decode U V w n_max (.query u) regs = some res := by
  dsimp only [decode]
  rw [h0, h1]
  cases res <;> rfl

/-! ## Section 5: Memory footprint congruence lemmas for `TableRep`, `SeedRep`, `DictStateInv` -/

theorem tableRep_congr {base w w₀ b b' k : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ a, base ≤ a → a < base + ReducedKWise.space w w₀ b b' k → mem₁ a = mem₂ a)
    (htab : ReducedKWise.TableRep base w w₀ b b' k mem₁) :
    ReducedKWise.TableRep base w w₀ b b' k mem₂ := by
  rcases htab with ⟨hword, hentry⟩
  refine ⟨fun wIdx hwIdx => ?_, fun idx hidx => ?_⟩
  · rw [← heq (ReducedKWise.tabBase base w₀ b b' k + wIdx)
      (by dsimp only [ReducedKWise.tabBase]; omega)
      (by dsimp only [ReducedKWise.tabBase, ReducedKWise.space]; omega)]
    exact hword wIdx hwIdx
  · have hsh : idx >>> reducedPackShift (reducedTrinomialStep w₀ b b') w <
        ReducedKWise.tableWords w w₀ b b' :=
      shiftRight_lt_reducedTableWords hidx
    rw [← heq
      (ReducedKWise.tabBase base w₀ b b' k +
        idx >>> reducedPackShift (reducedTrinomialStep w₀ b b') w)
      (by dsimp only [ReducedKWise.tabBase]; rw [Nat.add_assoc]; exact Nat.le_add_right base _)
      (by dsimp only [ReducedKWise.tabBase, ReducedKWise.space]; omega)]
    exact hentry idx hidx

theorem seedRep_congr {base w w₀ b b' k : ℕ} {θ : ReducedPolySeed w₀ b b' k}
    {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ a, base ≤ a → a < base + ReducedKWise.space w w₀ b b' k → mem₁ a = mem₂ a)
    (hseed : ReducedKWise.SeedRep base w₀ b b' k θ mem₁) :
    ReducedKWise.SeedRep base w₀ b b' k θ mem₂ := by
  rcases hseed with ⟨h0, hlimb⟩
  have hs_pos : 0 < ReducedKWise.seedWords w₀ b b' k := ReducedKWise.seedWords_pos w₀ b b' k
  refine ⟨?_, fun j m => ?_⟩
  · rw [← heq base (le_refl base) (by dsimp only [ReducedKWise.space]; omega)]
    exact h0
  · have hidx : m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val <
        k * reducedLimbCount (reducedTrinomialStep w₀ b b') := by
      calc m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val
          < reducedLimbCount (reducedTrinomialStep w₀ b b') +
              reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val :=
            Nat.add_lt_add_right m.isLt _
        _ = (j.val + 1) * reducedLimbCount (reducedTrinomialStep w₀ b b') := by ring
        _ ≤ k * reducedLimbCount (reducedTrinomialStep w₀ b b') :=
            Nat.mul_le_mul_right _ j.isLt
    have hlt_sp : base + 1 + (m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val) <
        base + ReducedKWise.space w w₀ b b' k := by
      dsimp only [ReducedKWise.space, ReducedKWise.seedWords]
      omega
    rw [← heq (base + 1 + (m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val))
      (by omega) hlt_sp]
    exact hlimb j m

theorem bucketStateInv_congr {U V w n_max h_space base : ℕ} (hw : 0 < w)
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s₁ s₂ : Memory.State}
    (heq : ∀ a, base + h_space ≤ a → a < base + totalSpace U V w n_max h_space →
      s₁.mem a = s₂.mem a)
    (hinv : BucketStateInv U V w n_max h_space base mOf L B s₁) :
    BucketStateInv U V w n_max h_space base mOf L B s₂ := by
  obtain ⟨hq, hv, hlm, hgm⟩ := arrays_congr_of_eq_on hw heq
  rcases hinv with ⟨hslot, hchains, hcm, hnodup, hsome, hdom⟩
  refine ⟨hgm ▸ hslot, hlm ▸ hchains, ?_, ?_, ?_, ?_⟩
  · simpa only [← hgm, ← hq] using hcm
  · simpa only [← hgm, ← hq] using hnodup
  · simpa only [← hgm, ← hq, ← hv] using hsome
  · simpa only [← hgm, ← hq] using hdom

theorem dictStateInv_congr {U V w n_max base : ℕ} (hw : 0 < w)
    {θ : QuotHashSeed U n_max} {s_abs : Dynamic.State U} {s₁ s₂ : Memory.State}
    (heq : ∀ a, base + hashSpace U w n_max ≤ a → a < base + space U V w n_max →
      s₁.mem a = s₂.mem a)
    (hinv : DictStateInv U V w n_max base θ s_abs s₁) :
    DictStateInv U V w n_max base θ s_abs s₂ := by
  obtain ⟨_, _, _, hgm⟩ := arrays_congr_of_eq_on hw heq
  rcases hinv with ⟨⟨L, hb⟩, htot⟩
  exact ⟨⟨L, bucketStateInv_congr hw heq hb⟩, hgm ▸ htot⟩

theorem modifies_footprint_of_table {U V w n_max base : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hout : ∀ a, ¬(base + offQuot (hashSpace U w n_max) ≤ a ∧
      a < base + space U V w n_max) → mem₂ a = mem₁ a) :
    Modifies (Block.mk base (space U V w n_max)).footprint mem₁ mem₂ := by
  intro a ha
  rw [Block.mem_footprint, Block.Owns] at ha
  dsimp only at ha
  dsimp only [offQuot] at hout
  exact hout a (fun ⟨h1, h2⟩ => ha ⟨by omega, h2⟩)

/-! ## Section 6: Common prefix and branch execution helpers -/

private theorem exec_extCode {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (henv : DictEnv U V w n_max (hashSpace U w n_max) w base)
    (u : Fin U) {x : Data (rSuccinct U V w n_max)}
    (hx_bdd : x.Bounded w)
    (hfr : x.regs (frontierReg U V w n_max) = base + space U V w n_max)
    (hu_reg : x.regs (argUReg U V w n_max) = u.val) :
    ∃ x₁ : Data (rSuccinct U V w n_max),
      ExecWithin w (extCode U V w n_max) x x₁ ((realizes_extractQuot n_max).factor * 1) ∧
      x₁.mem = x.mem ∧
      x₁.regs (frontierReg U V w n_max) = base + space U V w n_max ∧
      x₁.regs (hashKeyReg U V w n_max) = (quotientFin U n_max u).val ∧
      ∀ i : Fin 256, i ≠ 1 →
        x₁.regs (sReg U V w n_max i) = x.regs (sReg U V w n_max i) := by
  have hspec := ((realizes_extractQuot n_max).code_spec
    (frontierReg U V w n_max) (srcExt U V w n_max) (tmpExt U V w n_max)
    (tmpExt_injective U V w n_max) (srcExt_ne_tmpExt U V w n_max)
    (tmpExt_ne_frontier U V w n_max) (srcExt_ne_frontier U V w n_max)).2
  have hin : x.regs ∘ srcExt U V w n_max = WordEncoding.encode (α := ℕ) u.val := by
    funext i
    fin_cases i
    exact hu_reg
  have hsafe : ExtractQuotPre n_max w u.val (memoryState (frontierReg U V w n_max) x) :=
    ⟨u.isLt.trans hwf.2.2.1,
      (fits_bucketBits_and_mask henv hwf.1 hwf.2.1 hwf.2.2.1).1⟩
  obtain ⟨x₁, hex, hm, hout, hframe⟩ := hspec w u.val x hx_bdd hin hsafe trivial
  have hmem : x₁.mem = x.mem := congrArg Memory.State.mem hm
  have hfr₁ : x₁.regs (frontierReg U V w n_max) = base + space U V w n_max :=
    (congrArg Memory.State.frontier hm).trans hfr
  have hout0 := hout 0
  have htmp0 : tmpExt U V w n_max (Fin.castAdd ((realizes_extractQuot n_max).scratchSize + 1) 0) =
      hashKeyReg U V w n_max := rfl
  rw [htmp0] at hout0
  have hres : WordEncoding.encode (α := ℕ)
      ((Memory.spec w).clientResult (memoryState (frontierReg U V w n_max) x)
        (extractQuotProg n_max u.val)) 0 = (quotientFin U n_max u).val := by
    rw [clientResult_width]
    change u.val >>> bucketBits n_max = (quotientFin U n_max u).val
    rw [quotientFin_val_eq hwf.2.1 u, keyQuotient, Nat.shiftRight_eq_div_pow]
  rw [hres] at hout0
  refine ⟨x₁, hex, hmem, hfr₁, hout0, fun i hi1 => ?_⟩
  by_cases hif : i = 240
  · subst hif; exact hfr₁.trans hfr.symm
  · refine hframe (sReg U V w n_max i) (sReg_ne hif) (fun j => ?_)
    intro hj
    have hval := congrArg Fin.val hj
    rw [val_tmpExt, val_sReg] at hval
    have hi_lt := i.isLt
    have hi1_val : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
    split_ifs at hval <;> omega

private theorem hValOfSeed_eq_val_reducedPolyHash (U n_max : ℕ) (θ : QuotHashSeed U n_max)
    (q : Fin (2 ^ quotientBits U n_max)) :
    hValOfSeed U n_max θ q.val =
      (reducedPolyHash (2 ^ quotientBits U n_max) (qBits U n_max) (hashB n_max)
        (totalMicroBits n_max) 3 θ q).val := by
  unfold hValOfSeed evalQuotHash
  congr 2
  exact Fin.ext (Nat.mod_eq_of_lt q.isLt)

private theorem exec_hashEvalCode {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (q : Fin (2 ^ quotientBits U n_max))
    {x : Data (rSuccinct U V w n_max)}
    (hbase : x.regs (baseReg U V w n_max) = base)
    (hkey : x.regs (hashKeyReg U V w n_max) = q.val)
    (htab : ReducedKWise.TableRep base w (qBits U n_max) (hashB n_max)
      (totalMicroBits n_max) 3 x.mem)
    (hseed : ReducedKWise.SeedRep base (qBits U n_max) (hashB n_max)
      (totalMicroBits n_max) 3 θ x.mem) :
    ∃ y : Data (rSuccinct U V w n_max),
      ExecWithin w (hashEvalCode U V w n_max) x y
        (ReducedKWise.evalSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3) ∧
      y.mem = x.mem ∧
      y.regs (baseReg U V w n_max) = base ∧
      y.regs (hashOutReg U V w n_max) = hValOfSeed U n_max θ q.val ∧
      ∀ i : Fin 256, 240 ≤ i.val →
        y.regs (sReg U V w n_max i) = x.regs (sReg U V w n_max i) := by
  have hfit_hash : Fits w (base + hashSpace U w n_max) := by
    refine hfit.of_le ?_
    unfold space totalSpace offGM offLM offVal offQuot
    omega
  have hc_lt := two_mul_reducedChunkBits_hash_lt hwf.2.1 (le_of_lt hwf.2.2.1) hfit
  obtain ⟨y_core, hex_core, hymem, hy0, hy2⟩ :=
    ReducedKWise.evalCode_execWithin
      (qBits_pos U n_max)
      (qBits_le_of_le_pow hwf.1 (le_of_lt hwf.2.2.1))
      (two_pow_quotientBits_le_two_pow_qBits U n_max)
      (totalMicroBits_le_of_le_pow hwf.2.1 (le_of_lt hwf.2.2.1))
      hc_lt hfit_hash θ q (x.comap (coreReg U V w n_max))
      hbase hkey htab hseed
  let y := y_core.extend (coreReg U V w n_max) x
  have hex_ren : ExecWithin w (hashEvalCode U V w n_max) x y
      (ReducedKWise.evalSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3) :=
    hex_core.rename (coreReg_injective U V w n_max)
  have hy_base : y.regs (baseReg U V w n_max) = base := by
    change (y.comap (coreReg U V w n_max)).regs 0 = base
    rw [Data.comap_extend (coreReg_injective U V w n_max)]
    exact hy0
  have hy_out : y.regs (hashOutReg U V w n_max) = hValOfSeed U n_max θ q.val := by
    change (y.comap (coreReg U V w n_max)).regs 2 = hValOfSeed U n_max θ q.val
    rw [Data.comap_extend (coreReg_injective U V w n_max), hy2]
    exact (hValOfSeed_eq_val_reducedPolyHash U n_max θ q).symm
  refine ⟨y, hex_ren, hymem, hy_base, hy_out, fun i hi => ?_⟩
  exact Data.extend_regs_of_notMem _ _ (notMem_range_coreReg (r := sReg U V w n_max i) hi)

/-! ## Section 7: Per-operation deterministic execution of `opCode` -/

private theorem exec_opCode_query {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (s_abs : Dynamic.State U) (u : Fin U)
    {x : Data (rSuccinct U V w n_max)}
    (hrep : Rep U V w n_max base θ s_abs x)
    (harg : argMatch U V w n_max (.query u) x.regs) :
    ∃ (y : Data (rSuccinct U V w n_max)) (steps : ℕ),
      ExecWithin w (opCode U V w n_max) x y steps ∧
      decode U V w n_max (.query u) y.regs = some (s_abs u) ∧
      Rep U V w n_max base θ s_abs y ∧
      Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem ∧
      steps + potential U V w n_max base θ y ≤
        potential U V w n_max base θ x + (273 * opFactor U V w n_max + 284689) +
          (8 * opFactor U V w n_max) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dynamic.dom s_abs) u := by
  rcases hrep with ⟨hx_bdd, hbase, hfr, htab, hseed, hdict⟩
  rcases harg with ⟨htag, hu_reg⟩
  have henv : DictEnv U V w n_max (hashSpace U w n_max) w base := ⟨rfl, hfit⟩
  obtain ⟨x₁, hex_ext, hmem₁, hfr₁, hkey₁, hframe₁⟩ :=
    exec_extCode hwf henv u hx_bdd hfr hu_reg
  have hx₁_bdd : x₁.Bounded w := hex_ext.bounded hx_bdd
  have hbase₁ : x₁.regs (baseReg U V w n_max) = base :=
    (hframe₁ 0 (by decide)).trans hbase
  obtain ⟨x₂, hex_h1, hmem₂, hbase₂, hout₂, hhigh₂⟩ :=
    exec_hashEvalCode hwf hfit θ (quotientFin U n_max u) hbase₁ hkey₁
      (hmem₁ ▸ htab) (hmem₁ ▸ hseed)
  rw [quotientFin_val_eq hwf.2.1 u] at hout₂
  have hx₂_bdd : x₂.Bounded w := hex_h1.bounded hx₁_bdd
  have hfr₂ : x₂.regs (frontierReg U V w n_max) = base + space U V w n_max :=
    (hhigh₂ 240 (by decide)).trans hfr₁
  have htag₂ : x₂.regs (tagReg U V w n_max) = 0 :=
    (hhigh₂ 244 (by decide)).trans ((hframe₁ 244 (by decide)).trans htag)
  have hu₂ : x₂.regs (argUReg U V w n_max) = u.val :=
    (hhigh₂ 245 (by decide)).trans ((hframe₁ 245 (by decide)).trans hu_reg)
  let x₃ := x₂.set (zeroReg U V w n_max) 0
  have hex_z : ExecWithin (B := .exact) w (.op (.const (zeroReg U V w n_max) 0)) x₂ x₃ 1 :=
    ExecWithin.const (Nat.two_pow_pos w)
  have hx₃_bdd : x₃.Bounded w := hex_z.bounded hx₂_bdd
  have hcond_pos : (Cond.eq (tagReg U V w n_max) (zeroReg U V w n_max)).Holds x₃ := by
    change x₃.regs (tagReg U V w n_max) = x₃.regs (zeroReg U V w n_max)
    simp only [x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, htag₂]
  have hmem₃ : x₃.mem = x.mem := hmem₂.trans hmem₁
  have hfr₃ : x₃.regs (frontierReg U V w n_max) = base + space U V w n_max := by
    simp only [x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hfr₂]
  have hbase₃ : x₃.regs (baseReg U V w n_max) = base := by
    simp only [x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hbase₂]
  have hu₃ : x₃.regs (argUReg U V w n_max) = u.val := by
    simp only [x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hu₂]
  have hout₃ : x₃.regs (hashOutReg U V w n_max) =
      hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val) := by
    simp only [x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hout₂]
  have hms₃ : memoryState (frontierReg U V w n_max) x₃ =
      memoryState (frontierReg U V w n_max) x :=
    Memory.State.ext hmem₃ (hfr₃.trans hfr.symm)
  let h_q := hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val)
  let d_qry := ((base, u.val), h_q)
  have hdict₃ : DictStateInv U V w n_max base θ s_abs (memoryState (frontierReg U V w n_max) x₃) :=
    hms₃.symm ▸ hdict
  obtain ⟨hpre_qry, hst_qry, hres_qry, hcost_qry⟩ :=
    queryWithHashProg_dict_spec hwf henv θ hdict₃ u
  have hin_qry : x₃.regs ∘ srcQry U V w n_max =
      WordEncoding.encode (α := (ℕ × ℕ) × ℕ) d_qry := by
    funext i
    fin_cases i
    · exact hbase₃
    · exact hu₃
    · exact hout₃
  have hv_qry : (Memory.spec w).ValidHistory (memoryState (frontierReg U V w n_max) x₃)
      ((Memory.spec w).clientHistory (memoryState (frontierReg U V w n_max) x₃)
        (queryWithHashProg U V w n_max d_qry)) :=
    validProg_queryWithHash hpre_qry ⟨wellFormed_memoryState hx₃_bdd, le_of_eq hfr₃.symm⟩
  obtain ⟨y, hex_qry, hm_qry, hout_qry, hframe_qry⟩ :=
    ((realizes_queryWithHash U V w n_max).code_spec
      (frontierReg U V w n_max) (srcQry U V w n_max) (tmpQry U V w n_max)
      (tmpQry_injective U V w n_max) (srcQry_ne_tmpQry U V w n_max)
      (tmpQry_ne_frontier U V w n_max) (srcQry_ne_frontier U V w n_max)).2
      w d_qry x₃ hx₃_bdd hin_qry hpre_qry hv_qry
  change ExecWithin w (qryCode U V w n_max) x₃ y _ at hex_qry
  rw [clientState_width, hst_qry] at hm_qry
  rw [clientResult_width, hres_qry] at hout_qry
  have hymem : y.mem = x.mem := (congrArg Memory.State.mem hm_qry).trans hmem₃
  have hyfr : y.regs (frontierReg U V w n_max) = base + space U V w n_max :=
    (congrArg Memory.State.frontier hm_qry).trans hfr₃
  have hybase : y.regs (baseReg U V w n_max) = base := by
    rw [hframe_qry (baseReg U V w n_max) (sReg_ne (by decide)) (fun j => ?_)]
    · exact hbase₃
    · intro hj
      have hval := congrArg Fin.val hj
      rw [val_tmpQry] at hval
      change (if j.val = 0 then 252 else if j.val = 1 then 253 else 256 + j.val) = 0 at hval
      (split_ifs at hval; omega)
  have hy_dec : decode U V w n_max (.query u) y.regs = some (s_abs u) :=
    decode_query_optionWords U V w n_max u (s_abs u) y.regs (hout_qry 0) (hout_qry 1)
  have hex_br : ExecWithin w
      (.branch (.eq (tagReg U V w n_max) (zeroReg U V w n_max))
        (qryCode U V w n_max)
        (.seq (.op (.const (oneReg U V w n_max) 1))
          (.branch (.eq (tagReg U V w n_max) (oneReg U V w n_max))
            (insCode U V w n_max)
            (delCode U V w n_max)))) x₃ y _ :=
    ExecWithin.branch_pos hcond_pos hex_qry
  have hex_all : ExecWithin w (opCode U V w n_max) x y _ :=
    hex_ext.seq (hex_h1.seq (hex_z.seq hex_br))
  have hy_bdd : y.Bounded w := hex_all.bounded hx_bdd
  have hy_rep : Rep U V w n_max base θ s_abs y :=
    ⟨hy_bdd, hybase, hyfr, hymem ▸ htab, hymem ▸ hseed,
      (hm_qry.trans hms₃).symm ▸ hdict⟩
  have hmod : Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem := by
    rw [hymem]; exact fun _ _ => rfl
  have hpot_eq : potential U V w n_max base θ y = potential U V w n_max base θ x := by
    unfold potential
    rw [hymem]
  have hF_ext := factor_extractQuot_le U V w n_max
  have hF_qry := factor_queryWithHash_le U V w n_max
  have hH_le := ReducedKWise.evalSteps_le (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3
  dsimp only [ReducedKWise.evalBound] at hH_le
  have hcost_qry' :
      memoryCost (queryWithHashProg U V w n_max d_qry)
        (memoryState (frontierReg U V w n_max) x₃) + 0 + 1 ≤
      26 + 8 * probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
        (Dynamic.dom s_abs) u + 1 :=
    Nat.add_le_add_right hcost_qry 1
  have hmul_qry :
      (realizes_queryWithHash U V w n_max).factor *
        (memoryCost (queryWithHashProg U V w n_max d_qry)
          (memoryState (frontierReg U V w n_max) x₃) + 0 + 1) ≤
      27 * opFactor U V w n_max +
        (8 * opFactor U V w n_max) *
          probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
            (Dynamic.dom s_abs) u := by
    calc (realizes_queryWithHash U V w n_max).factor *
          (memoryCost (queryWithHashProg U V w n_max d_qry)
            (memoryState (frontierReg U V w n_max) x₃) + 0 + 1)
        ≤ opFactor U V w n_max *
            (26 + 8 * probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dynamic.dom s_abs) u + 1) :=
          Nat.mul_le_mul hF_qry hcost_qry'
      _ = 27 * opFactor U V w n_max +
            (8 * opFactor U V w n_max) *
              probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
                (Dynamic.dom s_abs) u := by ring
  have hmul_ext :
      (realizes_extractQuot n_max).factor *
        (memoryCost (extractQuotProg n_max u.val)
          (memoryState (frontierReg U V w n_max) x) + 0 + 1) ≤
      opFactor U V w n_max := by
    simpa only [extractQuotProg, memoryCost_pure, Nat.add_zero, Nat.zero_add, Nat.mul_one]
      using hF_ext
  refine ⟨y, _, hex_all, hy_dec, hy_rep, hmod, ?_⟩
  rw [hpot_eq]
  omega

private theorem exec_opCode_insert {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (s_abs : Dynamic.State U) (u : Fin U) (v : ℕ)
    (hval : (Dynamic.spec U V n_max).valid s_abs (.insert u v))
    {x : Data (rSuccinct U V w n_max)}
    (hrep : Rep U V w n_max base θ s_abs x)
    (harg : argMatch U V w n_max (.insert u v) x.regs) :
    ∃ (y : Data (rSuccinct U V w n_max)) (steps : ℕ),
      ExecWithin w (opCode U V w n_max) x y steps ∧
      decode U V w n_max (.insert u v) y.regs = some () ∧
      Rep U V w n_max base θ (Function.update s_abs u (some v)) y ∧
      Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem ∧
      steps + potential U V w n_max base θ y ≤
        potential U V w n_max base θ x + (273 * opFactor U V w n_max + 284689) +
          (8 * opFactor U V w n_max) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dynamic.dom s_abs) u := by
  rcases hrep with ⟨hx_bdd, hbase, hfr, htab, hseed, hdict⟩
  rcases harg with ⟨htag, hu_reg, hv_reg⟩
  have henv : DictEnv U V w n_max (hashSpace U w n_max) w base := ⟨rfl, hfit⟩
  obtain ⟨x₁, hex_ext, hmem₁, hfr₁, hkey₁, hframe₁⟩ :=
    exec_extCode hwf henv u hx_bdd hfr hu_reg
  have hx₁_bdd : x₁.Bounded w := hex_ext.bounded hx_bdd
  have hbase₁ : x₁.regs (baseReg U V w n_max) = base :=
    (hframe₁ 0 (by decide)).trans hbase
  obtain ⟨x₂, hex_h1, hmem₂, hbase₂, hout₂, hhigh₂⟩ :=
    exec_hashEvalCode hwf hfit θ (quotientFin U n_max u) hbase₁ hkey₁
      (hmem₁ ▸ htab) (hmem₁ ▸ hseed)
  rw [quotientFin_val_eq hwf.2.1 u] at hout₂
  have hx₂_bdd : x₂.Bounded w := hex_h1.bounded hx₁_bdd
  have hfr₂ : x₂.regs (frontierReg U V w n_max) = base + space U V w n_max :=
    (hhigh₂ 240 (by decide)).trans hfr₁
  have htag₂ : x₂.regs (tagReg U V w n_max) = 1 :=
    (hhigh₂ 244 (by decide)).trans ((hframe₁ 244 (by decide)).trans htag)
  have hu₂ : x₂.regs (argUReg U V w n_max) = u.val :=
    (hhigh₂ 245 (by decide)).trans ((hframe₁ 245 (by decide)).trans hu_reg)
  have hv₂ : x₂.regs (argVReg U V w n_max) = v :=
    (hhigh₂ 246 (by decide)).trans ((hframe₁ 246 (by decide)).trans hv_reg)
  let x₃ := x₂.set (zeroReg U V w n_max) 0
  have hex_z : ExecWithin (B := .exact) w (.op (.const (zeroReg U V w n_max) 0)) x₂ x₃ 1 :=
    ExecWithin.const (Nat.two_pow_pos w)
  have hx₃_bdd : x₃.Bounded w := hex_z.bounded hx₂_bdd
  have hcond_neg0 : ¬(Cond.eq (tagReg U V w n_max) (zeroReg U V w n_max)).Holds x₃ := by
    change x₃.regs (tagReg U V w n_max) ≠ x₃.regs (zeroReg U V w n_max)
    simp only [x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, htag₂, ne_eq,
      one_ne_zero, not_false_eq_true]
  let x₄ := x₃.set (oneReg U V w n_max) 1
  have hfit1 : Fits w 1 :=
    Nat.lt_of_le_of_lt Nat.one_le_two_pow (Nat.pow_lt_pow_right one_lt_two
      (lt_of_lt_of_le one_lt_two (two_le_w_of_fits_space hfit)))
  have hex_o : ExecWithin (B := .exact) w (.op (.const (oneReg U V w n_max) 1)) x₃ x₄ 1 :=
    ExecWithin.const hfit1
  have hx₄_bdd : x₄.Bounded w := hex_o.bounded hx₃_bdd
  have hcond_pos1 : (Cond.eq (tagReg U V w n_max) (oneReg U V w n_max)).Holds x₄ := by
    change x₄.regs (tagReg U V w n_max) = x₄.regs (oneReg U V w n_max)
    simp only [x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, htag₂]
  have hmem₄ : x₄.mem = x.mem := hmem₂.trans hmem₁
  have hfr₄ : x₄.regs (frontierReg U V w n_max) = base + space U V w n_max := by
    simp only [x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hfr₂]
  have hbase₄ : x₄.regs (baseReg U V w n_max) = base := by
    simp only [x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hbase₂]
  have hu₄ : x₄.regs (argUReg U V w n_max) = u.val := by
    simp only [x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hu₂]
  have hv₄ : x₄.regs (argVReg U V w n_max) = v := by
    simp only [x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hv₂]
  have hout₄ : x₄.regs (hashOutReg U V w n_max) =
      hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val) := by
    simp only [x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hout₂]
  have hms₄ : memoryState (frontierReg U V w n_max) x₄ =
      memoryState (frontierReg U V w n_max) x :=
    Memory.State.ext hmem₄ (hfr₄.trans hfr.symm)
  let h_q := hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val)
  let d_ins := (((base, u.val), v), h_q)
  have hdict₄ : DictStateInv U V w n_max base θ s_abs (memoryState (frontierReg U V w n_max) x₄) :=
    hms₄.symm ▸ hdict
  obtain ⟨hpre_ins, hfr_ins, hout_ins, hdict_ins, hcost_ins⟩ :=
    insertWithHashProg_dict_spec hwf henv θ hdict₄ u v hval
  have hin_ins : x₄.regs ∘ srcIns U V w n_max =
      WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ) d_ins := by
    funext i
    fin_cases i
    · exact hbase₄
    · exact hu₄
    · exact hv₄
    · exact hout₄
  have hv_ins : (Memory.spec w).ValidHistory (memoryState (frontierReg U V w n_max) x₄)
      ((Memory.spec w).clientHistory (memoryState (frontierReg U V w n_max) x₄)
        (insertWithHashProg U V w n_max d_ins)) :=
    validProg_insertWithHash hpre_ins ⟨wellFormed_memoryState hx₄_bdd, le_of_eq hfr₄.symm⟩
  obtain ⟨y, hex_ins, hm_ins, _, hframe_ins⟩ :=
    ((realizes_insertWithHash U V w n_max).code_spec
      (frontierReg U V w n_max) (srcIns U V w n_max) (tmpIns U V w n_max)
      (tmpIns_injective U V w n_max) (srcIns_ne_tmpIns U V w n_max)
      (tmpIns_ne_frontier U V w n_max) (srcIns_ne_frontier U V w n_max)).2
      w d_ins x₄ hx₄_bdd hin_ins hpre_ins hv_ins
  change ExecWithin w (insCode U V w n_max) x₄ y _ at hex_ins
  rw [clientState_width] at hm_ins
  have hyfr : y.regs (frontierReg U V w n_max) = base + space U V w n_max :=
    ((congrArg Memory.State.frontier hm_ins).trans hfr_ins).trans hfr₄
  have hybase : y.regs (baseReg U V w n_max) = base := by
    rw [hframe_ins (baseReg U V w n_max) (sReg_ne (by decide)) (fun j => ?_)]
    · exact hbase₄
    · intro hj
      have hval := congrArg Fin.val hj
      rw [val_tmpIns] at hval
      change 256 + j.val = 0 at hval
      omega
  have hhash_eq : ∀ a, base ≤ a → a < base + hashSpace U w n_max → x.mem a = y.mem a := by
    intro a ha1 ha2
    have hmy : y.mem a = (memoryState (frontierReg U V w n_max) x₄).mem a := by
      change (memoryState (frontierReg U V w n_max) y).mem a = _
      rw [hm_ins]
      exact hout_ins a (by dsimp [offQuot]; omega)
    rw [hmy]
    exact hmem₄.symm ▸ rfl
  have hex_br1 : ExecWithin w
      (.branch (.eq (tagReg U V w n_max) (oneReg U V w n_max))
        (insCode U V w n_max)
        (delCode U V w n_max)) x₄ y _ :=
    ExecWithin.branch_pos hcond_pos1 hex_ins
  have hex_br0 : ExecWithin w
      (.branch (.eq (tagReg U V w n_max) (zeroReg U V w n_max))
        (qryCode U V w n_max)
        (.seq (.op (.const (oneReg U V w n_max) 1))
          (.branch (.eq (tagReg U V w n_max) (oneReg U V w n_max))
            (insCode U V w n_max)
            (delCode U V w n_max)))) x₃ y _ :=
    ExecWithin.branch_neg hcond_neg0 (hex_o.seq hex_br1)
  have hex_all : ExecWithin w (opCode U V w n_max) x y _ :=
    hex_ext.seq (hex_h1.seq (hex_z.seq hex_br0))
  have hy_bdd : y.Bounded w := hex_all.bounded hx_bdd
  have hy_rep : Rep U V w n_max base θ (Function.update s_abs u (some v)) y :=
    ⟨hy_bdd, hybase, hyfr,
      tableRep_congr hhash_eq htab,
      seedRep_congr hhash_eq hseed,
      by rw [hm_ins]; exact hdict_ins⟩
  have hmod : Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem := by
    refine modifies_footprint_of_table (fun a ha => ?_)
    have hmy : y.mem a = x₄.mem a := by
      change (memoryState (frontierReg U V w n_max) y).mem a = _
      rw [hm_ins]
      exact hout_ins a ha
    rw [hmy, hmem₄]
  have hgm_y : gmAt base U V w n_max (hashSpace U w n_max) y.mem =
      gmAt base U V w n_max (hashSpace U w n_max)
        ((Memory.spec 0).clientState (memoryState (frontierReg U V w n_max) x₄)
          (insertWithHashProg U V w n_max d_ins)).mem :=
    congrArg (fun s : Memory.State => gmAt base U V w n_max (hashSpace U w n_max) s.mem) hm_ins
  have hgm_x4 : gmAt base U V w n_max (hashSpace U w n_max)
      (memoryState (frontierReg U V w n_max) x₄).mem =
      gmAt base U V w n_max (hashSpace U w n_max) x.mem := by
    change gmAt base U V w n_max (hashSpace U w n_max) x₄.mem = _
    rw [hmem₄]
  have hF_ext := factor_extractQuot_le U V w n_max
  have hF_ins := factor_insertWithHash_le U V w n_max
  have hH_le := ReducedKWise.evalSteps_le (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3
  dsimp only [ReducedKWise.evalBound] at hH_le
  have hmul_ext :
      (realizes_extractQuot n_max).factor *
        (memoryCost (extractQuotProg n_max u.val)
          (memoryState (frontierReg U V w n_max) x) + 0 + 1) ≤
      opFactor U V w n_max := by
    simpa only [extractQuotProg, memoryCost_pure, Nat.add_zero, Nat.zero_add, Nat.mul_one]
      using hF_ext
  have hmul_ins :
      (realizes_insertWithHash U V w n_max).factor *
        (memoryCost (insertWithHashProg U V w n_max d_ins)
          (memoryState (frontierReg U V w n_max) x₄) + 0 + 1) ≤
      opFactor U V w n_max *
        memoryCost (insertWithHashProg U V w n_max d_ins)
          (memoryState (frontierReg U V w n_max) x₄) +
        opFactor U V w n_max := by
    calc (realizes_insertWithHash U V w n_max).factor *
          (memoryCost (insertWithHashProg U V w n_max d_ins)
            (memoryState (frontierReg U V w n_max) x₄) + 0 + 1)
        ≤ opFactor U V w n_max *
            (memoryCost (insertWithHashProg U V w n_max d_ins)
              (memoryState (frontierReg U V w n_max) x₄) + 1) :=
          Nat.mul_le_mul hF_ins (by omega)
      _ = opFactor U V w n_max *
            memoryCost (insertWithHashProg U V w n_max d_ins)
              (memoryState (frontierReg U V w n_max) x₄) +
            opFactor U V w n_max := by ring
  rw [hgm_x4] at hcost_ins
  have hcost_scaled :
      opFactor U V w n_max *
        memoryCost (insertWithHashProg U V w n_max d_ins)
          (memoryState (frontierReg U V w n_max) x₄) +
      (66 * opFactor U V w n_max) *
        slotPotential n_max
          (gmAt base U V w n_max (hashSpace U w n_max)
            ((Memory.spec 0).clientState (memoryState (frontierReg U V w n_max) x₄)
              (insertWithHashProg U V w n_max d_ins)).mem) ≤
      (66 * opFactor U V w n_max) *
        slotPotential n_max (gmAt base U V w n_max (hashSpace U w n_max) x.mem) +
      184 * opFactor U V w n_max +
      (8 * opFactor U V w n_max) *
        probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
          (Dynamic.dom s_abs) u := by
    calc opFactor U V w n_max *
          memoryCost (insertWithHashProg U V w n_max d_ins)
            (memoryState (frontierReg U V w n_max) x₄) +
        (66 * opFactor U V w n_max) *
          slotPotential n_max
            (gmAt base U V w n_max (hashSpace U w n_max)
              ((Memory.spec 0).clientState (memoryState (frontierReg U V w n_max) x₄)
                (insertWithHashProg U V w n_max d_ins)).mem)
        = opFactor U V w n_max *
            (memoryCost (insertWithHashProg U V w n_max d_ins)
              (memoryState (frontierReg U V w n_max) x₄) +
              66 * slotPotential n_max
                (gmAt base U V w n_max (hashSpace U w n_max)
                  ((Memory.spec 0).clientState (memoryState (frontierReg U V w n_max) x₄)
                    (insertWithHashProg U V w n_max d_ins)).mem)) := by ring
      _ ≤ opFactor U V w n_max *
            (66 * slotPotential n_max (gmAt base U V w n_max (hashSpace U w n_max) x.mem) +
              184 +
              8 * probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
                (Dynamic.dom s_abs) u) :=
          Nat.mul_le_mul_left _ hcost_ins
      _ = (66 * opFactor U V w n_max) *
            slotPotential n_max (gmAt base U V w n_max (hashSpace U w n_max) x.mem) +
          184 * opFactor U V w n_max +
          (8 * opFactor U V w n_max) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dynamic.dom s_abs) u := by ring
  refine ⟨y, _, hex_all, rfl, hy_rep, hmod, ?_⟩
  unfold potential
  rw [hgm_y]
  omega

private theorem exec_opCode_delete {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (s_abs : Dynamic.State U) (u : Fin U)
    {x : Data (rSuccinct U V w n_max)}
    (hrep : Rep U V w n_max base θ s_abs x)
    (harg : argMatch U V w n_max (.delete u) x.regs) :
    ∃ (y : Data (rSuccinct U V w n_max)) (steps : ℕ),
      ExecWithin w (opCode U V w n_max) x y steps ∧
      decode U V w n_max (.delete u) y.regs = some () ∧
      Rep U V w n_max base θ (Function.update s_abs u none) y ∧
      Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem ∧
      steps + potential U V w n_max base θ y ≤
        potential U V w n_max base θ x + (273 * opFactor U V w n_max + 284689) +
          (8 * opFactor U V w n_max) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dynamic.dom s_abs) u := by
  rcases hrep with ⟨hx_bdd, hbase, hfr, htab, hseed, hdict⟩
  rcases harg with ⟨htag, hu_reg⟩
  have henv : DictEnv U V w n_max (hashSpace U w n_max) w base := ⟨rfl, hfit⟩
  obtain ⟨x₁, hex_ext, hmem₁, hfr₁, hkey₁, hframe₁⟩ :=
    exec_extCode hwf henv u hx_bdd hfr hu_reg
  have hx₁_bdd : x₁.Bounded w := hex_ext.bounded hx_bdd
  have hbase₁ : x₁.regs (baseReg U V w n_max) = base :=
    (hframe₁ 0 (by decide)).trans hbase
  obtain ⟨x₂, hex_h1, hmem₂, hbase₂, hout₂, hhigh₂⟩ :=
    exec_hashEvalCode hwf hfit θ (quotientFin U n_max u) hbase₁ hkey₁
      (hmem₁ ▸ htab) (hmem₁ ▸ hseed)
  rw [quotientFin_val_eq hwf.2.1 u] at hout₂
  have hx₂_bdd : x₂.Bounded w := hex_h1.bounded hx₁_bdd
  have hfr₂ : x₂.regs (frontierReg U V w n_max) = base + space U V w n_max :=
    (hhigh₂ 240 (by decide)).trans hfr₁
  have htag₂ : x₂.regs (tagReg U V w n_max) = 2 :=
    (hhigh₂ 244 (by decide)).trans ((hframe₁ 244 (by decide)).trans htag)
  have hu₂ : x₂.regs (argUReg U V w n_max) = u.val :=
    (hhigh₂ 245 (by decide)).trans ((hframe₁ 245 (by decide)).trans hu_reg)
  let x₃ := x₂.set (zeroReg U V w n_max) 0
  have hex_z : ExecWithin (B := .exact) w (.op (.const (zeroReg U V w n_max) 0)) x₂ x₃ 1 :=
    ExecWithin.const (Nat.two_pow_pos w)
  have hx₃_bdd : x₃.Bounded w := hex_z.bounded hx₂_bdd
  have hcond_neg0 : ¬(Cond.eq (tagReg U V w n_max) (zeroReg U V w n_max)).Holds x₃ := by
    change x₃.regs (tagReg U V w n_max) ≠ x₃.regs (zeroReg U V w n_max)
    simp only [x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, htag₂, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true]
  let x₄ := x₃.set (oneReg U V w n_max) 1
  have hfit1 : Fits w 1 :=
    Nat.lt_of_le_of_lt Nat.one_le_two_pow (Nat.pow_lt_pow_right one_lt_two
      (lt_of_lt_of_le one_lt_two (two_le_w_of_fits_space hfit)))
  have hex_o : ExecWithin (B := .exact) w (.op (.const (oneReg U V w n_max) 1)) x₃ x₄ 1 :=
    ExecWithin.const hfit1
  have hx₄_bdd : x₄.Bounded w := hex_o.bounded hx₃_bdd
  have hcond_neg1 : ¬(Cond.eq (tagReg U V w n_max) (oneReg U V w n_max)).Holds x₄ := by
    change x₄.regs (tagReg U V w n_max) ≠ x₄.regs (oneReg U V w n_max)
    simp only [x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, htag₂, ne_eq,
      Nat.reduceEqDiff, not_false_eq_true]
  let x₅ := x₄.set (hqReg U V w n_max) (x₄.regs (hashOutReg U V w n_max))
  have hex_cp : ExecWithin (B := .exact) w
      (.op (.copy (hqReg U V w n_max) (hashOutReg U V w n_max))) x₄ x₅ 1 :=
    ExecWithin.copy
  have hx₅_bdd : x₅.Bounded w := hex_cp.bounded hx₄_bdd
  have hmem₅ : x₅.mem = x.mem := hmem₂.trans hmem₁
  have hfr₅ : x₅.regs (frontierReg U V w n_max) = base + space U V w n_max := by
    simp only [x₅, x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hfr₂]
  have hbase₅ : x₅.regs (baseReg U V w n_max) = base := by
    simp only [x₅, x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hbase₂]
  have hu₅ : x₅.regs (argUReg U V w n_max) = u.val := by
    simp only [x₅, x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hu₂]
  have hhq₅ : x₅.regs (hqReg U V w n_max) =
      hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val) := by
    simp only [x₅, x₄, x₃, set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hout₂]
  have hms₅ : memoryState (frontierReg U V w n_max) x₅ =
      memoryState (frontierReg U V w n_max) x :=
    Memory.State.ext hmem₅ (hfr₅.trans hfr.symm)
  let s₅ := memoryState (frontierReg U V w n_max) x₅
  let h_q := hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val)
  let d_prep := ((base, u.val), h_q)
  let prog_prep := deletePrepWithHashProg U V w n_max d_prep
  have hdict₅ : DictStateInv U V w n_max base θ s_abs s₅ := by
    dsimp only [s₅]
    rw [hms₅]
    exact hdict
  obtain ⟨found, j_del, phys_del, q_last, hprep_eq, hpre_prep, hst_prep, hqlast_lt,
      hpre_fin, hfr_fin, hout_fin, hdict_fin, hcost_del⟩ :=
    deleteWithHashProg_dict_spec hwf henv θ hdict₅ u
  let h_q_last := hValOfSeed U n_max θ q_last
  let d_fin := ((((base, u.val), h_q), ((found, j_del), phys_del)), h_q_last)
  let prog_fin := deleteFinishWithHashProg U V w n_max d_fin
  have hin_prep : x₅.regs ∘ srcDelPrep U V w n_max =
      WordEncoding.encode (α := (ℕ × ℕ) × ℕ) d_prep := by
    funext i
    fin_cases i
    · exact hbase₅
    · exact hu₅
    · exact hhq₅
  have hv_prep : (Memory.spec w).ValidHistory s₅ ((Memory.spec w).clientHistory s₅ prog_prep) :=
    validProg_deletePrepWithHash hpre_prep ⟨wellFormed_memoryState hx₅_bdd, le_of_eq hfr₅.symm⟩
  obtain ⟨x₆, hex_prep, hm_prep, hout_prep, hframe_prep⟩ :=
    ((realizes_deletePrepWithHash U V w n_max).code_spec
      (frontierReg U V w n_max) (srcDelPrep U V w n_max) (tmpDelPrep U V w n_max)
      (tmpDelPrep_injective U V w n_max) (srcDelPrep_ne_tmpDelPrep U V w n_max)
      (tmpDelPrep_ne_frontier U V w n_max) (srcDelPrep_ne_frontier U V w n_max)).2
      w d_prep x₅ hx₅_bdd hin_prep hpre_prep hv_prep
  change ExecWithin w (delPrepCode U V w n_max) x₅ x₆ _ at hex_prep
  rw [clientState_width, hst_prep] at hm_prep
  rw [clientResult_width, hprep_eq] at hout_prep
  have hx₆_bdd : x₆.Bounded w := hex_prep.bounded hx₅_bdd
  have hmem₆ : x₆.mem = x.mem := (congrArg Memory.State.mem hm_prep).trans hmem₅
  have hfr₆ : x₆.regs (frontierReg U V w n_max) = base + space U V w n_max :=
    (congrArg Memory.State.frontier hm_prep).trans hfr₅
  have hframe6_of : ∀ i : Fin 256,
      i ≠ 240 → i ≠ 249 → i ≠ 250 → i ≠ 251 → i ≠ 1 →
        x₆.regs (sReg U V w n_max i) = x₅.regs (sReg U V w n_max i) := by
    intro i hi240 hi249 hi250 hi251 hi1
    refine hframe_prep (sReg U V w n_max i) (sReg_ne hi240) (fun j => ?_)
    intro hj
    have hval := congrArg Fin.val hj
    rw [val_tmpDelPrep, val_sReg] at hval
    have hi_lt := i.isLt
    have h249 : i.val ≠ 249 := fun h => hi249 (Fin.ext h)
    have h250 : i.val ≠ 250 := fun h => hi250 (Fin.ext h)
    have h251 : i.val ≠ 251 := fun h => hi251 (Fin.ext h)
    have h1 : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
    split_ifs at hval <;> omega
  have hbase₆ : x₆.regs (baseReg U V w n_max) = base :=
    (hframe6_of 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbase₅
  have hu₆ : x₆.regs (argUReg U V w n_max) = u.val :=
    (hframe6_of 245 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hu₅
  have hhq₆ : x₆.regs (hqReg U V w n_max) = h_q :=
    (hframe6_of 248 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hhq₅
  have hfound₆ : x₆.regs (foundReg U V w n_max) = found := hout_prep 0
  have hjdel₆ : x₆.regs (jDelReg U V w n_max) = j_del := hout_prep 1
  have hphys₆ : x₆.regs (physDelReg U V w n_max) = phys_del := hout_prep 2
  have hkey₆ : x₆.regs (hashKeyReg U V w n_max) = q_last := hout_prep 3
  obtain ⟨x₇, hex_h2, hmem₇, hbase₇, hout₇, hhigh₇⟩ :=
    exec_hashEvalCode hwf hfit θ ⟨q_last, hqlast_lt⟩ hbase₆ hkey₆
      (hmem₆ ▸ htab) (hmem₆ ▸ hseed)
  have hx₇_bdd : x₇.Bounded w := hex_h2.bounded hx₆_bdd
  have hmem₇_x : x₇.mem = x.mem := hmem₇.trans hmem₆
  have hfr₇ : x₇.regs (frontierReg U V w n_max) = base + space U V w n_max :=
    (hhigh₇ 240 (by decide)).trans hfr₆
  have hu₇ : x₇.regs (argUReg U V w n_max) = u.val :=
    (hhigh₇ 245 (by decide)).trans hu₆
  have hhq₇ : x₇.regs (hqReg U V w n_max) = h_q :=
    (hhigh₇ 248 (by decide)).trans hhq₆
  have hfound₇ : x₇.regs (foundReg U V w n_max) = found :=
    (hhigh₇ 249 (by decide)).trans hfound₆
  have hjdel₇ : x₇.regs (jDelReg U V w n_max) = j_del :=
    (hhigh₇ 250 (by decide)).trans hjdel₆
  have hphys₇ : x₇.regs (physDelReg U V w n_max) = phys_del :=
    (hhigh₇ 251 (by decide)).trans hphys₆
  have hms₇ : memoryState (frontierReg U V w n_max) x₇ = s₅ :=
    Memory.State.ext (hmem₇_x.trans hmem₅.symm) (hfr₇.trans hfr₅.symm)
  have hin_fin : x₇.regs ∘ srcDelFin U V w n_max =
      WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ) d_fin := by
    funext i
    fin_cases i
    · exact hbase₇
    · exact hu₇
    · exact hhq₇
    · exact hfound₇
    · exact hjdel₇
    · exact hphys₇
    · exact hout₇
  have hv_fin : (Memory.spec w).ValidHistory (memoryState (frontierReg U V w n_max) x₇)
      ((Memory.spec w).clientHistory (memoryState (frontierReg U V w n_max) x₇) prog_fin) := by
    rw [hms₇]
    exact validProg_deleteFinishWithHash hpre_fin
      ⟨wellFormed_memoryState hx₅_bdd, le_of_eq hfr₅.symm⟩
  have hpre_fin₇ : DeleteFinishWithHashPre U V w n_max w d_fin
      (memoryState (frontierReg U V w n_max) x₇) := by
    rw [hms₇]
    exact hpre_fin
  obtain ⟨y, hex_fin, hm_fin, _, hframe_fin⟩ :=
    ((realizes_deleteFinishWithHash U V w n_max).code_spec
      (frontierReg U V w n_max) (srcDelFin U V w n_max) (tmpDelFin U V w n_max)
      (tmpDelFin_injective U V w n_max) (srcDelFin_ne_tmpDelFin U V w n_max)
      (tmpDelFin_ne_frontier U V w n_max) (srcDelFin_ne_frontier U V w n_max)).2
      w d_fin x₇ hx₇_bdd hin_fin hpre_fin₇ hv_fin
  change ExecWithin w (delFinCode U V w n_max) x₇ y _ at hex_fin
  rw [clientState_width, hms₇] at hm_fin
  have hyfr : y.regs (frontierReg U V w n_max) = base + space U V w n_max :=
    ((congrArg Memory.State.frontier hm_fin).trans hfr_fin).trans hfr₅
  have hybase : y.regs (baseReg U V w n_max) = base := by
    rw [hframe_fin (baseReg U V w n_max) (sReg_ne (by decide)) (fun j => ?_)]
    · exact hbase₇
    · intro hj
      have hval := congrArg Fin.val hj
      rw [val_tmpDelFin] at hval
      change 256 + j.val = 0 at hval
      omega
  have hhash_eq : ∀ a, base ≤ a → a < base + hashSpace U w n_max → x.mem a = y.mem a := by
    intro a ha1 ha2
    have hmy : y.mem a = s₅.mem a := by
      change (memoryState (frontierReg U V w n_max) y).mem a = _
      rw [hm_fin]
      exact hout_fin a (by dsimp [offQuot]; omega)
    rw [hmy]
    exact hmem₅.symm ▸ rfl
  have hex_del : ExecWithin w (delCode U V w n_max) x₄ y _ :=
    hex_cp.seq (hex_prep.seq (hex_h2.seq hex_fin))
  have hex_br1 : ExecWithin w
      (.branch (.eq (tagReg U V w n_max) (oneReg U V w n_max))
        (insCode U V w n_max)
        (delCode U V w n_max)) x₄ y _ :=
    ExecWithin.branch_neg hcond_neg1 hex_del
  have hex_br0 : ExecWithin w
      (.branch (.eq (tagReg U V w n_max) (zeroReg U V w n_max))
        (qryCode U V w n_max)
        (.seq (.op (.const (oneReg U V w n_max) 1))
          (.branch (.eq (tagReg U V w n_max) (oneReg U V w n_max))
            (insCode U V w n_max)
            (delCode U V w n_max)))) x₃ y _ :=
    ExecWithin.branch_neg hcond_neg0 (hex_o.seq hex_br1)
  have hex_all : ExecWithin w (opCode U V w n_max) x y _ :=
    hex_ext.seq (hex_h1.seq (hex_z.seq hex_br0))
  have hy_bdd : y.Bounded w := hex_all.bounded hx_bdd
  have hy_rep : Rep U V w n_max base θ (Function.update s_abs u none) y :=
    ⟨hy_bdd, hybase, hyfr,
      tableRep_congr hhash_eq htab,
      seedRep_congr hhash_eq hseed,
      by rw [hm_fin]; exact hdict_fin⟩
  have hmod : Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem := by
    refine modifies_footprint_of_table (fun a ha => ?_)
    have hmy : y.mem a = s₅.mem a := by
      change (memoryState (frontierReg U V w n_max) y).mem a = _
      rw [hm_fin]
      exact hout_fin a ha
    rw [hmy]
    exact congrFun hmem₅ a
  have hgm_y : gmAt base U V w n_max (hashSpace U w n_max) y.mem =
      gmAt base U V w n_max (hashSpace U w n_max)
        ((Memory.spec 0).clientState s₅ prog_fin).mem :=
    congrArg (fun s : Memory.State => gmAt base U V w n_max (hashSpace U w n_max) s.mem) hm_fin
  have hgm_s5 : gmAt base U V w n_max (hashSpace U w n_max) s₅.mem =
      gmAt base U V w n_max (hashSpace U w n_max) x.mem := by
    change gmAt base U V w n_max (hashSpace U w n_max) x₅.mem = _
    rw [hmem₅]
  have hF_ext := factor_extractQuot_le U V w n_max
  have hF_prep := factor_deletePrepWithHash_le U V w n_max
  have hF_fin := factor_deleteFinishWithHash_le U V w n_max
  have hH_le := ReducedKWise.evalSteps_le (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3
  dsimp only [ReducedKWise.evalBound] at hH_le
  have hmul_ext :
      (realizes_extractQuot n_max).factor *
        (memoryCost (extractQuotProg n_max u.val)
          (memoryState (frontierReg U V w n_max) x) + 0 + 1) ≤
      opFactor U V w n_max := by
    simpa only [extractQuotProg, memoryCost_pure, Nat.add_zero, Nat.zero_add, Nat.mul_one]
      using hF_ext
  have hmul_prep :
      (realizes_deletePrepWithHash U V w n_max).factor *
        (memoryCost (deletePrepWithHashProg U V w n_max d_prep)
          (memoryState (frontierReg U V w n_max) x₅) + 0 + 1) ≤
      opFactor U V w n_max * memoryCost prog_prep s₅ + opFactor U V w n_max := by
    calc (realizes_deletePrepWithHash U V w n_max).factor *
          (memoryCost prog_prep s₅ + 0 + 1)
        ≤ opFactor U V w n_max * (memoryCost prog_prep s₅ + 1) :=
          Nat.mul_le_mul hF_prep (by omega)
      _ = opFactor U V w n_max * memoryCost prog_prep s₅ + opFactor U V w n_max := by ring
  have hmul_fin :
      (realizes_deleteFinishWithHash U V w n_max).factor *
        (memoryCost (deleteFinishWithHashProg U V w n_max d_fin)
          (memoryState (frontierReg U V w n_max) x₇) + 0 + 1) ≤
      opFactor U V w n_max * memoryCost prog_fin s₅ + opFactor U V w n_max := by
    change (realizes_deleteFinishWithHash U V w n_max).factor *
        (memoryCost prog_fin (memoryState (frontierReg U V w n_max) x₇) + 0 + 1) ≤ _
    rw [hms₇]
    calc (realizes_deleteFinishWithHash U V w n_max).factor *
          (memoryCost prog_fin s₅ + 0 + 1)
        ≤ opFactor U V w n_max * (memoryCost prog_fin s₅ + 1) :=
          Nat.mul_le_mul hF_fin (by omega)
      _ = opFactor U V w n_max * memoryCost prog_fin s₅ + opFactor U V w n_max := by ring
  rw [hgm_s5] at hcost_del
  have hcost_scaled :
      opFactor U V w n_max * memoryCost prog_prep s₅ +
      opFactor U V w n_max * memoryCost prog_fin s₅ +
      (66 * opFactor U V w n_max) *
        slotPotential n_max
          (gmAt base U V w n_max (hashSpace U w n_max)
            ((Memory.spec 0).clientState s₅ prog_fin).mem) ≤
      (66 * opFactor U V w n_max) *
        slotPotential n_max (gmAt base U V w n_max (hashSpace U w n_max) x.mem) +
      270 * opFactor U V w n_max +
      (8 * opFactor U V w n_max) *
        probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
          (Dynamic.dom s_abs) u := by
    calc opFactor U V w n_max * memoryCost prog_prep s₅ +
        opFactor U V w n_max * memoryCost prog_fin s₅ +
        (66 * opFactor U V w n_max) *
          slotPotential n_max
            (gmAt base U V w n_max (hashSpace U w n_max)
              ((Memory.spec 0).clientState s₅ prog_fin).mem)
        = opFactor U V w n_max *
            (memoryCost prog_prep s₅ + memoryCost prog_fin s₅ +
              66 * slotPotential n_max
                (gmAt base U V w n_max (hashSpace U w n_max)
                  ((Memory.spec 0).clientState s₅ prog_fin).mem)) := by ring
      _ ≤ opFactor U V w n_max *
            (66 * slotPotential n_max (gmAt base U V w n_max (hashSpace U w n_max) x.mem) +
              270 +
              8 * probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
                (Dynamic.dom s_abs) u) :=
          Nat.mul_le_mul_left _ hcost_del
      _ = (66 * opFactor U V w n_max) *
            slotPotential n_max (gmAt base U V w n_max (hashSpace U w n_max) x.mem) +
          270 * opFactor U V w n_max +
          (8 * opFactor U V w n_max) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dynamic.dom s_abs) u := by ring
  refine ⟨y, _, hex_all, rfl, hy_rep, hmod, ?_⟩
  unfold potential
  rw [hgm_y]
  omega

/-- Extract the target key `u : Fin U` of a dynamic dictionary operation `o : Dynamic.Op U`. -/
@[expose]
def opKey {U : ℕ} : Dynamic.Op U → Fin U
  | .query u => u
  | .insert u _ => u
  | .delete u => u

/-- Unified per-operation deterministic execution of `opCode` for any `o : Dynamic.Op U`. -/
theorem exec_opCode {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (s_abs : Dynamic.State U) (o : Dynamic.Op U)
    (hval : (Dynamic.spec U V n_max).valid s_abs o)
    {x : Data (rSuccinct U V w n_max)}
    (hrep : Rep U V w n_max base θ s_abs x)
    (harg : argMatch U V w n_max o x.regs) :
    ∃ (y : Data (rSuccinct U V w n_max)) (steps : ℕ),
      ExecWithin w (opCode U V w n_max) x y steps ∧
      decode U V w n_max o y.regs = some ((Dynamic.spec U V n_max).stepFn s_abs o).2 ∧
      Rep U V w n_max base θ ((Dynamic.spec U V n_max).stepFn s_abs o).1 y ∧
      Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem ∧
      steps + potential U V w n_max base θ y ≤
        potential U V w n_max base θ x + (273 * opFactor U V w n_max + 284689) +
          (8 * opFactor U V w n_max) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dynamic.dom s_abs) (opKey o) := by
  cases o with
  | query u => exact exec_opCode_query hwf hfit θ s_abs u hrep harg
  | insert u v => exact exec_opCode_insert hwf hfit θ s_abs u v hval hrep harg
  | delete u => exact exec_opCode_delete hwf hfit θ s_abs u hrep harg

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
