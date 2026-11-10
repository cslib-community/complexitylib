/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.OfWordRAM
public import CslibFrontier.DataStructure.CellProbe.OfWordRAM
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
import CslibFrontier.Probability.PMF.Expect

/-!
# Word-RAM-to-Cell-Probe Simulation Bridge and Lower-Bound Transfer Tests

Kernel-checked end-to-end instances, lower-bound transfers, and non-vacuity sanity checks for
`CslibFrontier.Computability.CellProbe.OfWordRAM` and
`CslibFrontier.DataStructure.CellProbe.OfWordRAM`:

1. **Concrete deterministic `WordRAM.StateTransitionImpl` → `CellProbe.StateTransitionImpl`
   simulations on `Dictionary.Dynamic.spec`:**
   - **Zero persistent registers (`persistentRegCount P = 0`, `∀ i, P.input i = true`):**
     direct-mapped `Dictionary.Dynamic.spec 2 3 2` at `base = 0, space = 2, w = 2` maps via
     `toCellProbe` to a `2`-cell `2`-bit `CellProbe.StateTransitionImpl` with `0` extra cells and
     `0` extra probes per operation, bounds `initFresh` probes via `simInit_spec`, and checks an
     explicit `insert → insert → query → delete → query → query` sequence.
   - **Positive persistent registers (`persistentRegCount P = 2`):** relocated
     `Dictionary.Dynamic.spec 2 3 2` at `base = 1, space = 2, w = 3` keeps two persistent
     registers (`r0 = base`, `r1 = 1`), comparing standard `toCellProbe` (`4` cells of width `3`,
     `+ 4` probes/op) against single-spill `toCellProbeWide` (`3` cells of width `6`, `+ 2`
     probes/op).
2. **Unconditional contrapositive Word-RAM lower-bound transfer over non-`Fintype`
   `Dictionary.Dynamic.Op 1` (`0` `η`-loss):** proves a `3`-probe deterministic step-indexed
   `IndexedScheme` lower bound across `[.insert 0 0, .query 0]` and `[.insert 0 1, .query 0]` at
   arbitrary cell count and word width, then transfers it via
   `wordRAM_lower_bound_of_det_cellProbe_lower_bound`,
   `wordRAM_lower_bound_of_det_cellProbe_wide`, and
   `oblivious_wordRAM_lower_bound_of_det_cellProbe` to every zero-error randomized Word-RAM
   implementation.
3. **Trivial `[Instr.halt retReg]` non-vacuity sanity check:** proves directly from
   `ExecProgramDist.haltedLim_eq` that a `1`-instruction `[Instr.halt retReg]` flat program cannot
   satisfy `ExecFlatProgramOps` on both `[.insert 0 0, .query 0]` and `[.insert 0 1, .query 0]`
   under any register count, input mask, encoding, or decoding.
-/

public section

namespace CslibFrontierTests.CellProbeOfWordRAM

open Cslib Cslib.WordRAM Cslib.CellProbe Cslib.DataStructure
open Cslib.DataStructure.CellProbe
open scoped ENNReal

instance (U : ℕ) : ∀ o : Dictionary.Dynamic.Op U, Inhabited o.Result
  | .query _ => inferInstanceAs (Inhabited (Option ℕ))
  | .insert _ _ => inferInstanceAs (Inhabited Unit)
  | .delete _ => inferInstanceAs (Inhabited Unit)

/-! ### 1A. Deterministic simulation with `persistentRegCount P = 0` (`∀ i, P.input i = true`) -/

/-- Direct-mapped Word-RAM subroutine for `Dictionary.Dynamic.spec 2 3 2` at `base = 0, space = 2,
w = 2` with **all** registers marked caller-input (`persistentRegCount = 0`).
Register convention on entry: `r0` = op tag (`0` for `query`, `1` for `insert`/`delete`),
`r1` = key `u.1 ∈ {0, 1}`, `r2` = encoded cell word (`v + 1` on `insert`, `0` on `delete`),
`r3` = output scratch, `r4 = 0`. -/
def dynDictZeroPersCode : SubroutineCode .standard 5 0 where
  allocSpan := .seq (.op (.copy 0 1)) (.op (.const 1 2))
  initSetup := .op (.const 0 0)
  code := .branch (.eq 0 4) (.op (.load 3 1)) (.op (.store 1 2))
  frontierReg := 1
  baseReg := 0
  initParams := Fin.elim0
  curReg := 3
  zeroReg := 2
  oneReg := 4
  incCur := .bin .add 3 3 4
  input := fun _ => true
  output := 3

example : persistentRegCount dynDictZeroPersCode = 0 :=
  persistentRegCount_eq_zero_of_all_input fun _ => rfl

def dynDictZeroPersEncode (o : Dictionary.Dynamic.Op 2) (i : Fin 5) : ℕ :=
  match o with
  | .query u => if i.val = 1 then u.1 else 0
  | .insert u v =>
      if i.val = 0 then 1
      else if i.val = 1 then u.1
      else if i.val = 2 then (if v < 3 then v + 1 else 0)
      else 0
  | .delete u =>
      if i.val = 0 then 1
      else if i.val = 1 then u.1
      else 0

def dynDictZeroPersArgMatch (o : Dictionary.Dynamic.Op 2) (regs : Fin 5 → ℕ) : Prop :=
  regs = dynDictZeroPersEncode o

def dynDictZeroPersDecode :
    (o : Dictionary.Dynamic.Op 2) → (Fin 5 → ℕ) → Option o.Result
  | .query _, regs => some (if regs 3 == 0 then none else some (regs 3 - 1))
  | .insert _ _, _ => some ()
  | .delete _, _ => some ()

def dynDictZeroPersRep (s : Dictionary.State 2) (x : Data 5) : Prop :=
  x.Bounded 2 ∧
    Dictionary.ValuesBounded 3 s ∧
    ∀ u : Fin 2, x.mem u.1 = match s u with | none => 0 | some v => v + 1

def dynDictZeroPersCharge (_ : Dictionary.State 2) : Dictionary.Dynamic.Op 2 → ℕ
  | .query _ => 2
  | .insert _ _ => 3
  | .delete _ => 3

def dynDictZeroPersImpl :
    WordRAM.StateTransitionImpl dynDictZeroPersCode (Dictionary.Dynamic.spec 2 3 2) 2 0 Fin.elim0
      (Dictionary.empty 2) :=
  WordRAM.StateTransitionImpl.ofFn
    (space := 2) (spanTime := 2) (setupTime := 1) (initPotential := 0)
    (charge := dynDictZeroPersCharge)
    (rep := dynDictZeroPersRep)
    (potential := fun _ => 0)
    (encode := dynDictZeroPersEncode)
    (argMatch := dynDictZeroPersArgMatch)
    (decode := dynDictZeroPersDecode)
    (bounded := fun h => h.1)
    (arguments_fit := by
      intro s o _ i _
      cases o with
      | query u =>
        have hu := u.2
        (fin_cases i <;> simp [dynDictZeroPersEncode, Fits]); omega
      | insert u v =>
        have hu := u.2
        fin_cases i <;> simp only [dynDictZeroPersEncode, Fits]
        · norm_num
        · simpa using by omega
        · split_ifs <;> omega
        · norm_num
        · norm_num
      | delete u =>
        have hu := u.2
        (fin_cases i <;> simp [dynDictZeroPersEncode, Fits]); omega)
    (encode_matches := fun o _ => by simp [dynDictZeroPersArgMatch, dynDictZeroPersCode])
    (rep_supported := fun _ hmem hbdd ⟨_, hvb, hcells⟩ =>
      ⟨hbdd, hvb, fun u => by
        have hu := u.2
        have hfp : u.1 ∈ (Block.mk 0 2).footprint := by
          simp only [Block.mem_footprint, Block.Owns]
          omega
        exact (hmem u.1 hfp).trans (hcells u)⟩)
    (potential_supported := fun _ _ _ => rfl)
    (clear_nodup := by decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} h1 hfit => by
      change Data.put 2 x 3 (x.regs 3 + x.regs 4) = some (x.set 3 (x.regs 3 + 1))
      change x.regs 4 = 1 at h1
      rw [h1]
      exact Data.put_of_fits hfit)
    (span_exec := fun {_} _ hfr _ => by
      refine ⟨_, (Exec.copy.within).seq (Exec.const (by decide : Fits 2 2)).within,
        rfl, ?_, by simp [dynDictZeroPersCode, Data.set], fun j => Fin.elim0 j⟩
      simpa [dynDictZeroPersCode, Data.set] using hfr)
    (setup_exec := fun {x₁} hbdd₁ _ hfr₁ _ hzero => by
      refine ⟨x₁.set 0 0, (Exec.const (fits_zero 2)).within,
        by simpa [dynDictZeroPersCode, Data.set] using hfr₁,
        ⟨hbdd₁.set (fits_zero 2), Dictionary.valuesBounded_empty 2 3, fun u => ?_⟩,
        Nat.le_refl 0, Modifies.refl _ _⟩
      have hu := u.2
      have hfp : u.1 ∈ (Block.mk 0 2).footprint := by
        simp only [Block.mem_footprint, Block.Owns]
        omega
      simpa [Data.set, Dictionary.empty] using hzero u.1 hfp)
    (step_exec := by
      intro s x o ⟨hbdd, hvb, hcells⟩ hval hmatch
      dsimp only [dynDictZeroPersArgMatch] at hmatch
      cases o with
      | query u =>
        have hc : (Cond.eq (0 : Fin 5) 4).Holds x := by
          simp [Cond.Holds, hmatch, dynDictZeroPersEncode]
        refine ⟨_, 2, Exec.branch_pos hc Exec.load, ?_, ?_, Modifies.refl _ _,
          by dsimp [dynDictZeroPersCharge]; omega⟩
        · have hmu := hcells u
          have hr1 : x.regs 1 = u.1 := by simp [hmatch, dynDictZeroPersEncode]
          cases hsu : s u with
          | none =>
            rw [hsu] at hmu
            simp [dynDictZeroPersDecode, Data.set, hr1, hmu, Dictionary.Dynamic.spec, hsu]
          | some v =>
            rw [hsu] at hmu
            simp [dynDictZeroPersDecode, Data.set, hr1, hmu, Dictionary.Dynamic.spec, hsu]
        · exact ⟨hbdd.set (hbdd.2 _), hvb, fun u' => hcells u'⟩
      | insert u v =>
        have hv3 : v < 3 := hval.2
        have hc : ¬(Cond.eq (0 : Fin 5) 4).Holds x := by
          simp [Cond.Holds, hmatch, dynDictZeroPersEncode]
        have hr1 : x.regs 1 = u.1 := by simp [hmatch, dynDictZeroPersEncode]
        have hr2 : x.regs 2 = v + 1 := by simp [hmatch, dynDictZeroPersEncode, hv3]
        refine ⟨_, 3, Exec.branch_neg hc Exec.store, rfl, ?_, ?_,
          by dsimp [dynDictZeroPersCharge]; omega⟩
        · refine ⟨⟨hbdd.1, fun a => ?_⟩,
            Dictionary.Dynamic.valuesBounded_step_of_valid hvb hval, fun u' => ?_⟩
          · by_cases ha : a = x.regs 1
            · subst ha
              simpa [Data.write] using hbdd.1 2
            · simpa [Data.write, ha] using hbdd.2 a
          · by_cases hu' : u' = u
            · subst hu'
              simp [Data.write, hr1, hr2]
            · have hne : u'.1 ≠ u.1 := Fin.val_ne_of_ne hu'
              dsimp only [Dictionary.Dynamic.spec, StateTransitionSpec.stepFn,
                StateTransitionSpec.ofFn, Dictionary.Dynamic.step]
              rw [Function.update_of_ne hu']
              simpa [Data.write, hr1, hne] using hcells u'
        · intro a ha
          have hu := u.2
          have hau : a ≠ x.regs 1 := by
            rw [hr1]
            rintro rfl
            exact ha (by simp only [Block.mem_footprint, Block.Owns]; omega)
          simp [Data.write, hau]
      | delete u =>
        have hc : ¬(Cond.eq (0 : Fin 5) 4).Holds x := by
          simp [Cond.Holds, hmatch, dynDictZeroPersEncode]
        have hr1 : x.regs 1 = u.1 := by simp [hmatch, dynDictZeroPersEncode]
        have hr2 : x.regs 2 = 0 := by simp [hmatch, dynDictZeroPersEncode]
        refine ⟨_, 3, Exec.branch_neg hc Exec.store, rfl, ?_, ?_,
          by dsimp [dynDictZeroPersCharge]; omega⟩
        · refine ⟨⟨hbdd.1, fun a => ?_⟩,
            Dictionary.Dynamic.valuesBounded_delete hvb u, fun u' => ?_⟩
          · by_cases ha : a = x.regs 1
            · subst ha
              simp [Data.write, hr2]
            · simpa [Data.write, ha] using hbdd.2 a
          · by_cases hu' : u' = u
            · subst hu'
              simp [Data.write, hr1, hr2]
            · have hne : u'.1 ≠ u.1 := Fin.val_ne_of_ne hu'
              dsimp only [Dictionary.Dynamic.spec, StateTransitionSpec.stepFn,
                StateTransitionSpec.ofFn, Dictionary.Dynamic.step]
              rw [Function.update_of_ne hu']
              simpa [Data.write, hr1, hne] using hcells u'
        · intro a ha
          have hu := u.2
          have hau : a ≠ x.regs 1 := by
            rw [hr1]
            rintro rfl
            exact ha (by simp only [Block.mem_footprint, Block.Owns]; omega)
          simp [Data.write, hau])

/-- Simulated deterministic `CellProbe.StateTransitionImpl` with `0` extra cells (`2 + 0 = 2`) and
`0` additive probe overhead (`C_cp.charge s o = dynDictZeroPersImpl.charge s o`). -/
noncomputable def simZeroPersBundle :=
  let h0 := mkInitData0_spec dynDictZeroPersCode Fin.elim0 (fits_zero 2)
  dynDictZeroPersImpl.toCellProbe h0.1 h0.2.1 h0.2.2.1

def sampleDynTrace : List (Dictionary.Dynamic.Op 2) :=
  [.insert 0 2, .insert 1 1, .query 0, .delete 0, .query 0, .query 1]

private theorem sampleDynTrace_run_eq :
    ((Dictionary.Dynamic.spec 2 3 2).run (Dictionary.empty 2) sampleDynTrace).2 =
      [⟨.insert 0 2, ()⟩, ⟨.insert 1 1, ()⟩, ⟨.query 0, some 2⟩,
        ⟨.delete 0, ()⟩, ⟨.query 0, none⟩, ⟨.query 1, some 1⟩] := by
  simp [sampleDynTrace, Dictionary.Dynamic.spec, StateTransitionSpec.run,
    StateTransitionSpec.ofFn, Dictionary.Dynamic.step]

theorem simZeroPers_trace_and_init_spec :
    let P_cp := simZeroPersBundle.1
    let C_cp := simZeroPersBundle.2.1
    (∀ s o, C_cp.charge s o = dynDictZeroPersImpl.charge s o) ∧
      (P_cp.runSeq sampleDynTrace).1 =
        [⟨.insert 0 2, ()⟩, ⟨.insert 1 1, ()⟩, ⟨.query 0, some 2⟩,
          ⟨.delete 0, ()⟩, ⟨.query 0, none⟩, ⟨.query 1, some 1⟩] ∧
      P_cp.seqProbes sampleDynTrace ≤ 15 ∧
      ((dynDictZeroPersImpl.simInit (mkInitData0 dynDictZeroPersCode 0)).probes (fun _ => 0) ≤
          dynDictZeroPersImpl.initTime ∧
        C_cp.rep (Dictionary.empty 2)
          ((dynDictZeroPersImpl.simInit
            (mkInitData0 dynDictZeroPersCode 0)).run (fun _ => 0)).2) := by
  intro P_cp C_cp
  have h0 := mkInitData0_spec dynDictZeroPersCode Fin.elim0 (fits_zero 2)
  have hpers0 : persistentRegCount dynDictZeroPersCode = 0 :=
    persistentRegCount_eq_zero_of_all_input fun _ => rfl
  have hchg : ∀ s o, C_cp.charge s o = dynDictZeroPersImpl.charge s o := by
    intro s o
    simpa [hpers0] using simZeroPersBundle.2.2.2 s o
  have hv : (Dictionary.Dynamic.spec 2 3 2).ValidHistory (Dictionary.empty 2) sampleDynTrace := by
    dsimp [sampleDynTrace, Dictionary.Dynamic.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dictionary.Dynamic.valid, Dictionary.Dynamic.step,
      Dictionary.empty]
    refine ⟨⟨Or.inl (by decide), by decide⟩, ⟨Or.inl (by decide), by decide⟩,
      trivial, trivial, trivial, trivial, trivial⟩
  obtain ⟨htr, _⟩ := C_cp.runSeq_ofFn sampleDynTrace hv
  have hpr_le := C_cp.seqProbes_le_ofFn sampleDynTrace hv
  have hip0 : C_cp.initPotential = 0 := simZeroPersBundle.2.2.1
  have htot :
      (Dictionary.Dynamic.spec 2 3 2).totalCost C_cp.charge (Dictionary.empty 2) sampleDynTrace =
        15 := by
    have hfn : C_cp.charge = dynDictZeroPersImpl.charge := funext fun s => funext (hchg s)
    rw [hfn]
    rfl
  obtain ⟨hinit_run, hinit_pr⟩ := dynDictZeroPersImpl.simInit_spec h0.1 h0.2.1 h0.2.2.1
  have hinit_mem :
      ((dynDictZeroPersImpl.simInit (mkInitData0 dynDictZeroPersCode 0)).run (fun _ => 0)).2 =
        P_cp.init :=
    congrArg Prod.snd hinit_run
  refine ⟨hchg, htr.trans sampleDynTrace_run_eq, ?_, ?_, hinit_mem ▸ C_cp.init_rep⟩
  · dsimp only [P_cp]
    omega
  · simpa [hpers0] using hinit_pr

/-! ### 1B. Relocated simulation with `persistentRegCount P = 2` -/

/-- Relocated Word-RAM subroutine for `Dictionary.Dynamic.spec 2 3 2` at `base = 1, space = 2,
w = 3` keeping two persistent registers (`r0 = base`, `r1 = 1`; `persistentRegCount = 2`).
Entry convention on `r2..r5`: `r2` = op tag (`0` for `query`, `1` for `insert`/`delete`),
`r3` = key `u.1 ∈ {0, 1}`, `r4` = encoded cell word, `r5 = 0`. -/
def dynDictRelocCode : SubroutineCode .standard 6 0 where
  allocSpan := .seq (.op (.copy 0 2)) (.op (.const 2 3))
  initSetup := .op (.const 1 1)
  code := .seq (.op (.bin .add 3 0 3))
    (.branch (.eq 2 5) (.op (.load 4 3)) (.op (.store 3 4)))
  frontierReg := 2
  baseReg := 0
  initParams := Fin.elim0
  curReg := 3
  zeroReg := 5
  oneReg := 1
  incCur := .bin .add 3 3 1
  input i := decide (2 ≤ i.val)
  output := 4

example : persistentRegCount dynDictRelocCode = 2 := by decide

def dynDictRelocEncode (o : Dictionary.Dynamic.Op 2) (i : Fin 6) : ℕ :=
  match o with
  | .query u => if i.val = 3 then u.1 else 0
  | .insert u v =>
      if i.val = 2 then 1
      else if i.val = 3 then u.1
      else if i.val = 4 then (if v < 3 then v + 1 else 0)
      else 0
  | .delete u =>
      if i.val = 2 then 1
      else if i.val = 3 then u.1
      else 0

def dynDictRelocArgMatch (o : Dictionary.Dynamic.Op 2) (regs : Fin 6 → ℕ) : Prop :=
  ∀ i : Fin 6, 2 ≤ i.val → regs i = dynDictRelocEncode o i

def dynDictRelocDecode :
    (o : Dictionary.Dynamic.Op 2) → (Fin 6 → ℕ) → Option o.Result
  | .query _, regs => some (if regs 4 == 0 then none else some (regs 4 - 1))
  | .insert _ _, _ => some ()
  | .delete _, _ => some ()

def dynDictRelocRep (s : Dictionary.State 2) (x : Data 6) : Prop :=
  x.Bounded 3 ∧
    x.regs 0 = 1 ∧
    x.regs 1 = 1 ∧
    Dictionary.ValuesBounded 3 s ∧
    ∀ u : Fin 2, x.mem (1 + u.1) = match s u with | none => 0 | some v => v + 1

def dynDictRelocImpl :
    WordRAM.StateTransitionImpl dynDictRelocCode (Dictionary.Dynamic.spec 2 3 2) 3 1 Fin.elim0
      (Dictionary.empty 2) :=
  WordRAM.StateTransitionImpl.ofFn
    (space := 2) (spanTime := 2) (setupTime := 1) (initPotential := 0)
    (charge := fun _ _ => 4)
    (rep := dynDictRelocRep)
    (potential := fun _ => 0)
    (encode := dynDictRelocEncode)
    (argMatch := dynDictRelocArgMatch)
    (decode := dynDictRelocDecode)
    (bounded := fun h => h.1)
    (arguments_fit := by
      intro s o _ i _
      cases o with
      | query u =>
        have hu := u.2
        (fin_cases i <;> simp [dynDictRelocEncode, Fits]); omega
      | insert u v =>
        have hu := u.2
        fin_cases i <;> simp only [dynDictRelocEncode, Fits]
        · norm_num
        · norm_num
        · norm_num
        · simpa using by omega
        · split_ifs <;> omega
        · norm_num
      | delete u =>
        have hu := u.2
        (fin_cases i <;> simp [dynDictRelocEncode, Fits]); omega)
    (encode_matches := fun o regs i hi => by simp [dynDictRelocCode, hi])
    (rep_supported := fun hreg hmem hbdd ⟨_, hr0, hr1, hvb, hcells⟩ =>
      ⟨hbdd,
        (hreg 0 rfl).trans hr0,
        (hreg 1 rfl).trans hr1,
        hvb,
        fun u => by
          have hu := u.2
          have hfp : 1 + u.1 ∈ (Block.mk 1 2).footprint := by
            simp only [Block.mem_footprint, Block.Owns]
            omega
          exact (hmem (1 + u.1) hfp).trans (hcells u)⟩)
    (potential_supported := fun _ _ _ => rfl)
    (clear_nodup := by decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} h1 hfit => by
      change Data.put 3 x 3 (x.regs 3 + x.regs 1) = some (x.set 3 (x.regs 3 + 1))
      change x.regs 1 = 1 at h1
      rw [h1]
      exact Data.put_of_fits hfit)
    (span_exec := fun {_} _ hfr _ => by
      refine ⟨_, (Exec.copy.within).seq (Exec.const (by decide : Fits 3 3)).within,
        rfl, ?_, by simp [dynDictRelocCode, Data.set], fun j => Fin.elim0 j⟩
      simpa [dynDictRelocCode, Data.set] using hfr)
    (setup_exec := fun {x₁} hbdd₁ hb₁ hfr₁ _ hzero => by
      refine ⟨x₁.set 1 1, (Exec.const (by decide : Fits 3 1)).within,
        by simpa [dynDictRelocCode, Data.set] using hfr₁,
        ⟨hbdd₁.set (by decide : Fits 3 1),
          by simpa [dynDictRelocCode, Data.set] using hb₁,
          by simp [Data.set],
          Dictionary.valuesBounded_empty 2 3,
          fun u => ?_⟩,
        Nat.le_refl 0, Modifies.refl _ _⟩
      have hu := u.2
      have hfp : 1 + u.1 ∈ (Block.mk 1 2).footprint := by
        simp only [Block.mem_footprint, Block.Owns]
        omega
      simpa [Data.set, Dictionary.empty] using hzero (1 + u.1) hfp)
    (step_exec := by
      intro s x o ⟨hbdd, hr0, hr1, hvb, hcells⟩ hval hmatch
      cases o with
      | query u =>
        have hr3 : x.regs 3 = u.1 := by simpa [dynDictRelocEncode] using hmatch 3 (by decide)
        have hr2 : x.regs 2 = 0 := by simpa [dynDictRelocEncode] using hmatch 2 (by decide)
        have hr5 : x.regs 5 = 0 := by simpa [dynDictRelocEncode] using hmatch 5 (by decide)
        have hadd_fit : Fits 3 (BinOp.add.eval (x.regs 0) (x.regs 3)) := by
          have hu := u.2
          simp [BinOp.eval, hr0, hr3, Fits]
          omega
        let x₁ := x.set 3 (BinOp.add.eval (x.regs 0) (x.regs 3))
        have hc : (Cond.eq (2 : Fin 6) 5).Holds x₁ := by
          dsimp only [x₁]
          simp [Cond.Holds, Data.set, hr2, hr5]
        refine ⟨_, 3, (Exec.bin hadd_fit).seq (Exec.branch_pos hc Exec.load), ?_, ?_,
          Modifies.refl _ _, by omega⟩
        · have hmu := hcells u
          cases hsu : s u with
          | none =>
            rw [hsu] at hmu
            dsimp only [x₁]
            simp [dynDictRelocDecode, Data.set, BinOp.eval, hr0, hr3, hmu, hsu]
          | some v =>
            rw [hsu] at hmu
            dsimp only [x₁]
            simp [dynDictRelocDecode, Data.set, BinOp.eval, hr0, hr3, hmu, hsu]
        · exact ⟨(hbdd.set hadd_fit).set (hbdd.2 _), hr0, hr1, hvb, fun u' => hcells u'⟩
      | insert u v =>
        have hv3 : v < 3 := hval.2
        have hr3 : x.regs 3 = u.1 := by simpa [dynDictRelocEncode] using hmatch 3 (by decide)
        have hr2 : x.regs 2 = 1 := by simpa [dynDictRelocEncode] using hmatch 2 (by decide)
        have hr4 : x.regs 4 = v + 1 := by
          simpa [dynDictRelocEncode, hv3] using hmatch 4 (by decide)
        have hr5 : x.regs 5 = 0 := by simpa [dynDictRelocEncode] using hmatch 5 (by decide)
        have hadd_fit : Fits 3 (BinOp.add.eval (x.regs 0) (x.regs 3)) := by
          have hu := u.2
          simp [BinOp.eval, hr0, hr3, Fits]
          omega
        let x₁ := x.set 3 (BinOp.add.eval (x.regs 0) (x.regs 3))
        have haddr : x₁.regs 3 = 1 + u.1 := by
          dsimp only [x₁]
          simp [Data.set, BinOp.eval, hr0, hr3]
        have hc : ¬(Cond.eq (2 : Fin 6) 5).Holds x₁ := by
          dsimp only [x₁]
          simp [Cond.Holds, Data.set, hr2, hr5]
        refine ⟨_, 4, (Exec.bin hadd_fit).seq (Exec.branch_neg hc Exec.store), rfl, ?_, ?_,
          by omega⟩
        · have hbdd₁ : x₁.Bounded 3 := hbdd.set hadd_fit
          refine ⟨⟨hbdd₁.1, fun a => ?_⟩, hr0, hr1,
            Dictionary.Dynamic.valuesBounded_step_of_valid hvb hval, fun u' => ?_⟩
          · change Fits 3 (Function.update x₁.mem (x₁.regs 3) (x₁.regs 4) a)
            by_cases ha : a = x₁.regs 3
            · subst ha
              rw [Function.update_self]
              exact hbdd₁.1 4
            · rw [Function.update_of_ne ha]
              exact hbdd₁.2 a
          · by_cases hu' : u' = u
            · subst hu'
              dsimp only [x₁]
              simp [Data.write, Data.set, BinOp.eval, hr0, hr3, hr4]
            · have hne : 1 + u'.1 ≠ 1 + u.1 := by
                have := Fin.val_ne_of_ne hu'
                omega
              dsimp only [Dictionary.Dynamic.spec, StateTransitionSpec.stepFn,
                StateTransitionSpec.ofFn, Dictionary.Dynamic.step]
              rw [Function.update_of_ne hu']
              change Function.update x₁.mem (x₁.regs 3) (x₁.regs 4) (1 + u'.1) = _
              rw [haddr, Function.update_of_ne hne]
              exact hcells u'
        · intro a ha
          have hu := u.2
          have hau : a ≠ 1 + u.1 := by
            rintro rfl
            exact ha (by simp only [Block.mem_footprint, Block.Owns]; omega)
          change Function.update x₁.mem (x₁.regs 3) (x₁.regs 4) a = x.mem a
          rw [haddr, Function.update_of_ne hau]
          rfl
      | delete u =>
        have hr3 : x.regs 3 = u.1 := by simpa [dynDictRelocEncode] using hmatch 3 (by decide)
        have hr2 : x.regs 2 = 1 := by simpa [dynDictRelocEncode] using hmatch 2 (by decide)
        have hr4 : x.regs 4 = 0 := by simpa [dynDictRelocEncode] using hmatch 4 (by decide)
        have hr5 : x.regs 5 = 0 := by simpa [dynDictRelocEncode] using hmatch 5 (by decide)
        have hadd_fit : Fits 3 (BinOp.add.eval (x.regs 0) (x.regs 3)) := by
          have hu := u.2
          simp [BinOp.eval, hr0, hr3, Fits]
          omega
        let x₁ := x.set 3 (BinOp.add.eval (x.regs 0) (x.regs 3))
        have haddr : x₁.regs 3 = 1 + u.1 := by
          dsimp only [x₁]
          simp [Data.set, BinOp.eval, hr0, hr3]
        have hc : ¬(Cond.eq (2 : Fin 6) 5).Holds x₁ := by
          dsimp only [x₁]
          simp [Cond.Holds, Data.set, hr2, hr5]
        refine ⟨_, 4, (Exec.bin hadd_fit).seq (Exec.branch_neg hc Exec.store), rfl, ?_, ?_,
          by omega⟩
        · have hbdd₁ : x₁.Bounded 3 := hbdd.set hadd_fit
          refine ⟨⟨hbdd₁.1, fun a => ?_⟩, hr0, hr1,
            Dictionary.Dynamic.valuesBounded_delete hvb u, fun u' => ?_⟩
          · change Fits 3 (Function.update x₁.mem (x₁.regs 3) (x₁.regs 4) a)
            by_cases ha : a = x₁.regs 3
            · subst ha
              rw [Function.update_self]
              exact hbdd₁.1 4
            · rw [Function.update_of_ne ha]
              exact hbdd₁.2 a
          · by_cases hu' : u' = u
            · subst hu'
              dsimp only [x₁]
              simp [Data.write, Data.set, BinOp.eval, hr0, hr3, hr4]
            · have hne : 1 + u'.1 ≠ 1 + u.1 := by
                have := Fin.val_ne_of_ne hu'
                omega
              dsimp only [Dictionary.Dynamic.spec, StateTransitionSpec.stepFn,
                StateTransitionSpec.ofFn, Dictionary.Dynamic.step]
              rw [Function.update_of_ne hu']
              change Function.update x₁.mem (x₁.regs 3) (x₁.regs 4) (1 + u'.1) = _
              rw [haddr, Function.update_of_ne hne]
              exact hcells u'
        · intro a ha
          have hu := u.2
          have hau : a ≠ 1 + u.1 := by
            rintro rfl
            exact ha (by simp only [Block.mem_footprint, Block.Owns]; omega)
          change Function.update x₁.mem (x₁.regs 3) (x₁.regs 4) a = x.mem a
          rw [haddr, Function.update_of_ne hau]
          rfl)

/-- Standard `toCellProbe` vs. wide-cell `toCellProbeWide` on `dynDictRelocImpl` (`r_pers = 2`):
`toCellProbe` uses `2 + 2 = 4` cells of width `3` with per-op charge `4 + 4 = 8`, whereas
`toCellProbeWide` uses `2 + 1 = 3` cells of width `wideSubroutineWidth dynDictRelocCode 3 = 6`
with per-op charge `4 + 2 = 6` (`2` fewer probes per operation!), while preserving exact
transcripts across `sampleDynTrace`. -/
theorem simReloc_standard_vs_wide_spec :
    let h0 := mkInitData0_spec dynDictRelocCode Fin.elim0 (by decide : Fits 3 1)
    let stdB := dynDictRelocImpl.toCellProbe h0.1 h0.2.1 h0.2.2.1
    let wideB := dynDictRelocImpl.toCellProbeWide h0.1 h0.2.1 h0.2.2.1
    wideSubroutineWidth dynDictRelocCode 3 = 6 ∧
      (∀ s o, stdB.2.1.charge s o = 8) ∧
      (∀ s o, wideB.2.1.charge s o = 6) ∧
      (wideB.1.runSeq sampleDynTrace).1 =
        [⟨.insert 0 2, ()⟩, ⟨.insert 1 1, ()⟩, ⟨.query 0, some 2⟩,
          ⟨.delete 0, ()⟩, ⟨.query 0, none⟩, ⟨.query 1, some 1⟩] := by
  intro h0 stdB wideB
  have hpers2 : persistentRegCount dynDictRelocCode = 2 := by decide
  have hstd_chg : ∀ s o, stdB.2.1.charge s o = 8 := by
    intro s o
    have h := stdB.2.2.2 s o
    simpa [dynDictRelocImpl, hpers2] using h
  have hwide_chg : ∀ s o, wideB.2.1.charge s o = 6 := by
    intro s o
    have h := wideB.2.2.2 s o
    simpa [dynDictRelocImpl, hpers2] using h
  have hv : (Dictionary.Dynamic.spec 2 3 2).ValidHistory (Dictionary.empty 2) sampleDynTrace := by
    dsimp [sampleDynTrace, Dictionary.Dynamic.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dictionary.Dynamic.valid, Dictionary.Dynamic.step,
      Dictionary.empty]
    refine ⟨⟨Or.inl (by decide), by decide⟩, ⟨Or.inl (by decide), by decide⟩,
      trivial, trivial, trivial, trivial, trivial⟩
  obtain ⟨htr, _⟩ := wideB.2.1.runSeq_ofFn sampleDynTrace hv
  exact ⟨by decide, hstd_chg, hwide_chg, htr.trans sampleDynTrace_run_eq⟩

/-! ### 2. Unconditional contrapositive Word-RAM lower-bound transfer (`Dictionary.Dynamic.spec`) -/

def dynLbOps0 : List (Dictionary.Dynamic.Op 1) := [.insert 0 0, .query 0]
def dynLbOps1 : List (Dictionary.Dynamic.Op 1) := [.insert 0 1, .query 0]

noncomputable def dynLbHardDist : PMF (List (Dictionary.Dynamic.Op 1)) :=
  (Probability.PMF.uniformOfFintype Bool).map fun b => cond b dynLbOps1 dynLbOps0

def dynLbAlphabet : Finset (Dictionary.Dynamic.Op 1) :=
  {.insert 0 0, .insert 0 1, .query 0, .delete 0}

/-- Deterministic cell-probe lower bound at **arbitrary** cell count `cells` and word width `w`:
any step-indexed `IndexedScheme` correctly answering `dynLbOps0` and `dynLbOps1` makes at least `3`
total probes across the pair. -/
theorem three_le_dynDict_seqProbes_pair_of_correct {cells w : ℕ}
    (D_det : IndexedScheme (Dictionary.Dynamic.Op 1) Dictionary.Dynamic.Op.Result cells w)
    (h0 : (D_det.runSeq dynLbOps0).1 =
      ((Dictionary.Dynamic.spec 1 2 1).run (Dictionary.empty 1) dynLbOps0).2)
    (h1 : (D_det.runSeq dynLbOps1).1 =
      ((Dictionary.Dynamic.spec 1 2 1).run (Dictionary.empty 1) dynLbOps1).2) :
    3 ≤ D_det.seqProbes dynLbOps0 + D_det.seqProbes dynLbOps1 := by
  set t0 := D_det.step 0 (.insert 0 0)
  set t1 := D_det.step 0 (.insert 0 1)
  set tq := D_det.step 1 (.query 0)
  set m0 := (t0.run D_det.init).2
  set m1 := (t1.run D_det.init).2
  have hq0 : (tq.run m0).1 = some 0 := by
    have hhead := congrArg List.head? (congrArg List.tail h0)
    simpa [IndexedScheme.runSeq, dynLbOps0, Dictionary.Dynamic.spec, StateTransitionSpec.run,
      StateTransitionSpec.ofFn, Dictionary.Dynamic.step, t0, tq, m0] using hhead
  have hq1 : (tq.run m1).1 = some 1 := by
    have hhead := congrArg List.head? (congrArg List.tail h1)
    simpa [IndexedScheme.runSeq, dynLbOps1, Dictionary.Dynamic.spec, StateTransitionSpec.run,
      StateTransitionSpec.ofFn, Dictionary.Dynamic.step, t1, tq, m1] using hhead
  have htq_pos : ∀ m : Mem cells w, 1 ≤ tq.probes m := by
    intro m
    cases htq : tq with
    | pure ans =>
      rw [htq] at hq0 hq1
      cases hq0.symm.trans hq1
    | liftBind q _ =>
      cases q <;> change 1 ≤ 1 + _ <;> omega
  have hins_pos : 1 ≤ t0.probes D_det.init + t1.probes D_det.init := by
    by_contra hlt
    have hp0 : t0.probes D_det.init = 0 := by omega
    have hp1 : t1.probes D_det.init = 0 := by omega
    have hm0 : m0 = D_det.init := by
      funext i
      refine t0.nextMem_eq_of_notMem_probedCells D_det.init fun hi => ?_
      have hcard := t0.card_probedCells_le_probes D_det.init
      rw [hp0, Nat.le_zero, Finset.card_eq_zero] at hcard
      rw [hcard] at hi
      exact Finset.notMem_empty i hi
    have hm1 : m1 = D_det.init := by
      funext i
      refine t1.nextMem_eq_of_notMem_probedCells D_det.init fun hi => ?_
      have hcard := t1.card_probedCells_le_probes D_det.init
      rw [hp1, Nat.le_zero, Finset.card_eq_zero] at hcard
      rw [hcard] at hi
      exact Finset.notMem_empty i hi
    have heq : (some 0 : Option ℕ) = some 1 := by rw [← hq0, ← hq1, hm0, hm1]
    cases heq
  have hpr0 : D_det.seqProbes dynLbOps0 = t0.probes D_det.init + tq.probes m0 := by
    simp [IndexedScheme.seqProbes, dynLbOps0, t0, tq, m0]
  have hpr1 : D_det.seqProbes dynLbOps1 = t1.probes D_det.init + tq.probes m1 := by
    simp [IndexedScheme.seqProbes, dynLbOps1, t1, tq, m1]
  have := htq_pos m0
  have := htq_pos m1
  omega

private theorem three_halves_le_expected_dynLb {cells w : ℕ}
    (D_det : IndexedScheme (Dictionary.Dynamic.Op 1) Dictionary.Dynamic.Op.Result cells w)
    (hD : ∀ ops ∈ ({dynLbOps0, dynLbOps1} : Set (List (Dictionary.Dynamic.Op 1))),
      (D_det.runSeq ops).1 = ((Dictionary.Dynamic.spec 1 2 1).run (Dictionary.empty 1) ops).2) :
    (3 : ℝ≥0∞) / 2 ≤ ∑' ops, dynLbHardDist ops * (D_det.seqProbes ops : ℝ≥0∞) := by
  have hpair := three_le_dynDict_seqProbes_pair_of_correct D_det (hD dynLbOps0 (Or.inl rfl))
    (hD dynLbOps1 (Or.inr rfl))
  rw [dynLbHardDist, Probability.PMF.tsum_map_mul, tsum_fintype]
  have hbool : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hbool, Finset.sum_pair (by decide)]
  simp only [Bool.cond_false, Bool.cond_true, Probability.PMF.uniformOfFintype_apply,
    Fintype.card_bool]
  rw [← mul_add, ← Nat.cast_add]
  have hcast : (3 : ℝ≥0∞) ≤
      ((D_det.seqProbes dynLbOps0 + D_det.seqProbes dynLbOps1 : ℕ) : ℝ≥0∞) :=
    Nat.cast_le.mpr hpair
  calc
    (3 : ℝ≥0∞) / 2 = (2 : ℝ≥0∞)⁻¹ * 3 := by rw [div_eq_mul_inv, mul_comm]
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ((D_det.seqProbes dynLbOps0 + D_det.seqProbes dynLbOps1 : ℕ) : ℝ≥0∞) :=
        mul_le_mul_right hcast _

private theorem dynLb_valid0 :
    (Dictionary.Dynamic.spec 1 2 1).ValidHistory (Dictionary.empty 1) dynLbOps0 := by
  dsimp [dynLbOps0, Dictionary.Dynamic.spec, StateTransitionSpec.ValidHistory,
    StateTransitionSpec.ofFn, Dictionary.Dynamic.valid, Dictionary.Dynamic.step]
  exact ⟨⟨Or.inl (by decide), by decide⟩, trivial, trivial⟩

private theorem dynLb_valid1 :
    (Dictionary.Dynamic.spec 1 2 1).ValidHistory (Dictionary.empty 1) dynLbOps1 := by
  dsimp [dynLbOps1, Dictionary.Dynamic.spec, StateTransitionSpec.ValidHistory,
    StateTransitionSpec.ofFn, Dictionary.Dynamic.valid, Dictionary.Dynamic.step]
  exact ⟨⟨Or.inl (by decide), by decide⟩, trivial, trivial⟩

private theorem dynLb_correctSeqs :
    ∀ ops ∈ ({dynLbOps0, dynLbOps1} : Set (List (Dictionary.Dynamic.Op 1))),
      (Dictionary.Dynamic.spec 1 2 1).ValidHistory (Dictionary.empty 1) ops ∧
        ops.length ≤ 2 ∧ ∀ o ∈ ops, o ∈ dynLbAlphabet := by
  rintro ops (rfl | rfl)
  · exact ⟨dynLb_valid0, by decide, by simp [dynLbOps0, dynLbAlphabet]⟩
  · exact ⟨dynLb_valid1, by decide, by simp [dynLbOps1, dynLbAlphabet]⟩

private theorem dynLb_hardDist_valid :
    ∀ ops ∈ dynLbHardDist.support,
      (Dictionary.Dynamic.spec 1 2 1).ValidHistory (Dictionary.empty 1) ops ∧
        ops.length ≤ 2 ∧ ∀ o ∈ ops, o ∈ dynLbAlphabet := by
  intro ops hops
  rw [dynLbHardDist, PMF.mem_support_map_iff] at hops
  obtain ⟨b, _, rfl⟩ := hops
  cases b
  · exact ⟨dynLb_valid0, by decide, by simp [dynLbOps0, dynLbAlphabet]⟩
  · exact ⟨dynLb_valid1, by decide, by simp [dynLbOps1, dynLbAlphabet]⟩

/-- **End-to-end unconditional Word-RAM lower-bound transfer (`0` `η`-loss, non-`Fintype`
`Dictionary.Dynamic.Op 1`):**
Every zero-error `WordRAM.Randomized.StateTransitionImpl` of `Dictionary.Dynamic.spec 1 2 1` over
**any** `Basis`, register count `r_ds`, word width `w`, and space `C.space` satisfies the `3 / 2`
certified expected instruction lower bound. -/
theorem three_halves_le_any_wordRAM_randomized_impl
    {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {params : Fin k_init → ℕ}
    (C : WordRAM.Randomized.StateTransitionImpl P (Dictionary.Dynamic.spec 1 2 1) w base params
      (Dictionary.empty 1))
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    (3 : ℝ≥0∞) / 2 ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, dynLbHardDist ops *
        (((Dictionary.Dynamic.spec 1 2 1).totalCost C.charge (Dictionary.empty 1) ops : ℝ≥0∞) +
          ((2 * persistentRegCount P : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) :=
  wordRAM_lower_bound_of_det_cellProbe_lower_bound C hd₀ hfr hpar le_rfl dynLbAlphabet 2
    {dynLbOps0, dynLbOps1} dynLb_correctSeqs dynLbHardDist dynLb_hardDist_valid
    fun D_det hD => three_halves_le_expected_dynLb D_det hD

/-- When all registers are caller-overwritable (`∀ i, P.input i = true`), **both** the register
spill overhead and `η` vanish completely: `(3 : ℝ≥0∞) / 2 ≤ C.initPotential + E[totalCost charge]`.
-/
theorem three_halves_le_any_zeroPers_wordRAM_randomized_impl
    {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init} (hall : ∀ i, P.input i = true)
    {params : Fin k_init → ℕ}
    (C : WordRAM.Randomized.StateTransitionImpl P (Dictionary.Dynamic.spec 1 2 1) w base params
      (Dictionary.empty 1))
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    (3 : ℝ≥0∞) / 2 ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, dynLbHardDist ops *
        ((Dictionary.Dynamic.spec 1 2 1).totalCost C.charge (Dictionary.empty 1) ops : ℝ≥0∞) := by
  have hraw := three_halves_le_any_wordRAM_randomized_impl C hd₀ hfr hpar
  simpa [persistentRegCount_eq_zero_of_all_input hall] using hraw

/-- **Wide-cell unconditional Word-RAM lower-bound transfer
(`wordRAM_lower_bound_of_det_cellProbe_wide`):**
Even when `P` retains arbitrarily many persistent registers `r_ds`, packing them into one wide cell
of width `wideSubroutineWidth P w` transfers the lower bound with additive overhead at most `2` per
operation (instead of `2 * r_ds`) and `0` `η`-loss. -/
theorem three_halves_le_any_wordRAM_randomized_impl_wide
    {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {params : Fin k_init → ℕ}
    (C : WordRAM.Randomized.StateTransitionImpl P (Dictionary.Dynamic.spec 1 2 1) w base params
      (Dictionary.empty 1))
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    (3 : ℝ≥0∞) / 2 ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, dynLbHardDist ops *
        (((Dictionary.Dynamic.spec 1 2 1).totalCost C.charge (Dictionary.empty 1) ops : ℝ≥0∞) +
          (2 : ℝ≥0∞) * (ops.length : ℝ≥0∞)) :=
  wordRAM_lower_bound_of_det_cellProbe_wide C hd₀ hfr hpar le_rfl dynLbAlphabet 2
    {dynLbOps0, dynLbOps1} dynLb_correctSeqs dynLbHardDist dynLb_hardDist_valid
    fun D_det hD => three_halves_le_expected_dynLb D_det hD

/-- Unconditional lower-bound transfer to zero-error `WordRAM.Randomized.ObliviousSequenceImpl`s. -/
theorem three_halves_le_any_oblivious_wordRAM_impl
    {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {params : Fin k_init → ℕ}
    (C : WordRAM.Randomized.ObliviousSequenceImpl P
      ((Dictionary.Dynamic.spec 1 2 1).toObliviousSequenceSpec (Dictionary.empty 1)) w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    (3 : ℝ≥0∞) / 2 ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, dynLbHardDist ops *
        (((ops.map C.charge).sum : ℝ≥0∞) +
          ((2 * persistentRegCount P : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) :=
  oblivious_wordRAM_lower_bound_of_det_cellProbe C hd₀ hfr hpar le_rfl dynLbAlphabet 2
    {dynLbOps0, dynLbOps1} dynLb_correctSeqs dynLbHardDist dynLb_hardDist_valid
    fun D_det hD => three_halves_le_expected_dynLb D_det hD

/-! ### 3. Explicit 1-instruction `[Instr.halt retReg]` non-vacuity sanity test -/

private theorem execProgramDist_halt_eq_pure {B : Basis} {r w : ℕ} (retReg : Fin r) (x : Data r)
    {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞}
    (h : ExecProgramDist w ([Instr.halt retReg] : Program B r) x μ T) :
    μ = PMF.pure (x.regs retReg, x) := by
  have h1 : evalRand w ([Instr.halt retReg] : Program B r) 1 ⟨0, x⟩ =
      PMF.pure (.halted (x.regs retReg) x) := by
    simp only [evalRand, runRand_succ, runRand_zero, bind_pure]
    rw [stepRand_halt (s := ⟨0, x⟩) (i := retReg) rfl, ProbComp.eval_pure]
  have h2 : ∀ t ≥ 1, evalRand w ([Instr.halt retReg] : Program B r) t ⟨0, x⟩ =
      PMF.pure (.halted (x.regs retReg) x) := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    induction d with
    | zero => exact h1
    | succ d ih =>
      rw [← Nat.add_assoc, evalRand, runRand_add w [Instr.halt retReg] (1 + d) 1,
        ProbComp.eval_bind]
      change (evalRand w [Instr.halt retReg] (1 + d) ⟨0, x⟩).bind _ = _
      rw [ih (Nat.le_add_right 1 d), PMF.pure_bind]
      simp [runRand_succ, runRand_zero, stepRand_halted]
  ext vy
  rcases vy with ⟨v, y⟩
  rw [← h.haltedLim_eq (v, y)]
  dsimp only [haltedLim]
  by_cases hvy : (v, y) = (x.regs retReg, x)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hvy.symm
    rw [PMF.pure_apply_self]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun t => ?_
      by_cases ht : 1 ≤ t
      · rw [h2 t ht, PMF.pure_apply_self]
      · have ht0 : t = 0 := by omega
        subst ht0
        simp [evalRand, runRand_zero]
    · calc (1 : ℝ≥0∞)
        _ = (evalRand w ([Instr.halt retReg] : Program B r) 1 ⟨0, x⟩)
              (.halted (x.regs retReg) x) := by
            rw [h1, PMF.pure_apply_self]
        _ ≤ ⨆ t, (evalRand w ([Instr.halt retReg] : Program B r) t ⟨0, x⟩)
              (.halted (x.regs retReg) x) :=
            le_iSup (fun t => (evalRand w ([Instr.halt retReg] : Program B r) t ⟨0, x⟩)
              (.halted (x.regs retReg) x)) 1
  · rw [PMF.pure_apply_of_ne _ _ hvy]
    refine le_antisymm (iSup_le fun t => ?_) zero_le
    by_cases ht : 1 ≤ t
    · rw [h2 t ht]
      have hne_cfg : RandCfg.halted v y ≠ RandCfg.halted (x.regs retReg) x := by
        intro heq
        cases heq
        exact hvy rfl
      exact le_of_eq (PMF.pure_apply_of_ne _ _ hne_cfg)
    · have ht0 : t = 0 := by omega
      subst ht0
      simp [evalRand, runRand_zero]

private theorem execFlatProgramOps_cons_inv
    {B : Basis} {r w base space : ℕ} {D : StateTransitionSpec.{0, 0, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type} {p_op : Program B r} {input : Fin r → Bool}
    {encode : D.Op → Fin r → ℕ}
    {decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o)}
    {s : D.State} {o : D.Op} {ops : List D.Op}
    {ν ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞}
    (hex : ExecFlatProgramOps D Latent w base space p_op input encode decode s (o :: ops)
      ν ν_final T_ops) :
    ∃ (μ_step : Latent × Data r → PMF (Latent × ℕ × Data r))
      (T_step : Latent × Data r → ℝ≥0∞) (T_rest : ℝ≥0∞),
      (∀ p ∈ ν.support,
        (∀ i, input i = true → Fits w (encode o i)) ∧
        ExecProgramDist w p_op (prepareFlatRegs input encode o p.2)
          ((μ_step p).map Prod.snd) (T_step p + 1) ∧
        ∀ q ∈ (μ_step p).support,
          q.2.2.Bounded w ∧
          decode o q.2.1 q.2.2.regs = some (D.stepFn s o).2 ∧
          Modifies (Block.mk base space).footprint p.2.mem q.2.2.mem) ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode (D.stepFn s o).1 ops
        (ν.bind fun p => (μ_step p).map fun q => (q.1, q.2.2)) ν_final T_rest := by
  generalize hops' : (o :: ops) = ops_idx at hex
  induction hex with
  | nil => cases hops'
  | cons hstep hrem _ =>
    cases hops'
    exact ⟨_, _, _, hstep, hrem⟩

/-- **Non-vacuity sanity check (`[Instr.halt retReg]`):**
A trivial `1`-instruction flat program `[Instr.halt retReg]` (for **any** `Basis`, register count
`r`, word width `w`, footprint, input mask `input`, encoder, decoder, and initial state law `ν₀`)
**cannot** satisfy `ExecFlatProgramOps` on both `dynLbOps0 = [.insert 0 0, .query 0]` and
`dynLbOps1 = [.insert 0 1, .query 0]` for `Dictionary.Dynamic.spec 1 2 1`, confirming that the
hypotheses of `flat_wordRAM_lower_bound_of_det_cellProbe` and
`wordRAM_lower_bound_of_det_cellProbe_lower_bound` refute probe-free `1`-step programs rather than
holding vacuously. -/
theorem not_execFlatProgramOps_halt_pair
    {B : Basis} {r w base space : ℕ} {Latent : Type}
    (retReg : Fin r) (input : Fin r → Bool)
    (encode : Dictionary.Dynamic.Op 1 → Fin r → ℕ)
    (decode : (o : Dictionary.Dynamic.Op 1) → ℕ → (Fin r → ℕ) → Option o.Result)
    (ν₀ ν_f0 ν_f1 : PMF (Latent × Data r)) (T0 T1 : ℝ≥0∞)
    (hex0 : ExecFlatProgramOps (Dictionary.Dynamic.spec 1 2 1) Latent w base space
      ([Instr.halt retReg] : Program B r) input encode decode (Dictionary.empty 1)
      dynLbOps0 ν₀ ν_f0 T0)
    (hex1 : ExecFlatProgramOps (Dictionary.Dynamic.spec 1 2 1) Latent w base space
      ([Instr.halt retReg] : Program B r) input encode decode (Dictionary.empty 1)
      dynLbOps1 ν₀ ν_f1 T1) :
    False := by
  obtain ⟨p₀, hp₀⟩ := ν₀.support_nonempty
  dsimp only [dynLbOps0] at hex0
  dsimp only [dynLbOps1] at hex1
  obtain ⟨μ_ins0, _, _, hins0, hrem0⟩ := execFlatProgramOps_cons_inv hex0
  obtain ⟨_, hpdist_i0, _⟩ := hins0 p₀ hp₀
  have hmap_i0 := execProgramDist_halt_eq_pure retReg _ hpdist_i0
  obtain ⟨q0, hq0⟩ := (μ_ins0 p₀).support_nonempty
  have hq0_pure : q0.2 ∈ (PMF.pure ((prepareFlatRegs input encode (.insert 0 0) p₀.2).regs retReg,
      prepareFlatRegs input encode (.insert 0 0) p₀.2) : PMF (ℕ × Data r)).support := by
    rw [← hmap_i0, PMF.mem_support_map_iff]
    exact ⟨q0, hq0, rfl⟩
  have hq0_data : q0.2.2 = prepareFlatRegs input encode (.insert 0 0) p₀.2 :=
    congrArg Prod.snd ((PMF.mem_support_pure_iff _ _).mp hq0_pure)
  have hmem_b0 : (q0.1, q0.2.2) ∈
      (ν₀.bind fun p => (μ_ins0 p).map fun q => (q.1, q.2.2)).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨p₀, hp₀, (PMF.mem_support_map_iff _ _ _).mpr ⟨q0, hq0, rfl⟩⟩
  obtain ⟨μ_qry0, _, _, hqry0, _⟩ := execFlatProgramOps_cons_inv hrem0
  obtain ⟨_, hpdist_q0, hdec_q0⟩ := hqry0 (q0.1, q0.2.2) hmem_b0
  have hmap_q0 := execProgramDist_halt_eq_pure retReg _ hpdist_q0
  obtain ⟨r0, hr0⟩ := (μ_qry0 (q0.1, q0.2.2)).support_nonempty
  have hr0_pure : r0.2 ∈
      (PMF.pure ((prepareFlatRegs input encode (.query 0) q0.2.2).regs retReg,
        prepareFlatRegs input encode (.query 0) q0.2.2) : PMF (ℕ × Data r)).support := by
    rw [← hmap_q0, PMF.mem_support_map_iff]
    exact ⟨r0, hr0, rfl⟩
  have hr0_eq := (PMF.mem_support_pure_iff _ _).mp hr0_pure
  have hans0 :
      decode (.query 0) ((prepareFlatRegs input encode (.query 0) q0.2.2).regs retReg)
        (prepareFlatRegs input encode (.query 0) q0.2.2).regs = some (some 0) := by
    have hd := (hdec_q0 r0 hr0).2.1
    rw [congrArg Prod.fst hr0_eq, congrArg Prod.snd hr0_eq] at hd
    simpa [Dictionary.Dynamic.spec, StateTransitionSpec.stepFn, Dictionary.Dynamic.step,
      Dictionary.empty] using hd
  obtain ⟨μ_ins1, _, _, hins1, hrem1⟩ := execFlatProgramOps_cons_inv hex1
  obtain ⟨_, hpdist_i1, _⟩ := hins1 p₀ hp₀
  have hmap_i1 := execProgramDist_halt_eq_pure retReg _ hpdist_i1
  obtain ⟨q1, hq1⟩ := (μ_ins1 p₀).support_nonempty
  have hq1_pure : q1.2 ∈
      (PMF.pure ((prepareFlatRegs input encode (.insert 0 1) p₀.2).regs retReg,
        prepareFlatRegs input encode (.insert 0 1) p₀.2) : PMF (ℕ × Data r)).support := by
    rw [← hmap_i1, PMF.mem_support_map_iff]
    exact ⟨q1, hq1, rfl⟩
  have hq1_data : q1.2.2 = prepareFlatRegs input encode (.insert 0 1) p₀.2 :=
    congrArg Prod.snd ((PMF.mem_support_pure_iff _ _).mp hq1_pure)
  have hmem_b1 : (q1.1, q1.2.2) ∈
      (ν₀.bind fun p => (μ_ins1 p).map fun q => (q.1, q.2.2)).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨p₀, hp₀, (PMF.mem_support_map_iff _ _ _).mpr ⟨q1, hq1, rfl⟩⟩
  obtain ⟨μ_qry1, _, _, hqry1, _⟩ := execFlatProgramOps_cons_inv hrem1
  obtain ⟨_, hpdist_q1, hdec_q1⟩ := hqry1 (q1.1, q1.2.2) hmem_b1
  have hmap_q1 := execProgramDist_halt_eq_pure retReg _ hpdist_q1
  obtain ⟨r1, hr1⟩ := (μ_qry1 (q1.1, q1.2.2)).support_nonempty
  have hr1_pure : r1.2 ∈
      (PMF.pure ((prepareFlatRegs input encode (.query 0) q1.2.2).regs retReg,
        prepareFlatRegs input encode (.query 0) q1.2.2) : PMF (ℕ × Data r)).support := by
    rw [← hmap_q1, PMF.mem_support_map_iff]
    exact ⟨r1, hr1, rfl⟩
  have hr1_eq := (PMF.mem_support_pure_iff _ _).mp hr1_pure
  have hans1 :
      decode (.query 0) ((prepareFlatRegs input encode (.query 0) q1.2.2).regs retReg)
        (prepareFlatRegs input encode (.query 0) q1.2.2).regs = some (some 1) := by
    have hd := (hdec_q1 r1 hr1).2.1
    rw [congrArg Prod.fst hr1_eq, congrArg Prod.snd hr1_eq] at hd
    simpa [Dictionary.Dynamic.spec, StateTransitionSpec.stepFn, Dictionary.Dynamic.step,
      Dictionary.empty] using hd
  have hregs_eq :
      (prepareFlatRegs input encode (.query 0) q0.2.2).regs =
        (prepareFlatRegs input encode (.query 0) q1.2.2).regs := by
    funext i
    rw [hq0_data, hq1_data]
    by_cases hi : input i = true <;> simp [prepareFlatRegs, hi]
  rw [hregs_eq] at hans0
  cases hans0.symm.trans hans1

end CslibFrontierTests.CellProbeOfWordRAM
