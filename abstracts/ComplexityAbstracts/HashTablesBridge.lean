/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.HashFamiliesBridge
import Complexity.DataStructure.Dictionary.WordRAM.ChainedHash
import Complexity.DataStructure.Dictionary.WordRAM.CuckooHashing
import Complexity.DataStructure.Dictionary.WordRAM.LinearProbing
import Complexity.DataStructure.Dictionary.WordRAM.UniformProbing

/-!
# Bridge for the Word-RAM Hash Tables Formal Abstract

`HashTablesAbstract.lean` states the self-contained formal abstract for the four Word-RAM
dictionary hash tables in Complexitylib specialized to the polynomial key-universe exponent
`c_exp = 4` (`U ≤ max n_max 4 ^ 4`):
1. Chained hashing with multiply-shift (`ChainedHash.lean`);
2. Linear probing with `5`-wise independent polynomial hashing (`LinearProbing.lean`);
3. Uniform probing via odd-stride double hashing (`UniformProbing.lean`);
4. Cuckoo hashing (`CuckooHashing.lean`).

This bridge connects the self-contained dictionary specification, distributional execution
relations (`ExecProgramDist`, `ExecDictOps`), resource functions, and headline theorems in
`HashTablesAbstract.lean` to the library definitions and theorems over `Cslib.WordRAM.Basis.exact`.
-/

namespace ComplexityAbstracts.HashTablesBridge

open scoped ENNReal BigOperators
open Cslib
open Cslib.WordRAM
open Cslib.WordRAM.Randomized
open Cslib.DataStructure Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM Cslib.DataStructure.WordRAM
open Cslib.DataStructure.WordRAM.Randomized
open ComplexityAbstracts.RandomizedWordRAMBridge
open ComplexityAbstracts.HashFamiliesBridge.HFPresentation (WordBounded UnchangedOutside)

/-! ## Part 1: Polymorphic Dictionary Presentation and Execution Transfer -/

/-- Polymorphic signature of the self-contained dictionary and multi-operation execution types in
`HashTablesAbstract.lean`. -/
structure DictPresentation (S : Presentation) where
  DictOp : ℕ → Type
  get {U : ℕ} : Fin U → DictOp U
  insert {U : ℕ} : Fin U → ℕ → DictOp U
  dictOp_induction {U : ℕ} {motive : DictOp U → Prop} :
    (∀ u, motive (get u)) → (∀ u v, motive (insert u v)) → ∀ o, motive o
  stepDict {U : ℕ} : (Fin U → Option ℕ) → DictOp U → (Fin U → Option ℕ)
  validDictOp {U : ℕ} : ℕ → ℕ → (Fin U → Option ℕ) → DictOp U → Prop
  ValidDictHistory {U : ℕ} : ℕ → ℕ → (Fin U → Option ℕ) → List (DictOp U) → Prop
  RegMem : ℕ → Type
  regMem {r : ℕ} : (Fin r → ℕ) → (ℕ → ℕ) → RegMem r
  rmReg {r : ℕ} : RegMem r → Fin r → ℕ
  rmMem {r : ℕ} : RegMem r → ℕ → ℕ
  CoupledState : Type → ℕ → Type
  coupledState {Seed : Type} {r : ℕ} : Seed → (Fin r → ℕ) → (ℕ → ℕ) → CoupledState Seed r
  csSeed {Seed : Type} {r : ℕ} : CoupledState Seed r → Seed
  csReg {Seed : Type} {r : ℕ} : CoupledState Seed r → Fin r → ℕ
  csMem {Seed : Type} {r : ℕ} : CoupledState Seed r → ℕ → ℕ
  prepareDictRegs {r U : ℕ} :
    Bool → Fin r → Fin r → Fin r → Fin r → DictOp U → (Fin r → ℕ) → Fin r → ℕ
  OpOutputCorrect {r U : ℕ} : Fin r → (Fin U → Option ℕ) → DictOp U → (Fin r → ℕ) → Prop
  ExecDictOps {Seed : Type} {r U : ℕ} :
    ℕ → List (S.Instr r) → Bool → Fin r → Fin r → Fin r → Fin r → Fin r → ℕ → ℕ →
    (Fin U → Option ℕ) → List (DictOp U) →
    PMF (CoupledState Seed r) → PMF (CoupledState Seed r) → ℝ≥0∞ → Prop

namespace DictPresentation

variable {S : Presentation} (P : DictPresentation S)

/-- Empty dictionary state `fun _ => none`. -/
def emptyDict (U : ℕ) : Fin U → Option ℕ :=
  fun _ => none

/-- No reachable configuration of program `p` from state `s` at word width `w` faults at any time
horizon `T`. -/
def RandFaultFree {r : ℕ} (w : ℕ) (p : List (S.Instr r)) (s : S.State r) : Prop :=
  ∀ T : ℕ, S.evalRand w p T s S.faulted = 0

/-- Project a coupled state to its register bank and memory snapshot. -/
def toRegMem {Seed : Type} {r : ℕ} (p : P.CoupledState Seed r) : P.RegMem r :=
  P.regMem (P.csReg p) (P.csMem p)

/-- Distributional execution of a compiled Word-RAM program `p` from `(0, reg, mem)`. -/
def ExecProgramDist {r : ℕ} (w : ℕ) (p : List (S.Instr r)) (outReg : Fin r)
    (reg : Fin r → ℕ) (mem : ℕ → ℕ) (μ : PMF (P.RegMem r)) (T : ℝ≥0∞) : Prop :=
  let s := S.state 0 reg mem
  RandFaultFree w p s ∧
  S.expectedTime w p s ≤ T + 1 ∧
  ∀ q : P.RegMem r,
    μ q ≤ ⨆ T_hor : ℕ,
      S.evalRand w p T_hor s (S.halted (P.rmReg q outReg) (P.rmReg q) (P.rmMem q))

/-- Translate a library dictionary operation `Dictionary.Op U` to `P.DictOp U`. -/
def dictOpOf {U : ℕ} : Dictionary.Op U → P.DictOp U
  | .get u => P.get u
  | .insert u v => P.insert u v

/-- Translate a library `Data r` state to `P.RegMem r`. -/
def regMemOf {r : ℕ} (d : Data r) : P.RegMem r :=
  P.regMem d.regs d.mem

/-- Translate `P.RegMem r` back to `Data r`. -/
def dataOfRegMem {r : ℕ} (q : P.RegMem r) : Data r :=
  ⟨P.rmReg q, P.rmMem q⟩

/-- Translate a library `(Seed × Data r)` pair to `P.CoupledState Seed r`. -/
def coupledStateOf {Seed : Type} {r : ℕ} (p : Seed × Data r) : P.CoupledState Seed r :=
  P.coupledState p.1 p.2.regs p.2.mem

/-- Translate `P.CoupledState Seed r` back to `Seed × Data r`. -/
def pairOfCoupledState {Seed : Type} {r : ℕ} (q : P.CoupledState Seed r) : Seed × Data r :=
  (P.csSeed q, ⟨P.csReg q, P.csMem q⟩)

end DictPresentation

/-- Equational specification for a dictionary presentation `P : DictPresentation S`. -/
structure DictLaws (S : Presentation) (P : DictPresentation S) : Prop where
  stepDict_get : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U),
    P.stepDict s (P.get u) = s
  stepDict_insert : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U) (v : ℕ),
    P.stepDict s (P.insert u v) = Function.update s u (some v)
  validDictOp_get : ∀ {U : ℕ} (V n_max : ℕ) (s : Fin U → Option ℕ) (u : Fin U),
    P.validDictOp V n_max s (P.get u) ↔ True
  validDictOp_insert : ∀ {U : ℕ} (V n_max : ℕ) (s : Fin U → Option ℕ) (u : Fin U) (v : ℕ),
    P.validDictOp V n_max s (P.insert u v) ↔
      ((Finset.univ.filter fun u' => (s u').isSome).card < n_max ∨ (s u).isSome) ∧ v < V
  validDictHistory_nil : ∀ {U : ℕ} (V n_max : ℕ) (s : Fin U → Option ℕ),
    P.ValidDictHistory V n_max s [] ↔ True
  validDictHistory_cons : ∀ {U : ℕ} (V n_max : ℕ) (s : Fin U → Option ℕ)
    (o : P.DictOp U) (os : List (P.DictOp U)),
    P.ValidDictHistory V n_max s (o :: os) ↔
      P.validDictOp V n_max s o ∧ P.ValidDictHistory V n_max (P.stepDict s o) os
  rmReg_mk : ∀ {r : ℕ} (reg : Fin r → ℕ) (mem : ℕ → ℕ),
    P.rmReg (P.regMem reg mem) = reg
  rmMem_mk : ∀ {r : ℕ} (reg : Fin r → ℕ) (mem : ℕ → ℕ),
    P.rmMem (P.regMem reg mem) = mem
  regMem_eta : ∀ {r : ℕ} (q : P.RegMem r),
    P.regMem (P.rmReg q) (P.rmMem q) = q
  csSeed_mk : ∀ {Seed : Type} {r : ℕ} (θ : Seed) (reg : Fin r → ℕ) (mem : ℕ → ℕ),
    P.csSeed (P.coupledState θ reg mem) = θ
  csReg_mk : ∀ {Seed : Type} {r : ℕ} (θ : Seed) (reg : Fin r → ℕ) (mem : ℕ → ℕ),
    P.csReg (P.coupledState θ reg mem) = reg
  csMem_mk : ∀ {Seed : Type} {r : ℕ} (θ : Seed) (reg : Fin r → ℕ) (mem : ℕ → ℕ),
    P.csMem (P.coupledState θ reg mem) = mem
  coupledState_eta : ∀ {Seed : Type} {r : ℕ} (p : P.CoupledState Seed r),
    P.coupledState (P.csSeed p) (P.csReg p) (P.csMem p) = p
  prepareDictRegs_get : ∀ {r U : ℕ} (clearScratch : Bool) (baseReg tagReg keyReg valReg : Fin r)
    (u : Fin U) (reg : Fin r → ℕ) (i : Fin r),
    P.prepareDictRegs clearScratch baseReg tagReg keyReg valReg (P.get u) reg i =
      if i = tagReg then 0
      else if i = keyReg then u.val
      else if i = valReg then 0
      else if clearScratch && decide (i ≠ baseReg) then 0
      else reg i
  prepareDictRegs_insert : ∀ {r U : ℕ} (clearScratch : Bool) (baseReg tagReg keyReg valReg : Fin r)
    (u : Fin U) (v : ℕ) (reg : Fin r → ℕ) (i : Fin r),
    P.prepareDictRegs clearScratch baseReg tagReg keyReg valReg (P.insert u v) reg i =
      if i = tagReg then 1
      else if i = keyReg then u.val
      else if i = valReg then v
      else if clearScratch && decide (i ≠ baseReg) then 0
      else reg i
  opOutputCorrect_get : ∀ {r U : ℕ} (outReg : Fin r) (s : Fin U → Option ℕ)
    (u : Fin U) (reg : Fin r → ℕ),
    P.OpOutputCorrect outReg s (P.get u) reg ↔
      (if reg outReg = 0 then none else some (reg outReg - 1)) = s u
  opOutputCorrect_insert : ∀ {r U : ℕ} (outReg : Fin r) (s : Fin U → Option ℕ)
    (u : Fin U) (v : ℕ) (reg : Fin r → ℕ),
    P.OpOutputCorrect outReg s (P.insert u v) reg ↔ True
  execDictOps_nil : ∀ {Seed : Type} {r U : ℕ} (w : ℕ) (p_op : List (S.Instr r))
    (clearScratch : Bool) (baseReg tagReg keyReg valReg outReg : Fin r) (base sp : ℕ)
    (s : Fin U → Option ℕ) (μ : PMF (P.CoupledState Seed r)),
    P.ExecDictOps w p_op clearScratch baseReg tagReg keyReg valReg outReg base sp s [] μ μ 0
  execDictOps_cons : ∀ {Seed : Type} {r U : ℕ} {w : ℕ} {p_op : List (S.Instr r)}
    {clearScratch : Bool} {baseReg tagReg keyReg valReg outReg : Fin r} {base sp : ℕ}
    {s : Fin U → Option ℕ} {o : P.DictOp U} {ops : List (P.DictOp U)}
    {μ μ_final : PMF (P.CoupledState Seed r)} {T_rest : ℝ≥0∞}
    (T_step : P.CoupledState Seed r → ℝ≥0∞)
    (μ_step : P.CoupledState Seed r → PMF (P.CoupledState Seed r)),
    (∀ p ∈ μ.support,
      P.ExecProgramDist w p_op outReg
        (P.prepareDictRegs clearScratch baseReg tagReg keyReg valReg o (P.csReg p)) (P.csMem p)
        ((μ_step p).map P.toRegMem) (T_step p) ∧
      ∀ q ∈ (μ_step p).support,
        WordBounded w (P.csReg q) (P.csMem q) ∧
        P.OpOutputCorrect outReg s o (P.csReg q) ∧
        UnchangedOutside base sp (P.csMem p) (P.csMem q)) →
    P.ExecDictOps w p_op clearScratch baseReg tagReg keyReg valReg outReg base sp
      (P.stepDict s o) ops (μ.bind μ_step) μ_final T_rest →
    P.ExecDictOps w p_op clearScratch baseReg tagReg keyReg valReg outReg base sp
      s (o :: ops) μ μ_final ((∑' p, μ p * T_step p) + T_rest)

/-! ### Correspondence Lemmas for `DictPresentation` -/

private theorem pmf_le_map_apply {α β : Type*} (ν : PMF α) (f : α → β) (a : α) :
    ν a ≤ (ν.map f) (f a) := by
  classical
  rw [PMF.map_apply]
  have h1 : ν a = (if f a = f a then ν a else 0) := by simp
  rw [h1]
  exact le_tsum (fun x => if f a = f x then ν x else 0) a

private theorem dictOpOf_surjective {S : Presentation} (P : DictPresentation S) {U : ℕ}
    (o : P.DictOp U) : ∃ o_lib : Dictionary.Op U, P.dictOpOf o_lib = o :=
  P.dictOp_induction (motive := fun o => ∃ o_lib, P.dictOpOf o_lib = o)
    (fun u => ⟨.get u, rfl⟩) (fun u v => ⟨.insert u v, rfl⟩) o

private theorem ops_surjective {S : Presentation} (P : DictPresentation S) {U : ℕ}
    (ops : List (P.DictOp U)) :
    ∃ ops_lib : List (Dictionary.Op U), ops_lib.map P.dictOpOf = ops := by
  choose f hf using dictOpOf_surjective P (U := U)
  refine ⟨ops.map f, ?_⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ops]
  congr 1
  funext o
  exact hf o

private theorem stepDict_dictOpOf {S : Presentation} {P : DictPresentation S} (hP : DictLaws S P)
    {U V n_max : ℕ} (s : Fin U → Option ℕ) (o : Dictionary.Op U) :
    P.stepDict s (P.dictOpOf o) = ((Dictionary.spec U V n_max).stepFn s o).1 := by
  cases o with
  | get u => exact hP.stepDict_get s u
  | insert u v => exact hP.stepDict_insert s u v

private theorem validDictOp_dictOpOf {S : Presentation} {P : DictPresentation S} (hP : DictLaws S P)
    {U V n_max : ℕ} (s : Fin U → Option ℕ) (o : Dictionary.Op U) :
    P.validDictOp V n_max s (P.dictOpOf o) ↔ (Dictionary.spec U V n_max).valid s o := by
  cases o with
  | get u => exact hP.validDictOp_get V n_max s u
  | insert u v => exact hP.validDictOp_insert V n_max s u v

private theorem validDictHistory_map_dictOpOf {S : Presentation} {P : DictPresentation S}
    (hP : DictLaws S P) {U V n_max : ℕ} (s : Fin U → Option ℕ) (ops : List (Dictionary.Op U)) :
    P.ValidDictHistory V n_max s (ops.map P.dictOpOf) ↔
      (Dictionary.spec U V n_max).ValidHistory s ops := by
  induction ops generalizing s with
  | nil => exact hP.validDictHistory_nil V n_max s
  | cons o os ih =>
    simp only [List.map_cons, hP.validDictHistory_cons, validDictOp_dictOpOf hP,
      stepDict_dictOpOf hP (V := V) (n_max := n_max), ih]
    rfl

private theorem dataOfRegMem_regMemOf {S : Presentation} {P : DictPresentation S}
    (hP : DictLaws S P) {r : ℕ} (d : Data r) :
    P.dataOfRegMem (P.regMemOf d) = d := by
  cases d
  simp [DictPresentation.dataOfRegMem, DictPresentation.regMemOf, hP.rmReg_mk, hP.rmMem_mk]

private theorem regMemOf_dataOfRegMem {S : Presentation} {P : DictPresentation S}
    (hP : DictLaws S P) {r : ℕ} (q : P.RegMem r) :
    P.regMemOf (P.dataOfRegMem q) = q :=
  hP.regMem_eta q

private theorem pairOfCoupledState_coupledStateOf {S : Presentation} {P : DictPresentation S}
    (hP : DictLaws S P) {Seed : Type} {r : ℕ} (p : Seed × Data r) :
    P.pairOfCoupledState (P.coupledStateOf p) = p := by
  rcases p with ⟨θ, ⟨reg, mem⟩⟩
  simp [DictPresentation.pairOfCoupledState, DictPresentation.coupledStateOf,
    hP.csSeed_mk, hP.csReg_mk, hP.csMem_mk]

private theorem coupledStateOf_pairOfCoupledState {S : Presentation} {P : DictPresentation S}
    (hP : DictLaws S P) {Seed : Type} {r : ℕ} (q : P.CoupledState Seed r) :
    P.coupledStateOf (P.pairOfCoupledState q) = q :=
  hP.coupledState_eta q

private theorem map_coupledStateOf_toRegMem {S : Presentation} {P : DictPresentation S}
    (hP : DictLaws S P) {Seed : Type} {r : ℕ} (ν : PMF (Seed × Data r)) :
    (ν.map P.coupledStateOf).map P.toRegMem = (ν.map Prod.snd).map P.regMemOf := by
  rw [PMF.map_comp, PMF.map_comp]
  refine congrArg (ν.map ·) (funext fun p => ?_)
  rcases p with ⟨θ, ⟨reg, mem⟩⟩
  simp [DictPresentation.toRegMem, DictPresentation.coupledStateOf, DictPresentation.regMemOf,
    hP.csReg_mk, hP.csMem_mk]

private theorem support_coupledStateOf_init {S : Presentation} {P : DictPresentation S}
    (hP : DictLaws S P) {Seed : Type} {r w base sp : ℕ}
    {baseReg frontierReg : Fin r} {mem₀ : ℕ → ℕ}
    {ν₀ : PMF (Seed × Data r)}
    (hsupp : ∀ p ∈ ν₀.support,
      WordBounded w p.2.regs p.2.mem ∧
      p.2.regs baseReg = base ∧
      p.2.regs frontierReg = base + sp ∧
      Modifies (Block.mk base sp).footprint mem₀ p.2.mem) :
    ∀ p_abs ∈ (ν₀.map P.coupledStateOf).support,
      WordBounded w (P.csReg p_abs) (P.csMem p_abs) ∧
      P.csReg p_abs baseReg = base ∧
      P.csReg p_abs frontierReg = base + sp ∧
      UnchangedOutside base sp mem₀ (P.csMem p_abs) := by
  intro p_abs hp_abs
  rw [PMF.mem_support_map_iff] at hp_abs
  obtain ⟨p, hp, rfl⟩ := hp_abs
  obtain ⟨hbdd, hbase, hfr, hmod⟩ := hsupp p hp
  have hreg : P.csReg (P.coupledStateOf p) = p.2.regs :=
    hP.csReg_mk p.1 p.2.regs p.2.mem
  have hmem : P.csMem (P.coupledStateOf p) = p.2.mem :=
    hP.csMem_mk p.1 p.2.regs p.2.mem
  rw [hreg, hmem]
  refine ⟨hbdd, hbase, hfr, fun a ha => ?_⟩
  have ha' : a ∉ (Block.mk base sp).footprint := by
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt]
    exact ha
  exact hmod a ha'

private theorem totalCost_const {U V n_max : ℕ} (c : ℕ) (s : Dictionary.State U)
    (ops : List (Dictionary.Op U)) :
    (Dictionary.spec U V n_max).totalCost (fun _ _ => c) s ops = ops.length * c := by
  induction ops generalizing s with
  | nil =>
    change 0 = 0 * c
    simp
  | cons o os ih =>
    change c + (Dictionary.spec U V n_max).totalCost (fun _ _ => c)
      ((Dictionary.spec U V n_max).stepFn s o).1 os = (os.length + 1) * c
    rw [ih]
    ring

/-- Compile any library `ExecCodeDist w c ⟨reg, mem⟩ μ_lib T` to `P.ExecProgramDist`. -/
theorem compile_execCodeDist {S : Presentation} (hS : Laws S)
    {P : DictPresentation S} (hP : DictLaws S P)
    {r w : ℕ} {c : Code .exact r} {reg : Fin r → ℕ} {mem : ℕ → ℕ}
    {μ_lib : PMF (Data r)} {T : ℝ≥0∞} (outReg : Fin r)
    (h : ExecCodeDist w c ⟨reg, mem⟩ μ_lib T) :
    P.ExecProgramDist w (S.programOf (c.program outReg)) outReg reg mem
      (μ_lib.map P.regMemOf) T := by
  obtain ⟨hexp, hff, -, hhalt⟩ := h.program_halts outReg
  refine ⟨?_, ?_, ?_⟩
  · intro T_hor
    rw [S.evalRand_eq hS, PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
    rintro ⟨cfg', hcfg', heq⟩
    rcases cfg' with ⟨pc', ⟨reg', mem'⟩⟩ | ⟨v', ⟨reg', mem'⟩⟩ | _
    · exact hS.running_ne_faulted heq
    · exact hS.halted_ne_faulted heq
    · rw [Cslib.WordRAM.support_evalRand] at hcfg'
      exact hff T_hor hcfg'
  · rw [S.expectedTime_eq hS]
    exact hexp
  · intro q
    have hmap_q : (μ_lib.map P.regMemOf) q = μ_lib (P.dataOfRegMem q) := by
      classical
      rw [PMF.map_apply]
      have hite : (fun d : Data r => if q = P.regMemOf d then μ_lib d else 0) =
          (fun d : Data r => if d = P.dataOfRegMem q then μ_lib d else 0) := by
        funext d
        have hiff : (q = P.regMemOf d) ↔ (d = P.dataOfRegMem q) :=
          ⟨fun h => h ▸ (dataOfRegMem_regMemOf hP d).symm,
           fun h => h ▸ (regMemOf_dataOfRegMem hP q).symm⟩
        simp [hiff]
      rw [hite, tsum_ite_eq]
    rw [hmap_q]
    refine (hhalt (P.dataOfRegMem q)).trans (iSup_mono fun T_hor => ?_)
    rw [S.evalRand_eq hS]
    exact pmf_le_map_apply _ S.cfgOf (.halted (P.rmReg q outReg) (P.dataOfRegMem q))

/-- Generic transfer of `StateTransitionImpl.ExecStepsOfFn` to `P.ExecDictOps`. -/
theorem compile_execStepsOfFn {S : Presentation} (hS : Laws S)
    {P : DictPresentation S} (hP : DictLaws S P)
    {r_ds k_init w base U V n_max : ℕ}
    {Sub : SubroutineCode .exact r_ds k_init}
    {params : Fin k_init → ℕ}
    {s₀ : (Dictionary.spec U V n_max).State}
    (C : Randomized.StateTransitionImpl Sub (Dictionary.spec U V n_max) w base params s₀)
    (clearScratch : Bool) (baseReg tagReg keyReg valReg outReg : Fin r_ds)
    (hprep : ∀ (o : Dictionary.Op U) (d : Data r_ds),
      (C.toDynamicProgram.prepare o d).regs =
        P.prepareDictRegs clearScratch baseReg tagReg keyReg valReg (P.dictOpOf o) d.regs)
    (hdec : ∀ (s : Dictionary.State U) (o : Dictionary.Op U) (regs : Fin r_ds → ℕ),
      C.decode o regs = some ((Dictionary.spec U V n_max).stepFn s o).2 →
        P.OpOutputCorrect outReg s (P.dictOpOf o) regs)
    {s : (Dictionary.spec U V n_max).State} {ops : List (Dictionary.spec U V n_max).Op}
    {ν ν_final : PMF (C.Seed × Data r_ds)} {T_ops : ℝ≥0∞}
    (hex : C.ExecStepsOfFn s ops ν ν_final T_ops) :
    P.ExecDictOps w (S.programOf (Sub.code.program outReg)) clearScratch
      baseReg tagReg keyReg valReg outReg base C.space s (ops.map P.dictOpOf)
      (ν.map P.coupledStateOf) (ν_final.map P.coupledStateOf) T_ops := by
  refine @Randomized.StateTransitionImpl.ExecStepsOfFn.rec .exact r_ds k_init w base Sub
    (Dictionary.spec U V n_max) params s₀ C (Dictionary.spec U V n_max).stepFn inferInstance
    (fun s ops ν ν_final T_ops _ =>
      P.ExecDictOps w (S.programOf (Sub.code.program outReg)) clearScratch
        baseReg tagReg keyReg valReg outReg base C.space s (ops.map P.dictOpOf)
        (ν.map P.coupledStateOf) (ν_final.map P.coupledStateOf) T_ops)
    (fun s ν =>
      hP.execDictOps_nil w _ clearScratch baseReg tagReg keyReg valReg outReg base C.space s
        (ν.map P.coupledStateOf))
    (fun {s o ops ν ν_final μ_step T_step T_rest} hstep _ ih => ?_)
    s ops ν ν_final T_ops hex
  let T_step_abs : P.CoupledState C.Seed r_ds → ℝ≥0∞ :=
    fun p => T_step (P.pairOfCoupledState p)
  let μ_step_abs : P.CoupledState C.Seed r_ds → PMF (P.CoupledState C.Seed r_ds) :=
    fun p => (μ_step (P.pairOfCoupledState p)).map P.coupledStateOf
  have hT_eq :
      (∑' p_abs, (ν.map P.coupledStateOf) p_abs * T_step_abs p_abs) =
        ∑' p, ν p * T_step p := by
    rw [Cslib.Probability.PMF.tsum_map_mul]
    refine tsum_congr fun p => ?_
    dsimp only [T_step_abs]
    rw [pairOfCoupledState_coupledStateOf hP]
  have hbind_eq :
      (ν.map P.coupledStateOf).bind μ_step_abs = (ν.bind μ_step).map P.coupledStateOf := by
    rw [PMF.bind_map, PMF.map_bind]
    refine congrArg (ν.bind ·) (funext fun p => ?_)
    dsimp only [Function.comp_apply, μ_step_abs]
    rw [pairOfCoupledState_coupledStateOf hP]
  rw [← hT_eq]
  refine hP.execDictOps_cons T_step_abs μ_step_abs (fun p_abs hp_abs => ?_) ?_
  · rw [PMF.mem_support_map_iff] at hp_abs
    obtain ⟨p, hp, rfl⟩ := hp_abs
    obtain ⟨he_step, hq_step⟩ := hstep p hp
    have hp_pair : P.pairOfCoupledState (P.coupledStateOf p) = p :=
      pairOfCoupledState_coupledStateOf hP p
    refine ⟨?_, ?_⟩
    · have hdist :
          (μ_step_abs (P.coupledStateOf p)).map P.toRegMem =
            ((μ_step p).map Prod.snd).map P.regMemOf := by
        dsimp only [μ_step_abs]
        rw [hp_pair]
        exact map_coupledStateOf_toRegMem hP (μ_step p)
      have hreg_p : P.csReg (P.coupledStateOf p) = p.2.regs :=
        hP.csReg_mk p.1 p.2.regs p.2.mem
      have hmem_p : P.csMem (P.coupledStateOf p) = p.2.mem :=
        hP.csMem_mk p.1 p.2.regs p.2.mem
      have hprep_data :
          C.toDynamicProgram.prepare o p.2 =
            ⟨P.prepareDictRegs clearScratch baseReg tagReg keyReg valReg (P.dictOpOf o)
              (P.csReg (P.coupledStateOf p)), P.csMem (P.coupledStateOf p)⟩ := by
        ext : 1
        · rw [hreg_p]
          exact hprep o p.2
        · rw [hmem_p]
          rfl
      have hT_p : T_step_abs (P.coupledStateOf p) = T_step p := by
        dsimp only [T_step_abs]
        rw [hp_pair]
      rw [hdist, hT_p]
      rw [hprep_data] at he_step
      exact compile_execCodeDist hS hP outReg he_step
    · intro q_abs hq_abs
      dsimp only [μ_step_abs] at hq_abs
      rw [hp_pair, PMF.mem_support_map_iff] at hq_abs
      obtain ⟨q, hq, rfl⟩ := hq_abs
      obtain ⟨hdec_q, hrep_q, hmod_q⟩ := hq_step q hq
      have hreg_q : P.csReg (P.coupledStateOf q) = q.2.regs :=
        hP.csReg_mk q.1 q.2.regs q.2.mem
      have hmem_q : P.csMem (P.coupledStateOf q) = q.2.mem :=
        hP.csMem_mk q.1 q.2.regs q.2.mem
      have hmem_p : P.csMem (P.coupledStateOf p) = p.2.mem :=
        hP.csMem_mk p.1 p.2.regs p.2.mem
      rw [hreg_q, hmem_q, hmem_p]
      refine ⟨C.bounded hrep_q, hdec s o q.2.regs hdec_q, fun a ha => ?_⟩
      have ha' : a ∉ (Block.mk base C.space).footprint := by
        rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt]
        exact ha
      exact hmod_q a ha'
  · rw [stepDict_dictOpOf hP (V := V) (n_max := n_max), hbind_eq]
    exact ih

/-! ## Part 2: Chained Hashing with Multiply-Shift (`ChainedHash.lean`) -/

/-- Bucket bit-width `Nat.clog 2 (max n_max 2)`. -/
def chainedBucketBits (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max n_max 2)

/-- Number of buckets `2 ^ chainedBucketBits n_max`. -/
def chainedNumBuckets (n_max : ℕ) : ℕ :=
  2 ^ chainedBucketBits n_max

/-- Multiply-shift word width `max (chainedBucketBits n_max) (Nat.clog 2 (max U 2))`. -/
def chainedHashBits (U n_max : ℕ) : ℕ :=
  max (chainedBucketBits n_max) (Nat.clog 2 (max U 2))

/-- Memory footprint `4 + chainedNumBuckets n_max + 3 * n_max` of chained hashing. -/
def chainedSpace (n_max : ℕ) : ℕ :=
  4 + chainedNumBuckets n_max + 3 * n_max

/-- Linear space bound `chainedSpace n_max ≤ 8 * (n_max + 1)`. -/
theorem chainedSpace_le (n_max : ℕ) : chainedSpace n_max ≤ 8 * (n_max + 1) := by
  have hb : chainedNumBuckets n_max ≤ 2 * n_max + 4 := ChainedHash.numBuckets_le n_max
  unfold chainedSpace
  omega

/-- Headline bridge theorem for chained hashing (`ChainedHash.seq_expected_amortized`). -/
theorem chainedHashing (S : Presentation) (hS : Laws S)
    (P : DictPresentation S) (hP : DictLaws S P) :
    ∀ (U n_max : ℕ),
      ∃ (p_init p_op : List (S.Instr 22)),
        ∀ (V w base : ℕ),
          2 * chainedHashBits U n_max ≤ w →
          base + chainedSpace n_max < 2 ^ w →
          V < 2 ^ w →
          ∀ (reg₀ : Fin 22 → ℕ) (mem₀ : ℕ → ℕ),
            WordBounded w reg₀ mem₀ →
            reg₀ ⟨6, by decide⟩ = base →
            (∀ a, base ≤ a → a < base + chainedSpace n_max → mem₀ a = 0) →
            ∃ (Seed : Type) (μ_init : PMF (P.CoupledState Seed 22)),
              P.ExecProgramDist w p_init ⟨10, by decide⟩ reg₀ mem₀
                (μ_init.map P.toRegMem) 16 ∧
              (∀ p ∈ μ_init.support,
                WordBounded w (P.csReg p) (P.csMem p) ∧
                P.csReg p ⟨5, by decide⟩ = base ∧
                P.csReg p ⟨6, by decide⟩ = base + chainedSpace n_max ∧
                UnchangedOutside base (chainedSpace n_max) mem₀ (P.csMem p)) ∧
              ∀ ops : List (P.DictOp U),
                P.ValidDictHistory V n_max (DictPresentation.emptyDict U) ops →
                ∃ (μ_final : PMF (P.CoupledState Seed 22)) (T_ops : ℝ≥0∞),
                  P.ExecDictOps w p_op true
                    ⟨5, by decide⟩ ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩
                    base (chainedSpace n_max) (DictPresentation.emptyDict U) ops
                    μ_init μ_final T_ops ∧
                  (16 : ℝ≥0∞) + T_ops ≤ ((16 + 73 * ops.length : ℕ) : ℝ≥0∞) := by
  intro U n_max
  let Sub := ChainedHash.subroutineCode U n_max
  refine ⟨S.programOf (Sub.initFresh.program ⟨10, by decide⟩),
    S.programOf (Sub.code.program ⟨10, by decide⟩), ?_⟩
  intro V w base hw hfit_space hfit_V reg₀ mem₀ hbdd₀ hfr₀ hz₀
  let C := ChainedHash.impl U V n_max w base hw hfit_space hfit_V
  have hz_lib : ∀ a ∈ (Block.mk base (ChainedHash.space n_max)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns] at ha
    exact hz₀ a ha.1 ha.2
  obtain ⟨ν₀, he_init, hseed₀, hsupp₀⟩ :=
    C.initFresh_exec (x := ⟨reg₀, mem₀⟩) hbdd₀ hfr₀ (fun j => Fin.elim0 j) hz_lib
  have hinit_time : C.initTime = 16 := by
    change (3 : ℝ≥0∞) + 13 = 16
    norm_num
  rw [hinit_time] at he_init
  refine ⟨C.Seed, ν₀.map P.coupledStateOf, ?_, ?_, ?_⟩
  · rw [map_coupledStateOf_toRegMem hP]
    exact compile_execCodeDist hS hP ⟨10, by decide⟩ he_init
  · exact support_coupledStateOf_init hP fun p hp =>
      ⟨(hsupp₀ p hp).2.1.bounded, (hsupp₀ p hp).2.1.reg_base, (hsupp₀ p hp).1, (hsupp₀ p hp).2.2.2⟩
  · intro ops hv_abs
    obtain ⟨ops_lib, rfl⟩ := ops_surjective P ops
    have hv_lib : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops_lib :=
      (validDictHistory_map_dictOpOf hP (DictPresentation.emptyDict U) ops_lib).mp hv_abs
    obtain ⟨ν_final, T_ops, hex_steps, -, -, hamort⟩ :=
      C.steps_expected_amortized_ofFn ops_lib ν₀ hv_lib hseed₀ fun p hp => (hsupp₀ p hp).2.1
    refine ⟨ν_final.map P.coupledStateOf, T_ops, ?_, ?_⟩
    · refine compile_execStepsOfFn hS hP C true
        ⟨5, by decide⟩ ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩
        (fun o d => ?_) (fun s o regs hdec => ?_) hex_steps
      · funext i
        cases o with
        | get u =>
          dsimp only [DictPresentation.dictOpOf]
          rw [hP.prepareDictRegs_get]
          change (if decide (i ≠ ⟨5, by decide⟩) then
            if i = ⟨7, by decide⟩ then 0 else if i = ⟨8, by decide⟩ then u.val else 0
          else d.regs i) = _
          fin_cases i <;> rfl
        | insert u v =>
          dsimp only [DictPresentation.dictOpOf]
          rw [hP.prepareDictRegs_insert]
          change (if decide (i ≠ ⟨5, by decide⟩) then
            if i = ⟨7, by decide⟩ then 1
            else if i = ⟨8, by decide⟩ then u.val
            else if i = ⟨9, by decide⟩ then v else 0
          else d.regs i) = _
          fin_cases i <;> rfl
      · cases o with
        | get u =>
          dsimp only [DictPresentation.dictOpOf]
          rw [hP.opOutputCorrect_get]
          change (if regs ⟨10, by decide⟩ = 0 then some none
            else some (some (regs ⟨10, by decide⟩ - 1))) = some (s u) at hdec
          split_ifs at hdec ⊢ with h0 <;> simp_all
        | insert u v =>
          dsimp only [DictPresentation.dictOpOf]
          rw [hP.opOutputCorrect_insert]
          trivial
    · change T_ops + ∑' q, ν_final q * ((0 : ℕ) : ℝ≥0∞) ≤
        ((Dictionary.spec U V n_max).totalCost (fun _ _ => ChainedHash.chargeVal)
          (Dictionary.empty U) ops_lib : ℝ≥0∞) + ∑' p, ν₀ p * ((0 : ℕ) : ℝ≥0∞) at hamort
      simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero] at hamort
      rw [totalCost_const] at hamort
      rw [List.length_map]
      calc (16 : ℝ≥0∞) + T_ops
        _ ≤ 16 + ((ops_lib.length * ChainedHash.chargeVal : ℕ) : ℝ≥0∞) := add_le_add le_rfl hamort
        _ = ((16 + 73 * ops_lib.length : ℕ) : ℝ≥0∞) := by
          dsimp only [ChainedHash.chargeVal]
          push_cast
          ring

/-! ## Part 3: Linear Probing with `5`-Wise Independent Hashing (`LinearProbing.lean`) -/

open ComplexityAbstracts.HashFamiliesBridge
  (chunkBits chunkBits_eq trinomialStepLoop trinomialStep trinomialStep_eq
   trinomialDeg trinomialDeg_eq)

/-- Number of `chunkBits n_max`-bit limbs `⌈trinomialDeg U M / chunkBits n_max⌉`. -/
def limbCount (n_max U M : ℕ) : ℕ :=
  (trinomialDeg U M + chunkBits n_max - 1) / chunkBits n_max

theorem limbCount_eq (n_max U M : ℕ) :
    limbCount n_max U M = KWise.limbCount n_max U M := by
  unfold limbCount KWise.limbCount
    KWise.limbCountFromB
  rw [trinomialDeg_eq, chunkBits_eq]

/-- Memory footprint `8 + k + 2 ^ (2 * chunkBits n_max)` of the `k`-wise polynomial hash table. -/
def kWiseSpace (n_max k : ℕ) : ℕ :=
  8 + k + 2 ^ (2 * chunkBits n_max)

theorem kWiseSpace_eq (n_max k : ℕ) :
    kWiseSpace n_max k = KWise.space n_max k := by
  unfold kWiseSpace KWise.space
    KWise.spaceFromB
  rw [chunkBits_eq]

/-- Deterministic lookup-table setup step count for `KWise.initTableCode`. -/
def kWiseInitTableSteps (n_max U M : ℕ) : ℕ :=
  19 * 2 ^ (2 * chunkBits n_max) +
    4 * Nat.log 2 (max n_max 2) +
    5 * Nat.clog 2 (max U 2) +
    5 * trinomialStep U M + 69

theorem kWiseInitTableSteps_eq (n_max U M : ℕ) :
    kWiseInitTableSteps n_max U M =
      KWise.initTableSteps n_max U M := by
  unfold kWiseInitTableSteps KWise.initTableSteps
  rw [chunkBits_eq, trinomialStep_eq]

/-- Deterministic instruction budget for `KWise.evalCode k`. -/
def kWiseEvalSteps (n_max U M k : ℕ) : ℕ :=
  ((11 * limbCount n_max U M + 12) * limbCount n_max U M + 30) * k + 19

theorem kWiseEvalSteps_eq (n_max U M k : ℕ) :
    kWiseEvalSteps n_max U M k =
      KWise.evalSteps n_max U M k := by
  unfold kWiseEvalSteps KWise.evalSteps
    KWise.evalStepsFromB
  rw [limbCount_eq]
  rfl

/-- Power-of-2 table bit-width `⌈log₂(max (8 * n_max) 8)⌉` for linear probing. -/
def lpTableLog (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max (8 * n_max) 8)

theorem lpTableLog_eq (n_max : ℕ) : lpTableLog n_max = LinearProbing.tableLog n_max := rfl

/-- Power-of-2 table size `2 ^ lpTableLog n_max` for linear probing. -/
def lpTableSize (n_max : ℕ) : ℕ :=
  2 ^ lpTableLog n_max

theorem lpTableSize_eq (n_max : ℕ) : lpTableSize n_max = LinearProbing.tableSize n_max := rfl

/-- Memory footprint `kWiseSpace n_max 5 + 3 * lpTableSize n_max` of linear probing. -/
def lpSpace (n_max : ℕ) : ℕ :=
  kWiseSpace n_max 5 + 3 * lpTableSize n_max

theorem lpSpace_eq (n_max : ℕ) : lpSpace n_max = LinearProbing.space n_max := by
  unfold lpSpace LinearProbing.space
  rw [kWiseSpace_eq, lpTableSize_eq]

/-- Linear space bound `lpSpace n_max ≤ 209 * (n_max + 1)` across all capacities `n_max`. -/
theorem linearProbingSpace_le (n_max : ℕ) : lpSpace n_max ≤ 209 * (n_max + 1) := by
  rw [lpSpace_eq]
  have hle := LinearProbing.space_le n_max
  have hmax : max n_max 4 ≤ 4 * (n_max + 1) := by omega
  omega

/-- Expected instruction count `3 + (kWiseInitTableSteps n_max U (lpTableLog n_max) + 38)` for
linear-probing fresh initialization. -/
def lpInitSteps (U n_max : ℕ) : ℕ :=
  3 + (kWiseInitTableSteps n_max U (lpTableLog n_max) + 38)

theorem lpInitSteps_eq (U n_max : ℕ) :
    lpInitSteps U n_max = 3 + LinearProbing.setupTime U n_max := by
  unfold lpInitSteps LinearProbing.setupTime
  rw [kWiseInitTableSteps_eq, lpTableLog_eq]

/-- Expected per-operation instruction charge `kWiseEvalSteps n_max U (lpTableLog n_max) 5 + 3483`
for linear probing. -/
def lpOpCharge (U n_max : ℕ) : ℕ :=
  kWiseEvalSteps n_max U (lpTableLog n_max) 5 + 12 * 288 + 27

theorem lpOpCharge_eq (U n_max : ℕ) : lpOpCharge U n_max = LinearProbing.charge U n_max := by
  unfold lpOpCharge LinearProbing.charge
  rw [kWiseEvalSteps_eq, lpTableLog_eq]

/-- Uniform `O(1)` per-operation instruction bound `559652` for linear probing at `c_exp = 4`. -/
def lpOpChargeBound : ℕ :=
  559652

private theorem lpTableLog_le_clog (n_max : ℕ) :
    LinearProbing.tableLog n_max ≤ max 4 1 * Nat.clog 2 (max n_max 4) + 5 := by
  have h1 : LinearProbing.tableLog n_max ≤ Nat.clog 2 (max n_max 4) + 3 := by
    unfold LinearProbing.tableLog
    refine Nat.clog_le_of_le_pow ?_
    calc max (8 * n_max) 8
        ≤ 8 * max n_max 4 := by omega
      _ ≤ 8 * 2 ^ Nat.clog 2 (max n_max 4) :=
          Nat.mul_le_mul_left 8 (Nat.le_pow_clog (by decide) _)
      _ = 2 ^ (Nat.clog 2 (max n_max 4) + 3) := by ring
  change LinearProbing.tableLog n_max ≤ 4 * Nat.clog 2 (max n_max 4) + 5
  omega

/-- Whenever `U ≤ max n_max 4 ^ 4`, the per-operation expected instruction charge
`lpOpCharge U n_max` of linear probing is bounded by `lpOpChargeBound = 559652`, independently of
`n_max` and `U`. -/
theorem linearProbingCharge_le {U n_max : ℕ} (hU : U ≤ max n_max 4 ^ 4) :
    lpOpCharge U n_max ≤ lpOpChargeBound := by
  rw [lpOpCharge_eq]
  have hL :
      KWise.limbCount n_max U (LinearProbing.tableLog n_max) ≤
        Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableLimbBound 4 :=
    Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.limbCount_le_provableLimbBound
      hU (lpTableLog_le_clog n_max)
  have hL100 :
      KWise.limbCount n_max U (LinearProbing.tableLog n_max) ≤
        100 := by
    simpa [Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableLimbBound] using hL
  unfold LinearProbing.charge KWise.evalSteps
    KWise.evalStepsFromB lpOpChargeBound
  change ((11 * KWise.limbCount n_max U
        (LinearProbing.tableLog n_max) + 12) *
      KWise.limbCount n_max U (LinearProbing.tableLog n_max) +
        30) * 5 + 19 + 12 * 288 + 27 ≤ 559652
  nlinarith

/-- Headline bridge theorem for linear probing (`LinearProbing.seq_expected_amortized`) at
`c_exp = 4`. -/
theorem linearProbing (S : Presentation) (hS : Laws S)
    (P : DictPresentation S) (hP : DictLaws S P) :
    ∀ (U n_max : ℕ),
      ∃ (p_init p_op : List (S.Instr 24)),
        ∀ (V w base : ℕ),
          U ≤ max n_max 4 ^ 4 →
          2 * trinomialDeg U (lpTableLog n_max) ≤ w →
          base + lpSpace n_max < 2 ^ w →
          V < 2 ^ w →
          ∀ (reg₀ : Fin 24 → ℕ) (mem₀ : ℕ → ℕ),
            WordBounded w reg₀ mem₀ →
            reg₀ ⟨18, by decide⟩ = base →
            (∀ a, base ≤ a → a < base + lpSpace n_max → mem₀ a = 0) →
            ∃ (Seed : Type) (μ_init : PMF (P.CoupledState Seed 24)),
              P.ExecProgramDist w p_init ⟨2, by decide⟩ reg₀ mem₀
                (μ_init.map P.toRegMem) (lpInitSteps U n_max) ∧
              (∀ p ∈ μ_init.support,
                WordBounded w (P.csReg p) (P.csMem p) ∧
                P.csReg p ⟨0, by decide⟩ = base ∧
                P.csReg p ⟨18, by decide⟩ = base + lpSpace n_max ∧
                UnchangedOutside base (lpSpace n_max) mem₀ (P.csMem p)) ∧
              ∀ ops : List (P.DictOp U),
                P.ValidDictHistory V n_max (DictPresentation.emptyDict U) ops →
                ∃ (μ_final : PMF (P.CoupledState Seed 24)) (T_ops : ℝ≥0∞),
                  P.ExecDictOps w p_op false
                    ⟨0, by decide⟩ ⟨22, by decide⟩ ⟨1, by decide⟩ ⟨23, by decide⟩ ⟨2, by decide⟩
                    base (lpSpace n_max) (DictPresentation.emptyDict U) ops
                    μ_init μ_final T_ops ∧
                  (lpInitSteps U n_max : ℝ≥0∞) + T_ops ≤
                    ((lpInitSteps U n_max + ops.length * lpOpCharge U n_max : ℕ) : ℝ≥0∞) ∧
                  (lpInitSteps U n_max : ℝ≥0∞) + T_ops ≤
                    ((lpInitSteps U n_max + ops.length * lpOpChargeBound : ℕ) : ℝ≥0∞) := by
  intro U n_max
  let Sub := LinearProbing.subroutineCode U n_max
  refine ⟨S.programOf (Sub.initFresh.program ⟨2, by decide⟩),
    S.programOf (Sub.code.program ⟨2, by decide⟩), ?_⟩
  intro V w base hU hw hfit_space hfit_V reg₀ mem₀ hbdd₀ hfr₀ hz₀
  have hw_lib : 2 * Cslib.Probability.trinomialDeg U (LinearProbing.tableLog n_max) ≤ w := by
    rwa [← trinomialDeg_eq, ← lpTableLog_eq]
  have hfit_space_lib : Fits w (base + LinearProbing.space n_max) := by
    rwa [← lpSpace_eq]
  let C := LinearProbing.impl U V n_max w base hw_lib hfit_space_lib hfit_V
  have hz_lib : ∀ a ∈ (Block.mk base (LinearProbing.space n_max)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns, ← lpSpace_eq] at ha
    exact hz₀ a ha.1 ha.2
  obtain ⟨ν₀, he_init, hseed₀, hsupp₀⟩ :=
    C.initFresh_exec (x := ⟨reg₀, mem₀⟩) hbdd₀ hfr₀ (fun j => Fin.elim0 j) hz_lib
  have hinit_time : C.initTime = (lpInitSteps U n_max : ℝ≥0∞) := by
    rw [lpInitSteps_eq, Nat.cast_add, Nat.cast_ofNat]
    rfl
  rw [hinit_time] at he_init
  refine ⟨C.Seed, ν₀.map P.coupledStateOf, ?_, ?_, ?_⟩
  · rw [map_coupledStateOf_toRegMem hP]
    exact compile_execCodeDist hS hP ⟨2, by decide⟩ he_init
  · rw [lpSpace_eq]
    exact support_coupledStateOf_init hP fun p hp =>
      ⟨(hsupp₀ p hp).2.1.bounded, (hsupp₀ p hp).2.1.reg_base, (hsupp₀ p hp).1, (hsupp₀ p hp).2.2.2⟩
  · intro ops hv_abs
    obtain ⟨ops_lib, rfl⟩ := ops_surjective P ops
    have hv_lib : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops_lib :=
      (validDictHistory_map_dictOpOf hP (DictPresentation.emptyDict U) ops_lib).mp hv_abs
    obtain ⟨ν_final, T_ops, hex_steps, -, -, hamort⟩ :=
      C.steps_expected_amortized_ofFn ops_lib ν₀ hv_lib hseed₀ fun p hp => (hsupp₀ p hp).2.1
    change T_ops + ∑' q, ν_final q * ((0 : ℕ) : ℝ≥0∞) ≤
      ((Dictionary.spec U V n_max).totalCost (fun _ _ => LinearProbing.charge U n_max)
        (Dictionary.empty U) ops_lib : ℝ≥0∞) + ∑' p, ν₀ p * ((0 : ℕ) : ℝ≥0∞) at hamort
    simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero] at hamort
    rw [totalCost_const, ← lpOpCharge_eq] at hamort
    have hbound : (lpInitSteps U n_max : ℝ≥0∞) + T_ops ≤
        ((lpInitSteps U n_max + ops_lib.length * lpOpCharge U n_max : ℕ) : ℝ≥0∞) := by
      rw [Nat.cast_add]
      exact add_le_add le_rfl hamort
    refine ⟨ν_final.map P.coupledStateOf, T_ops, ?_, ?_, ?_⟩
    · rw [lpSpace_eq]
      exact compile_execStepsOfFn hS hP C false
        ⟨0, by decide⟩ ⟨22, by decide⟩ ⟨1, by decide⟩ ⟨23, by decide⟩ ⟨2, by decide⟩
        (fun o d => by
          funext i
          cases o with
          | get u =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.prepareDictRegs_get]
            change (if decide (i = ⟨1, by decide⟩ ∨ i = ⟨22, by decide⟩ ∨ i = ⟨23, by decide⟩) then
              if i = ⟨1, by decide⟩ then u.val else 0
            else d.regs i) = _
            fin_cases i <;> rfl
          | insert u v =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.prepareDictRegs_insert]
            change (if decide (i = ⟨1, by decide⟩ ∨ i = ⟨22, by decide⟩ ∨ i = ⟨23, by decide⟩) then
              if i = ⟨1, by decide⟩ then u.val
              else if i = ⟨22, by decide⟩ then 1
              else if i = ⟨23, by decide⟩ then v else 0
            else d.regs i) = _
            fin_cases i <;> rfl)
        (fun s o regs hdec => by
          cases o with
          | get u =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.opOutputCorrect_get]
            change some (if regs ⟨2, by decide⟩ = 0 then none
              else some (regs ⟨2, by decide⟩ - 1)) = some (s u) at hdec
            exact Option.some.inj hdec
          | insert u v =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.opOutputCorrect_insert]
            trivial)
        hex_steps
    · rw [List.length_map]
      exact hbound
    · rw [List.length_map]
      refine hbound.trans ?_
      exact Nat.cast_le.mpr (Nat.add_le_add_left
        (Nat.mul_le_mul_left _ (linearProbingCharge_le hU)) _)

/-! ## Part 4: Uniform Probing via Odd-Stride Double Hashing (`UniformProbing.lean`) -/

open ComplexityAbstracts.HashFamiliesBridge
  (regimeThreshold regimeThreshold_eq charBits)

/-- Log₂ of the power-of-2 table size `⌈log₂(32 * max n_max 4)⌉` (`≥ 32 * max n_max 4`). -/
def tableBits32 (n_max : ℕ) : ℕ :=
  Nat.clog 2 (32 * max n_max 4)

/-- Power-of-2 table size `2 ^ tableBits32 n_max`. -/
def tableSize32 (n_max : ℕ) : ℕ :=
  2 ^ tableBits32 n_max

/-- Memory footprint `(c + 1) * d * 2 ^ b` of a single Double Tabulation instance. -/
def doubleTabSpace (c d b : ℕ) : ℕ :=
  (c + 1) * d * 2 ^ b

/-- Exact instruction count `5 * doubleTabSpace c d b + 13` for resampling a Double Tabulation
instance. -/
def doubleTabResampleSteps (c d b : ℕ) : ℕ :=
  5 * doubleTabSpace c d b + 13

/-- Exact instruction count `(12 * c + 11) * d + 10` for evaluating a Double Tabulation instance. -/
def doubleTabEvalSteps (c d : ℕ) : ℕ :=
  (12 * c + 11) * d + 10

/-- Memory footprint `doubleTabSpace 8 64 (charBits n_max)` of one Double Tabulation table at
`c_exp = 4`. -/
def upSingleTabSpace (n_max : ℕ) : ℕ :=
  doubleTabSpace 8 64 (charBits n_max)

/-- Total memory footprint `2 * upSingleTabSpace n_max + 3 * tableSize32 n_max` of uniform probing
at `c_exp = 4`. -/
def upSpace (n_max : ℕ) : ℕ :=
  2 * upSingleTabSpace n_max + 3 * tableSize32 n_max

theorem upSpace_eq (n_max : ℕ) : upSpace n_max = UniformProbing.space 4 n_max := rfl

/-- Linear-space factor `32 * (8 + 1) * 64 + 768 = 19200` for uniform probing at `c_exp = 4`. -/
def upSpaceFactor : ℕ :=
  32 * (8 + 1) * 64 + 768

/-- Across all capacities `n_max : ℕ`, uniform probing uses at most
`upSpaceFactor * (n_max + 1) = 19200 * (n_max + 1)` words of memory. -/
theorem uniformProbingSpace_le (n_max : ℕ) :
    upSpace n_max ≤ upSpaceFactor * (n_max + 1) :=
  UniformProbing.space_le 4 n_max

/-- Expected instruction count `3 + (2 * doubleTabResampleSteps 8 64 (charBits n_max) + 4)` for
uniform-probing initialization at `c_exp = 4`. -/
def upInitSteps (n_max : ℕ) : ℕ :=
  3 + (2 * doubleTabResampleSteps 8 64 (charBits n_max) + 4)

theorem upInitSteps_eq (n_max : ℕ) :
    upInitSteps n_max = 3 + UniformProbing.setupSteps 4 n_max := rfl

/-- Deterministic instruction count `2 * doubleTabEvalSteps 8 64 + 15 = 13731` for evaluating the
primary and odd-stride Double Tabulation hashes at `c_exp = 4`. -/
def upHashEvalSteps : ℕ :=
  2 * doubleTabEvalSteps 8 64 + 15

theorem upHashEvalSteps_eq : upHashEvalSteps = UniformProbing.hashEvalSteps 4 := rfl

/-- Uniform `O(1)` expected per-operation instruction charge
`13 * regimeThreshold + upHashEvalSteps + 8 = 13 * 2 ^ 320000 + 13739` for uniform probing at
`c_exp = 4`. -/
def upOpCharge : ℕ :=
  13 * regimeThreshold + upHashEvalSteps + 8

theorem upOpCharge_eq : upOpCharge = UniformProbing.expectedOpCharge 4 := by
  unfold upOpCharge UniformProbing.expectedOpCharge
  rw [regimeThreshold_eq, upHashEvalSteps_eq]

/-- Headline bridge theorem for uniform probing (`UniformProbing.seq_expected_amortized`) at
`c_exp = 4`. -/
theorem uniformProbing (S : Presentation) (hS : Laws S)
    (P : DictPresentation S) (hP : DictLaws S P)
    (regimeThreshold' upHashEvalSteps' upOpCharge' : ℕ)
    (hRegime : regimeThreshold' = 2 ^ 320000)
    (hHashEval : upHashEvalSteps' = 2 * doubleTabEvalSteps 8 64 + 15)
    (hCharge : upOpCharge' = 13 * regimeThreshold' + upHashEvalSteps' + 8) :
    ∀ (n_max : ℕ),
      ∃ (p_init p_op : List (S.Instr 16)),
        ∀ (U V w base : ℕ),
          U ≤ max n_max 4 ^ 4 →
          base + upSpace n_max < 2 ^ w →
          (∀ u : Fin U, u.val < 2 ^ w) →
          V < 2 ^ w →
          ∀ (reg₀ : Fin 16 → ℕ) (mem₀ : ℕ → ℕ),
            WordBounded w reg₀ mem₀ →
            reg₀ ⟨14, by decide⟩ = base →
            (∀ a, base ≤ a → a < base + upSpace n_max → mem₀ a = 0) →
            ∃ (Seed : Type) (μ_init : PMF (P.CoupledState Seed 16)),
              P.ExecProgramDist w p_init ⟨12, by decide⟩ reg₀ mem₀
                (μ_init.map P.toRegMem) (upInitSteps n_max) ∧
              (∀ p ∈ μ_init.support,
                WordBounded w (P.csReg p) (P.csMem p) ∧
                P.csReg p ⟨0, by decide⟩ = base ∧
                P.csReg p ⟨14, by decide⟩ = base + upSpace n_max ∧
                UnchangedOutside base (upSpace n_max) mem₀ (P.csMem p)) ∧
              ∀ ops : List (P.DictOp U),
                P.ValidDictHistory V n_max (DictPresentation.emptyDict U) ops →
                ∃ (μ_final : PMF (P.CoupledState Seed 16)) (T_ops : ℝ≥0∞),
                  P.ExecDictOps w p_op true
                    ⟨0, by decide⟩ ⟨12, by decide⟩ ⟨13, by decide⟩ ⟨14, by decide⟩ ⟨12, by decide⟩
                    base (upSpace n_max) (DictPresentation.emptyDict U) ops
                    μ_init μ_final T_ops ∧
                  (upInitSteps n_max : ℝ≥0∞) + T_ops ≤
                    ((upInitSteps n_max + ops.length * upOpCharge' : ℕ) : ℝ≥0∞) := by
  intro n_max
  let Sub := UniformProbing.subroutineCode 4 n_max
  refine ⟨S.programOf (Sub.initFresh.program ⟨12, by decide⟩),
    S.programOf (Sub.code.program ⟨12, by decide⟩), ?_⟩
  intro U V w base hU hfit_space hfit_U hfit_V reg₀ mem₀ hbdd₀ hfr₀ hz₀
  have hfit_space_lib : Fits w (base + UniformProbing.space 4 n_max) := by
    rwa [← upSpace_eq]
  let C := UniformProbing.impl (V := V) hfit_space_lib hfit_U hfit_V hU
  have hz_lib : ∀ a ∈ (Block.mk base (UniformProbing.space 4 n_max)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns, ← upSpace_eq] at ha
    exact hz₀ a ha.1 ha.2
  obtain ⟨ν₀, he_init, hseed₀, hsupp₀⟩ :=
    C.initFresh_exec (x := ⟨reg₀, mem₀⟩) hbdd₀ hfr₀ (fun j => Fin.elim0 j) hz_lib
  have hinit_c : C.initTime = (upInitSteps n_max : ℝ≥0∞) := by
    rw [upInitSteps_eq, Nat.cast_add, Nat.cast_ofNat]
    rfl
  rw [hinit_c] at he_init
  refine ⟨C.Seed, ν₀.map P.coupledStateOf, ?_, ?_, ?_⟩
  · rw [map_coupledStateOf_toRegMem hP]
    exact compile_execCodeDist hS hP ⟨12, by decide⟩ he_init
  · rw [upSpace_eq]
    exact support_coupledStateOf_init hP fun p hp =>
      ⟨(hsupp₀ p hp).2.1.bounded, (hsupp₀ p hp).2.1.regs_base, (hsupp₀ p hp).1, (hsupp₀ p hp).2.2.2⟩
  · intro ops hv_abs
    obtain ⟨ops_lib, rfl⟩ := ops_surjective P ops
    have hv_lib : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops_lib :=
      (validDictHistory_map_dictOpOf hP (DictPresentation.emptyDict U) ops_lib).mp hv_abs
    obtain ⟨ν_final, T_ops, hex_steps, -, -, hamort⟩ :=
      C.steps_expected_amortized_ofFn ops_lib ν₀ hv_lib hseed₀ fun p hp => (hsupp₀ p hp).2.1
    refine ⟨ν_final.map P.coupledStateOf, T_ops, ?_, ?_⟩
    · rw [upSpace_eq]
      exact compile_execStepsOfFn hS hP C true
        ⟨0, by decide⟩ ⟨12, by decide⟩ ⟨13, by decide⟩ ⟨14, by decide⟩ ⟨12, by decide⟩
        (fun o d => by
          funext i
          cases o with
          | get u =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.prepareDictRegs_get]
            change (if decide (i ≠ ⟨0, by decide⟩) then
              if i = ⟨12, by decide⟩ then 0 else if i = ⟨13, by decide⟩ then u.val else 0
            else d.regs i) = _
            fin_cases i <;> rfl
          | insert u v =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.prepareDictRegs_insert]
            change (if decide (i ≠ ⟨0, by decide⟩) then
              if i = ⟨12, by decide⟩ then 1
              else if i = ⟨13, by decide⟩ then u.val
              else if i = ⟨14, by decide⟩ then v else 0
            else d.regs i) = _
            fin_cases i <;> rfl)
        (fun s o regs hdec => by
          cases o with
          | get u =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.opOutputCorrect_get]
            change some (if regs ⟨12, by decide⟩ = 0 then none
              else some (regs ⟨12, by decide⟩ - 1)) = some (s u) at hdec
            exact Option.some.inj hdec
          | insert u v =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.opOutputCorrect_insert]
            trivial)
        hex_steps
    · change T_ops + ∑' q, ν_final q * ((0 : ℕ) : ℝ≥0∞) ≤
        ((Dictionary.spec U V n_max).totalCost (fun _ _ => UniformProbing.expectedOpCharge 4)
          (Dictionary.empty U) ops_lib : ℝ≥0∞) + ∑' p, ν₀ p * ((0 : ℕ) : ℝ≥0∞) at hamort
      simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero] at hamort
      have hReg : regimeThreshold' = regimeThreshold := hRegime
      have hHE : upHashEvalSteps' = upHashEvalSteps := hHashEval
      have hCharge_eq : upOpCharge' = UniformProbing.expectedOpCharge 4 := by
        rw [hCharge, hReg, hHE]
        exact upOpCharge_eq
      rw [totalCost_const, ← hCharge_eq] at hamort
      rw [List.length_map, Nat.cast_add]
      exact add_le_add le_rfl hamort

/-! ## Part 5: Pagh–Rodler Cuckoo Hashing (`CuckooHashing.lean`) -/

/-- Internal bundle of the space and time constants for Pagh–Rodler cuckoo hashing at
`c_exp = 4` in `HashTablesAbstract.lean`. The public bridge theorems take these constants as flat
parameters and construct `CuckooPresentation` internally so `instantiateRev` substitutes bound
variables directly (avoiding `.proj` terms on the right-hand side of equational laws) and each `rfl`
in `HashTablesAbstract.lean` succeeds by syntactic equality without reducing `2 ^ 320000`. -/
structure CuckooPresentation where
  regimeThreshold : ℕ
  charBits : ℕ → ℕ
  tableBits32 : ℕ → ℕ
  tableSize32 : ℕ → ℕ
  kWiseSpace : ℕ → ℕ → ℕ
  kWiseInitTableSteps : ℕ → ℕ → ℕ → ℕ
  doubleTabSpace : ℕ → ℕ → ℕ → ℕ
  doubleTabResampleSteps : ℕ → ℕ → ℕ → ℕ
  doubleTabEvalSteps : ℕ → ℕ → ℕ
  cuckooMaxEvictions : ℕ → ℕ
  cuckooK : ℕ → ℕ
  cuckooKBound : ℕ
  cuckooSingleHashSpace : ℕ → ℕ
  cuckooHashPairSpace : ℕ → ℕ
  cuckooSpace : ℕ → ℕ
  cuckooSpaceFactor : ℕ
  cuckooResampleSingleSteps : ℕ → ℕ
  cuckooInitSteps : ℕ → ℕ → ℕ
  cuckooEvalHashBound : ℕ
  cuckooGetStepsBound : ℕ
  cuckooGetCharge : ℕ
  cuckooEvictIterBound : ℕ
  cuckooInsertBaseBound : ℕ
  cuckooResampleAtBaseFactor : ℕ
  cuckooRehashAmortizedBound : ℕ
  cuckooInsertCharge : ℕ

/-- Definitional laws for `CuckooPresentation`, each proved by one-step `rfl` in
`HashTablesAbstract.lean`. -/
structure CuckooLaws (K : CuckooPresentation) : Prop where
  regimeThreshold_def : K.regimeThreshold = 2 ^ 320000
  charBits_def : ∀ n_max, K.charBits n_max = (1 + Nat.clog 2 (max n_max 4)) / 2
  tableBits32_def : ∀ n_max, K.tableBits32 n_max = Nat.clog 2 (32 * max n_max 4)
  tableSize32_def : ∀ n_max, K.tableSize32 n_max = 2 ^ K.tableBits32 n_max
  kWiseSpace_def : ∀ n_max k, K.kWiseSpace n_max k = kWiseSpace n_max k
  kWiseInitTableSteps_def : ∀ n_max U M,
    K.kWiseInitTableSteps n_max U M = kWiseInitTableSteps n_max U M
  doubleTabSpace_def : ∀ c d b, K.doubleTabSpace c d b = (c + 1) * d * 2 ^ b
  doubleTabResampleSteps_def : ∀ c d b,
    K.doubleTabResampleSteps c d b = 5 * K.doubleTabSpace c d b + 13
  doubleTabEvalSteps_def : ∀ c d, K.doubleTabEvalSteps c d = (12 * c + 11) * d + 10
  cuckooMaxEvictions_def : ∀ n_max,
    K.cuckooMaxEvictions n_max = 6 * (Nat.clog 2 (max n_max 2) + 2)
  cuckooK_def : ∀ n_max, K.cuckooK n_max = 2 * K.cuckooMaxEvictions n_max + 2
  cuckooKBound_def : K.cuckooKBound = 24 * 160000 + 26
  cuckooSingleHashSpace_def : ∀ n_max,
    K.cuckooSingleHashSpace n_max =
      if n_max < K.regimeThreshold then K.kWiseSpace n_max (K.cuckooK n_max)
      else K.doubleTabSpace 8 64 (K.charBits n_max)
  cuckooHashPairSpace_def : ∀ n_max,
    K.cuckooHashPairSpace n_max = 2 * K.cuckooSingleHashSpace n_max
  cuckooSpace_def : ∀ n_max,
    K.cuckooSpace n_max =
      20 + K.cuckooHashPairSpace n_max + 2 * K.tableSize32 n_max + 2 * n_max
  cuckooSpaceFactor_def :
    K.cuckooSpaceFactor = 20 + 2 * (16 + K.cuckooKBound + 16 * (8 + 1) * 64) + 514
  cuckooResampleSingleSteps_def : ∀ n_max,
    K.cuckooResampleSingleSteps n_max =
      if n_max < K.regimeThreshold then 5 * K.cuckooK n_max + 10
      else K.doubleTabResampleSteps 8 64 (K.charBits n_max)
  cuckooInitSteps_def : ∀ n_max U,
    K.cuckooInitSteps n_max U =
      8 + (6 + 35 +
        (K.kWiseInitTableSteps n_max U (K.tableBits32 n_max) +
          6 * K.cuckooSingleHashSpace n_max + 8) +
        (2 * K.cuckooResampleSingleSteps n_max + 4) + 5)
  cuckooEvalHashBound_def :
    K.cuckooEvalHashBound =
      max (((11 * 100 + 12) * 100 + 30) * K.cuckooKBound + 19)
        (K.doubleTabEvalSteps 8 64) + 4
  cuckooGetStepsBound_def :
    K.cuckooGetStepsBound = 2 * (K.cuckooEvalHashBound + 36) + 31
  cuckooGetCharge_def :
    K.cuckooGetCharge = K.cuckooGetStepsBound + 2
  cuckooEvictIterBound_def :
    K.cuckooEvictIterBound = 2 * (K.cuckooEvalHashBound + 54) + 59
  cuckooInsertBaseBound_def :
    K.cuckooInsertBaseBound = 2 * (K.cuckooEvalHashBound + 35) + 78
  cuckooResampleAtBaseFactor_def :
    K.cuckooResampleAtBaseFactor = max (10 * K.cuckooKBound + 35) (80 * ((8 + 1) * 64) + 63)
  cuckooRehashAmortizedBound_def :
    K.cuckooRehashAmortizedBound =
      3 * K.cuckooEvictIterBound + 2 * K.cuckooResampleAtBaseFactor + 4290 + 1
  cuckooInsertCharge_def :
    K.cuckooInsertCharge =
      2 * (K.cuckooInsertBaseBound + 3 + 3 * K.cuckooEvictIterBound +
        4 * K.cuckooRehashAmortizedBound)

private theorem cuckooSingleHashSpace_eq_of
    (regimeThreshold' : ℕ)
    (charBits' cuckooMaxEvictions' cuckooK' : ℕ → ℕ)
    (kWiseSpace' : ℕ → ℕ → ℕ)
    (doubleTabSpace' : ℕ → ℕ → ℕ → ℕ)
    (cuckooSingleHashSpace' : ℕ → ℕ)
    (hRegime : regimeThreshold' = 2 ^ 320000)
    (hChar : ∀ n_max, charBits' n_max = (1 + Nat.clog 2 (max n_max 4)) / 2)
    (hKW : ∀ n_max k, kWiseSpace' n_max k = kWiseSpace n_max k)
    (hDT : ∀ c d b, doubleTabSpace' c d b = (c + 1) * d * 2 ^ b)
    (hEv : ∀ n_max, cuckooMaxEvictions' n_max = 6 * (Nat.clog 2 (max n_max 2) + 2))
    (hCk : ∀ n_max, cuckooK' n_max = 2 * cuckooMaxEvictions' n_max + 2)
    (hSingle : ∀ n_max, cuckooSingleHashSpace' n_max =
      if n_max < regimeThreshold' then kWiseSpace' n_max (cuckooK' n_max)
      else doubleTabSpace' 8 64 (charBits' n_max))
    (n_max : ℕ) :
    cuckooSingleHashSpace' n_max = CuckooHashing.singleHashSpace 4 n_max := by
  have hReg := hRegime.trans regimeThreshold_eq
  unfold CuckooHashing.singleHashSpace
    Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableSpace
  rw [hSingle, hReg, hKW, kWiseSpace_eq, hCk, hEv, hDT, hChar]
  rfl

private theorem cuckooSpace_eq_of
    (regimeThreshold' : ℕ)
    (charBits' tableBits32' tableSize32' cuckooMaxEvictions' cuckooK' : ℕ → ℕ)
    (kWiseSpace' : ℕ → ℕ → ℕ)
    (doubleTabSpace' : ℕ → ℕ → ℕ → ℕ)
    (cuckooSingleHashSpace' cuckooHashPairSpace' cuckooSpace' : ℕ → ℕ)
    (hRegime : regimeThreshold' = 2 ^ 320000)
    (hChar : ∀ n_max, charBits' n_max = (1 + Nat.clog 2 (max n_max 4)) / 2)
    (hBits : ∀ n_max, tableBits32' n_max = Nat.clog 2 (32 * max n_max 4))
    (hSize : ∀ n_max, tableSize32' n_max = 2 ^ tableBits32' n_max)
    (hKW : ∀ n_max k, kWiseSpace' n_max k = kWiseSpace n_max k)
    (hDT : ∀ c d b, doubleTabSpace' c d b = (c + 1) * d * 2 ^ b)
    (hEv : ∀ n_max, cuckooMaxEvictions' n_max = 6 * (Nat.clog 2 (max n_max 2) + 2))
    (hCk : ∀ n_max, cuckooK' n_max = 2 * cuckooMaxEvictions' n_max + 2)
    (hSingle : ∀ n_max, cuckooSingleHashSpace' n_max =
      if n_max < regimeThreshold' then kWiseSpace' n_max (cuckooK' n_max)
      else doubleTabSpace' 8 64 (charBits' n_max))
    (hPair : ∀ n_max, cuckooHashPairSpace' n_max = 2 * cuckooSingleHashSpace' n_max)
    (hSpace : ∀ n_max, cuckooSpace' n_max =
      20 + cuckooHashPairSpace' n_max + 2 * tableSize32' n_max + 2 * n_max)
    (n_max : ℕ) :
    cuckooSpace' n_max = CuckooHashing.space 4 n_max := by
  have hSingle_eq := cuckooSingleHashSpace_eq_of regimeThreshold' charBits' cuckooMaxEvictions'
    cuckooK' kWiseSpace' doubleTabSpace' cuckooSingleHashSpace'
    hRegime hChar hKW hDT hEv hCk hSingle n_max
  rw [hSpace, hPair, hSingle_eq, hSize, hBits]
  rfl

namespace CuckooPresentation

variable (K : CuckooPresentation) (hK : CuckooLaws K)
include hK

theorem cuckooMaxEvictions_eq (n_max : ℕ) :
    K.cuckooMaxEvictions n_max = CuckooHashing.maxEvictions n_max :=
  hK.cuckooMaxEvictions_def n_max

theorem cuckooK_eq (n_max : ℕ) :
    K.cuckooK n_max = CuckooHashing.cuckooK n_max := by
  rw [hK.cuckooK_def, K.cuckooMaxEvictions_eq hK]
  rfl

theorem cuckooKBound_eq :
    K.cuckooKBound = CuckooHashing.cuckooKBound 4 :=
  hK.cuckooKBound_def

theorem tableBits32_eq_cuckoo (n_max : ℕ) :
    K.tableBits32 n_max = CuckooHashing.tableBits n_max :=
  hK.tableBits32_def n_max

theorem tableSize32_eq_cuckoo (n_max : ℕ) :
    K.tableSize32 n_max = CuckooHashing.tableSize n_max := by
  rw [hK.tableSize32_def, K.tableBits32_eq_cuckoo hK]
  rfl

theorem cuckooSingleHashSpace_eq (n_max : ℕ) :
    K.cuckooSingleHashSpace n_max = CuckooHashing.singleHashSpace 4 n_max :=
  cuckooSingleHashSpace_eq_of K.regimeThreshold K.charBits K.cuckooMaxEvictions K.cuckooK
    K.kWiseSpace K.doubleTabSpace K.cuckooSingleHashSpace
    hK.regimeThreshold_def hK.charBits_def hK.kWiseSpace_def hK.doubleTabSpace_def
    hK.cuckooMaxEvictions_def hK.cuckooK_def hK.cuckooSingleHashSpace_def n_max

theorem cuckooHashPairSpace_eq (n_max : ℕ) :
    K.cuckooHashPairSpace n_max = CuckooHashing.hashPairSpace 4 n_max := by
  rw [hK.cuckooHashPairSpace_def, K.cuckooSingleHashSpace_eq hK]
  rfl

theorem cuckooSpace_eq (n_max : ℕ) :
    K.cuckooSpace n_max = CuckooHashing.space 4 n_max :=
  cuckooSpace_eq_of K.regimeThreshold K.charBits K.tableBits32 K.tableSize32
    K.cuckooMaxEvictions K.cuckooK K.kWiseSpace K.doubleTabSpace
    K.cuckooSingleHashSpace K.cuckooHashPairSpace K.cuckooSpace
    hK.regimeThreshold_def hK.charBits_def hK.tableBits32_def hK.tableSize32_def
    hK.kWiseSpace_def hK.doubleTabSpace_def hK.cuckooMaxEvictions_def hK.cuckooK_def
    hK.cuckooSingleHashSpace_def hK.cuckooHashPairSpace_def hK.cuckooSpace_def n_max

theorem cuckooResampleSingleSteps_eq (n_max : ℕ) :
    K.cuckooResampleSingleSteps n_max = CuckooHashing.resampleSingleSteps 4 n_max := by
  have hReg := hK.regimeThreshold_def.trans regimeThreshold_eq
  unfold CuckooHashing.resampleSingleSteps
  rw [hK.cuckooResampleSingleSteps_def, hReg,
    K.cuckooK_eq hK, hK.doubleTabResampleSteps_def, hK.doubleTabSpace_def, hK.charBits_def]
  rfl

theorem cuckooInitSteps_eq (n_max U : ℕ) :
    K.cuckooInitSteps n_max U = CuckooHashing.spanSteps + CuckooHashing.setupSteps 4 n_max U := by
  rw [hK.cuckooInitSteps_def, hK.kWiseInitTableSteps_def, kWiseInitTableSteps_eq,
    K.tableBits32_eq_cuckoo hK, K.cuckooSingleHashSpace_eq hK,
    K.cuckooResampleSingleSteps_eq hK]
  rfl

theorem cuckooEvalHashBound_eq :
    K.cuckooEvalHashBound = CuckooHashing.evalHashBound 4 := by
  rw [hK.cuckooEvalHashBound_def, K.cuckooKBound_eq hK, hK.doubleTabEvalSteps_def]
  rfl

theorem cuckooGetStepsBound_eq :
    K.cuckooGetStepsBound = CuckooHashing.getStepsBound 4 := by
  rw [hK.cuckooGetStepsBound_def, K.cuckooEvalHashBound_eq hK]
  rfl

theorem cuckooGetCharge_eq :
    K.cuckooGetCharge = CuckooHashing.getChargeBound 4 := by
  rw [hK.cuckooGetCharge_def, K.cuckooGetStepsBound_eq hK]
  rfl

theorem cuckooEvictIterBound_eq :
    K.cuckooEvictIterBound = CuckooHashing.evictIterBound 4 := by
  rw [hK.cuckooEvictIterBound_def, K.cuckooEvalHashBound_eq hK]
  rfl

theorem cuckooInsertBaseBound_eq :
    K.cuckooInsertBaseBound = CuckooHashing.insertBaseBound 4 := by
  rw [hK.cuckooInsertBaseBound_def, K.cuckooEvalHashBound_eq hK]
  rfl

theorem cuckooResampleAtBaseFactor_eq :
    K.cuckooResampleAtBaseFactor = CuckooHashing.resampleAtBaseFactor 4 := by
  rw [hK.cuckooResampleAtBaseFactor_def, K.cuckooKBound_eq hK]
  rfl

theorem cuckooRehashAmortizedBound_eq :
    K.cuckooRehashAmortizedBound = CuckooHashing.rehashAmortizedBound 4 := by
  rw [hK.cuckooRehashAmortizedBound_def, K.cuckooEvictIterBound_eq hK,
    K.cuckooResampleAtBaseFactor_eq hK]
  rfl

theorem cuckooInsertCharge_eq :
    K.cuckooInsertCharge = CuckooHashing.insertChargeBound 4 := by
  rw [hK.cuckooInsertCharge_def, K.cuckooInsertBaseBound_eq hK,
    K.cuckooEvictIterBound_eq hK, K.cuckooRehashAmortizedBound_eq hK]
  rfl

end CuckooPresentation

/-- Across all capacities `n_max : ℕ`, cuckoo hashing at `c_exp = 4` uses at most
`cuckooSpaceFactor * (n_max + 1)` words of memory. -/
theorem cuckooSpace_le
    (regimeThreshold' : ℕ)
    (charBits' tableBits32' tableSize32' cuckooMaxEvictions' cuckooK' : ℕ → ℕ)
    (kWiseSpace' : ℕ → ℕ → ℕ)
    (doubleTabSpace' : ℕ → ℕ → ℕ → ℕ)
    (cuckooKBound' : ℕ)
    (cuckooSingleHashSpace' cuckooHashPairSpace' cuckooSpace' : ℕ → ℕ)
    (cuckooSpaceFactor' : ℕ)
    (hRegime : regimeThreshold' = 2 ^ 320000)
    (hChar : ∀ n_max, charBits' n_max = (1 + Nat.clog 2 (max n_max 4)) / 2)
    (hBits : ∀ n_max, tableBits32' n_max = Nat.clog 2 (32 * max n_max 4))
    (hSize : ∀ n_max, tableSize32' n_max = 2 ^ tableBits32' n_max)
    (hKW : ∀ n_max k, kWiseSpace' n_max k = kWiseSpace n_max k)
    (hDT : ∀ c d b, doubleTabSpace' c d b = (c + 1) * d * 2 ^ b)
    (hEv : ∀ n_max, cuckooMaxEvictions' n_max = 6 * (Nat.clog 2 (max n_max 2) + 2))
    (hK : ∀ n_max, cuckooK' n_max = 2 * cuckooMaxEvictions' n_max + 2)
    (hKB : cuckooKBound' = 24 * 160000 + 26)
    (hSingle : ∀ n_max, cuckooSingleHashSpace' n_max =
      if n_max < regimeThreshold' then kWiseSpace' n_max (cuckooK' n_max)
      else doubleTabSpace' 8 64 (charBits' n_max))
    (hPair : ∀ n_max, cuckooHashPairSpace' n_max = 2 * cuckooSingleHashSpace' n_max)
    (hSpace : ∀ n_max, cuckooSpace' n_max =
      20 + cuckooHashPairSpace' n_max + 2 * tableSize32' n_max + 2 * n_max)
    (hFactor : cuckooSpaceFactor' = 20 + 2 * (16 + cuckooKBound' + 16 * (8 + 1) * 64) + 514)
    (n_max : ℕ) :
    cuckooSpace' n_max ≤ cuckooSpaceFactor' * (n_max + 1) := by
  have hSpace_eq := cuckooSpace_eq_of regimeThreshold' charBits' tableBits32' tableSize32'
    cuckooMaxEvictions' cuckooK' kWiseSpace' doubleTabSpace'
    cuckooSingleHashSpace' cuckooHashPairSpace' cuckooSpace'
    hRegime hChar hBits hSize hKW hDT hEv hK hSingle hPair hSpace n_max
  have hFactor_eq : cuckooSpaceFactor' = CuckooHashing.spaceFactor 4 := by
    rw [hFactor, hKB]
    rfl
  rw [hSpace_eq, hFactor_eq]
  exact CuckooHashing.space_le 4 n_max

/-- For every dictionary operation `o`, the per-operation expected instruction charge of cuckoo
hashing is at most `cuckooInsertCharge`. -/
theorem cuckooOpCharge_le
    (DictOp : ℕ → Type)
    (get : ∀ {U : ℕ}, Fin U → DictOp U)
    (insert : ∀ {U : ℕ}, Fin U → ℕ → DictOp U)
    (dictOp_induction : ∀ {U : ℕ} {motive : DictOp U → Prop},
      (∀ u, motive (get u)) → (∀ u v, motive (insert u v)) → ∀ o, motive o)
    (cuckooEvalHashBound' cuckooGetStepsBound' cuckooGetCharge'
      cuckooEvictIterBound' cuckooInsertBaseBound' cuckooRehashAmortizedBound'
      cuckooInsertCharge' : ℕ)
    (hGetSteps : cuckooGetStepsBound' = 2 * (cuckooEvalHashBound' + 36) + 31)
    (hGetCharge : cuckooGetCharge' = cuckooGetStepsBound' + 2)
    (hInsBase : cuckooInsertBaseBound' = 2 * (cuckooEvalHashBound' + 35) + 78)
    (hInsCharge : cuckooInsertCharge' =
      2 * (cuckooInsertBaseBound' + 3 + 3 * cuckooEvictIterBound' +
        4 * cuckooRehashAmortizedBound'))
    (cuckooOpCharge : ∀ {U : ℕ}, DictOp U → ℕ)
    (hGet : ∀ {U : ℕ} (u : Fin U), cuckooOpCharge (get u) = cuckooGetCharge')
    (hIns : ∀ {U : ℕ} (u : Fin U) (v : ℕ), cuckooOpCharge (insert u v) = cuckooInsertCharge')
    {U : ℕ} (o : DictOp U) :
    cuckooOpCharge o ≤ cuckooInsertCharge' :=
  @dictOp_induction U (fun o => cuckooOpCharge o ≤ cuckooInsertCharge')
    (fun u => by
      rw [hGet]
      omega)
    (fun u v => by
      rw [hIns])
    o

private theorem totalCost_cuckoo {S : Presentation} (P : DictPresentation S)
    (K : CuckooPresentation) (hK : CuckooLaws K)
    (cuckooOpCharge : ∀ {U : ℕ}, P.DictOp U → ℕ)
    (hGet : ∀ {U : ℕ} (u : Fin U), cuckooOpCharge (P.get u) = K.cuckooGetCharge)
    (hIns : ∀ {U : ℕ} (u : Fin U) (v : ℕ), cuckooOpCharge (P.insert u v) = K.cuckooInsertCharge)
    {U V n_max : ℕ} (s : Dictionary.State U) (ops : List (Dictionary.Op U)) :
    (Dictionary.spec U V n_max).totalCost (CuckooHashing.expectedOpCharge 4) s ops =
      ((ops.map P.dictOpOf).map cuckooOpCharge).sum := by
  induction ops generalizing s with
  | nil => rfl
  | cons o os ih =>
    change CuckooHashing.expectedOpCharge 4 s o +
      (Dictionary.spec U V n_max).totalCost (CuckooHashing.expectedOpCharge 4)
        ((Dictionary.spec U V n_max).stepFn s o).1 os =
      cuckooOpCharge (P.dictOpOf o) + ((os.map P.dictOpOf).map cuckooOpCharge).sum
    rw [ih]
    congr 1
    cases o with
    | get u =>
      dsimp only [CuckooHashing.expectedOpCharge, DictPresentation.dictOpOf]
      rw [hGet, K.cuckooGetCharge_eq hK]
    | insert u v =>
      dsimp only [CuckooHashing.expectedOpCharge, DictPresentation.dictOpOf]
      rw [hIns, K.cuckooInsertCharge_eq hK]

private theorem sum_map_cuckooOpCharge_le {S : Presentation} (P : DictPresentation S)
    (K : CuckooPresentation) (hK : CuckooLaws K)
    (cuckooOpCharge : ∀ {U : ℕ}, P.DictOp U → ℕ)
    (hGet : ∀ {U : ℕ} (u : Fin U), cuckooOpCharge (P.get u) = K.cuckooGetCharge)
    (hIns : ∀ {U : ℕ} (u : Fin U) (v : ℕ), cuckooOpCharge (P.insert u v) = K.cuckooInsertCharge)
    {U : ℕ} (ops : List (P.DictOp U)) :
    (ops.map cuckooOpCharge).sum ≤ ops.length * K.cuckooInsertCharge := by
  induction ops with
  | nil => simp
  | cons o os ih =>
    have hle : cuckooOpCharge o ≤ K.cuckooInsertCharge :=
      cuckooOpCharge_le P.DictOp P.get P.insert P.dictOp_induction
        K.cuckooEvalHashBound K.cuckooGetStepsBound K.cuckooGetCharge
        K.cuckooEvictIterBound K.cuckooInsertBaseBound K.cuckooRehashAmortizedBound
        K.cuckooInsertCharge
        hK.cuckooGetStepsBound_def hK.cuckooGetCharge_def
        hK.cuckooInsertBaseBound_def hK.cuckooInsertCharge_def
        cuckooOpCharge hGet hIns o
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc cuckooOpCharge o + (os.map cuckooOpCharge).sum
      _ ≤ K.cuckooInsertCharge + os.length * K.cuckooInsertCharge := Nat.add_le_add hle ih
      _ = (os.length + 1) * K.cuckooInsertCharge := by ring

private theorem decodeOptionNat_eq_ite (n : ℕ) :
    CuckooHashing.decodeOptionNat n = if n = 0 then none else some (n - 1) := by
  cases n <;> rfl

private theorem cuckoo_init_and_steps (w base c_exp n_max U V : ℕ)
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hw : 2 * Cslib.Probability.trinomialDeg U (CuckooHashing.tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + CuckooHashing.space c_exp n_max))
    (hfit_ev : Fits w (CuckooHashing.maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_V : Fits w V)
    {x : Data 19}
    (hx : x.Bounded w) (hfr : x.regs 1 = base)
    (h3 : x.regs 3 = n_max) (h4 : x.regs 4 = U)
    (hz : ∀ a ∈ (Block.mk base (CuckooHashing.space c_exp n_max)).footprint, x.mem a = 0) :
    let C := CuckooHashing.impl w base c_exp n_max U V
      hU hw hfit_end hfit_ev hfit_U hfit_V
    ∃ ν₀ : PMF (CuckooHashing.Seed c_exp n_max U (CuckooHashing.tableBits n_max) × Data 19),
      ExecCodeDist w (CuckooHashing.cuckooCode c_exp n_max).initFresh x
        (ν₀.map Prod.snd) C.initTime ∧
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧
        p.2.regs 0 = base ∧
        p.2.regs 1 = base + CuckooHashing.space c_exp n_max ∧
        Modifies (Block.mk base (CuckooHashing.space c_exp n_max)).footprint x.mem p.2.mem) ∧
      ∀ ops : List (Dictionary.Op U),
        (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops →
        ∃ (ν_final :
            PMF (CuckooHashing.Seed c_exp n_max U (CuckooHashing.tableBits n_max) × Data 19))
          (T_ops : ℝ≥0∞),
          C.ExecStepsOfFn (Dictionary.empty U) ops ν₀ ν_final T_ops ∧
          C.initTime + T_ops ≤
            C.initTime +
              ((Dictionary.spec U V n_max).totalCost (CuckooHashing.expectedOpCharge c_exp)
                (Dictionary.empty U) ops : ℝ≥0∞) := by
  classical
  intro C
  have hd_pos : 0 < Cslib.Probability.trinomialDeg U (CuckooHashing.tableBits n_max) :=
    lt_of_lt_of_le (CuckooHashing.tableBits_pos n_max)
      (Cslib.Probability.le_trinomialDeg U (CuckooHashing.tableBits n_max))
  have hfit_q : Fits w (2 ^ Cslib.Probability.trinomialDeg U (CuckooHashing.tableBits n_max)) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨x₁, ⟨t_span, ht_span, he_span⟩, hm₁, hb₁, hfr₁, h3₁, h4₁⟩ :=
    CuckooHashing.allocSpan_execWithin hfr h3 h4 hfit_end hfit_ev
  have hx₁_bdd : x₁.Bounded w := he_span.bounded hx
  have hz₁ : ∀ a ∈ (Block.mk base (CuckooHashing.space c_exp n_max)).footprint, x₁.mem a = 0 := by
    intro a ha
    rw [hm₁]
    exact hz a ha
  obtain ⟨μ_init, hdist_setup, hseed_setup, hsupp_setup⟩ :=
    CuckooHashing.initSetup_spec (V := V) hx₁_bdd hb₁ hfr₁ h3₁ h4₁ hz₁ hfit_ev hfit_U hfit_q
  let ν₀ : PMF (CuckooHashing.Seed c_exp n_max U (CuckooHashing.tableBits n_max) × Data 19) :=
    μ_init.map fun y =>
      (CuckooHashing.extractSeed (CuckooHashing.hashBase base) c_exp n_max U
        (CuckooHashing.tableBits n_max) y.mem, y)
  have hsnd₀ : ν₀.map Prod.snd = μ_init := by
    dsimp only [ν₀]
    rw [PMF.map_comp]
    exact PMF.map_id _
  have he_init :
      ExecCodeDist w (CuckooHashing.cuckooCode c_exp n_max).initFresh x
        (ν₀.map Prod.snd) C.initTime := by
    rw [hsnd₀]
    have hseq := (ExecCodeDist.of_exec he_span).seq_pure hdist_setup
    refine hseq.mono ?_
    dsimp only [C, CuckooHashing.impl,
      Randomized.StateTransitionImpl.initTime,
      Randomized.StateTransitionImpl.ofFn]
    exact add_le_add (by exact_mod_cast ht_span) le_rfl
  have hE₀ :
      (CuckooHashing.survivingSeeds
        (Θ := CuckooHashing.Seed c_exp n_max U (CuckooHashing.tableBits n_max))
        CuckooHashing.evalHash1 CuckooHashing.evalHash2
        (CuckooHashing.maxEvictions n_max) ([] : List (Fin U))).Nonempty := by
    rw [CuckooHashing.survivingSeeds_nil]
    exact Finset.univ_nonempty
  have hseed₀ : ν₀.map Prod.fst =
      Cslib.Probability.PMF.uniformOfFinset
        (CuckooHashing.survivingSeeds CuckooHashing.evalHash1 CuckooHashing.evalHash2
          (CuckooHashing.maxEvictions n_max) ([] : List (Fin U))) hE₀ := by
    have hfst : ν₀.map Prod.fst =
        CuckooHashing.seedLaw c_exp n_max U (CuckooHashing.tableBits n_max) := by
      dsimp only [ν₀]
      rw [PMF.map_comp]
      exact hseed_setup
    rw [hfst]
    ext θ
    rw [CuckooHashing.seedLaw, Cslib.Probability.PMF.uniformOfFintype_apply,
      Cslib.Probability.PMF.uniformOfFinset_apply]
    simp [CuckooHashing.survivingSeeds_nil]
  have hsupp₀ : ∀ p ∈ ν₀.support,
      p.1 = CuckooHashing.extractSeed (CuckooHashing.hashBase base) c_exp n_max U
        (CuckooHashing.tableBits n_max) p.2.mem ∧
      CuckooHashing.RepWithKeys w base c_exp n_max U V [] (Dictionary.empty U) p.2 := by
    intro p hp
    dsimp only [ν₀] at hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    exact ⟨rfl, (hsupp_setup y hy).2.1⟩
  refine ⟨ν₀, he_init, ?_, ?_⟩
  · intro p hp
    dsimp only [ν₀] at hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    obtain ⟨hfr_y, hrep_y, hmod_y⟩ := hsupp_setup y hy
    rw [hm₁] at hmod_y
    exact ⟨hrep_y.1, hrep_y.2.1, hfr_y, hmod_y⟩
  · intro ops hv
    obtain ⟨ν_final, T_ops, hex_steps, -, -, hamort⟩ :=
      CuckooHashing.cuckoo_steps_expected_amortized w base c_exp n_max U V
        hU hw hfit_end hfit_ev hfit_U hfit_V
        ops ν₀ hv hE₀ hseed₀ hsupp₀
    exact ⟨ν_final, T_ops, hex_steps, add_le_add le_rfl hamort⟩

/-- Headline bridge theorem for Pagh–Rodler cuckoo hashing
(`CuckooHashing.cuckoo_seq_expected_amortized`) at `c_exp = 4`. -/
theorem cuckooHashing (S : Presentation) (hS : Laws S)
    (P : DictPresentation S) (hP : DictLaws S P)
    (regimeThreshold' : ℕ)
    (charBits' tableBits32' tableSize32' : ℕ → ℕ)
    (kWiseSpace' : ℕ → ℕ → ℕ)
    (kWiseInitTableSteps' : ℕ → ℕ → ℕ → ℕ)
    (doubleTabSpace' doubleTabResampleSteps' : ℕ → ℕ → ℕ → ℕ)
    (doubleTabEvalSteps' : ℕ → ℕ → ℕ)
    (cuckooMaxEvictions' cuckooK' : ℕ → ℕ)
    (cuckooKBound' : ℕ)
    (cuckooSingleHashSpace' cuckooHashPairSpace' cuckooSpace' : ℕ → ℕ)
    (cuckooSpaceFactor' : ℕ)
    (cuckooResampleSingleSteps' : ℕ → ℕ)
    (cuckooInitSteps' : ℕ → ℕ → ℕ)
    (cuckooEvalHashBound' cuckooGetStepsBound' cuckooGetCharge'
      cuckooEvictIterBound' cuckooInsertBaseBound' cuckooResampleAtBaseFactor'
      cuckooRehashAmortizedBound' cuckooInsertCharge' : ℕ)
    (hRegime : regimeThreshold' = 2 ^ 320000)
    (hChar : ∀ n_max, charBits' n_max = (1 + Nat.clog 2 (max n_max 4)) / 2)
    (hBits : ∀ n_max, tableBits32' n_max = Nat.clog 2 (32 * max n_max 4))
    (hSize : ∀ n_max, tableSize32' n_max = 2 ^ tableBits32' n_max)
    (hKW : ∀ n_max k, kWiseSpace' n_max k = kWiseSpace n_max k)
    (hKWInit : ∀ n_max U M, kWiseInitTableSteps' n_max U M = kWiseInitTableSteps n_max U M)
    (hDT : ∀ c d b, doubleTabSpace' c d b = (c + 1) * d * 2 ^ b)
    (hDTRes : ∀ c d b, doubleTabResampleSteps' c d b = 5 * doubleTabSpace' c d b + 13)
    (hDTEval : ∀ c d, doubleTabEvalSteps' c d = (12 * c + 11) * d + 10)
    (hEv : ∀ n_max, cuckooMaxEvictions' n_max = 6 * (Nat.clog 2 (max n_max 2) + 2))
    (hCk : ∀ n_max, cuckooK' n_max = 2 * cuckooMaxEvictions' n_max + 2)
    (hKB : cuckooKBound' = 24 * 160000 + 26)
    (hSingle : ∀ n_max, cuckooSingleHashSpace' n_max =
      if n_max < regimeThreshold' then kWiseSpace' n_max (cuckooK' n_max)
      else doubleTabSpace' 8 64 (charBits' n_max))
    (hPair : ∀ n_max, cuckooHashPairSpace' n_max = 2 * cuckooSingleHashSpace' n_max)
    (hSpace : ∀ n_max, cuckooSpace' n_max =
      20 + cuckooHashPairSpace' n_max + 2 * tableSize32' n_max + 2 * n_max)
    (hFactor : cuckooSpaceFactor' = 20 + 2 * (16 + cuckooKBound' + 16 * (8 + 1) * 64) + 514)
    (hResSingle : ∀ n_max, cuckooResampleSingleSteps' n_max =
      if n_max < regimeThreshold' then 5 * cuckooK' n_max + 10
      else doubleTabResampleSteps' 8 64 (charBits' n_max))
    (hInit : ∀ n_max U, cuckooInitSteps' n_max U =
      8 + (6 + 35 +
        (kWiseInitTableSteps' n_max U (tableBits32' n_max) +
          6 * cuckooSingleHashSpace' n_max + 8) +
        (2 * cuckooResampleSingleSteps' n_max + 4) + 5))
    (hEvalBound : cuckooEvalHashBound' =
      max (((11 * 100 + 12) * 100 + 30) * cuckooKBound' + 19)
        (doubleTabEvalSteps' 8 64) + 4)
    (hGetSteps : cuckooGetStepsBound' = 2 * (cuckooEvalHashBound' + 36) + 31)
    (hGetCharge : cuckooGetCharge' = cuckooGetStepsBound' + 2)
    (hEvictIter : cuckooEvictIterBound' = 2 * (cuckooEvalHashBound' + 54) + 59)
    (hInsBase : cuckooInsertBaseBound' = 2 * (cuckooEvalHashBound' + 35) + 78)
    (hResFactor : cuckooResampleAtBaseFactor' =
      max (10 * cuckooKBound' + 35) (80 * ((8 + 1) * 64) + 63))
    (hRehashBound : cuckooRehashAmortizedBound' =
      3 * cuckooEvictIterBound' + 2 * cuckooResampleAtBaseFactor' + 4290 + 1)
    (hInsCharge : cuckooInsertCharge' =
      2 * (cuckooInsertBaseBound' + 3 + 3 * cuckooEvictIterBound' +
        4 * cuckooRehashAmortizedBound'))
    (cuckooOpCharge : ∀ {U : ℕ}, P.DictOp U → ℕ)
    (hGet : ∀ {U : ℕ} (u : Fin U), cuckooOpCharge (P.get u) = cuckooGetCharge')
    (hIns : ∀ {U : ℕ} (u : Fin U) (v : ℕ), cuckooOpCharge (P.insert u v) = cuckooInsertCharge') :
    ∀ (n_max : ℕ),
      ∃ (p_init p_op : List (S.Instr 19)),
        ∀ (U V w base : ℕ),
          U ≤ max n_max 4 ^ 4 →
          2 * trinomialDeg U (tableBits32' n_max) ≤ w →
          base + cuckooSpace' n_max < 2 ^ w →
          cuckooMaxEvictions' n_max < 2 ^ w →
          max U 2 + 1 < 2 ^ w →
          V < 2 ^ w →
          ∀ (reg₀ : Fin 19 → ℕ) (mem₀ : ℕ → ℕ),
            WordBounded w reg₀ mem₀ →
            reg₀ ⟨1, by decide⟩ = base →
            reg₀ ⟨3, by decide⟩ = n_max →
            reg₀ ⟨4, by decide⟩ = U →
            (∀ a, base ≤ a → a < base + cuckooSpace' n_max → mem₀ a = 0) →
            ∃ (Seed : Type) (μ_init : PMF (P.CoupledState Seed 19)),
              P.ExecProgramDist w p_init ⟨2, by decide⟩ reg₀ mem₀
                (μ_init.map P.toRegMem) (cuckooInitSteps' n_max U) ∧
              (∀ p ∈ μ_init.support,
                WordBounded w (P.csReg p) (P.csMem p) ∧
                P.csReg p ⟨0, by decide⟩ = base ∧
                P.csReg p ⟨1, by decide⟩ = base + cuckooSpace' n_max ∧
                UnchangedOutside base (cuckooSpace' n_max) mem₀ (P.csMem p)) ∧
              ∀ ops : List (P.DictOp U),
                P.ValidDictHistory V n_max (DictPresentation.emptyDict U) ops →
                ∃ (μ_final : PMF (P.CoupledState Seed 19)) (T_ops : ℝ≥0∞),
                  P.ExecDictOps w p_op true
                    ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨2, by decide⟩
                    base (cuckooSpace' n_max) (DictPresentation.emptyDict U) ops
                    μ_init μ_final T_ops ∧
                  (cuckooInitSteps' n_max U : ℝ≥0∞) + T_ops ≤
                    ((cuckooInitSteps' n_max U + (ops.map cuckooOpCharge).sum : ℕ) : ℝ≥0∞) ∧
                  (cuckooInitSteps' n_max U : ℝ≥0∞) + T_ops ≤
                    ((cuckooInitSteps' n_max U + ops.length * cuckooInsertCharge' : ℕ) : ℝ≥0∞) := by
  classical
  let K : CuckooPresentation :=
    ⟨regimeThreshold', charBits', tableBits32', tableSize32', kWiseSpace', kWiseInitTableSteps',
      doubleTabSpace', doubleTabResampleSteps', doubleTabEvalSteps', cuckooMaxEvictions',
      cuckooK', cuckooKBound', cuckooSingleHashSpace', cuckooHashPairSpace', cuckooSpace',
      cuckooSpaceFactor', cuckooResampleSingleSteps', cuckooInitSteps', cuckooEvalHashBound',
      cuckooGetStepsBound', cuckooGetCharge', cuckooEvictIterBound', cuckooInsertBaseBound',
      cuckooResampleAtBaseFactor', cuckooRehashAmortizedBound', cuckooInsertCharge'⟩
  have hK : CuckooLaws K :=
    ⟨hRegime, hChar, hBits, hSize, hKW, hKWInit, hDT, hDTRes, hDTEval, hEv, hCk, hKB,
      hSingle, hPair, hSpace, hFactor, hResSingle, hInit, hEvalBound, hGetSteps, hGetCharge,
      hEvictIter, hInsBase, hResFactor, hRehashBound, hInsCharge⟩
  intro n_max
  let Sub := CuckooHashing.cuckooCode 4 n_max
  refine ⟨S.programOf (Sub.initFresh.program ⟨2, by decide⟩),
    S.programOf (Sub.code.program ⟨2, by decide⟩), ?_⟩
  intro U V w base hU hw hfit_end hfit_ev hfit_U hfit_V reg₀ mem₀ hbdd₀ hfr₀ h3₀ h4₀ hz₀
  have hw_lib : 2 * Cslib.Probability.trinomialDeg U (CuckooHashing.tableBits n_max) ≤ w := by
    rwa [← trinomialDeg_eq, ← K.tableBits32_eq_cuckoo hK]
  have hfit_end_lib : Fits w (base + CuckooHashing.space 4 n_max) := by
    rwa [← K.cuckooSpace_eq hK]
  have hfit_ev_lib : Fits w (CuckooHashing.maxEvictions n_max) := by
    rwa [← K.cuckooMaxEvictions_eq hK]
  let C := CuckooHashing.impl w base 4 n_max U V
    hU hw_lib hfit_end_lib hfit_ev_lib hfit_U hfit_V
  have hz_lib : ∀ a ∈ (Block.mk base (CuckooHashing.space 4 n_max)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns, ← K.cuckooSpace_eq hK] at ha
    exact hz₀ a ha.1 ha.2
  obtain ⟨ν₀, he_init, hsupp₀, hsteps⟩ :=
    cuckoo_init_and_steps w base 4 n_max U V
      hU hw_lib hfit_end_lib hfit_ev_lib hfit_U hfit_V
      (x := ⟨reg₀, mem₀⟩) hbdd₀ hfr₀ h3₀ h4₀ hz_lib
  have hinit_c : C.initTime = (K.cuckooInitSteps n_max U : ℝ≥0∞) := by
    rw [K.cuckooInitSteps_eq hK, Nat.cast_add]
    rfl
  rw [hinit_c] at he_init
  have hSpace_eq : cuckooSpace' n_max = CuckooHashing.space 4 n_max :=
    K.cuckooSpace_eq hK n_max
  refine ⟨CuckooHashing.Seed 4 n_max U (CuckooHashing.tableBits n_max),
    ν₀.map (P.coupledStateOf (r := 19)), ?_, ?_, ?_⟩
  · rw [map_coupledStateOf_toRegMem hP (r := 19)]
    exact compile_execCodeDist hS hP ⟨2, by decide⟩ he_init
  · rw [hSpace_eq]
    exact support_coupledStateOf_init hP hsupp₀
  · intro ops hv_abs
    obtain ⟨ops_lib, rfl⟩ := ops_surjective P ops
    have hv_lib : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops_lib :=
      (validDictHistory_map_dictOpOf hP (DictPresentation.emptyDict U) ops_lib).mp hv_abs
    obtain ⟨ν_final, T_ops, hex_steps, hamort⟩ := hsteps ops_lib hv_lib
    have hbound : (K.cuckooInitSteps n_max U : ℝ≥0∞) + T_ops ≤
        ((K.cuckooInitSteps n_max U +
          ((ops_lib.map P.dictOpOf).map cuckooOpCharge).sum : ℕ) : ℝ≥0∞) := by
      rw [hinit_c, totalCost_cuckoo P K hK cuckooOpCharge hGet hIns, ← Nat.cast_add] at hamort
      exact hamort
    refine ⟨ν_final.map (P.coupledStateOf (r := 19)), T_ops, ?_, ?_, ?_⟩
    · rw [hSpace_eq]
      exact compile_execStepsOfFn hS hP C true
        ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨2, by decide⟩
        (fun o d => by
          funext i
          cases o with
          | get u =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.prepareDictRegs_get]
            change (if decide (0 < i.val) then
              if i = ⟨2, by decide⟩ then 0 else if i = ⟨3, by decide⟩ then u.val else 0
            else d.regs i) = _
            fin_cases i <;> rfl
          | insert u v =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.prepareDictRegs_insert]
            change (if decide (0 < i.val) then
              if i = ⟨2, by decide⟩ then 1
              else if i = ⟨3, by decide⟩ then u.val
              else if i = ⟨4, by decide⟩ then v else 0
            else d.regs i) = _
            fin_cases i <;> rfl)
        (fun s o regs hdec => by
          cases o with
          | get u =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.opOutputCorrect_get, ← decodeOptionNat_eq_ite]
            change some (CuckooHashing.decodeOptionNat (regs ⟨2, by decide⟩)) = some (s u) at hdec
            exact Option.some.inj hdec
          | insert u v =>
            dsimp only [DictPresentation.dictOpOf]
            rw [hP.opOutputCorrect_insert]
            trivial)
        hex_steps
    · exact hbound
    · refine hbound.trans ?_
      exact Nat.cast_le.mpr (Nat.add_le_add_left
        (sum_map_cuckooOpCharge_le P K hK cuckooOpCharge hGet hIns _) _)

end ComplexityAbstracts.HashTablesBridge
