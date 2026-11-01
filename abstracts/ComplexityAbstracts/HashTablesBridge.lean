/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.HashFamiliesBridge
import Complexity.Algorithms.WordRAM.Dictionary.ChainedHash
import Complexity.Algorithms.WordRAM.Dictionary.LinearProbing
import Complexity.Algorithms.WordRAM.Dictionary.UniformProbing

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
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.Dictionary
open ComplexityAbstracts.RandomizedWordRAMBridge

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

/-- All registers and memory cells carry `w`-bit machine words (`< 2 ^ w`). -/
def WordBounded {r : ℕ} (w : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ i, reg i < 2 ^ w) ∧ ∀ a, mem a < 2 ^ w

/-- Memory cells outside `[base, base + sp)` are unchanged between `mem` and `mem'`. -/
def UnchangedOutside (base sp : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ∀ a, (a < base ∨ base + sp ≤ a) → mem' a = mem a

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
        DictPresentation.WordBounded w (P.csReg q) (P.csMem q) ∧
        P.OpOutputCorrect outReg s o (P.csReg q) ∧
        DictPresentation.UnchangedOutside base sp (P.csMem p) (P.csMem q)) →
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

/-- Generic transfer of `SubroutineDS.ExecStepsOfFn` to `P.ExecDictOps`. -/
theorem compile_execStepsOfFn {S : Presentation} (hS : Laws S)
    {P : DictPresentation S} (hP : DictLaws S P)
    {r_ds k_init w base U V n_max : ℕ}
    {Sub : SubroutineCode .exact r_ds k_init}
    {params : Fin k_init → ℕ}
    {s₀ : (Dictionary.spec U V n_max).State}
    (C : Randomized.SubroutineDS Sub (Dictionary.spec U V n_max) w base params s₀)
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
  refine @Randomized.SubroutineDS.ExecStepsOfFn.rec .exact r_ds k_init w base Sub
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

theorem chainedSpace_eq (n_max : ℕ) : chainedSpace n_max = ChainedHash.space n_max := rfl

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
            DictPresentation.WordBounded w reg₀ mem₀ →
            reg₀ ⟨6, by decide⟩ = base →
            (∀ a, base ≤ a → a < base + chainedSpace n_max → mem₀ a = 0) →
            ∀ ops : List (P.DictOp U),
              P.ValidDictHistory V n_max (DictPresentation.emptyDict U) ops →
              ∃ (Seed : Type) (T_ops : ℝ≥0∞) (μ_init μ_final : PMF (P.CoupledState Seed 22)),
                P.ExecProgramDist w p_init ⟨10, by decide⟩ reg₀ mem₀
                  (μ_init.map P.toRegMem) 16 ∧
                P.ExecDictOps w p_op true
                  ⟨5, by decide⟩ ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩
                  base (chainedSpace n_max) (DictPresentation.emptyDict U) ops
                  μ_init μ_final T_ops ∧
                (16 : ℝ≥0∞) + T_ops ≤ ((16 + 73 * ops.length : ℕ) : ℝ≥0∞) := by
  intro U n_max
  let Sub := ChainedHash.subroutineCode U n_max
  refine ⟨S.programOf (Sub.initFresh.program ⟨10, by decide⟩),
    S.programOf (Sub.code.program ⟨10, by decide⟩), ?_⟩
  intro V w base hw hfit_space hfit_V reg₀ mem₀ hbdd₀ hfr₀ hz₀ ops hv_abs
  let C := ChainedHash.subroutineDS U V n_max w base hw hfit_space hfit_V
  obtain ⟨ops_lib, rfl⟩ := ops_surjective P ops
  have hv_lib : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops_lib :=
    (validDictHistory_map_dictOpOf hP (DictPresentation.emptyDict U) ops_lib).mp hv_abs
  have hz_lib : ∀ a ∈ (Block.mk base (ChainedHash.space n_max)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns] at ha
    exact hz₀ a ha.1 ha.2
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, -, -, hbound⟩ :=
    ChainedHash.seq_expected_amortized U V n_max w base hw hfit_space hfit_V
      (x := ⟨reg₀, mem₀⟩) ops_lib hbdd₀ hfr₀ hz_lib hv_lib
  have hinit_time : C.initTime = 16 := by
    change (3 : ℝ≥0∞) + 13 = 16
    norm_num
  rw [hinit_time] at he_init hbound
  refine ⟨C.Seed, T_ops, ν₀.map P.coupledStateOf, ν_final.map P.coupledStateOf, ?_, ?_, ?_⟩
  · rw [map_coupledStateOf_toRegMem hP]
    exact compile_execCodeDist hS hP ⟨10, by decide⟩ he_init
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
  · rw [List.length_map]
    simpa only [ChainedHash.chargeVal, Nat.cast_add, Nat.cast_ofNat] using hbound

/-! ## Part 3: Linear Probing with `5`-Wise Independent Hashing (`LinearProbing.lean`) -/

open ComplexityAbstracts.HashFamiliesBridge
  (chunkBits chunkBits_eq trinomialStepLoop trinomialStep trinomialStep_eq
   trinomialDeg trinomialDeg_eq)

/-- Number of `chunkBits n_max`-bit limbs `⌈trinomialDeg U M / chunkBits n_max⌉`. -/
def limbCount (n_max U M : ℕ) : ℕ :=
  (trinomialDeg U M + chunkBits n_max - 1) / chunkBits n_max

theorem limbCount_eq (n_max U M : ℕ) :
    limbCount n_max U M = Cslib.Algorithms.WordRAM.Hashing.KWise.limbCount n_max U M := by
  unfold limbCount Cslib.Algorithms.WordRAM.Hashing.KWise.limbCount
    Cslib.Algorithms.WordRAM.Hashing.KWise.limbCountFromB
  rw [trinomialDeg_eq, chunkBits_eq]

/-- Memory footprint `8 + k + 2 ^ (2 * chunkBits n_max)` of the `k`-wise polynomial hash table. -/
def kWiseSpace (n_max k : ℕ) : ℕ :=
  8 + k + 2 ^ (2 * chunkBits n_max)

theorem kWiseSpace_eq (n_max k : ℕ) :
    kWiseSpace n_max k = Cslib.Algorithms.WordRAM.Hashing.KWise.space n_max k := by
  unfold kWiseSpace Cslib.Algorithms.WordRAM.Hashing.KWise.space
    Cslib.Algorithms.WordRAM.Hashing.KWise.spaceFromB
  rw [chunkBits_eq]

/-- Deterministic lookup-table setup step count for `KWise.initTableCode`. -/
def kWiseInitTableSteps (n_max U M : ℕ) : ℕ :=
  19 * 2 ^ (2 * chunkBits n_max) +
    4 * Nat.log 2 (max n_max 2) +
    5 * Nat.clog 2 (max U 2) +
    5 * trinomialStep U M + 69

theorem kWiseInitTableSteps_eq (n_max U M : ℕ) :
    kWiseInitTableSteps n_max U M =
      Cslib.Algorithms.WordRAM.Hashing.KWise.initTableSteps n_max U M := by
  unfold kWiseInitTableSteps Cslib.Algorithms.WordRAM.Hashing.KWise.initTableSteps
  rw [chunkBits_eq, trinomialStep_eq]

/-- Deterministic instruction budget for `KWise.evalCode k`. -/
def kWiseEvalSteps (n_max U M k : ℕ) : ℕ :=
  ((11 * limbCount n_max U M + 12) * limbCount n_max U M + 30) * k + 19

theorem kWiseEvalSteps_eq (n_max U M k : ℕ) :
    kWiseEvalSteps n_max U M k =
      Cslib.Algorithms.WordRAM.Hashing.KWise.evalSteps n_max U M k := by
  unfold kWiseEvalSteps Cslib.Algorithms.WordRAM.Hashing.KWise.evalSteps
    Cslib.Algorithms.WordRAM.Hashing.KWise.evalStepsFromB
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
      Cslib.Algorithms.WordRAM.Hashing.KWise.limbCount n_max U (LinearProbing.tableLog n_max) ≤
        Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableLimbBound 4 :=
    Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.limbCount_le_provableLimbBound
      hU (lpTableLog_le_clog n_max)
  have hL100 :
      Cslib.Algorithms.WordRAM.Hashing.KWise.limbCount n_max U (LinearProbing.tableLog n_max) ≤
        100 := by
    simpa [Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableLimbBound] using hL
  unfold LinearProbing.charge Cslib.Algorithms.WordRAM.Hashing.KWise.evalSteps
    Cslib.Algorithms.WordRAM.Hashing.KWise.evalStepsFromB lpOpChargeBound
  change ((11 * Cslib.Algorithms.WordRAM.Hashing.KWise.limbCount n_max U
        (LinearProbing.tableLog n_max) + 12) *
      Cslib.Algorithms.WordRAM.Hashing.KWise.limbCount n_max U (LinearProbing.tableLog n_max) +
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
            DictPresentation.WordBounded w reg₀ mem₀ →
            reg₀ ⟨18, by decide⟩ = base →
            (∀ a, base ≤ a → a < base + lpSpace n_max → mem₀ a = 0) →
            ∀ ops : List (P.DictOp U),
              P.ValidDictHistory V n_max (DictPresentation.emptyDict U) ops →
              ∃ (Seed : Type) (T_ops : ℝ≥0∞) (μ_init μ_final : PMF (P.CoupledState Seed 24)),
                P.ExecProgramDist w p_init ⟨2, by decide⟩ reg₀ mem₀
                  (μ_init.map P.toRegMem) (lpInitSteps U n_max) ∧
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
  intro V w base hU hw hfit_space hfit_V reg₀ mem₀ hbdd₀ hfr₀ hz₀ ops hv_abs
  have hw_lib : 2 * Cslib.Probability.trinomialDeg U (LinearProbing.tableLog n_max) ≤ w := by
    rwa [← trinomialDeg_eq, ← lpTableLog_eq]
  have hfit_space_lib : Fits w (base + LinearProbing.space n_max) := by
    rwa [← lpSpace_eq]
  let C := LinearProbing.subroutineDS U V n_max w base hw_lib hfit_space_lib hfit_V
  obtain ⟨ops_lib, rfl⟩ := ops_surjective P ops
  have hv_lib : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops_lib :=
    (validDictHistory_map_dictOpOf hP (DictPresentation.emptyDict U) ops_lib).mp hv_abs
  have hz_lib : ∀ a ∈ (Block.mk base (LinearProbing.space n_max)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns, ← lpSpace_eq] at ha
    exact hz₀ a ha.1 ha.2
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hbound⟩ :=
    LinearProbing.seq_expected_amortized U V n_max w base hw_lib hfit_space_lib hfit_V
      (x₀ := ⟨reg₀, mem₀⟩) hbdd₀ hfr₀ hz_lib ops_lib hv_lib
  rw [← lpInitSteps_eq] at he_init hbound
  refine ⟨LinearProbing.Seed U n_max, T_ops,
    ν₀.map (P.coupledStateOf (r := 24)), ν_final.map (P.coupledStateOf (r := 24)),
    ?_, ?_, ?_, ?_⟩
  · rw [map_coupledStateOf_toRegMem hP (r := 24)]
    exact compile_execCodeDist hS hP ⟨2, by decide⟩ he_init
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
  · rw [List.length_map, lpOpCharge_eq]
    exact hbound
  · rw [List.length_map]
    refine hbound.trans ?_
    rw [← lpOpCharge_eq]
    exact Nat.cast_le.mpr (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (linearProbingCharge_le hU)) _)

/-! ## Part 4: Uniform Probing via Odd-Stride Double Hashing (`UniformProbing.lean`) -/

open ComplexityAbstracts.HashFamiliesBridge
  (regimeThreshold regimeThreshold_eq charBits charBits_eq)

/-- Log₂ of the power-of-2 table size `⌈log₂(32 * max n_max 4)⌉` (`≥ 32 * max n_max 4`). -/
def tableBits32 (n_max : ℕ) : ℕ :=
  Nat.clog 2 (32 * max n_max 4)

theorem tableBits32_eq (n_max : ℕ) : tableBits32 n_max = UniformProbing.bucketBits n_max := rfl

/-- Power-of-2 table size `2 ^ tableBits32 n_max`. -/
def tableSize32 (n_max : ℕ) : ℕ :=
  2 ^ tableBits32 n_max

theorem tableSize32_eq (n_max : ℕ) : tableSize32 n_max = UniformProbing.numBuckets n_max := rfl

/-- Memory footprint `(c + 1) * d * 2 ^ b` of a single Double Tabulation instance. -/
def doubleTabSpace (c d b : ℕ) : ℕ :=
  (c + 1) * d * 2 ^ b

theorem doubleTabSpace_eq (c d b : ℕ) :
    doubleTabSpace c d b =
      Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.space c d b := rfl

/-- Exact instruction count `5 * doubleTabSpace c d b + 13` for resampling a Double Tabulation
instance. -/
def doubleTabResampleSteps (c d b : ℕ) : ℕ :=
  5 * doubleTabSpace c d b + 13

theorem doubleTabResampleSteps_eq (c d b : ℕ) :
    doubleTabResampleSteps c d b =
      Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.resampleSteps c d b := rfl

/-- Exact instruction count `(12 * c + 11) * d + 10` for evaluating a Double Tabulation instance. -/
def doubleTabEvalSteps (c d : ℕ) : ℕ :=
  (12 * c + 11) * d + 10

theorem doubleTabEvalSteps_eq (c d : ℕ) :
    doubleTabEvalSteps c d =
      Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.evalSteps c d := rfl

/-- Memory footprint `doubleTabSpace 8 64 (charBits n_max)` of one Double Tabulation table at
`c_exp = 4`. -/
def upSingleTabSpace (n_max : ℕ) : ℕ :=
  doubleTabSpace 8 64 (charBits n_max)

theorem upSingleTabSpace_eq (n_max : ℕ) :
    upSingleTabSpace n_max = UniformProbing.singleTabSpace 4 n_max := rfl

/-- Total memory footprint `2 * upSingleTabSpace n_max + 3 * tableSize32 n_max` of uniform probing
at `c_exp = 4`. -/
def upSpace (n_max : ℕ) : ℕ :=
  2 * upSingleTabSpace n_max + 3 * tableSize32 n_max

theorem upSpace_eq (n_max : ℕ) : upSpace n_max = UniformProbing.space 4 n_max := rfl

/-- Linear-space factor `32 * (8 + 1) * 64 + 768 = 19200` for uniform probing at `c_exp = 4`. -/
def upSpaceFactor : ℕ :=
  32 * (8 + 1) * 64 + 768

theorem upSpaceFactor_eq : upSpaceFactor = UniformProbing.spaceFactor 4 := rfl

theorem upSpaceFactor_val : upSpaceFactor = 19200 := rfl

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

theorem upHashEvalSteps_val : upHashEvalSteps = 13731 := rfl

/-- Uniform `O(1)` expected per-operation instruction charge
`13 * regimeThreshold + upHashEvalSteps + 8 = 13 * 2 ^ 320000 + 13739` for uniform probing at
`c_exp = 4`. -/
def upOpCharge : ℕ :=
  13 * regimeThreshold + upHashEvalSteps + 8

theorem upOpCharge_eq : upOpCharge = UniformProbing.expectedOpCharge 4 := by
  unfold upOpCharge UniformProbing.expectedOpCharge
  rw [regimeThreshold_eq, upHashEvalSteps_eq]

theorem upOpCharge_val : upOpCharge = 13 * 2 ^ 320000 + 13739 := by
  unfold upOpCharge regimeThreshold
  rw [upHashEvalSteps_val]

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
            DictPresentation.WordBounded w reg₀ mem₀ →
            reg₀ ⟨14, by decide⟩ = base →
            (∀ a, base ≤ a → a < base + upSpace n_max → mem₀ a = 0) →
            ∀ ops : List (P.DictOp U),
              P.ValidDictHistory V n_max (DictPresentation.emptyDict U) ops →
              ∃ (Seed : Type) (T_ops : ℝ≥0∞) (μ_init μ_final : PMF (P.CoupledState Seed 16)),
                P.ExecProgramDist w p_init ⟨12, by decide⟩ reg₀ mem₀
                  (μ_init.map P.toRegMem) (upInitSteps n_max) ∧
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
  intro U V w base hU hfit_space hfit_U hfit_V reg₀ mem₀ hbdd₀ hfr₀ hz₀ ops hv_abs
  have hfit_space_lib : Fits w (base + UniformProbing.space 4 n_max) := by
    rwa [← upSpace_eq]
  let C := UniformProbing.subroutineDS (V := V) hfit_space_lib hfit_U hfit_V hU
  obtain ⟨ops_lib, rfl⟩ := ops_surjective P ops
  have hv_lib : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops_lib :=
    (validDictHistory_map_dictOpOf hP (DictPresentation.emptyDict U) ops_lib).mp hv_abs
  have hz_lib : ∀ a ∈ (Block.mk base (UniformProbing.space 4 n_max)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns, ← upSpace_eq] at ha
    exact hz₀ a ha.1 ha.2
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, -, -, hbound⟩ :=
    UniformProbing.seq_expected_amortized (V := V) hfit_space_lib hfit_U hfit_V hU
      (x := ⟨reg₀, mem₀⟩) ops_lib hbdd₀ hfr₀ hz_lib hv_lib
  have hinit_time : (3 : ℝ≥0∞) + (UniformProbing.setupSteps 4 n_max : ℝ≥0∞) =
      (upInitSteps n_max : ℝ≥0∞) := by
    rw [upInitSteps_eq, Nat.cast_add, Nat.cast_ofNat]
  have hinit_c : C.initTime = (upInitSteps n_max : ℝ≥0∞) := hinit_time
  rw [hinit_c] at he_init hbound
  rw [hinit_time] at hbound
  refine ⟨UniformProbing.Seed 4 n_max, T_ops,
    ν₀.map (P.coupledStateOf (r := 16)), ν_final.map (P.coupledStateOf (r := 16)),
    ?_, ?_, ?_⟩
  · rw [map_coupledStateOf_toRegMem hP (r := 16)]
    exact compile_execCodeDist hS hP ⟨12, by decide⟩ he_init
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
  · have hReg : regimeThreshold' = regimeThreshold := hRegime
    have hHE : upHashEvalSteps' = upHashEvalSteps := hHashEval
    have hCharge_eq : upOpCharge' = UniformProbing.expectedOpCharge 4 := by
      rw [hCharge, hReg, hHE]
      exact upOpCharge_eq
    rw [totalCost_const, ← hCharge_eq] at hbound
    rw [List.length_map, Nat.cast_add]
    exact hbound

end ComplexityAbstracts.HashTablesBridge
