/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.HashFamiliesBridge
import CslibFrontier.DataStructure.Dictionary.WordRAM.Succinct
import CslibFrontier.Probability.PMF.Map

/-!
# Bridge for the Fixed-Capacity Succinct Dynamic Dictionary Formal Abstract

`SuccinctDictionaryAbstract.lean` states the self-contained formal abstract for the fixed-capacity
succinct dynamic dictionary with deletions on the randomized Word-RAM
(`CslibFrontier/DataStructure/Dictionary/WordRAM/Succinct.lean`). The construction combines the
bucket
partition and fingerprint-indexed buckets of `[BenderFarachColtonKuszmaulKuszmaul2024]` (SOSA 2024,
Sections 3–4) with one-round Feistel quotienting (`[ArbitmanNaorSegev2010]`, FOCS 2010, Claim 5.7;
`[BenderConwayFarachColtonKuszmaulTagliavini2023]`, *J. ACM* 70(6):40, 2023;
`arXiv:2109.04548`, Section 7, pp. 31–33). It uses the full-slab and shared tail-pool layout of
`[BenderFarachColtonKuszmaulKuszmaulLiu2022]` (STOC 2022; `arXiv:2111.00602`, Sections 5.2 and 6.1,
Lemma 24) together with this formalization's own micro-bucket chains and slab-hysteresis potential.
Quotients are hashed via two-stage multiply-shift reduction and `3`-wise independent polynomial
hashing with bit-packed multiplication tables (`ReducedKWise.lean`).

This bridge connects the self-contained dynamic dictionary specification, multi-operation
distributional execution relations (`ExecProgramDist`, `ExecDynDictOps`), resource functions, and
headline theorems in `SuccinctDictionaryAbstract.lean` to the library definitions and theorems over
`Cslib.WordRAM.Basis.exact`.
-/

namespace CslibFrontierAbstracts.SuccinctDictionaryBridge

open scoped ENNReal BigOperators
open Finset
open Cslib
open Cslib.WordRAM
open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.WordRAM.Randomized
open CslibFrontierAbstracts.RandomizedWordRAMBridge
open CslibFrontierAbstracts.HashFamiliesBridge.HFPresentation (WordBounded UnchangedOutside)

/-! ## Part 1: Polymorphic Dynamic Dictionary Presentation and Execution Transfer -/

/-- Polymorphic signature of the self-contained dynamic dictionary and multi-operation execution
types in `SuccinctDictionaryAbstract.lean`. -/
structure DynDictPresentation (S : Presentation) where
  DynDictOp : ℕ → Type
  query {U : ℕ} : Fin U → DynDictOp U
  insert {U : ℕ} : Fin U → ℕ → DynDictOp U
  delete {U : ℕ} : Fin U → DynDictOp U
  dynDictOp_induction {U : ℕ} {motive : DynDictOp U → Prop} :
    (∀ u, motive (query u)) → (∀ u v, motive (insert u v)) →
    (∀ u, motive (delete u)) → ∀ o, motive o
  stepDynDict {U : ℕ} : (Fin U → Option ℕ) → DynDictOp U → (Fin U → Option ℕ)
  validDynDictOp {U : ℕ} : ℕ → ℕ → (Fin U → Option ℕ) → DynDictOp U → Prop
  ValidDynDictHistory {U : ℕ} : ℕ → ℕ → (Fin U → Option ℕ) → List (DynDictOp U) → Prop
  RegMem : ℕ → Type
  regMem {r : ℕ} : (Fin r → ℕ) → (ℕ → ℕ) → RegMem r
  rmReg {r : ℕ} : RegMem r → Fin r → ℕ
  rmMem {r : ℕ} : RegMem r → ℕ → ℕ
  CoupledState : Type → ℕ → Type
  coupledState {Seed : Type} {r : ℕ} : Seed → (Fin r → ℕ) → (ℕ → ℕ) → CoupledState Seed r
  csSeed {Seed : Type} {r : ℕ} : CoupledState Seed r → Seed
  csReg {Seed : Type} {r : ℕ} : CoupledState Seed r → Fin r → ℕ
  csMem {Seed : Type} {r : ℕ} : CoupledState Seed r → ℕ → ℕ
  prepareDynDictRegs {r U : ℕ} :
    Fin r → Fin r → Fin r → DynDictOp U → (Fin r → ℕ) → Fin r → ℕ
  OpOutputCorrect {r U : ℕ} :
    Fin r → Fin r → (Fin U → Option ℕ) → DynDictOp U → (Fin r → ℕ) → Prop
  ExecDynDictOps {Seed : Type} {r U : ℕ} :
    ℕ → List (S.Instr r) → Fin r → Fin r → Fin r → Fin r → Fin r → Fin r → ℕ → ℕ →
    (Fin U → Option ℕ) → List (DynDictOp U) →
    PMF (CoupledState Seed r) → PMF (CoupledState Seed r) → ℝ≥0∞ → Prop

namespace DynDictPresentation

variable {S : Presentation} (P : DynDictPresentation S)

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

/-- Translate a library `Dynamic.Op U` to `P.DynDictOp U`. -/
def dynDictOpOf {U : ℕ} : Dynamic.Op U → P.DynDictOp U
  | .query u => P.query u
  | .insert u v => P.insert u v
  | .delete u => P.delete u

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

end DynDictPresentation

/-- Equational specification for a dynamic dictionary presentation `P : DynDictPresentation S`. -/
structure DynDictLaws (S : Presentation) (P : DynDictPresentation S) : Prop where
  stepDynDict_query : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U),
    P.stepDynDict s (P.query u) = s
  stepDynDict_insert : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U) (v : ℕ),
    P.stepDynDict s (P.insert u v) = Function.update s u (some v)
  stepDynDict_delete : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U),
    P.stepDynDict s (P.delete u) = Function.update s u none
  validDynDictOp_query : ∀ {U : ℕ} (V n_max : ℕ) (s : Fin U → Option ℕ) (u : Fin U),
    P.validDynDictOp V n_max s (P.query u) ↔ True
  validDynDictOp_insert : ∀ {U : ℕ} (V n_max : ℕ) (s : Fin U → Option ℕ) (u : Fin U) (v : ℕ),
    P.validDynDictOp V n_max s (P.insert u v) ↔
      ((Finset.univ.filter fun u' => (s u').isSome).card < n_max ∨ (s u).isSome) ∧ v < V
  validDynDictOp_delete : ∀ {U : ℕ} (V n_max : ℕ) (s : Fin U → Option ℕ) (u : Fin U),
    P.validDynDictOp V n_max s (P.delete u) ↔ True
  validDynDictHistory_nil : ∀ {U : ℕ} (V n_max : ℕ) (s : Fin U → Option ℕ),
    P.ValidDynDictHistory V n_max s [] ↔ True
  validDynDictHistory_cons : ∀ {U : ℕ} (V n_max : ℕ) (s : Fin U → Option ℕ)
    (o : P.DynDictOp U) (os : List (P.DynDictOp U)),
    P.ValidDynDictHistory V n_max s (o :: os) ↔
      P.validDynDictOp V n_max s o ∧ P.ValidDynDictHistory V n_max (P.stepDynDict s o) os
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
  prepareDynDictRegs_query : ∀ {r U : ℕ} (tagReg keyReg valReg : Fin r)
    (u : Fin U) (reg : Fin r → ℕ) (i : Fin r),
    P.prepareDynDictRegs tagReg keyReg valReg (P.query u) reg i =
      if i = tagReg then 0
      else if i = keyReg then u.val
      else if i = valReg then 0
      else reg i
  prepareDynDictRegs_insert : ∀ {r U : ℕ} (tagReg keyReg valReg : Fin r)
    (u : Fin U) (v : ℕ) (reg : Fin r → ℕ) (i : Fin r),
    P.prepareDynDictRegs tagReg keyReg valReg (P.insert u v) reg i =
      if i = tagReg then 1
      else if i = keyReg then u.val
      else if i = valReg then v
      else reg i
  prepareDynDictRegs_delete : ∀ {r U : ℕ} (tagReg keyReg valReg : Fin r)
    (u : Fin U) (reg : Fin r → ℕ) (i : Fin r),
    P.prepareDynDictRegs tagReg keyReg valReg (P.delete u) reg i =
      if i = tagReg then 2
      else if i = keyReg then u.val
      else if i = valReg then 0
      else reg i
  opOutputCorrect_query : ∀ {r U : ℕ} (resTagReg resValReg : Fin r) (s : Fin U → Option ℕ)
    (u : Fin U) (reg : Fin r → ℕ),
    P.OpOutputCorrect resTagReg resValReg s (P.query u) reg ↔
      (if reg resTagReg = 0 then none else some (reg resValReg)) = s u
  opOutputCorrect_insert : ∀ {r U : ℕ} (resTagReg resValReg : Fin r) (s : Fin U → Option ℕ)
    (u : Fin U) (v : ℕ) (reg : Fin r → ℕ),
    P.OpOutputCorrect resTagReg resValReg s (P.insert u v) reg ↔ True
  opOutputCorrect_delete : ∀ {r U : ℕ} (resTagReg resValReg : Fin r) (s : Fin U → Option ℕ)
    (u : Fin U) (reg : Fin r → ℕ),
    P.OpOutputCorrect resTagReg resValReg s (P.delete u) reg ↔ True
  execDynDictOps_nil : ∀ {Seed : Type} {r U : ℕ} (w : ℕ) (p_op : List (S.Instr r))
    (tagReg keyReg valReg outReg resTagReg resValReg : Fin r) (base sp : ℕ)
    (s : Fin U → Option ℕ) (μ : PMF (P.CoupledState Seed r)),
    P.ExecDynDictOps w p_op tagReg keyReg valReg outReg resTagReg resValReg base sp s [] μ μ 0
  execDynDictOps_cons : ∀ {Seed : Type} {r U : ℕ} {w : ℕ} {p_op : List (S.Instr r)}
    {tagReg keyReg valReg outReg resTagReg resValReg : Fin r} {base sp : ℕ}
    {s : Fin U → Option ℕ} {o : P.DynDictOp U} {ops : List (P.DynDictOp U)}
    {μ μ_final : PMF (P.CoupledState Seed r)} {T_rest : ℝ≥0∞}
    (T_step : P.CoupledState Seed r → ℝ≥0∞)
    (μ_step : P.CoupledState Seed r → PMF (P.CoupledState Seed r)),
    (∀ p ∈ μ.support,
      P.ExecProgramDist w p_op outReg
        (P.prepareDynDictRegs tagReg keyReg valReg o (P.csReg p)) (P.csMem p)
        ((μ_step p).map P.toRegMem) (T_step p) ∧
      ∀ q ∈ (μ_step p).support,
        WordBounded w (P.csReg q) (P.csMem q) ∧
        P.OpOutputCorrect resTagReg resValReg s o (P.csReg q) ∧
        UnchangedOutside base sp (P.csMem p) (P.csMem q)) →
    P.ExecDynDictOps w p_op tagReg keyReg valReg outReg resTagReg resValReg base sp
      (P.stepDynDict s o) ops (μ.bind μ_step) μ_final T_rest →
    P.ExecDynDictOps w p_op tagReg keyReg valReg outReg resTagReg resValReg base sp
      s (o :: ops) μ μ_final ((∑' p, μ p * T_step p) + T_rest)

/-! ### Correspondence Lemmas for `DynDictPresentation` -/

private theorem dynDictOpOf_surjective {S : Presentation} (P : DynDictPresentation S) {U : ℕ}
    (o : P.DynDictOp U) : ∃ o_lib : Dynamic.Op U, P.dynDictOpOf o_lib = o :=
  P.dynDictOp_induction (motive := fun o => ∃ o_lib, P.dynDictOpOf o_lib = o)
    (fun u => ⟨.query u, rfl⟩) (fun u v => ⟨.insert u v, rfl⟩) (fun u => ⟨.delete u, rfl⟩) o

private theorem ops_surjective {S : Presentation} (P : DynDictPresentation S) {U : ℕ}
    (ops : List (P.DynDictOp U)) :
    ∃ ops_lib : List (Dynamic.Op U), ops_lib.map P.dynDictOpOf = ops := by
  choose f hf using dynDictOpOf_surjective P (U := U)
  refine ⟨ops.map f, ?_⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ops]
  congr 1
  funext o
  exact hf o

private theorem stepDynDict_dynDictOpOf {S : Presentation} {P : DynDictPresentation S}
    (hP : DynDictLaws S P) {U V n_max : ℕ} (s : Fin U → Option ℕ) (o : Dynamic.Op U) :
    P.stepDynDict s (P.dynDictOpOf o) = ((Dynamic.spec U V n_max).stepFn s o).1 := by
  cases o with
  | query u => exact hP.stepDynDict_query s u
  | insert u v => exact hP.stepDynDict_insert s u v
  | delete u => exact hP.stepDynDict_delete s u

private theorem validDynDictOp_dynDictOpOf {S : Presentation} {P : DynDictPresentation S}
    (hP : DynDictLaws S P) {U V n_max : ℕ} (s : Fin U → Option ℕ) (o : Dynamic.Op U) :
    P.validDynDictOp V n_max s (P.dynDictOpOf o) ↔ (Dynamic.spec U V n_max).valid s o := by
  cases o with
  | query u => exact hP.validDynDictOp_query V n_max s u
  | insert u v => exact hP.validDynDictOp_insert V n_max s u v
  | delete u => exact hP.validDynDictOp_delete V n_max s u

private theorem validDynDictHistory_map_dynDictOpOf {S : Presentation} {P : DynDictPresentation S}
    (hP : DynDictLaws S P) {U V n_max : ℕ} (s : Fin U → Option ℕ) (ops : List (Dynamic.Op U)) :
    P.ValidDynDictHistory V n_max s (ops.map P.dynDictOpOf) ↔
      (Dynamic.spec U V n_max).ValidHistory s ops := by
  induction ops generalizing s with
  | nil => exact hP.validDynDictHistory_nil V n_max s
  | cons o os ih =>
    simp only [List.map_cons, hP.validDynDictHistory_cons, validDynDictOp_dynDictOpOf hP,
      stepDynDict_dynDictOpOf hP (V := V) (n_max := n_max), ih]
    rfl

private theorem dataOfRegMem_regMemOf {S : Presentation} {P : DynDictPresentation S}
    (hP : DynDictLaws S P) {r : ℕ} (d : Data r) :
    P.dataOfRegMem (P.regMemOf d) = d := by
  cases d
  simp [DynDictPresentation.dataOfRegMem, DynDictPresentation.regMemOf, hP.rmReg_mk, hP.rmMem_mk]

private theorem regMemOf_dataOfRegMem {S : Presentation} {P : DynDictPresentation S}
    (hP : DynDictLaws S P) {r : ℕ} (q : P.RegMem r) :
    P.regMemOf (P.dataOfRegMem q) = q :=
  hP.regMem_eta q

private theorem pairOfCoupledState_coupledStateOf {S : Presentation} {P : DynDictPresentation S}
    (hP : DynDictLaws S P) {Seed : Type} {r : ℕ} (p : Seed × Data r) :
    P.pairOfCoupledState (P.coupledStateOf p) = p := by
  rcases p with ⟨θ, ⟨reg, mem⟩⟩
  simp [DynDictPresentation.pairOfCoupledState, DynDictPresentation.coupledStateOf,
    hP.csSeed_mk, hP.csReg_mk, hP.csMem_mk]

private theorem map_coupledStateOf_toRegMem {S : Presentation} {P : DynDictPresentation S}
    (hP : DynDictLaws S P) {Seed : Type} {r : ℕ} (ν : PMF (Seed × Data r)) :
    (ν.map P.coupledStateOf).map P.toRegMem = (ν.map Prod.snd).map P.regMemOf := by
  rw [PMF.map_comp, PMF.map_comp]
  refine congrArg (ν.map ·) (funext fun p => ?_)
  rcases p with ⟨θ, ⟨reg, mem⟩⟩
  simp [DynDictPresentation.toRegMem, DynDictPresentation.coupledStateOf,
    DynDictPresentation.regMemOf, hP.csReg_mk, hP.csMem_mk]

private theorem support_coupledStateOf_init {S : Presentation} {P : DynDictPresentation S}
    (hP : DynDictLaws S P) {Seed : Type} {r w base sp : ℕ}
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

/-- Compile any library `ExecCodeDist w c ⟨reg, mem⟩ μ_lib T` to `P.ExecProgramDist`. -/
theorem compile_execCodeDist {S : Presentation} (hS : Laws S)
    {P : DynDictPresentation S} (hP : DynDictLaws S P)
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
    exact Cslib.Probability.PMF.le_map_apply _ S.cfgOf
      (.halted (P.rmReg q outReg) (P.dataOfRegMem q))

/-- Generic transfer of `StateTransitionImpl.ExecStepsOfFn` to `P.ExecDynDictOps`. -/
theorem compile_execStepsOfFn {S : Presentation} (hS : Laws S)
    {P : DynDictPresentation S} (hP : DynDictLaws S P)
    {r_ds k_init w base U V n_max : ℕ}
    {Sub : SubroutineCode .exact r_ds k_init}
    {params : Fin k_init → ℕ}
    {s₀ : (Dynamic.spec U V n_max).State}
    (C : Randomized.StateTransitionImpl Sub (Dynamic.spec U V n_max) w base params s₀)
    (tagReg keyReg valReg outReg resTagReg resValReg : Fin r_ds)
    (hprep : ∀ (o : Dynamic.Op U) (d : Data r_ds),
      (C.toDynamicProgram.prepare o d).regs =
        P.prepareDynDictRegs tagReg keyReg valReg (P.dynDictOpOf o) d.regs)
    (hdec : ∀ (s : Dictionary.State U) (o : Dynamic.Op U) (regs : Fin r_ds → ℕ),
      C.decode o regs = some ((Dynamic.spec U V n_max).stepFn s o).2 →
        P.OpOutputCorrect resTagReg resValReg s (P.dynDictOpOf o) regs)
    {s : (Dynamic.spec U V n_max).State} {ops : List (Dynamic.spec U V n_max).Op}
    {ν ν_final : PMF (C.Seed × Data r_ds)} {T_ops : ℝ≥0∞}
    (hex : C.ExecStepsOfFn s ops ν ν_final T_ops) :
    P.ExecDynDictOps w (S.programOf (Sub.code.program outReg))
      tagReg keyReg valReg outReg resTagReg resValReg base C.space s (ops.map P.dynDictOpOf)
      (ν.map P.coupledStateOf) (ν_final.map P.coupledStateOf) T_ops := by
  refine @Randomized.StateTransitionImpl.ExecStepsOfFn.rec .exact r_ds k_init w base Sub
    (Dynamic.spec U V n_max) params s₀ C (Dynamic.spec U V n_max).stepFn inferInstance
    (fun s ops ν ν_final T_ops _ =>
      P.ExecDynDictOps w (S.programOf (Sub.code.program outReg))
        tagReg keyReg valReg outReg resTagReg resValReg base C.space s (ops.map P.dynDictOpOf)
        (ν.map P.coupledStateOf) (ν_final.map P.coupledStateOf) T_ops)
    (fun s ν =>
      hP.execDynDictOps_nil w _ tagReg keyReg valReg outReg resTagReg resValReg base C.space s
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
  refine hP.execDynDictOps_cons T_step_abs μ_step_abs (fun p_abs hp_abs => ?_) ?_
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
            ⟨P.prepareDynDictRegs tagReg keyReg valReg (P.dynDictOpOf o)
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
  · rw [stepDynDict_dynDictOpOf hP (V := V) (n_max := n_max), hbind_eq]
    exact ih

/-! ## Part 2: Succinct Dynamic Dictionary Resource Functions and Headline Bridge Theorem -/

/-- Exact initialization instruction budget `Succinct.initSteps U n_max + 1`. -/
def succinctInitBudget (U n_max : ℕ) : ℕ :=
  Succinct.initSteps U n_max + 1

/-- Linear upper bound `succinctInitBudget U n_max ≤ 31 * n_max + 1092`. -/
theorem succinctInitBudget_le (U n_max : ℕ) :
    succinctInitBudget U n_max ≤ 31 * n_max + 1092 := by
  unfold succinctInitBudget
  have h := Succinct.initSteps_le U n_max
  omega

/-- Headline bridge theorem for the fixed-capacity succinct dynamic dictionary
(`Succinct.impl` with `initFresh_exec` and `steps_expected_amortized_ofFn`,
`Succinct.initSteps_le`, and `Succinct.space_le_succinctWords`). -/
theorem succinctDynamicDictionary (S : Presentation) (hS : Laws S)
    (P : DynDictPresentation S) (hP : DynDictLaws S P) :
    ∃ (r C_op : ℕ) (hr : 292 ≤ r),
      ∀ (U V w n_max : ℕ),
        ∃ (sp initBudget : ℕ) (p_init p_op : List (S.Instr r)),
          initBudget ≤ 31 * n_max + 1092 ∧
          (0 < w → n_max ≤ U → U < 2 ^ w →
            sp ≤ Dynamic.succinctWords 81 213 U V w n_max) ∧
          ∀ (base : ℕ),
            0 < w →
            n_max ≤ U →
            U < 2 ^ w →
            V < 2 ^ w →
            base + sp < 2 ^ w →
            ∀ (reg₀ : Fin r → ℕ) (mem₀ : ℕ → ℕ),
              WordBounded w reg₀ mem₀ →
              reg₀ ⟨240, by omega⟩ = base →
              (∀ a, base ≤ a → a < base + sp → mem₀ a = 0) →
              ∃ (Seed : Type) (μ_init : PMF (P.CoupledState Seed r)),
                P.ExecProgramDist w p_init ⟨247, by omega⟩ reg₀ mem₀
                  (μ_init.map P.toRegMem) initBudget ∧
                (∀ p ∈ μ_init.support,
                  WordBounded w (P.csReg p) (P.csMem p) ∧
                  P.csReg p ⟨0, by omega⟩ = base ∧
                  P.csReg p ⟨240, by omega⟩ = base + sp ∧
                  UnchangedOutside base sp mem₀ (P.csMem p)) ∧
                ∀ ops : List (P.DynDictOp U),
                  P.ValidDynDictHistory V n_max (DynDictPresentation.emptyDict U) ops →
                  ∃ (μ_final : PMF (P.CoupledState Seed r)) (T_ops : ℝ≥0∞),
                    P.ExecDynDictOps w p_op
                      ⟨244, by omega⟩ ⟨245, by omega⟩ ⟨246, by omega⟩
                      ⟨247, by omega⟩ ⟨252, by omega⟩ ⟨253, by omega⟩
                      base sp (DynDictPresentation.emptyDict U) ops
                      μ_init μ_final T_ops ∧
                    T_ops ≤ ((ops.length * C_op : ℕ) : ℝ≥0∞) := by
  refine ⟨Succinct.rSuccinct, Succinct.chargeVal, Succinct.le_rSuccinct, ?_⟩
  intro U V w n_max
  refine ⟨Succinct.space U V w n_max, succinctInitBudget U n_max,
    S.programOf ((Succinct.subroutineCode U V w n_max).initFresh.program
      Succinct.outReg),
    S.programOf ((Succinct.subroutineCode U V w n_max).code.program
      Succinct.outReg),
    succinctInitBudget_le U n_max,
    fun hw hnU hU => Succinct.space_le_succinctWords hw hnU (le_of_lt hU), ?_⟩
  intro base hw hnU hU hV hfit reg₀ mem₀ hbdd₀ hfr₀ hz₀
  let C := Succinct.impl hw hnU hU hV hfit
  have hz_lib : ∀ a ∈ (Block.mk base (Succinct.space U V w n_max)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns] at ha
    exact hz₀ a ha.1 ha.2
  obtain ⟨ν₀, he_init, hseed₀, hsupp₀⟩ :=
    C.initFresh_exec (x := ⟨reg₀, mem₀⟩) hbdd₀ hfr₀ (fun j => Fin.elim0 j) hz_lib
  have hinit_time : C.initTime = (succinctInitBudget U n_max : ℝ≥0∞) := by
    dsimp only [C, Succinct.impl, Randomized.StateTransitionImpl.ofFn,
      Randomized.StateTransitionImpl.initTime, succinctInitBudget, Succinct.initSteps]
    push_cast
    ring
  rw [hinit_time] at he_init
  refine ⟨C.Seed, ν₀.map P.coupledStateOf, ?_, ?_, ?_⟩
  · rw [map_coupledStateOf_toRegMem hP]
    exact compile_execCodeDist hS hP Succinct.outReg he_init
  · exact support_coupledStateOf_init hP fun p hp =>
      ⟨(hsupp₀ p hp).2.1.1, (hsupp₀ p hp).2.1.2.1, (hsupp₀ p hp).1, (hsupp₀ p hp).2.2.2⟩
  · intro ops hv_abs
    obtain ⟨ops_lib, rfl⟩ := ops_surjective P ops
    have hv_lib : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops_lib :=
      (validDynDictHistory_map_dynDictOpOf hP (DynDictPresentation.emptyDict U) ops_lib).mp hv_abs
    obtain ⟨ν_final, T_ops, hex_steps, -, -, hamort⟩ :=
      C.steps_expected_amortized_ofFn ops_lib ν₀ hv_lib hseed₀ fun p hp => (hsupp₀ p hp).2.1
    refine ⟨ν_final.map P.coupledStateOf, T_ops, ?_, ?_⟩
    · refine compile_execStepsOfFn hS hP C
        Succinct.tagReg Succinct.argUReg
        Succinct.argVReg Succinct.outReg
        Succinct.resTagReg Succinct.resValReg
        (fun o d => ?_) (fun s o regs hdec => ?_) hex_steps
      · funext i
        cases o with
        | query u =>
          dsimp only [DynDictPresentation.dynDictOpOf]
          rw [hP.prepareDynDictRegs_query]
          change (if decide (i = Succinct.tagReg ∨
              i = Succinct.argUReg ∨
              i = Succinct.argVReg) then
            if i = Succinct.tagReg then 0
            else if i = Succinct.argUReg then u.val
            else 0
          else d.regs i) = _
          by_cases h1 : i = Succinct.tagReg
          · subst h1; simp
          · by_cases h2 : i = Succinct.argUReg
            · subst h2; simp [h1]
            · by_cases h3 : i = Succinct.argVReg
              · subst h3; simp [h1, h2]
              · simp [h1, h2, h3]
        | insert u v =>
          dsimp only [DynDictPresentation.dynDictOpOf]
          rw [hP.prepareDynDictRegs_insert]
          change (if decide (i = Succinct.tagReg ∨
              i = Succinct.argUReg ∨
              i = Succinct.argVReg) then
            if i = Succinct.tagReg then 1
            else if i = Succinct.argUReg then u.val
            else if i = Succinct.argVReg then v
            else 0
          else d.regs i) = _
          by_cases h1 : i = Succinct.tagReg
          · subst h1; simp
          · by_cases h2 : i = Succinct.argUReg
            · subst h2; simp [h1]
            · by_cases h3 : i = Succinct.argVReg
              · subst h3; simp [h1, h2]
              · simp [h1, h2, h3]
        | delete u =>
          dsimp only [DynDictPresentation.dynDictOpOf]
          rw [hP.prepareDynDictRegs_delete]
          change (if decide (i = Succinct.tagReg ∨
              i = Succinct.argUReg ∨
              i = Succinct.argVReg) then
            if i = Succinct.tagReg then 2
            else if i = Succinct.argUReg then u.val
            else 0
          else d.regs i) = _
          by_cases h1 : i = Succinct.tagReg
          · subst h1; simp
          · by_cases h2 : i = Succinct.argUReg
            · subst h2; simp [h1]
            · by_cases h3 : i = Succinct.argVReg
              · subst h3; simp [h1, h2]
              · simp [h1, h2, h3]
      · cases o with
        | query u =>
          dsimp only [DynDictPresentation.dynDictOpOf]
          rw [hP.opOutputCorrect_query]
          change (if regs Succinct.resTagReg = 0 then some none
            else some (some (regs Succinct.resValReg))) = some (s u) at hdec
          split_ifs at hdec ⊢ with h0 <;> simp_all
        | insert u v =>
          dsimp only [DynDictPresentation.dynDictOpOf]
          rw [hP.opOutputCorrect_insert]
          trivial
        | delete u =>
          dsimp only [DynDictPresentation.dynDictOpOf]
          rw [hP.opOutputCorrect_delete]
          trivial
    · have hpot₀ : (∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞)) = 0 := by
        refine tsum_eq_zero_iff.mpr fun p => ?_
        by_cases hp : p ∈ ν₀.support
        · have hp0 : Succinct.potential U V w n_max base p.1 p.2 ≤ 0 := (hsupp₀ p hp).2.2.1
          have hp_eq : C.potential p.1 p.2 = 0 := Nat.eq_zero_of_le_zero hp0
          simp [hp_eq]
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul]
      have htot :
          (Dynamic.spec U V n_max).totalCost Succinct.charge
            (Dictionary.empty U) ops_lib =
            ops_lib.length * Succinct.chargeVal :=
        Succinct.totalCost_charge_eq U V n_max (Dictionary.empty U) ops_lib
      change T_ops + ∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞) ≤
        ((Dynamic.spec U V n_max).totalCost Succinct.charge
          (Dictionary.empty U) ops_lib : ℝ≥0∞) +
        ∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞) at hamort
      rw [hpot₀, add_zero, htot] at hamort
      rw [List.length_map]
      exact le_trans le_self_add hamort

end CslibFrontierAbstracts.SuccinctDictionaryBridge
