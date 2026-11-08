/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.HashFamiliesBridge
import CslibFrontier.DataStructure.ApproximateMembership.WordRAM.QuotientFilter

/-!
# Bridge for the Dynamic Approximate-Membership Filter (Quotient Filter) Formal Abstract

`ApproximateMembershipAbstract.lean` states the self-contained formal abstract for the dynamic
approximate-membership filter with deletions implemented by the two-stage quotient filter
(`CslibFrontier/DataStructure/ApproximateMembership/WordRAM/QuotientFilter.lean`), following
`[PaghPaghRao2005]` (SODA 2005) and `[BenderEtAl2012]` (PVLDB 5(11), 2012) combined with
two-stage multiply-shift + `5`-wise polynomial hashing with bit-packed multiplication tables
(`ReducedKWise.lean`).

This bridge connects the self-contained filter specification, multi-operation distributional
execution relation (`ExecProgramDist`, `ExecFilterOps`), resource functions, and headline theorems
in `ApproximateMembershipAbstract.lean` to the library definitions and theorems over
`Cslib.WordRAM.Basis.exact`.
-/

namespace ComplexityAbstracts.ApproximateMembershipBridge

open scoped ENNReal BigOperators
open Finset
open Cslib
open Cslib.WordRAM
open Cslib.DataStructure
open Cslib.DataStructure.ApproximateMembership
open Cslib.DataStructure.ApproximateMembership.QuotientFilter
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.WordRAM.Randomized
open ComplexityAbstracts.RandomizedWordRAMBridge
open ComplexityAbstracts.HashFamiliesBridge (trinomialStepLoop trinomialStepLoop_eq)
open ComplexityAbstracts.HashFamiliesBridge.HFPresentation (WordBounded UnchangedOutside)

/-! ## Part 1: Polymorphic Filter Presentation and Execution Transfer -/

/-- Polymorphic signature of the self-contained approximate-membership filter and multi-operation
execution types in `ApproximateMembershipAbstract.lean`. -/
structure FilterPresentation (S : Presentation) where
  FilterOp : ℕ → Type
  insert {U : ℕ} : Fin U → FilterOp U
  delete {U : ℕ} : Fin U → FilterOp U
  query {U : ℕ} : Fin U → FilterOp U
  filterOp_induction {U : ℕ} {motive : FilterOp U → Prop} :
    (∀ u, motive (insert u)) → (∀ u, motive (delete u)) → (∀ u, motive (query u)) → ∀ o, motive o
  opKey {U : ℕ} : FilterOp U → Fin U
  opTag {U : ℕ} : FilterOp U → ℕ
  stepSet {U : ℕ} : Finset (Fin U) → FilterOp U → Finset (Fin U)
  activeSetFrom {U : ℕ} : Finset (Fin U) → List (FilterOp U) → Finset (Fin U)
  ValidFilterOp {U : ℕ} : ℕ → Finset (Fin U) → FilterOp U → Prop
  ValidFilterSeqFrom {U : ℕ} : ℕ → Finset (Fin U) → List (FilterOp U) → Prop
  FilterContract {U : ℕ} : ℝ≥0∞ → List (FilterOp U) → PMF (List (FilterOp U × Bool)) → Prop
  RegMem : ℕ → Type
  regMem {r : ℕ} : (Fin r → ℕ) → (ℕ → ℕ) → RegMem r
  rmReg {r : ℕ} : RegMem r → Fin r → ℕ
  rmMem {r : ℕ} : RegMem r → ℕ → ℕ
  CoupledOutcome : Type → ℕ → ℕ → Type
  coupledOutcome {Seed : Type} {U r : ℕ} :
    Seed → (Fin r → ℕ) → (ℕ → ℕ) → List (FilterOp U × Bool) → CoupledOutcome Seed U r
  coSeed {Seed : Type} {U r : ℕ} : CoupledOutcome Seed U r → Seed
  coReg {Seed : Type} {U r : ℕ} : CoupledOutcome Seed U r → Fin r → ℕ
  coMem {Seed : Type} {U r : ℕ} : CoupledOutcome Seed U r → ℕ → ℕ
  coTranscript {Seed : Type} {U r : ℕ} : CoupledOutcome Seed U r → List (FilterOp U × Bool)
  prepareFilterRegs {r U : ℕ} : Fin r → Fin r → FilterOp U → (Fin r → ℕ) → Fin r → ℕ
  decodeFilterEntry {r U : ℕ} : Fin r → FilterOp U → (Fin r → ℕ) → FilterOp U × Bool
  ExecFilterOps {Seed : Type} {r U : ℕ} :
    ℕ → List (S.Instr r) → Fin r → Fin r → Fin r → ℕ → ℕ → ℕ →
    List (FilterOp U) →
    PMF (CoupledOutcome Seed U r) → PMF (CoupledOutcome Seed U r) → ℝ≥0∞ → Prop

namespace FilterPresentation

variable {S : Presentation} (P : FilterPresentation S)

/-- No reachable configuration of program `p` from state `s` at word width `w` faults at any time
horizon `T`. -/
def RandFaultFree {r : ℕ} (w : ℕ) (p : List (S.Instr r)) (s : S.State r) : Prop :=
  ∀ T : ℕ, S.evalRand w p T s S.faulted = 0

/-- Project a coupled outcome to its register bank and memory snapshot. -/
def toRegMem {Seed : Type} {U r : ℕ} (p : P.CoupledOutcome Seed U r) : P.RegMem r :=
  P.regMem (P.coReg p) (P.coMem p)

/-- Distributional execution of a compiled Word-RAM program `p` from `(0, reg, mem)`. -/
def ExecProgramDist {r : ℕ} (w : ℕ) (p : List (S.Instr r)) (outReg : Fin r)
    (reg : Fin r → ℕ) (mem : ℕ → ℕ) (μ : PMF (P.RegMem r)) (T : ℝ≥0∞) : Prop :=
  let s := S.state 0 reg mem
  RandFaultFree w p s ∧
  S.expectedTime w p s ≤ T + 1 ∧
  ∀ q : P.RegMem r,
    μ q ≤ ⨆ T_hor : ℕ,
      S.evalRand w p T_hor s (S.halted (P.rmReg q outReg) (P.rmReg q) (P.rmMem q))

/-- Translate a library `ApproximateMembership.Op U` to `P.FilterOp U`. -/
def filterOpOf {U : ℕ} : ApproximateMembership.Op U → P.FilterOp U
  | .insert u => P.insert u
  | .delete u => P.delete u
  | .query u => P.query u

/-- Translate a library transcript entry `Sigma (@ApproximateMembership.Result U)` to
`P.FilterOp U × Bool`. -/
def entryOf {U : ℕ} : Sigma (@ApproximateMembership.Result U) → P.FilterOp U × Bool
  | ⟨.insert u, ()⟩ => (P.insert u, false)
  | ⟨.delete u, ()⟩ => (P.delete u, false)
  | ⟨.query u, b⟩ => (P.query u, b)

/-- Translate a library `Data r` state to `P.RegMem r`. -/
def regMemOf {r : ℕ} (d : Data r) : P.RegMem r :=
  P.regMem d.regs d.mem

/-- Translate `P.RegMem r` back to `Data r`. -/
def dataOfRegMem {r : ℕ} (q : P.RegMem r) : Data r :=
  ⟨P.rmReg q, P.rmMem q⟩

/-- Translate a library `LatentState Seed r` to `P.CoupledOutcome Seed U r` with empty
transcript. -/
def coupledOutcomeOfLatent {Seed : Type} {U r : ℕ}
    (t : LatentState Seed r) : P.CoupledOutcome Seed U r :=
  P.coupledOutcome t.latent t.data.regs t.data.mem []

end FilterPresentation

/-- Equational specification for a filter presentation `P : FilterPresentation S`. -/
structure FilterLaws (S : Presentation) (P : FilterPresentation S) : Prop where
  opKey_insert : ∀ {U : ℕ} (u : Fin U), P.opKey (P.insert u) = u
  opKey_delete : ∀ {U : ℕ} (u : Fin U), P.opKey (P.delete u) = u
  opKey_query : ∀ {U : ℕ} (u : Fin U), P.opKey (P.query u) = u
  opTag_insert : ∀ {U : ℕ} (u : Fin U), P.opTag (P.insert u) = 0
  opTag_delete : ∀ {U : ℕ} (u : Fin U), P.opTag (P.delete u) = 1
  opTag_query : ∀ {U : ℕ} (u : Fin U), P.opTag (P.query u) = 2
  stepSet_insert : ∀ {U : ℕ} (A : Finset (Fin U)) (u : Fin U),
    P.stepSet A (P.insert u) = Insert.insert u A
  stepSet_delete : ∀ {U : ℕ} (A : Finset (Fin U)) (u : Fin U),
    P.stepSet A (P.delete u) = A.erase u
  stepSet_query : ∀ {U : ℕ} (A : Finset (Fin U)) (u : Fin U),
    P.stepSet A (P.query u) = A
  activeSetFrom_nil : ∀ {U : ℕ} (A : Finset (Fin U)),
    P.activeSetFrom A [] = A
  activeSetFrom_cons : ∀ {U : ℕ} (A : Finset (Fin U)) (o : P.FilterOp U) (os : List (P.FilterOp U)),
    P.activeSetFrom A (o :: os) = P.activeSetFrom (P.stepSet A o) os
  validFilterOp_insert : ∀ {U : ℕ} (n : ℕ) (A : Finset (Fin U)) (u : Fin U),
    P.ValidFilterOp n A (P.insert u) ↔ u ∉ A ∧ #A < n
  validFilterOp_delete : ∀ {U : ℕ} (n : ℕ) (A : Finset (Fin U)) (u : Fin U),
    P.ValidFilterOp n A (P.delete u) ↔ u ∈ A
  validFilterOp_query : ∀ {U : ℕ} (n : ℕ) (A : Finset (Fin U)) (u : Fin U),
    P.ValidFilterOp n A (P.query u) ↔ True
  validFilterSeqFrom_nil : ∀ {U : ℕ} (n : ℕ) (A : Finset (Fin U)),
    P.ValidFilterSeqFrom n A [] ↔ True
  validFilterSeqFrom_cons : ∀ {U : ℕ} (n : ℕ) (A : Finset (Fin U))
    (o : P.FilterOp U) (os : List (P.FilterOp U)),
    P.ValidFilterSeqFrom n A (o :: os) ↔
      P.ValidFilterOp n A o ∧ P.ValidFilterSeqFrom n (P.stepSet A o) os
  filterContract_iff : ∀ {U : ℕ} (ε : ℝ≥0∞) (ops : List (P.FilterOp U))
    (μ : PMF (List (P.FilterOp U × Bool))),
    P.FilterContract ε ops μ ↔
      ((∀ tr ∈ μ.support,
          (tr.map Prod.fst = ops) ∧
          ∀ (i : ℕ) (u : Fin U),
            ops[i]? = some (P.query u) →
            u ∈ P.activeSetFrom ∅ (ops.take i) →
            tr[i]? = some (P.query u, true)) ∧
        ∀ (i : ℕ) (u : Fin U),
          ops[i]? = some (P.query u) →
          u ∉ P.activeSetFrom ∅ (ops.take i) →
          μ.toOuterMeasure {tr |
            ops[i]? = some (P.query u) ∧
            u ∉ P.activeSetFrom ∅ (ops.take i) ∧
            tr[i]? = some (P.query u, true)} ≤ ε)
  rmReg_mk : ∀ {r : ℕ} (reg : Fin r → ℕ) (mem : ℕ → ℕ),
    P.rmReg (P.regMem reg mem) = reg
  rmMem_mk : ∀ {r : ℕ} (reg : Fin r → ℕ) (mem : ℕ → ℕ),
    P.rmMem (P.regMem reg mem) = mem
  regMem_eta : ∀ {r : ℕ} (q : P.RegMem r),
    P.regMem (P.rmReg q) (P.rmMem q) = q
  coSeed_mk : ∀ {Seed : Type} {U r : ℕ} (θ : Seed) (reg : Fin r → ℕ) (mem : ℕ → ℕ)
    (tr : List (P.FilterOp U × Bool)),
    P.coSeed (P.coupledOutcome θ reg mem tr) = θ
  coReg_mk : ∀ {Seed : Type} {U r : ℕ} (θ : Seed) (reg : Fin r → ℕ) (mem : ℕ → ℕ)
    (tr : List (P.FilterOp U × Bool)),
    P.coReg (P.coupledOutcome θ reg mem tr) = reg
  coMem_mk : ∀ {Seed : Type} {U r : ℕ} (θ : Seed) (reg : Fin r → ℕ) (mem : ℕ → ℕ)
    (tr : List (P.FilterOp U × Bool)),
    P.coMem (P.coupledOutcome θ reg mem tr) = mem
  coTranscript_mk : ∀ {Seed : Type} {U r : ℕ} (θ : Seed) (reg : Fin r → ℕ) (mem : ℕ → ℕ)
    (tr : List (P.FilterOp U × Bool)),
    P.coTranscript (P.coupledOutcome θ reg mem tr) = tr
  coupledOutcome_eta : ∀ {Seed : Type} {U r : ℕ} (p : P.CoupledOutcome Seed U r),
    P.coupledOutcome (P.coSeed p) (P.coReg p) (P.coMem p) (P.coTranscript p) = p
  prepareFilterRegs_insert : ∀ {r U : ℕ} (keyReg tagReg : Fin r) (u : Fin U)
    (reg : Fin r → ℕ) (i : Fin r),
    P.prepareFilterRegs keyReg tagReg (P.insert u) reg i =
      if i = keyReg then u.val else if i = tagReg then 0 else reg i
  prepareFilterRegs_delete : ∀ {r U : ℕ} (keyReg tagReg : Fin r) (u : Fin U)
    (reg : Fin r → ℕ) (i : Fin r),
    P.prepareFilterRegs keyReg tagReg (P.delete u) reg i =
      if i = keyReg then u.val else if i = tagReg then 1 else reg i
  prepareFilterRegs_query : ∀ {r U : ℕ} (keyReg tagReg : Fin r) (u : Fin U)
    (reg : Fin r → ℕ) (i : Fin r),
    P.prepareFilterRegs keyReg tagReg (P.query u) reg i =
      if i = keyReg then u.val else if i = tagReg then 2 else reg i
  decodeFilterEntry_insert : ∀ {r U : ℕ} (outReg : Fin r) (u : Fin U) (reg : Fin r → ℕ),
    P.decodeFilterEntry outReg (P.insert u) reg = (P.insert u, false)
  decodeFilterEntry_delete : ∀ {r U : ℕ} (outReg : Fin r) (u : Fin U) (reg : Fin r → ℕ),
    P.decodeFilterEntry outReg (P.delete u) reg = (P.delete u, false)
  decodeFilterEntry_query : ∀ {r U : ℕ} (outReg : Fin r) (u : Fin U) (reg : Fin r → ℕ),
    P.decodeFilterEntry outReg (P.query u) reg = (P.query u, decide (reg outReg = 1))
  execFilterOps_nil : ∀ {Seed : Type} {r U : ℕ} (w : ℕ) (p_op : List (S.Instr r))
    (keyReg tagReg outReg : Fin r) (base sp opCharge : ℕ) (μ : PMF (P.CoupledOutcome Seed U r)),
    P.ExecFilterOps w p_op keyReg tagReg outReg base sp opCharge [] μ μ 0
  execFilterOps_cons : ∀ {Seed : Type} {r U : ℕ} {w : ℕ} {p_op : List (S.Instr r)}
    {keyReg tagReg outReg : Fin r} {base sp opCharge : ℕ}
    {o : P.FilterOp U} {ops : List (P.FilterOp U)}
    {μ μ_final : PMF (P.CoupledOutcome Seed U r)} {T_rest : ℝ≥0∞}
    (T_step : P.CoupledOutcome Seed U r → ℝ≥0∞)
    (μ_step : P.CoupledOutcome Seed U r → PMF (P.CoupledOutcome Seed U r)),
    (∀ p ∈ μ.support,
      P.ExecProgramDist w p_op outReg
        (P.prepareFilterRegs keyReg tagReg o (P.coReg p)) (P.coMem p)
        ((μ_step p).map P.toRegMem) (T_step p) ∧
      ∀ q ∈ (μ_step p).support,
        WordBounded w (P.coReg q) (P.coMem q) ∧
        P.coTranscript q = P.coTranscript p ++ [P.decodeFilterEntry outReg o (P.coReg q)] ∧
        UnchangedOutside base sp (P.coMem p) (P.coMem q)) →
    (∑' p, μ p * T_step p) ≤ (opCharge : ℝ≥0∞) →
    P.ExecFilterOps w p_op keyReg tagReg outReg base sp opCharge
      ops (μ.bind μ_step) μ_final T_rest →
    P.ExecFilterOps w p_op keyReg tagReg outReg base sp opCharge
      (o :: ops) μ μ_final ((∑' p, μ p * T_step p) + T_rest)

/-! ### Correspondence Lemmas for `FilterPresentation` -/

private theorem pmf_le_map_apply {α β : Type*} (ν : PMF α) (f : α → β) (a : α) :
    ν a ≤ (ν.map f) (f a) := by
  classical
  rw [PMF.map_apply]
  have h1 : ν a = (if f a = f a then ν a else 0) := by simp
  rw [h1]
  exact le_tsum (fun x => if f a = f x then ν x else 0) a

private theorem opKey_filterOpOf {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U : ℕ} (o : ApproximateMembership.Op U) :
    P.opKey (P.filterOpOf o) = QuotientFilter.opKey o := by
  cases o with
  | insert u => exact hP.opKey_insert u
  | delete u => exact hP.opKey_delete u
  | query u => exact hP.opKey_query u

private theorem opTag_filterOpOf {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U : ℕ} (o : ApproximateMembership.Op U) :
    P.opTag (P.filterOpOf o) = QuotientFilter.opTag o := by
  cases o with
  | insert u => exact hP.opTag_insert u
  | delete u => exact hP.opTag_delete u
  | query u => exact hP.opTag_query u

private theorem filterOpOf_injective {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U : ℕ} :
    Function.Injective (P.filterOpOf (U := U)) := by
  intro o₁ o₂ h
  have hkey : QuotientFilter.opKey o₁ = QuotientFilter.opKey o₂ := by
    rw [← opKey_filterOpOf hP, ← opKey_filterOpOf hP, h]
  have htag : QuotientFilter.opTag o₁ = QuotientFilter.opTag o₂ := by
    rw [← opTag_filterOpOf hP, ← opTag_filterOpOf hP, h]
  cases o₁ <;> cases o₂ <;> dsimp only [QuotientFilter.opKey, QuotientFilter.opTag] at hkey htag
  · exact congrArg ApproximateMembership.Op.insert hkey
  · omega
  · omega
  · omega
  · exact congrArg ApproximateMembership.Op.delete hkey
  · omega
  · omega
  · omega
  · exact congrArg ApproximateMembership.Op.query hkey

private theorem filterOpOf_surjective {S : Presentation} (P : FilterPresentation S) {U : ℕ}
    (o : P.FilterOp U) : ∃ o_lib : ApproximateMembership.Op U, P.filterOpOf o_lib = o :=
  P.filterOp_induction (motive := fun o => ∃ o_lib, P.filterOpOf o_lib = o)
    (fun u => ⟨.insert u, rfl⟩) (fun u => ⟨.delete u, rfl⟩) (fun u => ⟨.query u, rfl⟩) o

private theorem ops_surjective {S : Presentation} (P : FilterPresentation S) {U : ℕ}
    (ops : List (P.FilterOp U)) :
    ∃ ops_lib : List (ApproximateMembership.Op U), ops_lib.map P.filterOpOf = ops := by
  choose f hf using filterOpOf_surjective P (U := U)
  refine ⟨ops.map f, ?_⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ops]
  congr 1
  funext o
  exact hf o

private theorem stepSet_filterOpOf {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U : ℕ} (A : Finset (Fin U)) (o : ApproximateMembership.Op U) :
    P.stepSet A (P.filterOpOf o) = ApproximateMembership.stepSet A o := by
  cases o with
  | insert u => exact hP.stepSet_insert A u
  | delete u => exact hP.stepSet_delete A u
  | query u => exact hP.stepSet_query A u

private theorem activeSetFrom_map_filterOpOf {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U : ℕ} (A : Finset (Fin U)) (ops : List (ApproximateMembership.Op U)) :
    P.activeSetFrom A (ops.map P.filterOpOf) = ApproximateMembership.activeSetFrom A ops := by
  induction ops generalizing A with
  | nil => exact hP.activeSetFrom_nil A
  | cons o os ih =>
    simp only [List.map_cons, hP.activeSetFrom_cons, stepSet_filterOpOf hP, ih]
    rfl

private theorem validFilterOp_filterOpOf {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U : ℕ} (n : ℕ) (A : Finset (Fin U)) (o : ApproximateMembership.Op U) :
    P.ValidFilterOp n A (P.filterOpOf o) ↔ ApproximateMembership.ValidOp n A o := by
  cases o with
  | insert u => exact hP.validFilterOp_insert n A u
  | delete u => exact hP.validFilterOp_delete n A u
  | query u => exact hP.validFilterOp_query n A u

private theorem validFilterSeqFrom_map_filterOpOf {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U : ℕ} (n : ℕ) (A : Finset (Fin U))
    (ops : List (ApproximateMembership.Op U)) :
    P.ValidFilterSeqFrom n A (ops.map P.filterOpOf) ↔
      ApproximateMembership.ValidOpSeqFrom n A ops := by
  induction ops generalizing A with
  | nil => exact hP.validFilterSeqFrom_nil n A
  | cons o os ih =>
    simp only [List.map_cons, hP.validFilterSeqFrom_cons, validFilterOp_filterOpOf hP,
      stepSet_filterOpOf hP, ih]
    rfl

private theorem entryOf_fst {S : Presentation} (P : FilterPresentation S) {U : ℕ}
    (e : Sigma (@ApproximateMembership.Result U)) :
    (P.entryOf e).1 = P.filterOpOf e.1 := by
  rcases e with ⟨o, res⟩
  cases o <;> cases res <;> rfl

private theorem entryOf_eq_query_true_iff {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U : ℕ} (e : Sigma (@ApproximateMembership.Result U)) (u : Fin U) :
    P.entryOf e = (P.query u, true) ↔ e = ⟨.query u, true⟩ := by
  rcases e with ⟨o, res⟩
  cases o with
  | insert u' =>
    cases res
    dsimp only [FilterPresentation.entryOf]
    simp
  | delete u' =>
    cases res
    dsimp only [FilterPresentation.entryOf]
    simp
  | query u' =>
    have hinj : P.query u' = P.query u ↔ u' = u := by
      refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
      have h' : P.filterOpOf (.query u') = P.filterOpOf (.query u) := h
      exact ApproximateMembership.Op.query.inj (filterOpOf_injective hP h')
    dsimp only [FilterPresentation.entryOf]
    rw [Prod.ext_iff, hinj]
    constructor
    · rintro ⟨rfl, rfl⟩
      rfl
    · intro h
      cases h
      exact ⟨rfl, rfl⟩

private theorem filterContract_of_spec_contract {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U n : ℕ} {ε : ℝ≥0∞}
    {ops_lib : List (ApproximateMembership.Op U)}
    {μ_lib : PMF (List (ApproximateMembership.Label U))}
    (hcontract : (ApproximateMembership.spec U n ε).Contract ops_lib μ_lib) :
    P.FilterContract ε (ops_lib.map P.filterOpOf)
      (μ_lib.map fun tr => tr.map P.entryOf) := by
  rw [hP.filterContract_iff]
  obtain ⟨hsupp_lib, hfp_lib⟩ := hcontract
  refine ⟨?_, ?_⟩
  · intro tr htr
    rw [PMF.mem_support_map_iff] at htr
    obtain ⟨tr_lib, htr_lib, rfl⟩ := htr
    obtain ⟨hmatch_lib, hnofn_lib⟩ := hsupp_lib tr_lib htr_lib
    refine ⟨?_, ?_⟩
    · rw [List.map_map]
      have hcomp : (Prod.fst ∘ P.entryOf (U := U)) = P.filterOpOf ∘ Sigma.fst := by
        funext e
        exact entryOf_fst P e
      rw [hcomp, ← List.map_map, hmatch_lib]
    · intro i u hq hu
      rw [List.getElem?_map] at hq ⊢
      have hq_lib : ops_lib[i]? = some (.query u) := by
        cases h : ops_lib[i]? with
        | none => simp [h] at hq
        | some o =>
          simp only [h, Option.map_some, Option.some.injEq] at hq
          exact congrArg some (filterOpOf_injective hP hq)
      obtain ⟨hi_lt, -⟩ := List.getElem?_eq_some_iff.mp hq_lib
      rw [← List.map_take, activeSetFrom_map_filterOpOf hP] at hu
      have htr_i := hnofn_lib i hi_lt u hq_lib hu
      rw [htr_i]
      rfl
  · intro i u hq hu
    have hq_lib : ops_lib[i]? = some (.query u) := by
      rw [List.getElem?_map] at hq
      cases h : ops_lib[i]? with
      | none => simp [h] at hq
      | some o =>
        simp only [h, Option.map_some, Option.some.injEq] at hq
        exact congrArg some (filterOpOf_injective hP hq)
    obtain ⟨hi_lt, -⟩ := List.getElem?_eq_some_iff.mp hq_lib
    have hu_lib : u ∉ ApproximateMembership.activeSetBefore ops_lib i := by
      rw [← List.map_take, activeSetFrom_map_filterOpOf hP] at hu
      exact hu
    have hbound := hfp_lib i hi_lt u hq_lib hu_lib
    rw [PMF.toOuterMeasure_map_apply]
    have hpre :
        ((fun tr : List (ApproximateMembership.Label U) => tr.map P.entryOf) ⁻¹'
          {tr | (ops_lib.map P.filterOpOf)[i]? = some (P.query u) ∧
            u ∉ P.activeSetFrom ∅ ((ops_lib.map P.filterOpOf).take i) ∧
            tr[i]? = some (P.query u, true)}) =
          {tr_lib | ApproximateMembership.FalsePositiveAt tr_lib i u} := by
      ext tr_lib
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, ApproximateMembership.FalsePositiveAt,
        hq, hu, not_false_eq_true, true_and, List.getElem?_map]
      cases h : tr_lib[i]? with
      | none => simp
      | some e =>
        simp only [Option.map_some, Option.some.injEq]
        exact entryOf_eq_query_true_iff hP e u
    rw [hpre]
    exact hbound

private theorem dataOfRegMem_regMemOf {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {r : ℕ} (d : Data r) :
    P.dataOfRegMem (P.regMemOf d) = d := by
  cases d
  simp [FilterPresentation.dataOfRegMem, FilterPresentation.regMemOf, hP.rmReg_mk, hP.rmMem_mk]

private theorem regMemOf_dataOfRegMem {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {r : ℕ} (q : P.RegMem r) :
    P.regMemOf (P.dataOfRegMem q) = q :=
  hP.regMem_eta q

/-- Compile any library `ExecCodeDist w c ⟨reg, mem⟩ μ_lib T` to `P.ExecProgramDist`. -/
theorem compile_execCodeDist {S : Presentation} (hS : Laws S)
    {P : FilterPresentation S} (hP : FilterLaws S P)
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

/-! ## Part 2: Resource Functions and Space Bounds for the Two-Stage Quotient Filter -/

/-- Effective capacity `min n (2 ^ w₀)`. -/
def qfEffCap (w₀ n : ℕ) : ℕ :=
  min n (2 ^ w₀)

theorem qfEffCap_eq (w₀ n : ℕ) : qfEffCap w₀ n = QuotientFilter.effCap w₀ n := rfl

/-- Quotient bit-width `⌈log₂(max (8 * min n (2 ^ w₀)) 8)⌉`. -/
def qfQuotBits (w₀ n : ℕ) : ℕ :=
  Nat.clog 2 (max (8 * qfEffCap w₀ n) 8)

theorem qfQuotBits_eq (w₀ n : ℕ) : qfQuotBits w₀ n = QuotientFilter.quotBits w₀ n := rfl

/-- Remainder bit-width `min w₀ (k + 1)`. -/
def qfRemBits (w₀ k : ℕ) : ℕ :=
  min w₀ (k + 1)

theorem qfRemBits_eq (w₀ k : ℕ) : qfRemBits w₀ k = QuotientFilter.remBits w₀ k := rfl

/-- Log₂ of the number of `d`-bit entries packed per `w`-bit word in a `2 ^ b`-slot array. -/
def qfSlotPackShift (b d w : ℕ) : ℕ :=
  min b (Nat.log 2 (w / (2 * d)))

theorem qfSlotPackShift_eq (b d w : ℕ) :
    qfSlotPackShift b d w = QuotientFilter.slotPackShift b d w := rfl

/-- Number of `w`-bit words `2 ^ (b - qfSlotPackShift b d w)` used by a `2 ^ b`-slot packed array
of `d`-bit entries. -/
def qfPackedWords (b d w : ℕ) : ℕ :=
  2 ^ (b - qfSlotPackShift b d w)

theorem qfPackedWords_eq (b d w : ℕ) :
    qfPackedWords b d w = QuotientFilter.packedWords b d w := rfl

/-- Target bit-width `max (min w₀ (3 * b)) (max b' 1)` for the second-stage trinomial field. -/
def qfReducedTargetBits (w₀ b b' : ℕ) : ℕ :=
  max (min w₀ (3 * b)) (max b' 1)

theorem qfReducedTargetBits_eq (w₀ b b' : ℕ) :
    qfReducedTargetBits w₀ b b' = Cslib.Probability.reducedTargetBits w₀ b b' := rfl

/-- Trinomial step parameter `t` for reduced `min w₀ (3 * b)`-bit keys and `b'`-bit outputs. -/
def qfReducedStep (w₀ b b' : ℕ) : ℕ :=
  let B := qfReducedTargetBits w₀ b b'
  trinomialStepLoop B B

theorem qfReducedStep_eq (w₀ b b' : ℕ) :
    qfReducedStep w₀ b b' = Cslib.Probability.reducedTrinomialStep w₀ b b' :=
  trinomialStepLoop_eq _ _ le_rfl

/-- Limb bit-width `c = 3 ^ (t - 3)` for trinomial step parameter `t`. -/
def qfReducedChunkBits (t : ℕ) : ℕ :=
  3 ^ (t - 3)

theorem qfReducedChunkBits_eq (t : ℕ) :
    qfReducedChunkBits t = Cslib.Probability.reducedChunkBits t := rfl

/-- Full-field limb count `L = 2 * 3 ^ min t 3 ≤ 54` for trinomial step parameter `t`. -/
def qfReducedLimbCount (t : ℕ) : ℕ :=
  2 * 3 ^ min t 3

theorem qfReducedLimbCount_eq (t : ℕ) :
    qfReducedLimbCount t = Cslib.Probability.reducedLimbCount t := rfl

/-- Log₂ of the number of `2 * c`-bit entries packed into each `w`-bit word. -/
def qfReducedPackShift (t w : ℕ) : ℕ :=
  min (2 * qfReducedChunkBits t) (Nat.log 2 (w / (2 * qfReducedChunkBits t)))

theorem qfReducedPackShift_eq (t w : ℕ) :
    qfReducedPackShift t w = Cslib.Probability.reducedPackShift t w := rfl

/-- Number of machine words `2 ^ (2 * c - p)` occupied by the bit-packed Four-Russians table. -/
def qfReducedTableWords (t w : ℕ) : ℕ :=
  2 ^ (2 * qfReducedChunkBits t - qfReducedPackShift t w)

theorem qfReducedTableWords_eq (t w : ℕ) :
    qfReducedTableWords t w = Cslib.Probability.reducedTableWords t w := rfl

/-- Number of seed words `1 + k * L` for the two-stage `k`-wise polynomial hash. -/
def qfReducedSeedWords (w₀ b b' k : ℕ) : ℕ :=
  1 + k * qfReducedLimbCount (qfReducedStep w₀ b b')

theorem qfReducedSeedWords_eq (w₀ b b' k : ℕ) :
    qfReducedSeedWords w₀ b b' k = ReducedKWise.seedWords w₀ b b' k := by
  unfold qfReducedSeedWords ReducedKWise.seedWords
  rw [qfReducedStep_eq, qfReducedLimbCount_eq]

/-- Memory footprint (in words) of the two-stage `k`-wise polynomial hash block. -/
def qfReducedKWiseSpace (w w₀ b b' k : ℕ) : ℕ :=
  qfReducedSeedWords w₀ b b' k + qfReducedTableWords (qfReducedStep w₀ b b') w

theorem qfReducedKWiseSpace_eq (w w₀ b b' k : ℕ) :
    qfReducedKWiseSpace w w₀ b b' k = ReducedKWise.space w w₀ b b' k := by
  unfold qfReducedKWiseSpace ReducedKWise.space ReducedKWise.tableWords
  rw [qfReducedSeedWords_eq, qfReducedStep_eq, qfReducedTableWords_eq]

/-- Total memory footprint (in machine words) of the two-stage quotient filter with error exponent
`k`. -/
def qfSpace (w w₀ n k : ℕ) : ℕ :=
  let b := qfQuotBits w₀ n
  let f := qfRemBits w₀ k
  qfReducedKWiseSpace w w₀ b b 5 + 1 + 3 * qfPackedWords b 1 w + qfPackedWords b f w

theorem qfSpace_eq (w w₀ n k : ℕ) :
    qfSpace w w₀ n k = QuotientFilter.space w w₀ n k := by
  unfold qfSpace QuotientFilter.space
  dsimp only
  rw [qfQuotBits_eq, qfRemBits_eq, qfReducedKWiseSpace_eq, qfPackedWords_eq, qfPackedWords_eq]

/-- Error-exponent selector `max 1 ⌈log₂ ⌈ε⁻¹.toNNReal⌉₊⌉` for false-positive target `ε : ℝ≥0∞`. -/
noncomputable def epsLog (ε : ℝ≥0∞) : ℕ :=
  max 1 (Nat.clog 2 ⌈ε⁻¹.toNNReal⌉₊)

theorem epsLog_eq (ε : ℝ≥0∞) :
    epsLog ε = QuotientFilter.epsLog ε := rfl

/-- Total memory footprint `qfSpace w w₀ n (epsLog ε)` (in machine words) for false-positive
target `ε`. -/
noncomputable def qfSpaceOfEps (w w₀ n : ℕ) (ε : ℝ≥0∞) : ℕ :=
  qfSpace w w₀ n (epsLog ε)

theorem qfSpaceOfEps_eq (w w₀ n : ℕ) (ε : ℝ≥0∞) :
    qfSpaceOfEps w w₀ n ε =
      QuotientFilter.space w w₀ n (QuotientFilter.epsLog ε) := by
  unfold qfSpaceOfEps
  rw [qfSpace_eq, epsLog_eq]

/-- Space bound `qfSpace w w₀ n k ≤ 640 * ((n * k + w - 1) / w + 1)` across all `n ≥ 1`, `k ≥ 1`,
`0 < w₀`, `2 * w₀ ≤ w`, and `qfQuotBits w₀ n ≤ w`. -/
theorem qfSpace_le {w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hb : qfQuotBits w₀ n ≤ w)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    qfSpace w w₀ n k ≤ 640 * ((n * k + w - 1) / w + 1) := by
  rw [qfSpace_eq]
  exact QuotientFilter.space_le hw₀_pos hw hb hn hk

/-- Space bound `qfSpaceOfEps w w₀ n ε ≤ 640 * ((n * epsLog ε + w - 1) / w + 1)` across all
`n ≥ 1`, `0 < w₀`, `2 * w₀ ≤ w`, and `qfQuotBits w₀ n ≤ w`. -/
theorem qfSpaceOfEps_le {w w₀ n : ℕ} {ε : ℝ≥0∞}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hb : qfQuotBits w₀ n ≤ w)
    (hn : 1 ≤ n) :
    qfSpaceOfEps w w₀ n ε ≤ 640 * ((n * epsLog ε + w - 1) / w + 1) := by
  rw [qfSpaceOfEps_eq, epsLog_eq]
  exact QuotientFilter.space_le hw₀_pos hw hb hn (QuotientFilter.one_le_epsLog ε)

/-- Instruction budget for initializing the bit-packed lookup table of the two-stage `k`-wise hash.
-/
def qfReducedInitTableSteps (w₀ b b' : ℕ) : ℕ :=
  31 * 2 ^ (2 * qfReducedChunkBits (qfReducedStep w₀ b b')) + 13

theorem qfReducedInitTableSteps_eq (w₀ b b' : ℕ) :
    qfReducedInitTableSteps w₀ b b' = ReducedKWise.initTableSteps w₀ b b' := by
  unfold qfReducedInitTableSteps ReducedKWise.initTableSteps
  rw [qfReducedStep_eq, qfReducedChunkBits_eq]

/-- Expected instruction count for fresh initialization of the two-stage quotient filter. -/
def qfInitSteps (w₀ n : ℕ) : ℕ :=
  let b := qfQuotBits w₀ n
  3 + (qfReducedInitTableSteps w₀ b b + (5 * qfReducedSeedWords w₀ b b 5 + 13 + 5))

theorem qfInitSteps_eq (w₀ n : ℕ) :
    qfInitSteps w₀ n = 3 + QuotientFilter.setupSteps w₀ n := by
  unfold qfInitSteps QuotientFilter.setupSteps ReducedKWise.resampleSteps
  dsimp only
  rw [qfQuotBits_eq, qfReducedInitTableSteps_eq, qfReducedSeedWords_eq]

/-! ## Part 3: Multi-Operation Execution and Headline Theorem Transfer -/

private theorem execProgramDist_congr {S : Presentation} (P : FilterPresentation S)
    {r w : ℕ} {p : List (S.Instr r)} {outReg : Fin r}
    {reg₁ reg₂ : Fin r → ℕ} {mem₁ mem₂ : ℕ → ℕ}
    {μ₁ μ₂ : PMF (P.RegMem r)} {T₁ T₂ : ℝ≥0∞}
    (hreg : reg₁ = reg₂) (hmem : mem₁ = mem₂) (hμ : μ₁ = μ₂) (hT : T₁ = T₂)
    (h : P.ExecProgramDist w p outReg reg₁ mem₁ μ₁ T₁) :
    P.ExecProgramDist w p outReg reg₂ mem₂ μ₂ T₂ := by
  subst hreg hmem hμ hT
  exact h

private theorem prepare_regs_eq {S : Presentation} {P : FilterPresentation S}
    (hP : FilterLaws S P) {U w w₀ n k : ℕ} (o : ApproximateMembership.Op U) (d : Data rQF) :
    (((QuotientFilter.subroutineCode w w₀ n k).toDynamicProgram
      QuotientFilter.encode QuotientFilter.decode).prepare o d).regs =
      P.prepareFilterRegs (qfReg 1) (qfReg 247) (P.filterOpOf o) d.regs := by
  funext i
  cases o with
  | insert u =>
    dsimp only [FilterPresentation.filterOpOf]
    rw [hP.prepareFilterRegs_insert]
    change (if QuotientFilter.inputReg i then QuotientFilter.encode (.insert u) i
      else d.regs i) = _
    by_cases h1 : i = qfReg 1 <;> by_cases h2 : i = qfReg 247 <;>
      simp +decide [QuotientFilter.inputReg, QuotientFilter.encode, QuotientFilter.opKey,
        QuotientFilter.opTag, h1, h2]
  | delete u =>
    dsimp only [FilterPresentation.filterOpOf]
    rw [hP.prepareFilterRegs_delete]
    change (if QuotientFilter.inputReg i then QuotientFilter.encode (.delete u) i
      else d.regs i) = _
    by_cases h1 : i = qfReg 1 <;> by_cases h2 : i = qfReg 247 <;>
      simp +decide [QuotientFilter.inputReg, QuotientFilter.encode, QuotientFilter.opKey,
        QuotientFilter.opTag, h1, h2]
  | query u =>
    dsimp only [FilterPresentation.filterOpOf]
    rw [hP.prepareFilterRegs_query]
    change (if QuotientFilter.inputReg i then QuotientFilter.encode (.query u) i
      else d.regs i) = _
    by_cases h1 : i = qfReg 1 <;> by_cases h2 : i = qfReg 247 <;>
      simp +decide [QuotientFilter.inputReg, QuotientFilter.encode, QuotientFilter.opKey,
        QuotientFilter.opTag, h1, h2]

private theorem coupledOutcome_of_seqOutcome_transfer
    {S : Presentation} (hS : Laws S)
    {P : FilterPresentation S} (hP : FilterLaws S P)
    {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + QuotientFilter.space w w₀ n k))
    (prefOps remOps : List (ApproximateMembership.Op U))
    (ν : PMF (SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF))
    (hS_card : #(ApproximateMembership.activeSet prefOps) ≤ n)
    (hv : ApproximateMembership.ValidOpSeqFrom n (ApproximateMembership.activeSet prefOps) remOps)
    (hseed : ν.map SeqOutcome.latent = filterSeedLaw w₀ n)
    (hsupp : ∀ t ∈ ν.support,
      t.transcript = simTranscript U w₀ n k t.latent ∅ prefOps ∧
      Rep U w base w₀ n k t.latent (ApproximateMembership.activeSet prefOps) t.data) :
    let toAbs (t : SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF) :
      P.CoupledOutcome (FilterSeed w₀ n) U rQF :=
      P.coupledOutcome t.latent t.data.regs t.data.mem (t.transcript.map P.entryOf)
    ∃ (ν_final : PMF (SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF))
      (T_ops : ℝ≥0∞),
      P.ExecFilterOps w
        (S.programOf ((QuotientFilter.subroutineCode w w₀ n k).code.program (qfReg 1)))
        (qfReg 1) (qfReg 247) (qfReg 1)
        base (QuotientFilter.space w w₀ n k) QuotientFilter.charge
        (remOps.map P.filterOpOf) (ν.map toAbs) (ν_final.map toAbs) T_ops ∧
      ν_final.map SeqOutcome.latent = filterSeedLaw w₀ n ∧
      (∀ t ∈ ν_final.support,
        t.transcript = simTranscript U w₀ n k t.latent ∅ (prefOps ++ remOps) ∧
        Rep U w base w₀ n k t.latent (ApproximateMembership.activeSet (prefOps ++ remOps)) t.data) ∧
      T_ops ≤ ((remOps.length * QuotientFilter.charge : ℕ) : ℝ≥0∞) := by
  intro toAbs
  induction remOps generalizing prefOps ν with
  | nil =>
    refine ⟨ν, 0, ?_, hseed, fun t ht => ?_, by simp⟩
    · exact hP.execFilterOps_nil w _ (qfReg 1) (qfReg 247) (qfReg 1)
        base (QuotientFilter.space w w₀ n k) QuotientFilter.charge (ν.map toAbs)
    · rw [List.append_nil]
      exact hsupp t ht
  | cons o os ih =>
    set A := ApproximateMembership.activeSet prefOps
    obtain ⟨ho_valid, hos_valid⟩ := hv
    let xPrep (t : SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF) :
        Data rQF :=
      ((QuotientFilter.subroutineCode w w₀ n k).toDynamicProgram
        QuotientFilter.encode QuotientFilter.decode).prepare o t.data
    have hstep_ex : ∀ (t : SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF),
        t ∈ ν.support →
        ∃ y : Data rQF,
          ExecWithin w (QuotientFilter.opCode w w₀ n k) (xPrep t) y
            (QuotientFilter.opStepBound (seedClusterBound U w₀ n A (opKey o) t.latent.1)) ∧
          Rep U w base w₀ n k t.latent (ApproximateMembership.stepSet A o) y ∧
          QuotientFilter.decode o y.regs = some (simResult U w₀ n k t.latent A o) ∧
          Modifies (Block.mk base (QuotientFilter.space w w₀ n k)).footprint t.data.mem y.mem := by
      intro t ht
      obtain ⟨hrep_prep, h1_prep, h247_prep, _⟩ :=
        QuotientFilter.prepare_rep hw₀_pos hw hU o (hsupp t ht).2
      exact QuotientFilter.opCode_execWithin hw₀_pos hw hU hfit_space hS_card ho_valid
        hrep_prep h1_prep h247_prep
    classical
    let nextData (t : SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF) :
        Data rQF :=
      if ht : t ∈ ν.support then Classical.choose (hstep_ex t ht) else t.data
    let μ_step (t : SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF) :
        PMF (StepOutcome (FilterSeed w₀ n) (ApproximateMembership.Result o) rQF) :=
      PMF.pure ⟨t.latent, nextData t, simResult U w₀ n k t.latent A o⟩
    let ν₁ : PMF (SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF) :=
      ν.bind fun t => (μ_step t).map (t.appendStep o)
    have hseed₁ : ν₁.map SeqOutcome.latent = filterSeedLaw w₀ n := by
      dsimp only [ν₁, μ_step]
      rw [PMF.map_bind]
      have hbind_eq :
          (ν.bind fun t =>
            ((PMF.pure ⟨t.latent, nextData t, simResult U w₀ n k t.latent A o⟩).map
              (t.appendStep o)).map SeqOutcome.latent) =
          ν.map SeqOutcome.latent := by
        refine congrArg (ν.bind ·) (funext fun t => ?_)
        rw [PMF.pure_map, PMF.pure_map]
        rfl
      rw [hbind_eq, hseed]
    have hact_append :
        ApproximateMembership.activeSet (prefOps ++ [o]) = ApproximateMembership.stepSet A o := by
      dsimp only [ApproximateMembership.activeSet, A]
      rw [ApproximateMembership.activeSetFrom_append, ApproximateMembership.activeSetFrom_cons,
        ApproximateMembership.activeSetFrom_nil]
    have hS₁ : #(ApproximateMembership.activeSet (prefOps ++ [o])) ≤ n := by
      rw [hact_append]
      exact ApproximateMembership.card_stepSet_le hS_card ho_valid
    have hos_valid' :
        ApproximateMembership.ValidOpSeqFrom n
          (ApproximateMembership.activeSet (prefOps ++ [o])) os := by
      rwa [hact_append]
    have hsupp₁ : ∀ q_seq ∈ ν₁.support,
        q_seq.transcript = simTranscript U w₀ n k q_seq.latent ∅ (prefOps ++ [o]) ∧
        Rep U w base w₀ n k q_seq.latent
          (ApproximateMembership.activeSet (prefOps ++ [o])) q_seq.data := by
      intro q_seq hq_seq
      dsimp only [ν₁, μ_step] at hq_seq
      rw [PMF.mem_support_bind_iff] at hq_seq
      obtain ⟨t, ht, hq_map⟩ := hq_seq
      rw [PMF.mem_support_map_iff] at hq_map
      obtain ⟨q, hq, rfl⟩ := hq_map
      rw [PMF.mem_support_pure_iff] at hq
      subst hq
      obtain ⟨htr_t, _⟩ := hsupp t ht
      have hspec := Classical.choose_spec (hstep_ex t ht)
      have hnd : nextData t = Classical.choose (hstep_ex t ht) :=
        dite_eq_left_of_eq_true (eq_true ht)
      refine ⟨?_, ?_⟩
      · dsimp only [SeqOutcome.appendStep]
        rw [htr_t, simTranscript_append]
        rfl
      · dsimp only [SeqOutcome.appendStep]
        rw [hact_append, hnd]
        exact hspec.2.1
    obtain ⟨ν_final, T_rest, hex_rest, hseed_final, hsupp_final, hcost_rest⟩ :=
      ih (prefOps ++ [o]) ν₁ hS₁ hos_valid' hseed₁ hsupp₁
    let T_step_abs (p_abs : P.CoupledOutcome (FilterSeed w₀ n) U rQF) : ℝ≥0∞ :=
      (QuotientFilter.opStepBound
        (seedClusterBound U w₀ n A (opKey o) (P.coSeed p_abs).1) : ℝ≥0∞)
    have hmem_map {p_abs : P.CoupledOutcome (FilterSeed w₀ n) U rQF}
        (hp : p_abs ∈ (ν.map toAbs).support) :
        ∃ t ∈ ν.support, toAbs t = p_abs := by
      rwa [PMF.mem_support_map_iff] at hp
    let stepFn_abs (p_abs : P.CoupledOutcome (FilterSeed w₀ n) U rQF) :
        P.CoupledOutcome (FilterSeed w₀ n) U rQF :=
      if hp : p_abs ∈ (ν.map toAbs).support then
        let t := Classical.choose (hmem_map hp)
        toAbs ((t.appendStep o) ⟨t.latent, nextData t, simResult U w₀ n k t.latent A o⟩)
      else p_abs
    let μ_step_abs (p_abs : P.CoupledOutcome (FilterSeed w₀ n) U rQF) :
        PMF (P.CoupledOutcome (FilterSeed w₀ n) U rQF) :=
      PMF.pure (stepFn_abs p_abs)
    have htoAbs_inj_on_support :
        ∀ t₁ ∈ ν.support, ∀ t₂ ∈ ν.support, toAbs t₁ = toAbs t₂ → t₁ = t₂ := by
      intro t₁ ht₁ t₂ ht₂ heq
      have hlat : t₁.latent = t₂.latent := by
        have := congrArg P.coSeed heq
        rwa [hP.coSeed_mk, hP.coSeed_mk] at this
      have hreg : t₁.data.regs = t₂.data.regs := by
        have := congrArg P.coReg heq
        rwa [hP.coReg_mk, hP.coReg_mk] at this
      have hmem : t₁.data.mem = t₂.data.mem := by
        have := congrArg P.coMem heq
        rwa [hP.coMem_mk, hP.coMem_mk] at this
      have htr : t₁.transcript = t₂.transcript := by
        rw [(hsupp t₁ ht₁).1, (hsupp t₂ ht₂).1, hlat]
      cases t₁
      cases t₂
      dsimp only at hlat hreg hmem htr
      subst hlat htr
      congr 1
      ext : 1
      · exact hreg
      · exact hmem
    have hstepFn_toAbs : ∀ t ∈ ν.support,
        stepFn_abs (toAbs t) =
          toAbs ((t.appendStep o) ⟨t.latent, nextData t, simResult U w₀ n k t.latent A o⟩) := by
      intro t ht
      have hp : toAbs t ∈ (ν.map toAbs).support := by
        rw [PMF.mem_support_map_iff]
        exact ⟨t, ht, rfl⟩
      dsimp only [stepFn_abs]
      rw [dite_eq_left_of_eq_true (eq_true hp)]
      have hchoose := Classical.choose_spec (hmem_map hp)
      have heq_t : Classical.choose (hmem_map hp) = t :=
        htoAbs_inj_on_support _ hchoose.1 t ht hchoose.2
      rw [heq_t]
    have hbind_eq :
        (ν.map toAbs).bind μ_step_abs = ν₁.map toAbs := by
      dsimp only [ν₁, μ_step]
      rw [PMF.bind_map, PMF.map_bind]
      ext q_abs
      rw [PMF.bind_apply, PMF.bind_apply]
      refine tsum_congr fun t => ?_
      by_cases ht : t ∈ ν.support
      · dsimp only [μ_step_abs, Function.comp_apply]
        rw [hstepFn_toAbs t ht, PMF.pure_map, PMF.pure_map]
      · have h0 : ν t = 0 := by rwa [PMF.apply_eq_zero_iff]
        rw [h0, zero_mul, zero_mul]
    have hT₁_eq :
        (∑' p_abs, (ν.map toAbs) p_abs * T_step_abs p_abs) =
          ∑' p : FilterSeed w₀ n,
            (ν.map SeqOutcome.latent) p *
              (QuotientFilter.opStepBound (seedClusterBound U w₀ n A (opKey o) p.1) : ℝ≥0∞) := by
      rw [Cslib.Probability.PMF.tsum_map_mul, Cslib.Probability.PMF.tsum_map_mul]
      refine tsum_congr fun t => ?_
      dsimp only [T_step_abs, toAbs]
      rw [hP.coSeed_mk]
    have hT₁_le :
        (∑' p_abs, (ν.map toAbs) p_abs * T_step_abs p_abs) ≤ (QuotientFilter.charge : ℝ≥0∞) := by
      rw [hT₁_eq, hseed]
      exact QuotientFilter.tsum_opStepBound_le hw₀_pos hU hS_card (opKey o)
    refine ⟨ν_final, (∑' p_abs, (ν.map toAbs) p_abs * T_step_abs p_abs) + T_rest,
      ?_, hseed_final, fun t ht => ?_, ?_⟩
    · refine hP.execFilterOps_cons T_step_abs μ_step_abs (fun p_abs hp_abs => ?_) hT₁_le ?_
      · have hp_abs' := hp_abs
        rw [PMF.mem_support_map_iff] at hp_abs'
        obtain ⟨t, ht, rfl⟩ := hp_abs'
        have hstep_t := hstepFn_toAbs t ht
        have hspec := Classical.choose_spec (hstep_ex t ht)
        have hnd : nextData t = Classical.choose (hstep_ex t ht) :=
          dite_eq_left_of_eq_true (eq_true ht)
        have hreg_t : P.coReg (toAbs t) = t.data.regs :=
          hP.coReg_mk _ _ _ _
        have hmem_t : P.coMem (toAbs t) = t.data.mem :=
          hP.coMem_mk _ _ _ _
        have hseed_t : P.coSeed (toAbs t) = t.latent :=
          hP.coSeed_mk _ _ _ _
        have htr_t : P.coTranscript (toAbs t) = t.transcript.map P.entryOf :=
          hP.coTranscript_mk _ _ _ _
        have hprep_regs :
            (xPrep t).regs =
              P.prepareFilterRegs (qfReg 1) (qfReg 247) (P.filterOpOf o)
                (P.coReg (toAbs t)) := by
          rw [hreg_t]
          exact prepare_regs_eq hP o t.data
        have hprep_mem : (xPrep t).mem = P.coMem (toAbs t) := hmem_t.symm
        refine ⟨?_, ?_⟩
        · have hmap_rm :
              (PMF.pure (nextData t)).map P.regMemOf =
                (μ_step_abs (toAbs t)).map P.toRegMem := by
            dsimp only [μ_step_abs]
            rw [hstep_t, PMF.pure_map, PMF.pure_map]
            dsimp only [FilterPresentation.toRegMem, toAbs, SeqOutcome.appendStep,
              FilterPresentation.regMemOf]
            rw [hP.coReg_mk, hP.coMem_mk]
          have hT_t :
              ((QuotientFilter.opStepBound
                  (seedClusterBound U w₀ n A (opKey o) t.latent.1) : ℕ) : ℝ≥0∞) =
                T_step_abs (toAbs t) := by
            dsimp only [T_step_abs]
            rw [hseed_t]
          have hex_step :
              ExecWithin w (QuotientFilter.opCode w w₀ n k) (xPrep t) (nextData t)
                (QuotientFilter.opStepBound (seedClusterBound U w₀ n A (opKey o) t.latent.1)) := by
            rw [hnd]
            exact hspec.1
          exact execProgramDist_congr P hprep_regs hprep_mem hmap_rm hT_t
            (compile_execCodeDist hS hP (qfReg 1) (ExecCodeDist.of_execWithin hex_step))
        · intro q_abs hq_abs
          dsimp only [μ_step_abs] at hq_abs
          rw [PMF.mem_support_pure_iff] at hq_abs
          subst hq_abs
          rw [hstep_t]
          dsimp only [toAbs, SeqOutcome.appendStep]
          rw [hP.coReg_mk, hP.coMem_mk, hP.coTranscript_mk, htr_t, hmem_t, List.map_append,
            List.map_singleton]
          refine ⟨?_, ?_, ?_⟩
          · rw [hnd]
            exact hspec.2.1.1
          · congr 2
            have hdec := hspec.2.2.1
            rw [← hnd] at hdec
            cases o with
            | insert u =>
              dsimp only [FilterPresentation.filterOpOf, FilterPresentation.entryOf]
              exact (hP.decodeFilterEntry_insert (qfReg 1) u _).symm
            | delete u =>
              dsimp only [FilterPresentation.filterOpOf, FilterPresentation.entryOf]
              exact (hP.decodeFilterEntry_delete (qfReg 1) u _).symm
            | query u =>
              dsimp only [FilterPresentation.filterOpOf, FilterPresentation.entryOf]
              rw [hP.decodeFilterEntry_query]
              change some (decide ((nextData t).regs (qfReg 1) = 1)) =
                some (simResult U w₀ n k t.latent A (.query u)) at hdec
              injection hdec with hdec_eq
              rw [← hdec_eq]
          · intro addr haddr
            have haddr' : addr ∉ (Block.mk base (QuotientFilter.space w w₀ n k)).footprint := by
              rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt]
              exact haddr
            rw [hnd]
            exact hspec.2.2.2 addr haddr'
      · rw [hbind_eq]
        exact hex_rest
    · have h := hsupp_final t ht
      rwa [List.append_assoc, List.singleton_append] at h
    · calc (∑' p_abs, (ν.map toAbs) p_abs * T_step_abs p_abs) + T_rest
          ≤ (QuotientFilter.charge : ℝ≥0∞) + ((os.length * QuotientFilter.charge : ℕ) : ℝ≥0∞) :=
            add_le_add hT₁_le hcost_rest
        _ = (((o :: os).length * QuotientFilter.charge : ℕ) : ℝ≥0∞) := by
            simp only [List.length_cons]
            push_cast
            ring

/-- Headline bridge theorem for the two-stage quotient filter (`QuotientFilter.implOfEps`). -/
theorem quotientFilter (S : Presentation) (hS : Laws S)
    (P : FilterPresentation S) (hP : FilterLaws S P) :
    ∃ (r C_op : ℕ) (hr : 248 ≤ r),
      ∀ (w w₀ n : ℕ) (ε : ℝ≥0∞),
        ∃ (p_init p_op : List (S.Instr r)),
          ∀ (U base : ℕ),
            ε ≠ 0 →
            1 ≤ n →
            0 < w₀ →
            2 * w₀ ≤ w →
            U ≤ 2 ^ w₀ →
            base + qfSpaceOfEps w w₀ n ε < 2 ^ w →
            qfSpaceOfEps w w₀ n ε ≤ 640 * ((n * epsLog ε + w - 1) / w + 1) ∧
            ∀ (reg₀ : Fin r → ℕ) (mem₀ : ℕ → ℕ),
              WordBounded w reg₀ mem₀ →
              reg₀ ⟨240, by omega⟩ = base →
              (∀ a, base ≤ a → a < base + qfSpaceOfEps w w₀ n ε → mem₀ a = 0) →
              ∃ (Seed : Type) (μ_init : PMF (P.CoupledOutcome Seed U r)),
                P.ExecProgramDist w p_init ⟨1, by omega⟩ reg₀ mem₀
                  (μ_init.map P.toRegMem) (qfInitSteps w₀ n) ∧
                (∀ p ∈ μ_init.support,
                  WordBounded w (P.coReg p) (P.coMem p) ∧
                  P.coReg p ⟨0, by omega⟩ = base ∧
                  P.coReg p ⟨240, by omega⟩ = base + qfSpaceOfEps w w₀ n ε ∧
                  P.coTranscript p = [] ∧
                  UnchangedOutside base (qfSpaceOfEps w w₀ n ε) mem₀ (P.coMem p)) ∧
                ∀ ops : List (P.FilterOp U),
                  P.ValidFilterSeqFrom n ∅ ops →
                  ∃ (μ_final : PMF (P.CoupledOutcome Seed U r)) (T_ops : ℝ≥0∞),
                    P.ExecFilterOps w p_op
                      ⟨1, by omega⟩ ⟨247, by omega⟩ ⟨1, by omega⟩
                      base (qfSpaceOfEps w w₀ n ε) C_op ops
                      μ_init μ_final T_ops ∧
                    P.FilterContract ε ops (μ_final.map P.coTranscript) ∧
                    T_ops ≤ ((ops.length * C_op : ℕ) : ℝ≥0∞) := by
  refine ⟨rQF, QuotientFilter.charge, le_rQF, ?_⟩
  intro w w₀ n ε
  let k := QuotientFilter.epsLog ε
  let Sub := QuotientFilter.subroutineCode w w₀ n k
  refine ⟨S.programOf (Sub.initFresh.program (qfReg 1)),
    S.programOf (Sub.code.program (qfReg 1)), ?_⟩
  intro U base hε0 hn hw₀_pos hw hU hfit_space
  have hfit_lib : Fits w (base + QuotientFilter.space w w₀ n k) := by
    rwa [← qfSpaceOfEps_eq]
  refine ⟨?_, ?_⟩
  · rw [qfSpaceOfEps_eq, epsLog_eq]
    exact QuotientFilter.implOfEps_space_le hε0 hw₀_pos hw hU hfit_lib hn
  intro reg₀ mem₀ hbdd₀ hfr₀ hz₀
  have hz_lib : ∀ a ∈ (Block.mk base (QuotientFilter.space w w₀ n k)).footprint, mem₀ a = 0 := by
    intro a ha
    rw [Block.mem_footprint, Block.Owns] at ha
    have ha' : base ≤ a ∧ a < base + QuotientFilter.space w w₀ n k := ha
    rw [← qfSpaceOfEps_eq] at ha'
    exact hz₀ a ha'.1 ha'.2
  obtain ⟨ν₀_raw, he_raw, hinv_raw, hsupp_raw⟩ :=
    (QuotientFilter.implOfEps hε0 hw₀_pos hw hU hfit_lib).initFresh_exec
      (x := ⟨reg₀, mem₀⟩) hbdd₀ hfr₀ (fun j => Fin.elim0 j) hz_lib
  let ν₀ : PMF (LatentState (FilterSeed w₀ n) rQF) := ν₀_raw
  have hinit_time :
      (QuotientFilter.implOfEps hε0 hw₀_pos hw hU hfit_lib).initTime =
        (qfInitSteps w₀ n : ℝ≥0∞) := by
    dsimp only [ObliviousSequenceImpl.initTime, QuotientFilter.implOfEps, QuotientFilter.implOfLe]
    rw [qfInitSteps_eq]
    push_cast
    ring
  have he_init :
      ExecCodeDist w Sub.initFresh ⟨reg₀, mem₀⟩ (ν₀.map LatentState.data) (qfInitSteps w₀ n) := by
    rw [← hinit_time]
    exact he_raw
  have hinv₀ :
      ν₀.map LatentState.latent = filterSeedLaw w₀ n ∧
      ∀ t ∈ ν₀.support, Rep U w base w₀ n k t.latent ∅ t.data := hinv_raw
  have hsupp₀ :
      ∀ t ∈ ν₀.support,
        t.data.Bounded w ∧
        t.data.regs (qfReg 240) = base + QuotientFilter.space w w₀ n k ∧
        Modifies (Block.mk base (QuotientFilter.space w w₀ n k)).footprint mem₀ t.data.mem :=
    hsupp_raw
  let toAbs (t : SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF) :
      P.CoupledOutcome (FilterSeed w₀ n) U rQF :=
    P.coupledOutcome t.latent t.data.regs t.data.mem (t.transcript.map P.entryOf)
  let ν_seq : PMF (SeqOutcome (FilterSeed w₀ n) (@ApproximateMembership.Result U) rQF) :=
    ν₀.map SeqOutcome.ofLatentState
  refine ⟨FilterSeed w₀ n, ν_seq.map toAbs, ?_, ?_, ?_⟩
  · have hmap_rm : (ν_seq.map toAbs).map P.toRegMem = (ν₀.map LatentState.data).map P.regMemOf := by
      dsimp only [ν_seq]
      rw [PMF.map_comp, PMF.map_comp, PMF.map_comp]
      refine congrArg (ν₀.map ·) (funext fun u => ?_)
      dsimp only [Function.comp_apply, FilterPresentation.toRegMem, toAbs,
        SeqOutcome.ofLatentState, FilterPresentation.regMemOf]
      rw [hP.coReg_mk, hP.coMem_mk]
    rw [hmap_rm]
    exact compile_execCodeDist hS hP (qfReg 1) he_init
  · intro p_abs hp_abs
    rw [PMF.mem_support_map_iff] at hp_abs
    obtain ⟨t, ht, rfl⟩ := hp_abs
    dsimp only [ν_seq] at ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    obtain ⟨hbdd_u, hfr_u, hmod_u⟩ := hsupp₀ u hu
    have hrep_u := hinv₀.2 u hu
    dsimp only [toAbs, SeqOutcome.ofLatentState]
    rw [hP.coReg_mk, hP.coMem_mk, hP.coTranscript_mk, List.map_nil, qfSpaceOfEps_eq]
    refine ⟨hbdd_u, hrep_u.2.1, hfr_u, rfl, fun addr haddr => ?_⟩
    have haddr' : addr ∉ (Block.mk base (QuotientFilter.space w w₀ n k)).footprint := by
      rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt]
      exact haddr
    exact hmod_u addr haddr'
  · intro ops hv_abs
    obtain ⟨ops_lib, rfl⟩ := ops_surjective P ops
    have hv_lib : ApproximateMembership.ValidOpSeq n ops_lib :=
      (validFilterSeqFrom_map_filterOpOf hP n ∅ ops_lib).mp hv_abs
    have hseed_seq : ν_seq.map SeqOutcome.latent = filterSeedLaw w₀ n := by
      dsimp only [ν_seq]
      rw [PMF.map_comp]
      exact hinv₀.1
    have hsupp_seq : ∀ t ∈ ν_seq.support,
        t.transcript = simTranscript U w₀ n k t.latent ∅ [] ∧
        Rep U w base w₀ n k t.latent (ApproximateMembership.activeSet []) t.data := by
      intro t ht
      dsimp only [ν_seq] at ht
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      exact ⟨rfl, hinv₀.2 u hu⟩
    obtain ⟨ν_final, T_ops, hex_abs, hseed_final, hsupp_final, hcost_abs⟩ :=
      coupledOutcome_of_seqOutcome_transfer hS hP hw₀_pos hw hU hfit_lib [] ops_lib ν_seq
        (by simp) hv_lib hseed_seq hsupp_seq
    refine ⟨ν_final.map toAbs, T_ops, ?_, ?_, ?_⟩
    · rw [qfSpaceOfEps_eq]
      exact hex_abs
    · have htr_map :
          (ν_final.map toAbs).map P.coTranscript =
            ((filterSeedLaw w₀ n).map (fun p => simTranscript U w₀ n k p ∅ ops_lib)).map
              (fun tr => tr.map P.entryOf) := by
        rw [PMF.map_comp, PMF.map_comp]
        have hcongr :
            ν_final.map (P.coTranscript ∘ toAbs) =
              ν_final.map (((fun tr => tr.map P.entryOf) ∘
                fun p => simTranscript U w₀ n k p ∅ ops_lib) ∘ SeqOutcome.latent) := by
          refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun t ht => ?_
          dsimp only [Function.comp_apply, toAbs]
          rw [hP.coTranscript_mk]
          have h := (hsupp_final t ht).1
          rw [List.nil_append] at h
          rw [h]
        rw [hcongr, ← PMF.map_comp, hseed_final]
      rw [htr_map]
      have hcontract_lib :
          (ApproximateMembership.spec U n ε).Contract ops_lib
            ((filterSeedLaw w₀ n).map (fun p => simTranscript U w₀ n k p ∅ ops_lib)) :=
        ApproximateMembership.spec_weaken
          (QuotientFilter.two_pow_neg_epsLog_le hε0)
          (contract_map_simTranscript hw₀_pos hU hv_lib)
      exact filterContract_of_spec_contract hP hcontract_lib
    · rw [List.length_map]
      exact hcost_abs

end ComplexityAbstracts.ApproximateMembershipBridge
