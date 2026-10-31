/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Randomized.Subroutine
public import Complexity.DataStructure.ObliviousSequence
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map

/-!
# Oblivious-Sequence Word-RAM Subroutines and Hash-Family Realizations

This file connects state-free oblivious-sequence specifications
(`Cslib.DataStructure.ObliviousSequenceSpec`) to concrete randomized Word-RAM subroutines and
multi-epoch hash-family implementations:

1. **`Cslib.WordRAM.Randomized.ObliviousSequenceDS`**:
   A reusable Word-RAM subroutine certificate realizing an
   `S : Cslib.DataStructure.ObliviousSequenceSpec` at word width `w`, base address `base`, and
   runtime initialization parameters `params`. It provides:
   - fresh zeroed-memory initialization (`initFresh_exec`) and dirty-memory clearing initialization
     (`initClear_exec`);
   - multi-step distributional execution `ExecSteps` across any admissible oblivious sequence
     `ops : List S.Op`;
   - end-to-end expected-time and distributional correctness theorems `seq_expected` and
     `seq_expected_clear` certifying both `S.Contract ops (ν_final.map SeqOutcome.transcript)` and
     the total expected instruction bound;
   - basis simulation transport `mapSimulates` and exact-to-standard lifting `toStandard`.

2. **Canonical embedding `Cslib.WordRAM.Randomized.SubroutineDS.toObliviousSequenceDS`**:
   Every relational `Cslib.WordRAM.Randomized.SubroutineDS P D w base params s₀` whose per-operation
   amortized charge is bounded by `opCharge : D.Op → ℕ` on admissible inputs canonically induces an
   `ObliviousSequenceDS P (D.toObliviousSequenceSpec s₀) w base params`.

3. **`Cslib.WordRAM.Randomized.HashFamilyDS`**:
   Packages a Word-RAM hash-function data structure at `[base, base + space)` with a finite seed
   type `Seed`, pure evaluation function `eval : Seed → Fin U → Fin m`, optional deterministic
   table initialization `initTableCode` (`initTableSteps`), randomized seed resampling
   `resampleCode` (`resampleSteps`, inducing `PMF.uniformOfFintype Seed`), and deterministic query
   evaluation `evalCode` (`evalSteps`, computing `(eval θ u).val` without modifying memory).
   Every `H : HashFamilyDS` canonically induces:
   - `H.toKWiseObliviousSequenceDS` realizing `DataStructure.kWiseHashSpec k U m` when
     `IsKWiseIndependentHash k H.eval`; and
   - `H.toWhpKWiseObliviousSequenceDS` realizing `DataStructure.whpKWiseHashSpec k U m δ` when `H`
     has a two-level `(1 - δ)`-good top-seed decomposition.

Both `ObliviousSequenceDS` and `HashFamilyDS` bound the instruction cost of initialization and of
the subroutine operation bodies across an oblivious sequence `ops`, excluding external caller
argument delivery and dispatch, with the word width `w` treated as an external admissible parameter.

## Main definitions

* `Cslib.WordRAM.Randomized.LatentState`, `Cslib.WordRAM.Randomized.StepOutcome`,
  `Cslib.WordRAM.Randomized.SeqOutcome`: named state and transcript records for multi-step
  distributional execution.
* `Cslib.WordRAM.Randomized.ExecSteps`: multi-operation distributional execution relation across an
  oblivious sequence `ops : List S.Op`.
* `Cslib.WordRAM.Randomized.ObliviousSequenceDS`: Word-RAM subroutine certificate for an
  `ObliviousSequenceSpec`.
* `Cslib.WordRAM.Randomized.SubroutineDS.toObliviousSequenceDS`: canonical embedding of a relational
  `SubroutineDS` into `ObliviousSequenceDS`.
* `Cslib.WordRAM.Randomized.HashFamilyDS`: Word-RAM hash-family data structure interface, together
  with `HashFamilyDS.resample_exec_of_execRand`, `HashFamilyDS.mapSimulates`,
  `HashFamilyDS.toStandard`, `HashFamilyDS.toObliviousSequenceDS`,
  `HashFamilyDS.toKWiseObliviousSequenceDS`, and `HashFamilyDS.toWhpKWiseObliviousSequenceDS`.

## Main results

* `Cslib.WordRAM.Randomized.ObliviousSequenceDS.initFresh_exec`,
  `Cslib.WordRAM.Randomized.ObliviousSequenceDS.initClear_exec`,
  `Cslib.WordRAM.Randomized.ObliviousSequenceDS.seq_expected`,
  `Cslib.WordRAM.Randomized.ObliviousSequenceDS.seq_expected_clear`: initialization and end-to-end
  expected-time + distributional-contract theorems.
* `Cslib.WordRAM.Randomized.HashFamilyDS.toKWiseObliviousSequenceDS`,
  `Cslib.WordRAM.Randomized.HashFamilyDS.toWhpKWiseObliviousSequenceDS`: canonical
  `ObliviousSequenceDS` realizations of `DataStructure.kWiseHashSpec` and
  `DataStructure.whpKWiseHashSpec` from a Word-RAM `HashFamilyDS`.

## References

* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
* [M. Mitzenmacher, E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

open Cslib.WordRAM Cslib.Probability
open scoped ENNReal

universe u v z

namespace Cslib.WordRAM.Randomized

/-! ## Named state and transcript bundles for oblivious-sequence execution -/

/-- Coupled latent state and concrete Word-RAM register/memory state. -/
structure LatentState (Latent : Type z) (r : ℕ) : Type z where
  /-- Internal latent state (such as a hash seed or coupled relational state). -/
  latent : Latent
  /-- Concrete Word-RAM register and memory state. -/
  data : Data r

/-- Outcome of a single subroutine operation step: updated latent state, updated concrete Word-RAM
state, and decoded operation observation. -/
structure StepOutcome (Latent : Type z) (α : Type v) (r : ℕ) : Type (max v z) where
  /-- Updated internal latent state. -/
  latent : Latent
  /-- Updated concrete Word-RAM register and memory state. -/
  data : Data r
  /-- Decoded observation returned by the operation. -/
  result : α

/-- Outcome of a multi-operation oblivious sequence: current latent state, concrete Word-RAM state,
and accumulated input-output transcript `List (Sigma Result)`. -/
structure SeqOutcome (Latent : Type z) {Op : Type u} (Result : Op → Type v) (r : ℕ) :
    Type (max u v z) where
  /-- Current internal latent state. -/
  latent : Latent
  /-- Current concrete Word-RAM register and memory state. -/
  data : Data r
  /-- Accumulated input-output transcript of operations executed so far. -/
  transcript : List (Sigma Result)

/-- Initialize a `SeqOutcome` from a `LatentState` with an empty transcript `[]`. -/
@[expose] def SeqOutcome.ofLatentState {Latent : Type z} {Op : Type u}
    {Result : Op → Type v} {r : ℕ} (t : LatentState Latent r) : SeqOutcome Latent Result r where
  latent := t.latent
  data := t.data
  transcript := []

/-- Append a single operation outcome `q : StepOutcome Latent (Result o) r` to `t : SeqOutcome`. -/
@[expose] def SeqOutcome.appendStep {Latent : Type z} {Op : Type u}
    {Result : Op → Type v} {r : ℕ}
    (t : SeqOutcome Latent Result r) (o : Op) (q : StepOutcome Latent (Result o) r) :
    SeqOutcome Latent Result r where
  latent := q.latent
  data := q.data
  transcript := t.transcript ++ [⟨o, q.result⟩]

/-- Multi-operation distributional execution relation across an oblivious sequence
`ops : List S.Op`.
At each operation `o`, arguments are delivered via `(P.toDynamicProgram encode decode).prepare o`,
`P.code` executes under `ExecCodeDist`, the observation `q.result` is decoded from `q.data.regs`,
memory outside `[base, base + space)` is preserved, and `⟨o, q.result⟩` is appended to the
accumulated transcript. -/
inductive ExecSteps {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, v})
    (Latent : Type z) (w base space : ℕ)
    (encode : S.Op → Fin r_ds → ℕ)
    (decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)) :
    List S.Op → PMF (SeqOutcome Latent S.Result r_ds) →
      PMF (SeqOutcome Latent S.Result r_ds) → ℝ≥0∞ → Prop where
  | nil (ν : PMF (SeqOutcome Latent S.Result r_ds)) :
      ExecSteps P S Latent w base space encode decode [] ν ν 0
  | cons {o : S.Op} {ops : List S.Op}
      {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)}
      {μ_step :
        SeqOutcome Latent S.Result r_ds → PMF (StepOutcome Latent (S.Result o) r_ds)}
      {T_step : SeqOutcome Latent S.Result r_ds → ℝ≥0∞} {T_rest : ℝ≥0∞} :
      (∀ t ∈ ν.support,
        ExecCodeDist w P.code ((P.toDynamicProgram encode decode).prepare o t.data)
          ((μ_step t).map StepOutcome.data) (T_step t) ∧
        ∀ q ∈ (μ_step t).support,
          decode o q.data.regs = some q.result ∧
          Modifies (Block.mk base space).footprint t.data.mem q.data.mem) →
      ExecSteps P S Latent w base space encode decode ops
        (ν.bind fun t => (μ_step t).map (t.appendStep o))
        ν_final T_rest →
      ExecSteps P S Latent w base space encode decode (o :: ops) ν ν_final
        ((∑' t, ν t * T_step t) + T_rest)

/-- Lift an `ExecSteps` derivation along a basis simulation `φ : B.Simulates B'`. -/
theorem ExecSteps.mapSimulates {B B' : Basis} {r_ds k_init : ℕ}
    (φ : B.Simulates B')
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base space : ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {ops : List S.Op}
    {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (h : ExecSteps P S Latent w base space encode decode ops ν ν_final T_ops) :
    ExecSteps (P.mapSimulates φ) S Latent w base space encode decode ops ν ν_final T_ops := by
  induction h with
  | nil ν => exact .nil ν
  | cons hstep _ ih =>
    refine .cons (fun t ht => ?_) ih
    obtain ⟨he, hq⟩ := hstep t ht
    exact ⟨he.mapSimulates φ, hq⟩

end Cslib.WordRAM.Randomized

namespace Cslib.WordRAM.Randomized

/-! ## `ObliviousSequenceDS`: Word-RAM certificate for an `ObliviousSequenceSpec` -/

/-- Reusable Word-RAM subroutine specification and resource certificate for a randomized data
structure `P : SubroutineCode B r_ds k_init` realizing an oblivious-sequence specification
`S : DataStructure.ObliviousSequenceSpec` at word width `w`, base address `base`, and runtime
parameters `params`. -/
structure ObliviousSequenceDS {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, v})
    (w base : ℕ) (params : Fin k_init → ℕ) : Type (max u v (z + 1)) where
  /-- Internal latent state type (e.g. a hash seed or coupled relational state). -/
  Latent : Type z
  /-- Contiguous memory footprint length `[base, base + space)`. -/
  space : ℕ
  /-- Worst-case instruction bound for `P.allocSpan`. -/
  spanTime : ℕ
  /-- Expected instruction bound for `P.initSetup`. -/
  setupTime : ℝ≥0∞
  /-- Upper bound on initial concrete potential after initialization (`0` when unamortized). -/
  initPotential : ℕ := 0
  /-- Per-operation instruction charge. -/
  charge : S.Op → ℕ
  /-- Distributional invariant on the initial coupled state distribution produced by `P.initSetup`.
  -/
  initInv : PMF (LatentState Latent r_ds) → Prop
  /-- Standalone register encoding for argument delivery. -/
  encode : S.Op → Fin r_ds → ℕ
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)
  /-- Distinctness of registers used by `zeroFillCode` relative to `baseReg` and `frontierReg`. -/
  clear_nodup : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup
  /-- Initialization parameter registers are not overwritten by `zeroFillCode`. -/
  params_not_clear : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg]
  /-- `P.incCur` increments `P.curReg` by `1` when `P.oneReg = 1` and the sum fits in `w` bits. -/
  incCur_eval : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
    P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1))
  /-- Execution of `P.allocSpan`: records `baseReg = base` and advances `frontierReg`. -/
  span_exec : ∀ {x : Data r_ds},
    x.Bounded w → x.regs P.frontierReg = base → (∀ j, x.regs (P.initParams j) = params j) →
    ∃ x₁, ExecWithin w P.allocSpan x x₁ spanTime ∧ x₁.mem = x.mem ∧
      x₁.regs P.baseReg = base ∧ x₁.regs P.frontierReg = base + space ∧
      (∀ j, x₁.regs (P.initParams j) = params j)
  /-- Execution of `P.initSetup` once `[base, base + space)` holds zeros, producing an initial
  coupled state distribution `ν₀ : PMF (LatentState Latent r_ds)` satisfying `initInv ν₀`. -/
  setup_exec : ∀ {x₁ : Data r_ds},
    x₁.Bounded w → x₁.regs P.baseReg = base → x₁.regs P.frontierReg = base + space →
    (∀ j, x₁.regs (P.initParams j) = params j) →
    (∀ a ∈ (Block.mk base space).footprint, x₁.mem a = 0) →
    ∃ ν₀ : PMF (LatentState Latent r_ds),
      ExecCodeDist w P.initSetup x₁ (ν₀.map LatentState.data) setupTime ∧
      initInv ν₀ ∧
      ∀ t ∈ ν₀.support,
        t.data.regs P.frontierReg = base + space ∧
        Modifies (Block.mk base space).footprint x₁.mem t.data.mem
  /-- Multi-operation execution across any admissible oblivious sequence `ops : List S.Op` from any
  initial distribution `ν₀` satisfying `initInv ν₀`, certifying both `S.Contract ops` on the joint
  output transcript distribution and the expected instruction bound. -/
  steps_exec : ∀ (ops : List S.Op) (ν₀ : PMF (LatentState Latent r_ds)),
    S.ValidOpSeq ops → initInv ν₀ →
    ∃ (ν_final : PMF (SeqOutcome Latent S.Result r_ds)) (T_ops : ℝ≥0∞),
      ExecSteps P S Latent w base space encode decode ops
        (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      S.Contract ops (ν_final.map SeqOutcome.transcript) ∧
      T_ops ≤ (initPotential : ℝ≥0∞) + ((ops.map charge).sum : ℝ≥0∞)

namespace ObliviousSequenceDS

variable {B B' : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init}
  {S : DataStructure.ObliviousSequenceSpec.{u, v}}
  {params : Fin k_init → ℕ}

/-- Total expected instruction bound for `P.initFresh` (`spanTime + setupTime`). -/
@[expose] def initTime (C : ObliviousSequenceDS.{u, v, z} P S w base params) : ℝ≥0∞ :=
  (C.spanTime : ℝ≥0∞) + C.setupTime

/-- Total expected instruction bound for `P.initClear` (`spanTime + (4 * space + 6) + setupTime`).
-/
@[expose] def initClearTime (C : ObliviousSequenceDS.{u, v, z} P S w base params) : ℝ≥0∞ :=
  (C.spanTime : ℝ≥0∞) + ((4 * C.space + 6 : ℕ) : ℝ≥0∞) + C.setupTime

/-- Total operation charge summed across an operation sequence `ops : List S.Op`. -/
@[expose] def totalCharge (C : ObliviousSequenceDS.{u, v, z} P S w base params)
    (ops : List S.Op) : ℕ :=
  (ops.map C.charge).sum

@[simp]
theorem totalCharge_nil (C : ObliviousSequenceDS.{u, v, z} P S w base params) :
    C.totalCharge [] = 0 := rfl

@[simp]
theorem totalCharge_cons (C : ObliviousSequenceDS.{u, v, z} P S w base params)
    (o : S.Op) (ops : List S.Op) :
    C.totalCharge (o :: ops) = C.charge o + C.totalCharge ops := by
  simp [totalCharge]

/-- Specialization of `Randomized.ExecSteps` to an `ObliviousSequenceDS` certificate `C`. -/
abbrev Steps (C : ObliviousSequenceDS.{u, v, z} P S w base params) :
    List S.Op → PMF (SeqOutcome C.Latent S.Result r_ds) →
      PMF (SeqOutcome C.Latent S.Result r_ds) → ℝ≥0∞ → Prop :=
  ExecSteps P S C.Latent w base C.space C.encode C.decode

/-- Transport an `ObliviousSequenceDS` certificate along a basis simulation `φ : B.Simulates B'`. -/
def mapSimulates (φ : B.Simulates B')
    (C : ObliviousSequenceDS.{u, v, z} P S w base params) :
    ObliviousSequenceDS.{u, v, z} (P.mapSimulates φ) S w base params where
  Latent := C.Latent
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  initPotential := C.initPotential
  charge := C.charge
  initInv := C.initInv
  encode := C.encode
  decode := C.decode
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval h1 hfit := Op.eval_mapSimulates_of_some φ (C.incCur_eval h1 hfit)
  span_exec hx hfr hpar := by
    obtain ⟨x₁, he, hmem, hb, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
    exact ⟨x₁, he.mapSimulates φ, hmem, hb, hfr₁, hpar₁⟩
  setup_exec hx₁ hb hfr hpar hz := by
    obtain ⟨ν₀, he, hinv, hsupp⟩ := C.setup_exec hx₁ hb hfr hpar hz
    exact ⟨ν₀, he.mapSimulates φ, hinv, hsupp⟩
  steps_exec ops ν₀ hv hinv := by
    obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ := C.steps_exec ops ν₀ hv hinv
    exact ⟨ν_final, T_ops, hex.mapSimulates φ, hcontract, hcost⟩

/-- Lift an exact-basis `ObliviousSequenceDS` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : ObliviousSequenceDS.{u, v, z} P S w base params) :
    ObliviousSequenceDS.{u, v, z} P.toStandard S w base params :=
  C.mapSimulates .exactStandard

/-- Expected-time execution of `P.initFresh` when `[base, base + C.space)` already holds zeros. -/
theorem initFresh_exec (C : ObliviousSequenceDS.{u, v, z} P S w base params)
    {x : Data r_ds} (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ ν₀ : PMF (LatentState C.Latent r_ds),
      ExecCodeDist w P.initFresh x (ν₀.map LatentState.data) C.initTime ∧
      C.initInv ν₀ ∧
      ∀ t ∈ ν₀.support,
        t.data.regs P.frontierReg = base + C.space ∧
        Modifies (Block.mk base C.space).footprint x.mem t.data.mem := by
  obtain ⟨x₁, he_span, hmem₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  have hx₁ : x₁.Bounded w := he_span.bounded hx
  have hz₁ : ∀ a ∈ (Block.mk base C.space).footprint, x₁.mem a = 0 := by
    intro a ha
    rw [hmem₁]
    exact hz a ha
  obtain ⟨ν₀, he_setup, hinv, hsupp⟩ := C.setup_exec hx₁ hb₁ hfr₁ hpar₁ hz₁
  rw [hmem₁] at hsupp
  exact ⟨ν₀, (ExecCodeDist.of_execWithin he_span).seq_pure he_setup, hinv, hsupp⟩

/-- Expected-time execution of `P.initClear` on arbitrary dirty memory. -/
theorem initClear_exec (C : ObliviousSequenceDS.{u, v, z} P S w base params)
    {x : Data r_ds} (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j) :
    ∃ ν₀ : PMF (LatentState C.Latent r_ds),
      ExecCodeDist w P.initClear x (ν₀.map LatentState.data) C.initClearTime ∧
      C.initInv ν₀ ∧
      ∀ t ∈ ν₀.support,
        t.data.regs P.frontierReg = base + C.space ∧
        Modifies (Block.mk base C.space).footprint x.mem t.data.mem := by
  obtain ⟨x₁, he_span, hmem₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  have hx₁ : x₁.Bounded w := he_span.bounded hx
  obtain ⟨x₂, he_zero, hx₂, hb₂, hfr₂, hpar₂, hz₂, hmod₂⟩ :=
    P.zeroFillCode_exec C.clear_nodup C.params_not_clear C.incCur_eval hx₁ hb₁ hfr₁ hpar₁
  obtain ⟨ν₀, he_setup, hinv, hsupp⟩ := C.setup_exec hx₂ hb₂ hfr₂ hpar₂ hz₂
  rw [hmem₁] at hmod₂
  have he_clear : ExecCodeDist w P.initClear x (ν₀.map LatentState.data) C.initClearTime := by
    unfold SubroutineCode.initClear initClearTime
    rw [add_assoc]
    exact (ExecCodeDist.of_execWithin he_span).seq_pure
      ((ExecCodeDist.of_execWithin he_zero).seq_pure he_setup)
  refine ⟨ν₀, he_clear, hinv, fun t ht => ?_⟩
  obtain ⟨hfr_t, hmod_t⟩ := hsupp t ht
  have hmod : Modifies (Block.mk base C.space).footprint x.mem t.data.mem := by
    simpa only [Finset.union_idempotent] using hmod₂.trans hmod_t
  exact ⟨hfr_t, hmod⟩

/-- **End-to-end expected-time and distributional correctness theorem from fresh initialization
(`seq_expected`).**
Starting from zeroed `[base, base + C.space)`, `P.initFresh` followed by any admissible oblivious
operation sequence `ops : List S.Op` (`S.ValidOpSeq ops`) executes in expected time at most
`C.initTime + C.initPotential + C.totalCharge ops` and induces an output transcript distribution
`ν_final.map SeqOutcome.transcript` satisfying `S.Contract ops`. -/
theorem seq_expected (C : ObliviousSequenceDS.{u, v, z} P S w base params)
    {x : Data r_ds} (ops : List S.Op)
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0)
    (hv : S.ValidOpSeq ops) :
    ∃ (ν₀ : PMF (LatentState C.Latent r_ds))
      (ν_final : PMF (SeqOutcome C.Latent S.Result r_ds)) (T_ops : ℝ≥0∞),
      ExecCodeDist w P.initFresh x (ν₀.map LatentState.data) C.initTime ∧
      C.Steps ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      S.Contract ops (ν_final.map SeqOutcome.transcript) ∧
      C.initTime + T_ops ≤
        C.initTime + (C.initPotential : ℝ≥0∞) + (C.totalCharge ops : ℝ≥0∞) := by
  obtain ⟨ν₀, he_init, hinv, _⟩ := C.initFresh_exec hx hfr hpar hz
  obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ := C.steps_exec ops ν₀ hv hinv
  refine ⟨ν₀, ν_final, T_ops, he_init, hex, hcontract, ?_⟩
  rw [add_assoc]
  exact add_le_add le_rfl hcost

/-- **End-to-end expected-time and distributional correctness theorem from dirty memory
(`seq_expected_clear`).** -/
theorem seq_expected_clear (C : ObliviousSequenceDS.{u, v, z} P S w base params)
    {x : Data r_ds} (ops : List S.Op)
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hv : S.ValidOpSeq ops) :
    ∃ (ν₀ : PMF (LatentState C.Latent r_ds))
      (ν_final : PMF (SeqOutcome C.Latent S.Result r_ds)) (T_ops : ℝ≥0∞),
      ExecCodeDist w P.initClear x (ν₀.map LatentState.data) C.initClearTime ∧
      C.Steps ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      S.Contract ops (ν_final.map SeqOutcome.transcript) ∧
      C.initClearTime + T_ops ≤
        C.initClearTime + (C.initPotential : ℝ≥0∞) + (C.totalCharge ops : ℝ≥0∞) := by
  obtain ⟨ν₀, he_init, hinv, _⟩ := C.initClear_exec hx hfr hpar
  obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ := C.steps_exec ops ν₀ hv hinv
  refine ⟨ν₀, ν_final, T_ops, he_init, hex, hcontract, ?_⟩
  rw [add_assoc]
  exact add_le_add le_rfl hcost

end ObliviousSequenceDS

/-! ## Part 3: Canonical Embedding of `SubroutineDS` into `ObliviousSequenceDS` -/

/-- Coupled latent seed, current abstract state, and accumulated relational transcript prefix for
embedding `Cslib.WordRAM.Randomized.SubroutineDS` into `ObliviousSequenceDS`. -/
structure TraceLatent (D : Stateful.Spec.{u, v, z}) (Seed : Type) : Type (max u v z) where
  /-- Latent random seed from the underlying `SubroutineDS`. -/
  seed : Seed
  /-- Current abstract state of `D`. -/
  state : D.State
  /-- Relational execution transcript accumulated since `s₀`. -/
  trace : D.Transcript

namespace SubroutineDS

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : Stateful.Spec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Project a `SeqOutcome (TraceLatent D C.Seed) D.Result r_ds` to
`CoupledState C.Seed D.State r_ds` by forgetting the accumulated transcript prefix. -/
private def projCoupled (C : SubroutineDS P D w base params s₀)
    (t : SeqOutcome (TraceLatent D C.Seed) D.Result r_ds) :
    CoupledState C.Seed D.State r_ds :=
  ⟨t.latent.seed, t.latent.state, t.data⟩

/-- Multi-step execution and potential-telescope helper for `SubroutineDS.toObliviousSequenceDS`. -/
private theorem steps_toObliviousSequenceDS (C : SubroutineDS P D w base params s₀)
    (opCharge : D.Op → ℕ)
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o)
    (prefOps remOps : List D.Op)
    (ν : PMF (SeqOutcome (TraceLatent D C.Seed) D.Result r_ds))
    (hseed : ∀ θ, ((ν.map C.projCoupled).map CoupledState.seed) θ ≤ C.seedSlack * C.seedLaw θ)
    (hsingle : C.singleState → ∃ s, ∀ t ∈ (ν.map C.projCoupled).support, t.state = s)
    (hsupp : ∀ t ∈ ν.support,
      t.latent.trace.ops = prefOps ∧
      t.latent.trace.labels = t.transcript ∧
      D.ValidTranscript s₀ t.latent.trace t.latent.state ∧
      D.ValidOpSeq t.latent.state remOps ∧
      C.rep t.latent.seed t.latent.state t.data) :
    ∃ (ν_final : PMF (SeqOutcome (TraceLatent D C.Seed) D.Result r_ds)) (T_ops : ℝ≥0∞),
      Randomized.ExecSteps P (D.toObliviousSequenceSpec s₀) (TraceLatent D C.Seed) w base
        C.space C.encode C.decode remOps ν ν_final T_ops ∧
      (∀ t ∈ ν_final.support,
        t.latent.trace.ops = prefOps ++ remOps ∧
        t.latent.trace.labels = t.transcript ∧
        D.ValidTranscript s₀ t.latent.trace t.latent.state) ∧
      T_ops + (∑' q, ν_final q * (C.potential q.latent.seed q.data : ℝ≥0∞)) ≤
        (((remOps.map opCharge).sum : ℕ) : ℝ≥0∞) +
          ∑' t, ν t * (C.potential t.latent.seed t.data : ℝ≥0∞) := by
  induction remOps generalizing prefOps ν with
  | nil =>
    refine ⟨ν, 0,
      Randomized.ExecSteps.nil (S := D.toObliviousSequenceSpec s₀) ν, fun t ht => ?_, by simp⟩
    obtain ⟨hops, hlbl, htr, _, _⟩ := hsupp t ht
    rw [List.append_nil]
    exact ⟨hops, hlbl, htr⟩
  | cons o os ih =>
    let prepCoupled : SeqOutcome (TraceLatent D C.Seed) D.Result r_ds →
        CoupledState C.Seed D.State r_ds :=
      fun t => ⟨t.latent.seed, t.latent.state, C.toDynamicProgram.prepare o t.data⟩
    let ν_prep : PMF (CoupledState C.Seed D.State r_ds) := ν.map prepCoupled
    have hsingle_prep : C.singleState → ∃ s, ∀ t' ∈ ν_prep.support, t'.state = s := by
      intro hd
      obtain ⟨s, hs⟩ := hsingle hd
      refine ⟨s, fun t' ht' => ?_⟩
      rw [PMF.mem_support_map_iff] at ht'
      obtain ⟨t, ht, rfl⟩ := ht'
      exact hs (C.projCoupled t) ((PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩)
    have hseed_prep : ∀ θ, (ν_prep.map CoupledState.seed) θ ≤ C.seedSlack * C.seedLaw θ := by
      intro θ
      have hmap : ν_prep.map CoupledState.seed = (ν.map C.projCoupled).map CoupledState.seed := by
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      rw [hmap]
      exact hseed θ
    have hsupp_prep : ∀ t' ∈ ν_prep.support,
        D.valid t'.state o ∧ C.rep t'.seed t'.state t'.data ∧ C.argMatch o t'.data.regs := by
      intro t' ht'
      rw [PMF.mem_support_map_iff] at ht'
      obtain ⟨t, ht, rfl⟩ := ht'
      obtain ⟨_, _, _, hv_t, hrep_t⟩ := hsupp t ht
      exact ⟨hv_t.1, C.prepare_rep hrep_t hv_t.1, C.prepare_argMatch o t.data⟩
    obtain ⟨μ_rel, T_rel, hstep_rel, hseed₁, hsingle₁, hamort₁⟩ :=
      C.step_exec o ν_prep hsingle_prep hseed_prep hsupp_prep
    have h_a_nonempty : Nonempty (D.Result o) := by
      obtain ⟨t₀, ht₀⟩ := ν.support_nonempty
      have ht₀' : prepCoupled t₀ ∈ ν_prep.support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨t₀, ht₀, rfl⟩
      obtain ⟨q₀, hq₀⟩ := (μ_rel (prepCoupled t₀)).support_nonempty
      obtain ⟨a₀, _, _, _, _⟩ := (hstep_rel (prepCoupled t₀) ht₀').2 q₀ hq₀
      exact ⟨a₀⟩
    let a_default : D.Result o := Classical.choice h_a_nonempty
    let outOf : CoupledState C.Seed D.State r_ds → D.Result o :=
      fun q => (C.decode o q.data.regs).getD a_default
    let liftStep (t : SeqOutcome (TraceLatent D C.Seed) D.Result r_ds)
        (q : CoupledState C.Seed D.State r_ds) :
        StepOutcome (TraceLatent D C.Seed) (D.Result o) r_ds :=
      ⟨⟨q.seed, q.state, t.latent.trace ++ [⟨o, outOf q, q.state⟩]⟩, q.data, outOf q⟩
    let μ_step (t : SeqOutcome (TraceLatent D C.Seed) D.Result r_ds) :
        PMF (StepOutcome (TraceLatent D C.Seed) (D.Result o) r_ds) :=
      (μ_rel (prepCoupled t)).map (liftStep t)
    let T_step (t : SeqOutcome (TraceLatent D C.Seed) D.Result r_ds) : ℝ≥0∞ :=
      T_rel (prepCoupled t)
    let ν₁ : PMF (SeqOutcome (TraceLatent D C.Seed) D.Result r_ds) :=
      ν.bind fun t => (μ_step t).map (t.appendStep o)
    have hproj_ν₁ : ν₁.map C.projCoupled = ν_prep.bind μ_rel := by
      dsimp only [ν₁, ν_prep, μ_step]
      rw [PMF.map_bind, PMF.bind_map]
      refine congrArg (ν.bind ·) (funext fun t => ?_)
      rw [PMF.map_comp, PMF.map_comp]
      exact PMF.map_id (μ_rel (prepCoupled t))
    have hseed₁' : ∀ θ, ((ν₁.map C.projCoupled).map CoupledState.seed) θ ≤
        C.seedSlack * C.seedLaw θ := by
      rw [hproj_ν₁]
      exact hseed₁
    have hsingle₁' : C.singleState → ∃ s', ∀ q ∈ (ν₁.map C.projCoupled).support, q.state = s' := by
      rw [hproj_ν₁]
      exact hsingle₁
    have hsupp₁ : ∀ q_seq ∈ ν₁.support,
        q_seq.latent.trace.ops = (prefOps ++ [o]) ∧
        q_seq.latent.trace.labels = q_seq.transcript ∧
        D.ValidTranscript s₀ q_seq.latent.trace q_seq.latent.state ∧
        D.ValidOpSeq q_seq.latent.state os ∧
        C.rep q_seq.latent.seed q_seq.latent.state q_seq.data := by
      intro q_seq hq_seq
      rw [PMF.mem_support_bind_iff] at hq_seq
      obtain ⟨t, ht, hq_map⟩ := hq_seq
      rw [PMF.mem_support_map_iff] at hq_map
      obtain ⟨u, hu, rfl⟩ := hq_map
      dsimp only [μ_step] at hu
      rw [PMF.mem_support_map_iff] at hu
      obtain ⟨q, hq, rfl⟩ := hu
      obtain ⟨hops_t, hlbl_t, htr_t, hv_t, _⟩ := hsupp t ht
      have ht' : prepCoupled t ∈ ν_prep.support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
      obtain ⟨a, hstep_a, hdec_a, hrep_q, _⟩ := (hstep_rel (prepCoupled t) ht').2 q hq
      have hout_eq : outOf q = a := by simp [outOf, hdec_a]
      refine ⟨?_, ?_, ?_, ?_, hrep_q⟩
      · simp [SeqOutcome.appendStep, liftStep, hops_t]
      · simp [SeqOutcome.appendStep, liftStep, hlbl_t]
      · refine htr_t.append ?_
        rw [hout_eq]
        exact .cons ⟨o, a, q.state⟩ hv_t.1 hstep_a (.nil q.state)
      · exact hv_t.2 q.state a hstep_a
    obtain ⟨ν_final, T_rest, hex_rest, htr_final, hamort_rest⟩ :=
      ih (prefOps ++ [o]) ν₁ hseed₁' hsingle₁' hsupp₁
    let T₁ : ℝ≥0∞ := ∑' t, ν t * T_step t
    have hex_cons : Randomized.ExecSteps P (D.toObliviousSequenceSpec s₀) (TraceLatent D C.Seed)
        w base C.space C.encode C.decode (o :: os) ν ν_final (T₁ + T_rest) := by
      refine Randomized.ExecSteps.cons (S := D.toObliviousSequenceSpec s₀)
        (μ_step := μ_step) (T_step := T_step) (fun t ht => ?_) hex_rest
      have ht' : prepCoupled t ∈ ν_prep.support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
      obtain ⟨he_rel, hq_rel⟩ := hstep_rel (prepCoupled t) ht'
      refine ⟨?_, ?_⟩
      · refine he_rel.congr_dist ?_ le_rfl
        dsimp only [μ_step]
        rw [PMF.map_comp]
        rfl
      · intro u hu
        dsimp only [μ_step] at hu
        rw [PMF.mem_support_map_iff] at hu
        obtain ⟨q, hq, rfl⟩ := hu
        obtain ⟨a, _, hdec_a, _, hmod_q⟩ := hq_rel q hq
        have hout_eq : outOf q = a := by simp [outOf, hdec_a]
        exact ⟨by simp [liftStep, hout_eq, hdec_a], hmod_q⟩
    have hT₁_eq : T₁ = ∑' t', ν_prep t' * T_rel t' :=
      (Cslib.Probability.PMF.tsum_map_mul ν prepCoupled T_rel).symm
    have hpot_ν₁ :
        (∑' q, ν₁ q * (C.potential q.latent.seed q.data : ℝ≥0∞)) =
          ∑' t', ν_prep t' * ∑' q, μ_rel t' q * (C.potential q.seed q.data : ℝ≥0∞) := by
      have hmap_pot :
          (∑' q, ν₁ q * (C.potential q.latent.seed q.data : ℝ≥0∞)) =
            ∑' q, (ν₁.map C.projCoupled) q * (C.potential q.seed q.data : ℝ≥0∞) :=
        (Cslib.Probability.PMF.tsum_map_mul ν₁ C.projCoupled
          fun q => (C.potential q.seed q.data : ℝ≥0∞)).symm
      rw [hmap_pot, hproj_ν₁, Cslib.Probability.PMF.tsum_bind_mul]
    have hstep_split :
        T₁ + (∑' q, ν₁ q * (C.potential q.latent.seed q.data : ℝ≥0∞)) =
          ∑' t', ν_prep t' *
            (T_rel t' + ∑' q, μ_rel t' q * (C.potential q.seed q.data : ℝ≥0∞)) := by
      rw [hT₁_eq, hpot_ν₁]
      simp only [← tsum_add, mul_add]
    have hpot_prep :
        (∑' t', ν_prep t' *
            ((C.charge t'.state o : ℝ≥0∞) + (C.potential t'.seed t'.data : ℝ≥0∞))) ≤
          (opCharge o : ℝ≥0∞) + ∑' t, ν t * (C.potential t.latent.seed t.data : ℝ≥0∞) := by
      rw [Cslib.Probability.PMF.tsum_map_mul]
      calc
        (∑' t, ν t * ((C.charge (prepCoupled t).state o : ℝ≥0∞) +
            (C.potential (prepCoupled t).seed (prepCoupled t).data : ℝ≥0∞)))
          ≤ ∑' t, ν t * ((opCharge o : ℝ≥0∞) + (C.potential t.latent.seed t.data : ℝ≥0∞)) := by
              refine tsum_le_tsum fun t => ?_
              by_cases ht : t ∈ ν.support
              · obtain ⟨_, _, _, hv_t, hrep_t⟩ := hsupp t ht
                refine mul_le_mul_right ?_ _
                dsimp only [prepCoupled]
                rw [C.prepare_potential hrep_t]
                exact add_le_add (Nat.cast_le.mpr (hcharge t.latent.state o hv_t.1)) le_rfl
              · rw [(PMF.apply_eq_zero_iff _ _).mpr ht, zero_mul, zero_mul]
        _ = (opCharge o : ℝ≥0∞) + ∑' t, ν t * (C.potential t.latent.seed t.data : ℝ≥0∞) := by
              simp_rw [mul_add, tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
    refine ⟨ν_final, T₁ + T_rest, hex_cons, fun t ht => ?_, ?_⟩
    · obtain ⟨hops, hlbl, htr⟩ := htr_final t ht
      rw [List.append_assoc, List.singleton_append] at hops
      exact ⟨hops, hlbl, htr⟩
    · simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      calc
        (T₁ + T_rest) + ∑' q, ν_final q * (C.potential q.latent.seed q.data : ℝ≥0∞)
          = T₁ + (T_rest + ∑' q, ν_final q * (C.potential q.latent.seed q.data : ℝ≥0∞)) := by
            ac_rfl
        _ ≤ T₁ + ((((os.map opCharge).sum : ℕ) : ℝ≥0∞) +
              ∑' q, ν₁ q * (C.potential q.latent.seed q.data : ℝ≥0∞)) :=
            add_le_add le_rfl hamort_rest
        _ = (((os.map opCharge).sum : ℕ) : ℝ≥0∞) +
              (T₁ + ∑' q, ν₁ q * (C.potential q.latent.seed q.data : ℝ≥0∞)) := by ac_rfl
        _ ≤ (((os.map opCharge).sum : ℕ) : ℝ≥0∞) +
              ((opCharge o : ℝ≥0∞) + ∑' t, ν t * (C.potential t.latent.seed t.data : ℝ≥0∞)) := by
            rw [hstep_split]
            exact add_le_add le_rfl (hamort₁.trans hpot_prep)
        _ = ((opCharge o : ℝ≥0∞) + (((os.map opCharge).sum : ℕ) : ℝ≥0∞)) +
              ∑' t, ν t * (C.potential t.latent.seed t.data : ℝ≥0∞) := by ac_rfl

/-- Canonical embedding of any relational `Cslib.WordRAM.Randomized.SubroutineDS` certificate into
`ObliviousSequenceDS` realizing `D.toObliviousSequenceSpec s₀`, given an operation-only charge
bound `opCharge : D.Op → ℕ` such that `∀ s o, D.valid s o → C.charge s o ≤ opCharge o`. -/
@[expose] noncomputable def toObliviousSequenceDS (C : SubroutineDS P D w base params s₀)
    (opCharge : D.Op → ℕ := C.charge s₀)
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o := by intros; exact le_rfl) :
    ObliviousSequenceDS.{v, z, max u v z} P (D.toObliviousSequenceSpec s₀) w base params where
  Latent := TraceLatent D C.Seed
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  initPotential := C.initPotential
  charge := opCharge
  initInv ν₀ :=
    (∀ θ, ((ν₀.map fun t => (⟨t.latent.seed, t.latent.state, t.data⟩ :
        CoupledState C.Seed D.State r_ds)).map CoupledState.seed) θ ≤
      C.seedSlack * C.seedLaw θ) ∧
    (C.singleState → ∃ s, ∀ t ∈ (ν₀.map fun t => (⟨t.latent.seed, t.latent.state, t.data⟩ :
        CoupledState C.Seed D.State r_ds)).support, t.state = s) ∧
    (∀ t ∈ ν₀.support,
      t.latent.state = s₀ ∧
      t.latent.trace = [] ∧
      C.rep t.latent.seed s₀ t.data ∧
      C.potential t.latent.seed t.data ≤ C.initPotential)
  encode := C.encode
  decode := C.decode
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval := C.incCur_eval
  span_exec := C.span_exec
  setup_exec hx₁ hb hfr hpar hz := by
    obtain ⟨ν₀, he, hseed, hsupp⟩ := C.setup_exec hx₁ hb hfr hpar hz
    let liftInit : C.Seed × Data r_ds → LatentState (TraceLatent D C.Seed) r_ds :=
      fun p => ⟨⟨p.1, s₀, []⟩, p.2⟩
    refine ⟨ν₀.map liftInit, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · refine he.congr_dist ?_ le_rfl
      rw [PMF.map_comp]
      rfl
    · intro θ
      rw [PMF.map_comp, PMF.map_comp]
      exact hseed θ
    · intro _
      refine ⟨s₀, fun t ht => ?_⟩
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      rw [PMF.mem_support_map_iff] at hu
      obtain ⟨p, _, rfl⟩ := hu
      rfl
    · intro t ht
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      obtain ⟨_, hrep, hpot, _⟩ := hsupp p hp
      exact ⟨rfl, rfl, hrep, hpot⟩
    · intro t ht
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      obtain ⟨hfr', _, _, hmod⟩ := hsupp p hp
      exact ⟨hfr', hmod⟩
  steps_exec ops ν₀ hv hinv := by
    obtain ⟨hseed₀, hsingle₀, hsupp₀⟩ := hinv
    let ν_seq : PMF (SeqOutcome (TraceLatent D C.Seed) D.Result r_ds) :=
      ν₀.map SeqOutcome.ofLatentState
    have hproj_eq : ν_seq.map C.projCoupled =
        ν₀.map fun t => (⟨t.latent.seed, t.latent.state, t.data⟩ :
          CoupledState C.Seed D.State r_ds) := by
      dsimp only [ν_seq]
      rw [PMF.map_comp]
      rfl
    have hseed_seq : ∀ θ, ((ν_seq.map C.projCoupled).map CoupledState.seed) θ ≤
        C.seedSlack * C.seedLaw θ := by
      rw [hproj_eq]
      exact hseed₀
    have hsingle_seq : C.singleState →
        ∃ s, ∀ t ∈ (ν_seq.map C.projCoupled).support, t.state = s := by
      rw [hproj_eq]
      exact hsingle₀
    have hsupp_seq : ∀ t ∈ ν_seq.support,
        t.latent.trace.ops = [] ∧
        t.latent.trace.labels = t.transcript ∧
        D.ValidTranscript s₀ t.latent.trace t.latent.state ∧
        D.ValidOpSeq t.latent.state ops ∧
        C.rep t.latent.seed t.latent.state t.data := by
      intro t ht
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      obtain ⟨hs_u, htr_u, hrep_u, _⟩ := hsupp₀ u hu
      dsimp only [SeqOutcome.ofLatentState]
      rw [hs_u, htr_u]
      exact ⟨rfl, rfl, .nil s₀, hv, hrep_u⟩
    obtain ⟨ν_final, T_ops, hex, htr_final, hamort⟩ :=
      C.steps_toObliviousSequenceDS opCharge hcharge [] ops ν_seq hseed_seq hsingle_seq hsupp_seq
    have hpot₀ :
        (∑' t, ν_seq t * (C.potential t.latent.seed t.data : ℝ≥0∞)) ≤ (C.initPotential : ℝ≥0∞) := by
      dsimp only [ν_seq]
      rw [Cslib.Probability.PMF.tsum_map_mul]
      calc
        (∑' u, ν₀ u * (C.potential u.latent.seed u.data : ℝ≥0∞))
          ≤ ∑' u, ν₀ u * (C.initPotential : ℝ≥0∞) := by
            refine tsum_le_tsum fun u => ?_
            by_cases hu : u ∈ ν₀.support
            · exact mul_le_mul_right (Nat.cast_le.mpr (hsupp₀ u hu).2.2.2) _
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hu, zero_mul, zero_mul]
        _ = (C.initPotential : ℝ≥0∞) := by
            rw [ENNReal.tsum_mul_right, ν₀.tsum_coe, one_mul]
    refine ⟨ν_final, T_ops, hex, ?_, ?_⟩
    · intro out hout
      rw [PMF.mem_support_map_iff] at hout
      obtain ⟨q, hq, rfl⟩ := hout
      obtain ⟨hops_q, hlbl_q, htr_q⟩ := htr_final q hq
      rw [List.nil_append] at hops_q
      exact ⟨q.latent.trace, q.latent.state, hops_q, hlbl_q, htr_q⟩
    · calc
        T_ops
          ≤ T_ops + ∑' q, ν_final q * (C.potential q.latent.seed q.data : ℝ≥0∞) := le_self_add
        _ ≤ (((ops.map opCharge).sum : ℕ) : ℝ≥0∞) +
              ∑' t, ν_seq t * (C.potential t.latent.seed t.data : ℝ≥0∞) := hamort
        _ ≤ (((ops.map opCharge).sum : ℕ) : ℝ≥0∞) + (C.initPotential : ℝ≥0∞) :=
            add_le_add le_rfl hpot₀
        _ = (C.initPotential : ℝ≥0∞) + (((ops.map opCharge).sum : ℕ) : ℝ≥0∞) := add_comm _ _

@[simp]
theorem toObliviousSequenceDS_space (C : SubroutineDS P D w base params s₀)
    (opCharge) (hcharge) :
    (C.toObliviousSequenceDS opCharge hcharge).space = C.space := by rfl

@[simp]
theorem toObliviousSequenceDS_initPotential (C : SubroutineDS P D w base params s₀)
    (opCharge) (hcharge) :
    (C.toObliviousSequenceDS opCharge hcharge).initPotential = C.initPotential := by rfl

@[simp]
theorem toObliviousSequenceDS_charge (C : SubroutineDS P D w base params s₀)
    (opCharge) (hcharge) :
    (C.toObliviousSequenceDS opCharge hcharge).charge = opCharge := by rfl

end SubroutineDS

/-! ## Part 4: `HashFamilyDS` — Word-RAM Hash-Family Data Structure Interface -/

/-- Embed a core hash-family register `i : Fin r_core` into `Fin (r_core + 5)`. -/
@[expose] def hashCoreReg {r_core : ℕ} (i : Fin r_core) : Fin (r_core + 5) :=
  Fin.castAdd 5 i

/-- Operation-tag register `r_core` (`0` for `.resample`, `1` for `.eval u`). -/
@[expose] def hashOpReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core, by omega⟩

/-- Scratch pointer register `r_core + 1` for `zeroFillCode` and `allocSpan`. -/
@[expose] def hashCurReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core + 1, by omega⟩

/-- Constant-`0` scratch register `r_core + 2` for `zeroFillCode` and operation dispatch. -/
@[expose] def hashZeroReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core + 2, by omega⟩

/-- Constant-`1` scratch register `r_core + 3` for `zeroFillCode`. -/
@[expose] def hashOneReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core + 3, by omega⟩

/-- Bump-pointer frontier register `r_core + 4` for `allocSpan` and `zeroFillCode`. -/
@[expose] def hashFrontierReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core + 4, by omega⟩

private theorem hashCoreReg_injective {r_core : ℕ} :
    Function.Injective (@hashCoreReg r_core) := by
  intro i j h
  simpa [hashCoreReg, Fin.ext_iff] using h

private theorem hashCoreReg_ne_of_val_ge {r_core : ℕ} (i : Fin r_core) {r : Fin (r_core + 5)}
    (hr : r_core ≤ r.val) : hashCoreReg i ≠ r := by
  intro h
  have hval := congrArg Fin.val h
  dsimp only [hashCoreReg, Fin.val_castAdd] at hval
  omega

private theorem hashFrontierReg_notMem_range_hashCoreReg {r_core : ℕ} :
    hashFrontierReg r_core ∉ Set.range (@hashCoreReg r_core) := by
  rintro ⟨i, hi⟩
  exact hashCoreReg_ne_of_val_ge i (by dsimp [hashFrontierReg]; omega) hi

/-- Reusable Word-RAM certificate for a resamplable hash-family data structure over universe `Fin U`
and codomain `Fin m` at word width `w`, base address `base`, and runtime initialization parameters
`params : Fin k_init → ℕ`.

Separates deterministic table precomputation (`initTableCode`, establishing `tableRep`), randomized
seed resampling (`resampleCode`, preserving `tableRep` and sampling `Seed` uniformly into
`seedRep`), and deterministic evaluation (`evalCode`, computing `(eval θ u).val` in `outReg` without
modifying memory). -/
structure HashFamilyDS (B : Basis) (r_core k_init w base U m : ℕ)
    (params : Fin k_init → ℕ) : Type 1 where
  /-- Finite type of hash seeds. -/
  Seed : Type
  /-- Finiteness instance on `Seed`. -/
  [seedFintype : Fintype Seed]
  /-- Nonemptiness instance on `Seed`. -/
  [seedNonempty : Nonempty Seed]
  /-- Pure mathematical hash evaluation map `Seed → Fin U → Fin m`. -/
  eval : Seed → Fin U → Fin m
  /-- Contiguous memory footprint length `[base, base + space)`. -/
  space : ℕ
  /-- Deterministic precomputed table invariant on memory (`fun _ => True` when none). -/
  tableRep : (ℕ → ℕ) → Prop := fun _ => True
  /-- Seed representation invariant linking `θ : Seed` to memory. -/
  seedRep : Seed → (ℕ → ℕ) → Prop
  /-- Persistent base-address register in `Fin r_core`. -/
  baseReg : Fin r_core
  /-- Input key register in `Fin r_core` for `evalCode`. -/
  keyReg : Fin r_core
  /-- Output hash-value register in `Fin r_core` for `evalCode`. -/
  outReg : Fin r_core
  /-- Registers carrying runtime parameters `params` into `initTableCode`. -/
  initParams : Fin k_init → Fin r_core
  /-- The input key register is distinct from `baseReg` so key preparation preserves `base`. -/
  key_ne_base : keyReg ≠ baseReg
  /-- Runtime parameter registers are distinct from `baseReg` so `allocSpan` preserves `params`. -/
  params_ne_base : ∀ j, initParams j ≠ baseReg
  /-- The end of the allocated footprint `base + space` fits in a `w`-bit word. -/
  fits_space : Fits w (base + space)
  /-- Single-instruction register addition `d ← a + b` over `B` on `Data (r_core + 5)`. -/
  addReg : Fin (r_core + 5) → Fin (r_core + 5) → Fin (r_core + 5) → Op B (r_core + 5)
  /-- `addReg d a b` sets register `d` to `x.regs a + x.regs b` when the sum fits in `w` bits. -/
  addReg_eval : ∀ {x : Data (r_core + 5)} (d a b : Fin (r_core + 5)),
    Fits w (x.regs a + x.regs b) →
    (addReg d a b).eval w x = some (x.set d (x.regs a + x.regs b))
  /-- Deterministic table initialization program on `Data r_core`. -/
  initTableCode : Code B r_core
  /-- Worst-case instruction bound for `initTableCode`. -/
  initTableSteps : ℕ
  /-- Randomized seed-resampling program on `Data r_core`. -/
  resampleCode : Code B r_core
  /-- Expected instruction bound for `resampleCode`. -/
  resampleSteps : ℕ
  /-- Deterministic hash-evaluation program on `Data r_core`. -/
  evalCode : Code B r_core
  /-- Worst-case instruction bound for `evalCode`. -/
  evalSteps : ℕ
  /-- Correctness and complexity of `initTableCode`: establishes `tableRep` and preserves `baseReg`
  while modifying only `[base, base + space)`. -/
  initTable_exec : ∀ {x : Data r_core},
    x.Bounded w → x.regs baseReg = base →
    (∀ j, x.regs (initParams j) = params j) →
    (∀ a ∈ (Block.mk base space).footprint, x.mem a = 0) →
    ∃ x₁, ExecWithin w initTableCode x x₁ initTableSteps ∧
      x₁.regs baseReg = base ∧
      tableRep x₁.mem ∧
      Modifies (Block.mk base space).footprint x.mem x₁.mem
  /-- Correctness and complexity of `resampleCode`: from any state with `x.regs baseReg = base` and
  `tableRep x.mem`, produces a coupled distribution `ν : PMF (LatentState Seed r_core)` whose seed
  marginal is `PMF.uniformOfFintype Seed`, preserving `baseReg` and `tableRep`, establishing
  `seedRep`, and modifying only `[base, base + space)`. -/
  resample_exec : ∀ {x : Data r_core},
    x.regs baseReg = base → tableRep x.mem →
    ∃ ν : PMF (LatentState Seed r_core),
      ExecCodeDist w resampleCode x (ν.map LatentState.data) resampleSteps ∧
      ν.map LatentState.latent = PMF.uniformOfFintype Seed ∧
      ∀ p ∈ ν.support,
        p.data.regs baseReg = base ∧
        tableRep p.data.mem ∧
        seedRep p.latent p.data.mem ∧
        Modifies (Block.mk base space).footprint x.mem p.data.mem
  /-- Correctness and complexity of `evalCode`: from any state with `x.regs baseReg = base`,
  `x.regs keyReg = u.val`, `tableRep x.mem`, and `seedRep θ x.mem`, halts within `evalSteps`
  instructions with `y.mem = x.mem`, `y.regs baseReg = base`, and `y.regs outReg = (eval θ u).val`.
  -/
  eval_exec : ∀ (θ : Seed) (u : Fin U) {x : Data r_core},
    x.regs baseReg = base → x.regs keyReg = u.val →
    tableRep x.mem → seedRep θ x.mem →
    ∃ y, ExecWithin w evalCode x y evalSteps ∧
      y.mem = x.mem ∧
      y.regs baseReg = base ∧
      y.regs outReg = (eval θ u).val

attribute [instance] HashFamilyDS.seedFintype HashFamilyDS.seedNonempty

namespace HashFamilyDS

variable {B B' : Basis} {r_core k_init w base U m : ℕ} {params : Fin k_init → ℕ}

/-- Build the `resample_exec` obligation of `HashFamilyDS` from an `ExecRand` computation
`m : ProbComp (Data r_core × ℕ)` and a memory seed-extraction function
`extractSeed : (ℕ → ℕ) → Seed`. -/
theorem resample_exec_of_execRand {Seed : Type} [Fintype Seed] [Nonempty Seed]
    {space resampleSteps : ℕ} {resampleCode : Code B r_core}
    {baseReg : Fin r_core} {tableRep : (ℕ → ℕ) → Prop} {seedRep : Seed → (ℕ → ℕ) → Prop}
    (extractSeed : (ℕ → ℕ) → Seed)
    {x : Data r_core} {m_comp : ProbComp (Data r_core × ℕ)}
    (hm : ExecRand w resampleCode x m_comp)
    (hunif : m_comp.eval.map (fun z => extractSeed z.1.mem) = PMF.uniformOfFintype Seed)
    (hsupp : ∀ z ∈ m_comp.support,
      z.1.regs baseReg = base ∧
      tableRep z.1.mem ∧
      seedRep (extractSeed z.1.mem) z.1.mem ∧
      Modifies (Block.mk base space).footprint x.mem z.1.mem ∧
      z.2 ≤ resampleSteps) :
    ∃ ν : PMF (LatentState Seed r_core),
      ExecCodeDist w resampleCode x (ν.map LatentState.data) resampleSteps ∧
      ν.map LatentState.latent = PMF.uniformOfFintype Seed ∧
      ∀ p ∈ ν.support,
        p.data.regs baseReg = base ∧
        tableRep p.data.mem ∧
        seedRep p.latent p.data.mem ∧
        Modifies (Block.mk base space).footprint x.mem p.data.mem := by
  let lift : Data r_core × ℕ → LatentState Seed r_core :=
    fun z => ⟨extractSeed z.1.mem, z.1⟩
  refine ⟨m_comp.eval.map lift, ?_, ?_, ?_⟩
  · refine (ExecCodeDist.of_execRand hm).congr_dist ?_ ?_
    · rw [ProbComp.eval_map, PMF.map_comp]
      rfl
    · calc
        ProbComp.expect m_comp (fun z => (z.2 : ℝ≥0∞))
          ≤ ProbComp.expect m_comp (fun _ => (resampleSteps : ℝ≥0∞)) :=
            ProbComp.expect_mono_on_support fun z hz => Nat.cast_le.mpr (hsupp z hz).2.2.2.2
        _ = (resampleSteps : ℝ≥0∞) := ProbComp.expect_const m_comp _
  · rw [PMF.map_comp]
    exact hunif
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    rw [ProbComp.support_eval] at hz
    obtain ⟨hb, htab, hseed, hmod, _⟩ := hsupp z hz
    exact ⟨hb, htab, hseed, hmod⟩

/-- Lift a `HashFamilyDS` certificate along a basis simulation `φ : B.Simulates B'`. -/
def mapSimulates (φ : B.Simulates B')
    (H : HashFamilyDS B r_core k_init w base U m params) :
    HashFamilyDS B' r_core k_init w base U m params where
  Seed := H.Seed
  eval := H.eval
  space := H.space
  tableRep := H.tableRep
  seedRep := H.seedRep
  baseReg := H.baseReg
  keyReg := H.keyReg
  outReg := H.outReg
  initParams := H.initParams
  key_ne_base := H.key_ne_base
  params_ne_base := H.params_ne_base
  fits_space := H.fits_space
  addReg d a b := (H.addReg d a b).mapSimulates φ
  addReg_eval d a b hfit := Op.eval_mapSimulates_of_some φ (H.addReg_eval d a b hfit)
  initTableCode := H.initTableCode.mapSimulates φ
  initTableSteps := H.initTableSteps
  resampleCode := H.resampleCode.mapSimulates φ
  resampleSteps := H.resampleSteps
  evalCode := H.evalCode.mapSimulates φ
  evalSteps := H.evalSteps
  initTable_exec hx hb hpar hz := by
    obtain ⟨x₁, he, hb₁, htab₁, hmod₁⟩ := H.initTable_exec hx hb hpar hz
    exact ⟨x₁, he.mapSimulates φ, hb₁, htab₁, hmod₁⟩
  resample_exec hb htab := by
    obtain ⟨ν, he, hunif, hsupp⟩ := H.resample_exec hb htab
    exact ⟨ν, he.mapSimulates φ, hunif, hsupp⟩
  eval_exec θ u {x} hb hk htab hseed := by
    obtain ⟨y, he, hmem, hb', hout⟩ := H.eval_exec θ u hb hk htab hseed
    exact ⟨y, he.mapSimulates φ, hmem, hb', hout⟩

/-- Lift a `HashFamilyDS` certificate from `Basis.exact` to `Basis.standard`. -/
def toStandard (H : HashFamilyDS .exact r_core k_init w base U m params) :
    HashFamilyDS .standard r_core k_init w base U m params :=
  H.mapSimulates .exactStandard

/-- Canonical `SubroutineCode` on `Data (r_core + 5)` wrapping `H : HashFamilyDS`:
* `allocSpan` copies `frontierReg` into `hashCoreReg H.baseReg` and advances `frontierReg` by
  `H.space`;
* `initSetup` runs `H.initTableCode` followed by `H.resampleCode` on the core registers;
* `code` sets `hashZeroReg r_core ← 0` and branches on `hashOpReg r_core == 0` between
  `H.resampleCode` (`.resample`) and `H.evalCode` (`.eval u`). -/
@[expose] def subroutineCode (H : HashFamilyDS B r_core k_init w base U m params) :
    SubroutineCode B (r_core + 5) k_init where
  allocSpan :=
    .seq (.op (.copy (hashCoreReg H.baseReg) (hashFrontierReg r_core)))
    (.seq (.op (.const (hashCurReg r_core) H.space))
          (.op (H.addReg (hashFrontierReg r_core) (hashFrontierReg r_core) (hashCurReg r_core))))
  initSetup :=
    .seq (H.initTableCode.rename hashCoreReg) (H.resampleCode.rename hashCoreReg)
  code :=
    .seq (.op (.const (hashZeroReg r_core) 0))
         (.branch (.eq (hashOpReg r_core) (hashZeroReg r_core))
           (H.resampleCode.rename hashCoreReg)
           (H.evalCode.rename hashCoreReg))
  frontierReg := hashFrontierReg r_core
  baseReg := hashCoreReg H.baseReg
  initParams j := hashCoreReg (H.initParams j)
  curReg := hashCurReg r_core
  zeroReg := hashZeroReg r_core
  oneReg := hashOneReg r_core
  incCur := H.addReg (hashCurReg r_core) (hashCurReg r_core) (hashOneReg r_core)
  input r := decide (r = hashOpReg r_core ∨ r = hashCoreReg H.keyReg)
  output := hashCoreReg H.outReg

/-- Standalone register encoding for `HashOp U` on `H.subroutineCode`:
* `.resample` sets `hashOpReg r_core ← 0` and `hashCoreReg H.keyReg ← 0`;
* `.eval u` sets `hashOpReg r_core ← 1` and `hashCoreReg H.keyReg ← u.val`. -/
@[expose] def encode (H : HashFamilyDS B r_core k_init w base U m params) :
    DataStructure.HashOp U → Fin (r_core + 5) → ℕ
  | .resample, _ => 0
  | .eval u, r =>
    if r = hashOpReg r_core then 1
    else if r = hashCoreReg H.keyReg then u.val
    else 0

/-- Output decoder for `HashOp U` on `H.subroutineCode`: returns `some PUnit.unit` on `.resample`
and reads `regs (hashCoreReg H.outReg) < m` on `.eval u`. -/
@[expose] def decode (H : HashFamilyDS B r_core k_init w base U m params) :
    (o : DataStructure.HashOp U) → (Fin (r_core + 5) → ℕ) → Option (DataStructure.HashResult m o)
  | .resample, _ => some PUnit.unit
  | .eval _, regs =>
    if h : regs (hashCoreReg H.outReg) < m then
      some ⟨regs (hashCoreReg H.outReg), h⟩
    else
      none

/-- Per-operation instruction charge on `H.subroutineCode`: `H.resampleSteps + 2` for `.resample`
and `H.evalSteps + 3` for `.eval u`. -/
@[expose] def charge (H : HashFamilyDS B r_core k_init w base U m params) :
    DataStructure.HashOp U → ℕ
  | .resample => H.resampleSteps + 2
  | .eval _ => H.evalSteps + 3

/-- Distributional invariant on the initial state distribution produced by
`H.subroutineCode.initSetup`. -/
@[expose] def initInv (H : HashFamilyDS B r_core k_init w base U m params)
    (ν₀ : PMF (LatentState H.Seed (r_core + 5))) : Prop :=
  ν₀.map LatentState.latent = PMF.uniformOfFintype H.Seed ∧
  ∀ t ∈ ν₀.support,
    t.data.regs (hashCoreReg H.baseReg) = base ∧
    H.tableRep t.data.mem ∧
    H.seedRep t.latent t.data.mem

private theorem clear_nodup_subroutineCode
    (H : HashFamilyDS B r_core k_init w base U m params) :
    [H.subroutineCode.curReg, H.subroutineCode.zeroReg, H.subroutineCode.oneReg,
      H.subroutineCode.baseReg, H.subroutineCode.frontierReg].Nodup := by
  have hb := H.baseReg.isLt
  simp only [subroutineCode, hashCurReg, hashZeroReg, hashOneReg, hashCoreReg, hashFrontierReg,
    Fin.castAdd, Fin.castLE, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    Fin.mk.injEq, List.nodup_nil, not_false_eq_true, and_true]
  omega

private theorem params_not_clear_subroutineCode
    (H : HashFamilyDS B r_core k_init w base U m params) (j : Fin k_init) :
    H.subroutineCode.initParams j ∉
      [H.subroutineCode.curReg, H.subroutineCode.zeroReg, H.subroutineCode.oneReg] := by
  have hj := (H.initParams j).isLt
  simp only [subroutineCode, hashCurReg, hashZeroReg, hashOneReg, hashCoreReg,
    Fin.castAdd, Fin.castLE, List.mem_cons, List.not_mem_nil, or_false, not_or, Fin.mk.injEq]
  omega

private theorem span_exec_subroutineCode
    (H : HashFamilyDS B r_core k_init w base U m params)
    {x : Data (r_core + 5)}
    (hfr : x.regs H.subroutineCode.frontierReg = base)
    (hpar : ∀ j, x.regs (H.subroutineCode.initParams j) = params j) :
    ∃ x₁, ExecWithin w H.subroutineCode.allocSpan x x₁ 3 ∧ x₁.mem = x.mem ∧
      x₁.regs H.subroutineCode.baseReg = base ∧
      x₁.regs H.subroutineCode.frontierReg = base + H.space ∧
      (∀ j, x₁.regs (H.subroutineCode.initParams j) = params j) := by
  have hfr' : x.regs (hashFrontierReg r_core) = base := hfr
  have hfit_sp : Fits w H.space := H.fits_space.of_le (Nat.le_add_left H.space base)
  set s₁ := x.set (hashCoreReg H.baseReg) base
  have e₁ : ExecWithin (B := B) w
      (.op (.copy (hashCoreReg H.baseReg) (hashFrontierReg r_core))) x s₁ 1 := by
    simpa [s₁, hfr'] using
      (Exec.copy (B := B) (w := w) (d := hashCoreReg H.baseReg)
        (s := hashFrontierReg r_core) (x := x)).within
  set s₂ := s₁.set (hashCurReg r_core) H.space
  have e₂ : ExecWithin (B := B) w (.op (.const (hashCurReg r_core) H.space)) s₁ s₂ 1 :=
    (Exec.const hfit_sp).within
  have hs₂_fr : s₂.regs (hashFrontierReg r_core) = base := by
    have hne₁ : hashFrontierReg r_core ≠ hashCurReg r_core := by
      simp [hashFrontierReg, hashCurReg, Fin.ext_iff]
    have hne₂ : hashFrontierReg r_core ≠ hashCoreReg H.baseReg :=
      (hashCoreReg_ne_of_val_ge H.baseReg (by simp [hashFrontierReg])).symm
    simp [s₂, s₁, Data.set, Function.update_of_ne hne₁, Function.update_of_ne hne₂, hfr']
  have hs₂_cur : s₂.regs (hashCurReg r_core) = H.space := by simp [s₂]
  set s₃ := s₂.set (hashFrontierReg r_core) (base + H.space)
  have e₃ : ExecWithin w
      (.op (H.addReg (hashFrontierReg r_core) (hashFrontierReg r_core) (hashCurReg r_core)))
      s₂ s₃ 1 := by
    have heval := H.addReg_eval (x := s₂)
      (hashFrontierReg r_core) (hashFrontierReg r_core) (hashCurReg r_core)
      (by rw [hs₂_fr, hs₂_cur]; exact H.fits_space)
    rw [hs₂_fr, hs₂_cur] at heval
    exact (Exec.op heval).within
  refine ⟨s₃, (e₁.seq (e₂.seq e₃)).mono (by omega), rfl, ?_, by simp [s₃, subroutineCode], ?_⟩
  · have hne₁ : hashCoreReg H.baseReg ≠ hashFrontierReg r_core :=
      hashCoreReg_ne_of_val_ge H.baseReg (by simp [hashFrontierReg])
    have hne₂ : hashCoreReg H.baseReg ≠ hashCurReg r_core :=
      hashCoreReg_ne_of_val_ge H.baseReg (by simp [hashCurReg])
    simp [s₃, s₂, s₁, subroutineCode, Data.set,
      Function.update_of_ne hne₁, Function.update_of_ne hne₂]
  · intro j
    have hne₁ : hashCoreReg (H.initParams j) ≠ hashFrontierReg r_core :=
      hashCoreReg_ne_of_val_ge (H.initParams j) (by simp [hashFrontierReg])
    have hne₂ : hashCoreReg (H.initParams j) ≠ hashCurReg r_core :=
      hashCoreReg_ne_of_val_ge (H.initParams j) (by simp [hashCurReg])
    have hne₃ : hashCoreReg (H.initParams j) ≠ hashCoreReg H.baseReg :=
      fun h => H.params_ne_base j (hashCoreReg_injective h)
    simp only [s₃, s₂, s₁, subroutineCode, Data.set,
      Function.update_of_ne hne₁, Function.update_of_ne hne₂, Function.update_of_ne hne₃]
    exact hpar j

private theorem setup_exec_subroutineCode
    (H : HashFamilyDS B r_core k_init w base U m params)
    {x₁ : Data (r_core + 5)}
    (hx₁ : x₁.Bounded w)
    (hb : x₁.regs H.subroutineCode.baseReg = base)
    (hfr : x₁.regs H.subroutineCode.frontierReg = base + H.space)
    (hpar : ∀ j, x₁.regs (H.subroutineCode.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base H.space).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (LatentState H.Seed (r_core + 5)),
      ExecCodeDist w H.subroutineCode.initSetup x₁ (ν₀.map LatentState.data)
        ((H.initTableSteps + H.resampleSteps : ℕ) : ℝ≥0∞) ∧
      H.initInv ν₀ ∧
      ∀ t ∈ ν₀.support,
        t.data.regs H.subroutineCode.frontierReg = base + H.space ∧
        Modifies (Block.mk base H.space).footprint x₁.mem t.data.mem := by
  obtain ⟨y_tab, he_tab, hy_base, hy_tab, hy_mod⟩ :=
    H.initTable_exec (hx₁.comap hashCoreReg) hb hpar hz
  let x₂ : Data (r_core + 5) := y_tab.extend hashCoreReg x₁
  have he_tab_ren : ExecCodeDist w (H.initTableCode.rename hashCoreReg) x₁ (PMF.pure x₂)
      (H.initTableSteps : ℝ≥0∞) := by
    simpa [x₂] using (ExecCodeDist.of_execWithin he_tab).rename hashCoreReg_injective
  have hx₂_comap : x₂.comap hashCoreReg = y_tab :=
    Data.comap_extend hashCoreReg_injective y_tab x₁
  obtain ⟨ν_core, he_res, hunif, hsupp_res⟩ :=
    H.resample_exec (x := x₂.comap hashCoreReg)
      (by rw [hx₂_comap]; exact hy_base)
      (by rw [hx₂_comap]; exact hy_tab)
  have he_res_ren := he_res.rename hashCoreReg_injective
  let lift0 : LatentState H.Seed r_core → LatentState H.Seed (r_core + 5) :=
    fun p => ⟨p.latent, p.data.extend hashCoreReg x₂⟩
  let ν₀ : PMF (LatentState H.Seed (r_core + 5)) := ν_core.map lift0
  have he_res_ν₀ : ExecCodeDist w (H.resampleCode.rename hashCoreReg) x₂
      (ν₀.map LatentState.data) (H.resampleSteps : ℝ≥0∞) := by
    refine he_res_ren.congr_dist ?_ le_rfl
    dsimp only [ν₀, lift0]
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  refine ⟨ν₀, ?_, ⟨?_, ?_⟩, ?_⟩
  · simpa only [subroutineCode, Nat.cast_add] using he_tab_ren.seq_pure he_res_ν₀
  · dsimp only [ν₀, lift0]
    rw [PMF.map_comp]
    exact hunif
  · intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    obtain ⟨hp_base, hp_tab, hp_seed, _⟩ := hsupp_res p hp
    have hreg : (p.data.extend hashCoreReg x₂).regs (hashCoreReg H.baseReg) = base := by
      change ((p.data.extend hashCoreReg x₂).comap hashCoreReg).regs H.baseReg = base
      rw [Data.comap_extend hashCoreReg_injective]
      exact hp_base
    exact ⟨hreg, hp_tab, hp_seed⟩
  · intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    obtain ⟨_, _, _, hp_mod⟩ := hsupp_res p hp
    have hfr_t : (p.data.extend hashCoreReg x₂).regs (hashFrontierReg r_core) = base + H.space := by
      rw [Data.extend_regs_of_notMem _ _ hashFrontierReg_notMem_range_hashCoreReg,
        Data.extend_regs_of_notMem _ _ hashFrontierReg_notMem_range_hashCoreReg]
      exact hfr
    have hmod_t : Modifies (Block.mk base H.space).footprint x₁.mem p.data.mem := by
      simpa only [Data.comap, Finset.union_idempotent] using hy_mod.trans hp_mod
    exact ⟨hfr_t, hmod_t⟩

private theorem step_resample_subroutineCode
    (H : HashFamilyDS B r_core k_init w base U m params)
    (t : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5))
    (hb : t.data.regs (hashCoreReg H.baseReg) = base)
    (htab : H.tableRep t.data.mem) :
    ∃ μ_t : PMF (StepOutcome H.Seed PUnit (r_core + 5)),
      ExecCodeDist w H.subroutineCode.code
        ((H.subroutineCode.toDynamicProgram H.encode H.decode).prepare .resample t.data)
        (μ_t.map StepOutcome.data) ((H.charge .resample : ℕ) : ℝ≥0∞) ∧
      μ_t.map StepOutcome.latent = PMF.uniformOfFintype H.Seed ∧
      ∀ q ∈ μ_t.support,
        H.decode .resample q.data.regs = some q.result ∧
        Modifies (Block.mk base H.space).footprint t.data.mem q.data.mem ∧
        q.data.regs (hashCoreReg H.baseReg) = base ∧
        H.tableRep q.data.mem ∧
        H.seedRep q.latent q.data.mem := by
  let x_prep := (H.subroutineCode.toDynamicProgram H.encode H.decode).prepare .resample t.data
  let x_z := x_prep.set (hashZeroReg r_core) 0
  have he_z : ExecCodeDist (B := B) w (.op (.const (hashZeroReg r_core) 0))
      x_prep (PMF.pure x_z) 1 := by
    simpa [x_z] using ExecCodeDist.of_exec (Exec.const (H.fits_space.of_le (Nat.zero_le _)))
  have hc_pos : (Cond.eq (hashOpReg r_core) (hashZeroReg r_core)).Holds x_z := by
    have hne : hashOpReg r_core ≠ hashZeroReg r_core := by
      simp [hashOpReg, hashZeroReg, Fin.ext_iff]
    simp [Cond.Holds, x_z, x_prep, SubroutineCode.toDynamicProgram, DynamicProgram.prepare,
      subroutineCode, encode, Data.set, Function.update_of_ne hne]
  have hxz_base : (x_z.comap hashCoreReg).regs H.baseReg = base := by
    have hne_z : hashCoreReg H.baseReg ≠ hashZeroReg r_core :=
      hashCoreReg_ne_of_val_ge H.baseReg (by simp [hashZeroReg])
    have hne_op : hashCoreReg H.baseReg ≠ hashOpReg r_core :=
      hashCoreReg_ne_of_val_ge H.baseReg (by simp [hashOpReg])
    have hne_key : hashCoreReg H.baseReg ≠ hashCoreReg H.keyReg :=
      fun h => H.key_ne_base (hashCoreReg_injective h.symm)
    simp [x_z, x_prep, Data.comap, Data.set, Function.update_of_ne hne_z,
      SubroutineCode.toDynamicProgram, DynamicProgram.prepare, subroutineCode,
      hne_op, hne_key, hb]
  have hxz_mem : (x_z.comap hashCoreReg).mem = t.data.mem := rfl
  obtain ⟨ν_core, he_res, hunif, hsupp⟩ :=
    H.resample_exec hxz_base (by rw [hxz_mem]; exact htab)
  have he_res_ren := he_res.rename hashCoreReg_injective
  let liftStep : LatentState H.Seed r_core → StepOutcome H.Seed PUnit (r_core + 5) :=
    fun p => ⟨p.latent, p.data.extend hashCoreReg x_z, PUnit.unit⟩
  let μ_t : PMF (StepOutcome H.Seed PUnit (r_core + 5)) := ν_core.map liftStep
  have he_branch : ExecCodeDist w
      (.branch (.eq (hashOpReg r_core) (hashZeroReg r_core))
        (H.resampleCode.rename hashCoreReg)
        (H.evalCode.rename hashCoreReg))
      x_z (μ_t.map StepOutcome.data) ((H.resampleSteps : ℝ≥0∞) + 1) := by
    refine (ExecCodeDist.branch_pos hc_pos he_res_ren).congr_dist ?_ le_rfl
    dsimp only [μ_t, liftStep]
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  refine ⟨μ_t, ?_, ?_, ?_⟩
  · have hseq := he_z.seq_pure he_branch
    refine hseq.congr_dist rfl (le_of_eq ?_)
    simp only [charge, Nat.cast_add, Nat.cast_ofNat]
    ring
  · dsimp only [μ_t, liftStep]
    rw [PMF.map_comp]
    exact hunif
  · intro q hq
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨hp_base, hp_tab, hp_seed, hp_mod⟩ := hsupp p hp
    have hreg : (p.data.extend hashCoreReg x_z).regs (hashCoreReg H.baseReg) = base := by
      change ((p.data.extend hashCoreReg x_z).comap hashCoreReg).regs H.baseReg = base
      rw [Data.comap_extend hashCoreReg_injective]
      exact hp_base
    exact ⟨rfl, hp_mod, hreg, hp_tab, hp_seed⟩

private theorem step_eval_subroutineCode
    (H : HashFamilyDS B r_core k_init w base U m params) (u : Fin U)
    (t : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5))
    (hb : t.data.regs (hashCoreReg H.baseReg) = base)
    (htab : H.tableRep t.data.mem)
    (hseed : H.seedRep t.latent t.data.mem) :
    ∃ y_ext : Data (r_core + 5),
      ExecCodeDist w H.subroutineCode.code
        ((H.subroutineCode.toDynamicProgram H.encode H.decode).prepare (.eval u) t.data)
        (PMF.pure y_ext) ((H.charge (.eval u) : ℕ) : ℝ≥0∞) ∧
      H.decode (.eval u) y_ext.regs = some (H.eval t.latent u) ∧
      y_ext.mem = t.data.mem ∧
      y_ext.regs (hashCoreReg H.baseReg) = base := by
  let x_prep := (H.subroutineCode.toDynamicProgram H.encode H.decode).prepare (.eval u) t.data
  let x_z := x_prep.set (hashZeroReg r_core) 0
  have he_z : ExecCodeDist (B := B) w (.op (.const (hashZeroReg r_core) 0))
      x_prep (PMF.pure x_z) 1 := by
    simpa [x_z] using ExecCodeDist.of_exec (Exec.const (H.fits_space.of_le (Nat.zero_le _)))
  have hc_neg : ¬(Cond.eq (hashOpReg r_core) (hashZeroReg r_core)).Holds x_z := by
    have hne : hashOpReg r_core ≠ hashZeroReg r_core := by
      simp [hashOpReg, hashZeroReg, Fin.ext_iff]
    simp [Cond.Holds, x_z, x_prep, SubroutineCode.toDynamicProgram, DynamicProgram.prepare,
      subroutineCode, encode, Data.set, Function.update_of_ne hne]
  have hxz_base : (x_z.comap hashCoreReg).regs H.baseReg = base := by
    have hne_z : hashCoreReg H.baseReg ≠ hashZeroReg r_core :=
      hashCoreReg_ne_of_val_ge H.baseReg (by simp [hashZeroReg])
    have hne_op : hashCoreReg H.baseReg ≠ hashOpReg r_core :=
      hashCoreReg_ne_of_val_ge H.baseReg (by simp [hashOpReg])
    have hne_key : hashCoreReg H.baseReg ≠ hashCoreReg H.keyReg :=
      fun h => H.key_ne_base (hashCoreReg_injective h.symm)
    simp [x_z, x_prep, Data.comap, Data.set, Function.update_of_ne hne_z,
      SubroutineCode.toDynamicProgram, DynamicProgram.prepare, subroutineCode,
      hne_op, hne_key, hb]
  have hxz_key : (x_z.comap hashCoreReg).regs H.keyReg = u.val := by
    have hne_z : hashCoreReg H.keyReg ≠ hashZeroReg r_core :=
      hashCoreReg_ne_of_val_ge H.keyReg (by simp [hashZeroReg])
    have hne_op : hashCoreReg H.keyReg ≠ hashOpReg r_core :=
      hashCoreReg_ne_of_val_ge H.keyReg (by simp [hashOpReg])
    simp [x_z, x_prep, Data.comap, Data.set, Function.update_of_ne hne_z,
      SubroutineCode.toDynamicProgram, DynamicProgram.prepare, subroutineCode,
      encode, hne_op]
  obtain ⟨y_core, he_eval, hy_mem, hy_base, hy_out⟩ :=
    H.eval_exec t.latent u hxz_base hxz_key htab hseed
  let y_ext : Data (r_core + 5) := y_core.extend hashCoreReg x_z
  have he_eval_ren : ExecCodeDist w (H.evalCode.rename hashCoreReg) x_z
      (PMF.pure y_ext) (H.evalSteps : ℝ≥0∞) := by
    simpa [y_ext] using (ExecCodeDist.of_execWithin he_eval).rename hashCoreReg_injective
  have he_branch : ExecCodeDist w
      (.branch (.eq (hashOpReg r_core) (hashZeroReg r_core))
        (H.resampleCode.rename hashCoreReg)
        (H.evalCode.rename hashCoreReg))
      x_z (PMF.pure y_ext) ((H.evalSteps : ℝ≥0∞) + 2) :=
    ExecCodeDist.branch_neg hc_neg he_eval_ren
  have hy_out_ext : y_ext.regs (hashCoreReg H.outReg) = (H.eval t.latent u).val := by
    change (y_ext.comap hashCoreReg).regs H.outReg = (H.eval t.latent u).val
    rw [Data.comap_extend hashCoreReg_injective]
    exact hy_out
  have hy_base_ext : y_ext.regs (hashCoreReg H.baseReg) = base := by
    change (y_ext.comap hashCoreReg).regs H.baseReg = base
    rw [Data.comap_extend hashCoreReg_injective]
    exact hy_base
  refine ⟨y_ext, ?_, ?_, hy_mem, hy_base_ext⟩
  · refine (he_z.seq_pure he_branch).congr_dist rfl (le_of_eq ?_)
    simp only [charge, Nat.cast_add, Nat.cast_ofNat]
    ring
  · simp [decode, hy_out_ext, (H.eval t.latent u).isLt]

private theorem steps_subroutineCode
    (H : HashFamilyDS B r_core k_init w base U m params)
    (ValidOpSeq : List (DataStructure.HashOp U) → Prop)
    (Contract : List (DataStructure.HashOp U) → PMF (List (DataStructure.HashLabel U m)) → Prop)
    (remOps : List (DataStructure.HashOp U))
    (ν : PMF (SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5)))
    (hsupp : ∀ t ∈ ν.support,
      t.data.regs (hashCoreReg H.baseReg) = base ∧
      H.tableRep t.data.mem ∧
      H.seedRep t.latent t.data.mem) :
    let S : DataStructure.ObliviousSequenceSpec :=
      ⟨DataStructure.HashOp U, @DataStructure.HashResult U m, ValidOpSeq, Contract⟩
    ∃ (ν_final : PMF (SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5)))
      (T_ops : ℝ≥0∞),
      Randomized.ExecSteps H.subroutineCode S H.Seed w base H.space H.encode H.decode
        remOps ν ν_final T_ops ∧
      ν_final.map SeqOutcome.transcript =
        ν.bind (fun t =>
          (DataStructure.evalHashOpsFromSeed (PMF.uniformOfFintype H.Seed) H.eval t.latent
            remOps).map (fun suf => t.transcript ++ suf)) ∧
      T_ops ≤ (((remOps.map H.charge).sum : ℕ) : ℝ≥0∞) := by
  intro S
  induction remOps generalizing ν with
  | nil =>
    refine ⟨ν, 0, Randomized.ExecSteps.nil (S := S) ν, ?_, by simp⟩
    ext tr
    simp [DataStructure.evalHashOpsFromSeed]
  | cons o os ih =>
    cases o with
    | resample =>
      classical
      let hasInv (t : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5)) : Prop :=
        t.data.regs (hashCoreReg H.baseReg) = base ∧ H.tableRep t.data.mem
      let θ₀ : H.Seed := Classical.arbitrary H.Seed
      let μ_step (t : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5)) :
          PMF (StepOutcome H.Seed PUnit (r_core + 5)) :=
        if ht : hasInv t then
          Classical.choose (H.step_resample_subroutineCode t ht.1 ht.2)
        else
          PMF.pure ⟨θ₀, t.data, PUnit.unit⟩
      let T_step : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5) → ℝ≥0∞ :=
        fun _ => ((H.charge .resample : ℕ) : ℝ≥0∞)
      let ν₁ := ν.bind fun t => (μ_step t).map (t.appendStep .resample)
      have hsupp₁ : ∀ q_seq ∈ ν₁.support,
          q_seq.data.regs (hashCoreReg H.baseReg) = base ∧
          H.tableRep q_seq.data.mem ∧
          H.seedRep q_seq.latent q_seq.data.mem := by
        intro q_seq hq_seq
        rw [PMF.mem_support_bind_iff] at hq_seq
        obtain ⟨t, ht, hq_map⟩ := hq_seq
        rw [PMF.mem_support_map_iff] at hq_map
        obtain ⟨q, hq, rfl⟩ := hq_map
        have ht_inv : hasInv t := ⟨(hsupp t ht).1, (hsupp t ht).2.1⟩
        have hμ_eq : μ_step t =
            Classical.choose (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2) := by
          simp [μ_step, ht_inv]
        rw [hμ_eq] at hq
        have hspec := (Classical.choose_spec
          (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2)).2.2 q hq
        exact ⟨hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2⟩
      obtain ⟨ν_final, T_rest, hex_rest, htr_rest, hcost_rest⟩ := ih ν₁ hsupp₁
      have hex_cons : Randomized.ExecSteps H.subroutineCode S H.Seed w base H.space
          H.encode H.decode (.resample :: os) ν ν_final
          ((∑' t, ν t * T_step t) + T_rest) := by
        refine Randomized.ExecSteps.cons (S := S) (μ_step := μ_step) (T_step := T_step)
          (fun t ht => ?_) hex_rest
        have ht_inv : hasInv t := ⟨(hsupp t ht).1, (hsupp t ht).2.1⟩
        have hμ_eq : μ_step t =
            Classical.choose (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2) := by
          simp [μ_step, ht_inv]
        have hspec := Classical.choose_spec (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2)
        rw [hμ_eq]
        exact ⟨hspec.1, fun q hq => ⟨(hspec.2.2 q hq).1, (hspec.2.2 q hq).2.1⟩⟩
      have hT₁ : (∑' t, ν t * T_step t) = ((H.charge .resample : ℕ) : ℝ≥0∞) := by
        dsimp only [T_step]
        rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
      refine ⟨ν_final, (∑' t, ν t * T_step t) + T_rest, hex_cons, ?_, ?_⟩
      · rw [htr_rest]
        dsimp only [ν₁]
        rw [PMF.bind_bind]
        refine PMF.bind_congr_on_support _ _ _ fun t ht => ?_
        have ht_inv : hasInv t := ⟨(hsupp t ht).1, (hsupp t ht).2.1⟩
        have hμ_eq : μ_step t =
            Classical.choose (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2) := by
          simp [μ_step, ht_inv]
        have hunif_t : (μ_step t).map StepOutcome.latent = PMF.uniformOfFintype H.Seed := by
          rw [hμ_eq]
          exact (Classical.choose_spec (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2)).2.1
        rw [PMF.bind_map, DataStructure.evalHashOpsFromSeed, PMF.map_bind, ← hunif_t, PMF.bind_map]
        refine congrArg ((μ_step t).bind ·) (funext fun q => ?_)
        rcases q with ⟨θ', x_q, ⟨⟩⟩
        dsimp only [Function.comp_apply, StepOutcome.latent]
        rw [PMF.map_comp]
        refine congrArg (PMF.map · _) (funext fun suf => ?_)
        simp [SeqOutcome.appendStep]
      · simp only [List.map_cons, List.sum_cons, Nat.cast_add, hT₁]
        exact add_le_add le_rfl hcost_rest
    | eval u =>
      classical
      let hasInv (t : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5)) : Prop :=
        t.data.regs (hashCoreReg H.baseReg) = base ∧
        H.tableRep t.data.mem ∧
        H.seedRep t.latent t.data.mem
      let yOf (t : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5)) :
          Data (r_core + 5) :=
        if ht : hasInv t then
          Classical.choose (H.step_eval_subroutineCode u t ht.1 ht.2.1 ht.2.2)
        else
          t.data
      let μ_step (t : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5)) :
          PMF (StepOutcome H.Seed (Fin m) (r_core + 5)) :=
        PMF.pure ⟨t.latent, yOf t, H.eval t.latent u⟩
      let T_step : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5) → ℝ≥0∞ :=
        fun _ => ((H.charge (.eval u) : ℕ) : ℝ≥0∞)
      let ν₁ := ν.bind fun t => (μ_step t).map (t.appendStep (.eval u))
      have hsupp₁ : ∀ q_seq ∈ ν₁.support,
          q_seq.data.regs (hashCoreReg H.baseReg) = base ∧
          H.tableRep q_seq.data.mem ∧
          H.seedRep q_seq.latent q_seq.data.mem := by
        intro q_seq hq_seq
        rw [PMF.mem_support_bind_iff] at hq_seq
        obtain ⟨t, ht, hq_map⟩ := hq_seq
        rw [PMF.mem_support_map_iff] at hq_map
        obtain ⟨q, hq, rfl⟩ := hq_map
        dsimp only [μ_step] at hq
        rw [PMF.support_pure, Set.mem_singleton_iff] at hq
        subst hq
        have ht_inv : hasInv t := hsupp t ht
        have hy_eq : yOf t =
            Classical.choose (H.step_eval_subroutineCode u t ht_inv.1 ht_inv.2.1 ht_inv.2.2) := by
          simp [yOf, ht_inv]
        have hspec := Classical.choose_spec
          (H.step_eval_subroutineCode u t ht_inv.1 ht_inv.2.1 ht_inv.2.2)
        dsimp only [SeqOutcome.appendStep]
        rw [hy_eq, hspec.2.2.1]
        exact ⟨hspec.2.2.2, ht_inv.2.1, ht_inv.2.2⟩
      obtain ⟨ν_final, T_rest, hex_rest, htr_rest, hcost_rest⟩ := ih ν₁ hsupp₁
      have hex_cons : Randomized.ExecSteps H.subroutineCode S H.Seed w base H.space
          H.encode H.decode (.eval u :: os) ν ν_final
          ((∑' t, ν t * T_step t) + T_rest) := by
        refine Randomized.ExecSteps.cons (S := S) (μ_step := μ_step) (T_step := T_step)
          (fun t ht => ?_) hex_rest
        have ht_inv : hasInv t := hsupp t ht
        have hy_eq : yOf t =
            Classical.choose (H.step_eval_subroutineCode u t ht_inv.1 ht_inv.2.1 ht_inv.2.2) := by
          simp [yOf, ht_inv]
        have hspec := Classical.choose_spec
          (H.step_eval_subroutineCode u t ht_inv.1 ht_inv.2.1 ht_inv.2.2)
        refine ⟨?_, ?_⟩
        · simpa [μ_step, hy_eq] using hspec.1
        · intro q hq
          dsimp only [μ_step] at hq
          rw [PMF.support_pure, Set.mem_singleton_iff] at hq
          subst hq
          refine ⟨by simpa [hy_eq] using hspec.2.1, ?_⟩
          rw [hy_eq, hspec.2.2.1]
          exact Modifies.refl _ _
      have hT₁ : (∑' t, ν t * T_step t) = ((H.charge (.eval u) : ℕ) : ℝ≥0∞) := by
        dsimp only [T_step]
        rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
      refine ⟨ν_final, (∑' t, ν t * T_step t) + T_rest, hex_cons, ?_, ?_⟩
      · rw [htr_rest]
        dsimp only [ν₁, μ_step]
        rw [PMF.bind_bind]
        refine PMF.bind_congr_on_support _ _ _ fun t _ => ?_
        rw [PMF.pure_map, PMF.pure_bind, DataStructure.evalHashOpsFromSeed, PMF.map_comp]
        refine congrArg (PMF.map · _) (funext fun suf => ?_)
        simp [SeqOutcome.appendStep]
      · simp only [List.map_cons, List.sum_cons, Nat.cast_add, hT₁]
        exact add_le_add le_rfl hcost_rest

/-- Executing any `ops : List (HashOp U)` on `H.subroutineCode` from an initial distribution `ν₀`
satisfying `H.initInv ν₀` produces a final state distribution `ν_final` whose transcript marginal
equals `DataStructure.evalHashOps (PMF.uniformOfFintype H.Seed) H.eval ops`. -/
theorem evalHashOps_execSteps
    (H : HashFamilyDS B r_core k_init w base U m params)
    (ValidOpSeq : List (DataStructure.HashOp U) → Prop)
    (Contract : List (DataStructure.HashOp U) → PMF (List (DataStructure.HashLabel U m)) → Prop)
    (ops : List (DataStructure.HashOp U))
    (ν₀ : PMF (LatentState H.Seed (r_core + 5)))
    (hinv : H.initInv ν₀) :
    let S : DataStructure.ObliviousSequenceSpec :=
      ⟨DataStructure.HashOp U, @DataStructure.HashResult U m, ValidOpSeq, Contract⟩
    ∃ (ν_final : PMF (SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5)))
      (T_ops : ℝ≥0∞),
      Randomized.ExecSteps H.subroutineCode S H.Seed w base H.space H.encode H.decode
        ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      ν_final.map SeqOutcome.transcript =
        DataStructure.evalHashOps (PMF.uniformOfFintype H.Seed) H.eval ops ∧
      T_ops ≤ (((ops.map H.charge).sum : ℕ) : ℝ≥0∞) := by
  intro S
  have hsupp_seq : ∀ t ∈ (ν₀.map (SeqOutcome.ofLatentState
      (Result := @DataStructure.HashResult U m))).support,
      t.data.regs (hashCoreReg H.baseReg) = base ∧
      H.tableRep t.data.mem ∧
      H.seedRep t.latent t.data.mem := by
    intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact hinv.2 u hu
  obtain ⟨ν_final, T_ops, hex, htr, hcost⟩ :=
    H.steps_subroutineCode ValidOpSeq Contract ops (ν₀.map SeqOutcome.ofLatentState) hsupp_seq
  refine ⟨ν_final, T_ops, hex, ?_, hcost⟩
  rw [htr, PMF.bind_map]
  have hbind_eq :
      (ν₀.bind
        ((fun t : SeqOutcome H.Seed (@DataStructure.HashResult U m) (r_core + 5) =>
            (DataStructure.evalHashOpsFromSeed (PMF.uniformOfFintype H.Seed) H.eval t.latent
              ops).map fun suf => t.transcript ++ suf) ∘
          SeqOutcome.ofLatentState)) =
        (ν₀.map LatentState.latent).bind
          (fun θ₀ =>
            DataStructure.evalHashOpsFromSeed (PMF.uniformOfFintype H.Seed) H.eval θ₀ ops) := by
    rw [PMF.bind_map]
    refine congrArg (ν₀.bind ·) (funext fun u => ?_)
    dsimp only [Function.comp_apply, SeqOutcome.ofLatentState, List.nil_append]
    exact PMF.map_id _
  rw [hbind_eq, hinv.1]
  rfl

/-- Package `H : HashFamilyDS` into an `ObliviousSequenceDS` certificate for any oblivious-sequence
specification `⟨HashOp U, HashResult m, ValidOpSeq, Contract⟩` satisfied by
`DataStructure.evalHashOps (PMF.uniformOfFintype H.Seed) H.eval`. -/
@[expose] noncomputable def toObliviousSequenceDS
    (H : HashFamilyDS B r_core k_init w base U m params)
    (ValidOpSeq : List (DataStructure.HashOp U) → Prop)
    (Contract : List (DataStructure.HashOp U) → PMF (List (DataStructure.HashLabel U m)) → Prop)
    (hcontract : ∀ ops, ValidOpSeq ops →
      Contract ops (DataStructure.evalHashOps (PMF.uniformOfFintype H.Seed) H.eval ops)) :
    ObliviousSequenceDS.{0, 0, 0} H.subroutineCode
      ⟨DataStructure.HashOp U, @DataStructure.HashResult U m, ValidOpSeq, Contract⟩
      w base params where
  Latent := H.Seed
  space := H.space
  spanTime := 3
  setupTime := ((H.initTableSteps + H.resampleSteps : ℕ) : ℝ≥0∞)
  initPotential := 0
  charge := H.charge
  initInv := H.initInv
  encode := H.encode
  decode := H.decode
  clear_nodup := by exact H.clear_nodup_subroutineCode
  params_not_clear := by exact H.params_not_clear_subroutineCode
  incCur_eval {x} hone hfit := by
    have h := H.addReg_eval (x := x) (hashCurReg r_core) (hashCurReg r_core) (hashOneReg r_core)
    rw [show x.regs (hashOneReg r_core) = 1 from hone] at h
    exact h hfit
  span_exec _ hfr hpar := by exact H.span_exec_subroutineCode hfr hpar
  setup_exec hx₁ hb hfr hpar hz := by exact H.setup_exec_subroutineCode hx₁ hb hfr hpar hz
  steps_exec ops ν₀ hv hinv := by
    obtain ⟨ν_final, T_ops, hex, htr, hcost⟩ :=
      H.evalHashOps_execSteps ValidOpSeq Contract ops ν₀ hinv
    refine ⟨ν_final, T_ops, hex, ?_, ?_⟩
    · dsimp only
      rw [htr]
      exact hcontract ops hv
    · simpa using hcost

@[simp]
theorem toObliviousSequenceDS_space
    (H : HashFamilyDS B r_core k_init w base U m params)
    (ValidOpSeq) (Contract) (hcontract) :
    (H.toObliviousSequenceDS ValidOpSeq Contract hcontract).space = H.space := by rfl

@[simp]
theorem toObliviousSequenceDS_initPotential
    (H : HashFamilyDS B r_core k_init w base U m params)
    (ValidOpSeq) (Contract) (hcontract) :
    (H.toObliviousSequenceDS ValidOpSeq Contract hcontract).initPotential = 0 := by rfl

@[simp]
theorem toObliviousSequenceDS_charge
    (H : HashFamilyDS B r_core k_init w base U m params)
    (ValidOpSeq) (Contract) (hcontract) :
    (H.toObliviousSequenceDS ValidOpSeq Contract hcontract).charge = H.charge := by rfl

/-- **Canonical `ObliviousSequenceDS` certificate for `kWiseHashSpec k U m`:**
every `H : HashFamilyDS` whose evaluation map satisfies `IsKWiseIndependentHash k H.eval`
canonically realizes `DataStructure.kWiseHashSpec k U m`. -/
@[expose] noncomputable def toKWiseObliviousSequenceDS [NeZero m]
    (H : HashFamilyDS B r_core k_init w base U m params)
    {k : ℕ} (hk : IsKWiseIndependentHash k H.eval) :
    ObliviousSequenceDS.{0, 0, 0} H.subroutineCode
      (DataStructure.kWiseHashSpec k U m) w base params :=
  H.toObliviousSequenceDS
    (DataStructure.kWiseHashSpec k U m).ValidOpSeq
    (DataStructure.kWiseHashSpec k U m).Contract
    (fun _ hv => DataStructure.kWiseHashSpec_contract_evalHashOps hk hv)

/-- **Canonical `ObliviousSequenceDS` certificate for `whpKWiseHashSpec k U m δ`:**
every `H : HashFamilyDS` with a two-level seed decomposition `e : H.Seed ≃ (TopSeed × BotSeed)` and
a good top-seed set `GoodTop : Finset TopSeed` on which `fun β => H.eval (e.symm (α, β))` is
`k`-wise independent canonically realizes `DataStructure.whpKWiseHashSpec k U m δ` with
`δ = (#(Finset.univ \ GoodTop) : ℝ≥0∞) / (Fintype.card TopSeed : ℝ≥0∞)`. -/
@[expose] noncomputable def toWhpKWiseObliviousSequenceDS [NeZero m]
    {TopSeed BotSeed : Type} [Fintype TopSeed] [DecidableEq TopSeed] [Nonempty TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    (H : HashFamilyDS B r_core k_init w base U m params)
    (e : H.Seed ≃ (TopSeed × BotSeed))
    {k : ℕ} (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop,
      IsKWiseIndependentHash k (fun β : BotSeed => H.eval (e.symm (α, β)))) :
    ObliviousSequenceDS.{0, 0, 0} H.subroutineCode
      (DataStructure.whpKWiseHashSpec k U m
        (((Finset.univ \ GoodTop).card : ℝ≥0∞) / (Fintype.card TopSeed : ℝ≥0∞)))
      w base params :=
  let δ := (((Finset.univ \ GoodTop).card : ℝ≥0∞) / (Fintype.card TopSeed : ℝ≥0∞))
  H.toObliviousSequenceDS
    (DataStructure.whpKWiseHashSpec k U m δ).ValidOpSeq
    (DataStructure.whpKWiseHashSpec k U m δ).Contract
    (fun _ hv =>
      DataStructure.whpKWiseHashSpec_contract_evalHashOps_equiv H.eval e GoodTop hgood hv)

end HashFamilyDS

end Cslib.WordRAM.Randomized
