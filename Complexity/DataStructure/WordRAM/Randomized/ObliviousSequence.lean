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
# Oblivious-Sequence Word-RAM Implementation Certificates

This file connects state-free oblivious-sequence specifications
(`Cslib.DataStructure.ObliviousSequenceSpec`) to concrete randomized Word-RAM subroutines:

1. **`Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl`**:
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

2. **Canonical embedding `Cslib.WordRAM.Randomized.SubroutineDS.toObliviousSequenceImpl`**:
   Every relational `Cslib.WordRAM.Randomized.SubroutineDS P D w base params s₀` whose per-operation
   amortized charge is bounded by a state-independent `opCharge : D.Op → ℕ` on admissible inputs
   canonically induces an `ObliviousSequenceImpl P (D.toObliviousSequenceSpec s₀) w base params`.

`ObliviousSequenceImpl` bounds the instruction cost of initialization and of the subroutine
operation bodies across an oblivious sequence `ops`, excluding external caller argument delivery and
dispatch, with the word width `w` treated as an external admissible parameter.

## Main definitions

* `Cslib.DataStructure.WordRAM.Randomized.LatentState`,
  `Cslib.DataStructure.WordRAM.Randomized.StepOutcome`,
  `Cslib.DataStructure.WordRAM.Randomized.SeqOutcome`: named state and transcript records for
  multi-step distributional execution.
* `Cslib.DataStructure.WordRAM.Randomized.ExecSteps`: multi-operation distributional execution
  relation across an oblivious sequence `ops : List S.Op`.
* `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl`: Word-RAM implementation
  certificate for an `ObliviousSequenceSpec`.
* `Cslib.WordRAM.Randomized.SubroutineDS.toObliviousSequenceImpl`: canonical embedding of a
  relational `SubroutineDS` into `ObliviousSequenceImpl`.

## Main results

* `Cslib.DataStructure.WordRAM.Randomized.ExecSteps.bounded`,
  `Cslib.DataStructure.WordRAM.Randomized.ExecSteps.arguments_fit`,
  `Cslib.DataStructure.WordRAM.Randomized.ExecSteps.mapSimulates`: preservation of `Data.Bounded w`,
  word-admissibility of encoded operation arguments, and basis simulation lifting for `ExecSteps`.
* `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.prepare_bounded`,
  `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.initFresh_exec`,
  `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.initClear_exec`,
  `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.seq_expected`,
  `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.seq_expected_clear`: word-bounded
  preparation, initialization, and end-to-end expected-time and distributional-contract theorems.
-/

public section

open Cslib.WordRAM Cslib.WordRAM.Randomized Cslib.Probability
open scoped ENNReal

universe u v z

namespace Cslib.DataStructure.WordRAM.Randomized

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
At each operation `o`, `t.data` and the encoded arguments are word-bounded (`Fits w`), arguments
are delivered via `(P.toDynamicProgram encode decode).prepare o`, `P.code` executes under
`ExecCodeDist` preserving `Data.Bounded w`, the observation `q.result` is decoded from
`q.data.regs`, memory outside `[base, base + space)` is preserved, and `⟨o, q.result⟩` is appended
to the accumulated transcript. -/
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
        t.data.Bounded w ∧
        (∀ i, P.input i = true → Fits w (encode o i)) ∧
        ((P.toDynamicProgram encode decode).prepare o t.data).Bounded w ∧
        ExecCodeDist w P.code ((P.toDynamicProgram encode decode).prepare o t.data)
          ((μ_step t).map StepOutcome.data) (T_step t) ∧
        ∀ q ∈ (μ_step t).support,
          q.data.Bounded w ∧
          decode o q.data.regs = some q.result ∧
          Modifies (Block.mk base space).footprint t.data.mem q.data.mem) →
      ExecSteps P S Latent w base space encode decode ops
        (ν.bind fun t => (μ_step t).map (t.appendStep o))
        ν_final T_rest →
      ExecSteps P S Latent w base space encode decode (o :: ops) ν ν_final
        ((∑' t, ν t * T_step t) + T_rest)

/-- `ExecSteps` preserves `Data.Bounded w` on every state in the support of `ν_final` whenever
every state in the support of `ν` is word-bounded. -/
theorem ExecSteps.bounded {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base space : ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {ops : List S.Op}
    {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (h : ExecSteps P S Latent w base space encode decode ops ν ν_final T_ops)
    (hbdd : ∀ t ∈ ν.support, t.data.Bounded w) :
    ∀ t ∈ ν_final.support, t.data.Bounded w := by
  induction h with
  | nil _ => exact hbdd
  | cons hstep _ ih =>
    refine ih fun q_seq hq_seq => ?_
    rw [PMF.mem_support_bind_iff] at hq_seq
    obtain ⟨t, ht, hq_map⟩ := hq_seq
    rw [PMF.mem_support_map_iff] at hq_map
    obtain ⟨q, hq, rfl⟩ := hq_map
    exact ((hstep t ht).2.2.2.2 q hq).1

/-- Every operation `o ∈ ops` in an `ExecSteps` derivation has word-bounded encoded arguments on
all input registers of `P`. -/
theorem ExecSteps.arguments_fit {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base space : ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {ops : List S.Op}
    {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (h : ExecSteps P S Latent w base space encode decode ops ν ν_final T_ops) :
    ∀ o ∈ ops, ∀ i, P.input i = true → Fits w (encode o i) := by
  induction h with
  | nil _ => intro _ ho; cases ho
  | @cons o' _ ν' _ _ _ _ hstep _ ih =>
    intro o ho
    rcases List.mem_cons.mp ho with rfl | ho'
    · obtain ⟨t₀, ht₀⟩ := ν'.support_nonempty
      exact (hstep t₀ ht₀).2.1
    · exact ih o ho'

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
    obtain ⟨hbdd, hfit, hprep, he, hq⟩ := hstep t ht
    exact ⟨hbdd, hfit, hprep, he.mapSimulates φ, hq⟩

end Cslib.DataStructure.WordRAM.Randomized

namespace Cslib.DataStructure.WordRAM.Randomized

/-! ## `ObliviousSequenceImpl`: Word-RAM implementation for an `ObliviousSequenceSpec` -/

/-- Reusable Word-RAM subroutine implementation certificate for a randomized data structure
`P : SubroutineCode B r_ds k_init` realizing an oblivious-sequence specification
`S : DataStructure.ObliviousSequenceSpec` at word width `w`, base address `base`, and runtime
parameters `params`. -/
structure ObliviousSequenceImpl {B : Basis} {r_ds k_init : ℕ}
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
  /-- Predicate identifying operations admissible from a latent state (`fun _ _ => True` when
  operation encoding is unconditionally word-bounded). -/
  validOp : Latent → S.Op → Prop := fun _ _ => True
  /-- Standalone register encoding for argument delivery. -/
  encode : S.Op → Fin r_ds → ℕ
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)
  /-- Initial distributions satisfying `initInv` are supported on word-bounded states. -/
  bounded : ∀ {ν : PMF (LatentState Latent r_ds)}, initInv ν → ∀ t ∈ ν.support, t.data.Bounded w
  /-- Standalone encoded arguments fit in `w`-bit words on admissible calls. -/
  arguments_fit : ∀ {z : Latent} (o : S.Op),
    validOp z o → ∀ i, P.input i = true → Fits w (encode o i)
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
        t.data.Bounded w ∧
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

namespace ObliviousSequenceImpl

variable {B B' : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init}
  {S : DataStructure.ObliviousSequenceSpec.{u, v}}
  {params : Fin k_init → ℕ}

/-- Argument preparation preserves `Data.Bounded w` on operations satisfying `C.validOp`. -/
theorem prepare_bounded (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    {z : C.Latent} {o : S.Op} {x : Data r_ds}
    (hx : x.Bounded w) (hv : C.validOp z o) :
    ((P.toDynamicProgram C.encode C.decode).prepare o x).Bounded w :=
  (P.toDynamicProgram C.encode C.decode).prepare_bounded hx (C.arguments_fit o hv)

/-- Total expected instruction bound for `P.initFresh` (`spanTime + setupTime`). -/
@[expose] def initTime (C : ObliviousSequenceImpl.{u, v, z} P S w base params) : ℝ≥0∞ :=
  (C.spanTime : ℝ≥0∞) + C.setupTime

/-- Total expected instruction bound for `P.initClear` (`spanTime + (4 * space + 6) + setupTime`).
-/
@[expose] def initClearTime (C : ObliviousSequenceImpl.{u, v, z} P S w base params) : ℝ≥0∞ :=
  (C.spanTime : ℝ≥0∞) + ((4 * C.space + 6 : ℕ) : ℝ≥0∞) + C.setupTime

/-- Total operation charge summed across an operation sequence `ops : List S.Op`. -/
@[expose] def totalCharge (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    (ops : List S.Op) : ℕ :=
  (ops.map C.charge).sum

@[simp]
theorem totalCharge_nil (C : ObliviousSequenceImpl.{u, v, z} P S w base params) :
    C.totalCharge [] = 0 := rfl

@[simp]
theorem totalCharge_cons (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    (o : S.Op) (ops : List S.Op) :
    C.totalCharge (o :: ops) = C.charge o + C.totalCharge ops := by
  simp [totalCharge]

/-- Specialization of `ExecSteps` to an `ObliviousSequenceImpl` certificate `C`. -/
abbrev Steps (C : ObliviousSequenceImpl.{u, v, z} P S w base params) :
    List S.Op → PMF (SeqOutcome C.Latent S.Result r_ds) →
      PMF (SeqOutcome C.Latent S.Result r_ds) → ℝ≥0∞ → Prop :=
  ExecSteps P S C.Latent w base C.space C.encode C.decode

/-- Transport an `ObliviousSequenceImpl` certificate along a basis simulation `φ : B.Simulates B'`.
-/
def mapSimulates (φ : B.Simulates B')
    (C : ObliviousSequenceImpl.{u, v, z} P S w base params) :
    ObliviousSequenceImpl.{u, v, z} (P.mapSimulates φ) S w base params where
  Latent := C.Latent
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  initPotential := C.initPotential
  charge := C.charge
  initInv := C.initInv
  validOp := C.validOp
  encode := C.encode
  decode := C.decode
  bounded := C.bounded
  arguments_fit := C.arguments_fit
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

/-- Lift an exact-basis `ObliviousSequenceImpl` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : ObliviousSequenceImpl.{u, v, z} P S w base params) :
    ObliviousSequenceImpl.{u, v, z} P.toStandard S w base params :=
  C.mapSimulates .exactStandard

/-- Expected-time execution of `P.initFresh` when `[base, base + C.space)` already holds zeros. -/
theorem initFresh_exec (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    {x : Data r_ds} (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ ν₀ : PMF (LatentState C.Latent r_ds),
      ExecCodeDist w P.initFresh x (ν₀.map LatentState.data) C.initTime ∧
      C.initInv ν₀ ∧
      ∀ t ∈ ν₀.support,
        t.data.Bounded w ∧
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
theorem initClear_exec (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    {x : Data r_ds} (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j) :
    ∃ ν₀ : PMF (LatentState C.Latent r_ds),
      ExecCodeDist w P.initClear x (ν₀.map LatentState.data) C.initClearTime ∧
      C.initInv ν₀ ∧
      ∀ t ∈ ν₀.support,
        t.data.Bounded w ∧
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
  obtain ⟨hbdd_t, hfr_t, hmod_t⟩ := hsupp t ht
  have hmod : Modifies (Block.mk base C.space).footprint x.mem t.data.mem := by
    simpa only [Finset.union_idempotent] using hmod₂.trans hmod_t
  exact ⟨hbdd_t, hfr_t, hmod⟩

/-- **End-to-end expected-time and distributional correctness theorem from fresh initialization
(`seq_expected`).**
Starting from zeroed `[base, base + C.space)`, `P.initFresh` followed by any admissible oblivious
operation sequence `ops : List S.Op` (`S.ValidOpSeq ops`) executes in expected time at most
`C.initTime + C.initPotential + C.totalCharge ops`, preserves `Data.Bounded w` on `ν_final.support`,
and induces an output transcript distribution `ν_final.map SeqOutcome.transcript` satisfying
`S.Contract ops`. -/
theorem seq_expected (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    {x : Data r_ds} (ops : List S.Op)
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0)
    (hv : S.ValidOpSeq ops) :
    ∃ (ν₀ : PMF (LatentState C.Latent r_ds))
      (ν_final : PMF (SeqOutcome C.Latent S.Result r_ds)) (T_ops : ℝ≥0∞),
      ExecCodeDist w P.initFresh x (ν₀.map LatentState.data) C.initTime ∧
      C.Steps ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      (∀ t ∈ ν_final.support, t.data.Bounded w) ∧
      S.Contract ops (ν_final.map SeqOutcome.transcript) ∧
      C.initTime + T_ops ≤
        C.initTime + (C.initPotential : ℝ≥0∞) + (C.totalCharge ops : ℝ≥0∞) := by
  obtain ⟨ν₀, he_init, hinv, _⟩ := C.initFresh_exec hx hfr hpar hz
  obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ := C.steps_exec ops ν₀ hv hinv
  have hbdd₀ : ∀ t ∈ (ν₀.map (SeqOutcome.ofLatentState (Result := S.Result))).support,
      t.data.Bounded w := by
    intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact C.bounded hinv u hu
  refine ⟨ν₀, ν_final, T_ops, he_init, hex, hex.bounded hbdd₀, hcontract, ?_⟩
  rw [add_assoc]
  exact add_le_add le_rfl hcost

/-- **End-to-end expected-time and distributional correctness theorem from dirty memory
(`seq_expected_clear`).** -/
theorem seq_expected_clear (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    {x : Data r_ds} (ops : List S.Op)
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hv : S.ValidOpSeq ops) :
    ∃ (ν₀ : PMF (LatentState C.Latent r_ds))
      (ν_final : PMF (SeqOutcome C.Latent S.Result r_ds)) (T_ops : ℝ≥0∞),
      ExecCodeDist w P.initClear x (ν₀.map LatentState.data) C.initClearTime ∧
      C.Steps ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      (∀ t ∈ ν_final.support, t.data.Bounded w) ∧
      S.Contract ops (ν_final.map SeqOutcome.transcript) ∧
      C.initClearTime + T_ops ≤
        C.initClearTime + (C.initPotential : ℝ≥0∞) + (C.totalCharge ops : ℝ≥0∞) := by
  obtain ⟨ν₀, he_init, hinv, _⟩ := C.initClear_exec hx hfr hpar
  obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ := C.steps_exec ops ν₀ hv hinv
  have hbdd₀ : ∀ t ∈ (ν₀.map (SeqOutcome.ofLatentState (Result := S.Result))).support,
      t.data.Bounded w := by
    intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact C.bounded hinv u hu
  refine ⟨ν₀, ν_final, T_ops, he_init, hex, hex.bounded hbdd₀, hcontract, ?_⟩
  rw [add_assoc]
  exact add_le_add le_rfl hcost

end ObliviousSequenceImpl

/-- Coupled latent seed, current abstract state, and accumulated relational transcript prefix for
embedding `Cslib.WordRAM.Randomized.SubroutineDS` into `ObliviousSequenceImpl`. -/
structure TraceLatent (D : Stateful.Spec.{u, v, z}) (Seed : Type) : Type (max u v z) where
  /-- Latent random seed from the underlying `SubroutineDS`. -/
  seed : Seed
  /-- Current abstract state of `D`. -/
  state : D.State
  /-- Relational execution transcript accumulated since `s₀`. -/
  trace : D.Transcript

end Cslib.DataStructure.WordRAM.Randomized

/-! ## Canonical Embedding of `SubroutineDS` into `ObliviousSequenceImpl` -/

namespace Cslib.WordRAM.Randomized.SubroutineDS

open Cslib.DataStructure.WordRAM.Randomized

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : Stateful.Spec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Project a `SeqOutcome (TraceLatent D C.Seed) D.Result r_ds` to
`CoupledState C.Seed D.State r_ds` by forgetting the accumulated transcript prefix. -/
private def projCoupled (C : SubroutineDS P D w base params s₀)
    (t : SeqOutcome (TraceLatent D C.Seed) D.Result r_ds) :
    CoupledState C.Seed D.State r_ds :=
  ⟨t.latent.seed, t.latent.state, t.data⟩

/-- Multi-step execution and potential-telescope helper for `SubroutineDS.toObliviousSequenceImpl`.
-/
private theorem steps_toObliviousSequenceImpl (C : SubroutineDS P D w base params s₀)
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
      DataStructure.WordRAM.Randomized.ExecSteps P (D.toObliviousSequenceSpec s₀)
        (TraceLatent D C.Seed) w base C.space C.encode C.decode remOps ν ν_final T_ops ∧
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
      DataStructure.WordRAM.Randomized.ExecSteps.nil
        (S := D.toObliviousSequenceSpec s₀) ν, fun t ht => ?_, by simp⟩
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
    have hex_cons :
        DataStructure.WordRAM.Randomized.ExecSteps P (D.toObliviousSequenceSpec s₀)
          (TraceLatent D C.Seed) w base C.space C.encode C.decode (o :: os) ν ν_final
          (T₁ + T_rest) := by
      refine DataStructure.WordRAM.Randomized.ExecSteps.cons (S := D.toObliviousSequenceSpec s₀)
        (μ_step := μ_step) (T_step := T_step) (fun t ht => ?_) hex_rest
      obtain ⟨_, _, _, hv_t, hrep_t⟩ := hsupp t ht
      have hbdd_t : t.data.Bounded w := C.bounded hrep_t
      have hfit_t : ∀ i, P.input i = true → Fits w (C.encode o i) := C.arguments_fit o hv_t.1
      have hprep_t : ((P.toDynamicProgram C.encode C.decode).prepare o t.data).Bounded w :=
        C.toDynamicProgram.prepare_bounded hbdd_t hfit_t
      have ht' : prepCoupled t ∈ ν_prep.support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
      obtain ⟨he_rel, hq_rel⟩ := hstep_rel (prepCoupled t) ht'
      refine ⟨hbdd_t, hfit_t, hprep_t, ?_, ?_⟩
      · refine he_rel.congr_dist ?_ le_rfl
        dsimp only [μ_step]
        rw [PMF.map_comp]
        rfl
      · intro u hu
        dsimp only [μ_step] at hu
        rw [PMF.mem_support_map_iff] at hu
        obtain ⟨q, hq, rfl⟩ := hu
        obtain ⟨a, _, hdec_a, hrep_q, hmod_q⟩ := hq_rel q hq
        have hout_eq : outOf q = a := by simp [outOf, hdec_a]
        exact ⟨C.bounded hrep_q, by simp [liftStep, hout_eq, hdec_a], hmod_q⟩
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
`ObliviousSequenceImpl` realizing `D.toObliviousSequenceSpec s₀`, given a state-independent
operation charge bound `opCharge : D.Op → ℕ` such that
`∀ s o, D.valid s o → C.charge s o ≤ opCharge o`. -/
@[expose] noncomputable def toObliviousSequenceImpl (C : SubroutineDS P D w base params s₀)
    (opCharge : D.Op → ℕ := C.charge s₀)
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o := by intros; exact le_rfl) :
    ObliviousSequenceImpl.{v, z, max u v z} P (D.toObliviousSequenceSpec s₀) w base params where
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
  validOp z o := D.valid z.state o
  encode := C.encode
  decode := C.decode
  bounded hinv t ht := C.bounded (hinv.2.2 t ht).2.2.1
  arguments_fit o hv := C.arguments_fit o hv
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
      obtain ⟨hfr', hrep, _, hmod⟩ := hsupp p hp
      exact ⟨C.bounded hrep, hfr', hmod⟩
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
      C.steps_toObliviousSequenceImpl opCharge hcharge [] ops ν_seq hseed_seq hsingle_seq hsupp_seq
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
theorem toObliviousSequenceImpl_space (C : SubroutineDS P D w base params s₀)
    (opCharge) (hcharge) :
    (C.toObliviousSequenceImpl opCharge hcharge).space = C.space := by rfl

@[simp]
theorem toObliviousSequenceImpl_initPotential (C : SubroutineDS P D w base params s₀)
    (opCharge) (hcharge) :
    (C.toObliviousSequenceImpl opCharge hcharge).initPotential = C.initPotential := by rfl

@[simp]
theorem toObliviousSequenceImpl_charge (C : SubroutineDS P D w base params s₀)
    (opCharge) (hcharge) :
    (C.toObliviousSequenceImpl opCharge hcharge).charge = opCharge := by rfl

end Cslib.WordRAM.Randomized.SubroutineDS
