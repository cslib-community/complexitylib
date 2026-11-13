/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.StateTransition
public import CslibFrontier.DataStructure.ObliviousSequence
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.SupportTsum

/-!
# Oblivious-Sequence Resizable Word RAM Implementation Certificates

Connects state-free oblivious-sequence specifications (`Cslib.DataStructure.ObliviousSequenceSpec`)
to randomized subroutines on the word-granular **Resizable Word RAM**
(`Cslib.WordRAM.Resizable.ExecRCodeDist` and `ExecRProgramDist`), accompanying the word-granular
resizable memory models of [LiLiangYuZhou2023Succincter], Section 2.1, and
[KuszmaulLiangZhou2026], Section 5.1, and adapting the bit-granular virtual-memory variant of
[LiLiangYuZhou2024], Section 3.2, at word granularity. Expected step times sum across
`ops : List S.Op` by linearity of expectation ([MitzenmacherUpfal2017], Section 2.1), tracking
trajectory-dependent resting (`spaceBound : List S.Op → ℕ`) and peak
(`peakSpaceBound : List S.Op → S.Op → ℕ`) word bounds while preserving caller memory `[0, base)`.

## Main definitions

* `Randomized.LatentRState`, `Randomized.StepROutcome`, `Randomized.SeqROutcome`: named state and
  transcript records over `RData r` for multi-step distributional execution.
* `Randomized.ObliviousPeakFits`: trajectory-relative peak-frontier admissibility along `ops`.
* `Randomized.ExecSteps`, `Randomized.ExecProgramSteps`: structured (`ExecRCodeDist`) and compiled
  flat-program (`ExecRProgramDist`) multi-operation oblivious execution relations.
* `Randomized.ObliviousSequenceImpl`: Resizable Word RAM implementation certificate for
  `S : ObliviousSequenceSpec`.
* `Randomized.StateTransitionImpl.toObliviousSequenceImpl`,
  `Randomized.StateTransitionImpl.toObliviousSequenceImplOfFn`: canonical embeddings of relational
  and functional `Resizable.Randomized.StateTransitionImpl` certificates into
  `ObliviousSequenceImpl` via `StateTransitionSpec.toObliviousSequenceSpec`.

## Main results

* `Randomized.ExecSteps.bounded`, `Randomized.ExecSteps.frontier_le`,
  `Randomized.ExecSteps.caller_mem`, `Randomized.ExecSteps.mapSimulates`: preservation of
  `RData.Bounded w`, resting frontier bounds, caller prefix `[0, base)`, and basis transport.
* `Randomized.ObliviousSequenceImpl.mapSimulates`, `Randomized.ObliviousSequenceImpl.toStandard`:
  basis transport from `Basis.exact` to `Basis.standard`.
* `Randomized.ObliviousSequenceImpl.seq_expected`,
  `Randomized.ExecSteps.toExecRProgramDist`,
  `Randomized.ObliviousSequenceImpl.seq_toExecRProgramDist`: end-to-end expected-time, resting/peak
  space, caller-prefix, and `S.Contract` theorems on `RCode` and compiled flat `RProgram`.
* `Randomized.not_execProgramSteps_halt`: `.halt`-rejection soundness check on `ExecProgramSteps`.

## References

* [MitzenmacherUpfal2017] Michael Mitzenmacher and Eli Upfal, *Probability and Computing*, 2nd ed.,
  Cambridge University Press, 2017, Section 2.1.
* [LiLiangYuZhou2023Succincter] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  "Succincter"*, FOCS 2023, pp. 1715–1733 (`arXiv:2309.12950v1`, Section 2.1, PDF pp. 6–7 /
  printed pp. 5–6).
* [LiLiangYuZhou2024] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary
  with Subconstant Wasted Bits per Key*, SODA 2024 (`arXiv:2310.20536v1`, Section 3.2, PDF pp. 9–10
  / printed pp. 8–9).
* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF pp. 16–20 / printed pp. 15–19).
-/

public section

open Cslib.WordRAM Cslib.WordRAM.Resizable Cslib.DataStructure
open Cslib.DataStructure.WordRAM.Resizable
open scoped ENNReal

universe u v z

namespace Cslib.DataStructure.WordRAM.Resizable.Randomized

/-! ## Named state, outcome, and trajectory-fit bundles -/

/-- Coupled latent state and concrete Resizable Word RAM state `RData r`. -/
structure LatentRState (Latent : Type z) (r : ℕ) : Type z where
  /-- Internal latent state (such as a hash seed or coupled relational state). -/
  latent : Latent
  /-- Concrete Resizable Word RAM register, memory, and frontier state. -/
  data : RData r

/-- Outcome of a single oblivious subroutine operation step. -/
structure StepROutcome (Latent : Type z) (α : Type v) (r : ℕ) : Type (max v z) where
  /-- Updated internal latent state. -/
  latent : Latent
  /-- Updated concrete Resizable Word RAM state. -/
  data : RData r
  /-- Decoded observation returned by the operation. -/
  result : α

/-- Outcome of a multi-operation oblivious sequence. -/
structure SeqROutcome (Latent : Type z) {Op : Type u} (Result : Op → Type v) (r : ℕ) :
    Type (max u v z) where
  /-- Current internal latent state. -/
  latent : Latent
  /-- Current concrete Resizable Word RAM state. -/
  data : RData r
  /-- Accumulated input-output transcript executed so far. -/
  transcript : List (Sigma Result)

/-- Initialize a `SeqROutcome` from a `LatentRState` with an empty transcript `[]`. -/
@[expose] def SeqROutcome.ofLatentRState {Latent : Type z} {Op : Type u}
    {Result : Op → Type v} {r : ℕ} (t : LatentRState Latent r) : SeqROutcome Latent Result r where
  latent := t.latent
  data := t.data
  transcript := []

/-- Append a single operation outcome `q : StepROutcome Latent (Result o) r` to `t`. -/
@[expose] def SeqROutcome.appendStep {Latent : Type z} {Op : Type u}
    {Result : Op → Type v} {r : ℕ}
    (t : SeqROutcome Latent Result r) (o : Op) (q : StepROutcome Latent (Result o) r) :
    SeqROutcome Latent Result r where
  latent := q.latent
  data := q.data
  transcript := t.transcript ++ [⟨o, q.result⟩]

/-- Trajectory-relative peak-frontier admissibility along remaining oblivious operations `remOps`
after prefix `prefOps`. -/
@[expose] def ObliviousPeakFits {Op : Type u} (w base : ℕ)
    (peakSpaceBound : List Op → Op → ℕ) : List Op → List Op → Prop
  | _, [] => True
  | prefOps, o :: ops =>
    Fits w (base + peakSpaceBound prefOps o) ∧
      ObliviousPeakFits w base peakSpaceBound (prefOps ++ [o]) ops

@[simp]
theorem obliviousPeakFits_nil {Op : Type u} (w base : ℕ)
    (peakSpaceBound : List Op → Op → ℕ) (prefOps : List Op) :
    ObliviousPeakFits w base peakSpaceBound prefOps [] ↔ True := Iff.rfl

@[simp]
theorem obliviousPeakFits_cons {Op : Type u} (w base : ℕ)
    (peakSpaceBound : List Op → Op → ℕ) (prefOps : List Op) (o : Op) (ops : List Op) :
    ObliviousPeakFits w base peakSpaceBound prefOps (o :: ops) ↔
      Fits w (base + peakSpaceBound prefOps o) ∧
        ObliviousPeakFits w base peakSpaceBound (prefOps ++ [o]) ops := Iff.rfl

/-! ## Multi-operation distributional execution (`ExecSteps` and `ExecProgramSteps`) -/

/-- Multi-operation structured distributional execution across remaining operations `remOps` after
prefix `prefOps`: at each operation `o`, `P.code` executes under `ExecRCodeDist` within peak
frontier `base + peakSpaceBound prefOps o`, establishes resting frontier
`base ≤ q.data.frontier ≤ base + spaceBound (prefOps ++ [o])` and `q.data.regs P.baseReg = base`,
decodes `q.result`, preserves caller memory `[0, base)`, and appends `⟨o, q.result⟩`. -/
inductive ExecSteps {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, v})
    (Latent : Type z) (w base : ℕ)
    (spaceBound : List S.Op → ℕ)
    (peakSpaceBound : List S.Op → S.Op → ℕ)
    (encode : S.Op → Fin r_ds → ℕ)
    (decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)) :
    List S.Op → List S.Op → PMF (SeqROutcome Latent S.Result r_ds) →
      PMF (SeqROutcome Latent S.Result r_ds) → ℝ≥0∞ → Prop where
  | nil (prefOps : List S.Op) (ν : PMF (SeqROutcome Latent S.Result r_ds)) :
      ExecSteps P S Latent w base spaceBound peakSpaceBound encode decode prefOps [] ν ν 0
  | cons {prefOps : List S.Op} {o : S.Op} {ops : List S.Op}
      {ν ν_final : PMF (SeqROutcome Latent S.Result r_ds)}
      {μ_step : SeqROutcome Latent S.Result r_ds → PMF (StepROutcome Latent (S.Result o) r_ds)}
      {T_step : SeqROutcome Latent S.Result r_ds → ℝ≥0∞} {T_rest : ℝ≥0∞} :
      (∀ t ∈ ν.support,
        t.data.Bounded w ∧
        (∀ i, P.input i = true → Fits w (encode o i)) ∧
        (P.prepare encode o t.data).Bounded w ∧
        ExecRCodeDist w P.code (P.prepare encode o t.data)
          ((μ_step t).map StepROutcome.data) (T_step t) (base + peakSpaceBound prefOps o) ∧
        ∀ q ∈ (μ_step t).support,
          q.data.Bounded w ∧
          (base ≤ q.data.frontier ∧
            q.data.frontier ≤ base + spaceBound (prefOps ++ [o]) ∧
            q.data.regs P.baseReg = base) ∧
          decode o q.data.regs = some q.result ∧
          (∀ addr < base, q.data.mem addr = t.data.mem addr)) →
      ExecSteps P S Latent w base spaceBound peakSpaceBound encode decode (prefOps ++ [o]) ops
        (ν.bind fun t => (μ_step t).map (t.appendStep o)) ν_final T_rest →
      ExecSteps P S Latent w base spaceBound peakSpaceBound encode decode prefOps (o :: ops)
        ν ν_final ((∑' t, ν t * T_step t) + T_rest)

/-- `ExecSteps` preserves `RData.Bounded w` across all support states. -/
theorem ExecSteps.bounded {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {prefOps remOps : List S.Op}
    {ν ν_final : PMF (SeqROutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (h : ExecSteps P S Latent w base spaceBound peakSpaceBound encode decode prefOps remOps
      ν ν_final T_ops)
    (hbdd : ∀ t ∈ ν.support, t.data.Bounded w) :
    ∀ t ∈ ν_final.support, t.data.Bounded w := by
  induction h with
  | nil _ _ => exact hbdd
  | cons hstep _ ih =>
    refine ih fun q_seq hq_seq => ?_
    rw [PMF.mem_support_bind_iff] at hq_seq; obtain ⟨t, ht, hq_map⟩ := hq_seq
    rw [PMF.mem_support_map_iff] at hq_map; obtain ⟨q, hq, rfl⟩ := hq_map
    exact ((hstep t ht).2.2.2.2 q hq).1

/-- `ExecSteps` establishes resting frontier bounds `base ≤ t.data.frontier ≤
base + spaceBound (prefOps ++ remOps)` and `t.data.regs P.baseReg = base` on `ν_final.support`. -/
theorem ExecSteps.frontier_le {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {prefOps remOps : List S.Op}
    {ν ν_final : PMF (SeqROutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (h : ExecSteps P S Latent w base spaceBound peakSpaceBound encode decode prefOps remOps
      ν ν_final T_ops)
    (hfr : ∀ t ∈ ν.support,
      base ≤ t.data.frontier ∧ t.data.frontier ≤ base + spaceBound prefOps ∧
        t.data.regs P.baseReg = base) :
    ∀ t ∈ ν_final.support,
      base ≤ t.data.frontier ∧ t.data.frontier ≤ base + spaceBound (prefOps ++ remOps) ∧
        t.data.regs P.baseReg = base := by
  induction h with
  | nil prefOps _ =>
    simpa only [List.append_nil] using hfr
  | @cons prefOps o ops ν _ μ_step _ _ hstep _ ih =>
    have h₁ : ∀ q_seq ∈ (ν.bind fun t => (μ_step t).map (t.appendStep o)).support,
        base ≤ q_seq.data.frontier ∧
        q_seq.data.frontier ≤ base + spaceBound (prefOps ++ [o]) ∧
        q_seq.data.regs P.baseReg = base := by
      intro q_seq hq_seq
      rw [PMF.mem_support_bind_iff] at hq_seq; obtain ⟨t, ht, hq_map⟩ := hq_seq
      rw [PMF.mem_support_map_iff] at hq_map; obtain ⟨q, hq, rfl⟩ := hq_map
      exact ((hstep t ht).2.2.2.2 q hq).2.1
    simpa only [List.append_assoc, List.singleton_append] using ih h₁

/-- `ExecSteps` preserves caller memory `[0, base)` across all support states. -/
theorem ExecSteps.caller_mem {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {prefOps remOps : List S.Op}
    {ν ν_final : PMF (SeqROutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (h : ExecSteps P S Latent w base spaceBound peakSpaceBound encode decode prefOps remOps
      ν ν_final T_ops)
    {mem₀ : ℕ → ℕ} (h₀ : ∀ t ∈ ν.support, ∀ addr < base, t.data.mem addr = mem₀ addr) :
    ∀ t ∈ ν_final.support, ∀ addr < base, t.data.mem addr = mem₀ addr := by
  induction h with
  | nil _ _ => exact h₀
  | cons hstep _ ih =>
    refine ih fun q_seq hq_seq addr hlt => ?_
    rw [PMF.mem_support_bind_iff] at hq_seq; obtain ⟨t, ht, hq_map⟩ := hq_seq
    rw [PMF.mem_support_map_iff] at hq_map; obtain ⟨q, hq, rfl⟩ := hq_map
    exact (((hstep t ht).2.2.2.2 q hq).2.2.2 addr hlt).trans (h₀ t ht addr hlt)

/-- Lift an `ExecSteps` derivation along a basis simulation `φ : B.Simulates B'`. -/
theorem ExecSteps.mapSimulates {B B' : Basis} {r_ds k_init : ℕ}
    (φ : B.Simulates B')
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {prefOps remOps : List S.Op}
    {ν ν_final : PMF (SeqROutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (h : ExecSteps P S Latent w base spaceBound peakSpaceBound encode decode prefOps remOps
      ν ν_final T_ops) :
    ExecSteps (P.mapSimulates φ) S Latent w base spaceBound peakSpaceBound encode decode
      prefOps remOps ν ν_final T_ops := by
  induction h with
  | nil prefOps ν => exact .nil prefOps ν
  | cons hstep _ ih =>
    refine .cons (fun t ht => ?_) ih
    obtain ⟨hbdd, hfit, hprep, he, hq⟩ := hstep t ht
    exact ⟨hbdd, hfit, hprep, he.mapSimulates φ, hq⟩

/-- Multi-operation compiled flat-`RProgram` execution relation over `ExecRProgramDist`. -/
inductive ExecProgramSteps {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, v})
    (Latent : Type z) (w base : ℕ)
    (spaceBound : List S.Op → ℕ)
    (peakSpaceBound : List S.Op → S.Op → ℕ)
    (encode : S.Op → Fin r_ds → ℕ)
    (decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o))
    (p_op : RProgram B r_ds) (out : Fin r_ds) :
    List S.Op → List S.Op → PMF (SeqROutcome Latent S.Result r_ds) →
      PMF (SeqROutcome Latent S.Result r_ds) → ℝ≥0∞ → Prop where
  | nil (prefOps : List S.Op) (ν : PMF (SeqROutcome Latent S.Result r_ds)) :
      ExecProgramSteps P S Latent w base spaceBound peakSpaceBound encode decode p_op out
        prefOps [] ν ν 0
  | cons {prefOps : List S.Op} {o : S.Op} {ops : List S.Op}
      {ν ν_final : PMF (SeqROutcome Latent S.Result r_ds)}
      {μ_step : SeqROutcome Latent S.Result r_ds → PMF (StepROutcome Latent (S.Result o) r_ds)}
      {T_step : SeqROutcome Latent S.Result r_ds → ℝ≥0∞} {T_rest : ℝ≥0∞} :
      (∀ t ∈ ν.support,
        ExecRProgramDist w p_op out (P.prepare encode o t.data)
          ((μ_step t).map StepROutcome.data) (T_step t) (base + peakSpaceBound prefOps o) ∧
        ∀ q ∈ (μ_step t).support,
          q.data.Bounded w ∧
          (base ≤ q.data.frontier ∧
            q.data.frontier ≤ base + spaceBound (prefOps ++ [o]) ∧
            q.data.regs P.baseReg = base) ∧
          decode o q.data.regs = some q.result ∧
          (∀ addr < base, q.data.mem addr = t.data.mem addr)) →
      ExecProgramSteps P S Latent w base spaceBound peakSpaceBound encode decode p_op out
        (prefOps ++ [o]) ops (ν.bind fun t => (μ_step t).map (t.appendStep o)) ν_final T_rest →
      ExecProgramSteps P S Latent w base spaceBound peakSpaceBound encode decode p_op out
        prefOps (o :: ops) ν ν_final ((∑' t, ν t * T_step t) + T_rest)

/-- Compile a structured `ExecSteps` derivation to `ExecProgramSteps ... (P.opProg out) out`,
charging `+ 1` instruction per operation for the trailing `halt out`. -/
theorem ExecSteps.toExecRProgramDist {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    (out : Fin r_ds) {prefOps remOps : List S.Op}
    {ν ν_final : PMF (SeqROutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (h : ExecSteps P S Latent w base spaceBound peakSpaceBound encode decode prefOps remOps
      ν ν_final T_ops) :
    ExecProgramSteps P S Latent w base spaceBound peakSpaceBound encode decode (P.opProg out) out
      prefOps remOps ν ν_final (T_ops + (remOps.length : ℝ≥0∞)) := by
  induction h with
  | nil prefOps ν => simpa using ExecProgramSteps.nil prefOps ν
  | @cons prefOps o ops ν ν_final μ_step T_step T_rest hstep _ ih =>
    rw [← StateTransitionImpl.tsum_add_one_add_length_cons ν T_step T_rest o ops]
    refine .cons (μ_step := μ_step) (T_step := fun t => T_step t + 1) (fun t ht => ?_) ih
    obtain ⟨_, _, _, he, hq⟩ := hstep t ht
    exact ⟨he.toExecRProgramDist out, hq⟩

/-- Every support state `t ∈ ν.support` extends to some final support state `u ∈ ν_final.support`
whose transcript has `t.transcript` as a prefix. -/
theorem ExecProgramSteps.transcript_prefix {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {p_op : RProgram B r_ds} {out : Fin r_ds} {prefOps remOps : List S.Op}
    {ν ν_final : PMF (SeqROutcome Latent S.Result r_ds)} {T_prog : ℝ≥0∞}
    (h : ExecProgramSteps P S Latent w base spaceBound peakSpaceBound encode decode p_op out
      prefOps remOps ν ν_final T_prog)
    {t : SeqROutcome Latent S.Result r_ds} (ht : t ∈ ν.support) :
    ∃ u ∈ ν_final.support, t.transcript <+: u.transcript := by
  induction h generalizing t with
  | nil _ _ => exact ⟨t, ht, List.prefix_refl _⟩
  | @cons _ o _ ν _ μ_step _ _ _ _ ih =>
    obtain ⟨q, hq⟩ := (μ_step t).support_nonempty
    have ht' : t.appendStep o q ∈ (ν.bind fun t => (μ_step t).map (t.appendStep o)).support := by
      rw [PMF.mem_support_bind_iff]
      exact ⟨t, ht, (PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩⟩
    obtain ⟨u, hu, hpref⟩ := ih ht'
    exact ⟨u, hu, (List.prefix_append t.transcript [⟨o, q.result⟩]).trans hpref⟩

/-- **`.halt`-rejection soundness check (`not_execProgramSteps_halt`):** a 1-instruction
`[.halt out]` stub cannot satisfy `ExecProgramSteps` on `(o :: ops)` whenever for some
`t ∈ ν.support`, no observation `a` decoded from `P.prepare encode o t.data` can appear at the next
position of `ν_final`'s transcripts (or when `P.prepare encode o t.data` violates the post-step
frontier bound). -/
theorem not_execProgramSteps_halt {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init} {S : DataStructure.ObliviousSequenceSpec.{u, v}}
    {Latent : Type z} {w base : ℕ} {spaceBound : List S.Op → ℕ}
    {peakSpaceBound : List S.Op → S.Op → ℕ} {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    (out : Fin r_ds) {prefOps : List S.Op} {o : S.Op} {ops : List S.Op}
    {ν ν_final : PMF (SeqROutcome Latent S.Result r_ds)} {T_prog : ℝ≥0∞}
    {t : SeqROutcome Latent S.Result r_ds} (ht : t ∈ ν.support)
    (hbad : ∀ a,
      decode o (P.prepare encode o t.data).regs = some a →
      base ≤ (P.prepare encode o t.data).frontier →
      (P.prepare encode o t.data).frontier ≤ base + spaceBound (prefOps ++ [o]) →
      ∀ u ∈ ν_final.support, t.transcript ++ [⟨o, a⟩] <+: u.transcript → False) :
    ¬ExecProgramSteps P S Latent w base spaceBound peakSpaceBound encode decode [.halt out] out
      prefOps (o :: ops) ν ν_final T_prog := by
  intro h; cases h with
  | @cons _ _ _ _ _ μ_step _ _ hstep hrest =>
    obtain ⟨hprog, hq_all⟩ := hstep t ht
    obtain ⟨q, hq⟩ := (μ_step t).support_nonempty
    obtain ⟨_, ⟨hlo, hhi, _⟩, hdec, _⟩ := hq_all q hq
    by_cases hqd : q.data = P.prepare encode o t.data
    · rw [hqd] at hlo hhi hdec
      have ht' : t.appendStep o q ∈ (ν.bind fun t => (μ_step t).map (t.appendStep o)).support := by
        rw [PMF.mem_support_bind_iff]
        exact ⟨t, ht, (PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩⟩
      obtain ⟨u, hu, hpref⟩ := hrest.transcript_prefix ht'
      exact hbad q.result hdec hlo hhi u hu hpref
    · exact not_execRProgramDist_halt ((PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩) hqd hprog

/-! ## `ObliviousSequenceImpl`: Resizable Word RAM implementation for an `ObliviousSequenceSpec` -/

/-- Reusable Resizable Word RAM subroutine implementation certificate for a randomized data
structure `P : SubroutineCode B r_ds k_init` realizing an oblivious-sequence specification
`S : DataStructure.ObliviousSequenceSpec` at word width `w`, base address `base`, and runtime
parameters `params`, with trajectory-dependent resting (`spaceBound : List S.Op → ℕ`) and peak
(`peakSpaceBound : List S.Op → S.Op → ℕ`) word bounds. -/
structure ObliviousSequenceImpl {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, v})
    (w base : ℕ) (params : Fin k_init → ℕ) : Type (max u v (z + 1)) where
  /-- Internal latent state type (such as a hash seed or coupled relational trace). -/
  Latent : Type z
  /-- Resting post-prefix word-footprint upper bound `x.frontier ≤ base + spaceBound prefOps`. -/
  spaceBound : List S.Op → ℕ
  /-- Peak intermediate word-footprint bound `y.frontier ≤ base + peakSpaceBound prefOps o`. -/
  peakSpaceBound : List S.Op → S.Op → ℕ
  /-- Expected instruction bound for `P.initCode`. -/
  initTime : ℝ≥0∞
  /-- Upper bound on initial concrete potential (`0` when unamortized). -/
  initPotential : ℕ := 0
  /-- Per-operation instruction charge. -/
  charge : S.Op → ℕ
  /-- Distributional invariant on the initial coupled distribution produced by `P.initCode`. -/
  initInv : PMF (LatentRState Latent r_ds) → Prop
  /-- Predicate under which `arguments_fit` bounds encoded arguments (`fun _ _ => True` default). -/
  validOp : Latent → S.Op → Prop := fun _ _ => True
  /-- Standalone register encoding for argument delivery. -/
  encode : S.Op → Fin r_ds → ℕ
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)
  /-- Initial distributions satisfying `initInv` are supported on word-bounded states. -/
  bounded : ∀ {ν : PMF (LatentRState Latent r_ds)}, initInv ν → ∀ t ∈ ν.support, t.data.Bounded w
  /-- Initial distributions satisfying `initInv` establish resting frontier bounds at `[]`. -/
  frontier_le : ∀ {ν : PMF (LatentRState Latent r_ds)}, initInv ν →
    ∀ t ∈ ν.support,
      base ≤ t.data.frontier ∧ t.data.frontier ≤ base + spaceBound [] ∧ t.data.regs P.baseReg = base
  /-- Standalone encoded arguments fit in `w`-bit words on operations satisfying `validOp`. -/
  arguments_fit : ∀ {z : Latent} (o : S.Op),
    validOp z o → ∀ i, P.input i = true → Fits w (encode o i)
  /-- Distributional initialization of `P.initCode` from `x₀.frontier = base`, preserving caller
  memory `[0, base)`. -/
  init_exec : ∀ {x₀ : RData r_ds},
    x₀.Bounded w → x₀.frontier = base → (∀ j, x₀.regs (P.initParams j) = params j) →
    Fits w (base + spaceBound []) →
    ∃ ν₀ : PMF (LatentRState Latent r_ds),
      ExecRCodeDist w P.initCode x₀ (ν₀.map LatentRState.data) initTime (base + spaceBound []) ∧
      initInv ν₀ ∧
      ∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr
  /-- Multi-operation execution across any admissible oblivious sequence `ops : List S.Op` whose
  trajectory peaks fit in `w`-bit words (`ObliviousPeakFits w base peakSpaceBound [] ops`). -/
  steps_exec : ∀ (ops : List S.Op) (ν₀ : PMF (LatentRState Latent r_ds)),
    S.ValidOpSeq ops → ObliviousPeakFits w base peakSpaceBound [] ops → initInv ν₀ →
    ∃ (ν_final : PMF (SeqROutcome Latent S.Result r_ds)) (T_ops : ℝ≥0∞),
      ExecSteps P S Latent w base spaceBound peakSpaceBound encode decode [] ops
        (ν₀.map SeqROutcome.ofLatentRState) ν_final T_ops ∧
      S.Contract ops (ν_final.map SeqROutcome.transcript) ∧
      T_ops ≤ (initPotential : ℝ≥0∞) + ((ops.map charge).sum : ℝ≥0∞)

namespace ObliviousSequenceImpl

variable {B B' : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init}
  {S : DataStructure.ObliviousSequenceSpec.{u, v}}
  {params : Fin k_init → ℕ}

/-- Total operation charge summed across `ops : List S.Op`. -/
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

/-- Specialization of `ExecSteps` from prefix `[]` to `C : ObliviousSequenceImpl`. -/
abbrev Steps (C : ObliviousSequenceImpl.{u, v, z} P S w base params) :
    List S.Op → PMF (SeqROutcome C.Latent S.Result r_ds) →
      PMF (SeqROutcome C.Latent S.Result r_ds) → ℝ≥0∞ → Prop :=
  ExecSteps P S C.Latent w base C.spaceBound C.peakSpaceBound C.encode C.decode []

/-- Specialization of `ExecProgramSteps` from prefix `[]` to `C : ObliviousSequenceImpl`. -/
abbrev ProgramSteps (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    (p_op : RProgram B r_ds) (out : Fin r_ds) :
    List S.Op → PMF (SeqROutcome C.Latent S.Result r_ds) →
      PMF (SeqROutcome C.Latent S.Result r_ds) → ℝ≥0∞ → Prop :=
  ExecProgramSteps P S C.Latent w base C.spaceBound C.peakSpaceBound C.encode C.decode p_op out []

/-- Transport an `ObliviousSequenceImpl` certificate along `φ : B.Simulates B'`. -/
def mapSimulates (φ : B.Simulates B')
    (C : ObliviousSequenceImpl.{u, v, z} P S w base params) :
    ObliviousSequenceImpl.{u, v, z} (P.mapSimulates φ) S w base params where
  Latent := C.Latent
  spaceBound := C.spaceBound
  peakSpaceBound := C.peakSpaceBound
  initTime := C.initTime
  initPotential := C.initPotential
  charge := C.charge
  initInv := C.initInv
  validOp := C.validOp
  encode := C.encode
  decode := C.decode
  bounded := C.bounded
  frontier_le := C.frontier_le
  arguments_fit := C.arguments_fit
  init_exec hx₀ hfr hpar hfit := by
    obtain ⟨ν₀, he, hinv, hcaller⟩ := C.init_exec hx₀ hfr hpar hfit
    exact ⟨ν₀, he.mapSimulates φ, hinv, hcaller⟩
  steps_exec ops ν₀ hv hfit hinv := by
    obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ := C.steps_exec ops ν₀ hv hfit hinv
    exact ⟨ν_final, T_ops, hex.mapSimulates φ, hcontract, hcost⟩

/-- Lift an exact-basis `ObliviousSequenceImpl` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : ObliviousSequenceImpl.{u, v, z} P S w base params) :
    ObliviousSequenceImpl.{u, v, z} P.toStandard S w base params :=
  C.mapSimulates .exactStandard

/-- **End-to-end expected-time, trajectory-space, caller-prefix, and distributional correctness
theorem (`seq_expected`).** -/
theorem seq_expected (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    {x₀ : RData r_ds} (ops : List S.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound []))
    (hv : S.ValidOpSeq ops) (hfit_ops : ObliviousPeakFits w base C.peakSpaceBound [] ops) :
    ∃ (ν₀ : PMF (LatentRState C.Latent r_ds))
      (ν_final : PMF (SeqROutcome C.Latent S.Result r_ds)) (T_ops : ℝ≥0∞),
      ExecRCodeDist w P.initCode x₀ (ν₀.map LatentRState.data) C.initTime
        (base + C.spaceBound []) ∧
      (∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
      C.Steps ops (ν₀.map SeqROutcome.ofLatentRState) ν_final T_ops ∧
      (∀ t ∈ ν_final.support,
        t.data.Bounded w ∧
        (base ≤ t.data.frontier ∧ t.data.frontier ≤ base + C.spaceBound ops ∧
          t.data.regs P.baseReg = base) ∧
        (∀ addr < base, t.data.mem addr = x₀.mem addr)) ∧
      S.Contract ops (ν_final.map SeqROutcome.transcript) ∧
      C.initTime + T_ops ≤
        C.initTime + (C.initPotential : ℝ≥0∞) + (C.totalCharge ops : ℝ≥0∞) := by
  obtain ⟨ν₀, he_init, hinv, hcaller₀⟩ := C.init_exec hx₀ hfr₀ hpar hfit₀
  obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ := C.steps_exec ops ν₀ hv hfit_ops hinv
  have hbdd₀ : ∀ t ∈ (ν₀.map (SeqROutcome.ofLatentRState (Result := S.Result))).support,
      t.data.Bounded w := by
    intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨u, hu, rfl⟩ := ht
    exact C.bounded hinv u hu
  have hfr_init : ∀ t ∈ (ν₀.map (SeqROutcome.ofLatentRState (Result := S.Result))).support,
      base ≤ t.data.frontier ∧ t.data.frontier ≤ base + C.spaceBound [] ∧
        t.data.regs P.baseReg = base := by
    intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨u, hu, rfl⟩ := ht
    exact C.frontier_le hinv u hu
  have hcaller_init : ∀ t ∈ (ν₀.map (SeqROutcome.ofLatentRState (Result := S.Result))).support,
      ∀ addr < base, t.data.mem addr = x₀.mem addr := by
    intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨u, hu, rfl⟩ := ht
    exact hcaller₀ u hu
  have hfr_fin := hex.frontier_le hfr_init
  rw [List.nil_append] at hfr_fin
  refine ⟨ν₀, ν_final, T_ops, he_init, hcaller₀, hex,
    fun t ht => ⟨hex.bounded hbdd₀ t ht, hfr_fin t ht, hex.caller_mem hcaller_init t ht⟩,
    hcontract, ?_⟩
  rw [add_assoc]
  exact add_le_add le_rfl hcost

/-- **End-to-end compiled flat-`RProgram` expected-time theorem (`seq_toExecRProgramDist`).** -/
theorem seq_toExecRProgramDist (C : ObliviousSequenceImpl.{u, v, z} P S w base params)
    (out : Fin r_ds) {x₀ : RData r_ds} (ops : List S.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound []))
    (hv : S.ValidOpSeq ops) (hfit_ops : ObliviousPeakFits w base C.peakSpaceBound [] ops) :
    ∃ (ν₀ : PMF (LatentRState C.Latent r_ds))
      (ν_final : PMF (SeqROutcome C.Latent S.Result r_ds)) (T_prog : ℝ≥0∞),
      ExecRProgramDist w (P.initProg out) out x₀ (ν₀.map LatentRState.data) (C.initTime + 1)
        (base + C.spaceBound []) ∧
      (∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
      C.ProgramSteps (P.opProg out) out ops (ν₀.map SeqROutcome.ofLatentRState) ν_final T_prog ∧
      (∀ t ∈ ν_final.support,
        t.data.Bounded w ∧
        (base ≤ t.data.frontier ∧ t.data.frontier ≤ base + C.spaceBound ops ∧
          t.data.regs P.baseReg = base) ∧
        (∀ addr < base, t.data.mem addr = x₀.mem addr)) ∧
      S.Contract ops (ν_final.map SeqROutcome.transcript) ∧
      (C.initTime + 1) + T_prog ≤
        (C.initTime + 1) + (C.initPotential : ℝ≥0∞) +
          (C.totalCharge ops : ℝ≥0∞) + (ops.length : ℝ≥0∞) := by
  obtain ⟨ν₀, ν_final, T_ops, he_init, hcaller₀, hex, hfin, hcontract, hcost⟩ :=
    C.seq_expected ops hx₀ hfr₀ hpar hfit₀ hv hfit_ops
  refine ⟨ν₀, ν_final, T_ops + (ops.length : ℝ≥0∞),
    he_init.toExecRProgramDist out, hcaller₀, hex.toExecRProgramDist out, hfin, hcontract, ?_⟩
  calc (C.initTime + 1) + (T_ops + ↑ops.length)
      = (C.initTime + T_ops) + 1 + ↑ops.length := by ac_rfl
    _ ≤ (C.initTime + ↑C.initPotential + ↑(C.totalCharge ops)) + 1 + ↑ops.length :=
        add_le_add (add_le_add hcost le_rfl) le_rfl
    _ = (C.initTime + 1) + ↑C.initPotential + ↑(C.totalCharge ops) + ↑ops.length := by ac_rfl

end ObliviousSequenceImpl

/-- Coupled latent seed, current abstract state, and accumulated relational transcript prefix for
embedding `Cslib.DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl` into
`ObliviousSequenceImpl`. -/
structure TraceRLatent (D : StateTransitionSpec.{u, v, z}) (Seed : Type) : Type (max u v z) where
  /-- Latent random seed from the underlying `StateTransitionImpl`. -/
  seed : Seed
  /-- Current abstract state of `D`. -/
  state : D.State
  /-- Relational execution transcript accumulated since `s₀`. -/
  trace : D.Transcript

/-- For a functional specification (`[D.HasStepFn stepFn]`), `ObliviousPeakFits` along the
canonical state trajectory `(D.run s₀ pref).1` agrees with `PeakFitsHistory`. -/
theorem obliviousPeakFits_iff_peakFitsHistory (D : StateTransitionSpec.{u, v, z})
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (w base : ℕ) (peakSpaceBound : D.State → D.Op → ℕ)
    (s₀ : D.State) (prefOps remOps : List D.Op) :
    ObliviousPeakFits w base (fun pref o => peakSpaceBound (D.run s₀ pref).1 o) prefOps remOps ↔
      PeakFitsHistory w base peakSpaceBound (D.run s₀ prefOps).1 remOps := by
  induction remOps generalizing prefOps with
  | nil => exact Iff.rfl
  | cons o os ih =>
    have hrun : (D.run s₀ (prefOps ++ [o])).1 = (D.stepFn (D.run s₀ prefOps).1 o).1 := by
      rw [D.run_append]; rfl
    simp only [obliviousPeakFits_cons, peakFitsHistory_cons, ih (prefOps ++ [o]), hrun]

end Cslib.DataStructure.WordRAM.Resizable.Randomized

/-! ## Canonical Embedding of `StateTransitionImpl` into `ObliviousSequenceImpl` -/

namespace Cslib.DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl

open Cslib.WordRAM Cslib.WordRAM.Resizable Cslib.DataStructure
open Cslib.DataStructure.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

private def projCoupled (C : StateTransitionImpl P D w base params s₀)
    (t : SeqROutcome (TraceRLatent D C.Seed) D.Result r_ds) :
    CoupledRState C.Seed D.State r_ds :=
  ⟨t.latent.seed, t.latent.state, t.data⟩

private theorem peakFitsOpSeq_of_obliviousPeakFits (C : StateTransitionImpl P D w base params s₀)
    (seqPeakSpaceBound : List D.Op → D.Op → ℕ)
    (hpeak : ∀ (tr : D.Transcript) (s : D.State) (o : D.Op),
      D.ValidTranscript s₀ tr s → D.valid s o → C.peakSpaceBound s o ≤ seqPeakSpaceBound tr.ops o)
    {remOps : List D.Op} :
    ∀ (tr : D.Transcript) (s : D.State),
      D.ValidTranscript s₀ tr s → D.ValidOpSeq s remOps →
      ObliviousPeakFits w base seqPeakSpaceBound tr.ops remOps →
      PeakFitsOpSeq w base C.peakSpaceBound s remOps := by
  induction remOps with
  | nil => intros; trivial
  | cons o os ih =>
    intro tr s htr hv hfit
    refine ⟨Nat.lt_of_le_of_lt (Nat.add_le_add_left (hpeak tr s o htr hv.1) base) hfit.1,
      fun s' a hstep => ?_⟩
    have htr' : D.ValidTranscript s₀ (tr ++ [⟨o, a, s'⟩]) s' :=
      htr.append (.cons ⟨o, a, s'⟩ hv.1 hstep (.nil s'))
    exact ih (tr ++ [⟨o, a, s'⟩]) s' htr' (hv.2 s' a hstep) (by simpa using hfit.2)

private theorem steps_toObliviousSequenceImpl (C : StateTransitionImpl P D w base params s₀)
    (seqSpaceBound : List D.Op → ℕ) (seqPeakSpaceBound : List D.Op → D.Op → ℕ)
    (opCharge : D.Op → ℕ)
    (hspace : ∀ (tr : D.Transcript) (s : D.State),
      D.ValidTranscript s₀ tr s → C.spaceBound s ≤ seqSpaceBound tr.ops)
    (hpeak : ∀ (tr : D.Transcript) (s : D.State) (o : D.Op),
      D.ValidTranscript s₀ tr s → D.valid s o → C.peakSpaceBound s o ≤ seqPeakSpaceBound tr.ops o)
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o)
    {remOps : List D.Op} {ν_rel ν_final_rel : PMF (CoupledRState C.Seed D.State r_ds)}
    {T_ops C_ops : ℝ≥0∞} (hex : C.ExecSteps remOps ν_rel ν_final_rel T_ops C_ops)
    (prefOps : List D.Op) (ν : PMF (SeqROutcome (TraceRLatent D C.Seed) D.Result r_ds))
    (hproj : ν.map C.projCoupled = ν_rel)
    (hsupp : ∀ t ∈ ν.support,
      t.latent.trace.ops = prefOps ∧
      t.latent.trace.labels = t.transcript ∧
      D.ValidTranscript s₀ t.latent.trace t.latent.state ∧
      D.ValidOpSeq t.latent.state remOps ∧
      C.rep t.latent.seed t.latent.state t.data) :
    ∃ ν_final : PMF (SeqROutcome (TraceRLatent D C.Seed) D.Result r_ds),
      Randomized.ExecSteps P (D.toObliviousSequenceSpec s₀)
        (TraceRLatent D C.Seed) w base seqSpaceBound seqPeakSpaceBound C.encode C.decode
        prefOps remOps ν ν_final T_ops ∧
      (∀ t ∈ ν_final.support,
        t.latent.trace.ops = prefOps ++ remOps ∧
        t.latent.trace.labels = t.transcript ∧
        D.ValidTranscript s₀ t.latent.trace t.latent.state) ∧
      C_ops ≤ (((remOps.map opCharge).sum : ℕ) : ℝ≥0∞) := by
  induction hex generalizing prefOps ν with
  | nil _ =>
    refine ⟨ν, .nil (S := D.toObliviousSequenceSpec s₀) prefOps ν, fun t ht => ?_, zero_le⟩
    obtain ⟨hops, hlbl, htr, _, _⟩ := hsupp t ht
    rw [List.append_nil]
    exact ⟨hops, hlbl, htr⟩
  | @cons o os ν_rel ν_final_rel μ_rel T_rel T_rest C_rest hstep _ ih =>
    subst hproj
    have hmem : ∀ t ∈ ν.support, C.projCoupled t ∈ (ν.map C.projCoupled).support :=
      fun t ht => (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
    have h_a_nonempty : Nonempty (D.Result o) := by
      obtain ⟨t₀, ht₀⟩ := ν.support_nonempty
      obtain ⟨q₀, hq₀⟩ := (μ_rel (C.projCoupled t₀)).support_nonempty
      obtain ⟨a₀, _⟩ := (hstep _ (hmem t₀ ht₀)).2 q₀ hq₀
      exact ⟨a₀⟩
    let outOf : CoupledRState C.Seed D.State r_ds → D.Result o :=
      fun q => (C.decode o q.data.regs).getD (Classical.choice h_a_nonempty)
    let liftStep (t : SeqROutcome (TraceRLatent D C.Seed) D.Result r_ds)
        (q : CoupledRState C.Seed D.State r_ds) :
        StepROutcome (TraceRLatent D C.Seed) (D.Result o) r_ds :=
      ⟨⟨q.seed, q.state, t.latent.trace ++ [⟨o, outOf q, q.state⟩]⟩, q.data, outOf q⟩
    let μ_step (t : SeqROutcome (TraceRLatent D C.Seed) D.Result r_ds) :
        PMF (StepROutcome (TraceRLatent D C.Seed) (D.Result o) r_ds) :=
      (μ_rel (C.projCoupled t)).map (liftStep t)
    let ν₁ : PMF (SeqROutcome (TraceRLatent D C.Seed) D.Result r_ds) :=
      ν.bind fun t => (μ_step t).map (t.appendStep o)
    have hproj₁ : ν₁.map C.projCoupled = (ν.map C.projCoupled).bind μ_rel := by
      dsimp only [ν₁, μ_step]
      rw [PMF.map_bind, PMF.bind_map]
      refine congrArg (ν.bind ·) (funext fun t => ?_)
      rw [PMF.map_comp, PMF.map_comp]
      exact PMF.map_id (μ_rel (C.projCoupled t))
    have hsupp₁ : ∀ u ∈ ν₁.support,
        u.latent.trace.ops = prefOps ++ [o] ∧
        u.latent.trace.labels = u.transcript ∧
        D.ValidTranscript s₀ u.latent.trace u.latent.state ∧
        D.ValidOpSeq u.latent.state os ∧
        C.rep u.latent.seed u.latent.state u.data := by
      intro u hu
      rw [PMF.mem_support_bind_iff] at hu; obtain ⟨t, ht, hu⟩ := hu
      rw [PMF.mem_support_map_iff] at hu; obtain ⟨u', hu', rfl⟩ := hu
      dsimp only [μ_step] at hu'; rw [PMF.mem_support_map_iff] at hu'; obtain ⟨q, hq, rfl⟩ := hu'
      obtain ⟨hops_t, hlbl_t, htr_t, hv_t, _⟩ := hsupp t ht
      obtain ⟨a, hstep_a, hdec_a, hrep_q, _⟩ := (hstep _ (hmem t ht)).2 q hq
      have hout_eq : outOf q = a := by simp [outOf, hdec_a]
      refine ⟨by simp [SeqROutcome.appendStep, liftStep, hops_t],
        by simp [SeqROutcome.appendStep, liftStep, hlbl_t], ?_, hv_t.2 q.state a hstep_a, hrep_q⟩
      refine htr_t.append ?_
      rw [hout_eq]; exact .cons ⟨o, a, q.state⟩ hv_t.1 hstep_a (.nil q.state)
    obtain ⟨ν_final, hex_rest, htr_final, hC_rest⟩ := ih (prefOps ++ [o]) ν₁ hproj₁ hsupp₁
    refine ⟨ν_final, ?_, fun t ht => ?_, ?_⟩
    · rw [Cslib.Probability.PMF.tsum_map_mul]
      refine Randomized.ExecSteps.cons (S := D.toObliviousSequenceSpec s₀)
        (μ_step := μ_step) (T_step := fun t => T_rel (C.projCoupled t)) (fun t ht => ?_) hex_rest
      obtain ⟨hops_t, _, htr_t, hv_t, hrep_t⟩ := hsupp t ht
      have hbdd_t : t.data.Bounded w := C.bounded hrep_t
      have hfit_t : ∀ i, P.input i = true → Fits w (C.encode o i) := C.arguments_fit o hv_t.1
      obtain ⟨he_rel, hq_rel⟩ := hstep _ (hmem t ht)
      have hpeak_le :
          base + C.peakSpaceBound t.latent.state o ≤ base + seqPeakSpaceBound prefOps o := by
        rw [← hops_t]
        exact Nat.add_le_add_left (hpeak t.latent.trace t.latent.state o htr_t hv_t.1) base
      refine ⟨hbdd_t, hfit_t, P.prepare_bounded hbdd_t hfit_t, ?_, ?_⟩
      · refine (he_rel.mono_peak hpeak_le).congr_dist ?_ le_rfl
        dsimp only [μ_step]; rw [PMF.map_comp]; rfl
      · intro u hu
        dsimp only [μ_step] at hu; rw [PMF.mem_support_map_iff] at hu; obtain ⟨q, hq, rfl⟩ := hu
        obtain ⟨a, hstep_a, hdec_a, hrep_q, hcaller_q⟩ := hq_rel q hq
        have hout_eq : outOf q = a := by simp [outOf, hdec_a]
        obtain ⟨hlo_q, hhi_q, hbase_q⟩ := C.frontier_le hrep_q
        have htr_q : D.ValidTranscript s₀ (t.latent.trace ++ [⟨o, a, q.state⟩]) q.state :=
          htr_t.append (.cons ⟨o, a, q.state⟩ hv_t.1 hstep_a (.nil q.state))
        have hops_q :
            (t.latent.trace ++ [({ op := o, result := a, nextState := q.state } : D.Step)]).ops =
              prefOps ++ [o] := by
          rw [StateTransitionSpec.Transcript.ops_append, hops_t]; rfl
        have hspace_q : C.spaceBound q.state ≤ seqSpaceBound (prefOps ++ [o]) := by
          rw [← hops_q]; exact hspace _ q.state htr_q
        exact ⟨C.bounded hrep_q,
          ⟨hlo_q, hhi_q.trans (Nat.add_le_add_left hspace_q base), hbase_q⟩,
          by simp [liftStep, hout_eq, hdec_a], hcaller_q⟩
    · obtain ⟨hops, hlbl, htr⟩ := htr_final t ht
      rw [List.append_assoc, List.singleton_append] at hops
      exact ⟨hops, hlbl, htr⟩
    · rw [List.map_cons, List.sum_cons, Nat.cast_add, Cslib.Probability.PMF.tsum_map_mul]
      refine add_le_add (Cslib.Probability.PMF.tsum_mul_le_of_support ν fun t ht => ?_) hC_rest
      exact Nat.cast_le.mpr (hcharge _ o (hsupp t ht).2.2.2.1.1)

/-- Canonical embedding of any relational
`Cslib.DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl` certificate into
`ObliviousSequenceImpl` realizing `D.toObliviousSequenceSpec s₀`, given trajectory-indexed resting
and peak word bounds (`seqSpaceBound`, `seqPeakSpaceBound`) and a state-independent operation
charge `opCharge : D.Op → ℕ`. -/
@[expose] noncomputable def toObliviousSequenceImpl (C : StateTransitionImpl P D w base params s₀)
    (seqSpaceBound : List D.Op → ℕ) (seqPeakSpaceBound : List D.Op → D.Op → ℕ)
    (opCharge : D.Op → ℕ := C.charge s₀)
    (hspace : ∀ (tr : D.Transcript) (s : D.State),
      D.ValidTranscript s₀ tr s → C.spaceBound s ≤ seqSpaceBound tr.ops)
    (hpeak : ∀ (tr : D.Transcript) (s : D.State) (o : D.Op),
      D.ValidTranscript s₀ tr s → D.valid s o → C.peakSpaceBound s o ≤ seqPeakSpaceBound tr.ops o)
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o := by intros; exact le_rfl) :
    ObliviousSequenceImpl.{v, z, max u v z} P (D.toObliviousSequenceSpec s₀) w base params where
  Latent := TraceRLatent D C.Seed
  spaceBound := seqSpaceBound
  peakSpaceBound := seqPeakSpaceBound
  initTime := C.initTime
  initPotential := C.initPotential
  charge := opCharge
  initInv ν₀ :=
    (∀ s, (∀ t ∈ (ν₀.map fun t => (⟨t.latent.seed, t.latent.state, t.data⟩ :
        CoupledRState C.Seed D.State r_ds)).support, t.state = s) →
      ∀ θ, ((ν₀.map fun t => (⟨t.latent.seed, t.latent.state, t.data⟩ :
          CoupledRState C.Seed D.State r_ds)).map CoupledRState.seed) θ ≤
        C.seedSlack * C.seedLaw s θ) ∧
    (C.singleState → ∃ s, ∀ t ∈ (ν₀.map fun t => (⟨t.latent.seed, t.latent.state, t.data⟩ :
        CoupledRState C.Seed D.State r_ds)).support, t.state = s) ∧
    (∀ t ∈ ν₀.support,
      t.latent.state = s₀ ∧
      t.latent.trace = [] ∧
      C.rep t.latent.seed s₀ t.data ∧
      C.potential t.latent.seed t.data ≤ C.initPotential)
  validOp z o := D.valid z.state o
  encode := C.encode
  decode := C.decode
  bounded hinv t ht := by
    obtain ⟨_, _, hsupp⟩ := hinv; obtain ⟨_, _, hrep, _⟩ := hsupp t ht; exact C.bounded hrep
  frontier_le hinv t ht := by
    obtain ⟨_, _, hsupp⟩ := hinv; obtain ⟨_, _, hrep, _⟩ := hsupp t ht
    obtain ⟨hlo, hhi, hbase⟩ := C.frontier_le hrep
    exact ⟨hlo, hhi.trans (Nat.add_le_add_left (hspace [] s₀ (.nil s₀)) base), hbase⟩
  arguments_fit o hv := C.arguments_fit o hv
  init_exec hx₀ hfr hpar hfit := by
    have hspace₀ : base + C.spaceBound s₀ ≤ base + seqSpaceBound [] :=
      Nat.add_le_add_left (hspace [] s₀ (.nil s₀)) base
    obtain ⟨ν₀, he, hseed, hsupp⟩ := C.init_exec hx₀ hfr hpar (Nat.lt_of_le_of_lt hspace₀ hfit)
    let liftInit : C.Seed × RData r_ds → LatentRState (TraceRLatent D C.Seed) r_ds :=
      fun p => ⟨⟨p.1, s₀, []⟩, p.2⟩
    refine ⟨ν₀.map liftInit, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · refine (he.mono_peak hspace₀).congr_dist ?_ le_rfl
      rw [PMF.map_comp]; rfl
    · intro s hs θ
      obtain ⟨p₀, hp₀⟩ := ν₀.support_nonempty
      have hs_eq : s = s₀ :=
        (hs ⟨p₀.1, s₀, p₀.2⟩
          ((PMF.mem_support_map_iff _ _ _).mpr
            ⟨liftInit p₀, (PMF.mem_support_map_iff _ _ _).mpr ⟨p₀, hp₀, rfl⟩, rfl⟩)).symm
      subst hs_eq
      rw [PMF.map_comp, PMF.map_comp]
      exact hseed θ
    · intro _
      refine ⟨s₀, fun t ht => ?_⟩
      rw [PMF.mem_support_map_iff] at ht; obtain ⟨u, hu, rfl⟩ := ht
      rw [PMF.mem_support_map_iff] at hu; obtain ⟨_, _, rfl⟩ := hu; rfl
    · intro t ht
      rw [PMF.mem_support_map_iff] at ht; obtain ⟨p, hp, rfl⟩ := ht
      obtain ⟨hrep, hpot, _⟩ := hsupp p hp
      exact ⟨rfl, rfl, hrep, hpot⟩
    · intro t ht
      rw [PMF.mem_support_map_iff] at ht; obtain ⟨p, hp, rfl⟩ := ht
      obtain ⟨_, _, hcaller⟩ := hsupp p hp; exact hcaller
  steps_exec ops ν₀ hv hfit_ops hinv := by
    obtain ⟨hseed₀, hsingle₀, hsupp₀⟩ := hinv
    let ν_seq : PMF (SeqROutcome (TraceRLatent D C.Seed) D.Result r_ds) :=
      ν₀.map SeqROutcome.ofLatentRState
    let ν_rel : PMF (CoupledRState C.Seed D.State r_ds) :=
      ν₀.map fun t => ⟨t.latent.seed, t.latent.state, t.data⟩
    have hproj_eq : ν_seq.map C.projCoupled = ν_rel := by
      dsimp only [ν_seq]; rw [PMF.map_comp]; rfl
    have hsupp_seq : ∀ t ∈ ν_seq.support,
        t.latent.trace.ops = [] ∧
        t.latent.trace.labels = t.transcript ∧
        D.ValidTranscript s₀ t.latent.trace t.latent.state ∧
        D.ValidOpSeq t.latent.state ops ∧
        C.rep t.latent.seed t.latent.state t.data := by
      intro t ht
      rw [PMF.mem_support_map_iff] at ht; obtain ⟨u, hu, rfl⟩ := ht
      obtain ⟨hs_u, htr_u, hrep_u, _⟩ := hsupp₀ u hu
      dsimp only [SeqROutcome.ofLatentRState]; rw [hs_u, htr_u]
      exact ⟨rfl, rfl, .nil s₀, hv, hrep_u⟩
    have hsupp_rel : ∀ t ∈ ν_rel.support,
        D.ValidOpSeq t.state ops ∧
        PeakFitsOpSeq w base C.peakSpaceBound t.state ops ∧
        C.rep t.seed t.state t.data := by
      intro t ht
      rw [← hproj_eq, PMF.mem_support_map_iff] at ht; obtain ⟨u, hu, rfl⟩ := ht
      obtain ⟨hops_u, _, htr_u, hv_u, hrep_u⟩ := hsupp_seq u hu
      refine ⟨hv_u, ?_, hrep_u⟩
      exact C.peakFitsOpSeq_of_obliviousPeakFits seqPeakSpaceBound hpeak u.latent.trace
        u.latent.state htr_u hv_u (hops_u ▸ hfit_ops)
    obtain ⟨_, T_ops, C_ops, hex_rel, _, _, hamort⟩ :=
      C.steps_expected_amortized ops ν_rel
        (fun t ht => (hsupp_rel t ht).1)
        (fun t ht => by obtain ⟨_, hf, _⟩ := hsupp_rel t ht; exact hf) hseed₀
        (fun t ht => by obtain ⟨_, _, hr⟩ := hsupp_rel t ht; exact hr) hsingle₀
    obtain ⟨ν_final, hex, htr_final, hC_ops⟩ :=
      C.steps_toObliviousSequenceImpl seqSpaceBound seqPeakSpaceBound opCharge hspace hpeak hcharge
        hex_rel [] ν_seq hproj_eq hsupp_seq
    have hpot₀ :
        (∑' t, ν_rel t * (C.potential t.seed t.data : ℝ≥0∞)) ≤ (C.initPotential : ℝ≥0∞) := by
      rw [Cslib.Probability.PMF.tsum_map_mul]
      refine Cslib.Probability.PMF.tsum_mul_le_of_support ν₀ fun u hu => ?_
      obtain ⟨_, _, _, hpot_u⟩ := hsupp₀ u hu; exact Nat.cast_le.mpr hpot_u
    refine ⟨ν_final, T_ops, hex, ?_, ?_⟩
    · intro out hout
      rw [PMF.mem_support_map_iff] at hout; obtain ⟨q, hq, rfl⟩ := hout
      obtain ⟨hops_q, hlbl_q, htr_q⟩ := htr_final q hq
      rw [List.nil_append] at hops_q
      exact ⟨q.latent.trace, q.latent.state, hops_q, hlbl_q, htr_q⟩
    · rw [add_comm]
      exact le_self_add.trans (hamort.trans (add_le_add hC_ops hpot₀))

/-- Canonical embedding of any functional
`Cslib.DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl` certificate
(`[D.HasStepFn stepFn]`) into `ObliviousSequenceImpl` using the exact canonical trajectory bounds
`pref ↦ C.spaceBound (D.run s₀ pref).1` and `(pref, o) ↦ C.peakSpaceBound (D.run s₀ pref).1 o`. -/
@[expose] noncomputable def toObliviousSequenceImplOfFn
    (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (opCharge : D.Op → ℕ := C.charge s₀)
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o := by intros; exact le_rfl) :
    ObliviousSequenceImpl.{v, z, max u v z} P (D.toObliviousSequenceSpec s₀) w base params :=
  C.toObliviousSequenceImpl
    (fun pref => C.spaceBound (D.run s₀ pref).1)
    (fun pref o => C.peakSpaceBound (D.run s₀ pref).1 o)
    opCharge
    (fun tr s htr => by
      obtain ⟨_, rfl, _⟩ := (D.validTranscript_iff_run s₀ tr s).mp htr; exact le_rfl)
    (fun tr s _ htr _ => by
      obtain ⟨_, rfl, _⟩ := (D.validTranscript_iff_run s₀ tr s).mp htr; exact le_rfl)
    hcharge

@[simp]
theorem toObliviousSequenceImplOfFn_spaceBound (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (opCharge) (hcharge) (pref : List D.Op) :
    (C.toObliviousSequenceImplOfFn opCharge hcharge).spaceBound pref =
      C.spaceBound (D.run s₀ pref).1 := rfl

@[simp]
theorem toObliviousSequenceImplOfFn_peakSpaceBound (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (opCharge) (hcharge) (pref : List D.Op) (o : D.Op) :
    (C.toObliviousSequenceImplOfFn opCharge hcharge).peakSpaceBound pref o =
      C.peakSpaceBound (D.run s₀ pref).1 o := rfl

@[simp]
theorem toObliviousSequenceImplOfFn_charge (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (opCharge) (hcharge) :
    (C.toObliviousSequenceImplOfFn opCharge hcharge).charge = opCharge := rfl

end Cslib.DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl
