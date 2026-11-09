/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.CellProbe.StateTransition
public import CslibFrontier.DataStructure.ObliviousSequence
public import CslibFrontier.Computability.CellProbe.Randomized
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map

/-!
# Randomized Cell-Probe State-Transition Implementations

This file extends `Cslib.DataStructure.CellProbe.StateTransitionImpl` to randomized cell-probe
schemes (`Cslib.CellProbe.Randomized.Scheme`, [Miltersen1999], §1.2) implementing relational
state-transition specifications (`Cslib.DataStructure.StateTransitionSpec`, [CLRS2009],
Section 17.3; [MitzenmacherUpfal2017], Sections 2.1 and 2.3).

A `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl D P s₀` couples cell-probe
execution with a latent seed type `Seed : Type`, a reference distribution `seedLaw : PMF Seed` up to
density factor `seedSlack : ℝ≥0∞`, a seed-coupled invariant `rep`, and an addition-only `ℝ≥0∞`
amortized-in-expectation probe inequality:
* Both initial-memory randomness (`P.init : PMF (Mem cells w)`) and per-operation internal coin
  flips (`P.step o : RandProbeTree cells w (D.Result o)`) are supported;
* `CoupledOutcome` carries the returned `result` explicitly so that the step marginal equation
  `((P.step o).run t.mem).map Prod.fst = (μ_step t).map CoupledOutcome.resultMem` holds directly
  without `Classical.choice`;
* `singleState : Prop` (default `False` for general relational specifications; `True` in `ofFn` for
  deterministic specifications `[D.HasStepFn f]`) prevents adaptive correlation between the
  abstract state and latent seed when needed by oblivious-adversary structures.

## Main definitions

* `Cslib.DataStructure.CellProbe.Randomized.CoupledState`,
  `Cslib.DataStructure.CellProbe.Randomized.CoupledOutcome`,
  `Cslib.DataStructure.CellProbe.Randomized.CoupledOutcome.toCoupledState`,
  `Cslib.DataStructure.CellProbe.Randomized.CoupledOutcome.resultMem`,
  `Cslib.DataStructure.CellProbe.Randomized.TraceState`: named state, step-outcome, and transcript
  bundles for coupled distributional analysis.
* `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl`: certified randomized cell-probe
  implementation of `D : StateTransitionSpec` from initial state `s₀`.
* `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.ofFn`: constructor for deterministic
  specifications (`[D.HasStepFn f]`).
* `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.padCells`: cell-space monotonicity
  (`cells ≤ cells'`) via `Cslib.CellProbe.Randomized.Scheme.padCells`.
* `Cslib.DataStructure.CellProbe.StateTransitionImpl.toRandomized`: canonical embedding of any
  deterministic `CellProbe.StateTransitionImpl` into `Randomized.StateTransitionImpl`.

## Main results

* `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.runFrom_cons_fst`,
  `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.runFrom_append_fst`,
  `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.expectedProbesFrom_cons`,
  `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.expectedProbesFrom_append`:
  structural decomposition of `Randomized.Scheme.runFrom` and `expectedProbesFrom`.
* `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.seq_expected_amortized`:
  multi-operation coupled transcript and expected-amortized probe telescope over any demonically
  admissible sequence `D.ValidOpSeq s₀ ops`.
* `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.contract_runSeq`: zero-error
  transcript correctness `(D.toObliviousSequenceSpec s₀).Contract ops ((P.runSeq ops).map Prod.fst)`
  on `D.ValidOpSeq s₀ ops`.
* `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.expectedSeqProbes_le_of_opCharge`:
  expected sequence probe bound under a state-independent operation charge bound `opCharge`.
* `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.seq_expected_amortized_ofFn`,
  `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.expectedSeqProbes_le_ofFn`:
  specialization to deterministic specifications (`[D.HasStepFn f]`), certifying exact
  concentration on `(D.run s₀ ops).2` and
  `P.expectedSeqProbes ops ≤ C.initPotential + D.totalCost C.charge s₀ ops`.

## References

* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 17.3][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing: Randomization and Probabilistic
  Techniques in Algorithms and Data Analysis*, Sections 2.1 and 2.3][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.DataStructure.CellProbe.Randomized

open Cslib.CellProbe Cslib.Probability
open scoped ENNReal

universe u v

/-! ### Coupled state, step-outcome, and transcript bundles -/

/-- Coupled latent seed, abstract specification state, and concrete cell-probe memory `Mem cells w`
for relational randomized cell-probe analysis. -/
structure CoupledState (Seed : Type) (State : Type u) (cells w : ℕ) : Type u where
  /-- Latent random seed. -/
  seed : Seed
  /-- Abstract specification state. -/
  state : State
  /-- Concrete cell-probe memory (`cells` words of `w` bits). -/
  mem : Mem cells w

/-- Coupled post-step outcome pairing the updated latent seed, abstract post-state, post-memory, and
returned observation. Carrying `result` explicitly makes the marginal equation
`((P.step o).run t.mem).map Prod.fst = (μ_step t).map CoupledOutcome.resultMem` syntactic without
`Classical.choice`. -/
structure CoupledOutcome (Seed : Type) (State : Type u) (Result : Type) (cells w : ℕ) : Type u where
  /-- Updated latent random seed. -/
  seed : Seed
  /-- Updated abstract specification state. -/
  state : State
  /-- Updated concrete cell-probe memory. -/
  mem : Mem cells w
  /-- Observation returned by the operation. -/
  result : Result

/-- Forget `result` to obtain the post-step `CoupledState`. -/
@[expose] def CoupledOutcome.toCoupledState {Seed : Type} {State : Type u} {Result : Type}
    {cells w : ℕ} (q : CoupledOutcome Seed State Result cells w) :
    CoupledState Seed State cells w :=
  ⟨q.seed, q.state, q.mem⟩

/-- Extract `(q.result, q.mem)` for comparison against `((P.step o).run m).map Prod.fst`. -/
@[expose] def CoupledOutcome.resultMem {Seed : Type} {State : Type u} {Result : Type}
    {cells w : ℕ} (q : CoupledOutcome Seed State Result cells w) :
    Result × Mem cells w :=
  (q.result, q.mem)

/-- Coupled state augmented with an accumulated relational transcript `D.Transcript`. -/
structure TraceState (Seed : Type) (D : StateTransitionSpec.{u, v, 0}) (cells w : ℕ) :
    Type (max u v) where
  /-- Current latent random seed. -/
  seed : Seed
  /-- Current abstract specification state. -/
  state : D.State
  /-- Current concrete cell-probe memory. -/
  mem : Mem cells w
  /-- Accumulated relational execution transcript from `s₀`. -/
  trace : D.Transcript

/-! ### Randomized cell-probe `StateTransitionImpl` -/

/-- Certified randomized cell-probe implementation of a relational `D : StateTransitionSpec` from
initial state `s₀` over `P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w`. -/
structure StateTransitionImpl {cells w : ℕ}
    (D : StateTransitionSpec.{u, v, 0})
    (P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w)
    (s₀ : D.State) : Type (max u v 1) where
  /-- Latent random seed type (`Unit` when no persistent seed is needed). -/
  Seed : Type
  /-- Reference distribution over latent seeds. -/
  seedLaw : PMF Seed
  /-- Marginal density slack factor (`1` when the seed marginal is exact). -/
  seedSlack : ℝ≥0∞ := 1
  /-- Finiteness of `seedSlack`. -/
  seedSlack_ne_top : seedSlack ≠ ⊤ := by simp
  /-- Upper bound on initial concrete potential (`0` when unamortized). -/
  initPotential : ℕ := 0
  /-- Amortized expected probe charge per operation. -/
  charge : D.State → D.Op → ℕ
  /-- Seed-indexed representation invariant linking `Seed`, `D.State`, and `Mem cells w`. -/
  rep : Seed → D.State → Mem cells w → Prop
  /-- Seed-indexed nonnegative integer potential (`0` when worst-case / unamortized). -/
  potential : Seed → Mem cells w → ℕ := fun _ _ => 0
  /-- Whether `step_exec` requires the pre-state distribution `ν` to concentrate on a single
  abstract state (`False` by default; `True` in `StateTransitionImpl.ofFn`). -/
  singleState : Prop := False
  /-- Coupled initialization distribution witnessing `P.init`, seed-marginal control, `rep`, and
  `potential ≤ initPotential` at `s₀`. -/
  init_exec : ∃ ν₀ : PMF (Seed × Mem cells w),
    ν₀.map Prod.snd = P.init ∧
    (∀ θ, (ν₀.map Prod.fst) θ ≤ seedSlack * seedLaw θ) ∧
    ∀ p ∈ ν₀.support, rep p.1 s₀ p.2 ∧ potential p.1 p.2 ≤ initPotential
  /-- Coupled one-step execution of `P.step o` from any coupled distribution `ν`, matching the
  `(result, postMem)` marginal of `(P.step o).run t.mem`, angelically witnessing `D.step`,
  preserving seed-marginal control and `singleState`, and satisfying the addition-only `ℝ≥0∞`
  amortized-in-expectation probe inequality. -/
  step_exec : ∀ (o : D.Op) (ν : PMF (CoupledState Seed D.State cells w)),
    (singleState → ∃ s, ∀ t ∈ ν.support, t.state = s) →
    (∀ θ, (ν.map CoupledState.seed) θ ≤ seedSlack * seedLaw θ) →
    (∀ t ∈ ν.support, D.valid t.state o ∧ rep t.seed t.state t.mem) →
    ∃ μ_step : CoupledState Seed D.State cells w →
        PMF (CoupledOutcome Seed D.State (D.Result o) cells w),
      (∀ t ∈ ν.support,
        ((P.step o).run t.mem).map Prod.fst = (μ_step t).map CoupledOutcome.resultMem ∧
        ∀ q ∈ (μ_step t).support,
          D.step t.state o q.state q.result ∧
          rep q.seed q.state q.mem) ∧
      (∀ θ', ((ν.bind μ_step).map CoupledOutcome.seed) θ' ≤ seedSlack * seedLaw θ') ∧
      (singleState → ∃ s', ∀ q ∈ (ν.bind μ_step).support, q.state = s') ∧
      (∑' t, ν t * ((P.step o).expectedProbes t.mem +
          ∑' q, μ_step t q * (potential q.seed q.mem : ℝ≥0∞))) ≤
        ∑' t, ν t * ((charge t.state o : ℝ≥0∞) + (potential t.seed t.mem : ℝ≥0∞))

end Cslib.DataStructure.CellProbe.Randomized

/-! ### Deterministic-to-randomized lifting -/

namespace Cslib.DataStructure.CellProbe.StateTransitionImpl

open Cslib.CellProbe Cslib.DataStructure.CellProbe.Randomized
open scoped ENNReal

universe u v

/-- Canonical embedding of any deterministic `CellProbe.StateTransitionImpl` into
`CellProbe.Randomized.StateTransitionImpl` over `Randomized.Scheme.ofDeterministic P`
(`Seed := Unit`, `seedLaw := PMF.pure ()`, `seedSlack := 1`). -/
@[expose] noncomputable def toRandomized {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State}
    (C : StateTransitionImpl D P s₀) :
    Randomized.StateTransitionImpl D (Cslib.CellProbe.Randomized.Scheme.ofDeterministic P) s₀ where
  Seed := Unit
  seedLaw := PMF.pure ()
  seedSlack := 1
  initPotential := C.initPotential
  charge := C.charge
  rep _ s m := C.rep s m
  potential _ m := C.potential m
  init_exec := by
    refine ⟨PMF.pure ((), P.init), ?_, ?_, ?_⟩
    · simp [Cslib.CellProbe.Randomized.Scheme.ofDeterministic]
    · intro θ
      cases θ
      simp
    · intro p hp
      rw [PMF.mem_support_pure_iff] at hp
      subst hp
      exact ⟨C.init_rep, C.init_potential⟩
  step_exec o ν _ _ hsupp := by
    classical
    let hasInv : CoupledState Unit D.State cells w → Prop := fun t =>
      D.valid t.state o ∧ C.rep t.state t.mem
    let nextS : CoupledState Unit D.State cells w → D.State := fun t =>
      if ht : hasInv t then
        Classical.choose (C.step_exec o ht.2 ht.1)
      else t.state
    let μ_step : CoupledState Unit D.State cells w →
        PMF (CoupledOutcome Unit D.State (D.Result o) cells w) :=
      fun t => PMF.pure ⟨(), nextS t, ((P.step o).run t.mem).2, ((P.step o).run t.mem).1⟩
    refine ⟨μ_step, ?_, ?_, nofun, ?_⟩
    · intro t ht_mem
      have ht : hasInv t := hsupp t ht_mem
      have hspec := Classical.choose_spec (C.step_exec o ht.2 ht.1)
      have hs_eq : nextS t = Classical.choose (C.step_exec o ht.2 ht.1) := by
        simp [nextS, ht]
      refine ⟨?_, ?_⟩
      · simp only [Cslib.CellProbe.Randomized.Scheme.ofDeterministic,
          RandProbeTree.run_ofProbeTree, PMF.pure_map, μ_step, CoupledOutcome.resultMem]
      · intro q hq
        rw [PMF.mem_support_pure_iff] at hq
        subst hq
        simpa only [hs_eq] using ⟨hspec.1, hspec.2.1⟩
    · intro θ'
      cases θ'
      have hconst : ((ν.bind μ_step).map CoupledOutcome.seed) () = 1 := by
        rw [PMF.map_bind]
        simp [μ_step]
      simp [hconst]
    · refine tsum_le_tsum fun t => ?_
      by_cases ht_mem : t ∈ ν.support
      · refine mul_le_mul_right ?_ _
        have ht : hasInv t := hsupp t ht_mem
        have hpot := (Classical.choose_spec (C.step_exec o ht.2 ht.1)).2.2
        simp only [Cslib.CellProbe.Randomized.Scheme.ofDeterministic,
          RandProbeTree.expectedProbes_ofProbeTree, μ_step]
        rw [tsum_eq_single ⟨(), nextS t, ((P.step o).run t.mem).2, ((P.step o).run t.mem).1⟩
          (fun q hq => by simp [PMF.pure_apply, hq])]
        simp only [PMF.pure_apply_self, one_mul]
        exact_mod_cast hpot
      · rw [(PMF.apply_eq_zero_iff _ _).mpr ht_mem, zero_mul, zero_mul]

@[simp]
theorem toRandomized_seed {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State} (C : StateTransitionImpl D P s₀) :
    C.toRandomized.Seed = Unit :=
  rfl

@[simp]
theorem toRandomized_seedLaw {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State} (C : StateTransitionImpl D P s₀) :
    C.toRandomized.seedLaw = PMF.pure () :=
  rfl

@[simp]
theorem toRandomized_seedSlack {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State} (C : StateTransitionImpl D P s₀) :
    C.toRandomized.seedSlack = 1 :=
  rfl

@[simp]
theorem toRandomized_initPotential {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State} (C : StateTransitionImpl D P s₀) :
    C.toRandomized.initPotential = C.initPotential :=
  rfl

@[simp]
theorem toRandomized_charge {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State} (C : StateTransitionImpl D P s₀) :
    C.toRandomized.charge = C.charge :=
  rfl

@[simp]
theorem toRandomized_rep {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State} (C : StateTransitionImpl D P s₀)
    (θ : Unit) (s : D.State) (m : Mem cells w) :
    C.toRandomized.rep θ s m ↔ C.rep s m :=
  Iff.rfl

@[simp]
theorem toRandomized_potential {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State} (C : StateTransitionImpl D P s₀)
    (θ : Unit) (m : Mem cells w) :
    C.toRandomized.potential θ m = C.potential m :=
  rfl

@[simp]
theorem toRandomized_singleState {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State} (C : StateTransitionImpl D P s₀) :
    C.toRandomized.singleState ↔ False :=
  Iff.rfl

end Cslib.DataStructure.CellProbe.StateTransitionImpl

namespace Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl

open Cslib.CellProbe Cslib.Probability
open scoped ENNReal

universe u v

variable {cells cells' w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
  {P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w} {s₀ : D.State}

/-- Construct a `Randomized.StateTransitionImpl` on a functional specification (`[D.HasStepFn f]`),
setting `singleState := True` and reasoning over `PMF (Seed × Mem cells w)`. -/
noncomputable abbrev ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f]
    (Seed : Type) (seedLaw : PMF Seed)
    (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → Mem cells w → Prop)
    (seedSlack : ℝ≥0∞ := 1)
    (seedSlack_ne_top : seedSlack ≠ ⊤ := by simp)
    (initPotential : ℕ := 0)
    (potential : Seed → Mem cells w → ℕ := fun _ _ => 0)
    (init_exec : ∃ ν₀ : PMF (Seed × Mem cells w),
      ν₀.map Prod.snd = P.init ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ seedSlack * seedLaw θ) ∧
      ∀ p ∈ ν₀.support, rep p.1 s₀ p.2 ∧ potential p.1 p.2 ≤ initPotential)
    (step_exec : ∀ (s : D.State) (o : D.Op) (ν : PMF (Seed × Mem cells w)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2) →
      ∃ μ_step : Seed × Mem cells w → PMF (Seed × Mem cells w),
        (∀ p ∈ ν.support,
          ((P.step o).run p.2).map Prod.fst =
            (μ_step p).map (fun q => ((D.stepFn s o).2, q.2)) ∧
          ∀ q ∈ (μ_step p).support, rep q.1 (D.stepFn s o).1 q.2) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (∑' p, ν p * ((P.step o).expectedProbes p.2 +
            ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    StateTransitionImpl D P s₀ where
  Seed := Seed
  seedLaw := seedLaw
  seedSlack := seedSlack
  seedSlack_ne_top := seedSlack_ne_top
  initPotential := initPotential
  charge := charge
  rep := rep
  potential := potential
  singleState := True
  init_exec := init_exec
  step_exec o ν hsingle hseed hsupp := by
    obtain ⟨s, hs⟩ := hsingle trivial
    obtain ⟨t₀, ht₀⟩ := ν.support_nonempty
    have hv : D.valid s o := hs t₀ ht₀ ▸ (hsupp t₀ ht₀).1
    let proj : CoupledState Seed D.State cells w → Seed × Mem cells w := fun t => (t.seed, t.mem)
    let ν_det : PMF (Seed × Mem cells w) := ν.map proj
    have hseed_det : ∀ θ, (ν_det.map Prod.fst) θ ≤ seedSlack * seedLaw θ := by
      intro θ
      rw [PMF.map_comp]
      exact hseed θ
    have hsupp_det : ∀ p ∈ ν_det.support, rep p.1 s p.2 := by
      intro p hp
      rw [PMF.mem_support_map_iff] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      exact hs t ht ▸ (hsupp t ht).2
    obtain ⟨μ_det, hstep_det, hseed_det', hamort_det⟩ :=
      step_exec s o ν_det hv hseed_det hsupp_det
    let μ_step : CoupledState Seed D.State cells w →
        PMF (CoupledOutcome Seed D.State (D.Result o) cells w) :=
      fun t => (μ_det (proj t)).map fun q => ⟨q.1, (D.stepFn s o).1, q.2, (D.stepFn s o).2⟩
    refine ⟨μ_step, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have hp_det : proj t ∈ ν_det.support := (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
      obtain ⟨hmarg, hq_det⟩ := hstep_det (proj t) hp_det
      refine ⟨?_, ?_⟩
      · dsimp only [μ_step]
        rw [PMF.map_comp]
        exact hmarg
      · intro q' hq'
        dsimp only [μ_step] at hq'
        rw [PMF.mem_support_map_iff] at hq'
        obtain ⟨q, hq, rfl⟩ := hq'
        refine ⟨?_, hq_det q hq⟩
        rw [hs t ht]
        exact D.step_stepFn s o
    · intro θ'
      have hmap_eq : (ν.bind μ_step).map CoupledOutcome.seed = (ν_det.bind μ_det).map Prod.fst := by
        rw [PMF.map_bind, PMF.map_bind, PMF.bind_map]
        refine congrArg (ν.bind ·) (funext fun t => ?_)
        dsimp only [μ_step]
        rw [PMF.map_comp]
        rfl
      rw [hmap_eq]
      exact hseed_det' θ'
    · intro _
      refine ⟨(D.stepFn s o).1, fun q hq => ?_⟩
      rw [PMF.mem_support_bind_iff] at hq
      obtain ⟨t, _, hq_step⟩ := hq
      dsimp only [μ_step] at hq_step
      rw [PMF.mem_support_map_iff] at hq_step
      obtain ⟨_, _, rfl⟩ := hq_step
      rfl
    · have hPot_inner : ∀ t : CoupledState Seed D.State cells w,
          (∑' q', μ_step t q' * (potential q'.seed q'.mem : ℝ≥0∞)) =
            ∑' q, μ_det (proj t) q * (potential q.1 q.2 : ℝ≥0∞) := by
        intro t
        dsimp only [μ_step]
        rw [PMF.tsum_map_mul]
      simp_rw [hPot_inner]
      have hLHS :
          (∑' t, ν t * ((P.step o).expectedProbes t.mem +
              ∑' q, μ_det (proj t) q * (potential q.1 q.2 : ℝ≥0∞))) =
            ∑' p, ν_det p * ((P.step o).expectedProbes p.2 +
              ∑' q, μ_det p q * (potential q.1 q.2 : ℝ≥0∞)) :=
        (PMF.tsum_map_mul ν proj fun p =>
          (P.step o).expectedProbes p.2 +
            ∑' q, μ_det p q * (potential q.1 q.2 : ℝ≥0∞)).symm
      have hRHS_pot :
          (∑' p, ν_det p * (potential p.1 p.2 : ℝ≥0∞)) =
            ∑' t, ν t * (potential t.seed t.mem : ℝ≥0∞) :=
        PMF.tsum_map_mul ν proj fun p => (potential p.1 p.2 : ℝ≥0∞)
      have hRHS_charge :
          (charge s o : ℝ≥0∞) + (∑' t, ν t * (potential t.seed t.mem : ℝ≥0∞)) =
            ∑' t, ν t * ((charge t.state o : ℝ≥0∞) + (potential t.seed t.mem : ℝ≥0∞)) := by
        have hch : (charge s o : ℝ≥0∞) = ∑' t, ν t * (charge t.state o : ℝ≥0∞) := by
          calc
            (charge s o : ℝ≥0∞)
              = ∑' t, ν t * (charge s o : ℝ≥0∞) := by
                  rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
            _ = ∑' t, ν t * (charge t.state o : ℝ≥0∞) := by
                  refine tsum_congr fun t => ?_
                  by_cases ht : t ∈ ν.support
                  · rw [hs t ht]
                  · rw [(PMF.apply_eq_zero_iff _ _).mpr ht, zero_mul, zero_mul]
        rw [hch, ← tsum_add]
        simp_rw [mul_add]
      rw [hLHS, ← hRHS_charge, ← hRHS_pot]
      exact hamort_det

@[simp]
theorem ofFn_seed {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (Seed : Type) (seedLaw : PMF Seed) (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → Mem cells w → Prop) (seedSlack : ℝ≥0∞)
    (seedSlack_ne_top : seedSlack ≠ ⊤) (initPotential : ℕ)
    (potential : Seed → Mem cells w → ℕ) (init_exec)
    (step_exec : ∀ (s : D.State) (o : D.Op) (ν : PMF (Seed × Mem cells w)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2) →
      ∃ μ_step : Seed × Mem cells w → PMF (Seed × Mem cells w),
        (∀ p ∈ ν.support,
          ((P.step o).run p.2).map Prod.fst =
            (μ_step p).map (fun q => ((D.stepFn s o).2, q.2)) ∧
          ∀ q ∈ (μ_step p).support, rep q.1 (D.stepFn s o).1 q.2) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (∑' p, ν p * ((P.step o).expectedProbes p.2 +
            ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    (ofFn (P := P) (s₀ := s₀) Seed seedLaw charge rep seedSlack seedSlack_ne_top initPotential
      potential init_exec step_exec).Seed = Seed :=
  rfl

@[simp]
theorem ofFn_seedLaw {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (Seed : Type) (seedLaw : PMF Seed) (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → Mem cells w → Prop) (seedSlack : ℝ≥0∞)
    (seedSlack_ne_top : seedSlack ≠ ⊤) (initPotential : ℕ)
    (potential : Seed → Mem cells w → ℕ) (init_exec)
    (step_exec : ∀ (s : D.State) (o : D.Op) (ν : PMF (Seed × Mem cells w)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2) →
      ∃ μ_step : Seed × Mem cells w → PMF (Seed × Mem cells w),
        (∀ p ∈ ν.support,
          ((P.step o).run p.2).map Prod.fst =
            (μ_step p).map (fun q => ((D.stepFn s o).2, q.2)) ∧
          ∀ q ∈ (μ_step p).support, rep q.1 (D.stepFn s o).1 q.2) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (∑' p, ν p * ((P.step o).expectedProbes p.2 +
            ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    (ofFn (P := P) (s₀ := s₀) Seed seedLaw charge rep seedSlack seedSlack_ne_top initPotential
      potential init_exec step_exec).seedLaw = seedLaw :=
  rfl

@[simp]
theorem ofFn_seedSlack {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (Seed : Type) (seedLaw : PMF Seed) (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → Mem cells w → Prop) (seedSlack : ℝ≥0∞)
    (seedSlack_ne_top : seedSlack ≠ ⊤) (initPotential : ℕ)
    (potential : Seed → Mem cells w → ℕ) (init_exec)
    (step_exec : ∀ (s : D.State) (o : D.Op) (ν : PMF (Seed × Mem cells w)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2) →
      ∃ μ_step : Seed × Mem cells w → PMF (Seed × Mem cells w),
        (∀ p ∈ ν.support,
          ((P.step o).run p.2).map Prod.fst =
            (μ_step p).map (fun q => ((D.stepFn s o).2, q.2)) ∧
          ∀ q ∈ (μ_step p).support, rep q.1 (D.stepFn s o).1 q.2) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (∑' p, ν p * ((P.step o).expectedProbes p.2 +
            ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    (ofFn (P := P) (s₀ := s₀) Seed seedLaw charge rep seedSlack seedSlack_ne_top initPotential
      potential init_exec step_exec).seedSlack = seedSlack :=
  rfl

@[simp]
theorem ofFn_initPotential {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (Seed : Type) (seedLaw : PMF Seed) (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → Mem cells w → Prop) (seedSlack : ℝ≥0∞)
    (seedSlack_ne_top : seedSlack ≠ ⊤) (initPotential : ℕ)
    (potential : Seed → Mem cells w → ℕ) (init_exec)
    (step_exec : ∀ (s : D.State) (o : D.Op) (ν : PMF (Seed × Mem cells w)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2) →
      ∃ μ_step : Seed × Mem cells w → PMF (Seed × Mem cells w),
        (∀ p ∈ ν.support,
          ((P.step o).run p.2).map Prod.fst =
            (μ_step p).map (fun q => ((D.stepFn s o).2, q.2)) ∧
          ∀ q ∈ (μ_step p).support, rep q.1 (D.stepFn s o).1 q.2) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (∑' p, ν p * ((P.step o).expectedProbes p.2 +
            ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    (ofFn (P := P) (s₀ := s₀) Seed seedLaw charge rep seedSlack seedSlack_ne_top initPotential
      potential init_exec step_exec).initPotential = initPotential :=
  rfl

@[simp]
theorem ofFn_charge {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (Seed : Type) (seedLaw : PMF Seed) (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → Mem cells w → Prop) (seedSlack : ℝ≥0∞)
    (seedSlack_ne_top : seedSlack ≠ ⊤) (initPotential : ℕ)
    (potential : Seed → Mem cells w → ℕ) (init_exec)
    (step_exec : ∀ (s : D.State) (o : D.Op) (ν : PMF (Seed × Mem cells w)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2) →
      ∃ μ_step : Seed × Mem cells w → PMF (Seed × Mem cells w),
        (∀ p ∈ ν.support,
          ((P.step o).run p.2).map Prod.fst =
            (μ_step p).map (fun q => ((D.stepFn s o).2, q.2)) ∧
          ∀ q ∈ (μ_step p).support, rep q.1 (D.stepFn s o).1 q.2) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (∑' p, ν p * ((P.step o).expectedProbes p.2 +
            ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    (ofFn (P := P) (s₀ := s₀) Seed seedLaw charge rep seedSlack seedSlack_ne_top initPotential
      potential init_exec step_exec).charge = charge :=
  rfl

@[simp]
theorem ofFn_rep {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (Seed : Type) (seedLaw : PMF Seed) (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → Mem cells w → Prop) (seedSlack : ℝ≥0∞)
    (seedSlack_ne_top : seedSlack ≠ ⊤) (initPotential : ℕ)
    (potential : Seed → Mem cells w → ℕ) (init_exec)
    (step_exec : ∀ (s : D.State) (o : D.Op) (ν : PMF (Seed × Mem cells w)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2) →
      ∃ μ_step : Seed × Mem cells w → PMF (Seed × Mem cells w),
        (∀ p ∈ ν.support,
          ((P.step o).run p.2).map Prod.fst =
            (μ_step p).map (fun q => ((D.stepFn s o).2, q.2)) ∧
          ∀ q ∈ (μ_step p).support, rep q.1 (D.stepFn s o).1 q.2) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (∑' p, ν p * ((P.step o).expectedProbes p.2 +
            ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    (ofFn (P := P) (s₀ := s₀) Seed seedLaw charge rep seedSlack seedSlack_ne_top initPotential
      potential init_exec step_exec).rep = rep :=
  rfl

@[simp]
theorem ofFn_potential {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (Seed : Type) (seedLaw : PMF Seed) (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → Mem cells w → Prop) (seedSlack : ℝ≥0∞)
    (seedSlack_ne_top : seedSlack ≠ ⊤) (initPotential : ℕ)
    (potential : Seed → Mem cells w → ℕ) (init_exec)
    (step_exec : ∀ (s : D.State) (o : D.Op) (ν : PMF (Seed × Mem cells w)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2) →
      ∃ μ_step : Seed × Mem cells w → PMF (Seed × Mem cells w),
        (∀ p ∈ ν.support,
          ((P.step o).run p.2).map Prod.fst =
            (μ_step p).map (fun q => ((D.stepFn s o).2, q.2)) ∧
          ∀ q ∈ (μ_step p).support, rep q.1 (D.stepFn s o).1 q.2) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (∑' p, ν p * ((P.step o).expectedProbes p.2 +
            ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    (ofFn (P := P) (s₀ := s₀) Seed seedLaw charge rep seedSlack seedSlack_ne_top initPotential
      potential init_exec step_exec).potential = potential :=
  rfl

@[simp]
theorem ofFn_singleState {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (Seed : Type) (seedLaw : PMF Seed) (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → Mem cells w → Prop) (seedSlack : ℝ≥0∞)
    (seedSlack_ne_top : seedSlack ≠ ⊤) (initPotential : ℕ)
    (potential : Seed → Mem cells w → ℕ) (init_exec)
    (step_exec : ∀ (s : D.State) (o : D.Op) (ν : PMF (Seed × Mem cells w)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2) →
      ∃ μ_step : Seed × Mem cells w → PMF (Seed × Mem cells w),
        (∀ p ∈ ν.support,
          ((P.step o).run p.2).map Prod.fst =
            (μ_step p).map (fun q => ((D.stepFn s o).2, q.2)) ∧
          ∀ q ∈ (μ_step p).support, rep q.1 (D.stepFn s o).1 q.2) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (∑' p, ν p * ((P.step o).expectedProbes p.2 +
            ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    (ofFn (P := P) (s₀ := s₀) Seed seedLaw charge rep seedSlack seedSlack_ne_top initPotential
      potential init_exec step_exec).singleState ↔ True :=
  Iff.rfl

/-! ### Cell padding (`cells ≤ cells'`) -/

/-- Lift a `Randomized.StateTransitionImpl` from `cells` cells to `cells'` cells (`cells ≤ cells'`)
via `Cslib.CellProbe.Randomized.Scheme.padCells`, preserving `initPotential` and `charge`. -/
@[expose] noncomputable def padCells (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    StateTransitionImpl D (P.padCells h) s₀ where
  Seed := C.Seed
  seedLaw := C.seedLaw
  seedSlack := C.seedSlack
  seedSlack_ne_top := C.seedSlack_ne_top
  initPotential := C.initPotential
  charge := C.charge
  rep θ s m' := ∃ m : Mem cells w, m' = padMem h m ∧ C.rep θ s m
  potential θ m' := C.potential θ (fun i => m' (Fin.castLE h i))
  singleState := C.singleState
  init_exec := by
    have hunpad : ∀ m : Mem cells w, (fun i => padMem h m (Fin.castLE h i)) = m :=
      fun m => funext (padMem_castLE h m)
    obtain ⟨ν₀, hinit, hseed, hsupp⟩ := C.init_exec
    refine ⟨ν₀.map (fun p => (p.1, padMem h p.2)), ?_, ?_, ?_⟩
    · rw [PMF.map_comp, Cslib.CellProbe.Randomized.Scheme.padCells, ← hinit, PMF.map_comp]
      rfl
    · intro θ
      rw [PMF.map_comp]
      exact hseed θ
    · intro p' hp'
      rw [PMF.mem_support_map_iff] at hp'
      obtain ⟨p, hp, rfl⟩ := hp'
      obtain ⟨hrep, hpot⟩ := hsupp p hp
      rw [hunpad]
      exact ⟨⟨p.2, rfl, hrep⟩, hpot⟩
  step_exec o ν' hsingle' hseed' hsupp' := by
    let unpad : Mem cells' w → Mem cells w := fun m' i => m' (Fin.castLE h i)
    have hunpad : ∀ m : Mem cells w, unpad (padMem h m) = m :=
      fun m => funext (padMem_castLE h m)
    let unpadState : CoupledState C.Seed D.State cells' w →
        CoupledState C.Seed D.State cells w :=
      fun t' => ⟨t'.seed, t'.state, unpad t'.mem⟩
    let ν : PMF (CoupledState C.Seed D.State cells w) := ν'.map unpadState
    have hmem_eq : ∀ t' ∈ ν'.support, t'.mem = padMem h (unpad t'.mem) := by
      intro t' ht'
      obtain ⟨m, hm, _⟩ := (hsupp' t' ht').2
      rw [hm, hunpad]
    have hsingle : C.singleState → ∃ s, ∀ t ∈ ν.support, t.state = s := by
      intro hs
      obtain ⟨s, hs_eq⟩ := hsingle' hs
      refine ⟨s, fun t ht => ?_⟩
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨t', ht', rfl⟩ := ht
      exact hs_eq t' ht'
    have hseed : ∀ θ, (ν.map CoupledState.seed) θ ≤ C.seedSlack * C.seedLaw θ := by
      intro θ
      rw [PMF.map_comp]
      exact hseed' θ
    have hsupp : ∀ t ∈ ν.support, D.valid t.state o ∧ C.rep t.seed t.state t.mem := by
      intro t ht
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨t', ht', rfl⟩ := ht
      obtain ⟨hval, ⟨m, hm, hrep⟩⟩ := hsupp' t' ht'
      dsimp only [unpadState]
      rw [hm, hunpad]
      exact ⟨hval, hrep⟩
    obtain ⟨μ_step, hstep, hseed₁, hsingle₁, hamort⟩ :=
      C.step_exec o ν hsingle hseed hsupp
    let padOutcome : CoupledOutcome C.Seed D.State (D.Result o) cells w →
        CoupledOutcome C.Seed D.State (D.Result o) cells' w :=
      fun q => ⟨q.seed, q.state, padMem h q.mem, q.result⟩
    let μ_step' : CoupledState C.Seed D.State cells' w →
        PMF (CoupledOutcome C.Seed D.State (D.Result o) cells' w) :=
      fun t' => (μ_step (unpadState t')).map padOutcome
    refine ⟨μ_step', ?_, ?_, ?_, ?_⟩
    · intro t' ht'
      have ht : unpadState t' ∈ ν.support := (PMF.mem_support_map_iff _ _ _).mpr ⟨t', ht', rfl⟩
      obtain ⟨hmarg, hq_step⟩ := hstep (unpadState t') ht
      refine ⟨?_, ?_⟩
      · rw [Cslib.CellProbe.Randomized.Scheme.padCells_step, hmem_eq t' ht',
          RandProbeTree.run_padCells, PMF.map_comp]
        have hcomp :
            ((P.step o).run (unpad t'.mem)).map
              (Prod.fst ∘ fun ((a, m₁), p) => ((a, padMem h m₁), p)) =
            (((P.step o).run (unpad t'.mem)).map Prod.fst).map
              (fun (a, m₁) => (a, padMem h m₁)) := by
          rw [PMF.map_comp]
          rfl
        rw [hcomp, hmarg, PMF.map_comp]
        dsimp only [μ_step', unpadState]
        rw [PMF.map_comp]
        rfl
      · intro q' hq'
        dsimp only [μ_step'] at hq'
        rw [PMF.mem_support_map_iff] at hq'
        obtain ⟨q, hq, rfl⟩ := hq'
        obtain ⟨hdstep, hqrep⟩ := hq_step q hq
        exact ⟨hdstep, ⟨q.mem, rfl, hqrep⟩⟩
    · intro θ'
      have hmap_eq : (ν'.bind μ_step').map CoupledOutcome.seed =
          (ν.bind μ_step).map CoupledOutcome.seed := by
        dsimp only [ν, μ_step']
        rw [PMF.map_bind, PMF.map_bind, PMF.bind_map]
        refine congrArg (ν'.bind ·) (funext fun t' => ?_)
        rw [PMF.map_comp]
        rfl
      rw [hmap_eq]
      exact hseed₁ θ'
    · intro hs
      obtain ⟨s', hs'⟩ := hsingle₁ hs
      refine ⟨s', fun q' hq' => ?_⟩
      rw [PMF.mem_support_bind_iff] at hq'
      obtain ⟨t', ht', hq_map⟩ := hq'
      dsimp only [μ_step'] at hq_map
      rw [PMF.mem_support_map_iff] at hq_map
      obtain ⟨q, hq, rfl⟩ := hq_map
      refine hs' q (PMF.mem_support_bind_iff _ _ _ |>.mpr ?_)
      exact ⟨unpadState t', (PMF.mem_support_map_iff _ _ _).mpr ⟨t', ht', rfl⟩, hq⟩
    · have hLHS :
          (∑' t', ν' t' * ((((P.padCells h).step o).expectedProbes t'.mem) +
              ∑' q', μ_step' t' q' * (C.potential q'.seed (unpad q'.mem) : ℝ≥0∞))) =
            ∑' t, ν t * (((P.step o).expectedProbes t.mem) +
              ∑' q, μ_step t q * (C.potential q.seed q.mem : ℝ≥0∞)) := by
        rw [PMF.tsum_map_mul]
        refine tsum_congr fun t' => ?_
        by_cases ht' : t' ∈ ν'.support
        · refine congrArg (ν' t' * ·) ?_
          have hpr : ((P.padCells h).step o).expectedProbes t'.mem =
              (P.step o).expectedProbes (unpad t'.mem) := by
            conv_lhs =>
              rw [Cslib.CellProbe.Randomized.Scheme.padCells_step, hmem_eq t' ht',
                RandProbeTree.expectedProbes_padCells]
          have hpot :
              (∑' q', μ_step' t' q' * (C.potential q'.seed (unpad q'.mem) : ℝ≥0∞)) =
                ∑' q, μ_step (unpadState t') q * (C.potential q.seed q.mem : ℝ≥0∞) := by
            dsimp only [μ_step', padOutcome]
            rw [PMF.tsum_map_mul]
            simp only [hunpad]
          rw [hpr, hpot]
        · rw [(PMF.apply_eq_zero_iff _ _).mpr ht', zero_mul, zero_mul]
      have hRHS :
          (∑' t, ν t * ((C.charge t.state o : ℝ≥0∞) + (C.potential t.seed t.mem : ℝ≥0∞))) =
            ∑' t', ν' t' * ((C.charge t'.state o : ℝ≥0∞) +
              (C.potential t'.seed (unpad t'.mem) : ℝ≥0∞)) :=
        PMF.tsum_map_mul ν' unpadState fun t =>
          (C.charge t.state o : ℝ≥0∞) + (C.potential t.seed t.mem : ℝ≥0∞)
      rw [hLHS, ← hRHS]
      exact hamort

@[simp]
theorem padCells_seed (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    (C.padCells h).Seed = C.Seed :=
  rfl

@[simp]
theorem padCells_seedLaw (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    (C.padCells h).seedLaw = C.seedLaw :=
  rfl

@[simp]
theorem padCells_seedSlack (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    (C.padCells h).seedSlack = C.seedSlack :=
  rfl

@[simp]
theorem padCells_initPotential (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    (C.padCells h).initPotential = C.initPotential :=
  rfl

@[simp]
theorem padCells_charge (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    (C.padCells h).charge = C.charge :=
  rfl

@[simp]
theorem padCells_rep (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) (θ : C.Seed)
    (s : D.State) (m' : Mem cells' w) :
    (C.padCells h).rep θ s m' ↔ ∃ m : Mem cells w, m' = padMem h m ∧ C.rep θ s m :=
  Iff.rfl

@[simp]
theorem padCells_potential (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) (θ : C.Seed)
    (m' : Mem cells' w) :
    (C.padCells h).potential θ m' = C.potential θ (fun i => m' (Fin.castLE h i)) :=
  rfl

@[simp]
theorem padCells_singleState (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    (C.padCells h).singleState ↔ C.singleState :=
  Iff.rfl

/-! ### Sequence-level expected-amortized probe bounds and transcript contracts -/

/-- First-component `(transcript, postMem)` decomposition of `Randomized.Scheme.runFrom` on
`o :: ops`. -/
theorem runFrom_cons_fst {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    (Q : Cslib.CellProbe.Randomized.Scheme Op Result cells w)
    (m : Mem cells w) (o : Op) (ops : List Op) :
    (Q.runFrom m (o :: ops)).map Prod.fst =
      (((Q.step o).run m).map Prod.fst).bind fun (a, m') =>
        ((Q.runFrom m' ops).map Prod.fst).map fun (tr, m'') => (⟨o, a⟩ :: tr, m'') := by
  rw [Cslib.CellProbe.Randomized.Scheme.runFrom_cons, PMF.map_bind, PMF.bind_map]
  refine congrArg (PMF.bind ((Q.step o).run m)) (funext fun ((a, m'), _) => ?_)
  simp only [Function.comp_def, PMF.map_comp]

/-- First-component `(transcript, postMem)` decomposition of `Randomized.Scheme.runFrom` across
`ops₁ ++ ops₂`. -/
theorem runFrom_append_fst {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    (Q : Cslib.CellProbe.Randomized.Scheme Op Result cells w)
    (m : Mem cells w) (ops₁ ops₂ : List Op) :
    (Q.runFrom m (ops₁ ++ ops₂)).map Prod.fst =
      ((Q.runFrom m ops₁).map Prod.fst).bind fun (tr₁, m₁) =>
        ((Q.runFrom m₁ ops₂).map Prod.fst).map fun (tr₂, m₂) => (tr₁ ++ tr₂, m₂) := by
  induction ops₁ generalizing m with
  | nil =>
    simp only [List.nil_append, Cslib.CellProbe.Randomized.Scheme.runFrom_nil, PMF.pure_map,
      PMF.pure_bind]
    exact (PMF.map_id _).symm
  | cons o rest ih =>
    simp only [List.cons_append, runFrom_cons_fst Q, ih, PMF.bind_bind, PMF.map_bind]
    refine congrArg (PMF.bind (((Q.step o).run m).map Prod.fst)) (funext fun (a, m') => ?_)
    rw [PMF.bind_map ((Q.runFrom m' rest).map Prod.fst)]
    refine congrArg (PMF.bind ((Q.runFrom m' rest).map Prod.fst)) (funext fun (tr₁, m₁) => ?_)
    simp only [Function.comp_def, PMF.map_comp, List.cons_append]

/-- Stepwise expected-probe recurrence for `Randomized.Scheme.expectedProbesFrom` on `o :: ops`. -/
theorem expectedProbesFrom_cons {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    (Q : Cslib.CellProbe.Randomized.Scheme Op Result cells w)
    (m : Mem cells w) (o : Op) (ops : List Op) :
    Q.expectedProbesFrom m (o :: ops) =
      (Q.step o).expectedProbes m +
        ∑' am : Result o × Mem cells w,
          (((Q.step o).run m).map Prod.fst) am * Q.expectedProbesFrom am.2 ops := by
  rw [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom,
    Cslib.CellProbe.Randomized.Scheme.runFrom_cons,
    PMF.tsum_bind_mul, PMF.tsum_map_mul]
  have hterm : ∀ z : (Result o × Mem cells w) × ℕ,
      ((Q.step o).run m) z *
        (∑' z₂ : (List (Sigma Result) × Mem cells w) × ℕ,
          ((Q.runFrom z.1.2 ops).map (fun ((tr, m''), p₂) =>
            ((⟨o, z.1.1⟩ :: tr, m''), z.2 + p₂))) z₂ * (z₂.2 : ℝ≥0∞)) =
      ((Q.step o).run m) z * (z.2 : ℝ≥0∞) +
        ((Q.step o).run m) z * Q.expectedProbesFrom z.1.2 ops := by
    rintro ⟨⟨a, m'⟩, p₁⟩
    rw [PMF.tsum_map_mul]
    simp only [Nat.cast_add, mul_add, tsum_add, ENNReal.tsum_mul_right,
      (Q.runFrom m' ops).tsum_coe, one_mul,
      Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom]
  simp only [hterm, tsum_add]
  rfl

/-- Append decomposition for `Randomized.Scheme.expectedProbesFrom` across `ops₁ ++ ops₂`. -/
theorem expectedProbesFrom_append {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    (Q : Cslib.CellProbe.Randomized.Scheme Op Result cells w)
    (m : Mem cells w) (ops₁ ops₂ : List Op) :
    Q.expectedProbesFrom m (ops₁ ++ ops₂) =
      Q.expectedProbesFrom m ops₁ +
        ∑' tm : List (Sigma Result) × Mem cells w,
          ((Q.runFrom m ops₁).map Prod.fst) tm * Q.expectedProbesFrom tm.2 ops₂ := by
  induction ops₁ generalizing m with
  | nil =>
    simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom,
      Cslib.CellProbe.Randomized.Scheme.runFrom]
  | cons o rest ih =>
    have hpull :
        (∑' am : Result o × Mem cells w,
          (((Q.step o).run m).map Prod.fst) am * Q.expectedProbesFrom am.2 (rest ++ ops₂)) =
        (∑' am : Result o × Mem cells w,
          (((Q.step o).run m).map Prod.fst) am * Q.expectedProbesFrom am.2 rest) +
        ∑' tm : List (Sigma Result) × Mem cells w,
          ((Q.runFrom m (o :: rest)).map Prod.fst) tm * Q.expectedProbesFrom tm.2 ops₂ := by
      rw [runFrom_cons_fst Q, PMF.tsum_bind_mul]
      simp only [ih, mul_add, tsum_add, PMF.tsum_map_mul]
    rw [List.cons_append, expectedProbesFrom_cons Q m o (rest ++ ops₂),
      expectedProbesFrom_cons Q m o rest, hpull, ← add_assoc]

private theorem expectedSeqProbes_snoc {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    (Q : Cslib.CellProbe.Randomized.Scheme Op Result cells w)
    (ops : List Op) (o : Op) :
    Q.expectedSeqProbes (ops ++ [o]) =
      Q.expectedSeqProbes ops +
        ∑' tm : List (Sigma Result) × Mem cells w,
          (Q.init.bind fun m₀ => (Q.runFrom m₀ ops).map Prod.fst) tm *
            (Q.step o).expectedProbes tm.2 := by
  have hone : ∀ m₁ : Mem cells w, Q.expectedProbesFrom m₁ [o] = (Q.step o).expectedProbes m₁ := by
    intro m₁
    rw [expectedProbesFrom_cons]
    have hnil : ∀ m₂ : Mem cells w, Q.expectedProbesFrom m₂ [] = 0 := by
      intro m₂
      simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom,
        Cslib.CellProbe.Randomized.Scheme.runFrom]
    simp [hnil]
  rw [Q.expectedSeqProbes_eq_init_tsum (ops ++ [o]), Q.expectedSeqProbes_eq_init_tsum ops,
    PMF.tsum_bind_mul]
  simp only [expectedProbesFrom_append Q, hone, mul_add, tsum_add]

private def traceToCoupled {Seed : Type} (u : TraceState Seed D cells w) :
    CoupledState Seed D.State cells w :=
  ⟨u.seed, u.state, u.mem⟩

private theorem steps_trace_amortized (C : StateTransitionImpl D P s₀)
    (prefOps remOps : List D.Op)
    (ν : PMF (TraceState C.Seed D cells w))
    (hmarg : ν.map (fun u => (u.trace.labels, u.mem)) =
      P.init.bind fun m₀ => (P.runFrom m₀ prefOps).map Prod.fst)
    (hseed : ∀ θ, (ν.map TraceState.seed) θ ≤ C.seedSlack * C.seedLaw θ)
    (hsingle : C.singleState → ∃ s, ∀ u ∈ ν.support, u.state = s)
    (hsupp : ∀ u ∈ ν.support,
      u.trace.ops = prefOps ∧
      D.ValidTranscript s₀ u.trace u.state ∧
      D.ValidOpSeq u.state remOps ∧
      C.rep u.seed u.state u.mem)
    (hamort_pref :
      P.expectedSeqProbes prefOps + (∑' u, ν u * (C.potential u.seed u.mem : ℝ≥0∞)) ≤
        (C.initPotential : ℝ≥0∞) +
          ∑' u, ν u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞)) :
    ∃ ν_final : PMF (TraceState C.Seed D cells w),
      ν_final.map (fun u => (u.trace.labels, u.mem)) =
        (P.init.bind fun m₀ => (P.runFrom m₀ (prefOps ++ remOps)).map Prod.fst) ∧
      (∀ θ, (ν_final.map TraceState.seed) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      (C.singleState → ∃ s', ∀ u ∈ ν_final.support, u.state = s') ∧
      (∀ u ∈ ν_final.support,
        u.trace.ops = prefOps ++ remOps ∧
        D.ValidTranscript s₀ u.trace u.state ∧
        C.rep u.seed u.state u.mem) ∧
      P.expectedSeqProbes (prefOps ++ remOps) +
          (∑' u, ν_final u * (C.potential u.seed u.mem : ℝ≥0∞)) ≤
        (C.initPotential : ℝ≥0∞) +
          ∑' u, ν_final u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞) := by
  induction remOps generalizing prefOps ν with
  | nil =>
    refine ⟨ν, ?_, hseed, hsingle, fun u hu => ?_, ?_⟩
    · simpa only [List.append_nil] using hmarg
    · obtain ⟨hops, htr, _, hrep⟩ := hsupp u hu
      rw [List.append_nil]
      exact ⟨hops, htr, hrep⟩
    · simpa only [List.append_nil] using hamort_pref
  | cons o rest ih =>
    let ν_c : PMF (CoupledState C.Seed D.State cells w) := ν.map traceToCoupled
    have hsingle_c : C.singleState → ∃ s, ∀ t ∈ ν_c.support, t.state = s := by
      intro hs
      obtain ⟨s, hs_eq⟩ := hsingle hs
      refine ⟨s, fun t ht => ?_⟩
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      exact hs_eq u hu
    have hseed_c : ∀ θ, (ν_c.map CoupledState.seed) θ ≤ C.seedSlack * C.seedLaw θ := by
      intro θ
      rw [PMF.map_comp]
      exact hseed θ
    have hsupp_c : ∀ t ∈ ν_c.support, D.valid t.state o ∧ C.rep t.seed t.state t.mem := by
      intro t ht
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      obtain ⟨_, _, hv_u, hrep_u⟩ := hsupp u hu
      exact ⟨hv_u.1, hrep_u⟩
    obtain ⟨μ_step, hstep, hseed₁, hsingle₁, hamort₁⟩ :=
      C.step_exec o ν_c hsingle_c hseed_c hsupp_c
    let liftStep (u : TraceState C.Seed D cells w)
        (q : CoupledOutcome C.Seed D.State (D.Result o) cells w) :
        TraceState C.Seed D cells w :=
      ⟨q.seed, q.state, q.mem, u.trace ++ [⟨o, q.result, q.state⟩]⟩
    let ν₁ : PMF (TraceState C.Seed D cells w) :=
      ν.bind fun u => (μ_step (traceToCoupled u)).map (liftStep u)
    have hmarg₁ : ν₁.map (fun u => (u.trace.labels, u.mem)) =
        P.init.bind fun m₀ => (P.runFrom m₀ (prefOps ++ [o])).map Prod.fst := by
      have hrhs :
          (P.init.bind fun m₀ => (P.runFrom m₀ (prefOps ++ [o])).map Prod.fst) =
          (P.init.bind fun m₀ => (P.runFrom m₀ prefOps).map Prod.fst).bind fun (out₁, m₁) =>
            (((P.step o).run m₁).map Prod.fst).map fun (a, m₂) => (out₁ ++ [⟨o, a⟩], m₂) := by
        simp only [runFrom_append_fst P, PMF.bind_bind]
        refine congrArg (PMF.bind P.init) (funext fun m₀ => ?_)
        refine congrArg (PMF.bind ((P.runFrom m₀ prefOps).map Prod.fst))
          (funext fun (out₁, m₁) => ?_)
        rw [runFrom_cons_fst P]
        simp only [Cslib.CellProbe.Randomized.Scheme.runFrom_nil, PMF.pure_map, PMF.map_bind]
        exact PMF.bind_pure_comp _ _
      rw [hrhs, ← hmarg, PMF.bind_map]
      dsimp only [ν₁]
      rw [PMF.map_bind]
      refine PMF.bind_congr_on_support ν _ _ fun u hu => ?_
      have hc : traceToCoupled u ∈ ν_c.support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨u, hu, rfl⟩
      have hm_u := (hstep (traceToCoupled u) hc).1
      dsimp only [Function.comp_def]
      change ((μ_step (traceToCoupled u)).map (liftStep u)).map
          (fun w => (w.trace.labels, w.mem)) =
        (((P.step o).run (traceToCoupled u).mem).map Prod.fst).map
          (fun (a, m₂) => (u.trace.labels ++ [⟨o, a⟩], m₂))
      rw [hm_u, PMF.map_comp, PMF.map_comp]
      refine congrArg (PMF.map · (μ_step (traceToCoupled u))) (funext fun q => ?_)
      simp [liftStep, CoupledOutcome.resultMem]
    have hseed_ν₁ : ∀ θ, (ν₁.map TraceState.seed) θ ≤ C.seedSlack * C.seedLaw θ := by
      intro θ
      have hmap : ν₁.map TraceState.seed = (ν_c.bind μ_step).map CoupledOutcome.seed := by
        dsimp only [ν₁, ν_c]
        rw [PMF.map_bind, PMF.map_bind, PMF.bind_map]
        refine congrArg (ν.bind ·) (funext fun u => ?_)
        rw [PMF.map_comp]
        rfl
      rw [hmap]
      exact hseed₁ θ
    have hsingle_ν₁ : C.singleState → ∃ s', ∀ u ∈ ν₁.support, u.state = s' := by
      intro hs
      obtain ⟨s', hs'⟩ := hsingle₁ hs
      refine ⟨s', fun u₁ hu₁ => ?_⟩
      rw [PMF.mem_support_bind_iff] at hu₁
      obtain ⟨u, hu, hu_map⟩ := hu₁
      rw [PMF.mem_support_map_iff] at hu_map
      obtain ⟨q, hq, rfl⟩ := hu_map
      refine hs' q ((PMF.mem_support_bind_iff _ _ _).mpr ?_)
      exact ⟨traceToCoupled u, (PMF.mem_support_map_iff _ _ _).mpr ⟨u, hu, rfl⟩, hq⟩
    have hsupp_ν₁ : ∀ u₁ ∈ ν₁.support,
        u₁.trace.ops = prefOps ++ [o] ∧
        D.ValidTranscript s₀ u₁.trace u₁.state ∧
        D.ValidOpSeq u₁.state rest ∧
        C.rep u₁.seed u₁.state u₁.mem := by
      intro u₁ hu₁
      rw [PMF.mem_support_bind_iff] at hu₁
      obtain ⟨u, hu, hu_map⟩ := hu₁
      rw [PMF.mem_support_map_iff] at hu_map
      obtain ⟨q, hq, rfl⟩ := hu_map
      obtain ⟨hops_u, htr_u, hv_u, _⟩ := hsupp u hu
      have hc : traceToCoupled u ∈ ν_c.support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨u, hu, rfl⟩
      obtain ⟨hdstep, hrep_q⟩ := (hstep (traceToCoupled u) hc).2 q hq
      refine ⟨?_, ?_, hv_u.2 q.state q.result hdstep, hrep_q⟩
      · simp [liftStep, hops_u]
      · exact htr_u.append (.cons ⟨o, q.result, q.state⟩ hv_u.1 hdstep (.nil q.state))
    have hamort_ν₁ :
        P.expectedSeqProbes (prefOps ++ [o]) +
            (∑' u₁, ν₁ u₁ * (C.potential u₁.seed u₁.mem : ℝ≥0∞)) ≤
          (C.initPotential : ℝ≥0∞) +
            ∑' u₁, ν₁ u₁ * (D.totalCostTranscript C.charge s₀ u₁.trace : ℝ≥0∞) := by
      have hsnoc : P.expectedSeqProbes (prefOps ++ [o]) =
          P.expectedSeqProbes prefOps + ∑' u, ν u * (P.step o).expectedProbes u.mem := by
        rw [expectedSeqProbes_snoc P prefOps o, ← hmarg, PMF.tsum_map_mul]
      have hpot₁ :
          (∑' u₁, ν₁ u₁ * (C.potential u₁.seed u₁.mem : ℝ≥0∞)) =
            ∑' u, ν u * ∑' q, μ_step (traceToCoupled u) q * (C.potential q.seed q.mem : ℝ≥0∞) := by
        dsimp only [ν₁]
        rw [PMF.tsum_bind_mul]
        refine tsum_congr fun u => congrArg (ν u * ·) ?_
        rw [PMF.tsum_map_mul]
      have hstep_u :
          (∑' u, ν u * (P.step o).expectedProbes u.mem) +
              (∑' u₁, ν₁ u₁ * (C.potential u₁.seed u₁.mem : ℝ≥0∞)) ≤
            (∑' u, ν u * (C.charge u.state o : ℝ≥0∞)) +
              ∑' u, ν u * (C.potential u.seed u.mem : ℝ≥0∞) := by
        rw [hpot₁, ← tsum_add]
        simp_rw [← mul_add]
        have hLHS_c :
            (∑' u, ν u * ((P.step o).expectedProbes u.mem +
                ∑' q, μ_step (traceToCoupled u) q * (C.potential q.seed q.mem : ℝ≥0∞))) =
              ∑' t, ν_c t * ((P.step o).expectedProbes t.mem +
                ∑' q, μ_step t q * (C.potential q.seed q.mem : ℝ≥0∞)) :=
          (PMF.tsum_map_mul ν traceToCoupled fun t =>
            (P.step o).expectedProbes t.mem +
              ∑' q, μ_step t q * (C.potential q.seed q.mem : ℝ≥0∞)).symm
        have hRHS_c :
            (∑' t, ν_c t * ((C.charge t.state o : ℝ≥0∞) + (C.potential t.seed t.mem : ℝ≥0∞))) =
              (∑' u, ν u * (C.charge u.state o : ℝ≥0∞)) +
                ∑' u, ν u * (C.potential u.seed u.mem : ℝ≥0∞) := by
          rw [PMF.tsum_map_mul]
          simp_rw [traceToCoupled, mul_add, tsum_add]
        rw [hLHS_c, ← hRHS_c]
        exact hamort₁
      have hcost₁ :
          (∑' u₁, ν₁ u₁ * (D.totalCostTranscript C.charge s₀ u₁.trace : ℝ≥0∞)) =
            (∑' u, ν u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞)) +
              ∑' u, ν u * (C.charge u.state o : ℝ≥0∞) := by
        dsimp only [ν₁]
        rw [PMF.tsum_bind_mul]
        have hinner : ∀ u : TraceState C.Seed D cells w,
            ν u * (∑' u₁, ((μ_step (traceToCoupled u)).map (liftStep u)) u₁ *
                (D.totalCostTranscript C.charge s₀ u₁.trace : ℝ≥0∞)) =
              ν u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞) +
                ν u * (C.charge u.state o : ℝ≥0∞) := by
          intro u
          by_cases hu : u ∈ ν.support
          · rw [PMF.tsum_map_mul]
            have htr_u := (hsupp u hu).2.1
            have htot : ∀ q : CoupledOutcome C.Seed D.State (D.Result o) cells w,
                (D.totalCostTranscript C.charge s₀ (liftStep u q).trace : ℝ≥0∞) =
                  (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞) +
                    (C.charge u.state o : ℝ≥0∞) := by
              intro q
              dsimp only [liftStep]
              rw [D.totalCostTranscript_append C.charge htr_u]
              simp [Nat.cast_add]
            simp only [htot, mul_add, tsum_add, ENNReal.tsum_mul_right,
              (μ_step (traceToCoupled u)).tsum_coe, one_mul]
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hu]
            simp
        simp only [hinner, tsum_add]
      rw [hsnoc, hcost₁]
      calc
        (P.expectedSeqProbes prefOps + ∑' u, ν u * (P.step o).expectedProbes u.mem) +
            ∑' u₁, ν₁ u₁ * (C.potential u₁.seed u₁.mem : ℝ≥0∞)
          = P.expectedSeqProbes prefOps +
              ((∑' u, ν u * (P.step o).expectedProbes u.mem) +
                ∑' u₁, ν₁ u₁ * (C.potential u₁.seed u₁.mem : ℝ≥0∞)) := by ac_rfl
        _ ≤ P.expectedSeqProbes prefOps +
              ((∑' u, ν u * (C.charge u.state o : ℝ≥0∞)) +
                ∑' u, ν u * (C.potential u.seed u.mem : ℝ≥0∞)) :=
            add_le_add le_rfl hstep_u
        _ = (P.expectedSeqProbes prefOps + ∑' u, ν u * (C.potential u.seed u.mem : ℝ≥0∞)) +
              ∑' u, ν u * (C.charge u.state o : ℝ≥0∞) := by ac_rfl
        _ ≤ ((C.initPotential : ℝ≥0∞) +
              ∑' u, ν u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞)) +
              ∑' u, ν u * (C.charge u.state o : ℝ≥0∞) :=
            add_le_add hamort_pref le_rfl
        _ = (C.initPotential : ℝ≥0∞) +
              ((∑' u, ν u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞)) +
                ∑' u, ν u * (C.charge u.state o : ℝ≥0∞)) := by ac_rfl
    obtain ⟨ν_final, hmarg_f, hseed_f, hsingle_f, hsupp_f, hamort_f⟩ :=
      ih (prefOps ++ [o]) ν₁ hmarg₁ hseed_ν₁ hsingle_ν₁ hsupp_ν₁ hamort_ν₁
    rw [List.append_assoc, List.singleton_append] at hmarg_f hamort_f
    refine ⟨ν_final, hmarg_f, hseed_f, hsingle_f, fun u hu => ?_, hamort_f⟩
    obtain ⟨hops_f, htr_f, hrep_f⟩ := hsupp_f u hu
    rw [List.append_assoc, List.singleton_append] at hops_f
    exact ⟨hops_f, htr_f, hrep_f⟩

/-- **Multi-operation expected-amortized sequence theorem (`seq_expected_amortized`).**
For any demonically admissible operation sequence `D.ValidOpSeq s₀ ops`, executing `P` from
`P.init` admits a coupled transcript-and-state distribution `ν_final` whose label marginal equals
`(P.runSeq ops).map Prod.fst`, whose support elements are valid relational transcripts of `ops`
ending in represented states, and whose expected total transcript charge plus `C.initPotential`
bounds `P.expectedSeqProbes ops` plus expected final potential. -/
theorem seq_expected_amortized (C : StateTransitionImpl D P s₀)
    (ops : List D.Op) (hv : D.ValidOpSeq s₀ ops) :
    ∃ ν_final : PMF (TraceState C.Seed D cells w),
      (P.runSeq ops).map Prod.fst = ν_final.map (fun u => u.trace.labels) ∧
      (∀ θ, (ν_final.map TraceState.seed) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      (C.singleState → ∃ s', ∀ u ∈ ν_final.support, u.state = s') ∧
      (∀ u ∈ ν_final.support,
        u.trace.ops = ops ∧
        D.ValidTranscript s₀ u.trace u.state ∧
        C.rep u.seed u.state u.mem) ∧
      P.expectedSeqProbes ops + (∑' u, ν_final u * (C.potential u.seed u.mem : ℝ≥0∞)) ≤
        (C.initPotential : ℝ≥0∞) +
          ∑' u, ν_final u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞) := by
  obtain ⟨ν₀, hinit, hseed₀, hsupp₀⟩ := C.init_exec
  let ν₀_tr : PMF (TraceState C.Seed D cells w) :=
    ν₀.map fun p => ⟨p.1, s₀, p.2, []⟩
  have hmarg₀ : ν₀_tr.map (fun u => (u.trace.labels, u.mem)) =
      P.init.bind fun m₀ => (P.runFrom m₀ []).map Prod.fst := by
    dsimp only [ν₀_tr]
    rw [PMF.map_comp, ← hinit, PMF.bind_map]
    simp only [Cslib.CellProbe.Randomized.Scheme.runFrom_nil, PMF.pure_map, Function.comp_def,
      StateTransitionSpec.Transcript.labels_nil]
    exact (PMF.bind_pure_comp _ ν₀).symm
  have hseed₀_tr : ∀ θ, (ν₀_tr.map TraceState.seed) θ ≤ C.seedSlack * C.seedLaw θ := by
    intro θ
    rw [PMF.map_comp]
    exact hseed₀ θ
  have hsingle₀ : C.singleState → ∃ s, ∀ u ∈ ν₀_tr.support, u.state = s := by
    intro _
    refine ⟨s₀, fun u hu => ?_⟩
    rw [PMF.mem_support_map_iff] at hu
    obtain ⟨_, _, rfl⟩ := hu
    rfl
  have hsupp₀_tr : ∀ u ∈ ν₀_tr.support,
      u.trace.ops = [] ∧
      D.ValidTranscript s₀ u.trace u.state ∧
      D.ValidOpSeq u.state ops ∧
      C.rep u.seed u.state u.mem := by
    intro u hu
    rw [PMF.mem_support_map_iff] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    exact ⟨rfl, .nil s₀, hv, (hsupp₀ p hp).1⟩
  have hamort₀ :
      P.expectedSeqProbes [] + (∑' u, ν₀_tr u * (C.potential u.seed u.mem : ℝ≥0∞)) ≤
        (C.initPotential : ℝ≥0∞) +
          ∑' u, ν₀_tr u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞) := by
    simp only [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_nil, zero_add, ν₀_tr,
      PMF.tsum_map_mul, StateTransitionSpec.totalCostTranscript_nil, Nat.cast_zero, mul_zero,
      tsum_zero, add_zero]
    calc
      (∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞))
        ≤ ∑' p, ν₀ p * (C.initPotential : ℝ≥0∞) := by
            refine tsum_le_tsum fun p => ?_
            by_cases hp : p ∈ ν₀.support
            · exact mul_le_mul_right (Nat.cast_le.mpr (hsupp₀ p hp).2) _
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]
      _ = (C.initPotential : ℝ≥0∞) := by
            rw [ENNReal.tsum_mul_right, ν₀.tsum_coe, one_mul]
  obtain ⟨ν_final, hmarg_f, hseed_f, hsingle_f, hsupp_f, hamort_f⟩ :=
    C.steps_trace_amortized [] ops ν₀_tr hmarg₀ hseed₀_tr hsingle₀ hsupp₀_tr hamort₀
  rw [List.nil_append] at hmarg_f hamort_f
  have hrunSeq_fst : (P.runSeq ops).map Prod.fst = ν_final.map (fun u => u.trace.labels) := by
    have h1 : (P.runSeq ops).map Prod.fst =
        (P.init.bind fun m₀ => (P.runFrom m₀ ops).map Prod.fst).map Prod.fst := by
      simp only [Cslib.CellProbe.Randomized.Scheme.runSeq, PMF.map_bind, PMF.map_comp,
        Function.comp_def]
    rw [h1, ← hmarg_f, PMF.map_comp]
    rfl
  refine ⟨ν_final, hrunSeq_fst, hseed_f, hsingle_f, fun u hu => ?_, hamort_f⟩
  obtain ⟨hops, htr, hrep⟩ := hsupp_f u hu
  rw [List.nil_append] at hops
  exact ⟨hops, htr, hrep⟩

/-- Zero-error transcript correctness of `P.runSeq ops` in `D.toObliviousSequenceSpec s₀` across any
demonically admissible sequence `D.ValidOpSeq s₀ ops`. -/
theorem contract_runSeq (C : StateTransitionImpl D P s₀)
    {ops : List D.Op} (hv : D.ValidOpSeq s₀ ops) :
    (D.toObliviousSequenceSpec s₀).Contract ops ((P.runSeq ops).map Prod.fst) := by
  obtain ⟨ν_final, hlbl, _, _, hsupp, _⟩ := C.seq_expected_amortized ops hv
  intro out hout
  rw [hlbl, PMF.mem_support_map_iff] at hout
  obtain ⟨u, hu, rfl⟩ := hout
  obtain ⟨hops, htr, _⟩ := hsupp u hu
  exact ⟨u.trace, u.state, hops, rfl, htr⟩

private theorem totalCostTranscript_le_sum_map (C : StateTransitionImpl D P s₀)
    {opCharge : D.Op → ℕ}
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o)
    {s s' : D.State} {tr : D.Transcript} (htr : D.ValidTranscript s tr s') :
    D.totalCostTranscript C.charge s tr ≤ (tr.ops.map opCharge).sum := by
  induction htr with
  | nil _ => simp
  | cons st hv_o _ _ ih =>
    simp only [StateTransitionSpec.totalCostTranscript_cons,
      StateTransitionSpec.Transcript.ops_cons, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hcharge _ st.op hv_o) ih

/-- When `C.charge s o ≤ opCharge o` on admissible inputs, `P.expectedSeqProbes ops` is bounded by
`C.initPotential + (ops.map opCharge).sum` for every `ops` satisfying `D.ValidOpSeq s₀ ops`. -/
theorem expectedSeqProbes_le_of_opCharge (C : StateTransitionImpl D P s₀)
    {opCharge : D.Op → ℕ}
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o)
    {ops : List D.Op} (hv : D.ValidOpSeq s₀ ops) :
    P.expectedSeqProbes ops ≤ (C.initPotential : ℝ≥0∞) + (((ops.map opCharge).sum : ℕ) : ℝ≥0∞) := by
  obtain ⟨ν_final, _, _, _, hsupp, hamort⟩ := C.seq_expected_amortized ops hv
  calc
    P.expectedSeqProbes ops
      ≤ P.expectedSeqProbes ops + ∑' u, ν_final u * (C.potential u.seed u.mem : ℝ≥0∞) :=
        le_self_add
    _ ≤ (C.initPotential : ℝ≥0∞) +
          ∑' u, ν_final u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞) := hamort
    _ ≤ (C.initPotential : ℝ≥0∞) +
          ∑' u, ν_final u * (((ops.map opCharge).sum : ℕ) : ℝ≥0∞) := by
        refine add_le_add le_rfl (tsum_le_tsum fun u => ?_)
        by_cases hu : u ∈ ν_final.support
        · obtain ⟨hops, htr, _⟩ := hsupp u hu
          have hle := C.totalCostTranscript_le_sum_map hcharge htr
          rw [hops] at hle
          exact mul_le_mul_right (Nat.cast_le.mpr hle) _
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hu, zero_mul, zero_mul]
    _ = (C.initPotential : ℝ≥0∞) + (((ops.map opCharge).sum : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, ν_final.tsum_coe, one_mul]

/-- **Sequence-level expected-amortized theorem on deterministic specifications
(`D.HasStepFn f`).** Across any admissible history `D.ValidHistory s₀ ops`, `P.runSeq ops`
satisfies the zero-error contract `(D.toObliviousSequenceSpec s₀).Contract ops` (concentrating
every supported output trace on `(D.run s₀ ops).2`) and satisfies
`P.expectedSeqProbes ops ≤ C.initPotential + D.totalCost C.charge s₀ ops`. -/
theorem seq_expected_amortized_ofFn (C : StateTransitionImpl D P s₀)
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (ops : List D.Op) (hv : D.ValidHistory s₀ ops) :
    (D.toObliviousSequenceSpec s₀).Contract ops ((P.runSeq ops).map Prod.fst) ∧
      (∀ out ∈ ((P.runSeq ops).map Prod.fst).support, out = (D.run s₀ ops).2) ∧
      P.expectedSeqProbes ops ≤
        (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
  have hv_rel : D.ValidOpSeq s₀ ops := (D.validOpSeq_iff_validHistory s₀ ops).mpr hv
  obtain ⟨ν_final, hlbl, _, _, hsupp, hamort⟩ := C.seq_expected_amortized ops hv_rel
  have hcontract : (D.toObliviousSequenceSpec s₀).Contract ops ((P.runSeq ops).map Prod.fst) :=
    C.contract_runSeq hv_rel
  have hout : ∀ out ∈ ((P.runSeq ops).map Prod.fst).support, out = (D.run s₀ ops).2 :=
    (D.toObliviousSequenceSpec_contract_iff_of_hasStepFn s₀ hv _).mp hcontract
  refine ⟨hcontract, hout, ?_⟩
  calc
    P.expectedSeqProbes ops
      ≤ P.expectedSeqProbes ops + ∑' u, ν_final u * (C.potential u.seed u.mem : ℝ≥0∞) :=
        le_self_add
    _ ≤ (C.initPotential : ℝ≥0∞) +
          ∑' u, ν_final u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞) := hamort
    _ = (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
        congr 1
        calc
          (∑' u, ν_final u * (D.totalCostTranscript C.charge s₀ u.trace : ℝ≥0∞))
            = ∑' u, ν_final u * (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
                refine tsum_congr fun u => ?_
                by_cases hu : u ∈ ν_final.support
                · obtain ⟨hops, htr, _⟩ := hsupp u hu
                  obtain ⟨_, _, htr_eq⟩ := (D.validTranscript_iff_run s₀ u.trace u.state).mp htr
                  rw [htr_eq, hops, D.totalCostTranscript_canonicalTranscript]
                · rw [(PMF.apply_eq_zero_iff _ _).mpr hu, zero_mul, zero_mul]
          _ = (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
                rw [ENNReal.tsum_mul_right, ν_final.tsum_coe, one_mul]

/-- Expected sequence probes of `P` across any admissible history `D.ValidHistory s₀ ops` on a
deterministic specification (`[D.HasStepFn f]`) is at most
`C.initPotential + D.totalCost C.charge s₀ ops`. -/
theorem expectedSeqProbes_le_ofFn (C : StateTransitionImpl D P s₀)
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (ops : List D.Op) (hv : D.ValidHistory s₀ ops) :
    P.expectedSeqProbes ops ≤
      (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) :=
  (C.seq_expected_amortized_ofFn ops hv).2.2

end Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl
