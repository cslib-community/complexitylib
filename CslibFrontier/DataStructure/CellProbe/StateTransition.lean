/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.Defs
public import CslibFrontier.DataStructure.StateTransition.Amortized

/-!
# Deterministic Cell-Probe State-Transition Implementations

This file connects deterministic adaptive cell-probe schemes (`Cslib.CellProbe.Scheme`,
[Miltersen1999], §1.2) to the general relational data-structure specification hierarchy
(`Cslib.DataStructure.StateTransitionSpec`, [CLRS2009], Section 17.3).

A `Cslib.DataStructure.CellProbe.StateTransitionImpl D P s₀` certifies that a time-invariant
cell-probe scheme `P : Cslib.CellProbe.Scheme D.Op D.Result cells w` implements `D` starting from
abstract initial state `s₀` in `cells` cells of `w`-bit words (`cells * w` bits total, with no
persistent registers across operations), with nonnegative integer potential `potential` and
amortized per-operation probe charge `charge`.

From a single `StateTransitionImpl`, this file derives:
* Projections to `Cslib.DataStructure.StateTransitionImpl`, `Cslib.DataStructure.Amortized`, and
  (when `potential` is identically zero) `Cslib.DataStructure.Bound` over `ExecOp P`, inheriting
  all adaptive-client (`D.Client α`) soundness and potential-telescoping theorems;
* Multi-operation sequence theorems connecting `P.runSeq ops` and `P.seqProbes ops` directly to
  `D.ValidTranscript` (and `D.run s₀ ops` / `D.totalCost` on deterministic specifications
  `[D.HasStepFn f]`);
* Cell-space monotonicity `StateTransitionImpl.padCells` (`cells ≤ cells'`).

## Main definitions

* `Cslib.DataStructure.CellProbe.OperationTrace`: native single-operation cell-probe trace
  recording `probes` and `probedCells`.
* `Cslib.DataStructure.CellProbe.ExecOp`: native `DataStructure.Execution` semantics of a
  deterministic `Cslib.CellProbe.Scheme`.
* `Cslib.DataStructure.CellProbe.StateTransitionImpl`: certified deterministic cell-probe
  implementation of `D : StateTransitionSpec` from initial state `s₀`.
* `Cslib.DataStructure.CellProbe.StateTransitionImpl.ofFn`: constructor for deterministic
  specifications (`[D.HasStepFn f]`).
* `Cslib.DataStructure.CellProbe.StateTransitionImpl.toBaseImpl`: projection to
  `Cslib.DataStructure.StateTransitionImpl D (ExecOp P)`.
* `Cslib.DataStructure.CellProbe.StateTransitionImpl.padCells`: lift an implementation from
  `cells` to `cells'` cells (`cells ≤ cells'`) via `Cslib.CellProbe.Scheme.padCells`.

## Main results

* `Cslib.DataStructure.CellProbe.execOp_run`, `Cslib.DataStructure.CellProbe.ExecOp.eq_of_execOp`,
  `Cslib.DataStructure.CellProbe.ExecOp.card_probedCells_le_probes`: totality, determinism, and
  probed-cell cardinality bound for `ExecOp`.
* `Cslib.DataStructure.CellProbe.StateTransitionImpl.toAmortized`,
  `Cslib.DataStructure.CellProbe.StateTransitionImpl.toBound`: projections to
  `DataStructure.Amortized` and `DataStructure.Bound`.
* `Cslib.DataStructure.CellProbe.StateTransitionImpl.run_client_demonic_amortized`,
  `Cslib.DataStructure.CellProbe.StateTransitionImpl.run_client_amortized`,
  `Cslib.DataStructure.CellProbe.StateTransitionImpl.run_client_bound`: adaptive-client probe bounds
  from `P.init`.
* `Cslib.DataStructure.CellProbe.StateTransitionImpl.runFrom_amortized`,
  `Cslib.DataStructure.CellProbe.StateTransitionImpl.runSeq_amortized`,
  `Cslib.DataStructure.CellProbe.StateTransitionImpl.runSeq_ofFn`,
  `Cslib.DataStructure.CellProbe.StateTransitionImpl.seqProbes_le_ofFn`: multi-operation sequence
  correctness and amortized probe bounds on `P.runFrom`, `P.runSeq`, and `P.seqProbes`.

## References

* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 17.3][CLRS2009]
-/

public section

namespace Cslib.DataStructure.CellProbe

open Cslib.CellProbe

universe u v

/-! ### Native single-operation execution evidence -/

/-- Native execution evidence of a single deterministic cell-probe operation: the number of probes
incurred and the finite set of distinct cells accessed. -/
structure OperationTrace (cells : ℕ) : Type where
  /-- Number of cell reads and writes executed during the operation. -/
  probes : ℕ
  /-- Set of distinct cell indices accessed during the operation. -/
  probedCells : Finset (Fin cells)
  deriving DecidableEq

/-- Native `Cslib.DataStructure.Execution` semantics of a deterministic cell-probe `Scheme`. -/
@[expose] def ExecOp {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    (P : Scheme Op Result cells w) :
    DataStructure.Execution ⟨Op, Result⟩ (Mem cells w) (OperationTrace cells) :=
  fun m o a m' tr =>
    (P.step o).run m = (a, m') ∧
      tr.probes = (P.step o).probes m ∧
      tr.probedCells = (P.step o).probedCells m

/-- Every memory `m` and operation `o` admits a canonical `ExecOp` step of `P`. -/
theorem execOp_run {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    (P : Scheme Op Result cells w) (m : Mem cells w) (o : Op) :
    ExecOp P m o ((P.step o).run m).1 ((P.step o).run m).2
      ⟨(P.step o).probes m, (P.step o).probedCells m⟩ :=
  ⟨Prod.eta ((P.step o).run m), rfl, rfl⟩

/-- `ExecOp P` is deterministic: its answer, post-memory, and trace are uniquely determined by
`(P.step o)` and `m`. -/
theorem ExecOp.eq_of_execOp {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    {P : Scheme Op Result cells w} {m m' : Mem cells w} {o : Op} {a : Result o}
    {tr : OperationTrace cells} (he : ExecOp P m o a m' tr) :
    a = ((P.step o).run m).1 ∧
      m' = ((P.step o).run m).2 ∧
      tr = ⟨(P.step o).probes m, (P.step o).probedCells m⟩ := by
  obtain ⟨hrun, hpr, hcells⟩ := he
  cases tr
  simp only [OperationTrace.mk.injEq] at hpr hcells ⊢
  exact ⟨(congrArg Prod.fst hrun).symm, (congrArg Prod.snd hrun).symm, hpr, hcells⟩

/-- On any `ExecOp P` step, the number of distinct probed cells is at most `tr.probes`. -/
theorem ExecOp.card_probedCells_le_probes {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    {P : Scheme Op Result cells w} {m m' : Mem cells w} {o : Op} {a : Result o}
    {tr : OperationTrace cells} (he : ExecOp P m o a m' tr) :
    tr.probedCells.card ≤ tr.probes := by
  rw [he.2.1, he.2.2]
  exact (P.step o).card_probedCells_le_probes m

/-! ### Deterministic cell-probe `StateTransitionImpl` -/

/-- Certified deterministic cell-probe implementation of `D : StateTransitionSpec` from initial
state `s₀` using `cells` cells of `w`-bit words (`cells * w` bits total) with nonnegative potential
`potential` and per-operation amortized probe charge `charge`. -/
structure StateTransitionImpl {cells w : ℕ}
    (D : StateTransitionSpec.{u, v, 0})
    (P : Scheme D.Op D.Result cells w) (s₀ : D.State) where
  /-- Representation invariant linking abstract states of `D` to concrete `Mem cells w` states. -/
  rep : D.State → Mem cells w → Prop
  /-- Nonnegative integer potential on cell memories (`0` when worst-case / unamortized). -/
  potential : Mem cells w → ℕ := fun _ => 0
  /-- Upper bound on initial potential at `P.init` (`0` when unamortized). -/
  initPotential : ℕ := 0
  /-- Per-operation amortized probe charge. -/
  charge : D.State → D.Op → ℕ
  /-- Initial cell memory `P.init` represents `s₀`. -/
  init_rep : rep s₀ P.init
  /-- Potential at `P.init` is bounded by `initPotential`. -/
  init_potential : potential P.init ≤ initPotential := by simp
  /-- Angelic step correctness and potential-amortized probe bound for every admissible `o`. -/
  step_exec : ∀ {s : D.State} {m : Mem cells w} (o : D.Op),
    rep s m → D.valid s o →
    ∃ s' : D.State,
      D.step s o s' ((P.step o).run m).1 ∧
      rep s' ((P.step o).run m).2 ∧
      (P.step o).probes m + potential ((P.step o).run m).2 ≤ charge s o + potential m

namespace StateTransitionImpl

variable {cells cells' w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
  {P : Scheme D.Op D.Result cells w} {s₀ : D.State}

/-- Construct a deterministic cell-probe `StateTransitionImpl` on a functional specification
(`D.HasStepFn f`) from a functional step-correctness and amortized probe proof. -/
abbrev ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (rep : D.State → Mem cells w → Prop)
    (charge : D.State → D.Op → ℕ)
    (init_rep : rep s₀ P.init)
    (potential : Mem cells w → ℕ := fun _ => 0)
    (initPotential : ℕ := 0)
    (init_potential : potential P.init ≤ initPotential := by simp)
    (step_exec : ∀ (s : D.State) (m : Mem cells w) (o : D.Op),
      rep s m → D.valid s o →
      ((P.step o).run m).1 = (D.stepFn s o).2 ∧
      rep (D.stepFn s o).1 ((P.step o).run m).2 ∧
      (P.step o).probes m + potential ((P.step o).run m).2 ≤ charge s o + potential m) :
    StateTransitionImpl D P s₀ where
  rep := rep
  potential := potential
  initPotential := initPotential
  charge := charge
  init_rep := init_rep
  init_potential := init_potential
  step_exec {s m} o hr hv := by
    obtain ⟨ha, hr', hpr⟩ := step_exec s m o hr hv
    refine ⟨(D.stepFn s o).1, ?_, hr', hpr⟩
    rw [ha]
    exact D.step_stepFn s o

@[simp]
theorem ofFn_rep {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (rep : D.State → Mem cells w → Prop) (charge : D.State → D.Op → ℕ)
    (init_rep : rep s₀ P.init) (potential : Mem cells w → ℕ) (initPotential : ℕ)
    (init_potential : potential P.init ≤ initPotential)
    (step_exec : ∀ (s : D.State) (m : Mem cells w) (o : D.Op),
      rep s m → D.valid s o →
      ((P.step o).run m).1 = (D.stepFn s o).2 ∧
      rep (D.stepFn s o).1 ((P.step o).run m).2 ∧
      (P.step o).probes m + potential ((P.step o).run m).2 ≤ charge s o + potential m) :
    (ofFn (P := P) (s₀ := s₀) rep charge init_rep potential initPotential init_potential
      step_exec).rep = rep :=
  rfl

@[simp]
theorem ofFn_potential {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (rep : D.State → Mem cells w → Prop) (charge : D.State → D.Op → ℕ)
    (init_rep : rep s₀ P.init) (potential : Mem cells w → ℕ) (initPotential : ℕ)
    (init_potential : potential P.init ≤ initPotential)
    (step_exec : ∀ (s : D.State) (m : Mem cells w) (o : D.Op),
      rep s m → D.valid s o →
      ((P.step o).run m).1 = (D.stepFn s o).2 ∧
      rep (D.stepFn s o).1 ((P.step o).run m).2 ∧
      (P.step o).probes m + potential ((P.step o).run m).2 ≤ charge s o + potential m) :
    (ofFn (P := P) (s₀ := s₀) rep charge init_rep potential initPotential init_potential
      step_exec).potential = potential :=
  rfl

@[simp]
theorem ofFn_initPotential {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (rep : D.State → Mem cells w → Prop) (charge : D.State → D.Op → ℕ)
    (init_rep : rep s₀ P.init) (potential : Mem cells w → ℕ) (initPotential : ℕ)
    (init_potential : potential P.init ≤ initPotential)
    (step_exec : ∀ (s : D.State) (m : Mem cells w) (o : D.Op),
      rep s m → D.valid s o →
      ((P.step o).run m).1 = (D.stepFn s o).2 ∧
      rep (D.stepFn s o).1 ((P.step o).run m).2 ∧
      (P.step o).probes m + potential ((P.step o).run m).2 ≤ charge s o + potential m) :
    (ofFn (P := P) (s₀ := s₀) rep charge init_rep potential initPotential init_potential
      step_exec).initPotential = initPotential :=
  rfl

@[simp]
theorem ofFn_charge {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (rep : D.State → Mem cells w → Prop) (charge : D.State → D.Op → ℕ)
    (init_rep : rep s₀ P.init) (potential : Mem cells w → ℕ) (initPotential : ℕ)
    (init_potential : potential P.init ≤ initPotential)
    (step_exec : ∀ (s : D.State) (m : Mem cells w) (o : D.Op),
      rep s m → D.valid s o →
      ((P.step o).run m).1 = (D.stepFn s o).2 ∧
      rep (D.stepFn s o).1 ((P.step o).run m).2 ∧
      (P.step o).probes m + potential ((P.step o).run m).2 ≤ charge s o + potential m) :
    (ofFn (P := P) (s₀ := s₀) rep charge init_rep potential initPotential init_potential
      step_exec).charge = charge :=
  rfl

/-- Project a cell-probe `StateTransitionImpl` to the backend-agnostic
`Cslib.DataStructure.StateTransitionImpl D (ExecOp P)`. -/
@[expose] def toBaseImpl (C : StateTransitionImpl D P s₀) :
    DataStructure.StateTransitionImpl D (ExecOp P) where
  rep := C.rep
  total o _ _ := ⟨_, _, _, execOp_run P _ o⟩
  correct {s m o a m' tr} hr hv he := by
    obtain ⟨ha, hm', _⟩ := he.eq_of_execOp
    subst ha hm'
    obtain ⟨s', hstep, hr', _⟩ := C.step_exec o hr hv
    exact ⟨s', hstep, hr'⟩

@[simp]
theorem toBaseImpl_rep (C : StateTransitionImpl D P s₀) :
    C.toBaseImpl.rep = C.rep := by
  rfl

/-- Project a cell-probe `StateTransitionImpl` to `Cslib.DataStructure.Amortized` with probe count
weight `OperationTrace.probes`. -/
theorem toAmortized (C : StateTransitionImpl D P s₀) :
    DataStructure.Amortized C.toBaseImpl OperationTrace.probes
      (fun _ m => C.potential m) C.charge where
  step {s m o a m' tr} hr hv he := by
    obtain ⟨ha, hm', htr⟩ := he.eq_of_execOp
    subst ha hm' htr
    exact C.step_exec o hr hv

/-- When `C.potential` is identically zero, `StateTransitionImpl` projects directly to a worst-case
per-operation `Cslib.DataStructure.Bound` certificate. -/
theorem toBound (C : StateTransitionImpl D P s₀)
    (hpot : ∀ m, C.potential m = 0 := by intro _; first | rfl | simp) :
    DataStructure.Bound C.toBaseImpl OperationTrace.probes C.charge := by
  intro s m o a m' tr hr hv he
  obtain ⟨_, _, _, h⟩ := C.toAmortized.step hr hv he
  simp only [hpot] at h
  omega

/-! ### Adaptive-client and multi-operation sequence theorems -/

/-- Adaptive-client amortized probe bound from `P.init` along any demonically admissible client
`p : D.Client α`. -/
theorem run_client_demonic_amortized (C : StateTransitionImpl D P s₀)
    {α : Type*} (p : D.Client α) (hv : D.DemonicValid s₀ p) :
    ∃ a m' traces s' tr,
      DataStructure.Executes (ExecOp P) p P.init a m' traces ∧
      D.ClientRun s₀ p a s' tr ∧
      C.rep s' m' ∧
      traces.length = tr.length ∧
      DataStructure.total OperationTrace.probes traces + C.potential m' ≤
        C.initPotential + D.totalCostTranscript C.charge s₀ tr := by
  obtain ⟨a, m', traces, s', tr, he, hrun, hr', hlen, hpot⟩ :=
    C.toAmortized.exists_demonic p C.init_rep hv
  have hinit := C.init_potential
  exact ⟨a, m', traces, s', tr, he, hrun, hr', hlen, by omega⟩

/-- Adaptive-client amortized probe bound from `P.init` on a deterministic specification
(`D.HasStepFn f`). -/
theorem run_client_amortized (C : StateTransitionImpl D P s₀)
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {α : Type*} (p : D.Client α) (hv : D.ValidHistory s₀ (D.clientHistory s₀ p)) :
    ∃ m' traces,
      DataStructure.Executes (ExecOp P) p P.init (D.clientResult s₀ p) m' traces ∧
      C.rep (D.clientState s₀ p) m' ∧
      DataStructure.total OperationTrace.probes traces + C.potential m' ≤
        C.initPotential + D.totalCost C.charge s₀ (D.clientHistory s₀ p) := by
  obtain ⟨m', traces, he, hr', hpot⟩ := C.toAmortized.exists_executes p C.init_rep hv
  have hinit := C.init_potential
  exact ⟨m', traces, he, hr', by omega⟩

/-- Adaptive-client worst-case probe bound from `P.init` on a deterministic specification when
`C.potential` is identically zero. -/
theorem run_client_bound (C : StateTransitionImpl D P s₀)
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {α : Type*} (p : D.Client α) (hv : D.ValidHistory s₀ (D.clientHistory s₀ p))
    (hpot : ∀ m, C.potential m = 0 := by intro _; first | rfl | simp) :
    ∃ m' traces,
      DataStructure.Executes (ExecOp P) p P.init (D.clientResult s₀ p) m' traces ∧
      C.rep (D.clientState s₀ p) m' ∧
      DataStructure.total OperationTrace.probes traces ≤
        D.totalCost C.charge s₀ (D.clientHistory s₀ p) :=
  DataStructure.Bound.exists_executes (C.toBound hpot) p C.init_rep hv

/-- Multi-operation execution of `P.runFrom m ops` from any represented memory `m`: every
demonically admissible sequence `ops` witnesses a valid relational transcript `tr` whose labels
equal `(P.runFrom m ops).1` and whose total charge bounds `P.probesFrom m ops` up to potential. -/
theorem runFrom_amortized (C : StateTransitionImpl D P s₀)
    {s : D.State} {m : Mem cells w} (ops : List D.Op)
    (hr : C.rep s m) (hv : D.ValidOpSeq s ops) :
    ∃ (tr : D.Transcript) (s' : D.State),
      tr.ops = ops ∧
      tr.labels = (P.runFrom m ops).1 ∧
      D.ValidTranscript s tr s' ∧
      C.rep s' (P.runFrom m ops).2 ∧
      P.probesFrom m ops + C.potential (P.runFrom m ops).2 ≤
        D.totalCostTranscript C.charge s tr + C.potential m := by
  induction ops generalizing s m with
  | nil =>
    exact ⟨[], s, rfl, rfl, .nil s, hr, Nat.le_refl _⟩
  | cons o rest ih =>
    obtain ⟨hv_o, hv_rest⟩ := hv
    obtain ⟨s₁, hstep, hr₁, hpot₁⟩ := C.step_exec o hr hv_o
    obtain ⟨tr_rest, s₂, hops_rest, hlbl_rest, htr_rest, hr₂, hpot₂⟩ :=
      ih hr₁ (hv_rest s₁ ((P.step o).run m).1 hstep)
    refine ⟨⟨o, ((P.step o).run m).1, s₁⟩ :: tr_rest, s₂,
      congrArg (o :: ·) hops_rest, ?_,
      .cons _ hv_o hstep htr_rest, ?_, ?_⟩
    · simp only [Scheme.runFrom_cons, StateTransitionSpec.Transcript.labels_cons, hlbl_rest]
    · simpa only [Scheme.runFrom_cons] using hr₂
    · simp only [Scheme.probesFrom_cons, Scheme.runFrom_cons,
        StateTransitionSpec.totalCostTranscript_cons]
      omega

/-- Multi-operation execution of `P.runSeq ops` from `P.init`: every demonically admissible
sequence `D.ValidOpSeq s₀ ops` produces a valid relational transcript `tr` matching
`(P.runSeq ops).1` with `P.seqProbes ops + C.potential (P.runSeq ops).2 ≤
C.initPotential + D.totalCostTranscript C.charge s₀ tr`. -/
theorem runSeq_amortized (C : StateTransitionImpl D P s₀)
    (ops : List D.Op) (hv : D.ValidOpSeq s₀ ops) :
    ∃ (tr : D.Transcript) (s' : D.State),
      tr.ops = ops ∧
      tr.labels = (P.runSeq ops).1 ∧
      D.ValidTranscript s₀ tr s' ∧
      C.rep s' (P.runSeq ops).2 ∧
      P.seqProbes ops + C.potential (P.runSeq ops).2 ≤
        C.initPotential + D.totalCostTranscript C.charge s₀ tr := by
  obtain ⟨tr, s', hops, hlbl, htr, hr', hpot⟩ := C.runFrom_amortized ops C.init_rep hv
  have hrun : P.runFrom P.init ops = P.runSeq ops := rfl
  have hpr : P.probesFrom P.init ops = P.seqProbes ops := rfl
  rw [hrun] at hlbl hr' hpot
  rw [hpr] at hpot
  have hinit := C.init_potential
  exact ⟨tr, s', hops, hlbl, htr, hr', by omega⟩

/-- On a deterministic specification (`D.HasStepFn f`), `P.runSeq ops` on any admissible history
`D.ValidHistory s₀ ops` produces the exact canonical transcript `(D.run s₀ ops).2`, reaches a
memory representing `(D.run s₀ ops).1`, and satisfies
`P.seqProbes ops + C.potential (P.runSeq ops).2 ≤ C.initPotential + D.totalCost C.charge s₀ ops`. -/
theorem runSeq_ofFn (C : StateTransitionImpl D P s₀)
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (ops : List D.Op) (hv : D.ValidHistory s₀ ops) :
    (P.runSeq ops).1 = (D.run s₀ ops).2 ∧
      C.rep (D.run s₀ ops).1 (P.runSeq ops).2 ∧
      P.seqProbes ops + C.potential (P.runSeq ops).2 ≤
        C.initPotential + D.totalCost C.charge s₀ ops := by
  obtain ⟨tr, s', hops, hlbl, htr, hr', hpot⟩ :=
    C.runSeq_amortized ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr hv)
  obtain ⟨_, hs', htr_eq⟩ := (D.validTranscript_iff_run s₀ tr s').mp htr
  subst hs'
  rw [hops] at htr_eq hr'
  rw [htr_eq, D.canonicalTranscript_labels] at hlbl
  rw [htr_eq, D.totalCostTranscript_canonicalTranscript] at hpot
  exact ⟨hlbl.symm, hr', hpot⟩

/-- Total cell probes `P.seqProbes ops` across any admissible history `D.ValidHistory s₀ ops` on a
deterministic specification is at most `C.initPotential + D.totalCost C.charge s₀ ops`. -/
theorem seqProbes_le_ofFn (C : StateTransitionImpl D P s₀)
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (ops : List D.Op) (hv : D.ValidHistory s₀ ops) :
    P.seqProbes ops ≤ C.initPotential + D.totalCost C.charge s₀ ops :=
  Nat.le_of_add_right_le (C.runSeq_ofFn ops hv).2.2

/-! ### Cell padding (`cells ≤ cells'`) -/

/-- Lift a deterministic cell-probe `StateTransitionImpl` from `cells` cells to `cells'` cells
(`cells ≤ cells'`) via `Cslib.CellProbe.Scheme.padCells`, preserving `initPotential` and `charge`.
-/
@[expose] def padCells (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    StateTransitionImpl D (P.padCells h) s₀ where
  rep s m' := ∃ m : Mem cells w, m' = padMem h m ∧ C.rep s m
  potential m' := C.potential (fun i => m' (Fin.castLE h i))
  initPotential := C.initPotential
  charge := C.charge
  init_rep := ⟨P.init, rfl, C.init_rep⟩
  init_potential := by
    have hunpad : (fun i => padMem h P.init (Fin.castLE h i)) = P.init :=
      funext (padMem_castLE h P.init)
    change C.potential (fun i => padMem h P.init (Fin.castLE h i)) ≤ C.initPotential
    rw [hunpad]
    exact C.init_potential
  step_exec {s m'} o hr hv := by
    obtain ⟨m, rfl, hrm⟩ := hr
    obtain ⟨s', hstep, hr', hpot⟩ := C.step_exec o hrm hv
    have hunpad : ∀ m₁ : Mem cells w, (fun i => padMem h m₁ (Fin.castLE h i)) = m₁ :=
      fun m₁ => funext (padMem_castLE h m₁)
    refine ⟨s', ?_, ?_, ?_⟩
    · simpa only [Scheme.padCells, ProbeTree.run_padCells] using hstep
    · refine ⟨((P.step o).run m).2, ?_, hr'⟩
      simp only [Scheme.padCells, ProbeTree.run_padCells]
    · simp only [Scheme.padCells, ProbeTree.probes_padCells, ProbeTree.run_padCells, hunpad]
      exact hpot

@[simp]
theorem padCells_rep (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) (s : D.State)
    (m' : Mem cells' w) :
    (C.padCells h).rep s m' ↔ ∃ m : Mem cells w, m' = padMem h m ∧ C.rep s m :=
  Iff.rfl

@[simp]
theorem padCells_potential (h : cells ≤ cells') (C : StateTransitionImpl D P s₀)
    (m' : Mem cells' w) :
    (C.padCells h).potential m' = C.potential (fun i => m' (Fin.castLE h i)) :=
  rfl

@[simp]
theorem padCells_initPotential (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    (C.padCells h).initPotential = C.initPotential :=
  rfl

@[simp]
theorem padCells_charge (h : cells ≤ cells') (C : StateTransitionImpl D P s₀) :
    (C.padCells h).charge = C.charge :=
  rfl

end StateTransitionImpl

end Cslib.DataStructure.CellProbe
