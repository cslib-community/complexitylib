/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Subroutine
public import Complexity.DataStructure.StateTransition.Amortized

/-!
# Deterministic Word-RAM state-transition implementations

This file defines `Cslib.DataStructure.WordRAM.StateTransitionImpl`, the unified standalone and
inline Word-RAM subroutine implementation and resource certificate for a relational state-transition
specification `D : Cslib.DataStructure.StateTransitionSpec`.

A data structure is packaged once as a `Cslib.WordRAM.SubroutineCode B r_ds k_init` and certified by
a `StateTransitionImpl` bundle extending `Cslib.WordRAM.SubroutineBase`. From that single proof,
this file derives:

1. **Defined-evaluation basis lifting (`StateTransitionImpl.mapSimulates`,
   `StateTransitionImpl.toStandard`):** Non-faulting executions over `Basis.exact` lift
   instruction-for-instruction to `Basis.standard` via `Basis.Simulates.exactStandard`.
2. **Standalone `DataStructure` projections:** `toDynamicProgram`, `toCertificate`, `toAmortized`,
   `toBound`, and adaptive-client corollaries (`run_client_demonic_amortized`,
   `run_client_demonic_bound`, `run_client_amortized`, `run_client_bound`).
3. **Relocated inline calls (`code_rename`, `call_rename`, `code_rename_ofFn`,
   `call_rename_ofFn`):** Inline execution on caller state space `Data r_caller` with amortized
   potential accounting and DS-to-caller `Modifies` framing.
4. **Flat-program operation-sequence execution (`RunsOps`, `run_ops_exact_fresh`,
   `run_ops_exact_reusable`):** Standalone flat-program sequence theorems over `P.initFreshProg`,
   `P.initClearProg`, and `P.opProg`.

## Main definitions

* `Cslib.DataStructure.WordRAM.StateTransitionImpl`: unified standalone and inline Word-RAM
  implementation and resource certificate for `D : StateTransitionSpec`.
* `Cslib.DataStructure.WordRAM.StateTransitionImpl.ofFn`: constructor for deterministic
  specifications (`[D.HasStepFn f]`).
* `Cslib.DataStructure.WordRAM.StateTransitionImpl.toCertificate`: standalone `.standard`-basis
  `DynamicCertificate` projection.
* `Cslib.DataStructure.WordRAM.StateTransitionImpl.RunsOps`: sequential flat-program operation
  execution relation.

## Main results

* `Cslib.DataStructure.WordRAM.StateTransitionImpl.toAmortized`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.toBound`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.run_client_amortized`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.run_client_bound`: standalone amortized and
  worst-case instruction bounds over `Basis.standard`.
* `Cslib.DataStructure.WordRAM.StateTransitionImpl.code_rename`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.call_rename`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.code_rename_ofFn`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.call_rename_ofFn`: relocated inline subroutine
  calls.
* `Cslib.DataStructure.WordRAM.StateTransitionImpl.run_ops_exact_fresh`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.run_ops_exact_reusable`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.run_ops_exact_fresh_ofFn`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.run_ops_exact_reusable_ofFn`: standalone
  flat-program operation-sequence theorems.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 17][CLRS2009]
* [J. C. Reynolds, *Separation Logic: A Logic for Shared Mutable Data Structures*][Reynolds2002]
-/

@[expose] public section

namespace Cslib.DataStructure.WordRAM

open Cslib.WordRAM

universe u v z

/-- Unified standalone and subroutine specification/resource certificate for
`P : SubroutineCode B r_ds k_init` implementing a relational specification
`D : StateTransitionSpec` at word width `w`, base address `base`, runtime parameters `params`, and
initial state `s₀`.

Extends `SubroutineBase P D.Result D.valid w base params s₀` (inheriting `toDynamicProgram`,
`initFresh_exec`, `initFresh_rename`, `initClear_exec`, `initClear_rename`,
`frame_caller`, and `prepareRegs`), and existentially quantifies over a permitted outcome
`(s', a)` satisfying `D.step s o s' a` in `step_exec`. -/
structure StateTransitionImpl {B : Basis} {r_ds k_init : ℕ} (P : SubroutineCode B r_ds k_init)
    (D : StateTransitionSpec.{u, v, z}) (w base : ℕ) (params : Fin k_init → ℕ) (s₀ : D.State)
    extends SubroutineBase P D.Result D.valid w base params s₀ where
  /-- Angelic execution of `P.code` for any admissible operation `o` whose arguments match `x.regs`,
  witnessing some permitted outcome `(s', a)` with `D.step s o s' a`. -/
  step_exec : ∀ {s : D.State} {x : Data r_ds} (o : D.Op),
    rep s x → D.valid s o → argMatch o x.regs →
    ∃ y s' a n, Exec w P.code x y n ∧
      D.step s o s' a ∧
      decode o y.regs = some a ∧
      rep s' y ∧
      Modifies (Block.mk base space).footprint x.mem y.mem ∧
      n + potential y ≤ charge s o + potential x

namespace StateTransitionImpl

variable {B B' : Basis} {r_ds r_caller k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Construct a `StateTransitionImpl` for a deterministic specification (`[D.HasStepFn f]`) from a
functional `step_exec` proof at `(D.stepFn s o)`. -/
abbrev ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (space spanTime setupTime initPotential : ℕ)
    (charge : D.State → D.Op → ℕ)
    (rep : D.State → Data r_ds → Prop)
    (potential : Data r_ds → ℕ)
    (encode : D.Op → Fin r_ds → ℕ)
    (argMatch : D.Op → (Fin r_ds → ℕ) → Prop)
    (decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o))
    (bounded : ∀ {s x}, rep s x → x.Bounded w)
    (arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i))
    (encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
      argMatch o (fun i => if P.input i then encode o i else regs i))
    (rep_supported : ∀ {s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) →
      (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
      x'.Bounded w → rep s x → rep s x')
    (potential_supported : ∀ {s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) →
      (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
      rep s x → potential x' = potential x)
    (clear_nodup : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup)
    (params_not_clear : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg])
    (incCur_eval : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
      P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1)))
    (span_exec : ∀ {x : Data r_ds},
      x.Bounded w → x.regs P.frontierReg = base → (∀ j, x.regs (P.initParams j) = params j) →
      ∃ x₁, ExecWithin w P.allocSpan x x₁ spanTime ∧ x₁.mem = x.mem ∧
        x₁.regs P.baseReg = base ∧ x₁.regs P.frontierReg = base + space ∧
        (∀ j, x₁.regs (P.initParams j) = params j))
    (setup_exec : ∀ {x₁ : Data r_ds},
      x₁.Bounded w → x₁.regs P.baseReg = base → x₁.regs P.frontierReg = base + space →
      (∀ j, x₁.regs (P.initParams j) = params j) →
      (∀ a ∈ (Block.mk base space).footprint, x₁.mem a = 0) →
      ∃ y, ExecWithin w P.initSetup x₁ y setupTime ∧ y.regs P.frontierReg = base + space ∧
        rep s₀ y ∧ potential y ≤ initPotential ∧
        Modifies (Block.mk base space).footprint x₁.mem y.mem)
    (step_exec : ∀ {s : D.State} {x : Data r_ds} (o : D.Op),
      rep s x → D.valid s o → argMatch o x.regs →
      ∃ y n, Exec w P.code x y n ∧
        decode o y.regs = some (D.stepFn s o).2 ∧
        rep (D.stepFn s o).1 y ∧
        Modifies (Block.mk base space).footprint x.mem y.mem ∧
        n + potential y ≤ charge s o + potential x) :
    StateTransitionImpl P D w base params s₀ where
  space := space
  spanTime := spanTime
  setupTime := setupTime
  initPotential := initPotential
  charge := charge
  rep := rep
  potential := potential
  encode := encode
  argMatch := argMatch
  decode := decode
  bounded := bounded
  arguments_fit := arguments_fit
  encode_matches := encode_matches
  rep_supported := rep_supported
  potential_supported := potential_supported
  clear_nodup := clear_nodup
  params_not_clear := params_not_clear
  incCur_eval := incCur_eval
  span_exec := span_exec
  setup_exec := setup_exec
  step_exec {s _} o hr hv harg := by
    obtain ⟨y, n, he, hdec, hrep, hmod, hpot⟩ := step_exec o hr hv harg
    exact ⟨y, (D.stepFn s o).1, (D.stepFn s o).2, n, he, D.step_stepFn s o, hdec, hrep, hmod, hpot⟩

/-! ### Projection 1: Basis lifting and standalone `DynamicProgram` / `DataStructure` theorems -/

/-- Lift a `StateTransitionImpl` certificate along any defined-evaluation basis simulation. -/
def mapSimulates (φ : B.Simulates B') (C : StateTransitionImpl P D w base params s₀) :
    StateTransitionImpl (P.mapSimulates φ) D w base params s₀ where
  toSubroutineBase := C.toSubroutineBase.mapSimulates φ
  step_exec o hr hv harg :=
    let ⟨y, s', a, n, he, hstep, hdec, hrep, hmod, hpot⟩ := C.step_exec o hr hv harg
    ⟨y, s', a, n, he.mapSimulates φ, hstep, hdec, hrep, hmod, hpot⟩

/-- Lift an exact-basis `StateTransitionImpl` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : StateTransitionImpl P D w base params s₀) :
    StateTransitionImpl P.toStandard D w base params s₀ :=
  C.mapSimulates .exactStandard

section Standard

variable {P_std : SubroutineCode .standard r_ds k_init}
  (C : StateTransitionImpl P_std D w base params s₀)

/-- Project a `.standard`-basis `StateTransitionImpl` to a standalone `DynamicCertificate`. -/
def toCertificate : DynamicCertificate (D := D) C.toDynamicProgram w where
  rep := C.rep
  bounded := C.bounded
  arguments_fit := C.arguments_fit
  execute {s x} o hr hv := by
    have hb' : (C.toDynamicProgram.prepare o x).Bounded w :=
      C.toDynamicProgram.prepare_bounded (C.bounded hr) (C.arguments_fit o hv)
    have hr' : C.rep s (C.toDynamicProgram.prepare o x) :=
      C.rep_supported
        (fun i hi => C.toDynamicProgram.prepare_regs_of_not_input hi o x)
        (fun _ _ => rfl) hb' hr
    have harg : C.argMatch o (C.toDynamicProgram.prepare o x).regs :=
      C.encode_matches o x.regs
    obtain ⟨y, s', a, n, he, hstep, hdec, hrep, _, _⟩ := C.step_exec o hr' hv harg
    exact ⟨y, s', a, n, he, hstep, hdec, hrep⟩

/-- Project a `.standard`-basis `StateTransitionImpl` to a standalone `DataStructure.Amortized`
certificate, charging `+ 1` per operation for `DynamicProgram`'s trailing `halt` instruction. -/
theorem toAmortized :
    DataStructure.Amortized C.toCertificate.impl
      DynamicProgram.OperationTrace.instructions
      (fun _ x => C.potential x)
      (fun s o => C.charge s o + 1) where
  step {s x o a y trace} hr hv he := by
    have hb' : (C.toDynamicProgram.prepare o x).Bounded w :=
      C.toDynamicProgram.prepare_bounded (C.bounded hr) (C.arguments_fit o hv)
    have hr' : C.rep s (C.toDynamicProgram.prepare o x) :=
      C.rep_supported
        (fun i hi => C.toDynamicProgram.prepare_regs_of_not_input hi o x)
        (fun _ _ => rfl) hb' hr
    have hp_eq : C.potential (C.toDynamicProgram.prepare o x) = C.potential x :=
      C.potential_supported
        (fun i hi => C.toDynamicProgram.prepare_regs_of_not_input hi o x)
        (fun _ _ => rfl) hr
    have harg : C.argMatch o (C.toDynamicProgram.prepare o x).regs :=
      C.encode_matches o x.regs
    obtain ⟨z, s', a', m, hz, hstep, hdec, hrep, _, hpot⟩ := C.step_exec o hr' hv harg
    obtain ⟨rfl, hinst⟩ := he.eq_of_exec hz
    obtain ⟨_, _, _, ha_trace, _⟩ := he
    have ha_eq : a = a' := Option.some.inj (ha_trace.symm.trans hdec)
    subst ha_eq
    refine ⟨s', hstep, hrep, ?_⟩
    rw [hinst]
    rw [hp_eq] at hpot
    omega

/-- When `C.potential` is identically zero, `StateTransitionImpl` projects directly to a worst-case
`DataStructure.Bound` certificate. -/
theorem toBound (hpot : ∀ x, C.potential x = 0) :
    DataStructure.Bound C.toCertificate.impl
      DynamicProgram.OperationTrace.instructions
      (fun s o => C.charge s o + 1) := by
  intro s x o a y trace hr hv he
  obtain ⟨_, _, _, h⟩ := C.toAmortized.step hr hv he
  simp only [hpot] at h
  omega

/-- Standalone adaptive-client amortized bound for any demonically admissible client `p`. -/
theorem run_client_demonic_amortized {α : Type*} (p : D.Client α) {s : D.State} {x : Data r_ds}
    (hr : C.rep s x) (hv : D.DemonicValid s p) :
    ∃ a y traces s' tr,
      DataStructure.Executes (C.toDynamicProgram.ExecOp w) p x a y traces ∧
      D.ClientRun s p a s' tr ∧
      C.rep s' y ∧
      traces.length = tr.length ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces + C.potential y ≤
        D.totalCostTranscript (fun s o => C.charge s o + 1) s tr + C.potential x :=
  C.toAmortized.exists_demonic p hr hv

/-- Standalone adaptive-client worst-case bound when `C.potential` is identically zero. -/
theorem run_client_demonic_bound (hpot : ∀ x, C.potential x = 0) {α : Type*} (p : D.Client α)
    {s : D.State} {x : Data r_ds} (hr : C.rep s x) (hv : D.DemonicValid s p) :
    ∃ a y traces s' tr,
      DataStructure.Executes (C.toDynamicProgram.ExecOp w) p x a y traces ∧
      D.ClientRun s p a s' tr ∧
      C.rep s' y ∧
      traces.length = tr.length ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
        D.totalCostTranscript (fun s o => C.charge s o + 1) s tr :=
  DataStructure.Bound.exists_demonic (C.toBound hpot) p hr hv

/-- Standalone adaptive-client amortized bound on a deterministic specification. -/
theorem run_client_amortized
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {α : Type*} (p : D.Client α) {s : D.State} {x : Data r_ds}
    (hr : C.rep s x) (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ y traces,
      DataStructure.Executes (C.toDynamicProgram.ExecOp w) p x (D.clientResult s p) y traces ∧
      C.rep (D.clientState s p) y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces + C.potential y ≤
        D.totalCost (fun s o => C.charge s o + 1) s (D.clientHistory s p) + C.potential x :=
  C.toAmortized.exists_executes p hr hv

/-- Standalone adaptive-client worst-case bound on a deterministic specification when
`C.potential` is identically zero. -/
theorem run_client_bound
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (hpot : ∀ x, C.potential x = 0) {α : Type*} (p : D.Client α)
    {s : D.State} {x : Data r_ds} (hr : C.rep s x)
    (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ y traces,
      DataStructure.Executes (C.toDynamicProgram.ExecOp w) p x (D.clientResult s p) y traces ∧
      C.rep (D.clientState s p) y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
        D.totalCost (fun s o => C.charge s o + 1) s (D.clientHistory s p) :=
  DataStructure.Bound.exists_executes (C.toBound hpot) p hr hv

end Standard

/-! ### Projection 2: Relocated inline subroutine calls (`code_rename`, `call_rename`) -/

/-- Execute `P.code.rename f` inline when arguments already match `(x.comap f).regs`,
witnessing a permitted outcome `(s', a)` with `D.step s o s' a`. -/
theorem code_rename (C : StateTransitionImpl P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} {x : Data r_caller} (o : D.Op)
    (hr : C.rep s (x.comap f)) (hv : D.valid s o) (harg : C.argMatch o (x.comap f).regs) :
    ∃ z s' a t, ExecWithin w (P.code.rename f) x z t ∧
      D.step s o s' a ∧
      C.decode o (z.comap f).regs = some a ∧
      C.rep s' (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) ∧
      t + C.potential (z.comap f) ≤ C.charge s o + C.potential (x.comap f) := by
  obtain ⟨y, s', a, n, he, hstep, hdec, hrep, hmod, hpot⟩ := C.step_exec o hr hv harg
  refine ⟨y.extend f x, s', a, n, (he.rename hf).within, hstep, ?_, ?_, hmod,
    fun j hj => Data.extend_regs_of_notMem y x hj, ?_⟩
  · rw [Data.comap_extend hf]
    exact hdec
  · rw [Data.comap_extend hf]
    exact hrep
  · rw [Data.comap_extend hf]
    exact hpot

/-- Execute `.seq prep (P.code.rename f)` inline after a caller argument-preparation block `prep`
that preserves persistent DS registers and memory in `[base, base + C.space)`. -/
theorem call_rename (C : StateTransitionImpl P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} {x x' : Data r_caller} {prep : Code B r_caller} {t_prep : ℕ} (o : D.Op)
    (hr : C.rep s (x.comap f)) (hv : D.valid s o)
    (hprep : ExecWithin w prep x x' t_prep)
    (hb' : (x'.comap f).Bounded w)
    (hreg : ∀ i, P.input i = false → x'.regs (f i) = x.regs (f i))
    (hmem : ∀ a ∈ (Block.mk base C.space).footprint, x'.mem a = x.mem a)
    (harg : C.argMatch o (x'.comap f).regs) :
    ∃ z s' a t, ExecWithin w (.seq prep (P.code.rename f)) x z t ∧
      D.step s o s' a ∧
      C.decode o (z.comap f).regs = some a ∧
      C.rep s' (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x'.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x'.regs j) ∧
      t + C.potential (z.comap f) ≤ t_prep + C.charge s o + C.potential (x.comap f) := by
  have hr' : C.rep s (x'.comap f) :=
    C.rep_supported (x := x.comap f) (x' := x'.comap f) hreg hmem hb' hr
  have hp_eq : C.potential (x'.comap f) = C.potential (x.comap f) :=
    C.potential_supported (x := x.comap f) (x' := x'.comap f) hreg hmem hr
  obtain ⟨z, s', a, t_op, he_op, hstep, hdec, hrep_z, hmod_z, hregs_z, hpot_z⟩ :=
    C.code_rename hf o hr' hv harg
  exact ⟨z, s', a, t_prep + t_op, hprep.seq he_op, hstep, hdec, hrep_z, hmod_z, hregs_z,
    by rw [hp_eq] at hpot_z; omega⟩

/-- Deterministic specialization of `code_rename` for `[D.HasStepFn g]`. -/
theorem code_rename_ofFn
    {g : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn g]
    (C : StateTransitionImpl P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} {x : Data r_caller} (o : D.Op)
    (hr : C.rep s (x.comap f)) (hv : D.valid s o) (harg : C.argMatch o (x.comap f).regs) :
    ∃ z t, ExecWithin w (P.code.rename f) x z t ∧
      C.decode o (z.comap f).regs = some (D.stepFn s o).2 ∧
      C.rep (D.stepFn s o).1 (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) ∧
      t + C.potential (z.comap f) ≤ C.charge s o + C.potential (x.comap f) := by
  obtain ⟨z, s', a, t, he, hstep, hdec, hrep, hmod, hregs, hpot⟩ :=
    C.code_rename hf o hr hv harg
  have heq := (D.step_iff_stepFn s o s' a).mp hstep
  have hs' : s' = (D.stepFn s o).1 := congrArg Prod.fst heq
  have ha : a = (D.stepFn s o).2 := congrArg Prod.snd heq
  subst hs'; subst ha
  exact ⟨z, t, he, hdec, hrep, hmod, hregs, hpot⟩

/-- Deterministic specialization of `call_rename` for `[D.HasStepFn g]`. -/
theorem call_rename_ofFn
    {g : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn g]
    (C : StateTransitionImpl P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} {x x' : Data r_caller} {prep : Code B r_caller} {t_prep : ℕ} (o : D.Op)
    (hr : C.rep s (x.comap f)) (hv : D.valid s o)
    (hprep : ExecWithin w prep x x' t_prep)
    (hb' : (x'.comap f).Bounded w)
    (hreg : ∀ i, P.input i = false → x'.regs (f i) = x.regs (f i))
    (hmem : ∀ a ∈ (Block.mk base C.space).footprint, x'.mem a = x.mem a)
    (harg : C.argMatch o (x'.comap f).regs) :
    ∃ z t, ExecWithin w (.seq prep (P.code.rename f)) x z t ∧
      C.decode o (z.comap f).regs = some (D.stepFn s o).2 ∧
      C.rep (D.stepFn s o).1 (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x'.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x'.regs j) ∧
      t + C.potential (z.comap f) ≤ t_prep + C.charge s o + C.potential (x.comap f) := by
  obtain ⟨z, s', a, t, he, hstep, hdec, hrep, hmod, hregs, hpot⟩ :=
    C.call_rename hf o hr hv hprep hb' hreg hmem harg
  have heq := (D.step_iff_stepFn s o s' a).mp hstep
  have hs' : s' = (D.stepFn s o).1 := congrArg Prod.fst heq
  have ha : a = (D.stepFn s o).2 := congrArg Prod.snd heq
  subst hs'; subst ha
  exact ⟨z, t, he, hdec, hrep, hmod, hregs, hpot⟩

/-! ### Projection 3: Flat-program operation-sequence execution (`RunsOps`, `run_ops_exact_*`) -/

/-- Sequential flat-program execution of `ops : List D.Op` by repeated calls to `P.opProg`:
each call prepares input registers via `prepRegs`, runs `P.opProg` from `pc = 0` to `halt`,
decodes a permitted outcome `(s₁, a)` with `D.step s o s₁ a`, modifies memory only within
`[base, base + C.space)`, records the resulting transcript `tr : D.Transcript`, and accumulates
total instructions executed (including each trailing `halt`). -/
inductive RunsOps (C : StateTransitionImpl P D w base params s₀)
    (prepRegs : D.Op → (Fin r_ds → ℕ) → (Fin r_ds → ℕ) := C.prepareRegs) :
    D.State → Data r_ds → List D.Op → D.Transcript → D.State → Data r_ds → ℕ → Prop
  | nil {s x} : RunsOps C prepRegs s x [] [] s x 0
  | cons {s s₁ s₂ x o a ops tr pc y z steps rest} :
      Runs w P.opProg ⟨0, ⟨prepRegs o x.regs, x.mem⟩⟩ ⟨pc, y⟩ steps →
      (∃ out, step w P.opProg ⟨pc, y⟩ = .halt out) →
      D.step s o s₁ a →
      C.decode o y.regs = some a →
      Modifies (Block.mk base C.space).footprint x.mem y.mem →
      RunsOps C prepRegs s₁ y ops tr s₂ z rest →
      RunsOps C prepRegs s x (o :: ops) (⟨o, a, s₁⟩ :: tr) s₂ z ((steps + 1) + rest)

private theorem step_program_halt (c : Code B r_ds) (out : Fin r_ds) (y : Data r_ds) :
    step w (c.program out) ⟨0 + c.size, y⟩ = .halt (y.regs out) :=
  step_halt (by
    simp only [Code.program, Nat.zero_add,
      List.getElem?_append_right (Code.length_assemble c 0).le,
      Code.length_assemble, Nat.sub_self, List.getElem?_cons_zero])

/-- Flat-program sequence execution under a custom register-preparation function `prepRegs`. -/
theorem seq_runsOps_of_prep (C : StateTransitionImpl P D w base params s₀)
    (prepRegs : D.Op → (Fin r_ds → ℕ) → (Fin r_ds → ℕ))
    (hfit : ∀ {s} (o) (regs : Fin r_ds → ℕ), D.valid s o → (∀ i, Fits w (regs i)) →
      ∀ i, Fits w (prepRegs o regs i))
    (hnot_in : ∀ (o : D.Op) (regs : Fin r_ds → ℕ) (i : Fin r_ds),
      P.input i = false → prepRegs o regs i = regs i)
    (harg : ∀ (o : D.Op) (regs : Fin r_ds → ℕ), C.argMatch o (prepRegs o regs)) :
    ∀ (ops : List D.Op) {s : D.State} {x : Data r_ds},
      C.rep s x → D.ValidOpSeq s ops →
      ∃ tr s_fin z t_ops,
        C.RunsOps prepRegs s x ops tr s_fin z t_ops ∧
        tr.ops = ops ∧
        D.ValidTranscript s tr s_fin ∧
        C.rep s_fin z ∧
        t_ops + C.potential z ≤
          D.totalCostTranscript (fun st o => C.charge st o + 1) s tr + C.potential x
  | [], s, x, hr, _ =>
    ⟨[], s, x, 0, .nil, rfl, .nil s, hr, Nat.zero_add (C.potential x) ▸ le_rfl⟩
  | o :: ops, s, x, hr, ⟨hv_o, hv_rest⟩ => by
    let x' : Data r_ds := ⟨prepRegs o x.regs, x.mem⟩
    have hbx := C.bounded hr
    have hb' : x'.Bounded w := ⟨hfit o x.regs hv_o hbx.1, hbx.2⟩
    have hreg' : ∀ i, P.input i = false → x'.regs i = x.regs i :=
      fun i hi => hnot_in o x.regs i hi
    have hr' : C.rep s x' := C.rep_supported hreg' (fun _ _ => rfl) hb' hr
    have hpot' : C.potential x' = C.potential x :=
      C.potential_supported hreg' (fun _ _ => rfl) hr
    obtain ⟨y, s₁, a, m, he_op, hstep, hdec, hr_y, hmod, hpot_m⟩ :=
      C.step_exec o hr' hv_o (harg o x.regs)
    rw [hpot'] at hpot_m
    have hruns : Runs w P.opProg ⟨0, x'⟩ ⟨0 + P.code.size, y⟩ m :=
      he_op.runs (pc := 0) (p := P.opProg) (Program.Contains.self _).append_left
    have hhalt : step w P.opProg ⟨0 + P.code.size, y⟩ = .halt (y.regs P.output) :=
      step_program_halt P.code P.output y
    obtain ⟨tr, s_fin, z, rest, hrest, hops, htr, hr_z, hpot_rest⟩ :=
      seq_runsOps_of_prep C prepRegs hfit hnot_in harg ops hr_y (hv_rest s₁ a hstep)
    refine ⟨⟨o, a, s₁⟩ :: tr, s_fin, z, (m + 1) + rest,
      .cons hruns ⟨_, hhalt⟩ hstep hdec hmod hrest,
      congrArg (o :: ·) hops, .cons _ hv_o hstep htr, hr_z, ?_⟩
    simp only [StateTransitionSpec.totalCostTranscript_cons]
    omega

/-- Flat-program sequence execution using `C.prepareRegs`. -/
theorem seq_runsOps (C : StateTransitionImpl P D w base params s₀)
    (ops : List D.Op) {s : D.State} {x : Data r_ds}
    (hr : C.rep s x) (hv : D.ValidOpSeq s ops) :
    ∃ tr s_fin z t_ops,
      C.RunsOps C.prepareRegs s x ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s tr s_fin ∧
      C.rep s_fin z ∧
      t_ops + C.potential z ≤
        D.totalCostTranscript (fun st o => C.charge st o + 1) s tr + C.potential x := by
  refine C.seq_runsOps_of_prep C.prepareRegs ?_ ?_ C.encode_matches ops hr hv
  · intro s' o regs hv_o hregs i
    simp only [SubroutineBase.prepareRegs]
    split_ifs with hi
    · exact C.arguments_fit o hv_o i hi
    · exact hregs i
  · intro o regs i hi
    simp [SubroutineBase.prepareRegs, hi]

/-- Standalone flat-program operation-sequence theorem with `O(1)` fresh initialization on zeroed
`[base, base + C.space)`. -/
theorem run_ops_exact_fresh (C : StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hzero : ∀ a ∈ (Block.mk base C.space).footprint, d₀.mem a = 0)
    (ops : List D.Op) (hv : D.ValidOpSeq s₀ ops) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w P.initFreshProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsOps C.prepareRegs s₀ x₀ ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s₀ tr s_fin ∧
      C.rep s_fin z ∧
      t_init ≤ C.initTime ∧
      t_ops + C.potential z ≤
        D.totalCostTranscript (fun st o => C.charge st o + 1) s₀ tr + C.initPotential := by
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hr₀, hpot₀, hmod₀⟩ :=
    C.initFresh_exec hd₀ hfr hpar hzero
  have hruns₀ : Runs w P.initFreshProg ⟨0, d₀⟩ ⟨0 + P.initFresh.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := P.initFreshProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w P.initFreshProg ⟨0 + P.initFresh.size, x₀⟩ = .halt (x₀.regs P.output) :=
    step_program_halt P.initFresh P.output x₀
  obtain ⟨tr, s_fin, z, t_ops, hruns_ops, hops, htr, hr_z, hbound⟩ :=
    C.seq_runsOps ops hr₀ hv
  exact ⟨_, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops,
    hops, htr, hr_z, ht_init, by omega⟩

/-- Standalone flat-program operation-sequence theorem with `O(space)` reusable initialization on
arbitrary `w`-bounded memory. -/
theorem run_ops_exact_reusable (C : StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (ops : List D.Op) (hv : D.ValidOpSeq s₀ ops) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w P.initClearProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsOps C.prepareRegs s₀ x₀ ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s₀ tr s_fin ∧
      C.rep s_fin z ∧
      t_init ≤ C.initTime + 4 * C.space + 6 ∧
      t_ops + C.potential z ≤
        D.totalCostTranscript (fun st o => C.charge st o + 1) s₀ tr + C.initPotential := by
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hr₀, hpot₀, hmod₀⟩ :=
    C.initClear_exec hd₀ hfr hpar
  have hruns₀ : Runs w P.initClearProg ⟨0, d₀⟩ ⟨0 + P.initClear.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := P.initClearProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w P.initClearProg ⟨0 + P.initClear.size, x₀⟩ = .halt (x₀.regs P.output) :=
    step_program_halt P.initClear P.output x₀
  obtain ⟨tr, s_fin, z, t_ops, hruns_ops, hops, htr, hr_z, hbound⟩ :=
    C.seq_runsOps ops hr₀ hv
  exact ⟨_, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops,
    hops, htr, hr_z, ht_init, by omega⟩

/-- Deterministic specialization of `run_ops_exact_fresh` for `[D.HasStepFn g]`, executing the
canonical transcript `D.canonicalTranscript s₀ ops` to `(D.run s₀ ops).1`. -/
theorem run_ops_exact_fresh_ofFn
    {g : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn g]
    (C : StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hzero : ∀ a ∈ (Block.mk base C.space).footprint, d₀.mem a = 0)
    (ops : List D.Op) (hv : D.ValidHistory s₀ ops) :
    ∃ pc₀ x₀ t_init z t_ops,
      Runs w P.initFreshProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsOps C.prepareRegs s₀ x₀ ops
        (D.canonicalTranscript s₀ ops) (D.run s₀ ops).1 z t_ops ∧
      C.rep (D.run s₀ ops).1 z ∧
      t_init ≤ C.initTime ∧
      t_ops + C.potential z ≤
        D.totalCost (fun st o => C.charge st o + 1) s₀ ops + C.initPotential := by
  obtain ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, hhalt₀, hmod₀,
      hruns_ops, hops, htr, hr_z, ht_init, hbound⟩ :=
    C.run_ops_exact_fresh hd₀ hfr hpar hzero ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr hv)
  obtain ⟨_, hs_fin, htr_eq⟩ := (D.validTranscript_iff_run s₀ tr s_fin).mp htr
  rw [hops] at hs_fin htr_eq
  subst hs_fin; subst htr_eq
  rw [D.totalCostTranscript_canonicalTranscript] at hbound
  exact ⟨pc₀, x₀, t_init, z, t_ops, hruns₀, hhalt₀, hmod₀, hruns_ops, hr_z, ht_init, hbound⟩

/-- Deterministic specialization of `run_ops_exact_reusable` for `[D.HasStepFn g]`, executing the
canonical transcript `D.canonicalTranscript s₀ ops` to `(D.run s₀ ops).1`. -/
theorem run_ops_exact_reusable_ofFn
    {g : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn g]
    (C : StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (ops : List D.Op) (hv : D.ValidHistory s₀ ops) :
    ∃ pc₀ x₀ t_init z t_ops,
      Runs w P.initClearProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsOps C.prepareRegs s₀ x₀ ops
        (D.canonicalTranscript s₀ ops) (D.run s₀ ops).1 z t_ops ∧
      C.rep (D.run s₀ ops).1 z ∧
      t_init ≤ C.initTime + 4 * C.space + 6 ∧
      t_ops + C.potential z ≤
        D.totalCost (fun st o => C.charge st o + 1) s₀ ops + C.initPotential := by
  obtain ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, hhalt₀, hmod₀,
      hruns_ops, hops, htr, hr_z, ht_init, hbound⟩ :=
    C.run_ops_exact_reusable hd₀ hfr hpar ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr hv)
  obtain ⟨_, hs_fin, htr_eq⟩ := (D.validTranscript_iff_run s₀ tr s_fin).mp htr
  rw [hops] at hs_fin htr_eq
  subst hs_fin; subst htr_eq
  rw [D.totalCostTranscript_canonicalTranscript] at hbound
  exact ⟨pc₀, x₀, t_init, z, t_ops, hruns₀, hhalt₀, hmod₀, hruns_ops, hr_z, ht_init, hbound⟩

end StateTransitionImpl

end Cslib.DataStructure.WordRAM
