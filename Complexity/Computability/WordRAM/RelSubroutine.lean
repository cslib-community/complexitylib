/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Subroutine
public import Complexity.Foundations.Semantics.Stateful.Relational

/-!
# Relational Word-RAM dynamic programs and composable data-structure subroutines

This file extends `Complexity.Computability.WordRAM.Dynamic` and
`Complexity.Computability.WordRAM.Subroutine` from deterministic specifications (`Stateful.Spec`)
to relational specifications (`Stateful.RelSpec`):

1. **Standalone relational fixed-program implementations (`RelDynamicProgram`,
   `RelDynamicCertificate`):** Generalizes `DynamicProgram` and `DynamicCertificate` to
   `D : Stateful.RelSpec`, where `execute` witnesses an angelic outcome `(s', a)` satisfying
   `D.step s o s' a`. Because the Word-RAM structured semantics `Exec` is deterministic,
   `RelDynamicCertificate.realization` establishes `Stateful.RelRealization` directly via
   `Exec.unique`.
2. **Unified standalone and inline relational subroutine certificates (`RelSubroutineDS`):**
   Mirrors `SubroutineDS` over `D : Stateful.RelSpec`, omitting `rep_unique` (since concrete
   potential `potential : Data r_ds → ℕ` depends only on machine data) and existentially
   quantifying over `(s', a)` with `D.step s o s' a` in `step_exec`.
3. **Zero-cost embedding of deterministic subroutines (`SubroutineDS.toRelSubroutineDS`):**
   Every `SubroutineDS P D w base params s₀` embeds into
   `RelSubroutineDS P D.toRelSpec w base params s₀`.
4. **Basis lifting, standalone `Stateful` projections, inline subroutine calls, and flat-program
   operation sequences:** Provides `mapSimulates`, `toStandard`, `toRelDynamicProgram`,
   `toRelCertificate`, `toRelAmortized`, `toRelBound`, `run_client_amortized`, `run_client_bound`,
   `initFresh_exec`, `initFresh_rename`, `zeroFillCode_exec`, `initClear_exec`,
   `initClear_rename`, `code_rename`, `call_rename`, `frame_caller`, and flat-program sequence
   execution (`RunsRelOps`, `seq_runsRelOps`, `run_ops_exact_fresh`, `run_ops_exact_reusable`).

## Main definitions

* `Cslib.WordRAM.RelDynamicProgram`, `Cslib.WordRAM.RelDynamicCertificate`: standalone fixed-program
  realization and certificate for a relational specification `D : Stateful.RelSpec`.
* `Cslib.WordRAM.RelSubroutineDS`: unified standalone and inline subroutine specification and
  amortized resource certificate for `P : SubroutineCode B r_ds k_init` realizing
  `D : Stateful.RelSpec` (without `rep_unique`).
* `Cslib.WordRAM.SubroutineDS.toRelSubroutineDS`: embedding of a deterministic `SubroutineDS` into
  `RelSubroutineDS`.
* `Cslib.WordRAM.RelSubroutineDS.RunsRelOps`: sequential flat-program execution of an operation list
  recording the resulting abstract transcript `D.Transcript`.

## Main results

* `Cslib.WordRAM.RelDynamicCertificate.realization`,
  `Cslib.WordRAM.RelDynamicCertificate.instruction_bound`: standalone `Stateful.RelRealization`
  and `Stateful.RelBound` certificates.
* `Cslib.WordRAM.RelSubroutineDS.toRelAmortized`,
  `Cslib.WordRAM.RelSubroutineDS.run_client_amortized`: standalone amortized potential certificate
  and adaptive-client bound over `Basis.standard`.
* `Cslib.WordRAM.RelSubroutineDS.initFresh_rename`,
  `Cslib.WordRAM.RelSubroutineDS.initClear_rename`,
  `Cslib.WordRAM.RelSubroutineDS.call_rename`,
  `Cslib.WordRAM.RelSubroutineDS.frame_caller`: relocated inline initialization, inline operation
  calls, and bidirectional framing.
* `Cslib.WordRAM.RelSubroutineDS.run_ops_exact_fresh`,
  `Cslib.WordRAM.RelSubroutineDS.run_ops_exact_reusable`: end-to-end flat-program execution of any
  demonically admissible operation sequence `D.ValidOpSeq s₀ ops`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 17][CLRS2009]
* [J. C. Reynolds, *Separation Logic: A Logic for Shared Mutable Data Structures*][Reynolds2002]
-/

@[expose] public section

namespace Cslib.WordRAM

universe u v z

/-! ## Standalone relational dynamic programs (`RelDynamicProgram`, `RelDynamicCertificate`) -/

variable {r : ℕ} {D : Stateful.RelSpec.{u, v, z}}

/-- A single `.standard`-basis Word-RAM program serving all operations of a relational
specification `D : Stateful.RelSpec` through a fixed register calling convention. -/
structure RelDynamicProgram (D : Stateful.RelSpec.{u, v, z}) (r : ℕ) where
  /-- The same structured program is executed for every operation. -/
  code : Code .standard r
  /-- Register returned by the final `halt` instruction. -/
  output : Fin r
  /-- Registers overwritten by externally supplied operation arguments. -/
  input : Fin r → Bool
  /-- Encoded arguments, independent of the maintained machine state. -/
  encode : D.Op → Fin r → ℕ
  /-- Interpretation of the final register tuple as the operation's typed observation. -/
  decode : (o : D.Op) → (Fin r → ℕ) → Option (D.Result o)

/-- Embed a deterministic `DynamicProgram D r` as a `RelDynamicProgram D.toRelSpec r`. -/
abbrev DynamicProgram.toRelDynamicProgram {D : Stateful.Spec.{u, v, z}} {r : ℕ}
    (P : DynamicProgram D r) : RelDynamicProgram D.toRelSpec r where
  code := P.code
  output := P.output
  input := P.input
  encode := P.encode
  decode := P.decode

namespace RelDynamicProgram

variable (P : RelDynamicProgram D r)

/-- Deliver operation arguments without changing maintained memory or non-input registers. -/
def prepare (o : D.Op) (x : Data r) : Data r where
  regs i := if P.input i then P.encode o i else x.regs i
  mem := x.mem

/-- Delivering operation arguments preserves the machine memory unchanged. -/
@[simp]
theorem prepare_mem (o : D.Op) (x : Data r) : (P.prepare o x).mem = x.mem := rfl

/-- Registers outside the calling convention retain their contents. -/
theorem prepare_regs_of_not_input {i : Fin r} (hi : P.input i = false) (o : D.Op) (x : Data r) :
    (P.prepare o x).regs i = x.regs i := by
  simp [prepare, hi]

/-- Argument delivery preserves bounded words when the arguments fit. -/
theorem prepare_bounded {w : ℕ} {o : D.Op} {x : Data r} (hx : x.Bounded w)
    (ho : ∀ i, P.input i = true → Fits w (P.encode o i)) : (P.prepare o x).Bounded w := by
  refine ⟨fun i => ?_, hx.2⟩
  change Fits w (if P.input i then P.encode o i else x.regs i)
  split
  · exact ho i (by assumption)
  · exact hx.1 i

/-- Evaluate one typed call, delivering its arguments and decoding its observation. The returned
cost includes the final `halt`. -/
def eval (w fuel : ℕ) (o : D.Op) (x : Data r) : Option (Data r × D.Result o × ℕ) :=
  match P.code.eval w fuel (P.prepare o x) with
  | none => none
  | some (y, n) => (P.decode o y.regs).map fun a => (y, a, n + 1)

/-- A bounded machine call with native execution evidence (`DynamicProgram.OperationTrace`). -/
def ExecOp (w : ℕ) : Stateful.RelExecution D (Data r) DynamicProgram.OperationTrace :=
  fun x o a y trace =>
    (P.prepare o x).Bounded w ∧ ∃ n, TraceExec w P.code (P.prepare o x) y n trace.probes ∧
      P.decode o y.regs = some a ∧ trace.instructions = n + 1

/-- Successful typed evaluation supplies an exact operation trace when the delivered state is
bounded. -/
theorem ExecOp.of_eval {w fuel k : ℕ} {o : D.Op} {x y : Data r} {a : D.Result o}
    (hb : (P.prepare o x).Bounded w) (h : P.eval w fuel o x = some (y, a, k)) :
    ∃ probes, P.ExecOp w x o a y ⟨k, probes⟩ := by
  cases he : P.code.eval w fuel (P.prepare o x) with
  | none => simp [eval, he] at h
  | some yn =>
    obtain ⟨z, n⟩ := yn
    cases hd : P.decode o z.regs with
    | none => simp [eval, he, hd] at h
    | some b =>
      simp only [eval, he, hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨probes, hp⟩ := (Exec.of_eval he).exists_trace
      exact ⟨probes, hb, n, hp, hd, rfl⟩

/-- Every call is an execution of one fixed flat machine program. -/
theorem ExecOp.executes {w : ℕ} {x y : Data r} {o : D.Op} {a : D.Result o}
    {trace : DynamicProgram.OperationTrace} (h : P.ExecOp w x o a y trace) :
    Executes w (P.code.program P.output) ⟨0, P.prepare o x⟩ (y.regs P.output)
      trace.instructions := by
  obtain ⟨_, n, he, _, ht⟩ := h
  rw [ht]
  exact he.exec.executes P.output

/-- A call preserves bounded words. -/
theorem ExecOp.bounded {w : ℕ} {x y : Data r} {o : D.Op} {a : D.Result o}
    {trace : DynamicProgram.OperationTrace} (h : P.ExecOp w x o a y trace) : y.Bounded w := by
  obtain ⟨hb, _, he, _, _⟩ := h
  exact he.exec.bounded hb

/-- Calls are deterministic in their final representation, observation, and instruction count. -/
theorem ExecOp.unique {w : ℕ} {x y y' : Data r} {o : D.Op} {a a' : D.Result o}
    {trace trace' : DynamicProgram.OperationTrace} (h : P.ExecOp w x o a y trace)
    (h' : P.ExecOp w x o a' y' trace') :
    y = y' ∧ a = a' ∧ trace.instructions = trace'.instructions := by
  obtain ⟨_, _, he, ha, ht⟩ := h
  obtain ⟨_, _, he', ha', ht'⟩ := h'
  obtain ⟨rfl, rfl⟩ := he.exec.unique he'.exec
  exact ⟨rfl, Option.some.inj (ha.symm.trans ha'), ht.trans ht'.symm⟩

/-- A call's final state and instruction count agree with any structured execution of the code. -/
theorem ExecOp.eq_of_exec {P : RelDynamicProgram D r} {w : ℕ} {x y z : Data r} {o : D.Op}
    {a : D.Result o} {trace : DynamicProgram.OperationTrace} {m : ℕ}
    (he : P.ExecOp w x o a y trace) (h : Exec w P.code (P.prepare o x) z m) :
    y = z ∧ trace.instructions = m + 1 := by
  obtain ⟨_, _, ht, _, hn⟩ := he
  obtain ⟨rfl, rfl⟩ := ht.exec.unique h
  exact ⟨rfl, hn⟩

/-- The write transcript supplies a frame rule for a call, including register-only delivery. -/
theorem ExecOp.frame {w : ℕ} {x y : Data r} {o : D.Op} {a : D.Result o}
    {trace : DynamicProgram.OperationTrace} (h : P.ExecOp w x o a y trace) {Q : HeapAssertion}
    (hQ : Q.holds x.mem) (hd : Disjoint Q.footprint (Probe.writes trace.probes)) :
    Q.holds y.mem := by
  obtain ⟨_, _, he, _, _⟩ := h
  exact he.frame hQ hd

end RelDynamicProgram

/-- Per-operation angelic machine proof obligations for a `RelDynamicProgram`. -/
structure RelDynamicCertificate (P : RelDynamicProgram D r) (w : ℕ) where
  /-- Abstract state represented by the persistent machine data. -/
  rep : D.State → Data r → Prop
  /-- Represented configurations contain only machine words. -/
  bounded : ∀ {s x}, rep s x → x.Bounded w
  /-- Admissible arguments fit the machine's word size. -/
  arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (P.encode o i)
  /-- A machine execution implements an admissible operation by realizing some permitted
  `(s', a)` with `D.step s o s' a`. -/
  execute : ∀ {s x} (o), rep s x → D.valid s o →
    ∃ y s' a n, Exec w P.code (P.prepare o x) y n ∧
      D.step s o s' a ∧ P.decode o y.regs = some a ∧ rep s' y

/-- Embed a deterministic `DynamicCertificate` as a `RelDynamicCertificate`. -/
def DynamicCertificate.toRelDynamicCertificate {D : Stateful.Spec.{u, v, z}} {r w : ℕ}
    {P : DynamicProgram D r} (C : DynamicCertificate P w) :
    RelDynamicCertificate P.toRelDynamicProgram w where
  rep := C.rep
  bounded := C.bounded
  arguments_fit := C.arguments_fit
  execute o hr hv := by
    obtain ⟨y, n, he, hdec, hrep⟩ := C.execute o hr hv
    exact ⟨y, (D.step _ o).1, (D.step _ o).2, n, he, rfl, hdec, hrep⟩

namespace RelDynamicCertificate

variable {P : RelDynamicProgram D r} {w : ℕ} (C : RelDynamicCertificate P w)

/-- Turn a successful typed evaluation on a represented state and admissible operation into
certified `ExecOp` evidence. -/
theorem execOp_of_eval {s : D.State} {x y : Data r} {o : D.Op} {a : D.Result o} {fuel k : ℕ}
    (hr : C.rep s x) (hv : D.valid s o) (h : P.eval w fuel o x = some (y, a, k)) :
    ∃ probes, P.ExecOp w x o a y ⟨k, probes⟩ :=
  RelDynamicProgram.ExecOp.of_eval P
    (P.prepare_bounded (C.bounded hr) (C.arguments_fit o hv)) h

/-- Fixed-program relational certificates realize `D` via `Stateful.RelRealization`. -/
def realization : Stateful.RelRealization D (P.ExecOp w) where
  rep := C.rep
  total o hr hv := by
    obtain ⟨y, _, a, n, he, _, ha, _⟩ := C.execute o hr hv
    obtain ⟨ts, hts⟩ := he.exists_trace
    exact ⟨a, y, ⟨n + 1, ts⟩,
      P.prepare_bounded (C.bounded hr) (C.arguments_fit o hv), n, hts, ha, rfl⟩
  correct hr hv he := by
    obtain ⟨y, s', a, n, he', hstep, ha, hr'⟩ := C.execute _ hr hv
    obtain ⟨_, _, ht, ha', _⟩ := he
    obtain ⟨rfl, rfl⟩ := ht.exec.unique he'
    have h_eq : _ = a := Option.some.inj (ha'.symm.trans ha)
    subst h_eq
    exact ⟨s', hstep, hr'⟩

/-- A separate per-operation instruction estimate supplies a reusable `Stateful.RelBound`. -/
theorem instruction_bound (charge : D.State → D.Op → ℕ)
    (hbound : ∀ {s x} (o) {y n}, C.rep s x → D.valid s o →
      Exec w P.code (P.prepare o x) y n → n + 1 ≤ charge s o) :
    Stateful.RelBound C.realization DynamicProgram.OperationTrace.instructions charge := by
  intro s x o a y trace hr hv he
  obtain ⟨_, n, ht, _, hn⟩ := he
  rw [hn]
  exact hbound o hr hv ht.exec

/-- A uniform constant instruction bound follows from an existential per-operation execution. -/
theorem instruction_bound_const (K : ℕ)
    (hbound : ∀ {s x} (o), C.rep s x → D.valid s o →
      ∃ y n, Exec w P.code (P.prepare o x) y n ∧ n + 1 ≤ K) :
    Stateful.RelBound C.realization DynamicProgram.OperationTrace.instructions
      (fun _ _ => K) := by
  apply C.instruction_bound
  intro s x o y n hr hv he
  obtain ⟨_, _, he', hn⟩ := hbound o hr hv
  obtain ⟨_, rfl⟩ := he.unique he'
  exact hn

/-- Adaptive client execution, final representation, and linear total instruction bound for a
uniform constant per-operation instruction certificate. -/
theorem run_client_const {K : ℕ}
    (B : Stateful.RelBound C.realization DynamicProgram.OperationTrace.instructions
      (fun _ _ => K))
    {α : Type*} (p : D.Client α) {s : D.State} {x : Data r}
    (hr : C.rep s x) (hv : D.DemonicValid s p) :
    ∃ a y traces s' tr,
      Stateful.RelExecutes (P.ExecOp w) p x a y traces ∧
      D.ClientRun s p a s' tr ∧
      C.rep s' y ∧
      traces.length = tr.length ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤ tr.length * K := by
  obtain ⟨a, y, traces, s', tr, he, hrun, hr', hlen, hcost⟩ := B.exists_executes p hr hv
  rw [D.totalCost_const] at hcost
  exact ⟨a, y, traces, s', tr, he, hrun, hr', hlen, hcost⟩

/-- Lift a per-operation pointwise memory frame from `Exec` to `ExecOp`. -/
theorem frame_of_execute {j : ℕ}
    (hframe : ∀ {s x} (o), C.rep s x → D.valid s o →
      ∃ z n, Exec w P.code (P.prepare o x) z n ∧ z.mem j = x.mem j)
    {s : D.State} {x y : Data r} {o : D.Op} {a : D.Result o}
    {trace : DynamicProgram.OperationTrace}
    (hr : C.rep s x) (hv : D.valid s o) (he : P.ExecOp w x o a y trace) :
    y.mem j = x.mem j := by
  obtain ⟨z, n, hz, hf⟩ := hframe o hr hv
  exact (he.eq_of_exec hz).1 ▸ hf

/-- Lift a per-operation `Modifies` bound from `Exec` to `ExecOp`. -/
theorem modifies_of_execute {F : Finset ℕ}
    (hmod : ∀ {s x} (o), C.rep s x → D.valid s o →
      ∃ z n, Exec w P.code (P.prepare o x) z n ∧ Modifies F x.mem z.mem)
    {s : D.State} {x y : Data r} {o : D.Op} {a : D.Result o}
    {trace : DynamicProgram.OperationTrace}
    (hr : C.rep s x) (hv : D.valid s o) (he : P.ExecOp w x o a y trace) :
    Modifies F x.mem y.mem :=
  fun j hj => C.frame_of_execute
    (fun o hr' hv' => let ⟨z, n, hz, hf⟩ := hmod o hr' hv'; ⟨z, n, hz, hf j hj⟩)
    hr hv he

/-- Lift a per-operation pointwise memory frame across a demonically admissible adaptive client
execution. -/
theorem executes_client_frame {j : ℕ}
    (hframe : ∀ {s x y o a trace}, C.rep s x → D.valid s o →
      P.ExecOp w x o a y trace → y.mem j = x.mem j)
    {α : Type*} {p : D.Client α} {s : D.State} {x y : Data r} {val : α}
    {traces : List DynamicProgram.OperationTrace}
    (hr : C.rep s x) (hv : D.DemonicValid s p)
    (he : Stateful.RelExecutes (P.ExecOp w) p x val y traces) :
    y.mem j = x.mem j := by
  induction he generalizing s with
  | pure _ _ => rfl
  | @call o k c a c' trace _ _ _ hstep _ ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    obtain ⟨s', hstep_d, hr'⟩ := C.realization.correct hr hv_o hstep
    exact (ih hr' (hv_k s' a hstep_d)).trans (hframe hr hv_o hstep)

/-- Lift a per-operation `Modifies` bound across a demonically admissible adaptive client
execution. -/
theorem executes_client_modifies {F : Finset ℕ}
    (hmod : ∀ {s x y o a trace}, C.rep s x → D.valid s o →
      P.ExecOp w x o a y trace → Modifies F x.mem y.mem)
    {α : Type*} {p : D.Client α} {s : D.State} {x y : Data r} {val : α}
    {traces : List DynamicProgram.OperationTrace}
    (hr : C.rep s x) (hv : D.DemonicValid s p)
    (he : Stateful.RelExecutes (P.ExecOp w) p x val y traces) :
    Modifies F x.mem y.mem :=
  fun j hj => C.executes_client_frame
    (fun hr' hv' he' => hmod hr' hv' he' j hj) hr hv he

/-- Memory probes are bounded by the instruction charge. -/
theorem probe_bound (charge : D.State → D.Op → ℕ)
    (B : Stateful.RelBound C.realization DynamicProgram.OperationTrace.instructions charge) :
    Stateful.RelBound C.realization (fun t => t.probes.length) charge := by
  intro s x o a y trace hr hv he
  have hb := B hr hv he
  obtain ⟨_, n, ht, _, hn⟩ := he
  exact ht.length_le.trans ((Nat.le_add_right n 1).trans (hn ▸ hb))

end RelDynamicCertificate

/-! ## `RelSubroutineDS` and `SubroutineDS.toRelSubroutineDS` -/

namespace SubroutineCode

variable {B : Basis} {r_ds k_init : ℕ}

/-- Compiled flat `Program B r_ds` for `O(1)` fresh zeroed-memory initialization. -/
def initFreshProg (P : SubroutineCode B r_ds k_init) : Program B r_ds :=
  P.initFresh.program P.output

/-- Compiled flat `Program B r_ds` for `O(space)` dirty-memory reusable initialization. -/
def initClearProg (P : SubroutineCode B r_ds k_init) : Program B r_ds :=
  P.initClear.program P.output

/-- Compiled flat `Program B r_ds` serving all operations of the data structure. -/
def opProg (P : SubroutineCode B r_ds k_init) : Program B r_ds :=
  P.code.program P.output

end SubroutineCode

/-- Unified standalone and subroutine specification/resource certificate for
`P : SubroutineCode B r_ds k_init` realizing a relational specification `D : Stateful.RelSpec`
at word width `w`, base address `base`, runtime parameters `params`, and initial state `s₀`.

In contrast to `SubroutineDS`, `rep_unique` is omitted (because concrete potential
`potential : Data r_ds → ℕ` depends only on machine data) and `step_exec` existentially
quantifies over a permitted outcome `(s', a)` satisfying `D.step s o s' a`. -/
structure RelSubroutineDS {B : Basis} {r_ds k_init : ℕ} (P : SubroutineCode B r_ds k_init)
    (D : Stateful.RelSpec.{u, v, z}) (w base : ℕ) (params : Fin k_init → ℕ) (s₀ : D.State) where
  /-- Contiguous memory footprint length `[base, base + space)`. -/
  space : ℕ
  /-- Instruction bound for `P.allocSpan`. -/
  spanTime : ℕ
  /-- Instruction bound for `P.initSetup`. -/
  setupTime : ℕ
  /-- Upper bound on initial concrete potential after initialization. -/
  initPotential : ℕ
  /-- Amortized instruction charge per operation (excluding trailing standalone `halt`). -/
  charge : D.State → D.Op → ℕ
  /-- Representation invariant linking mathematical state `s` to concrete `Data r_ds`. -/
  rep : D.State → Data r_ds → Prop
  /-- Concrete integer potential depending only on `Data r_ds`. -/
  potential : Data r_ds → ℕ
  /-- Standalone register encoding for `RelDynamicProgram.prepare`. -/
  encode : D.Op → Fin r_ds → ℕ
  /-- Partial argument-matching predicate for inline callers (refined by `encode`). -/
  argMatch : D.Op → (Fin r_ds → ℕ) → Prop
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o)
  /-- Represented configurations are word-bounded. -/
  bounded : ∀ {s x}, rep s x → x.Bounded w
  /-- Standalone encoded arguments fit in `w`-bit words on admissible calls. -/
  arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i)
  /-- Full standalone `prepare` delivery satisfies `argMatch`. -/
  encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
    argMatch o (fun i => if P.input i then encode o i else regs i)
  /-- `rep` depends only on persistent registers (`P.input i = false`) and `[base, base + space)`.
  -/
  rep_supported : ∀ {s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) →
    (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
    x'.Bounded w → rep s x → rep s x'
  /-- `potential` depends only on persistent registers and `[base, base + space)` under `rep`. -/
  potential_supported : ∀ {s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) →
    (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
    rep s x → potential x' = potential x
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
  /-- Execution of `P.initSetup` once `[base, base + space)` holds zeros. -/
  setup_exec : ∀ {x₁ : Data r_ds},
    x₁.Bounded w → x₁.regs P.baseReg = base → x₁.regs P.frontierReg = base + space →
    (∀ j, x₁.regs (P.initParams j) = params j) →
    (∀ a ∈ (Block.mk base space).footprint, x₁.mem a = 0) →
    ∃ y, ExecWithin w P.initSetup x₁ y setupTime ∧ y.regs P.frontierReg = base + space ∧
      rep s₀ y ∧ potential y ≤ initPotential ∧
      Modifies (Block.mk base space).footprint x₁.mem y.mem
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

/-- Embed any deterministic `SubroutineDS P D w base params s₀` as a relational
`RelSubroutineDS P D.toRelSpec w base params s₀`. -/
def SubroutineDS.toRelSubroutineDS {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init} {D : Stateful.Spec.{u, v, z}}
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : SubroutineDS P D w base params s₀) :
    RelSubroutineDS P D.toRelSpec w base params s₀ where
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  initPotential := C.initPotential
  charge := C.charge
  rep := C.rep
  potential := C.potential
  encode := C.encode
  argMatch := C.argMatch
  decode := C.decode
  bounded := C.bounded
  arguments_fit := C.arguments_fit
  encode_matches := C.encode_matches
  rep_supported := C.rep_supported
  potential_supported := C.potential_supported
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval := C.incCur_eval
  span_exec := C.span_exec
  setup_exec := C.setup_exec
  step_exec o hr hv harg := by
    obtain ⟨y, n, he, hdec, hrep, hmod, hpot⟩ := C.step_exec o hr hv harg
    exact ⟨y, (D.step _ o).1, (D.step _ o).2, n, he, rfl, hdec, hrep, hmod, hpot⟩

namespace RelSubroutineDS

variable {B B' : Basis} {r_ds r_caller k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : Stateful.RelSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Total instruction bound for `P.initFresh`. -/
def initTime (C : RelSubroutineDS P D w base params s₀) : ℕ :=
  C.spanTime + C.setupTime

/-! ### Projection 1: Basis lifting and standalone `RelDynamicProgram` / `Stateful` theorems -/

/-- Lift a `RelSubroutineDS` certificate along any defined-evaluation basis simulation. -/
def mapSimulates (φ : B.Simulates B') (C : RelSubroutineDS P D w base params s₀) :
    RelSubroutineDS (P.mapSimulates φ) D w base params s₀ where
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  initPotential := C.initPotential
  charge := C.charge
  rep := C.rep
  potential := C.potential
  encode := C.encode
  argMatch := C.argMatch
  decode := C.decode
  bounded := C.bounded
  arguments_fit := C.arguments_fit
  encode_matches := C.encode_matches
  rep_supported := C.rep_supported
  potential_supported := C.potential_supported
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval h1 hfit := Op.eval_mapSimulates_of_some φ (C.incCur_eval h1 hfit)
  span_exec hx hf hp :=
    let ⟨x₁, he, hm, hb, hfr, hpar⟩ := C.span_exec hx hf hp
    ⟨x₁, he.mapSimulates φ, hm, hb, hfr, hpar⟩
  setup_exec hx₁ hb hfr hpar hz :=
    let ⟨y, he, hfr', hrep, hpot, hmod⟩ := C.setup_exec hx₁ hb hfr hpar hz
    ⟨y, he.mapSimulates φ, hfr', hrep, hpot, hmod⟩
  step_exec o hr hv harg :=
    let ⟨y, s', a, n, he, hstep, hdec, hrep, hmod, hpot⟩ := C.step_exec o hr hv harg
    ⟨y, s', a, n, he.mapSimulates φ, hstep, hdec, hrep, hmod, hpot⟩

/-- Lift an exact-basis `RelSubroutineDS` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : RelSubroutineDS P D w base params s₀) :
    RelSubroutineDS P.toStandard D w base params s₀ :=
  C.mapSimulates .exactStandard

section Standard

variable {P_std : SubroutineCode .standard r_ds k_init}
  (C : RelSubroutineDS P_std D w base params s₀)

/-- Project a `.standard`-basis `RelSubroutineDS` to a standalone `RelDynamicProgram`. -/
def toRelDynamicProgram : RelDynamicProgram D r_ds where
  code := P_std.code
  output := P_std.output
  input := P_std.input
  encode := C.encode
  decode := C.decode

/-- Project a `.standard`-basis `RelSubroutineDS` to a standalone `RelDynamicCertificate`. -/
def toRelCertificate : RelDynamicCertificate C.toRelDynamicProgram w where
  rep := C.rep
  bounded := C.bounded
  arguments_fit := C.arguments_fit
  execute {s x} o hr hv := by
    have hb' : (C.toRelDynamicProgram.prepare o x).Bounded w :=
      C.toRelDynamicProgram.prepare_bounded (C.bounded hr) (C.arguments_fit o hv)
    have hr' : C.rep s (C.toRelDynamicProgram.prepare o x) :=
      C.rep_supported
        (fun i hi => C.toRelDynamicProgram.prepare_regs_of_not_input hi o x)
        (fun _ _ => rfl) hb' hr
    have harg : C.argMatch o (C.toRelDynamicProgram.prepare o x).regs :=
      C.encode_matches o x.regs
    obtain ⟨y, s', a, n, he, hstep, hdec, hrep, _, _⟩ := C.step_exec o hr' hv harg
    exact ⟨y, s', a, n, he, hstep, hdec, hrep⟩

/-- Project a `.standard`-basis `RelSubroutineDS` to a standalone `Stateful.RelAmortized`
certificate, charging `+ 1` per operation for `RelDynamicProgram`'s trailing `halt` instruction. -/
theorem toRelAmortized :
    Stateful.RelAmortized C.toRelCertificate.realization
      DynamicProgram.OperationTrace.instructions
      (fun _ x => C.potential x)
      (fun s o => C.charge s o + 1) where
  step {s x o a y trace} hr hv he := by
    have hb' : (C.toRelDynamicProgram.prepare o x).Bounded w :=
      C.toRelDynamicProgram.prepare_bounded (C.bounded hr) (C.arguments_fit o hv)
    have hr' : C.rep s (C.toRelDynamicProgram.prepare o x) :=
      C.rep_supported
        (fun i hi => C.toRelDynamicProgram.prepare_regs_of_not_input hi o x)
        (fun _ _ => rfl) hb' hr
    have hp_eq : C.potential (C.toRelDynamicProgram.prepare o x) = C.potential x :=
      C.potential_supported
        (fun i hi => C.toRelDynamicProgram.prepare_regs_of_not_input hi o x)
        (fun _ _ => rfl) hr
    have harg : C.argMatch o (C.toRelDynamicProgram.prepare o x).regs :=
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

/-- Alias for `toRelAmortized` matching `SubroutineDS.toAmortized`. -/
abbrev toAmortized := @toRelAmortized

/-- When `C.potential` is identically zero, `RelSubroutineDS` projects directly to a worst-case
`Stateful.RelBound` certificate. -/
theorem toRelBound (hpot : ∀ x, C.potential x = 0) :
    Stateful.RelBound C.toRelCertificate.realization
      DynamicProgram.OperationTrace.instructions
      (fun s o => C.charge s o + 1) := by
  intro s x o a y trace hr hv he
  obtain ⟨_, _, _, h⟩ := C.toRelAmortized.step hr hv he
  simp only [hpot] at h
  omega

/-- Alias for `toRelBound` matching `SubroutineDS.toBound`. -/
abbrev toBound := @toRelBound

/-- Standalone adaptive-client amortized bound for any demonically admissible client `p`. -/
theorem run_client_amortized {α : Type*} (p : D.Client α) {s : D.State} {x : Data r_ds}
    (hr : C.rep s x) (hv : D.DemonicValid s p) :
    ∃ a y traces s' tr,
      Stateful.RelExecutes (C.toRelDynamicProgram.ExecOp w) p x a y traces ∧
      D.ClientRun s p a s' tr ∧
      C.rep s' y ∧
      traces.length = tr.length ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces + C.potential y ≤
        D.totalCost (fun s o => C.charge s o + 1) s tr + C.potential x :=
  C.toRelAmortized.run_client_amortized p hr hv

/-- Standalone adaptive-client worst-case bound when `C.potential` is identically zero. -/
theorem run_client_bound (hpot : ∀ x, C.potential x = 0) {α : Type*} (p : D.Client α)
    {s : D.State} {x : Data r_ds} (hr : C.rep s x) (hv : D.DemonicValid s p) :
    ∃ a y traces s' tr,
      Stateful.RelExecutes (C.toRelDynamicProgram.ExecOp w) p x a y traces ∧
      D.ClientRun s p a s' tr ∧
      C.rep s' y ∧
      traces.length = tr.length ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        D.totalCost (fun s o => C.charge s o + 1) s tr :=
  Stateful.RelBound.exists_executes (C.toRelBound hpot) p hr hv

end Standard

/-! ### Projection 2: Fresh `O(1)` initialization and register relocation -/

/-- Execute `P.initFresh` on zeroed `[base, base + C.space)` in `C.initTime` instructions. -/
theorem initFresh_exec (C : RelSubroutineDS P D w base params s₀) {x : Data r_ds}
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ y, ExecWithin w P.initFresh x y C.initTime ∧
      y.regs P.frontierReg = base + C.space ∧
      C.rep s₀ y ∧
      C.potential y ≤ C.initPotential ∧
      Modifies (Block.mk base C.space).footprint x.mem y.mem := by
  obtain ⟨x₁, he₁, hm₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  have hx₁ : x₁.Bounded w := he₁.bounded hx
  have hz₁ : ∀ a ∈ (Block.mk base C.space).footprint, x₁.mem a = 0 := by
    intro a ha
    rw [hm₁]
    exact hz a ha
  obtain ⟨y, he₂, hfr₂, hrep, hpot, hmod⟩ := C.setup_exec hx₁ hb₁ hfr₁ hpar₁ hz₁
  rw [hm₁] at hmod
  exact ⟨y, he₁.seq he₂, hfr₂, hrep, hpot, hmod⟩

/-- Relocated `O(1)` fresh initialization along any injective register embedding `f`. -/
theorem initFresh_rename (C : RelSubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective) {x : Data r_caller}
    (hx : (x.comap f).Bounded w) (hfr : x.regs (f P.frontierReg) = base)
    (hpar : ∀ j, x.regs (f (P.initParams j)) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ z, ExecWithin w (P.initFresh.rename f) x z C.initTime ∧
      z.regs (f P.frontierReg) = base + C.space ∧
      C.rep s₀ (z.comap f) ∧
      C.potential (z.comap f) ≤ C.initPotential ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) := by
  obtain ⟨y, he, hfr', hrep, hpot, hmod⟩ := C.initFresh_exec hx hfr hpar hz
  refine ⟨y.extend f x, he.rename hf, ?_, ?_, ?_, hmod,
    fun j hj => Data.extend_regs_of_notMem y x hj⟩
  · change ((y.extend f x).comap f).regs P.frontierReg = base + C.space
    rw [Data.comap_extend hf]
    exact hfr'
  · rw [Data.comap_extend hf]
    exact hrep
  · rw [Data.comap_extend hf]
    exact hpot

/-! ### Projection 3: Generic `O(space)` dirty-memory initialization (`initClear`) -/

/-- Auxiliary deterministic `SubroutineDS` sharing `C`'s initialization fields so
`zeroFillCode_exec` is reused without duplicating its loop proof. -/
private def toInitSubroutineDS (C : RelSubroutineDS P D w base params s₀) :
    SubroutineDS P
      { State := PUnit.{1}, Op := PUnit.{1}, Result := fun _ => PUnit.{1},
        step := fun _ _ => (⟨⟩, ⟨⟩), valid := fun _ _ => False }
      w base params ⟨⟩ where
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  initPotential := C.initPotential
  charge _ _ := 0
  rep _ x := C.rep s₀ x
  potential := C.potential
  encode _ _ := 0
  argMatch _ _ := True
  decode _ _ := some ⟨⟩
  bounded := C.bounded
  rep_unique _ _ := rfl
  arguments_fit _ hv := False.elim hv
  encode_matches _ _ := trivial
  rep_supported := C.rep_supported
  potential_supported := C.potential_supported
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval := C.incCur_eval
  span_exec := C.span_exec
  setup_exec := C.setup_exec
  step_exec _ _ hv := False.elim hv

/-- Generic execution of `P.zeroFillCode` clearing `[base, base + C.space)` in `4 * C.space + 6`
instructions over any basis `B`. -/
theorem zeroFillCode_exec (C : RelSubroutineDS P D w base params s₀) {x₁ : Data r_ds}
    (hx₁ : x₁.Bounded w) (hb₁ : x₁.regs P.baseReg = base)
    (hfr₁ : x₁.regs P.frontierReg = base + C.space)
    (hpar₁ : ∀ j, x₁.regs (P.initParams j) = params j) :
    ∃ x₂, ExecWithin w P.zeroFillCode x₁ x₂ (4 * C.space + 6) ∧
      x₂.Bounded w ∧
      x₂.regs P.baseReg = base ∧
      x₂.regs P.frontierReg = base + C.space ∧
      (∀ j, x₂.regs (P.initParams j) = params j) ∧
      (∀ a ∈ (Block.mk base C.space).footprint, x₂.mem a = 0) ∧
      Modifies (Block.mk base C.space).footprint x₁.mem x₂.mem :=
  C.toInitSubroutineDS.zeroFillCode_exec hx₁ hb₁ hfr₁ hpar₁

/-- Execute `P.initClear` on arbitrary dirty memory in `C.initTime + 4 * C.space + 6`
instructions. -/
theorem initClear_exec (C : RelSubroutineDS P D w base params s₀) {x : Data r_ds}
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j) :
    ∃ y, ExecWithin w P.initClear x y (C.initTime + 4 * C.space + 6) ∧
      y.regs P.frontierReg = base + C.space ∧
      C.rep s₀ y ∧
      C.potential y ≤ C.initPotential ∧
      Modifies (Block.mk base C.space).footprint x.mem y.mem := by
  obtain ⟨x₁, he₁, hm₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  obtain ⟨x₂, he₂, hx₂, hb₂, hfr₂, hpar₂, hz₂, hmod₂⟩ :=
    C.zeroFillCode_exec (he₁.bounded hx) hb₁ hfr₁ hpar₁
  obtain ⟨y, he₃, hfr₃, hrep, hpot, hmod₃⟩ := C.setup_exec hx₂ hb₂ hfr₂ hpar₂ hz₂
  rw [hm₁] at hmod₂
  have hmod : Modifies (Block.mk base C.space).footprint x.mem y.mem := by
    simpa only [Finset.union_idempotent] using hmod₂.trans hmod₃
  exact ⟨y, (he₁.seq (he₂.seq he₃)).mono (by unfold initTime; omega), hfr₃, hrep, hpot, hmod⟩

/-- Relocated `O(space)` dirty-memory initialization along any injective register embedding `f`. -/
theorem initClear_rename (C : RelSubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective) {x : Data r_caller}
    (hx : (x.comap f).Bounded w) (hfr : x.regs (f P.frontierReg) = base)
    (hpar : ∀ j, x.regs (f (P.initParams j)) = params j) :
    ∃ z, ExecWithin w (P.initClear.rename f) x z (C.initTime + 4 * C.space + 6) ∧
      z.regs (f P.frontierReg) = base + C.space ∧
      C.rep s₀ (z.comap f) ∧
      C.potential (z.comap f) ≤ C.initPotential ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) := by
  obtain ⟨y, he, hfr', hrep, hpot, hmod⟩ := C.initClear_exec hx hfr hpar
  refine ⟨y.extend f x, he.rename hf, ?_, ?_, ?_, hmod,
    fun j hj => Data.extend_regs_of_notMem y x hj⟩
  · change ((y.extend f x).comap f).regs P.frontierReg = base + C.space
    rw [Data.comap_extend hf]
    exact hfr'
  · rw [Data.comap_extend hf]
    exact hrep
  · rw [Data.comap_extend hf]
    exact hpot

/-! ### Projection 4: Relocated inline subroutine calls (`code_rename`, `call_rename`) -/

/-- Execute `P.code.rename f` inline when arguments already match `(x.comap f).regs`,
witnessing a permitted outcome `(s', a)` with `D.step s o s' a`. -/
theorem code_rename (C : RelSubroutineDS P D w base params s₀)
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
theorem call_rename (C : RelSubroutineDS P D w base params s₀)
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

/-! ### Projection 5: Caller-to-DS bidirectional framing (`frame_caller`) -/

/-- Any caller state transition that preserves `(x'.comap f).Bounded w`, leaves persistent DS
registers (`P.input i = false`) unchanged, and writes only to a set `F` disjoint from
`[base, base + C.space)` preserves both `C.rep s (x'.comap f)` and `C.potential (x'.comap f)`. -/
theorem frame_caller (C : RelSubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} {s : D.State} {x x' : Data r_caller} {F : Finset ℕ}
    (hr : C.rep s (x.comap f))
    (hb' : (x'.comap f).Bounded w)
    (hreg : ∀ i, P.input i = false → x'.regs (f i) = x.regs (f i))
    (hdisj : Disjoint (Block.mk base C.space).footprint F)
    (hmem : Modifies F x.mem x'.mem) :
    C.rep s (x'.comap f) ∧ C.potential (x'.comap f) = C.potential (x.comap f) := by
  have hag : ∀ a ∈ (Block.mk base C.space).footprint, x'.mem a = x.mem a := fun a ha =>
    hmem a (fun hf => Finset.disjoint_left.mp hdisj ha hf)
  exact ⟨C.rep_supported (x := x.comap f) (x' := x'.comap f) hreg hag hb' hr,
    C.potential_supported (x := x.comap f) (x' := x'.comap f) hreg hag hr⟩

/-! ### Projection 6: Flat-program operation-sequence execution (`RunsRelOps`, `run_ops_exact_*`) -/

/-- Default register-preparation function overwriting `P.input` registers with `C.encode o`. -/
def prepareRegs (C : RelSubroutineDS P D w base params s₀) (o : D.Op)
    (regs : Fin r_ds → ℕ) : Fin r_ds → ℕ :=
  fun i => if P.input i then C.encode o i else regs i

/-- Sequential flat-program execution of `ops : List D.Op` by repeated calls to `P.opProg`:
each call prepares input registers via `prepRegs`, runs `P.opProg` from `pc = 0` to `halt`,
decodes a permitted outcome `(s₁, a)` with `D.step s o s₁ a`, modifies memory only within
`[base, base + C.space)`, records the resulting transcript `tr : D.Transcript`, and accumulates
total instructions executed (including each trailing `halt`). -/
inductive RunsRelOps (C : RelSubroutineDS P D w base params s₀)
    (prepRegs : D.Op → (Fin r_ds → ℕ) → (Fin r_ds → ℕ) := C.prepareRegs) :
    D.State → Data r_ds → List D.Op → D.Transcript → D.State → Data r_ds → ℕ → Prop
  | nil {s x} : RunsRelOps C prepRegs s x [] [] s x 0
  | cons {s s₁ s₂ x o a ops tr pc y z steps rest} :
      Runs w P.opProg ⟨0, ⟨prepRegs o x.regs, x.mem⟩⟩ ⟨pc, y⟩ steps →
      (∃ out, step w P.opProg ⟨pc, y⟩ = .halt out) →
      D.step s o s₁ a →
      C.decode o y.regs = some a →
      Modifies (Block.mk base C.space).footprint x.mem y.mem →
      RunsRelOps C prepRegs s₁ y ops tr s₂ z rest →
      RunsRelOps C prepRegs s x (o :: ops) (⟨o, a, s₁⟩ :: tr) s₂ z ((steps + 1) + rest)

private theorem step_program_halt (c : Code B r_ds) (out : Fin r_ds) (y : Data r_ds) :
    step w (c.program out) ⟨0 + c.size, y⟩ = .halt (y.regs out) :=
  step_halt (by
    simp only [Code.program, Nat.zero_add,
      List.getElem?_append_right (Code.length_assemble c 0).le,
      Code.length_assemble, Nat.sub_self, List.getElem?_cons_zero])

/-- Flat-program sequence execution under a custom register-preparation function `prepRegs`. -/
theorem seq_runsRelOps_of_prep (C : RelSubroutineDS P D w base params s₀)
    (prepRegs : D.Op → (Fin r_ds → ℕ) → (Fin r_ds → ℕ))
    (hfit : ∀ {s} (o) (regs : Fin r_ds → ℕ), D.valid s o → (∀ i, Fits w (regs i)) →
      ∀ i, Fits w (prepRegs o regs i))
    (hnot_in : ∀ (o : D.Op) (regs : Fin r_ds → ℕ) (i : Fin r_ds),
      P.input i = false → prepRegs o regs i = regs i)
    (harg : ∀ (o : D.Op) (regs : Fin r_ds → ℕ), C.argMatch o (prepRegs o regs)) :
    ∀ (ops : List D.Op) {s : D.State} {x : Data r_ds},
      C.rep s x → D.ValidOpSeq s ops →
      ∃ tr s_fin z t_ops,
        C.RunsRelOps prepRegs s x ops tr s_fin z t_ops ∧
        tr.ops = ops ∧
        D.ValidTranscript s tr s_fin ∧
        C.rep s_fin z ∧
        t_ops + C.potential z ≤
          D.totalCost (fun st o => C.charge st o + 1) s tr + C.potential x
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
      seq_runsRelOps_of_prep C prepRegs hfit hnot_in harg ops hr_y (hv_rest s₁ a hstep)
    refine ⟨⟨o, a, s₁⟩ :: tr, s_fin, z, (m + 1) + rest,
      .cons hruns ⟨_, hhalt⟩ hstep hdec hmod hrest,
      congrArg (o :: ·) hops, .cons _ hv_o hstep htr, hr_z, ?_⟩
    simp only [Stateful.RelSpec.totalCost_cons]
    omega

/-- Flat-program sequence execution using `C.prepareRegs`. -/
theorem seq_runsRelOps (C : RelSubroutineDS P D w base params s₀)
    (ops : List D.Op) {s : D.State} {x : Data r_ds}
    (hr : C.rep s x) (hv : D.ValidOpSeq s ops) :
    ∃ tr s_fin z t_ops,
      C.RunsRelOps C.prepareRegs s x ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s tr s_fin ∧
      C.rep s_fin z ∧
      t_ops + C.potential z ≤
        D.totalCost (fun st o => C.charge st o + 1) s tr + C.potential x := by
  refine C.seq_runsRelOps_of_prep C.prepareRegs ?_ ?_ C.encode_matches ops hr hv
  · intro s' o regs hv_o hregs i
    simp only [prepareRegs]
    split_ifs with hi
    · exact C.arguments_fit o hv_o i hi
    · exact hregs i
  · intro o regs i hi
    simp [prepareRegs, hi]

/-- Standalone flat-program operation-sequence theorem with `O(1)` fresh initialization on zeroed
`[base, base + C.space)`. -/
theorem run_ops_exact_fresh (C : RelSubroutineDS P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hzero : ∀ a ∈ (Block.mk base C.space).footprint, d₀.mem a = 0)
    (ops : List D.Op) (hv : D.ValidOpSeq s₀ ops) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w P.initFreshProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsRelOps C.prepareRegs s₀ x₀ ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s₀ tr s_fin ∧
      C.rep s_fin z ∧
      t_init ≤ C.initTime ∧
      t_ops + C.potential z ≤
        D.totalCost (fun st o => C.charge st o + 1) s₀ tr + C.initPotential := by
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hr₀, hpot₀, hmod₀⟩ :=
    C.initFresh_exec hd₀ hfr hpar hzero
  have hruns₀ : Runs w P.initFreshProg ⟨0, d₀⟩ ⟨0 + P.initFresh.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := P.initFreshProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w P.initFreshProg ⟨0 + P.initFresh.size, x₀⟩ = .halt (x₀.regs P.output) :=
    step_program_halt P.initFresh P.output x₀
  obtain ⟨tr, s_fin, z, t_ops, hruns_ops, hops, htr, hr_z, hbound⟩ :=
    C.seq_runsRelOps ops hr₀ hv
  exact ⟨_, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops,
    hops, htr, hr_z, ht_init, by omega⟩

/-- Standalone flat-program operation-sequence theorem with `O(space)` reusable initialization on
arbitrary `w`-bounded memory. -/
theorem run_ops_exact_reusable (C : RelSubroutineDS P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (ops : List D.Op) (hv : D.ValidOpSeq s₀ ops) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w P.initClearProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsRelOps C.prepareRegs s₀ x₀ ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s₀ tr s_fin ∧
      C.rep s_fin z ∧
      t_init ≤ C.initTime + 4 * C.space + 6 ∧
      t_ops + C.potential z ≤
        D.totalCost (fun st o => C.charge st o + 1) s₀ tr + C.initPotential := by
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hr₀, hpot₀, hmod₀⟩ :=
    C.initClear_exec hd₀ hfr hpar
  have hruns₀ : Runs w P.initClearProg ⟨0, d₀⟩ ⟨0 + P.initClear.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := P.initClearProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w P.initClearProg ⟨0 + P.initClear.size, x₀⟩ = .halt (x₀.regs P.output) :=
    step_program_halt P.initClear P.output x₀
  obtain ⟨tr, s_fin, z, t_ops, hruns_ops, hops, htr, hr_z, hbound⟩ :=
    C.seq_runsRelOps ops hr₀ hv
  exact ⟨_, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops,
    hops, htr, hr_z, ht_init, by omega⟩

end RelSubroutineDS

end Cslib.WordRAM
