/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Compile
public import Complexity.DataStructure.StateTransition.Resource
public import Complexity.Computability.WordRAM.Trace

/-!
# Fixed-program implementations of dynamic data structures

`DynamicProgram` depends only on the existing `PFunctor` operation signature and its instruction
basis, which defaults to `.standard`. Deterministic and relational specifications supply their
signatures by coercion; correctness certificates retain the actual specification separately.

An implementation has one structured program, one output register, and a register-only calling
convention. Each call replaces designated input registers with encoded words, preserving all
other registers and the entire memory. Argument encoding, external delivery, and result decoding
are not charged; all
instructions of the operation, including its final `halt`, are charged. Initialization is a
separate obligation expressed by the initial representation hypothesis. Argument encoding
depends on the requested operation, without access to the maintained machine data.

Certificates require bounded configurations and bounded arguments, and a successful exact
machine execution for every admissible operation. Determinism supplies correctness for every
execution. The generic history theorem then preserves all observations and adds actual costs.
The same single compiled program is used at every call; the interface does not generate code
from the requested operation.

## Evaluating calls

`P.eval w fuel o x` delivers the arguments, runs the fixed program and decodes the operation's
typed observation. It returns `some (y, answer, cost)`, with final data `y` for the next call and
a cost that already includes halt. `fuel` bounds each structured loop's iterations per entry,
not the total instruction count. Exhaustion, a machine fault or decoder rejection returns
outer `none`; a successful empty stack pop instead has observation `none`.

Evaluation does not establish admissibility or check untouched memory for word bounds.
`C.execOp_of_eval hr hv he` turns a successful evaluation `he` into exact execution evidence
using representation `hr` and admissibility `hv`. Argument delivery and decoding remain
uncharged. Whole-client bounds remain separate resource proofs.

See the checked examples in ComplexityTests/WordRAMDynamic.lean for typed stack observations,
the seven-body/eight-charged push and certificate lifting, and
ComplexityTests/WordRAMPrefixSums.lean for repeated calls retaining persistent data.

## Main definitions

* `DynamicProgram`, `DynamicProgram.prepare`: fixed code, an input-register convention, an output
  decoder, and argument-delivery state update.
* `DynamicProgram.eval`: typed call evaluation with halt-inclusive instruction cost.
* `DynamicProgram.OperationTrace`, `DynamicProgram.ExecOp`: call trace and execution of a call,
  including the final halt charge.
* `DynamicCertificate`: representation, word bounds, and per-operation semantic machine proofs.

## Main results

* `DynamicProgram.ExecOp.executes`: calls execute the same flat program.
* `DynamicCertificate.execOp_of_eval`: certify an evaluated admissible call.
* `DynamicCertificate.impl`: machine certificates instantiate shared adaptive execution.
* `DynamicCertificate.instruction_bound`: separate native instruction-cost certificates.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM

universe u v z

variable {r : ℕ} {D : DataStructure.StateTransitionSpec.{u, v, z}}

/-- A single program serving an operation signature through a fixed register calling convention.
Deterministic and relational stateful specifications supply their signatures by coercion;
the program itself makes no assumption about abstract states or permitted transitions. -/
structure DynamicProgram (S : PFunctor.{v, z}) (r : ℕ) (B : Basis := .standard) where
  /-- The same code is executed for every operation. -/
  code : Code B r
  /-- Register returned by the final halt instruction. -/
  output : Fin r
  /-- Registers overwritten by externally supplied operation arguments. -/
  input : Fin r → Bool
  /-- Encoded arguments, independent of the maintained machine state. -/
  encode : S.A → Fin r → ℕ
  /-- Interpretation of the final register tuple as the operation's typed observation. -/
  decode : (o : S.A) → (Fin r → ℕ) → Option (S.B o)

namespace DynamicProgram

variable {S : PFunctor.{v, z}} {B : Basis} (P : DynamicProgram S r B)

/-- Deliver operation arguments without changing maintained memory or non-input registers. -/
def prepare (o : S.A) (x : Data r) : Data r where
  regs i := if P.input i then P.encode o i else x.regs i
  mem := x.mem

/-- Delivering operation arguments preserves the machine memory unchanged. -/
@[simp]
theorem prepare_mem (o : S.A) (x : Data r) : (P.prepare o x).mem = x.mem := rfl

/-- Registers outside the calling convention retain their contents. -/
theorem prepare_regs_of_not_input {i : Fin r} (hi : P.input i = false) (o : S.A) (x : Data r) :
    (P.prepare o x).regs i = x.regs i := by
  simp [prepare, hi]

/-- Argument delivery preserves bounded words when the arguments fit. -/
theorem prepare_bounded {w : ℕ} {o : S.A} {x : Data r} (hx : x.Bounded w)
    (ho : ∀ i, P.input i = true → Fits w (P.encode o i)) : (P.prepare o x).Bounded w := by
  refine ⟨fun i => ?_, hx.2⟩
  change Fits w (if P.input i then P.encode o i else x.regs i)
  split
  · exact ho i (by assumption)
  · exact hx.1 i

/-- Evaluate one typed call, delivering its arguments and decoding its observation. The returned
cost includes the final halt. `fuel` bounds iterations of each structured loop per entry, not
instructions; exhaustion, a machine fault, or decoder failure returns `none`.

This interpreter does not check the initial state's global word bound or operation admissibility.
Use `DynamicCertificate.execOp_of_eval` to connect a successful call to certified execution. -/
def eval (w fuel : ℕ) (o : S.A) (x : Data r) : Option (Data r × S.B o × ℕ) :=
  match P.code.eval w fuel (P.prepare o x) with
  | none => none
  | some (y, n) => (P.decode o y.regs).map fun a => (y, a, n + 1)

/-- Native evidence for one call: instruction count including halt and the memory transcript. -/
structure OperationTrace where
  /-- Number of executed machine instructions, including the final halt. -/
  instructions : ℕ
  /-- All reads and writes, in execution order. -/
  probes : List Probe

/-- A bounded machine call with native execution evidence independent of any resource bound. -/
def ExecOp (w : ℕ) : DataStructure.Execution S (Data r) OperationTrace := fun x o a y trace =>
  (P.prepare o x).Bounded w ∧ ∃ n, TraceExec w P.code (P.prepare o x) y n trace.probes ∧
    P.decode o y.regs = some a ∧ trace.instructions = n + 1

/-- Successful typed evaluation supplies an exact operation trace when the delivered state is
bounded. Evaluator success alone does not imply a bound on untouched memory. -/
theorem ExecOp.of_eval {w fuel k : ℕ} {o : S.A} {x y : Data r} {a : S.B o}
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

/-- Every call is an execution of one fixed flat machine program. The returned register tuple
is observed at the final state; the designated output register is also the halt value. -/
theorem ExecOp.executes {w : ℕ} {x y : Data r} {o : S.A} {a : S.B o}
    {trace : OperationTrace} (h : P.ExecOp w x o a y trace) :
    Executes w (P.code.program P.output) ⟨0, P.prepare o x⟩ (y.regs P.output)
      trace.instructions := by
  obtain ⟨_, n, he, _, ht⟩ := h
  rw [ht]
  exact he.exec.executes P.output

/-- A call preserves bounded words, including every word in the observed register tuple. -/
theorem ExecOp.bounded {w : ℕ} {x y : Data r} {o : S.A} {a : S.B o}
    {trace : OperationTrace} (h : P.ExecOp w x o a y trace) : y.Bounded w := by
  obtain ⟨hb, n, he, _, _⟩ := h
  exact he.exec.bounded hb

/-- Calls are deterministic in their final representation, observation, and instruction count. -/
theorem ExecOp.unique {w : ℕ} {x y y' : Data r} {o : S.A} {a a' : S.B o}
    {trace trace' : OperationTrace} (h : P.ExecOp w x o a y trace)
    (h' : P.ExecOp w x o a' y' trace') :
    y = y' ∧ a = a' ∧ trace.instructions = trace'.instructions := by
  obtain ⟨_, n, he, ha, ht⟩ := h
  obtain ⟨_, n', he', ha', ht'⟩ := h'
  obtain ⟨rfl, rfl⟩ := he.exec.unique he'.exec
  exact ⟨rfl, Option.some.inj (ha.symm.trans ha'), ht.trans ht'.symm⟩

/-- A call's final state and instruction count agree with any structured execution of the code. -/
theorem ExecOp.eq_of_exec {P : DynamicProgram S r B} {w : ℕ} {x y z : Data r} {o : S.A}
    {a : S.B o} {trace : OperationTrace} {m : ℕ} (he : P.ExecOp w x o a y trace)
    (h : Exec w P.code (P.prepare o x) z m) :
    y = z ∧ trace.instructions = m + 1 := by
  obtain ⟨_, n, ht, _, hn⟩ := he
  obtain ⟨rfl, rfl⟩ := ht.exec.unique h
  exact ⟨rfl, hn⟩

/-- The write transcript supplies a frame rule for a call, including register-only delivery. -/
theorem ExecOp.frame {w : ℕ} {x y : Data r} {o : S.A} {a : S.B o}
    {trace : OperationTrace} (h : P.ExecOp w x o a y trace) {Q : HeapAssertion}
    (hQ : Q.holds x.mem) (hd : Disjoint Q.footprint (Probe.writes trace.probes)) :
    Q.holds y.mem := by
  obtain ⟨_, n, he, _, _⟩ := h
  exact he.frame hQ hd

end DynamicProgram

/-- Per-operation relational semantic proof obligations tied to fixed bounded-word code.
Performance claims are supplied separately, as `DataStructure.Bound` or `DataStructure.Amortized`
certificates. -/
structure DynamicCertificate (P : DynamicProgram D r) (w : ℕ) where
  /-- Abstract state represented by the persistent machine data. -/
  rep : D.State → Data r → Prop
  /-- Represented configurations contain only machine words. -/
  bounded : ∀ {s x}, rep s x → x.Bounded w
  /-- Admissible arguments fit the machine's word size. -/
  arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (P.encode o i)
  /-- A machine execution implements some permitted outcome `(s', a)` of an admissible
  operation. -/
  execute : ∀ {s x} (o), rep s x → D.valid s o →
    ∃ y s' a n, Exec w P.code (P.prepare o x) y n ∧
      D.step s o s' a ∧ P.decode o y.regs = some a ∧ rep s' y

namespace DynamicCertificate

variable {P : DynamicProgram D r} {w : ℕ} (C : DynamicCertificate P w)

/-- Construct a `DynamicCertificate` for a deterministic specification (`[D.HasStepFn f]`) from a
functional `execute` obligation at `(D.stepFn s o)`. -/
def ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (rep : D.State → Data r → Prop)
    (bounded : ∀ {s x}, rep s x → x.Bounded w)
    (arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (P.encode o i))
    (execute : ∀ {s x} (o), rep s x → D.valid s o →
      ∃ y n, Exec w P.code (P.prepare o x) y n ∧
        P.decode o y.regs = some (D.stepFn s o).2 ∧ rep (D.stepFn s o).1 y) :
    DynamicCertificate P w where
  rep := rep
  bounded := bounded
  arguments_fit := arguments_fit
  execute {s _} o hr hv := by
    obtain ⟨y, n, he, ha, hr'⟩ := execute o hr hv
    exact ⟨y, (D.stepFn s o).1, (D.stepFn s o).2, n, he, D.step_stepFn s o, ha, hr'⟩

/-- A represented state and an admissible operation supply the word bounds needed to turn
typed evaluation into a certified call, including its final halt charge. -/
theorem execOp_of_eval {s : D.State} {x y : Data r} {o : D.Op} {a : D.Result o} {fuel k : ℕ}
    (hr : C.rep s x) (hv : D.valid s o) (h : P.eval w fuel o x = some (y, a, k)) :
    ∃ probes, P.ExecOp w x o a y ⟨k, probes⟩ :=
  DynamicProgram.ExecOp.of_eval P
    (P.prepare_bounded (C.bounded hr) (C.arguments_fit o hv)) h

/-- Fixed-program certificates implement the relational dynamic specification, without choosing a
cost. -/
def impl : DataStructure.StateTransitionImpl D (P.ExecOp w) where
  rep := C.rep
  total o hr hv := by
    obtain ⟨y, _, a, n, he, _, ha, _⟩ := C.execute o hr hv
    obtain ⟨ts, hts⟩ := he.exists_trace
    exact ⟨a, y, ⟨n + 1, ts⟩,
      P.prepare_bounded (C.bounded hr) (C.arguments_fit o hv), n, hts, ha, rfl⟩
  correct {s x o a y trace} hr hv he := by
    obtain ⟨y', s', a', n', he', hstep, ha', hr'⟩ := C.execute o hr hv
    obtain ⟨_, n, ht, ha, _⟩ := he
    obtain ⟨rfl, rfl⟩ := ht.exec.unique he'
    have ha_eq : a = a' := Option.some.inj (ha.symm.trans ha')
    subst ha_eq
    exact ⟨s', hstep, hr'⟩

/-- A separate per-operation instruction estimate supplies a reusable resource certificate. -/
theorem instruction_bound (charge : D.State → D.Op → ℕ)
    (hbound : ∀ {s x} (o) {y n}, C.rep s x → D.valid s o →
      Exec w P.code (P.prepare o x) y n → n + 1 ≤ charge s o) :
    DataStructure.Bound C.impl DynamicProgram.OperationTrace.instructions charge := by
  intro s x o a y trace hr hv he
  obtain ⟨_, n, ht, _, hn⟩ := he
  rw [hn]
  exact hbound o hr hv ht.exec

/-- A uniform constant instruction bound follows from an existential per-operation execution. -/
theorem instruction_bound_const (K : ℕ)
    (hbound : ∀ {s x} (o), C.rep s x → D.valid s o →
      ∃ y n, Exec w P.code (P.prepare o x) y n ∧ n + 1 ≤ K) :
    DataStructure.Bound C.impl DynamicProgram.OperationTrace.instructions (fun _ _ => K) := by
  apply C.instruction_bound
  intro s x o y n hr hv he
  obtain ⟨z, m, he', hn⟩ := hbound o hr hv
  obtain ⟨_, rfl⟩ := he.unique he'
  exact hn

/-- Adaptive client execution, final representation, and linear total instruction bound for a
uniform constant per-operation instruction certificate on a deterministic specification. -/
theorem run_client_const
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {K : ℕ}
    (B : DataStructure.Bound C.impl DynamicProgram.OperationTrace.instructions (fun _ _ => K))
    {α : Type*} (p : D.Client α) {s : D.State} {x : Data r}
    (hr : C.rep s x) (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ y traces, DataStructure.Executes (P.ExecOp w) p x (D.clientResult s p) y traces ∧
      C.rep (D.clientState s p) y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
        (D.clientHistory s p).length * K :=
  B.exists_executes_const p hr hv

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
theorem executes_demonic_frame {j : ℕ}
    (hframe : ∀ {s x y o a trace}, C.rep s x → D.valid s o →
      P.ExecOp w x o a y trace → y.mem j = x.mem j)
    {α : Type*} {p : D.Client α} {s : D.State} {x y : Data r} {val : α}
    {traces : List DynamicProgram.OperationTrace}
    (hr : C.rep s x) (hv : D.DemonicValid s p)
    (he : DataStructure.Executes (P.ExecOp w) p x val y traces) :
    y.mem j = x.mem j := by
  induction he generalizing s with
  | pure _ _ => rfl
  | @call o k x res x₁ trace _ _ _ hstep _ ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    obtain ⟨s₁, hstep_s, hr₁⟩ := C.impl.correct hr hv_o hstep
    exact (ih hr₁ (hv_k s₁ res hstep_s)).trans (hframe hr hv_o hstep)

/-- Lift a per-operation `Modifies` bound across a demonically admissible adaptive client
execution. -/
theorem executes_demonic_modifies {F : Finset ℕ}
    (hmod : ∀ {s x y o a trace}, C.rep s x → D.valid s o →
      P.ExecOp w x o a y trace → Modifies F x.mem y.mem)
    {α : Type*} {p : D.Client α} {s : D.State} {x y : Data r} {val : α}
    {traces : List DynamicProgram.OperationTrace}
    (hr : C.rep s x) (hv : D.DemonicValid s p)
    (he : DataStructure.Executes (P.ExecOp w) p x val y traces) :
    Modifies F x.mem y.mem :=
  fun j hj => C.executes_demonic_frame
    (fun hr' hv' he' => hmod hr' hv' he' j hj) hr hv he

/-- Lift a per-operation pointwise memory frame across an adaptive client execution on a
deterministic specification. -/
theorem executes_client_frame
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {j : ℕ}
    (hframe : ∀ {s x y o a trace}, C.rep s x → D.valid s o →
      P.ExecOp w x o a y trace → y.mem j = x.mem j)
    {α : Type*} {p : D.Client α} {s : D.State} {x y : Data r} {val : α}
    {traces : List DynamicProgram.OperationTrace}
    (hr : C.rep s x) (hv : D.ValidHistory s (D.clientHistory s p))
    (he : DataStructure.Executes (P.ExecOp w) p x val y traces) :
    y.mem j = x.mem j :=
  C.executes_demonic_frame hframe hr
    ((D.demonicValid_iff_validHistory_runClient s p).mpr hv) he

/-- Lift a per-operation `Modifies` bound across an adaptive client execution on a deterministic
specification. -/
theorem executes_client_modifies
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {F : Finset ℕ}
    (hmod : ∀ {s x y o a trace}, C.rep s x → D.valid s o →
      P.ExecOp w x o a y trace → Modifies F x.mem y.mem)
    {α : Type*} {p : D.Client α} {s : D.State} {x y : Data r} {val : α}
    {traces : List DynamicProgram.OperationTrace}
    (hr : C.rep s x) (hv : D.ValidHistory s (D.clientHistory s p))
    (he : DataStructure.Executes (P.ExecOp w) p x val y traces) :
    Modifies F x.mem y.mem :=
  C.executes_demonic_modifies hmod hr
    ((D.demonicValid_iff_validHistory_runClient s p).mpr hv) he

/-- The same native evidence separately bounds memory probes by the instruction charge. -/
theorem probe_bound (charge : D.State → D.Op → ℕ)
    (B : DataStructure.Bound C.impl DynamicProgram.OperationTrace.instructions charge) :
    DataStructure.Bound C.impl (fun t => t.probes.length) charge := by
  intro s x o a y trace hr hv he
  have hb := B hr hv he
  obtain ⟨_, n, ht, _, hn⟩ := he
  exact ht.length_le.trans ((Nat.le_add_right n 1).trans (hn ▸ hb))

end DynamicCertificate

end Cslib.WordRAM
