/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.FrameMachines
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelAppend
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelComp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelZeroSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bound
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Correct
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Logic.Equiv.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Named native compiler witnesses

This internal module retains actual deterministic machine terms through a small construction
kernel. `NativeCompiler` is data, not a second computability predicate: it packages a finite-state
machine, its state encoding, independent time and workspace maps, and a tidy computation proof.
`NativeCompiler.computesInTimeAndSpace` exposes the recorded machine to plain consumers, while
`NativeCompiler.computableInTimeAndSpace` forgets it into the existing existential predicate.

The resource coordinates stay componentwise. `NativeCompiler.staticBits` is the exact encoded
length of the compiler machine; `NativeCompiler.inputBits` and `NativeCompiler.outputBits` are the
exact encoded source and emitted-result lengths; `time` and `workspace` apply only when that
machine is executed.
In particular, using a precompiled result does not pay compiler runtime, but a result used as code
still carries its `outputBits` program-size charge. No scalar total is built into this kernel.

The constructors use the existing machine combinators directly. In particular, they do not select
a machine from `ComputableInPolyTime`, `ComputableInO`, `ComputableInDegree`, or a normal-form
existence theorem. Their resource formulas retain the constants of those combinators. The exact
static program charge is `NativeCompiler.staticBits`, the `eDesc` length of the packaged machine
under its recorded state encoding.

The constructors assemble fixed machine terms at the proof level; they are not a free dynamic code
generator. The functions and encodings in their types specify behavior and resource expressions,
not callbacks executed outside the packaged machine. A compiler that receives descriptions at
runtime must itself be a `NativeCompiler` whose machine performs that encoded transformation.

This is a bounded internal prerequisite for concrete compilers. It does not claim that an arbitrary
existential computability proof can be extracted into a `NativeCompiler`.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler`: a named native machine and resource certificate.
* `Turing.MultiTapeTM.Internal.NativeCompiler.staticBits`: exact encoded compiler-machine length.
* `Turing.MultiTapeTM.Internal.NativeCompiler.inputBits`: exact encoded input length.
* `Turing.MultiTapeTM.Internal.NativeCompiler.outputBits`: exact encoded output length.
* `Turing.MultiTapeTM.Internal.NativeCompiler.identity`: the copy-and-rewind machine.
* `Turing.MultiTapeTM.Internal.NativeCompiler.const`: a named constant-output machine.
* `Turing.MultiTapeTM.Internal.NativeCompiler.comp`: direct machine composition.
* `Turing.MultiTapeTM.Internal.NativeCompiler.pair`: direct standard-pair construction.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.description_eq_desc`: identify the recorded
  description with the universal description of the packaged machine.
* `Turing.MultiTapeTM.Internal.NativeCompiler.computableInTimeAndSpace`: forget the named
  construction into the existing plain existential calculus.
-/

public section

namespace Turing.MultiTapeTM.Internal

open Universal

/-- A named finite-state native machine computing `f`, with independent exact-form resource maps.
This is internal construction data, not a parallel public computability calculus. -/
structure NativeCompiler {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) where
  /-- Number of work tapes of the named machine. -/
  tapeCount : ℕ
  /-- Finite control-state type of the named machine. -/
  State : Type
  /-- The control-state type is explicitly finite. -/
  [stateFintype : Fintype State]
  /-- The actual deterministic machine term. -/
  machine : MultiTapeTM tapeCount Bool State
  /-- State encoding used for the exact universal description. -/
  stateEncoding : State ↪ ℕ
  /-- Native time bound when this machine is executed, kept separate from workspace. -/
  time : α → ℕ
  /-- Native workspace bound when this machine is executed, kept separate from time. -/
  workspace : α → ℕ
  /-- Direct tidy computation certificate for the named machine. -/
  computes : ∀ a, machine.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a))
    (time a) (workspace a)

namespace NativeCompiler

/-- Constructive disjoint-union encoding used by the core constructors. -/
@[expose] def sumStateEncoding {S₁ S₂ : Type} (left : S₁ ↪ ℕ) (right : S₂ ↪ ℕ) :
    S₁ ⊕ S₂ ↪ ℕ :=
  (left.sumMap right).trans Equiv.natSumNatEquivNat.toEmbedding

/-- Constructive product encoding used by the core constructors. -/
@[expose] def prodStateEncoding {S₁ S₂ : Type} (left : S₁ ↪ ℕ) (right : S₂ ↪ ℕ) :
    S₁ × S₂ ↪ ℕ :=
  (left.prodMap right).trans Nat.pairEquiv.toEmbedding

/-- Constructive optional-state encoding used by the core constructors. -/
@[expose] def optionStateEncoding {S : Type} (state : S ↪ ℕ) : Option S ↪ ℕ :=
  (Equiv.optionEquivSumPUnit S).toEmbedding.trans
    (sumStateEncoding state (Function.Embedding.punit 0))

/-- The unique unit state is encoded as zero. -/
@[expose] def unitStateEncoding : Unit ↪ ℕ :=
  ⟨fun _ => 0, by intro a b _; cases a; cases b; rfl⟩

/-- Explicit encoding of the input-rewinding states. -/
@[expose] def rewindStateEncoding : RewindState ↪ ℕ :=
  ⟨fun q => match q with | .start => 0 | .walk => 1,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- Explicit encoding of the work-tape-rewinding states. -/
@[expose] def rewindWorkStateEncoding : RewindWorkState ↪ ℕ :=
  ⟨fun q => match q with | .start => 0 | .scan => 1,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- Explicit encoding of the work-tape-marking states. -/
@[expose] def markWorkStateEncoding : MarkWorkState ↪ ℕ :=
  ⟨fun q => match q with | .start => 0 | .put => 1,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- The exact universal description of the named machine. -/
@[expose] noncomputable def description {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) : Desc := by
  letI := compiler.stateFintype
  exact desc compiler.stateEncoding eBit compiler.machine

/-- The recorded description is the universal description of the packaged machine under its
recorded state encoding. -/
theorem description_eq_desc {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) :
    compiler.description =
      @desc compiler.tapeCount Bool compiler.State compiler.stateFintype inferInstance
        compiler.stateEncoding eBit compiler.machine :=
  rfl

/-- Exact length of the compiler input under its recorded encoding. This is a separate resource
coordinate, not runtime charged merely for presenting an already encoded input. -/
@[expose] def inputBits {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (_compiler : NativeCompiler f encIn encOut) (a : α) : ℕ :=
  (encIn a).length

/-- Exact length of the compiler output under its recorded encoding. When the output is executable
code, this is its emitted program-size charge even if compilation itself is offline. -/
@[expose] def outputBits {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (_compiler : NativeCompiler f encIn encOut) (a : α) : ℕ :=
  (encOut (f a)).length

/-- Exact unary-model static program length of the named machine. -/
@[expose] noncomputable def staticBits {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) : ℕ :=
  descLen compiler.description

/-- The static program charge is definitionally the length of the recorded description. -/
theorem staticBits_eq_descLen {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) :
    compiler.staticBits = descLen compiler.description :=
  rfl

/-- Forget tidiness while retaining the same named machine and independent bounds. -/
theorem computesInTimeAndSpace {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) :
    compiler.machine.ComputesFunInTimeAndSpace encIn encOut f compiler.time
      compiler.workspace :=
  fun a => (compiler.computes a).computesInTimeAndSpace

/-- Forget the construction data into the existing plain existential computability predicate.
This direction packages the recorded machine; it does not extract a machine from that predicate. -/
theorem computableInTimeAndSpace {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) :
    ComputableInTimeAndSpace f encIn encOut compiler.time compiler.workspace :=
  ⟨compiler.tapeCount, compiler.State, @Finite.of_fintype _ compiler.stateFintype,
    compiler.machine,
    compiler.computesInTimeAndSpace⟩

/-- The named copy-and-rewind machine. -/
@[expose] noncomputable def identity {α : Type*} (enc : α ↪ List Bool) :
    NativeCompiler (id : α → α) enc enc := by
  letI : Fintype (Unit ⊕ RewindState) := inferInstance
  exact {
    tapeCount := 0
    State := Unit ⊕ RewindState
    machine := tidyCopy Bool
    stateEncoding := sumStateEncoding unitStateEncoding rewindStateEncoding
    time := fun a => 2 * (enc a).length + 4
    workspace := fun _ => 0
    computes := fun a => computesTidily_tidyCopy (enc a)
  }

/-- The identity constructor retains the named copy-and-rewind machine definitionally. -/
theorem machine_identity {α : Type*} (enc : α ↪ List Bool) :
    (identity enc).machine = tidyCopy Bool :=
  rfl

/-- A zero-tape machine that ignores its input and emits `out`, one bit per state, then halts. -/
@[expose] def constantOutputTM (out : List Bool) : MultiTapeTM 0 Bool (Fin (out.length + 1)) :=
  MultiTapeTM.ofTr ⟨0, by omega⟩ fun q _ _ =>
    if h : q.val < out.length then
      { inputTape := 0
        workTapes := Fin.elim0
        output := some out[q.val]
        state := some ⟨q.val + 1, by omega⟩ }
    else
      { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

private def constantOutputCfg (input out : List Bool) (n : ℕ) (hn : n ≤ out.length) :
    Cfg 0 Bool (Fin (out.length + 1)) input :=
  { state := some ⟨n, by omega⟩
    inputPos := 1
    workTapes := fun i => Fin.elim0 i
    workTapePos := fun i => Fin.elim0 i
    output := out.take n }

private theorem step_constantOutputCfg (input out : List Bool) (n : ℕ)
    (hn : n < out.length) :
    (constantOutputTM out).step (constantOutputCfg input out n hn.le) =
      constantOutputCfg input out (n + 1) hn := by
  rw [MultiTapeTM.step_of_state rfl, constantOutputTM, MultiTapeTM.tr_ofTr, dite_eq_left hn]
  apply Cfg.ext_zero_tapes
  · rfl
  · rfl
  · simp only [constantOutputCfg, Action.apply_output, Option.toList_some]
    rw [List.take_add_one, List.getElem?_eq_getElem hn]
    rfl

private theorem step_constantOutputCfg_halt (input out : List Bool) :
    (constantOutputTM out).step (constantOutputCfg input out out.length le_rfl) =
      wordsCfg input none (fun _ => []) out := by
  rw [MultiTapeTM.step_of_state rfl, constantOutputTM, MultiTapeTM.tr_ofTr,
    dite_eq_right (Nat.not_lt.mpr le_rfl)]
  apply Cfg.ext_zero_tapes
  · rfl
  · rfl
  · simp [constantOutputCfg, Action.apply_output]

private theorem runFrom_constantOutputCfg (input out : List Bool) (n : ℕ)
    (hn : n ≤ out.length) :
    (constantOutputTM out).runFrom ((constantOutputTM out).initCfg input) n =
      constantOutputCfg input out n hn := by
  induction n with
  | zero => exact Cfg.ext_zero_tapes rfl rfl rfl
  | succ n ih =>
      rw [MultiTapeTM.runFrom_succ, ih (by omega), step_constantOutputCfg input out n (by omega)]

/-- The constant-output machine computes tidily in exactly `out.length + 1` allowed steps and no
workspace. -/
theorem computesTidily_constantOutputTM (input out : List Bool) :
    (constantOutputTM out).ComputesTidilyInTimeAndSpace input out (out.length + 1) 0 := by
  rw [computesTidily_iff_runFrom]
  constructor
  · rw [show wordsCfg input (some (constantOutputTM out).q₀) (fun _ => []) [] =
        (constantOutputTM out).initCfg input from (initCfg_eq_wordsCfg input).symm,
      MultiTapeTM.runFrom_succ, runFrom_constantOutputCfg input out out.length le_rfl,
      step_constantOutputCfg_halt]
  · simp [MultiTapeNTM.RunPath.space]

/-- A named constant-output machine with its exact output-length clock and zero workspace. -/
@[expose] noncomputable def const {α β : Type*} (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (b : β) :
    NativeCompiler (Function.const α b) encIn encOut :=
  {
    tapeCount := 0
    State := Fin ((encOut b).length + 1)
    machine := constantOutputTM (encOut b)
    stateEncoding := Fin.valEmbedding
    time := fun _ => (encOut b).length + 1
    workspace := fun _ => 0
    computes := fun a => computesTidily_constantOutputTM (encIn a) (encOut b)
  }

/-- The constant constructor retains the named output transducer definitionally. -/
theorem machine_const {α β : Type*} (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (b : β) :
    (const encIn encOut b).machine = constantOutputTM (encOut b) :=
  rfl

/-- Direct composition of two named machines. The result definitionally contains `MultiTapeTM.comp`
and retains every constant from its exact time and workspace theorem. -/
@[expose] noncomputable def comp {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    (outer : NativeCompiler f encMid encOut) (inner : NativeCompiler g encIn encMid) :
    NativeCompiler (fun a => f (g a)) encIn encOut := by
  let CompilerState :=
    ((inner.State ⊕ RewindWorkState) ⊕
      (MarkWorkState ⊕ outer.State ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState)
  letI := inner.stateFintype
  letI := outer.stateFintype
  letI : Fintype CompilerState := inferInstance
  let machine : MultiTapeTM (max inner.tapeCount outer.tapeCount + 2) Bool CompilerState :=
    outer.machine.comp inner.machine true
  exact {
    tapeCount := max inner.tapeCount outer.tapeCount + 2
    State := CompilerState
    machine := machine
    stateEncoding := sumStateEncoding
      (sumStateEncoding inner.stateEncoding rewindWorkStateEncoding)
      (sumStateEncoding
        (sumStateEncoding markWorkStateEncoding
          (sumStateEncoding outer.stateEncoding markWorkStateEncoding))
        (sumStateEncoding unitStateEncoding rewindWorkStateEncoding))
    time := fun a => inner.time a + outer.time (g a) + 4 * (encMid (g a)).length + 9
    workspace := fun a => inner.workspace a + outer.workspace (g a) +
      5 * (encMid (g a)).length + (6 * max inner.tapeCount outer.tapeCount + 20)
    computes := fun a => (inner.computes a).comp (outer.computes (g a)) true
  }

/-- Composition retains the actual machine-combinator term. -/
theorem machine_comp {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    (outer : NativeCompiler f encMid encOut) (inner : NativeCompiler g encIn encMid) :
    (outer.comp inner).machine = outer.machine.comp inner.machine true :=
  rfl

/-- The named finite-state transducer that frames an encoded value. -/
@[expose] noncomputable def encodeFrame {β : Type*} (enc : β ↪ List Bool) :
    NativeCompiler (fun b => frame (enc b)) enc encBits := by
  let FrameState := (Unit × Option Bool × Bool) ⊕ RewindState
  letI : Fintype FrameState := inferInstance
  let frameMachine : MultiTapeTM 0 Bool FrameState :=
    Encodings.frameT.toTM.seq (rewindInput Bool)
  exact {
    tapeCount := 0
    State := FrameState
    machine := frameMachine
    stateEncoding := sumStateEncoding
      (prodStateEncoding unitStateEncoding
        (prodStateEncoding (optionStateEncoding eBit) eBit))
      rewindStateEncoding
    time := fun b => 4 * (enc b).length + 8
    workspace := fun _ => 0
    computes := fun a => by
      simpa [frameMachine, Encodings.frameT_run] using Encodings.frameT.computesTidily (enc a)
  }

/-- The framing constructor retains the named finite-state transducer definitionally. -/
theorem machine_encodeFrame {β : Type*} (enc : β ↪ List Bool) :
    (encodeFrame enc).machine = Encodings.frameT.toTM.seq (rewindInput Bool) :=
  rfl

universe u

/-- Direct standard-pair construction from two named machines on a common input. The left encoded
output is framed by `encodeFrame`, then the right output is appended. -/
@[expose] noncomputable def pair {α β γ : Type u} {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encLeft : β ↪ List Bool} {encRight : γ ↪ List Bool}
    (left : NativeCompiler f encIn encLeft) (right : NativeCompiler g encIn encRight) :
    NativeCompiler (fun a => (f a, g a)) encIn (encPair encLeft encRight) := by
  let framed := (encodeFrame encLeft).comp left
  letI := framed.stateFintype
  letI := right.stateFintype
  letI : Fintype (framed.State ⊕ right.State) := inferInstance
  exact {
    tapeCount := max framed.tapeCount right.tapeCount
    State := framed.State ⊕ right.State
    machine := appendTM framed.machine right.machine
    stateEncoding := sumStateEncoding framed.stateEncoding right.stateEncoding
    time := fun a => framed.time a + right.time a
    workspace := fun a => framed.workspace a + right.workspace a +
      2 * max framed.tapeCount right.tapeCount
    computes := fun a => by
      simpa only [encPair_apply, encBits_apply] using
        (framed.computes a).append (right.computes a)
  }

/-- Pairing retains the actual framing, composition and append machine terms. -/
theorem machine_pair {α β γ : Type u} {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encLeft : β ↪ List Bool} {encRight : γ ↪ List Bool}
    (left : NativeCompiler f encIn encLeft) (right : NativeCompiler g encIn encRight) :
    (left.pair right).machine =
      appendTM (((encodeFrame encLeft).comp left).machine) right.machine :=
  rfl

end NativeCompiler

end Turing.MultiTapeTM.Internal
