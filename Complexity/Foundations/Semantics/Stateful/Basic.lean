/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Foundations.Semantics.FLTS.Basic
public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Stateful specifications and adaptive clients

Specifications describe mathematical states, typed operations, relational transitions, and input
admissibility. Clients use Quang Dao's upstream `PFunctor.FreeM`; continuations may depend on
earlier answers. The state interpreter and its transcripts have no computational-model or
performance claim. In particular, pure Lean computation in continuations is not charged as a
machine instruction.

The relational semantics is **demonic** for callers and **angelic** for implementations:
* An adaptive client `p : D.Client α` is demonically admissible (`D.DemonicValid s p`) when each
  issued operation is admissible (`D.valid`) and the continuation remains admissible under *every*
  outcome `(s', a)` permitted by `D.step`.
* Deterministic specifications are constructed via `Spec.ofFn` and characterized by the
  `Spec.HasStepFn` typeclass, which equips them with functional execution helpers (`Spec.stepFn`,
  `Spec.toFLTS`, `Spec.run`, `Spec.ValidHistory`, `Spec.totalCost`, `Spec.runClient`, `eval`) and
  equivalence lemmas connecting the relational and functional views.

## Main definitions

* `Spec`: relational stateful operation semantics with typed answers and admissibility.
* `Spec.Total`, `Spec.Deterministic`: totality on admissible inputs and transition determinism.
* `Spec.toLTS`: the underlying labelled transition system (`Cslib.LTS`) of input-output transitions.
* `Spec.Step`, `Spec.Transcript`, `Spec.ValidTranscript`, `Spec.ValidOpSeq`,
  `Spec.totalCostTranscript`, `Spec.totalCostOutcome`: execution transcripts, demonic
  operation-sequence admissibility, and transcript cost accounting.
* `Spec.signature`, `Spec.Client`, `Spec.call`, `Spec.ClientRun`, `Spec.DemonicValid`: adaptive
  clients, relational client runs, and demonic client admissibility.
* `Spec.ofFn`, `Spec.HasStepFn`, `Spec.stepFn`: constructor and typeclass for deterministic
  specifications.
* `Spec.toFLTS`, `Spec.run`, `Spec.ValidHistory`, `Spec.totalCost`, `Spec.runClient`, `eval`:
  functional execution and history interpretation for deterministic specifications.
* `product`: independent abstract components; concrete independence is a realization obligation.

## Main results

* `Spec.ValidTranscript.append`, `Spec.totalCostTranscript_append`: transcript composition laws.
* `Spec.exists_validTranscript_of_validOpSeq`, `Spec.DemonicValid.exists_clientRun`: existence of
  valid runs under `[Spec.Total]`.
* `Spec.ClientRun.bind`, `Spec.clientRun_bind_iff`, `Spec.DemonicValid.bind`: sequential
  composition for relational adaptive clients.
* `Spec.validOpSeq_iff_validHistory`, `Spec.validTranscript_iff_run`,
  `Spec.demonicValid_iff_validHistory_runClient`, `Spec.clientRun_iff_runClient`: equivalence of
  relational and functional semantics under `[Spec.HasStepFn]`.
* `Spec.fst_run_eq_toFLTS_mtr`, `Spec.run_append`, `Spec.validHistory_append`,
  `Spec.totalCost_append`, `Spec.run_runClient`, `Spec.runClient_bind`, `eval_bind`,
  `eval_eq_liftM`: functional history and client laws under `[Spec.HasStepFn]`.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006].
* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*][Sangiorgi2011].
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x y

/-- A relational abstract state machine with operation-dependent observations.
`step s o s' a` holds when transitioning from `s` to `s'` and returning `a : Result o` is a
permitted outcome of operation `o`. Only admissible operations (`valid s o`) are constrained by
refinement certificates. -/
structure Spec where
  /-- Mathematical states, independent of a storage representation. -/
  State : Type u
  /-- Operations available to clients. -/
  Op : Type v
  /-- The observation type returned by each operation. -/
  Result : Op → Type w
  /-- Relational state transition and observation specification. -/
  step : (s : State) → (o : Op) → State → Result o → Prop
  /-- Preconditions under which an operation's implementation must satisfy its contract. -/
  valid : State → Op → Prop := fun _ _ => True

namespace Spec

variable (D : Spec.{u, v, w})

/-- The set of permitted `(nextState, result)` outcomes of operation `o` from state `s`. -/
def outcomes (s : D.State) (o : D.Op) : Set (D.State × D.Result o) :=
  {p | D.step s o p.1 p.2}

/-- Membership in `D.outcomes s o` unfolds to `D.step s o`. -/
@[simp]
theorem mem_outcomes_iff (s : D.State) (o : D.Op) (p : D.State × D.Result o) :
    p ∈ D.outcomes s o ↔ D.step s o p.1 p.2 := Iff.rfl

/-- A specification is total on admissible inputs if every valid `(s, o)` admits at least one
permitted outcome `(s', a)`. -/
class Total : Prop where
  /-- Every admissible operation call has at least one permitted post-state and result. -/
  step_total : ∀ s o, D.valid s o → ∃ s' a, D.step s o s' a

/-- Obtain a permitted outcome `(s', a)` for an admissible operation under `[D.Total]`. -/
theorem exists_step [D.Total] {s : D.State} {o : D.Op} (hv : D.valid s o) :
    ∃ s' a, D.step s o s' a :=
  Total.step_total s o hv

/-- A specification is deterministic if each `(s, o)` admits at most one outcome `(s', a)`. -/
class Deterministic : Prop where
  /-- Any two permitted outcomes for the same state and operation coincide. -/
  step_deterministic : ∀ {s o s₁ a₁ s₂ a₂},
    D.step s o s₁ a₁ → D.step s o s₂ a₂ → s₁ = s₂ ∧ a₁ = a₂

/-- The polynomial operation signature, shared with upstream effectful programs. -/
abbrev signature : PFunctor.{v, w} := ⟨D.Op, D.Result⟩

instance : Coe Spec.{u, v, w} PFunctor.{v, w} := ⟨Spec.signature⟩

/-- An adaptive client: each continuation may depend on the observed answer.
Inductive clients have no infinite execution branch; branching need not be finite. -/
abbrev Client (α : Type y) : Type (max v w y) := D.signature.FreeM α

/-- Invoke a single operation `o : D.Op` in an adaptive `D.Client`. -/
abbrev call (o : D.Op) : D.Client (D.Result o) := .liftBind o .pure

/-- An input-output transition label pairing an operation `o : D.Op` with its result `a`. -/
abbrev Label : Type (max v w) := Σ o : D.Op, D.Result o

/-- View a stateful specification as a labelled transition system (`Cslib.LTS`) labelled by
input-output pairs `⟨o, a⟩ : Σ o : D.Op, D.Result o`. -/
def toLTS : LTS D.State D.Label where
  Tr s lbl s' := D.step s lbl.1 s' lbl.2

/-- A transition in `D.toLTS` is a step of `D`. -/
@[simp]
theorem toLTS_tr (s s' : D.State) (lbl : D.Label) :
    D.toLTS.Tr s lbl s' ↔ D.step s lbl.1 s' lbl.2 := Iff.rfl

instance [D.Deterministic] : D.toLTS.Deterministic where
  deterministic _ _ _ _ h₁ h₂ := (Deterministic.step_deterministic h₁ h₂).1

/-! ## Transcripts, non-adaptive operation sequences, and cost accounting -/

/-- One recorded step of a specification: the issued operation `op`, its returned observation
`result`, and the resulting post-state `nextState`. -/
structure Step : Type (max u v w) where
  /-- The operation invoked at this step. -/
  op : D.Op
  /-- The observation returned by `op`. -/
  result : D.Result op
  /-- The abstract post-state reached after `op`. -/
  nextState : D.State

/-- A finite execution transcript is a list of recorded steps. -/
abbrev Transcript : Type (max u v w) := List D.Step

/-- Extract the underlying sequence of operations from a transcript. -/
def Transcript.ops {D : Spec.{u, v, w}} (tr : D.Transcript) : List D.Op :=
  tr.map Step.op

/-- Extract the `Cslib.LTS` input-output labels from a transcript. -/
def Transcript.labels {D : Spec.{u, v, w}} (tr : D.Transcript) : List D.Label :=
  tr.map fun st => ⟨st.op, st.result⟩

@[simp]
theorem Transcript.ops_nil {D : Spec.{u, v, w}} :
    Transcript.ops ([] : D.Transcript) = [] := rfl

@[simp]
theorem Transcript.ops_cons {D : Spec.{u, v, w}} (st : D.Step) (tr : D.Transcript) :
    Transcript.ops (st :: tr) = st.op :: Transcript.ops tr := rfl

@[simp]
theorem Transcript.ops_append {D : Spec.{u, v, w}} (tr₁ tr₂ : D.Transcript) :
    Transcript.ops (tr₁ ++ tr₂) = Transcript.ops tr₁ ++ Transcript.ops tr₂ :=
  List.map_append

@[simp]
theorem Transcript.length_ops {D : Spec.{u, v, w}} (tr : D.Transcript) :
    (Transcript.ops tr).length = tr.length :=
  List.length_map _

@[simp]
theorem Transcript.labels_nil {D : Spec.{u, v, w}} :
    Transcript.labels ([] : D.Transcript) = [] := rfl

@[simp]
theorem Transcript.labels_cons {D : Spec.{u, v, w}} (st : D.Step) (tr : D.Transcript) :
    Transcript.labels (st :: tr) = ⟨st.op, st.result⟩ :: Transcript.labels tr := rfl

@[simp]
theorem Transcript.labels_append {D : Spec.{u, v, w}} (tr₁ tr₂ : D.Transcript) :
    Transcript.labels (tr₁ ++ tr₂) = Transcript.labels tr₁ ++ Transcript.labels tr₂ :=
  List.map_append

@[simp]
theorem Transcript.length_labels {D : Spec.{u, v, w}} (tr : D.Transcript) :
    (Transcript.labels tr).length = tr.length :=
  List.length_map _

/-- `D.ValidTranscript s tr s'` holds when `tr` is a valid step-by-step execution starting at `s`
and ending at `s'`, where each step is admissible (`D.valid`) and permitted by `D.step`. -/
inductive ValidTranscript : D.State → D.Transcript → D.State → Prop
  | nil (s : D.State) : ValidTranscript s [] s
  | cons {s : D.State} (st : D.Step) {tr : D.Transcript} {s_fin : D.State} :
      D.valid s st.op →
      D.step s st.op st.nextState st.result →
      ValidTranscript st.nextState tr s_fin →
      ValidTranscript s (st :: tr) s_fin

/-- The empty transcript is valid iff the initial and final states coincide. -/
@[simp]
theorem validTranscript_nil_iff {D : Spec.{u, v, w}} (s s' : D.State) :
    D.ValidTranscript s [] s' ↔ s = s' := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil s

/-- A nonempty transcript is valid iff its head step is admissible and permitted and its tail is
valid from `st.nextState`. -/
@[simp]
theorem validTranscript_cons_iff {D : Spec.{u, v, w}} (s s' : D.State) (st : D.Step)
    (tr : D.Transcript) :
    D.ValidTranscript s (st :: tr) s' ↔
      D.valid s st.op ∧ D.step s st.op st.nextState st.result ∧
        D.ValidTranscript st.nextState tr s' := by
  constructor
  · intro h
    cases h with
    | cons _ hv hstep htr => exact ⟨hv, hstep, htr⟩
  · rintro ⟨hv, hstep, htr⟩
    exact .cons st hv hstep htr

/-- Valid transcripts compose across concatenation. -/
theorem ValidTranscript.append {D : Spec.{u, v, w}} {s s₁ s₂ : D.State}
    {tr₁ tr₂ : D.Transcript} (h₁ : D.ValidTranscript s tr₁ s₁)
    (h₂ : D.ValidTranscript s₁ tr₂ s₂) :
    D.ValidTranscript s (tr₁ ++ tr₂) s₂ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons st hv hstep _ ih => exact .cons st hv hstep (ih h₂)

/-- Every valid transcript projects to a multi-step transition in `D.toLTS`. -/
theorem ValidTranscript.toLTS_mtr {D : Spec.{u, v, w}} {s s' : D.State}
    {tr : D.Transcript} (h : D.ValidTranscript s tr s') :
    D.toLTS.MTr s tr.labels s' := by
  induction h with
  | nil _ => exact .refl
  | cons _ _ hstep _ ih => exact .stepL hstep ih

/-- Demonic admissibility of a non-adaptive operation sequence `ops : List D.Op` from `s`:
the head operation is admissible at `s`, and the tail sequence remains admissible from every
permitted post-state `s'` of the head operation. -/
def ValidOpSeq (s : D.State) : List D.Op → Prop
  | [] => True
  | o :: ops => D.valid s o ∧ ∀ s' a, D.step s o s' a → ValidOpSeq s' ops

@[simp]
theorem validOpSeq_nil (s : D.State) : D.ValidOpSeq s [] ↔ True := Iff.rfl

@[simp]
theorem validOpSeq_cons (s : D.State) (o : D.Op) (ops : List D.Op) :
    D.ValidOpSeq s (o :: ops) ↔ D.valid s o ∧ ∀ s' a, D.step s o s' a → D.ValidOpSeq s' ops :=
  Iff.rfl

/-- Total interfaces have no operation-sequence admissibility obligations. -/
theorem validOpSeq_of_forall_valid (h : ∀ s o, D.valid s o) (s : D.State) (ops : List D.Op) :
    D.ValidOpSeq s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons o ops ih => exact ⟨h s o, fun s' _ _ => ih s'⟩

/-- Demonic operation-sequence admissibility splits across concatenation across all valid
transcripts of the prefix. -/
theorem validOpSeq_append {D : Spec.{u, v, w}} {s : D.State} {xs ys : List D.Op}
    (h : D.ValidOpSeq s (xs ++ ys)) :
    D.ValidOpSeq s xs ∧
      ∀ {tr s'}, tr.ops = xs → D.ValidTranscript s tr s' → D.ValidOpSeq s' ys := by
  induction xs generalizing s with
  | nil =>
    refine ⟨trivial, fun {tr s'} hops htr => ?_⟩
    cases tr with
    | nil =>
      cases htr
      exact h
    | cons _ _ => cases hops
  | cons o xs ih =>
    obtain ⟨hvo, hrest⟩ := h
    refine ⟨⟨hvo, fun s₁ a hstep => (ih (hrest s₁ a hstep)).1⟩, fun {tr s'} hops htr => ?_⟩
    cases tr with
    | nil => cases hops
    | cons st tr' =>
      cases hops
      cases htr with
      | cons _ _ hstep htr' =>
        exact (ih (hrest st.nextState st.result hstep)).2 rfl htr'

/-- Under `[D.Total]`, every demonically admissible operation sequence admits at least one valid
transcript. -/
theorem exists_validTranscript_of_validOpSeq [D.Total] {s : D.State} {ops : List D.Op}
    (hv : D.ValidOpSeq s ops) :
    ∃ tr s', tr.ops = ops ∧ D.ValidTranscript s tr s' := by
  induction ops generalizing s with
  | nil => exact ⟨[], s, rfl, .nil s⟩
  | cons o ops ih =>
    obtain ⟨hv_o, hv_rest⟩ := hv
    obtain ⟨s₁, a, hstep⟩ := D.exists_step hv_o
    obtain ⟨tr, s₂, hops, htr⟩ := ih (hv_rest s₁ a hstep)
    exact ⟨⟨o, a, s₁⟩ :: tr, s₂, congrArg (o :: ·) hops, .cons _ hv_o hstep htr⟩

/-- State-dependent charges summed along a transcript. -/
def totalCostTranscript (charge : D.State → D.Op → ℕ) : D.State → D.Transcript → ℕ
  | _, [] => 0
  | s, st :: tr => charge s st.op + totalCostTranscript charge st.nextState tr

/-- Outcome-dependent charges summed along a transcript, where each step charge may also inspect
the post-state `st.nextState` and result `st.result`. -/
def totalCostOutcome (charge : D.State → (o : D.Op) → D.State → D.Result o → ℕ) :
    D.State → D.Transcript → ℕ
  | _, [] => 0
  | s, st :: tr =>
    charge s st.op st.nextState st.result + totalCostOutcome charge st.nextState tr

@[simp]
theorem totalCostTranscript_nil (charge : D.State → D.Op → ℕ) (s : D.State) :
    D.totalCostTranscript charge s [] = 0 := rfl

@[simp]
theorem totalCostTranscript_cons (charge : D.State → D.Op → ℕ) (s : D.State) (st : D.Step)
    (tr : D.Transcript) :
    D.totalCostTranscript charge s (st :: tr) =
      charge s st.op + D.totalCostTranscript charge st.nextState tr := rfl

@[simp]
theorem totalCostOutcome_nil (charge : D.State → (o : D.Op) → D.State → D.Result o → ℕ)
    (s : D.State) :
    D.totalCostOutcome charge s [] = 0 := rfl

@[simp]
theorem totalCostOutcome_cons (charge : D.State → (o : D.Op) → D.State → D.Result o → ℕ)
    (s : D.State) (st : D.Step) (tr : D.Transcript) :
    D.totalCostOutcome charge s (st :: tr) =
      charge s st.op st.nextState st.result + D.totalCostOutcome charge st.nextState tr := rfl

/-- `totalCostTranscript` is the special case of `totalCostOutcome` that ignores the post-state and
result. -/
theorem totalCostTranscript_eq_totalCostOutcome (charge : D.State → D.Op → ℕ) (s : D.State)
    (tr : D.Transcript) :
    D.totalCostTranscript charge s tr = D.totalCostOutcome (fun s o _ _ => charge s o) s tr := by
  induction tr generalizing s with
  | nil => rfl
  | cons st tr ih => simp [ih]

/-- Along a valid transcript prefix `D.ValidTranscript s tr₁ s₁`, `totalCostTranscript` splits
additively at the intermediate state `s₁`. -/
theorem totalCostTranscript_append {D : Spec.{u, v, w}} (charge : D.State → D.Op → ℕ)
    {s s₁ : D.State} {tr₁ : D.Transcript} (h₁ : D.ValidTranscript s tr₁ s₁)
    (tr₂ : D.Transcript) :
    D.totalCostTranscript charge s (tr₁ ++ tr₂) =
      D.totalCostTranscript charge s tr₁ + D.totalCostTranscript charge s₁ tr₂ := by
  induction h₁ with
  | nil _ => simp
  | cons st _ _ _ ih => simp [ih, Nat.add_assoc]

/-- Uniform per-operation bounds scale by the transcript length on any valid transcript. -/
theorem totalCostTranscript_le_length_mul {D : Spec.{u, v, w}} (charge : D.State → D.Op → ℕ) (T : ℕ)
    (h : ∀ s o, D.valid s o → charge s o ≤ T) {s s' : D.State} {tr : D.Transcript}
    (hv : D.ValidTranscript s tr s') :
    D.totalCostTranscript charge s tr ≤ tr.length * T := by
  induction hv with
  | nil _ => simp
  | cons st hv_o _ _ ih =>
    have hstep := h _ st.op hv_o
    simp only [totalCostTranscript_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A constant charge `K` per operation totals `tr.length * K`. -/
theorem totalCostTranscript_const (K : ℕ) (s : D.State) (tr : D.Transcript) :
    D.totalCostTranscript (fun _ _ => K) s tr = tr.length * K := by
  induction tr generalizing s with
  | nil => simp
  | cons st tr ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- A unit charge per operation totals the transcript length. -/
theorem totalCostTranscript_one (s : D.State) (tr : D.Transcript) :
    D.totalCostTranscript (fun _ _ => 1) s tr = tr.length := by
  simpa using D.totalCostTranscript_const 1 s tr

/-! ## Adaptive clients (`ClientRun` and `DemonicValid`) -/

variable {α β : Type y}

/-- `D.ClientRun s p v s' tr` holds when running the adaptive client `p : D.Client α` from initial
state `s` can produce return value `v : α`, final state `s' : D.State`, and transcript `tr` by
making admissible and permitted transitions at each operation call. -/
inductive ClientRun : D.State → D.Client α → α → D.State → D.Transcript → Prop
  | pure (s : D.State) (a : α) :
      ClientRun s (.pure a) a s []
  | liftBind {s s₁ s₂ : D.State} (o : D.Op) (k : D.Result o → D.Client α)
      (a : D.Result o) {v : α} {tr : D.Transcript} :
      D.valid s o →
      D.step s o s₁ a →
      ClientRun s₁ (k a) v s₂ tr →
      ClientRun s (.liftBind o k) v s₂ (⟨o, a, s₁⟩ :: tr)

/-- Every `ClientRun` produces a valid transcript. -/
theorem ClientRun.validTranscript {D : Spec.{u, v, w}} {s s' : D.State} {p : D.Client α}
    {v : α} {tr : D.Transcript} (h : D.ClientRun s p v s' tr) :
    D.ValidTranscript s tr s' := by
  induction h with
  | pure s _ => exact .nil s
  | liftBind _ _ _ hv hstep _ ih => exact .cons _ hv hstep ih

theorem clientRun_pure_iff {D : Spec.{u, v, w}} (s : D.State) (a v : α) (s' : D.State)
    (tr : D.Transcript) :
    D.ClientRun s (.pure a) v s' tr ↔ v = a ∧ s' = s ∧ tr = [] := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact .pure s' v

theorem clientRun_liftBind_iff {D : Spec.{u, v, w}} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) (v : α) (s₂ : D.State) (tr : D.Transcript) :
    D.ClientRun s (.liftBind o k) v s₂ tr ↔
      D.valid s o ∧ ∃ a s₁ tr', D.step s o s₁ a ∧
        D.ClientRun s₁ (k a) v s₂ tr' ∧ tr = ⟨o, a, s₁⟩ :: tr' := by
  constructor
  · intro h
    cases h with
    | liftBind _ _ a hv hstep hrest =>
      exact ⟨hv, a, _, _, hstep, hrest, rfl⟩
  · rintro ⟨hv, a, s₁, tr', hstep, hrest, rfl⟩
    exact .liftBind o k a hv hstep hrest

/-- Sequential client runs compose by concatenating their transcripts. -/
theorem ClientRun.bind {D : Spec.{u, v, w}} {s s₁ s₂ : D.State} {p : D.Client α}
    {k : α → D.Client β} {a : α} {b : β} {tr₁ tr₂ : D.Transcript}
    (h₁ : D.ClientRun s p a s₁ tr₁) (h₂ : D.ClientRun s₁ (k a) b s₂ tr₂) :
    D.ClientRun s (p.bind k) b s₂ (tr₁ ++ tr₂) := by
  induction h₁ with
  | pure _ _ => exact h₂
  | liftBind o cont res hv hstep _ ih =>
    exact .liftBind o (fun r => (cont r).bind k) res hv hstep (ih h₂)

/-- A client run of `p.bind k` splits into a run of `p` and a run of `k` from the intermediate
result and state. -/
theorem clientRun_bind_iff {D : Spec.{u, v, w}} {s s₂ : D.State} {p : D.Client α}
    {k : α → D.Client β} {b : β} {tr : D.Transcript} :
    D.ClientRun s (p.bind k) b s₂ tr ↔
      ∃ a s₁ tr₁ tr₂, D.ClientRun s p a s₁ tr₁ ∧
        D.ClientRun s₁ (k a) b s₂ tr₂ ∧ tr = tr₁ ++ tr₂ := by
  constructor
  · intro h
    induction p generalizing s tr with
    | pure a =>
      exact ⟨a, s, [], tr, .pure s a, h, rfl⟩
    | liftBind o cont ih =>
      change D.ClientRun s (.liftBind o fun r => (cont r).bind k) b s₂ tr at h
      cases h with
      | liftBind _ _ res hv hstep hrest =>
        obtain ⟨a, s₁, tr₁, tr₂, hp, hk, rfl⟩ := ih res hrest
        exact ⟨a, s₁, ⟨o, res, _⟩ :: tr₁, tr₂, .liftBind o cont res hv hstep hp, hk, rfl⟩
  · rintro ⟨a, s₁, tr₁, tr₂, hp, hk, rfl⟩
    exact hp.bind hk

/-- Demonic admissibility of an adaptive client `p` from state `s`:
* `.pure a` is always admissible;
* `.liftBind o k` requires `D.valid s o` now, and for *every* permitted outcome `(s', a)` of `o`
  from `s`, the continuation `k a` must be demonically admissible from `s'`. -/
inductive DemonicValid : D.State → D.Client α → Prop
  | pure (s : D.State) (a : α) :
      DemonicValid s (.pure a)
  | liftBind {s : D.State} (o : D.Op) (k : D.Result o → D.Client α) :
      D.valid s o →
      (∀ s' a, D.step s o s' a → DemonicValid s' (k a)) →
      DemonicValid s (.liftBind o k)

theorem demonicValid_pure_iff {D : Spec.{u, v, w}} (s : D.State) (a : α) :
    D.DemonicValid s (.pure a) ↔ True :=
  ⟨fun _ => trivial, fun _ => .pure s a⟩

theorem demonicValid_liftBind_iff {D : Spec.{u, v, w}} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    D.DemonicValid s (.liftBind o k) ↔
      D.valid s o ∧ ∀ s' a, D.step s o s' a → D.DemonicValid s' (k a) := by
  constructor
  · intro h
    cases h with
    | liftBind _ _ hv hk => exact ⟨hv, hk⟩
  · rintro ⟨hv, hk⟩; exact .liftBind o k hv hk

/-- On a specification where every operation is valid in every state, every client is demonically
admissible. -/
theorem demonicValid_of_forall_valid (h : ∀ s o, D.valid s o) (s : D.State) (p : D.Client α) :
    D.DemonicValid s p := by
  induction p generalizing s with
  | pure a => exact .pure s a
  | liftBind o k ih => exact .liftBind o k (h s o) fun s' a _ => ih a s'

/-- Under `[D.Total]`, every demonically admissible client admits at least one valid `ClientRun`. -/
theorem DemonicValid.exists_clientRun {D : Spec.{u, v, w}} [D.Total] {s : D.State}
    {p : D.Client α} (hv : D.DemonicValid s p) :
    ∃ v s' tr, D.ClientRun s p v s' tr := by
  induction hv with
  | pure s a => exact ⟨a, s, [], .pure s a⟩
  | liftBind o k hv_o _ ih =>
    obtain ⟨s₁, a, hstep⟩ := D.exists_step hv_o
    obtain ⟨v, s₂, tr, hrun⟩ := ih s₁ a hstep
    exact ⟨v, s₂, ⟨o, a, s₁⟩ :: tr, .liftBind o k a hv_o hstep hrun⟩

/-- Demonic admissibility composes across `bind` when the continuation is demonically admissible
after every valid run of the first client. -/
theorem DemonicValid.bind {D : Spec.{u, v, w}} {s : D.State} {p : D.Client α}
    {k : α → D.Client β} (hp : D.DemonicValid s p)
    (hk : ∀ a s' tr, D.ClientRun s p a s' tr → D.DemonicValid s' (k a)) :
    D.DemonicValid s (p.bind k) := by
  induction hp with
  | pure s a => exact hk a s [] (.pure s a)
  | liftBind o cont hv_o _ ih =>
    refine .liftBind o (fun r => (cont r).bind k) hv_o fun s₁ r hstep => ?_
    exact ih s₁ r hstep fun a s₂ tr hrun => hk a s₂ (⟨o, r, s₁⟩ :: tr)
      (.liftBind o cont r hv_o hstep hrun)

/-! ## Deterministic specifications (`Spec.ofFn`, `Spec.HasStepFn`) and functional helpers -/

/-- Construct a deterministic `Spec` from a pure transition function
`stepFn : (s : State) → (o : Op) → State × Result o` and an optional admissibility predicate
`valid`. -/
abbrev ofFn {State : Type u} {Op : Type v} {Result : Op → Type w}
    (stepFn : (s : State) → (o : Op) → State × Result o)
    (valid : State → Op → Prop := fun _ _ => True) : Spec.{u, v, w} where
  State := State
  Op := Op
  Result := Result
  step s o s' a := (s', a) = stepFn s o
  valid := valid

@[simp]
theorem ofFn_state {State : Type u} {Op : Type v} {Result : Op → Type w}
    (stepFn : (s : State) → (o : Op) → State × Result o)
    (valid : State → Op → Prop := fun _ _ => True) :
    (ofFn stepFn valid).State = State := rfl

@[simp]
theorem ofFn_op {State : Type u} {Op : Type v} {Result : Op → Type w}
    (stepFn : (s : State) → (o : Op) → State × Result o)
    (valid : State → Op → Prop := fun _ _ => True) :
    (ofFn stepFn valid).Op = Op := rfl

@[simp]
theorem ofFn_result {State : Type u} {Op : Type v} {Result : Op → Type w}
    (stepFn : (s : State) → (o : Op) → State × Result o)
    (valid : State → Op → Prop := fun _ _ => True) :
    (ofFn stepFn valid).Result = Result := rfl

@[simp]
theorem ofFn_step_iff {State : Type u} {Op : Type v} {Result : Op → Type w}
    (stepFn : (s : State) → (o : Op) → State × Result o)
    (valid : State → Op → Prop := fun _ _ => True)
    (s : State) (o : Op) (s' : State) (a : Result o) :
    (ofFn stepFn valid).step s o s' a ↔ (s', a) = stepFn s o := Iff.rfl

@[simp]
theorem ofFn_valid {State : Type u} {Op : Type v} {Result : Op → Type w}
    (stepFn : (s : State) → (o : Op) → State × Result o)
    (valid : State → Op → Prop := fun _ _ => True)
    (s : State) (o : Op) :
    (ofFn stepFn valid).valid s o ↔ valid s o := Iff.rfl

/-- Typeclass witnessing that a specification `D : Spec` is governed by a pure transition function
`f : (s : D.State) → (o : D.Op) → D.State × D.Result o`. -/
class HasStepFn (D : Spec.{u, v, w})
    (f : outParam ((s : D.State) → (o : D.Op) → D.State × D.Result o)) : Prop where
  /-- A transition `D.step s o s' a` holds if and only if `(s', a) = f s o`. -/
  step_iff : ∀ s o s' a, D.step s o s' a ↔ (s', a) = f s o

instance instHasStepFnOfFn {State : Type u} {Op : Type v} {Result : Op → Type w}
    (f : (s : State) → (o : Op) → State × Result o)
    (valid : State → Op → Prop) :
    (ofFn f valid).HasStepFn f :=
  ⟨fun _ _ _ _ => Iff.rfl⟩

/-- The functional transition `(s : D.State) → (o : D.Op) → D.State × D.Result o` of a
deterministic specification `D` (`[D.HasStepFn f]`). -/
@[simp, nolint unusedArguments]
abbrev stepFn (D : Spec.{u, v, w}) {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (s : D.State) (o : D.Op) : D.State × D.Result o :=
  f s o

theorem step_iff_stepFn (D : Spec.{u, v, w}) {f} [D.HasStepFn f]
    (s : D.State) (o : D.Op) (s' : D.State) (a : D.Result o) :
    D.step s o s' a ↔ (s', a) = D.stepFn s o :=
  HasStepFn.step_iff s o s' a

theorem step_stepFn (D : Spec.{u, v, w}) {f} [D.HasStepFn f]
    (s : D.State) (o : D.Op) :
    D.step s o (D.stepFn s o).1 (D.stepFn s o).2 :=
  (HasStepFn.step_iff s o _ _).mpr Prod.mk.eta

instance instTotalOfHasStepFn (D : Spec.{u, v, w}) {f} [D.HasStepFn f] : D.Total where
  step_total s o _ := ⟨(D.stepFn s o).1, (D.stepFn s o).2, D.step_stepFn s o⟩

instance instDeterministicOfHasStepFn (D : Spec.{u, v, w}) {f} [D.HasStepFn f] :
    D.Deterministic where
  step_deterministic h₁ h₂ := by
    have e₁ := (D.step_iff_stepFn _ _ _ _).mp h₁
    have e₂ := (D.step_iff_stepFn _ _ _ _).mp h₂
    exact Prod.ext_iff.mp (e₁.trans e₂.symm)

variable {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]

/-- Forget typed observations to view state transitions as a functional labelled transition
system. -/
def toFLTS : FLTS D.State D.Op := ⟨fun s o => (D.stepFn s o).1⟩

/-- The transition function of `D.toFLTS` is the state component of `D.stepFn`. -/
@[simp] theorem toFLTS_tr (s : D.State) (o : D.Op) :
    D.toFLTS.tr s o = (D.stepFn s o).1 := rfl

/-- Transitions in `D.toLTS` agree with `D.toFLTS` on states and `(D.stepFn s o).2` on
observations. -/
theorem toLTS_tr_iff_toFLTS (s s' : D.State) (o : D.Op) (a : D.Result o) :
    D.toLTS.Tr s ⟨o, a⟩ s' ↔ s' = D.toFLTS.tr s o ∧ a = (D.stepFn s o).2 := by
  rw [toLTS_tr, step_iff_stepFn, Prod.ext_iff, toFLTS_tr]

/-- The final state and complete typed observation trace of a history. -/
def run (s : D.State) : List D.Op → D.State × List (Sigma D.Result)
  | [] => (s, [])
  | o :: os =>
    let next := D.stepFn s o
    let rest := run next.1 os
    (rest.1, ⟨o, next.2⟩ :: rest.2)

/-- Each operation is admissible in the state reached by its predecessors. -/
def ValidHistory (s : D.State) : List D.Op → Prop
  | [] => True
  | o :: os => D.valid s o ∧ ValidHistory (D.stepFn s o).1 os

/-- State-dependent charges summed along the abstract execution. -/
def totalCost (charge : D.State → D.Op → Nat) (s : D.State) : List D.Op → Nat
  | [] => 0
  | o :: os => charge s o + totalCost charge (D.stepFn s o).1 os

/-- Running the empty history keeps the state and observes nothing. -/
@[simp] theorem run_nil (s : D.State) : D.run s (@List.nil (no_index D.Op)) = (s, []) := rfl

/-- Running a nonempty history steps once and prepends the typed observation. -/
@[simp] theorem run_cons (s : D.State) (o : D.Op) (os : List D.Op) :
    D.run s (@List.cons (no_index D.Op) o os) =
      ((D.run (D.stepFn s o).1 os).1, ⟨o, (D.stepFn s o).2⟩ :: (D.run (D.stepFn s o).1 os).2) := rfl

/-- The final state of `D.run` agrees with the multi-step transition of `D.toFLTS`. -/
theorem fst_run_eq_toFLTS_mtr (s : D.State) (os : List D.Op) :
    (D.run s os).1 = D.toFLTS.mtr s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact ih (D.stepFn s o).1

/-- Multi-step execution `D.run` produces a valid multi-step trace in `D.toLTS` ending at
`D.toFLTS.mtr s os`. -/
theorem toLTS_mtr_run (s : D.State) (os : List D.Op) :
    D.toLTS.MTr s (D.run s os).2 (D.toFLTS.mtr s os) := by
  induction os generalizing s with
  | nil => exact .refl
  | cons o os ih =>
    exact .stepL (D.step_stepFn s o) (ih (D.stepFn s o).1)

/-- The empty history is admissible in every state. -/
@[simp] theorem validHistory_nil (s : D.State) :
    D.ValidHistory s (@List.nil (no_index D.Op)) ↔ True := Iff.rfl

/-- A nonempty history is admissible when its first operation is valid and the tail is admissible
from the next state. -/
@[simp] theorem validHistory_cons (s : D.State) (o : D.Op) (os : List D.Op) :
    D.ValidHistory s (@List.cons (no_index D.Op) o os) ↔
      D.valid s o ∧ D.ValidHistory (D.stepFn s o).1 os := Iff.rfl

/-- Total interfaces have no history admissibility obligations. -/
theorem validHistory_of_forall_valid (h : ∀ s o, D.valid s o)
    (s : D.State) (os : List D.Op) : D.ValidHistory s os := by
  induction os generalizing s with
  | nil => trivial
  | cons o os ih => exact ⟨h s o, ih _⟩

/-- The empty history costs nothing. -/
@[simp] theorem totalCost_nil (charge : D.State → D.Op → Nat) (s : D.State) :
    D.totalCost charge s (@List.nil (no_index D.Op)) = 0 := rfl

/-- The cost of a nonempty history adds the first operation's charge to the tail cost from the
next state. -/
@[simp] theorem totalCost_cons (charge : D.State → D.Op → Nat) (s : D.State)
    (o : D.Op) (os : List D.Op) :
    D.totalCost charge s (@List.cons (no_index D.Op) o os) =
      charge s o + D.totalCost charge (D.stepFn s o).1 os := rfl

/-- Concatenation preserves both the state and the observation order. -/
theorem run_append (s : D.State) (xs ys : List D.Op) :
    D.run s (xs ++ ys) =
      ((D.run (D.run s xs).1 ys).1, (D.run s xs).2 ++ (D.run (D.run s xs).1 ys).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons o os ih => simp [ih]

/-- Charges compose at the intermediate abstract state. -/
theorem totalCost_append (charge : D.State → D.Op → Nat) (s : D.State)
    (xs ys : List D.Op) :
    D.totalCost charge s (xs ++ ys) =
      D.totalCost charge s xs + D.totalCost charge (D.run s xs).1 ys := by
  induction xs generalizing s with
  | nil => simp
  | cons o os ih => simp [ih, Nat.add_assoc]

/-- Uniform operation bounds imply a bound proportional to history length. -/
theorem totalCost_le_length_mul (charge : D.State → D.Op → Nat) (T : Nat)
    (h : ∀ s o, D.valid s o → charge s o ≤ T) {s : D.State} {os : List D.Op}
    (hv : D.ValidHistory s os) : D.totalCost charge s os ≤ os.length * T := by
  induction os generalizing s with
  | nil => simp
  | cons o os ih =>
    have hstep := h s o hv.1
    have hrest := ih hv.2
    simp only [totalCost_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A constant charge `K` per operation totals `K` times the length of the history. -/
theorem totalCost_const (K : Nat) (s : D.State) (os : List D.Op) :
    D.totalCost (fun _ _ => K) s os = os.length * K := by
  induction os generalizing s with
  | nil => simp
  | cons o os ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- A unit charge per operation totals the length of the history. -/
theorem totalCost_one (s : D.State) (os : List D.Op) :
    D.totalCost (fun _ _ => 1) s os = os.length := by
  simpa using D.totalCost_const 1 s os

/-- Interpret a client mathematically, retaining its chosen operation history. -/
def runClient {α : Type y} (s : D.State) : D.Client α → α × D.State × List D.Op
  | .pure a => (a, s, [])
  | .liftBind o k =>
    let next := D.stepFn s o
    let rest := runClient next.1 (k next.2)
    (rest.1, rest.2.1, o :: rest.2.2)

/-- Interpreting a pure client returns its value, preserves the state, and records no operations. -/
@[simp, nolint simpNF] theorem runClient_pure {α : Type y} (s : D.State) (a : α) :
    D.runClient s (@PFunctor.FreeM.pure (no_index D.signature) α a) = (a, s, []) := rfl

/-- Interpreting a `pure` client returns its value, preserves the state, and records no
operations. -/
@[simp] theorem runClient_pure' {α : Type y} (s : D.State) (a : α) :
    D.runClient s (@Pure.pure (no_index D.Client) _ α a) = (a, s, []) := rfl

/-- Interpreting a single lifted operation steps the specification once. -/
@[simp] theorem runClient_lift (s : D.State) (o : D.Op) :
    @runClient D f _ (no_index (D.Result o)) s (@PFunctor.FreeM.lift (no_index D.signature) o) =
      ((D.stepFn s o).2, (D.stepFn s o).1, [o]) := rfl

/-- Interpreting an operation call steps the specification and continues from the resulting state
and answer. -/
@[simp, nolint simpNF] theorem runClient_liftBind {α : Type y} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    D.runClient s (@PFunctor.FreeM.liftBind (no_index D.signature) α o k) =
      ((D.runClient (D.stepFn s o).1 (k (D.stepFn s o).2)).1,
       (D.runClient (D.stepFn s o).1 (k (D.stepFn s o).2)).2.1,
       o :: (D.runClient (D.stepFn s o).1 (k (D.stepFn s o).2)).2.2) := rfl

/-- Interpreting a lifted operation bound to a continuation steps the specification and continues
from the resulting state and answer. -/
@[simp] theorem runClient_lift_bind {α : Type y} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    D.runClient s
        (@PFunctor.FreeM.bind (no_index D.signature) (no_index (D.Result o)) α
          (@PFunctor.FreeM.lift (no_index D.signature) o) k) =
      ((D.runClient (D.stepFn s o).1 (k (D.stepFn s o).2)).1,
       (D.runClient (D.stepFn s o).1 (k (D.stepFn s o).2)).2.1,
       o :: (D.runClient (D.stepFn s o).1 (k (D.stepFn s o).2)).2.2) := rfl

/-- Interpreting a lifted operation monadically bound to a continuation steps the specification and
continues from the resulting state and answer. -/
@[simp] theorem runClient_lift_bind' {α : Type w} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    D.runClient s
        (@Bind.bind (no_index D.Client) _ (no_index (D.Result o)) α
          (@PFunctor.FreeM.lift (no_index D.signature) o) k) =
      ((D.runClient (D.stepFn s o).1 (k (D.stepFn s o).2)).1,
       (D.runClient (D.stepFn s o).1 (k (D.stepFn s o).2)).2.1,
       o :: (D.runClient (D.stepFn s o).1 (k (D.stepFn s o).2)).2.2) := rfl

/-- The actual history chosen by an adaptive client has its computed final state. -/
theorem run_runClient {α : Type y} (p : D.Client α) (s : D.State) :
    (D.run s (D.runClient s p).2.2).1 = (D.runClient s p).2.1 := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o k ih => exact ih (D.stepFn s o).2 (D.stepFn s o).1

end Spec

namespace Spec

variable {D : Spec.{u, v, w}} {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
  [D.HasStepFn f] {α β : Type y}

/-- Admissibility splits at the mathematical state reached by the first history. -/
theorem validHistory_append (s : D.State) (xs ys : List D.Op) :
    D.ValidHistory s (xs ++ ys) ↔
      D.ValidHistory s xs ∧ D.ValidHistory (D.run s xs).1 ys := by
  induction xs generalizing s with
  | nil => simp
  | cons o xs ih => simp [ih, and_assoc]

/-- Sequential interpretation concatenates the histories actually selected by the client. -/
theorem runClient_bind (p : D.Client α) (k : α → D.Client β) (s : D.State) :
    D.runClient s (p.bind k) =
      let first := D.runClient s p
      let rest := D.runClient first.2.1 (k first.1)
      (rest.1, rest.2.1, first.2.2 ++ rest.2.2) := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o cont ih =>
    exact congrArg (fun r : β × D.State × List D.Op => (r.1, r.2.1, o :: r.2.2))
      (ih (D.stepFn s o).2 (D.stepFn s o).1)

/-- On a deterministic specification (`[D.HasStepFn f]`), demonic operation-sequence admissibility
`ValidOpSeq` coincides with `D.ValidHistory`. -/
@[simp]
theorem validOpSeq_iff_validHistory (s : D.State) (ops : List D.Op) :
    D.ValidOpSeq s ops ↔ D.ValidHistory s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    rw [validOpSeq_cons, validHistory_cons]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h
      exact (ih (D.stepFn s o).1).mp (h (D.stepFn s o).1 (D.stepFn s o).2 (D.step_stepFn s o))
    · intro h s' a hstep
      have heq := (D.step_iff_stepFn s o s' a).mp hstep
      have hs' : s' = (D.stepFn s o).1 := congrArg Prod.fst heq
      subst hs'
      exact (ih (D.stepFn s o).1).mpr h

/-- The unique canonical transcript determined by a deterministic specification `D` on an
operation list `os` from state `s`. -/
def canonicalTranscript (D : Spec.{u, v, w})
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (s : D.State) : List D.Op → D.Transcript
  | [] => []
  | o :: os =>
    let next := D.stepFn s o
    ⟨o, next.2, next.1⟩ :: D.canonicalTranscript next.1 os

@[simp]
theorem canonicalTranscript_nil (s : D.State) : D.canonicalTranscript s [] = [] := rfl

@[simp]
theorem canonicalTranscript_cons (s : D.State) (o : D.Op) (os : List D.Op) :
    D.canonicalTranscript s (o :: os) =
      ⟨o, (D.stepFn s o).2, (D.stepFn s o).1⟩ :: D.canonicalTranscript (D.stepFn s o).1 os := rfl

/-- The underlying operation list of `D.canonicalTranscript s os` is `os`. -/
@[simp]
theorem canonicalTranscript_ops (s : D.State) (os : List D.Op) :
    (D.canonicalTranscript s os).ops = os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp [ih]

/-- The labels of `D.canonicalTranscript s os` coincide with `(D.run s os).2`. -/
@[simp]
theorem canonicalTranscript_labels (s : D.State) (os : List D.Op) :
    (D.canonicalTranscript s os).labels = (D.run s os).2 := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp [ih]

/-- `totalCostTranscript` along `D.canonicalTranscript s os` equals `D.totalCost charge s os`. -/
@[simp]
theorem totalCostTranscript_canonicalTranscript (charge : D.State → D.Op → ℕ) (s : D.State)
    (os : List D.Op) :
    D.totalCostTranscript charge s (D.canonicalTranscript s os) = D.totalCost charge s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp [ih]

/-- Every admissible operation history executes canonically to `(D.run s os).1`. -/
theorem validTranscript_canonicalTranscript {s : D.State} {os : List D.Op}
    (hv : D.ValidHistory s os) :
    D.ValidTranscript s (D.canonicalTranscript s os) (D.run s os).1 := by
  induction os generalizing s with
  | nil => exact .nil s
  | cons o os ih =>
    exact .cons _ hv.1 (D.step_stepFn s o) (ih hv.2)

/-- On a deterministic specification (`[D.HasStepFn f]`), `ValidTranscript s tr s'` collapses
uniquely to `D.ValidHistory s tr.ops`, `s' = (D.run s tr.ops).1`, and
`tr = D.canonicalTranscript s tr.ops`. -/
theorem validTranscript_iff_run (s : D.State) (tr : D.Transcript) (s' : D.State) :
    D.ValidTranscript s tr s' ↔
      D.ValidHistory s tr.ops ∧
      s' = (D.run s tr.ops).1 ∧
      tr = D.canonicalTranscript s tr.ops := by
  induction tr generalizing s with
  | nil =>
    simp [eq_comm]
  | cons st tr ih =>
    rcases st with ⟨o, a, s₁⟩
    rw [validTranscript_cons_iff]
    simp only [Transcript.ops_cons, validHistory_cons, run_cons, canonicalTranscript_cons,
      step_iff_stepFn (D := D)]
    constructor
    · rintro ⟨hv_o, heq, htr⟩
      have hs₁ : s₁ = (D.stepFn s o).1 := congrArg Prod.fst heq
      have ha : a = (D.stepFn s o).2 := congrArg Prod.snd heq
      subst hs₁; subst ha
      obtain ⟨hv_rest, rfl, htr_eq⟩ := (ih (D.stepFn s o).1).mp htr
      exact ⟨⟨hv_o, hv_rest⟩, rfl, congrArg _ htr_eq⟩
    · rintro ⟨⟨hv_o, hv_rest⟩, rfl, htr_eq⟩
      injection htr_eq with hst htr_tail
      cases hst
      exact ⟨hv_o, Prod.mk.eta, (ih (D.stepFn s o).1).mpr ⟨hv_rest, rfl, htr_tail⟩⟩

/-- On a deterministic specification (`[D.HasStepFn f]`), demonic client admissibility
`DemonicValid s p` is equivalent to `D.ValidHistory s (D.runClient s p).2.2`. -/
theorem demonicValid_iff_validHistory_runClient (s : D.State) (p : D.Client α) :
    D.DemonicValid s p ↔ D.ValidHistory s (D.runClient s p).2.2 := by
  induction p generalizing s with
  | pure a =>
    exact ⟨fun _ => trivial, fun _ => .pure s a⟩
  | liftBind o k ih =>
    rw [demonicValid_liftBind_iff, runClient_liftBind, validHistory_cons]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h
      exact (ih (D.stepFn s o).2 (D.stepFn s o).1).mp
        (h (D.stepFn s o).1 (D.stepFn s o).2 (D.step_stepFn s o))
    · intro h s' a hstep
      have heq := (D.step_iff_stepFn s o s' a).mp hstep
      have hs' : s' = (D.stepFn s o).1 := congrArg Prod.fst heq
      have ha : a = (D.stepFn s o).2 := congrArg Prod.snd heq
      subst hs'; subst ha
      exact (ih (D.stepFn s o).2 (D.stepFn s o).1).mpr h

/-- Every client with an admissible deterministic history executes canonically. -/
theorem clientRun_canonical (s : D.State) (p : D.Client α)
    (hv : D.ValidHistory s (D.runClient s p).2.2) :
    D.ClientRun s p (D.runClient s p).1 (D.runClient s p).2.1
      (D.canonicalTranscript s (D.runClient s p).2.2) := by
  induction p generalizing s with
  | pure a =>
    exact .pure s a
  | liftBind o k ih =>
    exact .liftBind o k (D.stepFn s o).2 hv.1 (D.step_stepFn s o)
      (ih (D.stepFn s o).2 (D.stepFn s o).1 hv.2)

private theorem clientRun_imp_ofFn {s : D.State} {p : D.Client α}
    {v : α} {s' : D.State} {tr : D.Transcript}
    (h : D.ClientRun s p v s' tr) :
    D.ValidHistory s (D.runClient s p).2.2 ∧
    v = (D.runClient s p).1 ∧
    s' = (D.runClient s p).2.1 ∧
    tr = D.canonicalTranscript s (D.runClient s p).2.2 := by
  induction h with
  | pure s a =>
    exact ⟨trivial, rfl, rfl, rfl⟩
  | @liftBind s s₁ s₂ o k res v tr hv hstep _ ih =>
    have heq := (D.step_iff_stepFn s o s₁ res).mp hstep
    have hs₁ : s₁ = (D.stepFn s o).1 := congrArg Prod.fst heq
    have hres : res = (D.stepFn s o).2 := congrArg Prod.snd heq
    subst hs₁; subst hres
    obtain ⟨hv_rest, rfl, rfl, rfl⟩ := ih
    exact ⟨⟨hv, hv_rest⟩, rfl, rfl, rfl⟩

/-- On a deterministic specification (`[D.HasStepFn f]`), `ClientRun` collapses uniquely to
`D.runClient` and `D.ValidHistory`. -/
theorem clientRun_iff_runClient (s : D.State) (p : D.Client α) (v : α) (s' : D.State)
    (tr : D.Transcript) :
    D.ClientRun s p v s' tr ↔
      D.ValidHistory s (D.runClient s p).2.2 ∧
      v = (D.runClient s p).1 ∧
      s' = (D.runClient s p).2.1 ∧
      tr = D.canonicalTranscript s (D.runClient s p).2.2 :=
  ⟨D.clientRun_imp_ofFn, fun ⟨hv, h₁, h₂, h₃⟩ =>
    h₁ ▸ h₂ ▸ h₃ ▸ D.clientRun_canonical s p hv⟩

end Spec

variable {D : Spec.{u, v, w}} {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
  [D.HasStepFn f] {α β : Type y}

/-- Observe results and state without displaying the operation history. -/
def eval (D : Spec.{u, v, w}) {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (p : D.Client α) (s : D.State) : α × D.State :=
  ((D.runClient s p).1, (D.runClient s p).2.1)

/-- Evaluating a pure client returns its value and leaves the state unchanged. -/
@[simp, nolint simpNF] theorem eval_pure (s : D.State) (a : α) :
    eval D (@PFunctor.FreeM.pure (no_index D.signature) α a) s = (a, s) := rfl

/-- Evaluating a `pure` client returns its value and leaves the state unchanged. -/
@[simp] theorem eval_pure' (s : D.State) (a : α) :
    eval D (@Pure.pure (no_index D.Client) _ α a) s = (a, s) := rfl

/-- Evaluating a single lifted operation steps the state and returns its answer. -/
@[simp] theorem eval_lift (s : D.State) (o : D.Op) :
    @eval (no_index (D.Result o)) D f _ (@PFunctor.FreeM.lift (no_index D.signature) o) s =
      ((D.stepFn s o).2, (D.stepFn s o).1) := rfl

/-- Evaluating an operation call steps the state and continues with the observed answer. -/
@[simp, nolint simpNF] theorem eval_liftBind (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    eval D (@PFunctor.FreeM.liftBind (no_index D.signature) α o k) s =
      eval D (k (D.stepFn s o).2) (D.stepFn s o).1 := rfl

/-- Evaluating a lifted operation bound to a continuation steps the state and continues with the
observed answer. -/
@[simp] theorem eval_lift_bind (s : D.State) (o : D.Op) (k : D.Result o → D.Client α) :
    eval D
        (@PFunctor.FreeM.bind (no_index D.signature) (no_index (D.Result o)) α
          (@PFunctor.FreeM.lift (no_index D.signature) o) k) s =
      eval D (k (D.stepFn s o).2) (D.stepFn s o).1 := rfl

/-- Evaluating a lifted operation monadically bound to a continuation steps the state and continues
with the observed answer. -/
@[simp] theorem eval_lift_bind' {α : Type w} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    eval D
        (@Bind.bind (no_index D.Client) _ (no_index (D.Result o)) α
          (@PFunctor.FreeM.lift (no_index D.signature) o) k) s =
      eval D (k (D.stepFn s o).2) (D.stepFn s o).1 := rfl

/-- Evaluating `p.bind k` evaluates `p`, then the continuation `k` at its result from the state
`p` reaches. -/
theorem eval_bind (p : D.Client α) (k : α → D.Client β) (s : D.State) :
    eval D (p.bind k) s = eval D (k (eval D p s).1) (eval D p s).2 := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o cont ih => exact ih _ _

/-- `eval` agrees with interpreting the free monad into `StateM D.State` via `PFunctor.FreeM.liftM`
when states, operation answers, and client results share a universe. -/
theorem eval_eq_liftM {D : Spec.{u, v, u}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {α : Type u} (p : D.Client α) (s : D.State) :
    (p.liftM (m := StateM D.State) fun o s => ((D.stepFn s o).2, (D.stepFn s o).1)).run s =
      eval D p s := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o k ih => exact ih (D.stepFn s o).2 (D.stepFn s o).1

/-- Two independent abstract components. A backend must separately justify their independence. -/
abbrev product (D E : Spec.{u, v, w}) : Spec where
  State := D.State × E.State
  Op := D.Op ⊕ E.Op
  Result
    | .inl o => D.Result o
    | .inr o => E.Result o
  step s
    | .inl o, s', a => D.step s.1 o s'.1 a ∧ s'.2 = s.2
    | .inr o, s', a => s'.1 = s.1 ∧ E.step s.2 o s'.2 a
  valid s
    | .inl o => D.valid s.1 o
    | .inr o => E.valid s.2 o

/-- Stepping the left component of a product specification steps the left state and preserves the
right state. -/
@[simp] theorem product_step_inl (D E : Spec.{u, v, w}) (s s' : D.State × E.State) (o : D.Op)
    (a : D.Result o) :
    (product D E).step s (.inl o) s' a ↔ D.step s.1 o s'.1 a ∧ s'.2 = s.2 := Iff.rfl

/-- Stepping the right component of a product specification preserves the left state and steps the
right state. -/
@[simp] theorem product_step_inr (D E : Spec.{u, v, w}) (s s' : D.State × E.State) (o : E.Op)
    (a : E.Result o) :
    (product D E).step s (.inr o) s' a ↔ s'.1 = s.1 ∧ E.step s.2 o s'.2 a := Iff.rfl

/-- Admissibility of a left operation in a product specification depends only on the left state. -/
@[simp] theorem product_valid_inl (D E : Spec.{u, v, w}) (s : D.State × E.State) (o : D.Op) :
    (product D E).valid s (.inl o) ↔ D.valid s.1 o := Iff.rfl

/-- Admissibility of a right operation in a product specification depends only on the right
state. -/
@[simp] theorem product_valid_inr (D E : Spec.{u, v, w}) (s : D.State × E.State) (o : E.Op) :
    (product D E).valid s (.inr o) ↔ E.valid s.2 o := Iff.rfl

/-- Product of two total specifications is total. -/
instance instTotalProduct (D E : Spec.{u, v, w}) [D.Total] [E.Total] : (product D E).Total where
  step_total
    | s, .inl o, hv => by
      obtain ⟨s₁', a, hstep⟩ := D.exists_step hv
      exact ⟨(s₁', s.2), a, hstep, rfl⟩
    | s, .inr o, hv => by
      obtain ⟨s₂', a, hstep⟩ := E.exists_step hv
      exact ⟨(s.1, s₂'), a, rfl, hstep⟩

/-- Product of two deterministic specifications is deterministic. -/
instance instDeterministicProduct (D E : Spec.{u, v, w}) [D.Deterministic] [E.Deterministic] :
    (product D E).Deterministic where
  step_deterministic {_ o _ _ _ _} h₁ h₂ := by
    cases o with
    | inl o =>
      obtain ⟨h₁, he₁⟩ := h₁
      obtain ⟨h₂, he₂⟩ := h₂
      obtain ⟨hs, ha⟩ := Spec.Deterministic.step_deterministic h₁ h₂
      exact ⟨Prod.ext hs (he₁.trans he₂.symm), ha⟩
    | inr o =>
      obtain ⟨hd₁, h₁⟩ := h₁
      obtain ⟨hd₂, h₂⟩ := h₂
      obtain ⟨hs, ha⟩ := Spec.Deterministic.step_deterministic h₁ h₂
      exact ⟨Prod.ext (hd₁.trans hd₂.symm) hs, ha⟩

/-- The canonical transition function of a product of two deterministic specifications. -/
abbrev productStepFn (D E : Spec.{u, v, w})
    (fD : (s : D.State) → (o : D.Op) → D.State × D.Result o)
    (fE : (s : E.State) → (o : E.Op) → E.State × E.Result o)
    (s : (product D E).State) :
    (o : (product D E).Op) → (product D E).State × (product D E).Result o
  | .inl o => let r := fD s.1 o; ((r.1, s.2), r.2)
  | .inr o => let r := fE s.2 o; ((s.1, r.1), r.2)

instance instHasStepFnProduct (D E : Spec.{u, v, w})
    {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (s : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE] :
    (product D E).HasStepFn (productStepFn D E fD fE) where
  step_iff
    | ⟨s₁, s₂⟩, .inl o, ⟨s'₁, s'₂⟩, (a : D.Result o) => by
      simp only [productStepFn, Spec.HasStepFn.step_iff, Prod.ext_iff, and_assoc]
      exact and_congr_right fun _ => and_comm
    | ⟨s₁, s₂⟩, .inr o, ⟨s'₁, s'₂⟩, (a : E.Result o) => by
      simp [productStepFn, Spec.HasStepFn.step_iff, Prod.ext_iff, and_assoc]

instance instHasStepFnProductOfFn
    {State₁ : Type u} {Op₁ : Type v} {Result₁ : Op₁ → Type w}
    {State₂ : Type u} {Op₂ : Type v} {Result₂ : Op₂ → Type w}
    (fD : (s : State₁) → (o : Op₁) → State₁ × Result₁ o)
    (validD : State₁ → Op₁ → Prop)
    (fE : (s : State₂) → (o : Op₂) → State₂ × Result₂ o)
    (validE : State₂ → Op₂ → Prop) :
    (product (Spec.ofFn fD validD) (Spec.ofFn fE validE)).HasStepFn
      (productStepFn (Spec.ofFn fD validD) (Spec.ofFn fE validE) fD fE) :=
  instHasStepFnProduct (Spec.ofFn fD validD) (Spec.ofFn fE validE)

@[simp] theorem product_stepFn_inl (D E : Spec.{u, v, w})
    {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (s : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE]
    (s : D.State × E.State) (o : D.Op) :
    (product D E).stepFn s (.inl o) = (((D.stepFn s.1 o).1, s.2), (D.stepFn s.1 o).2) := rfl

@[simp] theorem product_stepFn_inr (D E : Spec.{u, v, w})
    {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (s : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE]
    (s : D.State × E.State) (o : E.Op) :
    (product D E).stepFn s (.inr o) = ((s.1, (E.stepFn s.2 o).1), (E.stepFn s.2 o).2) := rfl

end Cslib.Stateful
