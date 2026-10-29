/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Semantics.Stateful.Amortized
public import Complexity.Foundations.Semantics.Stateful.CostHoare
public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Relational stateful specifications, demonic adaptive clients, and angelic realizations

A relational stateful specification (`Cslib.Stateful.RelSpec`) generalizes `Cslib.Stateful.Spec`
from a deterministic transition function `step : State → (o : Op) → State × Result o` to a
transition relation `step : State → (o : Op) → State → Result o → Prop`. This allows data-structure
specifications to leave implementation choices (such as which free slot or handle is allocated, or
how equal-key ties are broken) underspecified in the abstract interface while keeping internal
allocator state hidden inside concrete representation invariants.

The semantics is **demonic** for callers and **angelic** for implementations:
* An adaptive client `p : D.Client α` is demonically admissible (`D.DemonicValid s p`) when each
  issued operation is admissible (`D.valid`) and the continuation remains admissible under *every*
  outcome `(s', a)` permitted by `D.step`. Caller postconditions (`D.Hoare`) and abstract cost
  budgets (`D.CostHoare`) hold across *all* permitted client runs (`D.ClientRun`).
* A concrete backend realization (`RelRealization`, `RelAmortized`) is angelic in the abstract
  post-state: each concrete operation execution witnesses *some* permitted abstract transition
  `D.step s o s' a` maintaining the representation invariant and potential inequality.

Every deterministic `D : Spec` embeds into `RelSpec` with zero overhead via `Spec.toRelSpec`
(preserving `State`, `Op`, `Result`, `valid`, `signature`, and `Client α` definitionally), and
`DemonicValid`, `ClientRun`, `Hoare`, and `CostHoare` on `D.toRelSpec` are equivalent to their
deterministic counterparts on `D`.

## Main definitions

* `Cslib.Stateful.RelSpec`: relational stateful specification with `State`, `Op`, `Result`,
  transition relation `step`, and input admissibility `valid`.
* `Cslib.Stateful.RelSpec.Total`: typeclass asserting that every admissible `(s, o)` has at least
  one permitted outcome `(s', a)`.
* `Cslib.Stateful.Spec.toRelSpec`: zero-cost embedding of a deterministic `Spec` into `RelSpec`.
* `Cslib.Stateful.RelSpec.toLTS`: projection of a `RelSpec` to a `Cslib.LTS` labelled by
  input-output pairs `Σ o : D.Op, D.Result o`.
* `Cslib.Stateful.RelSpec.Step`, `Cslib.Stateful.RelSpec.Transcript`,
  `Cslib.Stateful.RelSpec.ValidTranscript`, `Cslib.Stateful.RelSpec.ValidOpSeq`,
  `Cslib.Stateful.RelSpec.totalCost`, `Cslib.Stateful.RelSpec.totalCostOutcome`: execution
  transcripts, non-adaptive operation-sequence admissibility, and abstract cost accounting.
* `Cslib.Stateful.RelSpec.ClientRun`, `Cslib.Stateful.RelSpec.DemonicValid`,
  `Cslib.Stateful.RelSpec.Hoare`, `Cslib.Stateful.RelSpec.CostHoare`: adaptive client runs,
  demonic admissibility, and compositional Hoare / CostHoare triples.
* `Cslib.Stateful.RelRealization`, `Cslib.Stateful.RelBound`, `Cslib.Stateful.RelAmortized`:
  angelic representation simulation and potential-method certificates over `Execution` / `Executes`.

## Main results

* `Cslib.Stateful.Spec.toRelSpec_demonicValid_iff`,
  `Cslib.Stateful.Spec.toRelSpec_clientRun_iff`,
  `Cslib.Stateful.Spec.toRelSpec_hoare_iff`,
  `Cslib.Stateful.Spec.toRelSpec_costHoare_iff`: exact collapse of relational client semantics to
  deterministic `Spec` semantics on `D.toRelSpec`.
* `Cslib.Stateful.RelRealization.correct_client`,
  `Cslib.Stateful.RelRealization.exists_executes`: soundness and existence of native client
  executions under `DemonicValid`.
* `Cslib.Stateful.RelAmortized.executes_le`, `Cslib.Stateful.RelAmortized.run_client_amortized`:
  amortized potential telescoping along adaptive client executions.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 17][CLRS2009]
* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*][Sangiorgi2011]
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x y

/-! ## Core relational specification and totality -/

/-- A relational stateful specification with state type `State`, operation type `Op`,
operation-dependent observation family `Result`, transition relation `step`, and input
admissibility predicate `valid`. -/
structure RelSpec where
  /-- Mathematical states, independent of a concrete storage representation. -/
  State : Type u
  /-- Operations available to clients. -/
  Op : Type v
  /-- The observation type returned by each operation. -/
  Result : Op → Type w
  /-- Relational step specification: `step s o s' a` holds when transitioning from `s` to `s'`
  and returning `a : Result o` is a permitted outcome of `o`. -/
  step : State → (o : Op) → State → Result o → Prop
  /-- Preconditions under which an operation's implementation must satisfy its contract. -/
  valid : State → Op → Prop := fun _ _ => True

namespace RelSpec

variable (D : RelSpec.{u, v, w})

/-- The set of permitted `(nextState, result)` outcomes of operation `o` from state `s`. -/
def outcomes (s : D.State) (o : D.Op) : Set (D.State × D.Result o) :=
  {p | D.step s o p.1 p.2}

/-- Membership in `D.outcomes s o` unfolds to `D.step s o`. -/
@[simp]
theorem mem_outcomes_iff (s : D.State) (o : D.Op) (p : D.State × D.Result o) :
    p ∈ D.outcomes s o ↔ D.step s o p.1 p.2 := Iff.rfl

/-- A relational specification is total on admissible inputs if every valid `(s, o)` admits at
least one permitted outcome `(s', a)`. -/
class Total : Prop where
  /-- Every admissible operation call has at least one permitted post-state and result. -/
  step_total : ∀ s o, D.valid s o → ∃ s' a, D.step s o s' a

/-- Obtain a permitted outcome `(s', a)` for an admissible operation under `[D.Total]`. -/
theorem exists_step [D.Total] {s : D.State} {o : D.Op} (hv : D.valid s o) :
    ∃ s' a, D.step s o s' a :=
  Total.step_total s o hv

/-- The polynomial operation signature `⟨D.Op, D.Result⟩`. -/
abbrev signature : PFunctor.{v, w} := ⟨D.Op, D.Result⟩

instance : Coe RelSpec.{u, v, w} PFunctor.{v, w} := ⟨RelSpec.signature⟩

/-- An adaptive client over `D`: each continuation may branch on the observed operation result. -/
abbrev Client (α : Type y) : Type (max v w y) := D.signature.FreeM α

/-- Invoke a single operation `o : D.Op` in an adaptive `D.Client`. -/
abbrev call (o : D.Op) : D.Client (D.Result o) := .liftBind o .pure

/-- An input-output transition label pairing an operation `o : D.Op` with its result `a`. -/
abbrev Label : Type (max v w) := Σ o : D.Op, D.Result o

/-- View a relational stateful specification as a labelled transition system (`Cslib.LTS`)
labelled by input-output pairs `⟨o, a⟩ : Σ o : D.Op, D.Result o`. -/
def toLTS : LTS D.State D.Label where
  Tr s lbl s' := D.step s lbl.1 s' lbl.2

/-- A transition in `D.toLTS` is a step of `D`. -/
@[simp]
theorem toLTS_tr (s s' : D.State) (lbl : D.Label) :
    D.toLTS.Tr s lbl s' ↔ D.step s lbl.1 s' lbl.2 := Iff.rfl

end RelSpec

/-! ## Zero-cost embedding of deterministic specifications (`Spec.toRelSpec`) -/

/-- Embed a deterministic `Stateful.Spec` as a relational `RelSpec` whose transition relation
holds if and only if `(s', a) = D.step s o`. -/
abbrev Spec.toRelSpec (D : Spec.{u, v, w}) : RelSpec.{u, v, w} where
  State := D.State
  Op := D.Op
  Result := D.Result
  step s o s' a := (s', a) = D.step s o
  valid := D.valid

namespace Spec

variable (D : Spec.{u, v, w})

/-- `toRelSpec` preserves the state type definitionally. -/
@[simp]
theorem toRelSpec_state : D.toRelSpec.State = D.State := rfl

/-- `toRelSpec` preserves the operation type definitionally. -/
@[simp]
theorem toRelSpec_op : D.toRelSpec.Op = D.Op := rfl

/-- `toRelSpec` preserves the result family definitionally. -/
@[simp]
theorem toRelSpec_result : D.toRelSpec.Result = D.Result := rfl

/-- A step in `D.toRelSpec` holds iff `(s', a) = D.step s o`. -/
@[simp]
theorem toRelSpec_step (s : D.State) (o : D.Op) (s' : D.State) (a : D.Result o) :
    D.toRelSpec.step s o s' a ↔ (s', a) = D.step s o := Iff.rfl

/-- `toRelSpec` preserves the admissibility predicate definitionally. -/
@[simp]
theorem toRelSpec_valid (s : D.State) (o : D.Op) :
    D.toRelSpec.valid s o ↔ D.valid s o := Iff.rfl

/-- `toRelSpec` preserves the polynomial signature definitionally. -/
@[simp]
theorem toRelSpec_signature : D.toRelSpec.signature = D.signature := rfl

/-- `toRelSpec` preserves the adaptive client type definitionally. -/
@[simp]
theorem toRelSpec_client (α : Type y) : D.toRelSpec.Client α = D.Client α := rfl

/-- Every embedded deterministic specification is automatically total. -/
instance : D.toRelSpec.Total where
  step_total s o _ := ⟨(D.step s o).1, (D.step s o).2, Prod.mk.eta⟩

/-- Transitions in `D.toRelSpec.toLTS` agree with `D.toFLTS` on states and `(D.step s o).2` on
observations. -/
theorem toRelSpec_toLTS_tr (s s' : D.State) (o : D.Op) (a : D.Result o) :
    D.toRelSpec.toLTS.Tr s ⟨o, a⟩ s' ↔ s' = D.toFLTS.tr s o ∧ a = (D.step s o).2 := by
  simp [RelSpec.toLTS, Spec.toRelSpec, Spec.toFLTS, Prod.ext_iff]

/-- The labelled transition system of an embedded deterministic specification is deterministic. -/
instance : D.toRelSpec.toLTS.Deterministic where
  deterministic s lbl s₁ s₂ h₁ h₂ := by
    have h₁' := congrArg Prod.fst h₁
    have h₂' := congrArg Prod.fst h₂
    exact h₁'.trans h₂'.symm

/-- Multi-step execution `D.run` produces a valid multi-step trace in `D.toRelSpec.toLTS` ending
at `D.toFLTS.mtr s os`. -/
theorem toRelSpec_toLTS_mtr_run (s : D.State) (os : List D.Op) :
    D.toRelSpec.toLTS.MTr s (D.run s os).2 (D.toFLTS.mtr s os) := by
  induction os generalizing s with
  | nil => exact .refl
  | cons o os ih =>
    exact .stepL Prod.mk.eta (ih (D.step s o).1)

end Spec

/-! ## Transcripts, non-adaptive operation sequences, and cost accounting -/

namespace RelSpec

variable (D : RelSpec.{u, v, w})

/-- One recorded step of a relational specification: the issued operation `op`, its returned
observation `result`, and the resulting post-state `nextState`. -/
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
def Transcript.ops {D : RelSpec.{u, v, w}} (tr : D.Transcript) : List D.Op :=
  tr.map Step.op

/-- Extract the `Cslib.LTS` input-output labels from a transcript. -/
def Transcript.labels {D : RelSpec.{u, v, w}} (tr : D.Transcript) : List D.Label :=
  tr.map fun st => ⟨st.op, st.result⟩

@[simp]
theorem Transcript.ops_nil {D : RelSpec.{u, v, w}} :
    Transcript.ops ([] : D.Transcript) = [] := rfl

@[simp]
theorem Transcript.ops_cons {D : RelSpec.{u, v, w}} (st : D.Step) (tr : D.Transcript) :
    Transcript.ops (st :: tr) = st.op :: Transcript.ops tr := rfl

@[simp]
theorem Transcript.ops_append {D : RelSpec.{u, v, w}} (tr₁ tr₂ : D.Transcript) :
    Transcript.ops (tr₁ ++ tr₂) = Transcript.ops tr₁ ++ Transcript.ops tr₂ :=
  List.map_append

@[simp]
theorem Transcript.length_ops {D : RelSpec.{u, v, w}} (tr : D.Transcript) :
    (Transcript.ops tr).length = tr.length :=
  List.length_map _

@[simp]
theorem Transcript.labels_nil {D : RelSpec.{u, v, w}} :
    Transcript.labels ([] : D.Transcript) = [] := rfl

@[simp]
theorem Transcript.labels_cons {D : RelSpec.{u, v, w}} (st : D.Step) (tr : D.Transcript) :
    Transcript.labels (st :: tr) = ⟨st.op, st.result⟩ :: Transcript.labels tr := rfl

@[simp]
theorem Transcript.labels_append {D : RelSpec.{u, v, w}} (tr₁ tr₂ : D.Transcript) :
    Transcript.labels (tr₁ ++ tr₂) = Transcript.labels tr₁ ++ Transcript.labels tr₂ :=
  List.map_append

@[simp]
theorem Transcript.length_labels {D : RelSpec.{u, v, w}} (tr : D.Transcript) :
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
theorem validTranscript_nil_iff {D : RelSpec.{u, v, w}} (s s' : D.State) :
    D.ValidTranscript s [] s' ↔ s = s' := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil s

/-- A nonempty transcript is valid iff its head step is admissible and permitted and its tail is
valid from `st.nextState`. -/
@[simp]
theorem validTranscript_cons_iff {D : RelSpec.{u, v, w}} (s s' : D.State) (st : D.Step)
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
theorem ValidTranscript.append {D : RelSpec.{u, v, w}} {s s₁ s₂ : D.State}
    {tr₁ tr₂ : D.Transcript} (h₁ : D.ValidTranscript s tr₁ s₁)
    (h₂ : D.ValidTranscript s₁ tr₂ s₂) :
    D.ValidTranscript s (tr₁ ++ tr₂) s₂ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons st hv hstep _ ih => exact .cons st hv hstep (ih h₂)

/-- Every valid transcript projects to a multi-step transition in `D.toLTS`. -/
theorem ValidTranscript.toLTS_mtr {D : RelSpec.{u, v, w}} {s s' : D.State}
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
def totalCost (charge : D.State → D.Op → ℕ) : D.State → D.Transcript → ℕ
  | _, [] => 0
  | s, st :: tr => charge s st.op + totalCost charge st.nextState tr

/-- Outcome-dependent charges summed along a transcript, where each step charge may also inspect
the post-state `st.nextState` and result `st.result`. -/
def totalCostOutcome (charge : D.State → (o : D.Op) → D.State → D.Result o → ℕ) :
    D.State → D.Transcript → ℕ
  | _, [] => 0
  | s, st :: tr =>
    charge s st.op st.nextState st.result + totalCostOutcome charge st.nextState tr

@[simp]
theorem totalCost_nil (charge : D.State → D.Op → ℕ) (s : D.State) :
    D.totalCost charge s [] = 0 := rfl

@[simp]
theorem totalCost_cons (charge : D.State → D.Op → ℕ) (s : D.State) (st : D.Step)
    (tr : D.Transcript) :
    D.totalCost charge s (st :: tr) = charge s st.op + D.totalCost charge st.nextState tr := rfl

@[simp]
theorem totalCostOutcome_nil (charge : D.State → (o : D.Op) → D.State → D.Result o → ℕ)
    (s : D.State) :
    D.totalCostOutcome charge s [] = 0 := rfl

@[simp]
theorem totalCostOutcome_cons (charge : D.State → (o : D.Op) → D.State → D.Result o → ℕ)
    (s : D.State) (st : D.Step) (tr : D.Transcript) :
    D.totalCostOutcome charge s (st :: tr) =
      charge s st.op st.nextState st.result + D.totalCostOutcome charge st.nextState tr := rfl

/-- `totalCost` is the special case of `totalCostOutcome` that ignores the post-state and
result. -/
theorem totalCost_eq_totalCostOutcome (charge : D.State → D.Op → ℕ) (s : D.State)
    (tr : D.Transcript) :
    D.totalCost charge s tr = D.totalCostOutcome (fun s o _ _ => charge s o) s tr := by
  induction tr generalizing s with
  | nil => rfl
  | cons st tr ih => simp [ih]

/-- Along a valid transcript prefix `D.ValidTranscript s tr₁ s₁`, `totalCost` splits additively at
the intermediate state `s₁`. -/
theorem totalCost_append {D : RelSpec.{u, v, w}} (charge : D.State → D.Op → ℕ)
    {s s₁ : D.State} {tr₁ : D.Transcript} (h₁ : D.ValidTranscript s tr₁ s₁)
    (tr₂ : D.Transcript) :
    D.totalCost charge s (tr₁ ++ tr₂) =
      D.totalCost charge s tr₁ + D.totalCost charge s₁ tr₂ := by
  induction h₁ with
  | nil _ => simp
  | cons st _ _ _ ih => simp [ih, Nat.add_assoc]

/-- Uniform per-operation bounds scale by the transcript length on any valid transcript. -/
theorem totalCost_le_length_mul {D : RelSpec.{u, v, w}} (charge : D.State → D.Op → ℕ) (T : ℕ)
    (h : ∀ s o, D.valid s o → charge s o ≤ T) {s s' : D.State} {tr : D.Transcript}
    (hv : D.ValidTranscript s tr s') :
    D.totalCost charge s tr ≤ tr.length * T := by
  induction hv with
  | nil _ => simp
  | cons st hv_o _ _ ih =>
    have hstep := h _ st.op hv_o
    simp only [totalCost_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A constant charge `K` per operation totals `tr.length * K`. -/
theorem totalCost_const (K : ℕ) (s : D.State) (tr : D.Transcript) :
    D.totalCost (fun _ _ => K) s tr = tr.length * K := by
  induction tr generalizing s with
  | nil => simp
  | cons st tr ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- A unit charge per operation totals the transcript length. -/
theorem totalCost_one (s : D.State) (tr : D.Transcript) :
    D.totalCost (fun _ _ => 1) s tr = tr.length := by
  simpa using D.totalCost_const 1 s tr

end RelSpec

/-! ## Adaptive clients (`ClientRun`, `DemonicValid`) and demonic `Hoare` / `CostHoare` -/

namespace RelSpec

variable (D : RelSpec.{u, v, w}) {α β : Type y}

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
theorem ClientRun.validTranscript {D : RelSpec.{u, v, w}} {s s' : D.State} {p : D.Client α}
    {v : α} {tr : D.Transcript} (h : D.ClientRun s p v s' tr) :
    D.ValidTranscript s tr s' := by
  induction h with
  | pure s _ => exact .nil s
  | liftBind _ _ _ hv hstep _ ih => exact .cons _ hv hstep ih

theorem clientRun_pure_iff {D : RelSpec.{u, v, w}} (s : D.State) (a v : α) (s' : D.State)
    (tr : D.Transcript) :
    D.ClientRun s (.pure a) v s' tr ↔ v = a ∧ s' = s ∧ tr = [] := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact .pure s' v

theorem clientRun_liftBind_iff {D : RelSpec.{u, v, w}} (s : D.State) (o : D.Op)
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
theorem ClientRun.bind {D : RelSpec.{u, v, w}} {s s₁ s₂ : D.State} {p : D.Client α}
    {k : α → D.Client β} {a : α} {b : β} {tr₁ tr₂ : D.Transcript}
    (h₁ : D.ClientRun s p a s₁ tr₁) (h₂ : D.ClientRun s₁ (k a) b s₂ tr₂) :
    D.ClientRun s (p.bind k) b s₂ (tr₁ ++ tr₂) := by
  induction h₁ with
  | pure _ _ => exact h₂
  | liftBind o cont res hv hstep _ ih =>
    exact .liftBind o (fun r => (cont r).bind k) res hv hstep (ih h₂)

/-- A client run of `p.bind k` splits into a run of `p` and a run of `k` from the intermediate
result and state. -/
theorem clientRun_bind_iff {D : RelSpec.{u, v, w}} {s s₂ : D.State} {p : D.Client α}
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

theorem demonicValid_pure_iff {D : RelSpec.{u, v, w}} (s : D.State) (a : α) :
    D.DemonicValid s (.pure a) ↔ True :=
  ⟨fun _ => trivial, fun _ => .pure s a⟩

theorem demonicValid_liftBind_iff {D : RelSpec.{u, v, w}} (s : D.State) (o : D.Op)
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
theorem DemonicValid.exists_clientRun {D : RelSpec.{u, v, w}} [D.Total] {s : D.State}
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
theorem DemonicValid.bind {D : RelSpec.{u, v, w}} {s : D.State} {p : D.Client α}
    {k : α → D.Client β} (hp : D.DemonicValid s p)
    (hk : ∀ a s' tr, D.ClientRun s p a s' tr → D.DemonicValid s' (k a)) :
    D.DemonicValid s (p.bind k) := by
  induction hp with
  | pure s a => exact hk a s [] (.pure s a)
  | liftBind o cont hv_o _ ih =>
    refine .liftBind o (fun r => (cont r).bind k) hv_o fun s₁ r hstep => ?_
    exact ih s₁ r hstep fun a s₂ tr hrun => hk a s₂ (⟨o, r, s₁⟩ :: tr)
      (.liftBind o cont r hv_o hstep hrun)

/-- Demonic Hoare triple for a relational specification: from any initial state satisfying `pre`,
the client `p` is demonically admissible and *every* valid `ClientRun` satisfies `post`. -/
def Hoare (pre : D.State → Prop) (p : D.Client α) (post : α → D.State → Prop) : Prop :=
  ∀ s, pre s → D.DemonicValid s p ∧ ∀ v s' tr, D.ClientRun s p v s' tr → post v s'

namespace Hoare

variable {D : RelSpec.{u, v, w}}

/-- Returning a pure value leaves the state unchanged. -/
theorem pure (pre : D.State → Prop) (a : α) (post : α → D.State → Prop)
    (h : ∀ s, pre s → post a s) : D.Hoare pre (.pure a) post := by
  intro s hs
  refine ⟨.pure s a, ?_⟩
  intro v s' tr hrun
  cases hrun
  exact h s hs

/-- Calling an operation requires `D.valid s o` and establishes `post a s'` for every permitted
outcome `D.step s o s' a`. -/
theorem call (pre : D.State → Prop) (o : D.Op) (post : D.Result o → D.State → Prop)
    (h : ∀ s, pre s → D.valid s o ∧ ∀ s' a, D.step s o s' a → post a s') :
    D.Hoare pre (.liftBind o fun a => .pure a) post := by
  intro s hs
  obtain ⟨hv, hpost⟩ := h s hs
  refine ⟨.liftBind o (fun a => .pure a) hv fun s' a _ => .pure s' a, ?_⟩
  intro v s' tr hrun
  cases hrun with
  | liftBind _ _ a _ hstep hrest =>
    cases hrest
    exact hpost s' v hstep

/-- Sequential composition of demonic Hoare triples. -/
theorem bind {pre : D.State → Prop} {mid : α → D.State → Prop}
    {post : β → D.State → Prop} {p : D.Client α} {k : α → D.Client β}
    (hp : D.Hoare pre p mid) (hk : ∀ a, D.Hoare (mid a) (k a) post) :
    D.Hoare pre (p.bind k) post := by
  intro s hs
  obtain ⟨hvp, hpost_p⟩ := hp s hs
  refine ⟨hvp.bind fun a s₁ tr₁ hrun₁ => (hk a s₁ (hpost_p a s₁ tr₁ hrun₁)).1, ?_⟩
  intro b s₂ tr hrun
  obtain ⟨a, s₁, tr₁, tr₂, hrun₁, hrun₂, _⟩ := clientRun_bind_iff.mp hrun
  exact (hk a s₁ (hpost_p a s₁ tr₁ hrun₁)).2 b s₂ tr₂ hrun₂

/-- Consequence rule for demonic Hoare triples. -/
theorem consequence {pre pre' : D.State → Prop} {post post' : α → D.State → Prop}
    {p : D.Client α} (h : D.Hoare pre p post) (hp : ∀ s, pre' s → pre s)
    (hq : ∀ a s, post a s → post' a s) : D.Hoare pre' p post' := by
  intro s hs
  obtain ⟨hv, hpost⟩ := h s (hp s hs)
  exact ⟨hv, fun v s' tr hrun => hq v s' (hpost v s' tr hrun)⟩

end Hoare

/-- Demonic `CostHoare` triple: strengthens `D.Hoare` with a worst-case abstract charge bound
`D.totalCost charge s tr ≤ budget s` across *every* valid `ClientRun`. -/
def CostHoare (charge : D.State → D.Op → ℕ) (pre : D.State → Prop)
    (p : D.Client α) (post : α → D.State → Prop) (budget : D.State → ℕ) : Prop :=
  D.Hoare pre p post ∧
    ∀ s, pre s → ∀ v s' tr, D.ClientRun s p v s' tr → D.totalCost charge s tr ≤ budget s

namespace CostHoare

variable {D : RelSpec.{u, v, w}} {charge : D.State → D.Op → ℕ} {pre : D.State → Prop}
  {post : α → D.State → Prop} {budget : D.State → ℕ} {p : D.Client α}

/-- Project a `CostHoare` triple to its underlying `Hoare` triple. -/
theorem hoare (h : D.CostHoare charge pre p post budget) : D.Hoare pre p post := h.1

/-- Returning a pure value incurs zero operation cost. -/
theorem pure (a : α) (h : ∀ s, pre s → post a s) :
    D.CostHoare charge pre (.pure a) post (fun _ => 0) := by
  refine ⟨Hoare.pure pre a post h, ?_⟩
  intro s _ v s' tr hrun
  cases hrun
  exact Nat.le_refl 0

/-- Calling a single operation charges `charge s o` at the pre-state `s`. -/
theorem call (o : D.Op) {post : D.Result o → D.State → Prop}
    (h : ∀ s, pre s → D.valid s o ∧ ∀ s' a, D.step s o s' a → post a s') :
    D.CostHoare charge pre (.liftBind o fun a => .pure a) post (fun s => charge s o) := by
  refine ⟨Hoare.call pre o post h, ?_⟩
  intro s _ v s' tr hrun
  cases hrun with
  | liftBind _ _ a _ _ hrest =>
    cases hrest
    simp

/-- Compose `CostHoare` budgets at every intermediate state satisfying `mid`. -/
theorem bind {mid : α → D.State → Prop} {post : β → D.State → Prop}
    {k : α → D.Client β} {first : D.State → ℕ} {next : α → D.State → ℕ}
    (hp : D.CostHoare charge pre p mid first)
    (hk : ∀ a, D.CostHoare charge (mid a) (k a) post (next a))
    (hb : ∀ s, pre s → ∀ a s', mid a s' → first s + next a s' ≤ budget s) :
    D.CostHoare charge pre (p.bind k) post budget := by
  refine ⟨Hoare.bind hp.hoare (fun a => (hk a).hoare), ?_⟩
  intro s hs b s₂ tr hrun
  obtain ⟨a, s₁, tr₁, tr₂, hrun₁, hrun₂, rfl⟩ := clientRun_bind_iff.mp hrun
  have hmid : mid a s₁ := (hp.hoare s hs).2 a s₁ tr₁ hrun₁
  have hf := hp.2 s hs a s₁ tr₁ hrun₁
  have hn := (hk a).2 s₁ hmid b s₂ tr₂ hrun₂
  rw [D.totalCost_append charge hrun₁.validTranscript tr₂]
  exact (Nat.add_le_add hf hn).trans (hb s hs a s₁ hmid)

/-- Consequence rule for demonic `CostHoare` triples. -/
theorem consequence {pre' : D.State → Prop} {post' : α → D.State → Prop}
    {budget' : D.State → ℕ} (h : D.CostHoare charge pre p post budget)
    (hp : ∀ s, pre' s → pre s) (hq : ∀ a s, post a s → post' a s)
    (hb : ∀ s, pre' s → budget s ≤ budget' s) :
    D.CostHoare charge pre' p post' budget' :=
  ⟨h.hoare.consequence hp hq,
    fun s hs v s' tr hrun => (h.2 s (hp s hs) v s' tr hrun).trans (hb s hs)⟩

end CostHoare

end RelSpec

/-! ## Equivalence of relational and deterministic client semantics on `D.toRelSpec` -/

namespace Spec

variable (D : Spec.{u, v, w}) {α : Type y}

/-- On `D.toRelSpec`, non-adaptive operation-sequence admissibility `ValidOpSeq` coincides with
`D.ValidHistory`. -/
theorem toRelSpec_validOpSeq_iff (s : D.State) (ops : List D.Op) :
    D.toRelSpec.ValidOpSeq s ops ↔ D.ValidHistory s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    change (D.valid s o ∧ ∀ s' a, (s', a) = D.step s o → D.toRelSpec.ValidOpSeq s' ops) ↔
      D.valid s o ∧ D.ValidHistory (D.step s o).1 ops
    refine and_congr_right fun _ => ?_
    constructor
    · intro h
      exact (ih (D.step s o).1).mp (h (D.step s o).1 (D.step s o).2 Prod.mk.eta)
    · intro h s' a heq
      have hs' : s' = (D.step s o).1 := congrArg Prod.fst heq
      subst hs'
      exact (ih (D.step s o).1).mpr h

/-- The unique canonical transcript determined by a deterministic specification `D` on an
operation list `os` from state `s`. -/
def canonicalTranscript (s : D.State) : List D.Op → D.toRelSpec.Transcript
  | [] => []
  | o :: os =>
    let next := D.step s o
    ⟨o, next.2, next.1⟩ :: canonicalTranscript next.1 os

@[simp]
theorem canonicalTranscript_nil (s : D.State) : D.canonicalTranscript s [] = [] := rfl

@[simp]
theorem canonicalTranscript_cons (s : D.State) (o : D.Op) (os : List D.Op) :
    D.canonicalTranscript s (o :: os) =
      ⟨o, (D.step s o).2, (D.step s o).1⟩ :: D.canonicalTranscript (D.step s o).1 os := rfl

/-- The underlying operation list of `D.canonicalTranscript s os` is `os`. -/
@[simp]
theorem canonicalTranscript_ops (s : D.State) (os : List D.Op) :
    (D.canonicalTranscript s os).ops = os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp [ih]

/-- `totalCost` along `D.canonicalTranscript s os` equals `D.totalCost charge s os`. -/
@[simp]
theorem toRelSpec_totalCost_canonicalTranscript (charge : D.State → D.Op → ℕ) (s : D.State)
    (os : List D.Op) :
    D.toRelSpec.totalCost charge s (D.canonicalTranscript s os) = D.totalCost charge s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    change charge s o +
        D.toRelSpec.totalCost charge (D.step s o).1 (D.canonicalTranscript (D.step s o).1 os) =
      charge s o + D.totalCost charge (D.step s o).1 os
    rw [ih]

/-- On `D.toRelSpec`, demonic client admissibility `DemonicValid s p` is equivalent to
`D.ValidHistory s (D.runClient s p).2.2`. -/
theorem toRelSpec_demonicValid_iff (s : D.State) (p : D.Client α) :
    D.toRelSpec.DemonicValid s p ↔ D.ValidHistory s (D.runClient s p).2.2 := by
  induction p generalizing s with
  | pure a =>
    exact ⟨fun _ => trivial, fun _ => RelSpec.DemonicValid.pure (D := D.toRelSpec) s a⟩
  | liftBind o k ih =>
    rw [RelSpec.demonicValid_liftBind_iff (D := D.toRelSpec), runClient_liftBind, validHistory_cons]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h
      exact (ih (D.step s o).2 (D.step s o).1).mp
        (h (D.step s o).1 (D.step s o).2 Prod.mk.eta)
    · intro h s' a heq
      have hs' : s' = (D.step s o).1 := congrArg Prod.fst heq
      have ha : a = (D.step s o).2 := congrArg Prod.snd heq
      subst hs'; subst ha
      exact (ih (D.step s o).2 (D.step s o).1).mpr h

/-- Every client with an admissible deterministic history executes canonically in `D.toRelSpec`. -/
theorem toRelSpec_clientRun_canonical (s : D.State) (p : D.Client α)
    (hv : D.ValidHistory s (D.runClient s p).2.2) :
    D.toRelSpec.ClientRun s p (D.runClient s p).1 (D.runClient s p).2.1
      (D.canonicalTranscript s (D.runClient s p).2.2) := by
  induction p generalizing s with
  | pure a =>
    exact RelSpec.ClientRun.pure (D := D.toRelSpec) s a
  | liftBind o k ih =>
    exact RelSpec.ClientRun.liftBind (D := D.toRelSpec) o k (D.step s o).2 hv.1 Prod.mk.eta
      (ih (D.step s o).2 (D.step s o).1 hv.2)

private theorem toRelSpec_clientRun_imp {s : D.toRelSpec.State} {p : D.toRelSpec.Client α}
    {v : α} {s' : D.toRelSpec.State} {tr : D.toRelSpec.Transcript}
    (h : D.toRelSpec.ClientRun s p v s' tr) :
    D.ValidHistory s (D.runClient s p).2.2 ∧
    v = (D.runClient s p).1 ∧
    s' = (D.runClient s p).2.1 ∧
    tr = D.canonicalTranscript s (D.runClient s p).2.2 := by
  induction h with
  | pure s a =>
    exact ⟨trivial, rfl, rfl, rfl⟩
  | @liftBind s s₁ s₂ o k res v tr hv hstep _ ih =>
    have hs₁ : s₁ = (D.step s o).1 := congrArg Prod.fst hstep
    have hres : res = (D.step s o).2 := congrArg Prod.snd hstep
    subst hs₁; subst hres
    obtain ⟨hv_rest, rfl, rfl, rfl⟩ := ih
    exact ⟨⟨hv, hv_rest⟩, rfl, rfl, rfl⟩

/-- On `D.toRelSpec`, `ClientRun` collapses uniquely to `D.runClient` and `D.ValidHistory`. -/
theorem toRelSpec_clientRun_iff (s : D.State) (p : D.Client α) (v : α) (s' : D.State)
    (tr : D.toRelSpec.Transcript) :
    D.toRelSpec.ClientRun s p v s' tr ↔
      D.ValidHistory s (D.runClient s p).2.2 ∧
      v = (D.runClient s p).1 ∧
      s' = (D.runClient s p).2.1 ∧
      tr = D.canonicalTranscript s (D.runClient s p).2.2 :=
  ⟨D.toRelSpec_clientRun_imp, fun ⟨hv, h₁, h₂, h₃⟩ =>
    h₁ ▸ h₂ ▸ h₃ ▸ D.toRelSpec_clientRun_canonical s p hv⟩

/-- On `D.toRelSpec`, `RelSpec.Hoare` is equivalent to `Spec.Hoare`. -/
theorem toRelSpec_hoare_iff (pre : D.State → Prop) (p : D.Client α) (post : α → D.State → Prop) :
    D.toRelSpec.Hoare pre p post ↔ D.Hoare pre p post := by
  refine forall_congr' fun s => imp_congr_right fun _ => ?_
  rw [toRelSpec_demonicValid_iff]
  constructor
  · rintro ⟨hv, hpost⟩
    exact ⟨hv, hpost _ _ _ (D.toRelSpec_clientRun_canonical s p hv)⟩
  · rintro ⟨hv, hpost⟩
    refine ⟨hv, fun v s' tr hrun => ?_⟩
    obtain ⟨_, rfl, rfl, _⟩ := (D.toRelSpec_clientRun_iff s p v s' tr).mp hrun
    exact hpost

/-- On `D.toRelSpec`, `RelSpec.CostHoare` is equivalent to `Spec.CostHoare`. -/
theorem toRelSpec_costHoare_iff (charge : D.State → D.Op → ℕ) (pre : D.State → Prop)
    (p : D.Client α) (post : α → D.State → Prop) (budget : D.State → ℕ) :
    D.toRelSpec.CostHoare charge pre p post budget ↔ D.CostHoare charge pre p post budget := by
  unfold RelSpec.CostHoare Spec.CostHoare
  rw [toRelSpec_hoare_iff]
  refine and_congr_right fun hhoare => forall_congr' fun s => imp_congr_right fun hs => ?_
  have hv := (hhoare s hs).1
  constructor
  · intro h
    have hb := h _ _ _ (D.toRelSpec_clientRun_canonical s p hv)
    rwa [D.toRelSpec_totalCost_canonicalTranscript] at hb
  · intro h v s' tr hrun
    obtain ⟨_, _, _, rfl⟩ := (D.toRelSpec_clientRun_iff s p v s' tr).mp hrun
    rwa [D.toRelSpec_totalCost_canonicalTranscript]

end Spec

/-! ## Angelic backend realizations (`RelRealization`, `RelBound`, `RelAmortized`) -/

/-- Angelic semantic realization of a relational specification `D : RelSpec`:
* `total`: every represented state and admissible operation admits a native execution;
* `correct`: every native execution from a represented state on an admissible operation realizes
  *some* permitted abstract post-state `s'` with `D.step s o s' a ∧ rep s' c'`. -/
structure RelRealization (D : RelSpec.{u, v, w}) {C τ : Type x}
    (exec : Execution D C τ) where
  /-- Representation invariant linking abstract states to concrete backend states. -/
  rep : D.State → C → Prop
  /-- Existence of a native execution for every represented state and admissible operation. -/
  total : ∀ {s c} o, rep s c → D.valid s o → ∃ a c' trace, exec c o a c' trace
  /-- Angelic step correctness: every native execution realizes some permitted abstract step. -/
  correct : ∀ {s c o a c' trace}, rep s c → D.valid s o → exec c o a c' trace →
    ∃ s', D.step s o s' a ∧ rep s' c'

namespace RelRealization

variable {D : RelSpec.{u, v, w}} {C τ : Type x} {α : Type y}
  {exec : Execution D C τ} (R : RelRealization D exec)

/-- From related states, every native execution of a demonically admissible client realizes a
valid `ClientRun` ending in a related state. -/
theorem correct_client {p : D.Client α} {s : D.State} {c c' : C} {a : α}
    {traces : List τ} (hr : R.rep s c) (hv : D.DemonicValid s p)
    (he : Executes exec p c a c' traces) :
    ∃ s' tr, D.ClientRun s p a s' tr ∧ R.rep s' c' ∧ traces.length = tr.length := by
  induction he generalizing s with
  | pure a c =>
    exact ⟨s, [], .pure s a, hr, rfl⟩
  | @call o k c res c₁ trace b c₂ traces ho hes ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    obtain ⟨s₁, hstep, hr₁⟩ := R.correct hr hv_o ho
    obtain ⟨s₂, tr, hrun, hr₂, hlen⟩ := ih hr₁ (hv_k s₁ res hstep)
    exact ⟨s₂, ⟨o, res, s₁⟩ :: tr, .liftBind o k res hv_o hstep hrun, hr₂,
      congrArg (· + 1) hlen⟩

/-- From related states, every demonically admissible client admits a native execution realizing a
valid `ClientRun` ending in a related state. -/
theorem exists_executes (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.DemonicValid s p) :
    ∃ a c' traces s' tr, Executes exec p c a c' traces ∧
      D.ClientRun s p a s' tr ∧ R.rep s' c' ∧ traces.length = tr.length := by
  induction hv generalizing c with
  | pure s a =>
    exact ⟨a, c, [], s, [], .pure a c, .pure s a, hr, rfl⟩
  | liftBind o k hv_o _ ih =>
    obtain ⟨res, c₁, trace, ho⟩ := R.total o hr hv_o
    obtain ⟨s₁, hstep, hr₁⟩ := R.correct hr hv_o ho
    obtain ⟨b, c₂, traces, s₂, tr, hes, hrun, hr₂, hlen⟩ := ih s₁ res hstep hr₁
    exact ⟨b, c₂, trace :: traces, s₂, ⟨o, res, s₁⟩ :: tr,
      .call ho hes, .liftBind o k res hv_o hstep hrun, hr₂, congrArg (· + 1) hlen⟩

end RelRealization

/-- Lift a deterministic `Realization D exec` to a relational `RelRealization D.toRelSpec exec`. -/
def Realization.toRelRealization {D : Spec.{u, v, w}} {C τ : Type x}
    {exec : Execution D C τ} (R : Realization D exec) :
    RelRealization D.toRelSpec exec where
  rep := R.rep
  total o hr hv := R.total o hr hv
  correct {s c o a c' trace} hr hv he := by
    obtain ⟨ha, hr'⟩ := R.correct hr hv he
    exact ⟨(D.step s o).1, Prod.ext rfl ha, hr'⟩

/-- Every native execution of a verified demonic `Hoare` client satisfies its abstract
postcondition in a related final state. -/
theorem RelSpec.Hoare.realize {D : RelSpec.{u, v, w}} {C Trace : Type x} {α : Type y}
    {exec : Execution D C Trace} (R : RelRealization D exec)
    {pre : D.State → Prop} {post : α → D.State → Prop} {p : D.Client α}
    (h : D.Hoare pre p post) {s : D.State} {c c' : C} {a : α} {traces : List Trace}
    (hp : pre s) (hr : R.rep s c) (he : Executes exec p c a c' traces) :
    ∃ s' tr, D.ClientRun s p a s' tr ∧ R.rep s' c' ∧ post a s' := by
  obtain ⟨hv, hpost⟩ := h s hp
  obtain ⟨s', tr, hrun, hr', _⟩ := R.correct_client hr hv he
  exact ⟨s', tr, hrun, hr', hpost a s' tr hrun⟩

/-- Per-operation worst-case resource certificate over a relational realization `R`. -/
def RelBound {D : RelSpec.{u, v, w}} {C τ : Type x} {exec : Execution D C τ}
    (R : RelRealization D exec) (weight : τ → ℕ) (charge : D.State → D.Op → ℕ) : Prop :=
  ∀ {s c o a c' trace}, R.rep s c → D.valid s o → exec c o a c' trace →
    weight trace ≤ charge s o

/-- Lift a deterministic `Bound R weight charge` to `RelBound R.toRelRealization weight charge`. -/
theorem Bound.toRelBound {D : Spec.{u, v, w}} {C τ : Type x} {exec : Execution D C τ}
    {R : Realization D exec} {weight : τ → ℕ} {charge : D.State → D.Op → ℕ}
    (B : Bound R weight charge) :
    RelBound R.toRelRealization weight charge :=
  fun hr hv he => B hr hv he

/-- Potential-method amortized resource certificate over a relational realization `R`:
for every native operation execution from `R.rep s c` on an admissible `o`, there exists a
permitted abstract post-state `s'` satisfying `D.step s o s' a`, `R.rep s' c'`, and the
single-step potential inequality `weight trace + potential s' c' ≤ charge s o + potential s c`. -/
structure RelAmortized {D : RelSpec.{u, v, w}} {C Trace : Type x}
    {exec : Execution D C Trace} (R : RelRealization D exec) (weight : Trace → ℕ)
    (potential : D.State → C → ℕ) (charge : D.State → D.Op → ℕ) : Prop where
  /-- Angelic single-step potential inequality witnessing a permitted post-state `s'`. -/
  step : ∀ {s c o a c' trace}, R.rep s c → D.valid s o → exec c o a c' trace →
    ∃ s', D.step s o s' a ∧ R.rep s' c' ∧
      weight trace + potential s' c' ≤ charge s o + potential s c

namespace RelAmortized

variable {D : RelSpec.{u, v, w}} {C Trace : Type x} {α : Type y}
  {exec : Execution D C Trace} {R : RelRealization D exec}
  {weight : Trace → ℕ} {potential : D.State → C → ℕ} {charge : D.State → D.Op → ℕ}
  (A : RelAmortized R weight potential charge)

include A in
/-- **Amortized telescoping along adaptive clients (`executes_le`).**
For any demonically admissible client `p` and native execution `Executes exec p c a c' traces`,
there exist a final abstract state `s'` and transcript `tr` such that `D.ClientRun s p a s' tr`,
`R.rep s' c'`, and
`total weight traces + potential s' c' ≤ D.totalCost charge s tr + potential s c`. -/
theorem executes_le {p : D.Client α} {s : D.State} {c c' : C} {a : α}
    {traces : List Trace} (hr : R.rep s c) (hv : D.DemonicValid s p)
    (he : Executes exec p c a c' traces) :
    ∃ s' tr, D.ClientRun s p a s' tr ∧ R.rep s' c' ∧
      traces.length = tr.length ∧
      total weight traces + potential s' c' ≤
        D.totalCost charge s tr + potential s c := by
  induction he generalizing s with
  | pure a c =>
    exact ⟨s, [], .pure s a, hr, rfl, Nat.le_refl _⟩
  | @call o k c res c₁ trace b c₂ traces ho hes ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    obtain ⟨s₁, hstep, hr₁, hpot₁⟩ := A.step hr hv_o ho
    obtain ⟨s₂, tr, hrun, hr₂, hlen, hpot₂⟩ := ih hr₁ (hv_k s₁ res hstep)
    refine ⟨s₂, ⟨o, res, s₁⟩ :: tr, .liftBind o k res hv_o hstep hrun, hr₂,
      congrArg (· + 1) hlen, ?_⟩
    simp only [total_cons, RelSpec.totalCost_cons]
    omega

include A in
/-- **Existence, correctness, and amortized bound (`run_client_amortized`).**
From related initial states, every demonically admissible client `p` admits a native execution
satisfying `D.ClientRun`, `R.rep`, and the telescoping potential bound. -/
theorem run_client_amortized (p : D.Client α) {s : D.State} {c : C}
    (hr : R.rep s c) (hv : D.DemonicValid s p) :
    ∃ a c' traces s' tr, Executes exec p c a c' traces ∧
      D.ClientRun s p a s' tr ∧ R.rep s' c' ∧
      traces.length = tr.length ∧
      total weight traces + potential s' c' ≤
        D.totalCost charge s tr + potential s c := by
  obtain ⟨a, c', traces, _, _, he, _, _, _⟩ := R.exists_executes p hr hv
  obtain ⟨s', tr, hrun, hr', hlen, hpot⟩ := A.executes_le hr hv he
  exact ⟨a, c', traces, s', tr, he, hrun, hr', hlen, hpot⟩

/-- A worst-case `RelBound` is a zero-potential `RelAmortized` certificate. -/
theorem of_relBound (B : RelBound R weight charge) :
    RelAmortized R weight (fun _ _ => 0) charge where
  step hr hv he := by
    obtain ⟨s', hstep, hr'⟩ := R.correct hr hv he
    exact ⟨s', hstep, hr', by simpa using B hr hv he⟩

end RelAmortized

/-- Lift a deterministic `Amortized R weight potential charge` certificate to
`RelAmortized R.toRelRealization weight potential charge`. -/
theorem Amortized.toRelAmortized {D : Spec.{u, v, w}} {C Trace : Type x}
    {exec : Execution D C Trace} {R : Realization D exec}
    {weight : Trace → ℕ} {potential : D.State → C → ℕ} {charge : D.State → D.Op → ℕ}
    (A : Amortized R weight potential charge) :
    RelAmortized R.toRelRealization weight potential charge where
  step {s c o a c' trace} hr hv he := by
    obtain ⟨ha, hr'⟩ := R.correct hr hv he
    exact ⟨(D.step s o).1, Prod.ext rfl ha, hr', A.step hr hv he⟩

namespace RelBound

variable {D : RelSpec.{u, v, w}} {C τ : Type x} {α : Type y}
  {exec : Execution D C τ} {R : RelRealization D exec}
  {weight : τ → ℕ} {charge : D.State → D.Op → ℕ}
  (B : RelBound R weight charge)

include B in
/-- Under a worst-case `RelBound`, every native execution of a demonically admissible client has
total weight at most `D.totalCost charge s tr` for some valid `ClientRun` transcript `tr`. -/
theorem client {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List τ}
    (hr : R.rep s c) (hv : D.DemonicValid s p) (he : Executes exec p c a c' traces) :
    ∃ s' tr, D.ClientRun s p a s' tr ∧ R.rep s' c' ∧
      traces.length = tr.length ∧
      total weight traces ≤ D.totalCost charge s tr := by
  obtain ⟨s', tr, hrun, hr', hlen, hpot⟩ := (RelAmortized.of_relBound B).executes_le hr hv he
  exact ⟨s', tr, hrun, hr', hlen, by simpa using hpot⟩

include B in
/-- Under a worst-case `RelBound`, every demonically admissible client admits a native execution
meeting the total charge bound. -/
theorem exists_executes (p : D.Client α) {s : D.State} {c : C}
    (hr : R.rep s c) (hv : D.DemonicValid s p) :
    ∃ a c' traces s' tr, Executes exec p c a c' traces ∧
      D.ClientRun s p a s' tr ∧ R.rep s' c' ∧
      traces.length = tr.length ∧
      total weight traces ≤ D.totalCost charge s tr := by
  obtain ⟨a, c', traces, s', tr, he, hrun, hr', hlen, hpot⟩ :=
    (RelAmortized.of_relBound B).run_client_amortized p hr hv
  exact ⟨a, c', traces, s', tr, he, hrun, hr', hlen, by simpa using hpot⟩

end RelBound

/-- Transport a demonic `CostHoare` triple through a `RelAmortized` certificate to bound native
execution weight plus final potential by `budget s + potential s c`. -/
theorem RelSpec.CostHoare.realize_amortized {D : RelSpec.{u, v, w}} {C τ : Type x} {α : Type y}
    {exec : Execution D C τ} {R : RelRealization D exec}
    {weight : τ → ℕ} {potential : D.State → C → ℕ} {charge : D.State → D.Op → ℕ}
    {pre : D.State → Prop} {post : α → D.State → Prop} {budget : D.State → ℕ}
    {p : D.Client α} (A : RelAmortized R weight potential charge)
    (h : D.CostHoare charge pre p post budget) {s : D.State} {c c' : C}
    {a : α} {traces : List τ} (hs : pre s) (hr : R.rep s c)
    (he : Executes exec p c a c' traces) :
    ∃ s' tr, D.ClientRun s p a s' tr ∧ R.rep s' c' ∧ post a s' ∧
      total weight traces + potential s' c' ≤ budget s + potential s c := by
  obtain ⟨hv, hpost⟩ := h.1 s hs
  obtain ⟨s', tr, hrun, hr', _, hpot⟩ := A.executes_le hr hv he
  have hbud := h.2 s hs a s' tr hrun
  exact ⟨s', tr, hrun, hr', hpost a s' tr hrun, by omega⟩

/-- Transport a demonic `CostHoare` triple through a worst-case `RelBound` certificate. -/
theorem RelSpec.CostHoare.realize {D : RelSpec.{u, v, w}} {C τ : Type x} {α : Type y}
    {exec : Execution D C τ} {R : RelRealization D exec}
    {weight : τ → ℕ} {charge : D.State → D.Op → ℕ}
    {pre : D.State → Prop} {post : α → D.State → Prop} {budget : D.State → ℕ}
    {p : D.Client α} (B : RelBound R weight charge)
    (h : D.CostHoare charge pre p post budget) {s : D.State} {c c' : C}
    {a : α} {traces : List τ} (hs : pre s) (hr : R.rep s c)
    (he : Executes exec p c a c' traces) :
    (∃ s', R.rep s' c' ∧ post a s') ∧ total weight traces ≤ budget s := by
  obtain ⟨s', _, _, hr', hpost, hpot⟩ :=
    h.realize_amortized (RelAmortized.of_relBound B) hs hr he
  exact ⟨⟨s', hr', hpost⟩, by simpa using hpot⟩

/-- Existence of a native execution satisfying a demonic `CostHoare` contract under `RelBound`. -/
theorem RelSpec.CostHoare.exists_executes {D : RelSpec.{u, v, w}} {C τ : Type x} {α : Type y}
    {exec : Execution D C τ} {R : RelRealization D exec}
    {weight : τ → ℕ} {charge : D.State → D.Op → ℕ}
    {pre : D.State → Prop} {post : α → D.State → Prop} {budget : D.State → ℕ}
    {p : D.Client α} (B : RelBound R weight charge)
    (h : D.CostHoare charge pre p post budget) {s : D.State} {c : C}
    (hs : pre s) (hr : R.rep s c) :
    ∃ a c' traces, Executes exec p c a c' traces ∧
      (∃ s', R.rep s' c' ∧ post a s') ∧ total weight traces ≤ budget s := by
  obtain ⟨a, c', traces, _, _, he, _, _, _⟩ := R.exists_executes p hr (h.1 s hs).1
  exact ⟨a, c', traces, he, h.realize B hs hr he⟩

end Cslib.Stateful
