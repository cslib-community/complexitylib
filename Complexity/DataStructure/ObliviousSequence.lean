/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Oblivious-Sequence Data Structure Specifications

An *oblivious-sequence specification* (`Cslib.DataStructure.ObliviousSequenceSpec`) describes the
input-output contract of a randomized or deterministic data structure against an *oblivious*
(non-adaptive) caller that fixes a finite operation sequence `ops : List Op` in advance. Unlike a
state-transition specification (`Cslib.DataStructure.StateTransitionSpec`), an oblivious-sequence
specification has no abstract `State` field: it constrains the joint probability distribution
`μ : PMF (List (Sigma Result))` of the full input-output transcript directly via a predicate
`Contract ops μ`.

Every relational state-transition specification `D : Cslib.DataStructure.StateTransitionSpec` at an
initial state `s₀ : D.State` embeds canonically into `ObliviousSequenceSpec` via
`Cslib.DataStructure.StateTransitionSpec.toObliviousSequenceSpec`, requiring every transcript in the
support of `μ` to arise from a valid relational execution of `D` from `s₀`. On deterministic
specifications (`[D.HasStepFn f]`), this contract reduces to concentration on the unique canonical
output trace `(D.run s₀ ops).2`.

## Main definitions

* `Cslib.DataStructure.ObliviousSequenceSpec`: state-free distributional specification over finite
  oblivious operation sequences.
* `Cslib.DataStructure.TranscriptMatches`: alignment predicate `out.map Sigma.fst = ops` between an
  operation sequence and an input-output transcript.
* `Cslib.DataStructure.ObliviousSequenceSpec.weaken`: monotonicity combinator strengthening
  `ValidOpSeq` and weakening `Contract`.
* `Cslib.DataStructure.StateTransitionSpec.toObliviousSequenceSpec`,
  `Cslib.DataStructure.ObliviousSequenceSpec.ofFn`: canonical embeddings of relational and
  deterministic state-transition specifications into `ObliviousSequenceSpec`.

## Main results

* `Cslib.DataStructure.ObliviousSequenceSpec.contract_weaken`: monotonicity of
  `ObliviousSequenceSpec.weaken`.
* `Cslib.DataStructure.StateTransitionSpec.toObliviousSequenceSpec_contract_matches`: every
  transcript in the support of a distribution satisfying
  `(D.toObliviousSequenceSpec s₀).Contract ops` matches `ops`.
* `Cslib.DataStructure.StateTransitionSpec.toObliviousSequenceSpec_contract_iff_of_hasStepFn`: on a
  deterministic specification, `(D.toObliviousSequenceSpec s₀).Contract ops μ` holds under
  `D.ValidHistory s₀ ops` if and only if every `out ∈ μ.support` equals `(D.run s₀ ops).2`.
* `Cslib.DataStructure.StateTransitionSpec.toObliviousSequenceSpec_contract_pure_run`: the point
  mass `PMF.pure (D.run s₀ ops).2` satisfies `(D.toObliviousSequenceSpec s₀).Contract ops`.
-/

public section

universe u v w

namespace Cslib.DataStructure

/-! ## Oblivious-sequence specifications -/

/-- A state-free distributional specification for an oblivious (non-adaptive) caller.
For each admissible operation sequence `ops : List Op`, `Contract ops μ` constrains the joint
probability distribution `μ : PMF (List (Sigma Result))` of the returned input-output transcript. -/
structure ObliviousSequenceSpec where
  /-- Operations available to an oblivious caller. -/
  Op : Type u
  /-- Observation type returned by each operation. -/
  Result : Op → Type v
  /-- Admissibility predicate on finite oblivious operation sequences `ops : List Op`. -/
  ValidOpSeq : List Op → Prop := fun _ => True
  /-- Distributional correctness contract on the joint output transcript distribution `μ`
  induced by executing `ops`. -/
  Contract : (ops : List Op) → PMF (List (Sigma Result)) → Prop

/-- An input-output transcript `out : List (Sigma Result)` matches the operation sequence
`ops : List Op` when its first projections equal `ops`. -/
@[expose] def TranscriptMatches {Op : Type u} {Result : Op → Type v}
    (ops : List Op) (out : List (Sigma Result)) : Prop :=
  out.map Sigma.fst = ops

@[simp]
theorem transcriptMatches_nil {Op : Type u} {Result : Op → Type v}
    (out : List (Sigma Result)) :
    TranscriptMatches ([] : List Op) out ↔ out = [] :=
  List.map_eq_nil_iff

theorem transcriptMatches_nil_right {Op : Type u} {Result : Op → Type v} :
    TranscriptMatches ([] : List Op) ([] : List (Sigma Result)) := rfl

@[simp]
theorem transcriptMatches_cons {Op : Type u} {Result : Op → Type v}
    (o : Op) (a : Result o) (ops : List Op) (out : List (Sigma Result)) :
    TranscriptMatches (o :: ops) (⟨o, a⟩ :: out) ↔ TranscriptMatches ops out := by
  simp [TranscriptMatches]

theorem TranscriptMatches.append {Op : Type u} {Result : Op → Type v}
    {ops₁ ops₂ : List Op} {out₁ out₂ : List (Sigma Result)}
    (h₁ : TranscriptMatches ops₁ out₁) (h₂ : TranscriptMatches ops₂ out₂) :
    TranscriptMatches (ops₁ ++ ops₂) (out₁ ++ out₂) := by
  unfold TranscriptMatches at h₁ h₂ ⊢
  simp [h₁, h₂]

theorem TranscriptMatches.length_eq {Op : Type u} {Result : Op → Type v}
    {ops : List Op} {out : List (Sigma Result)} (h : TranscriptMatches ops out) :
    out.length = ops.length := by
  simpa [TranscriptMatches] using congrArg List.length h

namespace ObliviousSequenceSpec

variable (S : ObliviousSequenceSpec.{u, v})

/-- Input-output label pairing an operation with its observation. -/
abbrev Label : Type (max u v) := Sigma S.Result

/-- Weaken an `ObliviousSequenceSpec` by restricting the admissible operation sequences to
`ValidOpSeq'` and relaxing the distributional contract to `Contract'`. -/
@[expose] def weaken (S : ObliviousSequenceSpec.{u, v})
    (ValidOpSeq' : List S.Op → Prop)
    (Contract' : (ops : List S.Op) → PMF (List (Sigma S.Result)) → Prop) :
    ObliviousSequenceSpec.{u, v} where
  Op := S.Op
  Result := S.Result
  ValidOpSeq := ValidOpSeq'
  Contract := Contract'

@[simp]
theorem weaken_op (S : ObliviousSequenceSpec.{u, v}) (V C) :
    (S.weaken V C).Op = S.Op := rfl

@[simp]
theorem weaken_result (S : ObliviousSequenceSpec.{u, v}) (V C) :
    (S.weaken V C).Result = S.Result := rfl

@[simp]
theorem weaken_validOpSeq (S : ObliviousSequenceSpec.{u, v}) (V C) (ops : List S.Op) :
    (S.weaken V C).ValidOpSeq ops ↔ V ops := Iff.rfl

@[simp]
theorem weaken_contract (S : ObliviousSequenceSpec.{u, v}) (V C)
    (ops : List S.Op) (μ : PMF (List (Sigma S.Result))) :
    (S.weaken V C).Contract ops μ ↔ C ops μ := Iff.rfl

/-- Monotonicity of `ObliviousSequenceSpec.weaken`: any distribution satisfying `S.Contract` on
`S.ValidOpSeq` also satisfies `(S.weaken V C).Contract` on `V` when `V` implies `S.ValidOpSeq` and
`S.Contract` implies `C`. -/
theorem contract_weaken {S : ObliviousSequenceSpec.{u, v}}
    {V : List S.Op → Prop}
    {C : (ops : List S.Op) → PMF (List (Sigma S.Result)) → Prop}
    (hV : ∀ ops, V ops → S.ValidOpSeq ops)
    (hC : ∀ ops μ, S.ValidOpSeq ops → S.Contract ops μ → C ops μ)
    {ops : List S.Op} {μ : PMF (List (Sigma S.Result))}
    (hv : (S.weaken V C).ValidOpSeq ops)
    (hμ : S.ValidOpSeq ops → S.Contract ops μ) :
    (S.weaken V C).Contract ops μ :=
  hC ops μ (hV ops hv) (hμ (hV ops hv))

end ObliviousSequenceSpec

end Cslib.DataStructure

/-! ## Canonical embedding of `StateTransitionSpec` into `ObliviousSequenceSpec` -/

namespace Cslib.DataStructure.StateTransitionSpec

/-- Embed a relational state-transition specification `D : StateTransitionSpec` at initial state
`s₀ : D.State` into `DataStructure.ObliviousSequenceSpec`:
* `ValidOpSeq` is demonic operation-sequence admissibility `D.ValidOpSeq s₀`;
* `Contract ops μ` requires every transcript `out ∈ μ.support` to be the label sequence of some
  valid relational execution transcript `tr : D.Transcript` with `tr.ops = ops`. -/
abbrev toObliviousSequenceSpec (D : StateTransitionSpec.{u, v, w}) (s₀ : D.State) :
    DataStructure.ObliviousSequenceSpec.{v, w} where
  Op := D.Op
  Result := D.Result
  ValidOpSeq := D.ValidOpSeq s₀
  Contract ops μ :=
    ∀ out ∈ μ.support, ∃ (tr : D.Transcript) (s_fin : D.State),
      tr.ops = ops ∧ tr.labels = out ∧ D.ValidTranscript s₀ tr s_fin

@[simp]
theorem toObliviousSequenceSpec_op (D : StateTransitionSpec.{u, v, w}) (s₀ : D.State) :
    (D.toObliviousSequenceSpec s₀).Op = D.Op := rfl

@[simp]
theorem toObliviousSequenceSpec_result (D : StateTransitionSpec.{u, v, w}) (s₀ : D.State) :
    (D.toObliviousSequenceSpec s₀).Result = D.Result := rfl

@[simp]
theorem toObliviousSequenceSpec_validOpSeq (D : StateTransitionSpec.{u, v, w}) (s₀ : D.State)
    (ops : List D.Op) :
    (D.toObliviousSequenceSpec s₀).ValidOpSeq ops ↔ D.ValidOpSeq s₀ ops := Iff.rfl

theorem toObliviousSequenceSpec_contract (D : StateTransitionSpec.{u, v, w}) (s₀ : D.State)
    (ops : List D.Op) (μ : PMF (List (Sigma D.Result))) :
    (D.toObliviousSequenceSpec s₀).Contract ops μ ↔
      ∀ out ∈ μ.support, ∃ (tr : D.Transcript) (s_fin : D.State),
        tr.ops = ops ∧ tr.labels = out ∧ D.ValidTranscript s₀ tr s_fin := Iff.rfl

/-- Every transcript in the support of a distribution satisfying
`(D.toObliviousSequenceSpec s₀).Contract ops μ` matches `ops`. -/
theorem toObliviousSequenceSpec_contract_matches {D : StateTransitionSpec.{u, v, w}} {s₀ : D.State}
    {ops : List D.Op} {μ : PMF (List (Sigma D.Result))}
    (h : (D.toObliviousSequenceSpec s₀).Contract ops μ) :
    ∀ out ∈ μ.support, DataStructure.TranscriptMatches ops out := by
  intro out hout
  obtain ⟨tr, _, hops, rfl, _⟩ := h out hout
  simpa [DataStructure.TranscriptMatches, Transcript.labels_map_fst] using hops

/-- On a deterministic specification (`[D.HasStepFn f]`) and an admissible operation sequence
`D.ValidHistory s₀ ops`, `(D.toObliviousSequenceSpec s₀).Contract ops μ` holds if and only if
every output trace in `μ.support` equals `(D.run s₀ ops).2`. -/
theorem toObliviousSequenceSpec_contract_iff_of_hasStepFn (D : StateTransitionSpec.{u, v, w})
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (s₀ : D.State) {ops : List D.Op} (hv : D.ValidHistory s₀ ops)
    (μ : PMF (List (Sigma D.Result))) :
    (D.toObliviousSequenceSpec s₀).Contract ops μ ↔
      ∀ out ∈ μ.support, out = (D.run s₀ ops).2 := by
  constructor
  · intro h out hout
    obtain ⟨tr, s_fin, hops, rfl, htr⟩ := h out hout
    obtain ⟨_, _, htr_eq⟩ := (D.validTranscript_iff_run s₀ tr s_fin).mp htr
    rw [htr_eq, hops, D.canonicalTranscript_labels]
  · intro h out hout
    refine ⟨D.canonicalTranscript s₀ ops, (D.run s₀ ops).1, D.canonicalTranscript_ops s₀ ops,
      ?_, D.validTranscript_canonicalTranscript hv⟩
    rw [h out hout, D.canonicalTranscript_labels]

/-- The point mass `PMF.pure (D.run s₀ ops).2` satisfies
`(D.toObliviousSequenceSpec s₀).Contract ops` whenever `D.ValidHistory s₀ ops`. -/
theorem toObliviousSequenceSpec_contract_pure_run (D : StateTransitionSpec.{u, v, w})
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (s₀ : D.State) {ops : List D.Op} (hv : D.ValidHistory s₀ ops) :
    (D.toObliviousSequenceSpec s₀).Contract ops (PMF.pure (D.run s₀ ops).2) := by
  rw [D.toObliviousSequenceSpec_contract_iff_of_hasStepFn s₀ hv]
  intro out hout
  exact (PMF.mem_support_pure_iff _ _).mp hout

end Cslib.DataStructure.StateTransitionSpec

namespace Cslib.DataStructure.ObliviousSequenceSpec

/-- Construct an `ObliviousSequenceSpec` from a deterministic state-transition function
`stepFn : (s : State) → (o : Op) → State × Result o`, an initial state `s₀ : State`, and an
optional per-step admissibility predicate `valid`. -/
abbrev ofFn {State : Type u} {Op : Type v} {Result : Op → Type w}
    (stepFn : (s : State) → (o : Op) → State × Result o)
    (s₀ : State)
    (valid : State → Op → Prop := fun _ _ => True) :
    ObliviousSequenceSpec.{v, w} :=
  (StateTransitionSpec.ofFn stepFn valid).toObliviousSequenceSpec s₀

end Cslib.DataStructure.ObliviousSequenceSpec
