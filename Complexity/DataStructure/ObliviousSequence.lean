/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Basic
public import Complexity.Probability.KWiseIndependent.Coupling
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
import Complexity.Probability.Uniform

/-!
# Oblivious-Sequence Data Structure Specifications and Hash-Family Contracts

An *oblivious-sequence specification* (`Cslib.DataStructure.ObliviousSequenceSpec`) describes the
input-output contract of a randomized or deterministic data structure against an *oblivious*
(non-adaptive) caller that fixes a finite operation sequence `ops : List Op` in advance. Unlike a
state-transition specification (`Cslib.Stateful.Spec`), an oblivious-sequence specification has no
abstract `State` field: it constrains the joint probability distribution
`μ : PMF (List (Sigma Result))` of the full input-output transcript directly via a predicate
`Contract ops μ`.

Every relational state-transition specification `D : Cslib.Stateful.Spec` at an initial state
`s₀ : D.State` embeds canonically into `ObliviousSequenceSpec` via
`Cslib.Stateful.Spec.toObliviousSequenceSpec`, requiring every transcript in the support of `μ` to
arise from a valid relational execution of `D` from `s₀`. On deterministic specifications
(`[D.HasStepFn f]`), this contract reduces to concentration on the unique canonical output trace
`(D.run s₀ ops).2`.

The second half of this file specializes `ObliviousSequenceSpec` to multi-epoch hash families with
operations `HashOp.resample` and `HashOp.eval u`:
* `kWiseHashSpec k U m` specifies that on any oblivious sequence querying at most `k` distinct keys
  within each resampling epoch, the transcript distribution equals the exact independent-epoch
  `k`-wise uniform distribution `idealHashTranscriptPMF m ops`.
* `whpKWiseHashSpec k U m δ` relaxes this contract to an `E * δ` coupling bound
  (`Cslib.Probability.PMF.CoupledWithin`) against `idealHashTranscriptPMF m ops`, where
  `E = epochCount ops` is the number of resampling epochs.
* `kWiseHashSpec_contract_evalHashOps` and `whpKWiseHashSpec_contract_evalHashOps_prod` prove that
  any finite-seed `k`-wise independent hash family realizes `kWiseHashSpec`, and any two-level
  finite-seed hash family whose top seed falls in a `k`-wise independent set `GoodTop` with failure
  probability `δ` realizes `whpKWiseHashSpec k U m δ`.

## Main definitions

* `Cslib.DataStructure.ObliviousSequenceSpec`: state-free distributional specification over finite
  oblivious operation sequences.
* `Cslib.DataStructure.TranscriptMatches`: alignment predicate `out.map Sigma.fst = ops` between an
  operation sequence and an input-output transcript.
* `Cslib.DataStructure.ObliviousSequenceSpec.weaken`: monotonicity combinator strengthening
  `ValidOpSeq` and weakening `Contract`.
* `Cslib.Stateful.Spec.toObliviousSequenceSpec`, `Cslib.DataStructure.ObliviousSequenceSpec.ofFn`:
  canonical embeddings of relational and deterministic state-transition specifications into
  `ObliviousSequenceSpec`.
* `Cslib.DataStructure.HashOp`, `Cslib.DataStructure.HashResult`: hash-family operations
  (`.resample` and `.eval u`) and their observation types (`PUnit` and `Fin m`).
* `Cslib.DataStructure.BoundedEpochKeys`, `Cslib.DataStructure.epochCount`,
  `Cslib.DataStructure.idealHashTranscriptPMF`, `Cslib.DataStructure.evalHashOps`: epoch key-count
  bounds, ideal multi-epoch uniform hash transcripts, and concrete multi-epoch seed evaluation.
* `Cslib.DataStructure.kWiseHashSpec`, `Cslib.DataStructure.whpKWiseHashSpec`: exact and
  high-probability `k`-wise independent hash-family specifications.

## Main results

* `Cslib.Stateful.Spec.toObliviousSequenceSpec_contract_iff_of_hasStepFn`: on a deterministic
  specification, `(D.toObliviousSequenceSpec s₀).Contract ops μ` holds under `D.ValidHistory s₀ ops`
  if and only if every `out ∈ μ.support` equals `(D.run s₀ ops).2`.
* `Cslib.DataStructure.evalHashOpsFromSeed_eq_of_afterCurrentEpoch_eq_none`,
  `Cslib.DataStructure.evalHashOpsFromSeed_eq_of_afterCurrentEpoch_eq_some`,
  `Cslib.DataStructure.evalHashOps_eq_of_afterCurrentEpoch_eq_none`,
  `Cslib.DataStructure.evalHashOps_eq_of_afterCurrentEpoch_eq_some`,
  `Cslib.DataStructure.evalHashOpsFromSeed_map_equiv`: epoch decomposition and seed-equivalence
  transport equations for `evalHashOpsFromSeed` and `evalHashOps`.
* `Cslib.DataStructure.kWiseHashSpec_contract_evalHashOps`: any finite-seed `k`-wise independent
  hash family satisfies `kWiseHashSpec` under uniform resampling.
* `Cslib.DataStructure.whpKWiseHashSpec_contract_evalHashOps_prod`: any two-level hash family with a
  `(1 - δ)`-good top-seed event satisfies `whpKWiseHashSpec k U m δ` under uniform resampling.

## References

* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
* [S. P. Vadhan, *Pseudorandomness*, Section 3.5][Vadhan2012]
* [M. Mitzenmacher, E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

open scoped ENNReal NNReal Cslib.Probability.PMF
open Cslib.Probability Cslib.Probability.PMF MeasureTheory ProbabilityTheory

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

/-! ## Canonical embedding of `Stateful.Spec` into `ObliviousSequenceSpec` -/

namespace Cslib.Stateful.Spec

/-- Embed a relational state-transition specification `D : Stateful.Spec` at initial state
`s₀ : D.State` into `DataStructure.ObliviousSequenceSpec`:
* `ValidOpSeq` is demonic operation-sequence admissibility `D.ValidOpSeq s₀`;
* `Contract ops μ` requires every transcript `out ∈ μ.support` to be the label sequence of some
  valid relational execution transcript `tr : D.Transcript` with `tr.ops = ops`. -/
abbrev toObliviousSequenceSpec (D : Spec.{u, v, w}) (s₀ : D.State) :
    DataStructure.ObliviousSequenceSpec.{v, w} where
  Op := D.Op
  Result := D.Result
  ValidOpSeq := D.ValidOpSeq s₀
  Contract ops μ :=
    ∀ out ∈ μ.support, ∃ (tr : D.Transcript) (s_fin : D.State),
      tr.ops = ops ∧ tr.labels = out ∧ D.ValidTranscript s₀ tr s_fin

@[simp]
theorem toObliviousSequenceSpec_op (D : Spec.{u, v, w}) (s₀ : D.State) :
    (D.toObliviousSequenceSpec s₀).Op = D.Op := rfl

@[simp]
theorem toObliviousSequenceSpec_result (D : Spec.{u, v, w}) (s₀ : D.State) :
    (D.toObliviousSequenceSpec s₀).Result = D.Result := rfl

@[simp]
theorem toObliviousSequenceSpec_validOpSeq (D : Spec.{u, v, w}) (s₀ : D.State)
    (ops : List D.Op) :
    (D.toObliviousSequenceSpec s₀).ValidOpSeq ops ↔ D.ValidOpSeq s₀ ops := Iff.rfl

theorem toObliviousSequenceSpec_contract (D : Spec.{u, v, w}) (s₀ : D.State)
    (ops : List D.Op) (μ : PMF (List (Sigma D.Result))) :
    (D.toObliviousSequenceSpec s₀).Contract ops μ ↔
      ∀ out ∈ μ.support, ∃ (tr : D.Transcript) (s_fin : D.State),
        tr.ops = ops ∧ tr.labels = out ∧ D.ValidTranscript s₀ tr s_fin := Iff.rfl

/-- Every transcript in the support of a distribution satisfying
`(D.toObliviousSequenceSpec s₀).Contract ops μ` matches `ops`. -/
theorem toObliviousSequenceSpec_contract_matches {D : Spec.{u, v, w}} {s₀ : D.State}
    {ops : List D.Op} {μ : PMF (List (Sigma D.Result))}
    (h : (D.toObliviousSequenceSpec s₀).Contract ops μ) :
    ∀ out ∈ μ.support, DataStructure.TranscriptMatches ops out := by
  intro out hout
  obtain ⟨tr, _, hops, rfl, _⟩ := h out hout
  simpa [DataStructure.TranscriptMatches, Transcript.labels_map_fst] using hops

/-- On a deterministic specification (`[D.HasStepFn f]`) and an admissible operation sequence
`D.ValidHistory s₀ ops`, `(D.toObliviousSequenceSpec s₀).Contract ops μ` holds if and only if
every output trace in `μ.support` equals `(D.run s₀ ops).2`. -/
theorem toObliviousSequenceSpec_contract_iff_of_hasStepFn (D : Spec.{u, v, w})
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
theorem toObliviousSequenceSpec_contract_pure_run (D : Spec.{u, v, w})
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (s₀ : D.State) {ops : List D.Op} (hv : D.ValidHistory s₀ ops) :
    (D.toObliviousSequenceSpec s₀).Contract ops (PMF.pure (D.run s₀ ops).2) := by
  rw [D.toObliviousSequenceSpec_contract_iff_of_hasStepFn s₀ hv]
  intro out hout
  exact (PMF.mem_support_pure_iff _ _).mp hout

end Cslib.Stateful.Spec

namespace Cslib.DataStructure

namespace ObliviousSequenceSpec

/-- Construct an `ObliviousSequenceSpec` from a deterministic state-transition function
`stepFn : (s : State) → (o : Op) → State × Result o`, an initial state `s₀ : State`, and an
optional per-step admissibility predicate `valid`. -/
abbrev ofFn {State : Type u} {Op : Type v} {Result : Op → Type w}
    (stepFn : (s : State) → (o : Op) → State × Result o)
    (s₀ : State)
    (valid : State → Op → Prop := fun _ _ => True) :
    ObliviousSequenceSpec.{v, w} :=
  (Stateful.Spec.ofFn stepFn valid).toObliviousSequenceSpec s₀

end ObliviousSequenceSpec

/-! ## Multi-epoch hash-family operations and specifications -/

/-- Operations of a resamplable hash-family data structure over universe `Fin U`:
* `resample`: draw a fresh hash function from the family (starting a new resampling epoch);
* `eval u`: evaluate the current hash function at key `u : Fin U`. -/
inductive HashOp (U : ℕ) where
  | resample : HashOp U
  | eval (u : Fin U) : HashOp U
  deriving DecidableEq

/-- Observation type returned by each `HashOp U` for codomain `Fin m`:
`PUnit` for `.resample` and `Fin m` for `.eval u`. -/
abbrev HashResult {U : ℕ} (m : ℕ) : HashOp U → Type
  | .resample => PUnit
  | .eval _ => Fin m

/-- Input-output label pairing a `HashOp U` operation with its `HashResult m` observation. -/
abbrev HashLabel (U m : ℕ) : Type := Sigma (@HashResult U m)

/-- The finite set of distinct keys queried in the current epoch of `ops` (before the first
`.resample` operation). -/
@[expose] def currentEpochKeys {U : ℕ} : List (HashOp U) → Finset (Fin U)
  | [] => ∅
  | .resample :: _ => ∅
  | .eval u :: rest => insert u (currentEpochKeys rest)

@[simp]
theorem currentEpochKeys_nil {U : ℕ} : currentEpochKeys ([] : List (HashOp U)) = ∅ := rfl

@[simp]
theorem currentEpochKeys_resample {U : ℕ} (rest : List (HashOp U)) :
    currentEpochKeys (.resample :: rest) = ∅ := rfl

@[simp]
theorem currentEpochKeys_eval {U : ℕ} (u : Fin U) (rest : List (HashOp U)) :
    currentEpochKeys (.eval u :: rest) = insert u (currentEpochKeys rest) := rfl

/-- The suffix of `ops` following the first `.resample` operation, or `none` if `ops` contains no
`.resample`. -/
@[expose] def afterCurrentEpoch {U : ℕ} : List (HashOp U) → Option (List (HashOp U))
  | [] => none
  | .resample :: rest => some rest
  | .eval _ :: rest => afterCurrentEpoch rest

@[simp]
theorem afterCurrentEpoch_nil {U : ℕ} : afterCurrentEpoch ([] : List (HashOp U)) = none := rfl

@[simp]
theorem afterCurrentEpoch_resample {U : ℕ} (rest : List (HashOp U)) :
    afterCurrentEpoch (.resample :: rest) = some rest := rfl

@[simp]
theorem afterCurrentEpoch_eval {U : ℕ} (u : Fin U) (rest : List (HashOp U)) :
    afterCurrentEpoch (.eval u :: rest) = afterCurrentEpoch rest := rfl

/-- When `afterCurrentEpoch ops = some rest`, `rest` is strictly shorter than `ops`. -/
theorem length_lt_of_afterCurrentEpoch_eq_some {U : ℕ} {ops rest : List (HashOp U)}
    (h : afterCurrentEpoch ops = some rest) : rest.length < ops.length := by
  induction ops with
  | nil => cases h
  | cons o tail ih =>
    cases o with
    | resample =>
      injection h with hEq
      subst hEq
      exact Nat.lt_succ_self _
    | eval u =>
      exact Nat.lt_succ_of_lt (ih h)

/-- Number of `.resample` operations in `ops`. -/
@[expose] def resampleCount {U : ℕ} : List (HashOp U) → ℕ
  | [] => 0
  | .resample :: rest => 1 + resampleCount rest
  | .eval _ :: rest => resampleCount rest

/-- Total number of resampling epochs in `ops` (the initial epoch plus one for each `.resample`). -/
@[expose] def epochCount {U : ℕ} (ops : List (HashOp U)) : ℕ :=
  1 + resampleCount ops

@[simp]
theorem epochCount_pos {U : ℕ} (ops : List (HashOp U)) : 0 < epochCount ops := by
  simp [epochCount]

theorem resampleCount_eq_zero_of_afterCurrentEpoch_eq_none {U : ℕ} {ops : List (HashOp U)}
    (h : afterCurrentEpoch ops = none) : resampleCount ops = 0 := by
  induction ops with
  | nil => rfl
  | cons o tail ih =>
    cases o with
    | resample => cases h
    | eval _ => exact ih h

theorem resampleCount_eq_succ_of_afterCurrentEpoch_eq_some {U : ℕ} {ops rest : List (HashOp U)}
    (h : afterCurrentEpoch ops = some rest) : resampleCount ops = 1 + resampleCount rest := by
  induction ops with
  | nil => cases h
  | cons o tail ih =>
    cases o with
    | resample =>
      injection h with hEq
      subst hEq
      rfl
    | eval _ => exact ih h

/-- Admissibility predicate asserting that every resampling epoch of `ops` queries at most `k`
distinct keys. -/
@[expose] def BoundedEpochKeys {U : ℕ} (k : ℕ) (ops : List (HashOp U)) : Prop :=
  (currentEpochKeys ops).card ≤ k ∧
    match _h : afterCurrentEpoch ops with
    | none => True
    | some rest => BoundedEpochKeys k rest
termination_by ops.length
decreasing_by exact length_lt_of_afterCurrentEpoch_eq_some _h

theorem BoundedEpochKeys.card_currentEpochKeys_le {U : ℕ} {k : ℕ} {ops : List (HashOp U)}
    (h : BoundedEpochKeys k ops) : (currentEpochKeys ops).card ≤ k := by
  rw [BoundedEpochKeys] at h
  exact h.1

theorem BoundedEpochKeys.of_afterCurrentEpoch_eq_some {U : ℕ} {k : ℕ}
    {ops rest : List (HashOp U)} (h : BoundedEpochKeys k ops)
    (hafter : afterCurrentEpoch ops = some rest) : BoundedEpochKeys k rest := by
  rw [BoundedEpochKeys] at h
  have h₂ := h.2
  rw [hafter] at h₂
  exact h₂

@[simp]
theorem boundedEpochKeys_nil {U : ℕ} (k : ℕ) : BoundedEpochKeys k ([] : List (HashOp U)) := by
  rw [BoundedEpochKeys]
  simp

/-- Deterministic transcript of the current epoch of `ops` (before the first `.resample`),
determined by the restriction `g : currentEpochKeys ops → Fin m` of the hash function to the keys
queried in that epoch. -/
@[expose] def currentEpochPrefixTranscript {U : ℕ} (m : ℕ) :
    (ops : List (HashOp U)) → (currentEpochKeys ops → Fin m) → List (HashLabel U m)
  | [], _ => []
  | .resample :: _, _ => []
  | .eval u :: rest, g =>
    ⟨.eval u, g ⟨u, Finset.mem_insert_self u (currentEpochKeys rest)⟩⟩ ::
      currentEpochPrefixTranscript m rest
        (fun x => g ⟨x.1, Finset.mem_insert_of_mem x.2⟩)

/-- Ideal multi-epoch transcript distribution of a `k`-wise independent hash family with codomain
`Fin m`: in each epoch, the values on `currentEpochKeys ops` are drawn uniformly from
`currentEpochKeys ops → Fin m`, independently of all subsequent epochs. -/
@[expose] noncomputable def idealHashTranscriptPMF {U : ℕ} (m : ℕ) [NeZero m]
    (ops : List (HashOp U)) : PMF (List (HashLabel U m)) :=
  let epochPMF :=
    (PMF.uniformOfFintype (currentEpochKeys ops → Fin m)).map
      (currentEpochPrefixTranscript m ops)
  match _h : afterCurrentEpoch ops with
  | none => epochPMF
  | some rest =>
    epochPMF.bind fun pref =>
      (idealHashTranscriptPMF m rest).map fun tailOut =>
        pref ++ (⟨.resample, PUnit.unit⟩ :: tailOut)
termination_by ops.length
decreasing_by exact length_lt_of_afterCurrentEpoch_eq_some _h

/-- Step-by-step evaluation of `ops : List (HashOp U)` starting from an active seed `θ : Seed`:
`.eval u` deterministically returns `eval θ u` without changing `θ`, while `.resample` draws a
fresh seed `θ' ← seedLaw` and continues with `θ'`. -/
@[expose] noncomputable def evalHashOpsFromSeed {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (θ : Seed) :
    List (HashOp U) → PMF (List (HashLabel U m))
  | [] => PMF.pure []
  | .eval u :: rest =>
    (evalHashOpsFromSeed seedLaw eval θ rest).map (fun out => ⟨.eval u, eval θ u⟩ :: out)
  | .resample :: rest =>
    seedLaw.bind (fun θ' =>
      (evalHashOpsFromSeed seedLaw eval θ' rest).map (fun out => ⟨.resample, PUnit.unit⟩ :: out))

/-- Multi-epoch transcript distribution induced by drawing an initial seed `θ₀ ← seedLaw` and
executing `ops : List (HashOp U)` via `evalHashOpsFromSeed`. -/
@[expose] noncomputable def evalHashOps {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m)
    (ops : List (HashOp U)) : PMF (List (HashLabel U m)) :=
  seedLaw.bind (fun θ₀ => evalHashOpsFromSeed seedLaw eval θ₀ ops)

end Cslib.DataStructure

namespace Cslib.DataStructure

/-- Exact `k`-wise independent hash-family specification over universe `Fin U` and codomain
`Fin m`: on any oblivious operation sequence `ops` querying at most `k` distinct keys per
resampling epoch (`BoundedEpochKeys k ops`), the output transcript distribution equals
`idealHashTranscriptPMF m ops`. -/
abbrev kWiseHashSpec (k U m : ℕ) [NeZero m] : ObliviousSequenceSpec where
  Op := HashOp U
  Result := HashResult m
  ValidOpSeq := BoundedEpochKeys k
  Contract ops μ := μ = idealHashTranscriptPMF m ops

/-- High-probability `k`-wise independent hash-family specification with per-epoch failure bound
`δ : ℝ≥0∞`: on any oblivious operation sequence `ops` querying at most `k` distinct keys per
resampling epoch (`BoundedEpochKeys k ops`), every supported transcript matches `ops` and the
transcript distribution `μ` is coupled within `(epochCount ops : ℝ≥0∞) * δ` of
`idealHashTranscriptPMF m ops`. -/
abbrev whpKWiseHashSpec (k U m : ℕ) [NeZero m] (δ : ℝ≥0∞) : ObliviousSequenceSpec where
  Op := HashOp U
  Result := HashResult m
  ValidOpSeq := BoundedEpochKeys k
  Contract ops μ :=
    (∀ out ∈ μ.support, TranscriptMatches ops out) ∧
    CoupledWithin μ (idealHashTranscriptPMF m ops) ((epochCount ops : ℝ≥0∞) * δ)

/-- Every transcript in the support of `evalHashOpsFromSeed` matches `ops`. -/
theorem transcriptMatches_of_mem_support_evalHashOpsFromSeed {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (θ : Seed) (ops : List (HashOp U)) :
    ∀ out ∈ (evalHashOpsFromSeed seedLaw eval θ ops).support, TranscriptMatches ops out := by
  induction ops generalizing θ with
  | nil =>
    intro out hout
    rcases (PMF.mem_support_pure_iff _ _).mp hout with rfl
    rfl
  | cons o rest ih =>
    cases o with
    | eval u =>
      intro out hout
      obtain ⟨tailOut, htail, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      exact (transcriptMatches_cons (.eval u) (eval θ u) rest tailOut).mpr (ih θ tailOut htail)
    | resample =>
      intro out hout
      obtain ⟨θ', _, hout'⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨tailOut, htail, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout'
      exact (transcriptMatches_cons .resample PUnit.unit rest tailOut).mpr (ih θ' tailOut htail)

/-- Every transcript in the support of `evalHashOps` matches `ops`. -/
theorem transcriptMatches_of_mem_support_evalHashOps {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (ops : List (HashOp U)) :
    ∀ out ∈ (evalHashOps seedLaw eval ops).support, TranscriptMatches ops out := by
  intro out hout
  obtain ⟨θ₀, _, hout'⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  exact transcriptMatches_of_mem_support_evalHashOpsFromSeed seedLaw eval θ₀ ops out hout'

private theorem restrict_comp_inclusion {U m : ℕ} (f : Fin U → Fin m) (u : Fin U)
    (s : Finset (Fin U)) :
    (fun x : s => (insert u s).restrict f ⟨x.1, Finset.mem_insert_of_mem x.2⟩) =
      s.restrict f := rfl

/-- On a single-epoch sequence (`afterCurrentEpoch ops = none`), `evalHashOpsFromSeed` reduces to a
point mass on `currentEpochPrefixTranscript` applied to the restricted hash function
`(currentEpochKeys ops).restrict (eval θ)`. -/
theorem evalHashOpsFromSeed_eq_of_afterCurrentEpoch_eq_none {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (θ : Seed)
    {ops : List (HashOp U)} (hafter : afterCurrentEpoch ops = none) :
    evalHashOpsFromSeed seedLaw eval θ ops =
      PMF.pure (currentEpochPrefixTranscript m ops ((currentEpochKeys ops).restrict (eval θ))) := by
  induction ops with
  | nil => rfl
  | cons o rest ih =>
    cases o with
    | resample => cases hafter
    | eval u =>
      simp only [afterCurrentEpoch_eval] at hafter
      simp only [evalHashOpsFromSeed, ih hafter, _root_.PMF.pure_map, currentEpochPrefixTranscript,
        currentEpochKeys_eval, restrict_comp_inclusion]
      rfl

/-- When `afterCurrentEpoch ops = some rest`, `evalHashOpsFromSeed` decomposes into the
deterministic current-epoch prefix `currentEpochPrefixTranscript` followed by `.resample` and an
independent draw from `evalHashOps seedLaw eval rest`. -/
theorem evalHashOpsFromSeed_eq_of_afterCurrentEpoch_eq_some {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (θ : Seed)
    {ops rest : List (HashOp U)} (hafter : afterCurrentEpoch ops = some rest) :
    evalHashOpsFromSeed seedLaw eval θ ops =
      (evalHashOps seedLaw eval rest).map (fun tailOut =>
        currentEpochPrefixTranscript m ops ((currentEpochKeys ops).restrict (eval θ)) ++
          (⟨.resample, PUnit.unit⟩ :: tailOut)) := by
  induction ops with
  | nil => cases hafter
  | cons o tail ih =>
    cases o with
    | resample =>
      injection hafter with hEq
      subst hEq
      simp [evalHashOpsFromSeed, evalHashOps, currentEpochPrefixTranscript, PMF.map_bind]
    | eval u =>
      simp only [afterCurrentEpoch_eval] at hafter
      simp only [evalHashOpsFromSeed, ih hafter, PMF.map_comp, Function.comp_def,
        currentEpochPrefixTranscript, currentEpochKeys_eval, restrict_comp_inclusion,
        List.cons_append]
      rfl

/-- On a single-epoch sequence (`afterCurrentEpoch ops = none`), `evalHashOps` is the pushforward of
the restricted seed distribution `seedLaw.map (fun θ => (currentEpochKeys ops).restrict (eval θ))`
under `currentEpochPrefixTranscript m ops`. -/
theorem evalHashOps_eq_of_afterCurrentEpoch_eq_none {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m)
    {ops : List (HashOp U)} (hafter : afterCurrentEpoch ops = none) :
    evalHashOps seedLaw eval ops =
      (seedLaw.map (fun θ => (currentEpochKeys ops).restrict (eval θ))).map
        (currentEpochPrefixTranscript m ops) := by
  rw [PMF.map_comp]
  simp only [evalHashOps, evalHashOpsFromSeed_eq_of_afterCurrentEpoch_eq_none seedLaw eval _ hafter,
    Function.comp_def, _root_.PMF.map]

/-- When `afterCurrentEpoch ops = some rest`, `evalHashOps` decomposes into the current-epoch prefix
distribution bound to an independent tail draw `evalHashOps seedLaw eval rest`. -/
theorem evalHashOps_eq_of_afterCurrentEpoch_eq_some {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m)
    {ops rest : List (HashOp U)} (hafter : afterCurrentEpoch ops = some rest) :
    evalHashOps seedLaw eval ops =
      ((seedLaw.map (fun θ => (currentEpochKeys ops).restrict (eval θ))).map
        (currentEpochPrefixTranscript m ops)).bind (fun pref =>
          (evalHashOps seedLaw eval rest).map (fun tailOut =>
            pref ++ (⟨.resample, PUnit.unit⟩ :: tailOut))) := by
  simp only [evalHashOps, evalHashOpsFromSeed_eq_of_afterCurrentEpoch_eq_some seedLaw eval _ hafter,
    PMF.bind_map, Function.comp_def]

/-- **Fundamental bridge theorem for exact `k`-wise independent hash families**:
if `eval : Seed → Fin U → Fin m` satisfies `IsKWiseIndependentHash k eval`, then on any oblivious
operation sequence `ops` querying at most `k` distinct keys per epoch (`BoundedEpochKeys k ops`),
`evalHashOps (PMF.uniformOfFintype Seed) eval ops` equals `idealHashTranscriptPMF m ops` and
therefore satisfies `(kWiseHashSpec k U m).Contract ops`. -/
theorem kWiseHashSpec_contract_evalHashOps {Seed : Type u} {k U m : ℕ}
    [Fintype Seed] [Nonempty Seed] [NeZero m] {eval : Seed → Fin U → Fin m}
    (hk : Probability.IsKWiseIndependentHash k eval)
    {ops : List (HashOp U)} (hv : BoundedEpochKeys k ops) :
    (kWiseHashSpec k U m).Contract ops
      (evalHashOps (PMF.uniformOfFintype Seed) eval ops) := by
  change evalHashOps (PMF.uniformOfFintype Seed) eval ops = idealHashTranscriptPMF m ops
  have hcard : (currentEpochKeys ops).card ≤ k := hv.card_currentEpochKeys_le
  have hrest_unif := uniformOfFintype_map_restrict_eq hk hcard
  rw [idealHashTranscriptPMF]
  cases hafter : afterCurrentEpoch ops with
  | none =>
    rw [evalHashOps_eq_of_afterCurrentEpoch_eq_none _ _ hafter, hrest_unif]
  | some rest =>
    have ih := kWiseHashSpec_contract_evalHashOps hk (hv.of_afterCurrentEpoch_eq_some hafter)
    change evalHashOps (PMF.uniformOfFintype Seed) eval rest = idealHashTranscriptPMF m rest at ih
    rw [evalHashOps_eq_of_afterCurrentEpoch_eq_some _ _ hafter, hrest_unif, ih]
termination_by ops.length
decreasing_by exact length_lt_of_afterCurrentEpoch_eq_some hafter

end Cslib.DataStructure

namespace Cslib.DataStructure

/-- Every distribution satisfying `(kWiseHashSpec k U m).Contract ops` also satisfies
`(whpKWiseHashSpec k U m δ).Contract ops` for any `δ : ℝ≥0∞`. -/
theorem whpKWiseHashSpec_contract_of_kWiseHashSpec {k U m : ℕ} [NeZero m] (δ : ℝ≥0∞)
    {ops : List (HashOp U)} {μ : PMF (List (HashLabel U m))}
    (hmatch : ∀ out ∈ μ.support, TranscriptMatches ops out)
    (hk : (kWiseHashSpec k U m).Contract ops μ) :
    (whpKWiseHashSpec k U m δ).Contract ops μ := by
  refine ⟨hmatch, ?_⟩
  change μ = idealHashTranscriptPMF m ops at hk
  rw [hk]
  exact (CoupledWithin.refl _).mono (by simp)

private theorem coupledWithin_evalHashOps_prod {TopSeed : Type u} {BotSeed : Type v}
    {k U m : ℕ} [Fintype TopSeed] [Nonempty TopSeed] [DecidableEq TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    [NeZero m] (eval : TopSeed → BotSeed → Fin U → Fin m)
    (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop, Probability.IsKWiseIndependentHash k (eval α))
    {ops : List (HashOp U)} (hv : BoundedEpochKeys k ops) :
    CoupledWithin
      (evalHashOps (PMF.uniformOfFintype (TopSeed × BotSeed)) (fun p => eval p.1 p.2) ops)
      (idealHashTranscriptPMF m ops)
      ((epochCount ops : ℝ≥0∞) *
        (((Finset.univ \ GoodTop).card : ℝ≥0∞) / Fintype.card TopSeed)) := by
  let δ : ℝ≥0∞ := ((Finset.univ \ GoodTop).card : ℝ≥0∞) / Fintype.card TopSeed
  have hcard : (currentEpochKeys ops).card ≤ k := hv.card_currentEpochKeys_le
  have hepoch :
      CoupledWithin
        (((PMF.uniformOfFintype (TopSeed × BotSeed)).map
          (fun p => (currentEpochKeys ops).restrict (eval p.1 p.2))).map
            (currentEpochPrefixTranscript m ops))
        ((PMF.uniformOfFintype (currentEpochKeys ops → Fin m)).map
          (currentEpochPrefixTranscript m ops))
        δ :=
    (coupledWithin_uniformOfFintype_prod_restrict eval GoodTop hgood hcard).map
      (currentEpochPrefixTranscript m ops)
  rw [idealHashTranscriptPMF]
  cases hafter : afterCurrentEpoch ops with
  | none =>
    rw [evalHashOps_eq_of_afterCurrentEpoch_eq_none _ _ hafter]
    have hepoch_cnt : (epochCount ops : ℝ≥0∞) * δ = δ := by
      simp [epochCount, resampleCount_eq_zero_of_afterCurrentEpoch_eq_none hafter]
    rw [hepoch_cnt]
    exact hepoch
  | some rest =>
    rw [evalHashOps_eq_of_afterCurrentEpoch_eq_some _ _ hafter]
    have ih := coupledWithin_evalHashOps_prod eval GoodTop hgood
      (hv.of_afterCurrentEpoch_eq_some hafter)
    have hcomb := hepoch.map₂ ih (fun pref tailOut => pref ++ (⟨.resample, PUnit.unit⟩ :: tailOut))
    have hepoch_cnt :
        δ + (epochCount rest : ℝ≥0∞) * δ = (epochCount ops : ℝ≥0∞) * δ := by
      simp only [epochCount, resampleCount_eq_succ_of_afterCurrentEpoch_eq_some hafter]
      push_cast
      ring
    rwa [hepoch_cnt] at hcomb
termination_by ops.length
decreasing_by exact length_lt_of_afterCurrentEpoch_eq_some hafter

/-- **Fundamental bridge theorem for two-level high-probability `k`-wise hash families**:
if `eval : TopSeed → BotSeed → Fin U → Fin m` is `k`-wise independent on every good top seed
`α ∈ GoodTop`, then under uniform resampling on `TopSeed × BotSeed`, any oblivious sequence `ops`
querying at most `k` distinct keys per epoch (`BoundedEpochKeys k ops`) satisfies
`(whpKWiseHashSpec k U m δ).Contract ops` with bad-seed measure
`δ = (#(Finset.univ \ GoodTop) : ℝ≥0∞) / Fintype.card TopSeed`. -/
theorem whpKWiseHashSpec_contract_evalHashOps_prod {TopSeed : Type u} {BotSeed : Type v}
    {k U m : ℕ} [Fintype TopSeed] [Nonempty TopSeed] [DecidableEq TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    [NeZero m] (eval : TopSeed → BotSeed → Fin U → Fin m)
    (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop, Probability.IsKWiseIndependentHash k (eval α))
    {ops : List (HashOp U)} (hv : BoundedEpochKeys k ops) :
    (whpKWiseHashSpec k U m
      (((Finset.univ \ GoodTop).card : ℝ≥0∞) / Fintype.card TopSeed)).Contract ops
      (evalHashOps (PMF.uniformOfFintype (TopSeed × BotSeed)) (fun p => eval p.1 p.2) ops) :=
  ⟨transcriptMatches_of_mem_support_evalHashOps _ _ ops,
    coupledWithin_evalHashOps_prod eval GoodTop hgood hv⟩

/-- Relabelling the seed type along an equivalence `e : Seed₁ ≃ Seed₂` transports
`evalHashOpsFromSeed` by pushing forward `seedLaw` along `e` and pulling back `eval` along
`e.symm`. -/
theorem evalHashOpsFromSeed_map_equiv {Seed₁ : Type u} {Seed₂ : Type v} {U m : ℕ}
    (seedLaw : PMF Seed₁) (eval : Seed₁ → Fin U → Fin m)
    (e : Seed₁ ≃ Seed₂) (θ : Seed₁) (ops : List (HashOp U)) :
    evalHashOpsFromSeed seedLaw eval θ ops =
      evalHashOpsFromSeed (seedLaw.map e) (fun s => eval (e.symm s)) (e θ) ops := by
  induction ops generalizing θ with
  | nil => rfl
  | cons o rest ih =>
    cases o with
    | eval u =>
      simp [evalHashOpsFromSeed, ih θ]
    | resample =>
      dsimp only [evalHashOpsFromSeed]
      rw [PMF.bind_map]
      refine congrArg (seedLaw.bind ·) (funext fun θ' => ?_)
      dsimp only [Function.comp_def]
      rw [ih θ']

/-- Transport `whpKWiseHashSpec_contract_evalHashOps_prod` along a seed equivalence
`e : Seed ≃ (TopSeed × BotSeed)`. -/
theorem whpKWiseHashSpec_contract_evalHashOps_equiv {Seed : Type w}
    {TopSeed : Type u} {BotSeed : Type v}
    {k U m : ℕ} [Fintype Seed] [Nonempty Seed]
    [Fintype TopSeed] [Nonempty TopSeed] [DecidableEq TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    [NeZero m] (eval : Seed → Fin U → Fin m)
    (e : Seed ≃ (TopSeed × BotSeed))
    (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop, Probability.IsKWiseIndependentHash k (fun β => eval (e.symm (α, β))))
    {ops : List (HashOp U)} (hv : BoundedEpochKeys k ops) :
    (whpKWiseHashSpec k U m
      (((Finset.univ \ GoodTop).card : ℝ≥0∞) / Fintype.card TopSeed)).Contract ops
      (evalHashOps (PMF.uniformOfFintype Seed) eval ops) := by
  have hlaw : (PMF.uniformOfFintype Seed).map e = PMF.uniformOfFintype (TopSeed × BotSeed) :=
    Cslib.Probability.PMF.uniformOfFintype_map_equiv e
  have heq :
      evalHashOps (PMF.uniformOfFintype Seed) eval ops =
        evalHashOps (PMF.uniformOfFintype (TopSeed × BotSeed)) (fun p => eval (e.symm p)) ops := by
    rw [← hlaw]
    dsimp only [evalHashOps]
    rw [PMF.bind_map]
    refine congrArg ((PMF.uniformOfFintype Seed).bind ·) (funext fun θ₀ => ?_)
    exact evalHashOpsFromSeed_map_equiv _ _ e θ₀ ops
  rw [heq]
  exact whpKWiseHashSpec_contract_evalHashOps_prod (fun α β => eval (e.symm (α, β)))
    GoodTop hgood hv

end Cslib.DataStructure
