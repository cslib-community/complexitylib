/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.ObliviousSequence
public import Complexity.Probability.KWiseIndependent.Coupling
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
import Complexity.Probability.Uniform

/-!
# Multi-Epoch Hash-Family Oblivious-Sequence Specifications

This file defines oblivious-sequence specifications (`Cslib.DataStructure.ObliviousSequenceSpec`)
for resamplable hash families over a key universe `Fin U` and codomain `Fin m` with operations
`Op.resample` (starting a new resampling epoch with an independently sampled seed) and `Op.eval u`
(evaluating the active hash function at `u : Fin U`):

* `kWiseSpec k U m`: on any oblivious operation sequence querying at most `k` distinct keys within
  each resampling epoch (`BoundedEpochKeys k ops`), the transcript distribution equals the exact
  independent-epoch `k`-wise uniform distribution `idealTranscriptPMF m ops`.
* `whpKWiseSpec k U m δ`: relaxes this contract to an `E * δ` coupling bound
  (`Cslib.Probability.PMF.CoupledWithin`) against `idealTranscriptPMF m ops`, where
  `E = epochCount ops` is the number of resampling epochs.
* `kWiseSpec_contract_evalOps` and `whpKWiseSpec_contract_evalOps_prod`: prove that any finite-seed
  `k`-wise independent hash family satisfies `kWiseSpec`, and any two-level finite-seed hash family
  whose top seed falls in a `k`-wise independent set `GoodTop` with failure probability `δ`
  satisfies `whpKWiseSpec k U m δ`.

## Main definitions

* `Cslib.DataStructure.HashFamily.Op`, `Cslib.DataStructure.HashFamily.Result`,
  `Cslib.DataStructure.HashFamily.Label`: hash-family operations (`.resample` and `.eval u`),
  observation types (`PUnit` and `Fin m`), and input-output labels.
* `Cslib.DataStructure.HashFamily.BoundedEpochKeys`, `Cslib.DataStructure.HashFamily.epochCount`,
  `Cslib.DataStructure.HashFamily.idealTranscriptPMF`,
  `Cslib.DataStructure.HashFamily.evalOpsFromSeed`, `Cslib.DataStructure.HashFamily.evalOps`:
  epoch key-count bounds, ideal multi-epoch uniform hash transcripts, and concrete multi-epoch seed
  evaluation.
* `Cslib.DataStructure.HashFamily.kWiseSpec`, `Cslib.DataStructure.HashFamily.whpKWiseSpec`: exact
  and high-probability `k`-wise independent hash-family specifications.

## Main results

* `Cslib.DataStructure.HashFamily.evalOpsFromSeed_eq_of_afterCurrentEpoch_eq_none`,
  `Cslib.DataStructure.HashFamily.evalOpsFromSeed_eq_of_afterCurrentEpoch_eq_some`,
  `Cslib.DataStructure.HashFamily.evalOps_eq_of_afterCurrentEpoch_eq_none`,
  `Cslib.DataStructure.HashFamily.evalOps_eq_of_afterCurrentEpoch_eq_some`,
  `Cslib.DataStructure.HashFamily.evalOpsFromSeed_map_equiv`: epoch decomposition and
  seed-equivalence transport equations for `evalOpsFromSeed` and `evalOps`.
* `Cslib.DataStructure.HashFamily.kWiseSpec_contract_evalOps`: any finite-seed `k`-wise independent
  hash family satisfies `kWiseSpec` under uniform resampling.
* `Cslib.DataStructure.HashFamily.whpKWiseSpec_contract_evalOps_prod`,
  `Cslib.DataStructure.HashFamily.whpKWiseSpec_contract_evalOps_equiv`: any two-level hash family
  with a `(1 - δ)`-good top-seed event satisfies `whpKWiseSpec k U m δ` under uniform resampling.

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

namespace Cslib.DataStructure.HashFamily

/-- Operations of a resamplable hash-family data structure over universe `Fin U`:
* `resample`: draw a fresh hash function from the family (starting a new resampling epoch);
* `eval u`: evaluate the current hash function at key `u : Fin U`. -/
inductive Op (U : ℕ) where
  | resample : Op U
  | eval (u : Fin U) : Op U
  deriving DecidableEq

/-- Observation type returned by each `Op U` for codomain `Fin m`:
`PUnit` for `.resample` and `Fin m` for `.eval u`. -/
abbrev Result {U : ℕ} (m : ℕ) : Op U → Type
  | .resample => PUnit
  | .eval _ => Fin m

/-- Input-output label pairing an `Op U` operation with its `Result m` observation. -/
abbrev Label (U m : ℕ) : Type := Sigma (@Result U m)

/-- The finite set of distinct keys queried in the current epoch of `ops` (before the first
`.resample` operation). -/
@[expose] def currentEpochKeys {U : ℕ} : List (Op U) → Finset (Fin U)
  | [] => ∅
  | .resample :: _ => ∅
  | .eval u :: rest => insert u (currentEpochKeys rest)

@[simp]
theorem currentEpochKeys_nil {U : ℕ} : currentEpochKeys ([] : List (Op U)) = ∅ := rfl

@[simp]
theorem currentEpochKeys_resample {U : ℕ} (rest : List (Op U)) :
    currentEpochKeys (.resample :: rest) = ∅ := rfl

@[simp]
theorem currentEpochKeys_eval {U : ℕ} (u : Fin U) (rest : List (Op U)) :
    currentEpochKeys (.eval u :: rest) = insert u (currentEpochKeys rest) := rfl

/-- The suffix of `ops` following the first `.resample` operation, or `none` if `ops` contains no
`.resample`. -/
@[expose] def afterCurrentEpoch {U : ℕ} : List (Op U) → Option (List (Op U))
  | [] => none
  | .resample :: rest => some rest
  | .eval _ :: rest => afterCurrentEpoch rest

@[simp]
theorem afterCurrentEpoch_nil {U : ℕ} : afterCurrentEpoch ([] : List (Op U)) = none := rfl

@[simp]
theorem afterCurrentEpoch_resample {U : ℕ} (rest : List (Op U)) :
    afterCurrentEpoch (.resample :: rest) = some rest := rfl

@[simp]
theorem afterCurrentEpoch_eval {U : ℕ} (u : Fin U) (rest : List (Op U)) :
    afterCurrentEpoch (.eval u :: rest) = afterCurrentEpoch rest := rfl

/-- When `afterCurrentEpoch ops = some rest`, `rest` is strictly shorter than `ops`. -/
theorem length_lt_of_afterCurrentEpoch_eq_some {U : ℕ} {ops rest : List (Op U)}
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
@[expose] def resampleCount {U : ℕ} : List (Op U) → ℕ
  | [] => 0
  | .resample :: rest => 1 + resampleCount rest
  | .eval _ :: rest => resampleCount rest

/-- Total number of resampling epochs in `ops` (the initial epoch plus one for each `.resample`). -/
@[expose] def epochCount {U : ℕ} (ops : List (Op U)) : ℕ :=
  1 + resampleCount ops

@[simp]
theorem epochCount_pos {U : ℕ} (ops : List (Op U)) : 0 < epochCount ops := by
  simp [epochCount]

theorem resampleCount_eq_zero_of_afterCurrentEpoch_eq_none {U : ℕ} {ops : List (Op U)}
    (h : afterCurrentEpoch ops = none) : resampleCount ops = 0 := by
  induction ops with
  | nil => rfl
  | cons o tail ih =>
    cases o with
    | resample => cases h
    | eval _ => exact ih h

theorem resampleCount_eq_succ_of_afterCurrentEpoch_eq_some {U : ℕ} {ops rest : List (Op U)}
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
@[expose] def BoundedEpochKeys {U : ℕ} (k : ℕ) (ops : List (Op U)) : Prop :=
  (currentEpochKeys ops).card ≤ k ∧
    match _h : afterCurrentEpoch ops with
    | none => True
    | some rest => BoundedEpochKeys k rest
termination_by ops.length
decreasing_by exact length_lt_of_afterCurrentEpoch_eq_some _h

theorem BoundedEpochKeys.card_currentEpochKeys_le {U : ℕ} {k : ℕ} {ops : List (Op U)}
    (h : BoundedEpochKeys k ops) : (currentEpochKeys ops).card ≤ k := by
  rw [BoundedEpochKeys] at h
  exact h.1

theorem BoundedEpochKeys.of_afterCurrentEpoch_eq_some {U : ℕ} {k : ℕ}
    {ops rest : List (Op U)} (h : BoundedEpochKeys k ops)
    (hafter : afterCurrentEpoch ops = some rest) : BoundedEpochKeys k rest := by
  rw [BoundedEpochKeys] at h
  have h₂ := h.2
  rw [hafter] at h₂
  exact h₂

@[simp]
theorem boundedEpochKeys_nil {U : ℕ} (k : ℕ) : BoundedEpochKeys k ([] : List (Op U)) := by
  rw [BoundedEpochKeys]
  simp

/-- Deterministic transcript of the current epoch of `ops` (before the first `.resample`),
determined by the restriction `g : currentEpochKeys ops → Fin m` of the hash function to the keys
queried in that epoch. -/
@[expose] def currentEpochPrefixTranscript {U : ℕ} (m : ℕ) :
    (ops : List (Op U)) → (currentEpochKeys ops → Fin m) → List (Label U m)
  | [], _ => []
  | .resample :: _, _ => []
  | .eval u :: rest, g =>
    ⟨.eval u, g ⟨u, Finset.mem_insert_self u (currentEpochKeys rest)⟩⟩ ::
      currentEpochPrefixTranscript m rest
        (fun x => g ⟨x.1, Finset.mem_insert_of_mem x.2⟩)

/-- Ideal multi-epoch transcript distribution of a `k`-wise independent hash family with codomain
`Fin m`: in each epoch, the values on `currentEpochKeys ops` are drawn uniformly from
`currentEpochKeys ops → Fin m`, independently of all subsequent epochs. -/
@[expose] noncomputable def idealTranscriptPMF {U : ℕ} (m : ℕ) [NeZero m]
    (ops : List (Op U)) : PMF (List (Label U m)) :=
  let epochPMF :=
    (PMF.uniformOfFintype (currentEpochKeys ops → Fin m)).map
      (currentEpochPrefixTranscript m ops)
  match _h : afterCurrentEpoch ops with
  | none => epochPMF
  | some rest =>
    epochPMF.bind fun pref =>
      (idealTranscriptPMF m rest).map fun tailOut =>
        pref ++ (⟨.resample, PUnit.unit⟩ :: tailOut)
termination_by ops.length
decreasing_by exact length_lt_of_afterCurrentEpoch_eq_some _h

/-- Step-by-step evaluation of `ops : List (Op U)` starting from an active seed `θ : Seed`:
`.eval u` deterministically returns `eval θ u` without changing `θ`, while `.resample` draws a
fresh seed `θ' ← seedLaw` and continues with `θ'`. -/
@[expose] noncomputable def evalOpsFromSeed {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (θ : Seed) :
    List (Op U) → PMF (List (Label U m))
  | [] => PMF.pure []
  | .eval u :: rest =>
    (evalOpsFromSeed seedLaw eval θ rest).map (fun out => ⟨.eval u, eval θ u⟩ :: out)
  | .resample :: rest =>
    seedLaw.bind (fun θ' =>
      (evalOpsFromSeed seedLaw eval θ' rest).map (fun out => ⟨.resample, PUnit.unit⟩ :: out))

/-- Multi-epoch transcript distribution induced by drawing an initial seed `θ₀ ← seedLaw` and
executing `ops : List (Op U)` via `evalOpsFromSeed`. -/
@[expose] noncomputable def evalOps {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m)
    (ops : List (Op U)) : PMF (List (Label U m)) :=
  seedLaw.bind (fun θ₀ => evalOpsFromSeed seedLaw eval θ₀ ops)

/-- Exact `k`-wise independent hash-family specification over universe `Fin U` and codomain
`Fin m`: on any oblivious operation sequence `ops` querying at most `k` distinct keys per
resampling epoch (`BoundedEpochKeys k ops`), the output transcript distribution equals
`idealTranscriptPMF m ops`. -/
abbrev kWiseSpec (k U m : ℕ) [NeZero m] : ObliviousSequenceSpec where
  Op := Op U
  Result := Result m
  ValidOpSeq := BoundedEpochKeys k
  Contract ops μ := μ = idealTranscriptPMF m ops

/-- High-probability `k`-wise independent hash-family specification with per-epoch failure bound
`δ : ℝ≥0∞`: on any oblivious operation sequence `ops` querying at most `k` distinct keys per
resampling epoch (`BoundedEpochKeys k ops`), every supported transcript matches `ops` and the
transcript distribution `μ` is coupled within `(epochCount ops : ℝ≥0∞) * δ` of
`idealTranscriptPMF m ops`. -/
abbrev whpKWiseSpec (k U m : ℕ) [NeZero m] (δ : ℝ≥0∞) : ObliviousSequenceSpec where
  Op := Op U
  Result := Result m
  ValidOpSeq := BoundedEpochKeys k
  Contract ops μ :=
    (∀ out ∈ μ.support, TranscriptMatches ops out) ∧
    CoupledWithin μ (idealTranscriptPMF m ops) ((epochCount ops : ℝ≥0∞) * δ)

/-- Every transcript in the support of `evalOpsFromSeed` matches `ops`. -/
theorem transcriptMatches_of_mem_support_evalOpsFromSeed {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (θ : Seed) (ops : List (Op U)) :
    ∀ out ∈ (evalOpsFromSeed seedLaw eval θ ops).support, TranscriptMatches ops out := by
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

/-- Every transcript in the support of `evalOps` matches `ops`. -/
theorem transcriptMatches_of_mem_support_evalOps {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (ops : List (Op U)) :
    ∀ out ∈ (evalOps seedLaw eval ops).support, TranscriptMatches ops out := by
  intro out hout
  obtain ⟨θ₀, _, hout'⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  exact transcriptMatches_of_mem_support_evalOpsFromSeed seedLaw eval θ₀ ops out hout'

private theorem restrict_comp_inclusion {U m : ℕ} (f : Fin U → Fin m) (u : Fin U)
    (s : Finset (Fin U)) :
    (fun x : s => (insert u s).restrict f ⟨x.1, Finset.mem_insert_of_mem x.2⟩) =
      s.restrict f := rfl

/-- On a single-epoch sequence (`afterCurrentEpoch ops = none`), `evalOpsFromSeed` reduces to a
point mass on `currentEpochPrefixTranscript` applied to the restricted hash function
`(currentEpochKeys ops).restrict (eval θ)`. -/
theorem evalOpsFromSeed_eq_of_afterCurrentEpoch_eq_none {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (θ : Seed)
    {ops : List (Op U)} (hafter : afterCurrentEpoch ops = none) :
    evalOpsFromSeed seedLaw eval θ ops =
      PMF.pure (currentEpochPrefixTranscript m ops ((currentEpochKeys ops).restrict (eval θ))) := by
  induction ops with
  | nil => rfl
  | cons o rest ih =>
    cases o with
    | resample => cases hafter
    | eval u =>
      simp only [afterCurrentEpoch_eval] at hafter
      simp only [evalOpsFromSeed, ih hafter, _root_.PMF.pure_map, currentEpochPrefixTranscript,
        currentEpochKeys_eval, restrict_comp_inclusion]
      rfl

/-- When `afterCurrentEpoch ops = some rest`, `evalOpsFromSeed` decomposes into the
deterministic current-epoch prefix `currentEpochPrefixTranscript` followed by `.resample` and an
independent draw from `evalOps seedLaw eval rest`. -/
theorem evalOpsFromSeed_eq_of_afterCurrentEpoch_eq_some {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m) (θ : Seed)
    {ops rest : List (Op U)} (hafter : afterCurrentEpoch ops = some rest) :
    evalOpsFromSeed seedLaw eval θ ops =
      (evalOps seedLaw eval rest).map (fun tailOut =>
        currentEpochPrefixTranscript m ops ((currentEpochKeys ops).restrict (eval θ)) ++
          (⟨.resample, PUnit.unit⟩ :: tailOut)) := by
  induction ops with
  | nil => cases hafter
  | cons o tail ih =>
    cases o with
    | resample =>
      injection hafter with hEq
      subst hEq
      simp [evalOpsFromSeed, evalOps, currentEpochPrefixTranscript, PMF.map_bind]
    | eval u =>
      simp only [afterCurrentEpoch_eval] at hafter
      simp only [evalOpsFromSeed, ih hafter, PMF.map_comp, Function.comp_def,
        currentEpochPrefixTranscript, currentEpochKeys_eval, restrict_comp_inclusion,
        List.cons_append]
      rfl

/-- On a single-epoch sequence (`afterCurrentEpoch ops = none`), `evalOps` is the pushforward of
the restricted seed distribution `seedLaw.map (fun θ => (currentEpochKeys ops).restrict (eval θ))`
under `currentEpochPrefixTranscript m ops`. -/
theorem evalOps_eq_of_afterCurrentEpoch_eq_none {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m)
    {ops : List (Op U)} (hafter : afterCurrentEpoch ops = none) :
    evalOps seedLaw eval ops =
      (seedLaw.map (fun θ => (currentEpochKeys ops).restrict (eval θ))).map
        (currentEpochPrefixTranscript m ops) := by
  rw [PMF.map_comp]
  simp only [evalOps, evalOpsFromSeed_eq_of_afterCurrentEpoch_eq_none seedLaw eval _ hafter,
    Function.comp_def, _root_.PMF.map]

/-- When `afterCurrentEpoch ops = some rest`, `evalOps` decomposes into the current-epoch prefix
distribution bound to an independent tail draw `evalOps seedLaw eval rest`. -/
theorem evalOps_eq_of_afterCurrentEpoch_eq_some {Seed : Type u} {U m : ℕ}
    (seedLaw : PMF Seed) (eval : Seed → Fin U → Fin m)
    {ops rest : List (Op U)} (hafter : afterCurrentEpoch ops = some rest) :
    evalOps seedLaw eval ops =
      ((seedLaw.map (fun θ => (currentEpochKeys ops).restrict (eval θ))).map
        (currentEpochPrefixTranscript m ops)).bind (fun pref =>
          (evalOps seedLaw eval rest).map (fun tailOut =>
            pref ++ (⟨.resample, PUnit.unit⟩ :: tailOut))) := by
  simp only [evalOps, evalOpsFromSeed_eq_of_afterCurrentEpoch_eq_some seedLaw eval _ hafter,
    PMF.bind_map, Function.comp_def]

/-- **Fundamental bridge theorem for exact `k`-wise independent hash families**:
if `eval : Seed → Fin U → Fin m` satisfies `IsKWiseIndependentHash k eval`, then on any oblivious
operation sequence `ops` querying at most `k` distinct keys per epoch (`BoundedEpochKeys k ops`),
`evalOps (PMF.uniformOfFintype Seed) eval ops` equals `idealTranscriptPMF m ops` and
therefore satisfies `(kWiseSpec k U m).Contract ops`. -/
theorem kWiseSpec_contract_evalOps {Seed : Type u} {k U m : ℕ}
    [Fintype Seed] [Nonempty Seed] [NeZero m] {eval : Seed → Fin U → Fin m}
    (hk : Probability.IsKWiseIndependentHash k eval)
    {ops : List (Op U)} (hv : BoundedEpochKeys k ops) :
    (kWiseSpec k U m).Contract ops
      (evalOps (PMF.uniformOfFintype Seed) eval ops) := by
  change evalOps (PMF.uniformOfFintype Seed) eval ops = idealTranscriptPMF m ops
  have hcard : (currentEpochKeys ops).card ≤ k := hv.card_currentEpochKeys_le
  have hrest_unif := uniformOfFintype_map_restrict_eq hk hcard
  rw [idealTranscriptPMF]
  cases hafter : afterCurrentEpoch ops with
  | none =>
    rw [evalOps_eq_of_afterCurrentEpoch_eq_none _ _ hafter, hrest_unif]
  | some rest =>
    have ih := kWiseSpec_contract_evalOps hk (hv.of_afterCurrentEpoch_eq_some hafter)
    change evalOps (PMF.uniformOfFintype Seed) eval rest = idealTranscriptPMF m rest at ih
    rw [evalOps_eq_of_afterCurrentEpoch_eq_some _ _ hafter, hrest_unif, ih]
termination_by ops.length
decreasing_by exact length_lt_of_afterCurrentEpoch_eq_some hafter

/-- Every distribution satisfying `(kWiseSpec k U m).Contract ops` also satisfies
`(whpKWiseSpec k U m δ).Contract ops` for any `δ : ℝ≥0∞`. -/
theorem whpKWiseSpec_contract_of_kWiseSpec {k U m : ℕ} [NeZero m] (δ : ℝ≥0∞)
    {ops : List (Op U)} {μ : PMF (List (Label U m))}
    (hmatch : ∀ out ∈ μ.support, TranscriptMatches ops out)
    (hk : (kWiseSpec k U m).Contract ops μ) :
    (whpKWiseSpec k U m δ).Contract ops μ := by
  refine ⟨hmatch, ?_⟩
  change μ = idealTranscriptPMF m ops at hk
  rw [hk]
  exact (CoupledWithin.refl _).mono (by simp)

private theorem coupledWithin_evalOps_prod {TopSeed : Type u} {BotSeed : Type v}
    {k U m : ℕ} [Fintype TopSeed] [Nonempty TopSeed] [DecidableEq TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    [NeZero m] (eval : TopSeed → BotSeed → Fin U → Fin m)
    (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop, Probability.IsKWiseIndependentHash k (eval α))
    {ops : List (Op U)} (hv : BoundedEpochKeys k ops) :
    CoupledWithin
      (evalOps (PMF.uniformOfFintype (TopSeed × BotSeed)) (fun p => eval p.1 p.2) ops)
      (idealTranscriptPMF m ops)
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
  rw [idealTranscriptPMF]
  cases hafter : afterCurrentEpoch ops with
  | none =>
    rw [evalOps_eq_of_afterCurrentEpoch_eq_none _ _ hafter]
    have hepoch_cnt : (epochCount ops : ℝ≥0∞) * δ = δ := by
      simp [epochCount, resampleCount_eq_zero_of_afterCurrentEpoch_eq_none hafter]
    rw [hepoch_cnt]
    exact hepoch
  | some rest =>
    rw [evalOps_eq_of_afterCurrentEpoch_eq_some _ _ hafter]
    have ih := coupledWithin_evalOps_prod eval GoodTop hgood
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
`(whpKWiseSpec k U m δ).Contract ops` with bad-seed measure
`δ = (#(Finset.univ \ GoodTop) : ℝ≥0∞) / Fintype.card TopSeed`. -/
theorem whpKWiseSpec_contract_evalOps_prod {TopSeed : Type u} {BotSeed : Type v}
    {k U m : ℕ} [Fintype TopSeed] [Nonempty TopSeed] [DecidableEq TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    [NeZero m] (eval : TopSeed → BotSeed → Fin U → Fin m)
    (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop, Probability.IsKWiseIndependentHash k (eval α))
    {ops : List (Op U)} (hv : BoundedEpochKeys k ops) :
    (whpKWiseSpec k U m
      (((Finset.univ \ GoodTop).card : ℝ≥0∞) / Fintype.card TopSeed)).Contract ops
      (evalOps (PMF.uniformOfFintype (TopSeed × BotSeed)) (fun p => eval p.1 p.2) ops) :=
  ⟨transcriptMatches_of_mem_support_evalOps _ _ ops,
    coupledWithin_evalOps_prod eval GoodTop hgood hv⟩

/-- Relabelling the seed type along an equivalence `e : Seed₁ ≃ Seed₂` transports
`evalOpsFromSeed` by pushing forward `seedLaw` along `e` and pulling back `eval` along `e.symm`. -/
theorem evalOpsFromSeed_map_equiv {Seed₁ : Type u} {Seed₂ : Type v} {U m : ℕ}
    (seedLaw : PMF Seed₁) (eval : Seed₁ → Fin U → Fin m)
    (e : Seed₁ ≃ Seed₂) (θ : Seed₁) (ops : List (Op U)) :
    evalOpsFromSeed seedLaw eval θ ops =
      evalOpsFromSeed (seedLaw.map e) (fun s => eval (e.symm s)) (e θ) ops := by
  induction ops generalizing θ with
  | nil => rfl
  | cons o rest ih =>
    cases o with
    | eval u =>
      simp [evalOpsFromSeed, ih θ]
    | resample =>
      dsimp only [evalOpsFromSeed]
      rw [PMF.bind_map]
      refine congrArg (seedLaw.bind ·) (funext fun θ' => ?_)
      dsimp only [Function.comp_def]
      rw [ih θ']

/-- Transport `whpKWiseSpec_contract_evalOps_prod` along a seed equivalence
`e : Seed ≃ (TopSeed × BotSeed)`. -/
theorem whpKWiseSpec_contract_evalOps_equiv {Seed : Type w}
    {TopSeed : Type u} {BotSeed : Type v}
    {k U m : ℕ} [Fintype Seed] [Nonempty Seed]
    [Fintype TopSeed] [Nonempty TopSeed] [DecidableEq TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    [NeZero m] (eval : Seed → Fin U → Fin m)
    (e : Seed ≃ (TopSeed × BotSeed))
    (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop, Probability.IsKWiseIndependentHash k (fun β => eval (e.symm (α, β))))
    {ops : List (Op U)} (hv : BoundedEpochKeys k ops) :
    (whpKWiseSpec k U m
      (((Finset.univ \ GoodTop).card : ℝ≥0∞) / Fintype.card TopSeed)).Contract ops
      (evalOps (PMF.uniformOfFintype Seed) eval ops) := by
  have hlaw : (PMF.uniformOfFintype Seed).map e = PMF.uniformOfFintype (TopSeed × BotSeed) :=
    Cslib.Probability.PMF.uniformOfFintype_map_equiv e
  have heq :
      evalOps (PMF.uniformOfFintype Seed) eval ops =
        evalOps (PMF.uniformOfFintype (TopSeed × BotSeed)) (fun p => eval (e.symm p)) ops := by
    rw [← hlaw]
    dsimp only [evalOps]
    rw [PMF.bind_map]
    refine congrArg ((PMF.uniformOfFintype Seed).bind ·) (funext fun θ₀ => ?_)
    exact evalOpsFromSeed_map_equiv _ _ e θ₀ ops
  rw [heq]
  exact whpKWiseSpec_contract_evalOps_prod (fun α β => eval (e.symm (α, β)))
    GoodTop hgood hv

end Cslib.DataStructure.HashFamily
