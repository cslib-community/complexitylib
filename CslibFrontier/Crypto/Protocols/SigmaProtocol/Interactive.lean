/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Efficient
public import CslibFrontier.Computability.Interactive.Plain
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Composition
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Sigma protocols as public-coin interactive reductions

Every Sigma protocol `P : SigmaProtocol X Y T C Z` with a nonempty finite challenge space `C`
embeds as a three-round public-coin interactive reduction in the plain model
(`CslibFrontier.Computability.Interactive`), reducing the swapped relation `Function.swap R : Y → X
→
Prop` to `Interactive.Accept`:

1. The prover sends a commitment `t : T` with full oracle access (`OracleInterface.full T`).
2. The verifier samples a uniform challenge `c : C` via `ProbComp.uniform C`.
3. The prover sends a response `z : Z` with full oracle access (`OracleInterface.full Z`).
4. The verifier reads `t` and `z` and accepts (`some ()`) iff `P.verify y t c z = true`.

Because `SigmaProtocol.commit` is a semantic `PMF` while `Interactive.Reduction` requires an
explicit `ProbOracleComp` strategy tree, the honest prover takes a `ProbComp` commitment sampler
`sampleCommit : X → Y → ProbComp (T × P.State)` certified by `P.CommitRealizedBy sampleCommit`.
The verifier (`P.toInteractiveVerifier`) needs no sampler beyond `ProbComp.uniform C`.

This module proves that the Sigma-protocol security notions transfer across the bridge:

* **Completeness** (`Complete.toInteractiveReduction`): `P.Complete R` and
  `P.CommitRealizedBy sampleCommit` imply perfect completeness
  `(P.toInteractiveReduction sampleCommit).Complete World.plain (Function.swap R) Accept 0`.
* **Round-by-round soundness and soundness** (`SpecialSoundness.rbrSound`,
  `SpecialSoundness.sound`): `P.SpecialSoundness R extract` implies round-by-round soundness
  `P.toInteractiveVerifier.RbrSound (language (Function.swap R)) langOut (1 / |C|, ())` and
  plain-model soundness with error `1 / |C|`. At the commitment prefix `some (t, none)`, a prefix
  is doomed unless two distinct challenges have accepting responses; by 2-special soundness, no
  false statement can reach a non-doomed commitment, and from a doomed commitment at most one
  challenge in `C` has an accepting response.
* **Straight-line knowledge soundness** (`SpecialSoundness.knowledgeSound_of_extractor`,
  `SpecialSoundness.knowledgeSound`, `SpecialSoundness.efficientKnowledgeSound`): any straight-line
  extractor that succeeds on accepting transcripts of true statements is knowledge sound with error
  `1 / |C|`; in particular, the classical witness chooser `P.witnessChooser R` gives
  `KnowledgeSound`, and a polynomial-time straight-line extractor gives
  `Verifier.EfficientKnowledgeSound`.
* **Honest-verifier zero knowledge** (`SpecialHVZK.hvzk`, `SpecialHVZK.hvzk_zero`,
  `EfficientSpecialHVZK.efficientHVZK`): `P.SpecialHVZK R simulate` and a `ProbComp` simulator
  `simComp` within `ε` of `simulate` give `(P.toInteractiveReduction sampleCommit).HVZK
  (Function.swap R) (P.interactiveSim simComp) ε` (`0` when `simComp` is exact); combined with a
  strict PPT challenge sampler for `C i`, `EfficientSpecialHVZK` transfers to
  `Reduction.EfficientHVZK`.
* **Protocol instances**: commitment and simulator realizations for `SigmaProtocol.linear`,
  `SigmaProtocol.schnorr`, `SigmaProtocol.andProof` and `SigmaProtocol.orProof`.

## Main definitions

* `SigmaProtocol.sigmaSpec`, `SigmaProtocol.interactiveSpec`: the 3-round public-coin
  specification `[.prover T (OracleInterface.full T), .verifier C,
  .prover Z (OracleInterface.full Z)]`.
* `SigmaProtocol.interactiveTranscript`, `SigmaProtocol.transcriptOfConversation`,
  `SigmaProtocol.commitOfTranscript`, `SigmaProtocol.challengeOfTranscript`,
  `SigmaProtocol.responseOfTranscript`, `SigmaProtocol.conversationOfTranscript`: transcript
  constructors and projections.
* `SigmaProtocol.CommitRealizedBy`: `ProbComp` realization of `P.commit`.
* `SigmaProtocol.toInteractiveVerifier`, `SigmaProtocol.toInteractiveProver`,
  `SigmaProtocol.toInteractiveReduction`: the interactive verifier, prover and reduction.
* `SigmaProtocol.rbrState`: the round-by-round state function on prefixes of `P.interactiveSpec`.
* `SigmaProtocol.witnessChooser`: the classical straight-line witness chooser.
* `SigmaProtocol.interactiveSim`: the interactive transcript simulator induced by a
  challenge-conditioned simulator.
* `SigmaProtocol.Encoding.toInteractiveEncoding`: interactive word encodings induced by a
  `SigmaProtocol.Encoding`.

## Main results

* `SigmaProtocol.eval_toInteractiveReduction_run`,
  `SigmaProtocol.map_fst_eval_toInteractiveReduction_run`: the plain-model execution and transcript
  laws of `P.toInteractiveReduction`.
* `SigmaProtocol.Complete.toInteractiveReduction`: completeness transfer.
* `SigmaProtocol.SpecialSoundness.rbrSound`, `SigmaProtocol.SpecialSoundness.sound`:
  round-by-round soundness and plain-model soundness with error `1 / |C|`.
* `SigmaProtocol.SpecialSoundness.knowledgeSound_of_extractor`,
  `SigmaProtocol.SpecialSoundness.knowledgeSound`,
  `SigmaProtocol.SpecialSoundness.efficientKnowledgeSound`: knowledge-soundness transfer.
* `SigmaProtocol.SpecialHVZK.hvzk`, `SigmaProtocol.SpecialHVZK.hvzk_zero`,
  `SigmaProtocol.EfficientSpecialHVZK.efficientHVZK`: HVZK and efficient HVZK transfer.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Interactive Interactive.Spec Turing.MultiTapeTM
open scoped ENNReal

variable {X Y T C Z : Type}

/-! ### Specification and transcripts -/

/-- The three-round public-coin specification of a Sigma protocol with commitments in `T`,
challenges in `C` and responses in `Z`: prover commitment, verifier challenge, prover response. -/
@[reducible] def sigmaSpec (T C Z : Type) : Interactive.Spec :=
  [.prover T (OracleInterface.full T), .verifier C, .prover Z (OracleInterface.full Z)]

/-- The interactive specification of `P`. -/
abbrev interactiveSpec (_ : SigmaProtocol X Y T C Z) : Interactive.Spec := sigmaSpec T C Z

/-- Package a commitment `t`, challenge `c` and response `z` as a transcript of
`P.interactiveSpec`. -/
def interactiveTranscript (P : SigmaProtocol X Y T C Z) (t : T) (c : C) (z : Z) :
    Transcript P.interactiveSpec :=
  (t, c, z, ())

/-- Package a conversation triple `(t, c, z)` as a transcript of `P.interactiveSpec`. -/
def transcriptOfConversation (P : SigmaProtocol X Y T C Z) : T × C × Z →
    Transcript P.interactiveSpec :=
  fun (t, c, z) => (t, c, z, ())

/-- The commitment `t` of an interactive transcript. -/
def commitOfTranscript (P : SigmaProtocol X Y T C Z) : Transcript P.interactiveSpec → T :=
  fun (t, _, _, _) => t

/-- The challenge `c` of an interactive transcript. -/
def challengeOfTranscript (P : SigmaProtocol X Y T C Z) : Transcript P.interactiveSpec → C :=
  fun (_, c, _, _) => c

/-- The response `z` of an interactive transcript. -/
def responseOfTranscript (P : SigmaProtocol X Y T C Z) : Transcript P.interactiveSpec → Z :=
  fun (_, _, z, _) => z

/-- View an interactive transcript as a Sigma-protocol conversation `(t, c, z)`. -/
def conversationOfTranscript (P : SigmaProtocol X Y T C Z) :
    Transcript P.interactiveSpec → T × C × Z :=
  fun (t, c, z, _) => (t, c, z)

variable (P : SigmaProtocol X Y T C Z)

@[simp] theorem commitOfTranscript_interactiveTranscript (t : T) (c : C) (z : Z) :
    P.commitOfTranscript (P.interactiveTranscript t c z) = t := rfl

@[simp] theorem challengeOfTranscript_interactiveTranscript (t : T) (c : C) (z : Z) :
    P.challengeOfTranscript (P.interactiveTranscript t c z) = c := rfl

@[simp] theorem responseOfTranscript_interactiveTranscript (t : T) (c : C) (z : Z) :
    P.responseOfTranscript (P.interactiveTranscript t c z) = z := rfl

@[simp] theorem conversationOfTranscript_interactiveTranscript (t : T) (c : C) (z : Z) :
    P.conversationOfTranscript (P.interactiveTranscript t c z) = (t, c, z) := rfl

@[simp] theorem commitOfTranscript_transcriptOfConversation (t : T) (c : C) (z : Z) :
    P.commitOfTranscript (P.transcriptOfConversation (t, c, z)) = t := rfl

@[simp] theorem challengeOfTranscript_transcriptOfConversation (t : T) (c : C) (z : Z) :
    P.challengeOfTranscript (P.transcriptOfConversation (t, c, z)) = c := rfl

@[simp] theorem responseOfTranscript_transcriptOfConversation (t : T) (c : C) (z : Z) :
    P.responseOfTranscript (P.transcriptOfConversation (t, c, z)) = z := rfl

@[simp] theorem conversationOfTranscript_transcriptOfConversation (tcz : T × C × Z) :
    P.conversationOfTranscript (P.transcriptOfConversation tcz) = tcz := rfl

@[simp] theorem transcriptOfConversation_conversationOfTranscript
    (τ : Transcript P.interactiveSpec) :
    P.transcriptOfConversation (P.conversationOfTranscript τ) = τ := rfl

@[simp] theorem interactiveTranscript_projections (τ : Transcript P.interactiveSpec) :
    P.interactiveTranscript (P.commitOfTranscript τ) (P.challengeOfTranscript τ)
      (P.responseOfTranscript τ) = τ := rfl

theorem transcriptOfConversation_injective :
    Function.Injective P.transcriptOfConversation :=
  Function.LeftInverse.injective (conversationOfTranscript_transcriptOfConversation P)

theorem conversationOfTranscript_injective :
    Function.Injective P.conversationOfTranscript :=
  Function.LeftInverse.injective (transcriptOfConversation_conversationOfTranscript P)

/-! ### Interactive verifier, prover and reduction -/

/-- `sampleCommit` realizes `P.commit` as a `ProbComp` program. -/
def CommitRealizedBy (sampleCommit : X → Y → ProbComp (T × P.State)) : Prop :=
  ∀ x y, ProbComp.eval (sampleCommit x y) = P.commit x y

/-- The honest prover strategy of `P` in the plain model, using `sampleCommit` to sample the
commitment and private prover state, then answering the verifier's challenge with `P.respond`. -/
def toInteractiveProver (sampleCommit : X → Y → ProbComp (T × P.State)) (y : Y) (x : X) :
    ProbOracleComp OracleSpec.empty
      (ProverStrategy (ProbOracleComp OracleSpec.empty) P.interactiveSpec (Unit × Unit)) :=
  pure (show ProbOracleComp OracleSpec.empty
      (T × (C → ProbOracleComp OracleSpec.empty
        (ProbOracleComp OracleSpec.empty (Z × (Unit × Unit))))) from do
    let ts ← ProbOracleComp.sample (sampleCommit x y)
    return (ts.1, fun c =>
      pure (show ProbOracleComp OracleSpec.empty (Z × (Unit × Unit)) from
        pure (P.respond x y ts.2 c, ((), ())))))

variable [Fintype C] [Nonempty C]

/-- The public-coin interactive verifier of `P` in the plain model: sample a uniform challenge
`c : C`, read the commitment `t : T` and response `z : Z`, and output `some ()` iff
`P.verify y t c z = true`. -/
noncomputable def toInteractiveVerifier :
    Interactive.Verifier OracleSpec.empty P.interactiveSpec Y Unit where
  samplers := (ProbComp.uniform C, ())
  decide y ch := do
    let t : T ←
      OracleComp.query (spec := OracleSpec.empty ⊕ₒ msgSpec P.interactiveSpec) (.inr (.inl ()))
    let z : Z ←
      OracleComp.query (spec := OracleSpec.empty ⊕ₒ msgSpec P.interactiveSpec)
        (.inr (.inr (.inl ())))
    return if P.verify y t ch.1 z then some () else none

/-- Embed `P` as a three-round public-coin interactive reduction in the plain model, reducing
`Function.swap R : Y → X → Prop` to `Interactive.Accept`. -/
noncomputable def toInteractiveReduction (sampleCommit : X → Y → ProbComp (T × P.State)) :
    Interactive.Reduction OracleSpec.empty OracleSpec.empty P.interactiveSpec Y X Unit Unit where
  prover := P.toInteractiveProver sampleCommit
  verifier := P.toInteractiveVerifier

@[simp] theorem toInteractiveVerifier_outputOn (y : Y) (τ : Transcript P.interactiveSpec) :
    P.toInteractiveVerifier.outputOn y τ =
      if P.verify y (P.commitOfTranscript τ) (P.challengeOfTranscript τ)
        (P.responseOfTranscript τ) then some () else none := rfl

theorem toInteractiveVerifier_outputOn_eq_some_iff (y : Y)
    (τ : Transcript P.interactiveSpec) (u : Unit) :
    P.toInteractiveVerifier.outputOn y τ = some u ↔
      P.Accepts y (P.commitOfTranscript τ) (P.challengeOfTranscript τ)
        (P.responseOfTranscript τ) := by
  cases u
  simp [Accepts]

/-- In the plain model, running `P.toInteractiveProver sampleCommit` against the verifier's uniform
challenge sampler produces the conversation law `P.conversation x y`. -/
theorem plainLaw_toInteractiveProver_runStrategy
    {sampleCommit : X → Y → ProbComp (T × P.State)}
    (hcommit : P.CommitRealizedBy sampleCommit) (y : Y) (x : X) :
    plainLaw (P.toInteractiveProver sampleCommit y x >>=
        runStrategy P.interactiveSpec P.toInteractiveVerifier.samplers) =
      (P.conversation x y).map fun tcz => (P.transcriptOfConversation tcz, ((), ())) := by
  simp only [pmf_norm, toInteractiveProver, toInteractiveVerifier, runStrategy, plainLaw_bind,
    plainLaw_sample, plainLaw_pure, ProbComp.eval_uniform, hcommit x y, conversation,
    transcriptOfConversation]

/-- The full plain-model execution law of `P.toInteractiveReduction sampleCommit`. -/
theorem eval_toInteractiveReduction_run
    {sampleCommit : X → Y → ProbComp (T × P.State)}
    (hcommit : P.CommitRealizedBy sampleCommit) (y : Y) (x : X) :
    World.plain.eval ((P.toInteractiveReduction sampleCommit).run y x) =
      (P.conversation x y).map fun (t, c, z) =>
        (P.transcriptOfConversation (t, c, z),
          if P.verify y t c z then some () else none, ((), ())) := by
  rw [Interactive.Reduction.run, toInteractiveReduction, World.plain_eval_execute,
    P.plainLaw_toInteractiveProver_runStrategy hcommit y x, PMF.map_comp]
  rfl

/-- The transcript marginal of an honest plain-model run of `P.toInteractiveReduction` is
`(P.conversation x y).map P.transcriptOfConversation`. -/
theorem map_fst_eval_toInteractiveReduction_run
    {sampleCommit : X → Y → ProbComp (T × P.State)}
    (hcommit : P.CommitRealizedBy sampleCommit) (y : Y) (x : X) :
    (World.plain.eval ((P.toInteractiveReduction sampleCommit).run y x)).map Prod.fst =
      (P.conversation x y).map P.transcriptOfConversation := by
  rw [P.eval_toInteractiveReduction_run hcommit y x, PMF.map_comp]
  rfl

/-! ### Completeness transfer -/

variable {P}

/-- **Completeness transfer**: a complete Sigma protocol with a realized commitment sampler gives a
perfectly complete interactive reduction to `Interactive.Accept` in the plain model. -/
theorem Complete.toInteractiveReduction {R : X → Y → Prop}
    {sampleCommit : X → Y → ProbComp (T × P.State)}
    (h : P.Complete R) (hcommit : P.CommitRealizedBy sampleCommit) :
    (P.toInteractiveReduction sampleCommit).Complete World.plain (Function.swap R) Accept 0 := by
  intro y x hyx
  rw [P.eval_toInteractiveReduction_run hcommit y x, PMF.toOuterMeasure_map_apply,
    nonpos_iff_eq_zero, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  rintro ⟨t, c, z⟩ htcz hfail
  have hacc : P.verify y t c z = true :=
    h.accepts_of_mem_support_conversation hyx htcz
  exact hfail ⟨by simp [hacc], trivial⟩

/-! ### Round-by-round soundness and soundness transfer -/

/-- The round-by-round state predicate for `P` on transcript prefixes of `P.interactiveSpec`:
* at the empty prefix `none`, some commitment has accepting responses for two distinct challenges;
* after commitment `t` (`some (t, none)`), `t` has accepting responses for two distinct challenges;
* after challenge `c` (`some (t, some (c, none))`), `(t, c)` has an accepting response `z`;
* on a complete transcript `some (t, some (c, some (z, ())))`, `P.Accepts y t c z` holds. -/
def rbrState (P : SigmaProtocol X Y T C Z) (y : Y) : Prefix P.interactiveSpec → Prop
  | none => ∃ t c c', c ≠ c' ∧ (∃ z, P.Accepts y t c z) ∧ (∃ z', P.Accepts y t c' z')
  | some (t, none) => ∃ c c', c ≠ c' ∧ (∃ z, P.Accepts y t c z) ∧ (∃ z', P.Accepts y t c' z')
  | some (t, some (c, none)) => ∃ z, P.Accepts y t c z
  | some (t, some (c, some (z, ()))) => P.Accepts y t c z

omit [Fintype C] [Nonempty C] in
theorem not_rbrState_empty_of_specialSoundness {W : Type} {R : W → Y → Prop}
    {extract : Y → T → C → Z → C → Z → W}
    (h : P.SpecialSoundness R extract) {y : Y} (hy : y ∉ language (Function.swap R)) :
    ¬ P.rbrState y (Prefix.empty P.interactiveSpec) := by
  rintro ⟨t, c, c', hc, ⟨z, hz⟩, ⟨z', hz'⟩⟩
  exact hy (h.exists_witness hc hz hz')

/-- `P.rbrState y` satisfies `RbrFrom` with challenge error `1 / Fintype.card C`. -/
theorem rbrFrom_rbrState (y : Y) (langOut : Set Unit) :
    RbrFrom P.interactiveSpec P.toInteractiveVerifier.samplers
      (1 / (Fintype.card C : ℝ≥0∞), ()) (P.rbrState y)
      fun τ => ∃ x' ∈ langOut, P.toInteractiveVerifier.outputOn y τ = some x' := by
  refine ⟨fun h0 t ht => h0 ⟨t, ht⟩, fun t => ⟨?_, fun c => ⟨fun h2 z hz => h2 ⟨z, hz⟩, ?_⟩⟩⟩
  · intro h1
    classical
    let E : Set C := {c : C | ∃ z, P.Accepts y t c z}
    change (ProbComp.eval (ProbComp.uniform C)).toOuterMeasure E ≤ 1 / (Fintype.card C : ℝ≥0∞)
    rw [ProbComp.eval_uniform, Probability.PMF.toOuterMeasure_uniformOfFintype]
    have hcard : (Finset.univ.filter (· ∈ E)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun c₁ hc₁ c₂ hc₂ => ?_
      by_contra hne
      exact h1 ⟨c₁, c₂, hne, (Finset.mem_filter.mp hc₁).2, (Finset.mem_filter.mp hc₂).2⟩
    calc ((Finset.univ.filter (· ∈ E)).card : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹
      _ ≤ (1 : ℕ) * (Fintype.card C : ℝ≥0∞)⁻¹ := by
          gcongr
      _ = 1 / (Fintype.card C : ℝ≥0∞) := by simp [one_div]
  · intro z h3 ⟨x', _, hx'⟩
    exact h3 ((P.toInteractiveVerifier_outputOn_eq_some_iff y (t, c, z, ()) x').mp hx')

/-- **Round-by-round soundness transfer**: 2-special soundness of `P` implies round-by-round
soundness of `P.toInteractiveVerifier` with challenge error `1 / |C|`. -/
theorem SpecialSoundness.rbrSound {W : Type} {R : W → Y → Prop}
    {extract : Y → T → C → Z → C → Z → W}
    (h : P.SpecialSoundness R extract) (langOut : Set Unit := Set.univ) :
    P.toInteractiveVerifier.RbrSound (language (Function.swap R)) langOut
      (1 / (Fintype.card C : ℝ≥0∞), ()) :=
  ⟨P.rbrState, fun _ hy => not_rbrState_empty_of_specialSoundness h hy,
    fun y => rbrFrom_rbrState y langOut⟩

/-- **Soundness transfer**: 2-special soundness of `P` implies plain-model soundness of
`P.toInteractiveVerifier` against arbitrary unbounded provers with error `1 / |C|`. -/
theorem SpecialSoundness.sound {W : Type} {R : W → Y → Prop}
    {extract : Y → T → C → Z → C → Z → W}
    (h : P.SpecialSoundness R extract) (langOut : Set Unit := Set.univ) :
    P.toInteractiveVerifier.Sound World.plain (language (Function.swap R)) langOut
      (1 / (Fintype.card C : ℝ≥0∞)) := by
  simpa only [PerChallenge.sum, interactiveSpec, sigmaSpec, add_zero] using
    (SpecialSoundness.rbrSound h langOut).sound

/-! ### Knowledge soundness and efficient knowledge soundness transfer -/

/-- Any straight-line extractor `E` that recovers a valid witness from accepting transcripts on
statements in `language (Function.swap R)` makes `P.toInteractiveVerifier` knowledge sound with
error `1 / |C|`. -/
theorem SpecialSoundness.knowledgeSound_of_extractor {W : Type} {R : W → Y → Prop}
    {extract : Y → T → C → Z → C → Z → W}
    (h : P.SpecialSoundness R extract)
    (E : Y → Transcript P.interactiveSpec → Unit → W)
    (hE : ∀ y τ, y ∈ language (Function.swap R) →
      P.Accepts y (P.commitOfTranscript τ) (P.challengeOfTranscript τ)
        (P.responseOfTranscript τ) →
      R (E y τ ()) y) :
    P.toInteractiveVerifier.KnowledgeSound (Function.swap R) Accept E
      (1 / (Fintype.card C : ℝ≥0∞)) := by
  intro y strat
  by_cases hy : y ∈ language (Function.swap R)
  · refine le_of_eq_of_le ?_ zero_le
    rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    rintro ⟨τ, ⟨⟩⟩ _ ⟨⟨⟨⟩, hacc, -⟩, hnot⟩
    have hacc' := (P.toInteractiveVerifier_outputOn_eq_some_iff y τ ()).mp hacc
    exact hnot (hE y τ hy hacc')
  · refine (MeasureTheory.measure_mono ?_).trans (SpecialSoundness.sound h Set.univ y hy Unit strat)
    rintro r ⟨⟨x', hx', -⟩, -⟩
    exact ⟨x', Set.mem_univ x', hx'⟩

/-- The classical witness chooser on transcripts, picking a witness for `y` whenever one exists. -/
noncomputable def witnessChooser (P : SigmaProtocol X Y T C Z) {W : Type} [Nonempty W]
    (R : W → Y → Prop) :
    Y → Transcript P.interactiveSpec → Unit → W :=
  fun y _ _ => Classical.epsilon (fun w => R w y)

/-- **Knowledge soundness transfer**: 2-special soundness of `P` implies straight-line
`KnowledgeSound` in the plain model with error `1 / |C|` for `P.witnessChooser R`. -/
theorem SpecialSoundness.knowledgeSound {W : Type} [Nonempty W] {R : W → Y → Prop}
    {extract : Y → T → C → Z → C → Z → W}
    (h : P.SpecialSoundness R extract) :
    P.toInteractiveVerifier.KnowledgeSound (Function.swap R) Accept (P.witnessChooser R)
      (1 / (Fintype.card C : ℝ≥0∞)) :=
  SpecialSoundness.knowledgeSound_of_extractor h (P.witnessChooser R) fun _ _ hy _ =>
    Classical.epsilon_spec hy

/-! ### Honest-verifier zero knowledge transfer -/

/-- The interactive transcript simulator induced by a challenge-conditioned `ProbComp` simulator
`simComp`: sample a uniform challenge `c : C`, sample `(t, z) ← simComp y c`, and return
`(t, c, z, ())`. -/
noncomputable def interactiveSim (P : SigmaProtocol X Y T C Z)
    (simComp : Y → C → ProbComp (T × Z)) (y : Y) :
    ProbComp (Transcript P.interactiveSpec) := do
  let c ← ProbComp.uniform C
  let tz ← simComp y c
  return P.interactiveTranscript tz.1 c tz.2

theorem eval_interactiveSim (P : SigmaProtocol X Y T C Z)
    (simComp : Y → C → ProbComp (T × Z)) (y : Y) :
    ProbComp.eval (P.interactiveSim simComp y) =
      (PMF.uniformOfFintype C).bind fun c =>
        (ProbComp.eval (simComp y c)).map fun tz => P.interactiveTranscript tz.1 c tz.2 := by
  simp only [interactiveSim, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rfl

/-- **HVZK transfer**: if `P` is special HVZK with `simulate`, `sampleCommit` realizes `P.commit`,
and `simComp y c` is within statistical distance `ε` of `simulate y c` at every challenge, then
`P.toInteractiveReduction sampleCommit` is `ε`-HVZK with `P.interactiveSim simComp`. -/
theorem SpecialHVZK.hvzk {R : X → Y → Prop} {simulate : Y → C → PMF (T × Z)}
    {sampleCommit : X → Y → ProbComp (T × P.State)}
    {simComp : Y → C → ProbComp (T × Z)} {ε : ℝ≥0∞}
    (h : P.SpecialHVZK R simulate) (hcommit : P.CommitRealizedBy sampleCommit)
    (hsim : ∀ y c, CloseTo (simulate y c) (ProbComp.eval (simComp y c)) ε) :
    (P.toInteractiveReduction sampleCommit).HVZK (Function.swap R)
      (P.interactiveSim simComp) ε := by
  intro y x hyx
  rw [P.map_fst_eval_toInteractiveReduction_run hcommit y x, h.conversation_eq hyx,
    P.eval_interactiveSim simComp y]
  simp only [pmf_norm, transcriptOfConversation, interactiveTranscript]
  exact CloseTo.bind_right (PMF.uniformOfFintype C) fun c _ =>
    (hsim y c).map fun tz => (tz.1, c, tz.2, ())

/-- **Perfect HVZK transfer**: if `P` is special HVZK with `simulate`, `sampleCommit` realizes
`P.commit`, and `simComp` evaluates to `simulate` at every challenge, then
`P.toInteractiveReduction sampleCommit` is perfectly HVZK (`ε = 0`). -/
theorem SpecialHVZK.hvzk_zero {R : X → Y → Prop} {simulate : Y → C → PMF (T × Z)}
    {sampleCommit : X → Y → ProbComp (T × P.State)}
    {simComp : Y → C → ProbComp (T × Z)}
    (h : P.SpecialHVZK R simulate) (hcommit : P.CommitRealizedBy sampleCommit)
    (hsim : ∀ y c, ProbComp.eval (simComp y c) = simulate y c) :
    (P.toInteractiveReduction sampleCommit).HVZK (Function.swap R)
      (P.interactiveSim simComp) 0 :=
  h.hvzk hcommit fun y c => by rw [hsim y c]; exact CloseTo.refl _

/-! ### Indexed families: encodings, efficient knowledge soundness and efficient HVZK -/

section Family

variable {I : Type} {XF YF TF CF ZF WF : I → Type}
  (PF : ∀ i, SigmaProtocol (XF i) (YF i) (TF i) (CF i) (ZF i))

/-- Convert a `SigmaProtocol.Encoding` for an indexed family `PF` into an `Interactive.Encoding`,
encoding each transcript `(t, c, z, ())` as the nested pair `(t, (c, z))`. -/
def Encoding.toInteractiveEncoding (enc : Encoding I YF TF CF ZF) :
    Interactive.Encoding I (fun i => (PF i).interactiveSpec) YF where
  index := enc.index
  statement := enc.statement
  transcript i :=
    ⟨fun τ => encPair (enc.commitment i) (encPair (enc.challenge i) (enc.response i))
      ((PF i).conversationOfTranscript τ),
     (encPair (enc.commitment i) (encPair (enc.challenge i) (enc.response i))).injective.comp
      (PF i).conversationOfTranscript_injective⟩

theorem Encoding.toInteractiveEncoding_transcript_apply
    (enc : Encoding I YF TF CF ZF) (i : I) (τ : Transcript (PF i).interactiveSpec) :
    (enc.toInteractiveEncoding PF).transcript i τ =
      encPair encBits (encPair encBits encBits)
        (enc.commitment i ((PF i).commitOfTranscript τ),
          (enc.challenge i ((PF i).challengeOfTranscript τ),
            enc.response i ((PF i).responseOfTranscript τ))) := by
  simp only [toInteractiveEncoding, conversationOfTranscript, commitOfTranscript,
    challengeOfTranscript, responseOfTranscript, Function.Embedding.coeFn_mk, encPair_apply,
    encBits, Function.Embedding.coe_refl, id_eq]

/-- Combine a word-level challenge sampler `sampleChallengeWord` with a word-level Sigma-protocol
simulator `program` to sample encoded interactive transcripts `(t, (c, z))`. -/
def interactiveSimWord
    (program : I × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (sampleChallengeWord : I → ProbComp (List Bool)) :
    I × List Bool → ProbComp (List Bool) :=
  fun p =>
    encPair encBits (encPair encBits encBits) <$> do
      let cBits ← sampleChallengeWord p.1
      (fun tzBits => (tzBits.1, (cBits, tzBits.2))) <$> program (p.1, p.2, cBits)

/-- If `program` and `sampleChallengeWord` are uniform strict PPT, so is `interactiveSimWord`. -/
theorem isPPTOn_interactiveSimWord {enc : Encoding I YF TF CF ZF}
    {program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)}
    {sampleChallengeWord : I → ProbComp (List Bool)}
    (hprog : IsPPTOn (encSimulatorInput enc.index) (encPair encBits encBits) program)
    (hchal : IsPPTOn enc.index encBits sampleChallengeWord) :
    IsPPTOn (encPair enc.index encBits) encBits
      (interactiveSimWord program sampleChallengeWord) := by
  let encIn := encPair enc.index encBits
  have h1 : IsPPTOn encIn encBits (fun p : I × List Bool => sampleChallengeWord p.1) :=
    hchal.preprocess (by fun_prop)
  let encMid := encPair encIn encBits
  have h2 : IsPPTOn encMid (encPair encBits encBits)
      (fun q : (I × List Bool) × List Bool => program (q.1.1, q.1.2, q.2)) :=
    hprog.preprocess (by fun_prop)
  have h3 : IsPPTOn encMid (encPair encBits (encPair encBits encBits))
      (fun q : (I × List Bool) × List Bool =>
        (fun tzBits : List Bool × List Bool => (tzBits.1, (q.2, tzBits.2))) <$>
          program (q.1.1, q.1.2, q.2)) :=
    h2.map_with (by fun_prop)
  have h4 : IsPPTOn encIn (encPair encBits (encPair encBits encBits))
      (fun p : I × List Bool => do
        let cBits ← sampleChallengeWord p.1
        (fun tzBits : List Bool × List Bool => (tzBits.1, (cBits, tzBits.2))) <$>
          program (p.1, p.2, cBits)) :=
    h1.bind_with h3
  exact isPPTOn_iff_encoded.mp h4

variable [∀ i, Fintype (CF i)] [∀ i, Nonempty (CF i)]

/-- **Efficient knowledge soundness transfer**: if `PF` is special sound at every index and a
polynomial-time straight-line extractor family `E` recovers valid witnesses on accepting
transcripts of true statements, then `fun i => (PF i).toInteractiveVerifier` satisfies
`Verifier.EfficientKnowledgeSound` with error `fun i => 1 / |CF i|`. -/
theorem SpecialSoundness.efficientKnowledgeSound
    {RF : ∀ i, WF i → YF i → Prop}
    {extract : ∀ i, YF i → TF i → CF i → ZF i → CF i → ZF i → WF i}
    {enc : Encoding I YF TF CF ZF} {encW : ∀ i, WF i ↪ List Bool}
    {E : ∀ i, YF i → Transcript (PF i).interactiveSpec → Unit → WF i}
    (h : ∀ i, (PF i).SpecialSoundness (RF i) (extract i))
    (hE : ∀ i y τ, y ∈ language (Function.swap (RF i)) →
      (PF i).Accepts y ((PF i).commitOfTranscript τ) ((PF i).challengeOfTranscript τ)
        ((PF i).responseOfTranscript τ) →
      RF i (E i y τ ()) y)
    (hpoly : ∃ f, ComputableInPolyTime f
      (encPair enc.index (encPair encBits (encPair encBits encBits))) encBits ∧
      Interactive.ExtractorRealizedBy (enc.toInteractiveEncoding PF)
        (fun _ => encUnit) encW E f) :
    Interactive.Verifier.EfficientKnowledgeSound
      (fun i => (PF i).toInteractiveVerifier)
      (fun i => Function.swap (RF i)) (fun _ => Accept)
      (enc.toInteractiveEncoding PF) (fun _ => encUnit) encW E
      (fun i => 1 / (Fintype.card (CF i) : ℝ≥0∞)) where
  knowledgeSound i := SpecialSoundness.knowledgeSound_of_extractor (h i) (E i) (hE i)
  polyTime := hpoly

/-- `interactiveSimWord` realizes `(PF i).interactiveSim (simComp i)` on encodings up to
`δC i + δ i`. -/
theorem simulatorRealizedBy_interactiveSimWord
    {enc : Encoding I YF TF CF ZF}
    {simulate : ∀ i, YF i → CF i → PMF (TF i × ZF i)}
    {simComp : ∀ i, YF i → CF i → ProbComp (TF i × ZF i)}
    {program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)}
    {sampleChallenge : ∀ i, ProbComp (CF i)}
    {sampleChallengeWord : I → ProbComp (List Bool)}
    {δ δC : I → ℝ≥0∞}
    (hsim : ∀ i y c, ProbComp.eval (simComp i y c) = simulate i y c)
    (hreal : SimulatorRealizedBy enc simulate program δ)
    (hchal : ∀ i, CloseTo (PMF.uniformOfFintype (CF i))
      (ProbComp.eval (sampleChallenge i)) (δC i))
    (hchalWord : ∀ i, ProbComp.eval (sampleChallengeWord i) =
      (ProbComp.eval (sampleChallenge i)).map (enc.challenge i)) :
    Interactive.SimulatorRealizedBy (enc.toInteractiveEncoding PF)
      (fun i => (PF i).interactiveSim (simComp i))
      (interactiveSimWord program sampleChallengeWord)
      (fun i => δC i + δ i) := by
  intro i y
  let pack (cBits : List Bool) (tzBits : List Bool × List Bool) : List Bool :=
    encPair encBits (encPair encBits encBits) (tzBits.1, (cBits, tzBits.2))
  have hlhs :
      (ProbComp.eval ((PF i).interactiveSim (simComp i) y)).map
          ((enc.toInteractiveEncoding PF).transcript i) =
        (PMF.uniformOfFintype (CF i)).bind fun c =>
          ((simulate i y c).map (Prod.map (enc.commitment i) (enc.response i))).map
            (pack (enc.challenge i c)) := by
    rw [eval_interactiveSim, PMF.map_bind]
    refine congrArg ((PMF.uniformOfFintype (CF i)).bind ·) (funext fun c => ?_)
    rw [hsim i y c, PMF.map_comp, PMF.map_comp]
    rfl
  have hrhs :
      ProbComp.eval (interactiveSimWord program sampleChallengeWord
          (i, (enc.toInteractiveEncoding PF).statement i y)) =
        (ProbComp.eval (sampleChallenge i)).bind fun c =>
          (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))).map
            (pack (enc.challenge i c)) := by
    change ProbComp.eval (interactiveSimWord program sampleChallengeWord
        (i, enc.statement i y)) = _
    simp only [pmf_norm, interactiveSimWord, hchalWord i, pack]
  rw [hlhs, hrhs]
  exact CloseTo.bind (hchal i) fun c _ => (hreal i y c).map (pack (enc.challenge i c))

/-- **Efficient HVZK transfer**: an `EfficientSpecialHVZK` family of Sigma protocols, paired with a
strict PPT challenge sampler for `CF i` within `δC i` of uniform, yields
`Interactive.Reduction.EfficientHVZK` with simulation error `0` and realization error
`δC i + δ i`. -/
theorem EfficientSpecialHVZK.efficientHVZK
    {RF : ∀ i, XF i → YF i → Prop}
    {enc : Encoding I YF TF CF ZF}
    {simulate : ∀ i, YF i → CF i → PMF (TF i × ZF i)}
    {sampleCommit : ∀ i, XF i → YF i → ProbComp (TF i × (PF i).State)}
    {simComp : ∀ i, YF i → CF i → ProbComp (TF i × ZF i)}
    {sampleChallenge : ∀ i, ProbComp (CF i)}
    {sampleChallengeWord : I → ProbComp (List Bool)}
    {δ δC : I → ℝ≥0∞}
    (h : EfficientSpecialHVZK PF RF enc simulate δ)
    (hcommit : ∀ i, (PF i).CommitRealizedBy (sampleCommit i))
    (hsim : ∀ i y c, ProbComp.eval (simComp i y c) = simulate i y c)
    (hchalPPT : IsPPTOn enc.index encBits sampleChallengeWord)
    (hchal : ∀ i, CloseTo (PMF.uniformOfFintype (CF i))
      (ProbComp.eval (sampleChallenge i)) (δC i))
    (hchalWord : ∀ i, ProbComp.eval (sampleChallengeWord i) =
      (ProbComp.eval (sampleChallenge i)).map (enc.challenge i)) :
    Interactive.Reduction.EfficientHVZK
      (fun i => (PF i).toInteractiveReduction (sampleCommit i))
      (fun i => Function.swap (RF i))
      (enc.toInteractiveEncoding PF)
      (fun i => (PF i).interactiveSim (simComp i))
      (fun _ => 0) (fun i => δC i + δ i) where
  hvzk i := (h.specialHVZK i).hvzk_zero (hcommit i) (hsim i)
  realized := by
    obtain ⟨program, hprogPPT, hprogReal⟩ := h.realized
    exact ⟨interactiveSimWord program sampleChallengeWord,
      isPPTOn_interactiveSimWord hprogPPT hchalPPT,
      simulatorRealizedBy_interactiveSimWord PF hsim hprogReal hchal hchalWord⟩

end Family

/-! ### Realizations for linear, Schnorr, AND and OR protocols -/

section Linear

variable {q : ℕ} {M N Y C : Type} [AddCommGroup M] [Module (ZMod q) M] [Fintype M] [Nonempty M]
  [AddCommGroup N] [Module (ZMod q) N]

/-- `ProbComp` commitment sampler for `SigmaProtocol.linear`: draw `r ← ProbComp.uniform M` and
return `(ψ y r, r)`. -/
noncomputable def linearCommit (ψ : Y → M →ₗ[ZMod q] N) (_ : M) (y : Y) : ProbComp (N × M) :=
  (fun r => (ψ y r, r)) <$> ProbComp.uniform M

/-- `ProbComp` simulator for `SigmaProtocol.linear`: draw `z ← ProbComp.uniform M` and return
`(ψ y z - ι c • u y, z)`. -/
noncomputable def linearSimComp (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q)
    (y : Y) (c : C) : ProbComp (N × M) :=
  (fun z => (ψ y z - ι c • u y, z)) <$> ProbComp.uniform M

theorem commitRealizedBy_linear [DecidableEq N] (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N)
    (ι : C ↪ ZMod q) :
    (linear ψ u ι).CommitRealizedBy (linearCommit ψ) := by
  intro x y
  simp [linearCommit, linear]

@[simp] theorem eval_linearSimComp (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q)
    (y : Y) (c : C) :
    ProbComp.eval (linearSimComp ψ u ι y c) = linearSimulate ψ u ι y c := by
  simp [linearSimComp, linearSimulate]

end Linear

section Schnorr

variable {q : ℕ} [NeZero q] {G C : Type} [AddCommGroup G] [Module (ZMod q) G]
  (ι : C ↪ ZMod q) (g : G)

/-- `ProbComp` commitment sampler for `SigmaProtocol.schnorr`. -/
noncomputable def schnorrCommit : ZMod q → G → ProbComp (G × ZMod q) :=
  linearCommit (fun _ : G => LinearMap.toSpanSingleton (ZMod q) G g)

/-- `ProbComp` simulator for `SigmaProtocol.schnorr`. -/
noncomputable def schnorrSimComp : G → C → ProbComp (G × ZMod q) :=
  linearSimComp (fun _ : G => LinearMap.toSpanSingleton (ZMod q) G g) id ι

theorem commitRealizedBy_schnorr [DecidableEq G] :
    (schnorr ι g).CommitRealizedBy (schnorrCommit g) :=
  commitRealizedBy_linear _ _ ι

@[simp] theorem eval_schnorrSimComp (u : G) (c : C) :
    ProbComp.eval (schnorrSimComp ι g u c) =
      linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι u c :=
  eval_linearSimComp _ _ ι u c

end Schnorr

section Composition

variable {X₀ Y₀ T₀ Z₀ X₁ Y₁ T₁ Z₁ C : Type}
  {P₀ : SigmaProtocol X₀ Y₀ T₀ C Z₀} {P₁ : SigmaProtocol X₁ Y₁ T₁ C Z₁}

/-- `ProbComp` commitment sampler for `P₀.andProof P₁`. -/
def andCommit (sample₀ : X₀ → Y₀ → ProbComp (T₀ × P₀.State))
    (sample₁ : X₁ → Y₁ → ProbComp (T₁ × P₁.State)) (x : X₀ × X₁) (y : Y₀ × Y₁) :
    ProbComp ((T₀ × T₁) × P₀.State × P₁.State) := do
  let a ← sample₀ x.1 y.1
  let b ← sample₁ x.2 y.2
  return ((a.1, b.1), (a.2, b.2))

/-- `ProbComp` simulator for `P₀.andProof P₁`. -/
def andSimComp (sim₀ : Y₀ → C → ProbComp (T₀ × Z₀)) (sim₁ : Y₁ → C → ProbComp (T₁ × Z₁))
    (y : Y₀ × Y₁) (c : C) : ProbComp ((T₀ × T₁) × (Z₀ × Z₁)) := do
  let a ← sim₀ y.1 c
  let b ← sim₁ y.2 c
  return ((a.1, b.1), (a.2, b.2))

theorem commitRealizedBy_andProof {sample₀ : X₀ → Y₀ → ProbComp (T₀ × P₀.State)}
    {sample₁ : X₁ → Y₁ → ProbComp (T₁ × P₁.State)}
    (h₀ : P₀.CommitRealizedBy sample₀) (h₁ : P₁.CommitRealizedBy sample₁) :
    (P₀.andProof P₁).CommitRealizedBy (andCommit sample₀ sample₁) := by
  intro x y
  simp only [pmf_norm, andCommit, andProof, h₀ x.1 y.1, h₁ x.2 y.2]

theorem eval_andSimComp {simulate₀ : Y₀ → C → PMF (T₀ × Z₀)}
    {simulate₁ : Y₁ → C → PMF (T₁ × Z₁)}
    {sim₀ : Y₀ → C → ProbComp (T₀ × Z₀)} {sim₁ : Y₁ → C → ProbComp (T₁ × Z₁)}
    (h₀ : ∀ y c, ProbComp.eval (sim₀ y c) = simulate₀ y c)
    (h₁ : ∀ y c, ProbComp.eval (sim₁ y c) = simulate₁ y c)
    (y : Y₀ × Y₁) (c : C) :
    ProbComp.eval (andSimComp sim₀ sim₁ y c) = andSimulate simulate₀ simulate₁ y c := by
  simp only [pmf_norm, andSimComp, andSimulate, h₀ y.1 c, h₁ y.2 c]

variable [AddCommGroup C] [Fintype C] [Nonempty C]

/-- `ProbComp` commitment sampler for `orProof P₀ P₁ simulate₀ simulate₁`. -/
noncomputable def orCommit (sample₀ : X₀ → Y₀ → ProbComp (T₀ × P₀.State))
    (sample₁ : X₁ → Y₁ → ProbComp (T₁ × P₁.State))
    (sim₀ : Y₀ → C → ProbComp (T₀ × Z₀)) (sim₁ : Y₁ → C → ProbComp (T₁ × Z₁)) :
    X₀ ⊕ X₁ → Y₀ × Y₁ →
      ProbComp ((T₀ × T₁) × ((X₀ × P₀.State × C × Z₁) ⊕ (X₁ × P₁.State × C × Z₀)))
  | .inl x, y => do
    let c₁ ← ProbComp.uniform C
    let b ← sim₁ y.2 c₁
    let a ← sample₀ x y.1
    return ((a.1, b.1), Sum.inl (x, a.2, c₁, b.2))
  | .inr x, y => do
    let c₀ ← ProbComp.uniform C
    let a ← sim₀ y.1 c₀
    let b ← sample₁ x y.2
    return ((a.1, b.1), Sum.inr (x, b.2, c₀, a.2))

/-- `ProbComp` simulator for `orProof P₀ P₁ simulate₀ simulate₁`. -/
noncomputable def orSimComp (sim₀ : Y₀ → C → ProbComp (T₀ × Z₀))
    (sim₁ : Y₁ → C → ProbComp (T₁ × Z₁)) (y : Y₀ × Y₁) (c : C) :
    ProbComp ((T₀ × T₁) × C × Z₀ × Z₁) := do
  let c₀ ← ProbComp.uniform C
  let a ← sim₀ y.1 c₀
  let b ← sim₁ y.2 (c - c₀)
  return ((a.1, b.1), c₀, a.2, b.2)

theorem commitRealizedBy_orProof
    {simulate₀ : Y₀ → C → PMF (T₀ × Z₀)} {simulate₁ : Y₁ → C → PMF (T₁ × Z₁)}
    {sample₀ : X₀ → Y₀ → ProbComp (T₀ × P₀.State)}
    {sample₁ : X₁ → Y₁ → ProbComp (T₁ × P₁.State)}
    {sim₀ : Y₀ → C → ProbComp (T₀ × Z₀)} {sim₁ : Y₁ → C → ProbComp (T₁ × Z₁)}
    (h₀ : P₀.CommitRealizedBy sample₀) (h₁ : P₁.CommitRealizedBy sample₁)
    (hs₀ : ∀ y c, ProbComp.eval (sim₀ y c) = simulate₀ y c)
    (hs₁ : ∀ y c, ProbComp.eval (sim₁ y c) = simulate₁ y c) :
    (orProof P₀ P₁ simulate₀ simulate₁).CommitRealizedBy
      (orCommit sample₀ sample₁ sim₀ sim₁) := by
  rintro (x | x) y
  · simp only [pmf_norm, orCommit, orProof, ProbComp.eval_uniform, h₀ x y.1, hs₁]
  · simp only [pmf_norm, orCommit, orProof, ProbComp.eval_uniform, h₁ x y.2, hs₀]

theorem eval_orSimComp
    {simulate₀ : Y₀ → C → PMF (T₀ × Z₀)} {simulate₁ : Y₁ → C → PMF (T₁ × Z₁)}
    {sim₀ : Y₀ → C → ProbComp (T₀ × Z₀)} {sim₁ : Y₁ → C → ProbComp (T₁ × Z₁)}
    (hs₀ : ∀ y c, ProbComp.eval (sim₀ y c) = simulate₀ y c)
    (hs₁ : ∀ y c, ProbComp.eval (sim₁ y c) = simulate₁ y c)
    (y : Y₀ × Y₁) (c : C) :
    ProbComp.eval (orSimComp sim₀ sim₁ y c) = orSimulate simulate₀ simulate₁ y c := by
  simp only [pmf_norm, orSimComp, orSimulate, ProbComp.eval_uniform, hs₀, hs₁]

end Composition

end Cslib.Crypto.Protocols.SigmaProtocol
