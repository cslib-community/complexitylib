/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.Rewinding

/-!
# Sigma protocols are proofs of knowledge with a strict PPT rewinding extractor

A special-sound Sigma protocol is a proof of knowledge: from any prover that convinces the
verifier on a statement `y` with probability `ε`, a knowledge extractor that may rewind the prover
computes a witness for `y`. This module formalizes the standard extractor for an indexed family
`P i` of Sigma protocols with a polynomial-time special-soundness extractor
(`EfficientSpecialSoundness`), and proves that it is uniform strict PPT whenever the prover is.
Proofs of knowledge are defined by Bellare and Goldreich ([BellareGoldreich1992], Definition 3.1).
The per-statement, strict-time form proved here, and its proof from the rewinding lemma, are the
library's own; the end of this overview compares it with their definition.

A prover `A : MaliciousProver I` works on words, so it may cheat: at index `i` it commits from the
encoded statement, keeping a state word, and answers the encoded challenge from that state. The
verifier accepts when the two words it receives encode a commitment and a response that `P i`
accepts (`AcceptsWord`). `acceptanceGame` is one run of `A` against the verifier, with challenges
drawn from a given law; with the uniform law it is the honest verifier.

The extractor `knowledgeExtractor` runs `A` to its commitment, draws two challenges with a
sampler `sampleChallenge`, answers both from the same state, and applies the word function
`extractWord` of the special-soundness extractor to the two conversations. It runs `A` twice, so
it is strict PPT with no expected-time argument (`isPPTOn_knowledgeExtractor`). Its success
probability follows from the rewinding lemma `Rewinding.sq_sub_mul_le_twice`: on every statement,

  `ε ^ 2 - κ * ε ≤ ε'`  (`sq_sub_mul_le_extractionGame`),

where `ε` is the acceptance probability of `A` with challenges from the sampler, `κ` bounds the
sampler's atoms and `ε'` is the extractor's success probability (`extractionGame`). For a sampler
that is exactly uniform this is `ε ^ 2 - ε / |C| ≤ ε'` against the honest verifier
(`sq_sub_le_extractionGame`). A strict PPT machine with fair coins samples a challenge space such
as `ZMod q` only approximately; for a sampler within statistical distance `δ` of uniform, the
honest verifier's acceptance probability satisfies `ε ≤ 1 / |C| + 2 δ + √ε'`
(`le_add_sqrt_extractionGame`).

The hypotheses are only about generic components supplied by the caller: special soundness of
the protocol and a polynomial-time word function realizing its extractor, and a strict PPT
challenge sampler. Nothing is assumed about the knowledge extractor this module builds.

Bellare and Goldreich's validity condition asks for an extractor that, whenever `ε` exceeds the
knowledge error `κ`, outputs a witness within an expected number of steps bounded by a polynomial
divided by `ε - κ` ([BellareGoldreich1992], Definition 3.1). The extractor here instead runs in
strict polynomial time and succeeds with probability at least `ε ^ 2 - κ * ε`; repeating it
amplifies its success probability.

## Main definitions

* `SigmaProtocol.MaliciousProver`, `SigmaProtocol.MaliciousProver.IsPPT`: a two-stage prover on
  words and its uniform strict PPT admissibility.
* `SigmaProtocol.AcceptsWord`: the verifier of `P i` on a commitment word and a response word.
* `SigmaProtocol.acceptanceGame`: one run of a prover against the verifier.
* `SigmaProtocol.knowledgeExtractor`: the rewinding knowledge extractor.
* `SigmaProtocol.extractionGame`: a word extractor outputs the encoding of a witness.

## Main results

* `SigmaProtocol.isPPTOn_knowledgeExtractor`: the extractor is uniform strict PPT whenever the
  prover is.
* `SigmaProtocol.sq_sub_mul_le_extractionGame`: `ε ^ 2 - κ * ε ≤ ε'` for a sampler with atoms at
  most `κ`.
* `SigmaProtocol.sq_sub_le_extractionGame`: `ε ^ 2 - ε / |C| ≤ ε'` for an exactly uniform sampler.
* `SigmaProtocol.le_add_sqrt_extractionGame`: `ε ≤ 1 / |C| + 2 δ + √ε'` for a sampler within `δ`
  of uniform.

## References

* [M. Bellare, O. Goldreich, *On Defining Proofs of Knowledge*][BellareGoldreich1992]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable {I : Type} {X Y T C Z W : I → Type}

/-! ### Provers on words and acceptance -/

/-- A prover for a family of Sigma protocols indexed by `I`, which may cheat. At index `i`, its
first stage reads the encoded statement and returns a commitment word and a state word; its second
stage reads the state word and the encoded challenge and returns a response word. Both stages may
use fresh randomness. -/
structure MaliciousProver (I : Type) where
  /-- Commit from the index and the encoded statement, keeping a state word. -/
  commit : I → List Bool → ProbComp (List Bool × List Bool)
  /-- Respond from the index, the state word and the encoded challenge. -/
  respond : I → List Bool → List Bool → ProbComp (List Bool)

/-- Both stages of a prover are uniform strict PPT in their whole inputs, with the index encoded
by `encI`. -/
structure MaliciousProver.IsPPT (encI : I ↪ List Bool) (A : MaliciousProver I) : Prop where
  /-- The first stage is uniform strict PPT. -/
  commit : IsPPTOn (encPair encI encBits) (encPair encBits encBits)
    fun (i, y) => A.commit i y
  /-- The second stage is uniform strict PPT. -/
  respond : IsPPTOn (encPair encI (encPair encBits encBits)) encBits
    fun (i, s, c) => A.respond i s c

/-- The verifier of `P i` on words: the commitment word `t` and the response word `z` encode a
commitment and a response that `P i` accepts on the statement `y` at the challenge `c`. Words that
encode no commitment or no response are rejected. -/
def AcceptsWord (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (enc : Encoding I Y T C Z) (i : I) (y : Y i) (t : List Bool) (c : C i) (z : List Bool) :
    Prop :=
  ∃ t' z', enc.commitment i t' = t ∧ enc.response i z' = z ∧ (P i).Accepts y t' c z'

open Classical in
/-- One run of the prover `A` against the verifier of `P i` on the statement `y`, with the
challenge drawn from `challenge`; it succeeds when the verifier accepts. With
`challenge = PMF.uniformOfFintype (C i)` this is the honest verifier. -/
noncomputable def acceptanceGame (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (enc : Encoding I Y T C Z) (A : MaliciousProver I) (i : I) (y : Y i)
    (challenge : PMF (C i)) : Game := do
  let (t, s) ← ProbComp.eval (A.commit i (enc.statement i y))
  let c ← challenge
  let z ← ProbComp.eval (A.respond i s (enc.challenge i c))
  return decide (AcceptsWord P enc i y t c z)

/-! ### The rewinding knowledge extractor -/

/-- The rewinding knowledge extractor: on the index `i` and a statement word `y`, run `A` to its
commitment `t`, draw two challenges with `sampleChallenge i`, answer both from the same state,
and apply the word function `extractWord` of a special-soundness extractor to the two
conversations. -/
noncomputable def knowledgeExtractor (enc : Encoding I Y T C Z)
    (sampleChallenge : ∀ i, ProbComp (C i))
    (extractWord :
      I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool)
    (A : MaliciousProver I) : I × List Bool → ProbComp (List Bool) :=
  fun (i, y) => do
    let (t, s) ← A.commit i y
    let c ← enc.challenge i <$> sampleChallenge i
    let c' ← enc.challenge i <$> sampleChallenge i
    let z ← A.respond i s c
    let z' ← A.respond i s c'
    return extractWord (i, y, t, c, z, c', z')

open Classical in
/-- A word extractor `E`, run on the index `i` and the encoded statement `y`, outputs the encoding
of a witness for `y` under the relation `R i`. -/
noncomputable def extractionGame (enc : Encoding I Y T C Z) (encW : ∀ i, W i ↪ List Bool)
    (R : ∀ i, W i → Y i → Prop) (E : I × List Bool → ProbComp (List Bool)) (i : I) (y : Y i) :
    Game := do
  let w ← ProbComp.eval (E (i, enc.statement i y))
  return decide (∃ x, encW i x = w ∧ R i x y)

/-! ### Efficiency -/

/-- **The knowledge extractor is uniform strict PPT** whenever the prover is, the challenge
sampler writes encoded challenges in strict polynomial time, and `extractWord` is computable in
polynomial time. -/
theorem isPPTOn_knowledgeExtractor {enc : Encoding I Y T C Z}
    {sampleChallenge : ∀ i, ProbComp (C i)}
    {extractWord :
      I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool}
    (hchallenge : IsPPTOn enc.index encBits fun i => enc.challenge i <$> sampleChallenge i)
    (hextract : ComputableInPolyTime extractWord (encPair enc.index (encPair encBits
      (encPair encBits (encPair encBits (encPair encBits (encPair encBits encBits)))))) encBits)
    {A : MaliciousProver I} (hA : A.IsPPT enc.index) :
    IsPPTOn (encPair enc.index encBits) encBits (knowledgeExtractor enc sampleChallenge
      extractWord A) := by
  let encIn := encPair enc.index encBits
  have hcommit : IsPPTOn encIn (encPair encBits encBits)
      fun p : I × List Bool => A.commit p.1 p.2 := hA.commit
  have hrespond : IsPPTOn (encPair enc.index (encPair encBits encBits)) encBits
      fun p : I × List Bool × List Bool => A.respond p.1 p.2.1 p.2.2 := hA.respond
  change IsPPTOn encIn encBits fun p : I × List Bool => do
    let ts ← A.commit p.1 p.2
    let c ← enc.challenge p.1 <$> sampleChallenge p.1
    let c' ← enc.challenge p.1 <$> sampleChallenge p.1
    let z ← A.respond p.1 ts.2 c
    let z' ← A.respond p.1 ts.2 c'
    return extractWord (p.1, p.2, ts.1, c, z, c', z')
  refine hcommit.bind_with ?_
  refine (hchallenge.preprocess (prepare := fun q : (I × List Bool) × List Bool × List Bool =>
    q.1.1) (by fun_prop)).bind_with ?_
  refine (hchallenge.preprocess (prepare := fun q : ((I × List Bool) × List Bool × List Bool) ×
    List Bool => q.1.1.1) (by fun_prop)).bind_with ?_
  refine (hrespond.preprocess (prepare := fun q : (((I × List Bool) × List Bool × List Bool) ×
    List Bool) × List Bool => (q.1.1.1.1, q.1.1.2.2, q.1.2)) (by fun_prop)).bind_with ?_
  refine (hrespond.preprocess (prepare := fun q : ((((I × List Bool) × List Bool × List Bool) ×
    List Bool) × List Bool) × List Bool => (q.1.1.1.1.1, q.1.1.1.2.2, q.1.2))
    (by fun_prop)).bind_with ?_
  refine (ComputableInPolyTime.isPPTOn ?_)
  exact hextract.comp (by fun_prop)

/-! ### Success probability -/

variable {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)} {enc : Encoding I Y T C Z}
  {R : ∀ i, W i → Y i → Prop} {extract : ∀ i, Y i → T i → C i → Z i → C i → Z i → W i}
  {encW : ∀ i, W i ↪ List Bool}
  {extractWord :
    I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool}

/-- The prover's first stage on the encoded statement. -/
private noncomputable def firstStage (enc : Encoding I Y T C Z) (A : MaliciousProver I) (i : I)
    (y : Y i) : PMF (List Bool × List Bool) :=
  ProbComp.eval (A.commit i (enc.statement i y))

/-- An acceptance game is one run of the two-stage experiment of the rewinding lemma. -/
private theorem acceptanceGame_eq_once (A : MaliciousProver I) (i : I) (y : Y i)
    (challenge : PMF (C i)) :
    acceptanceGame P enc A i y challenge = Rewinding.once (firstStage enc A i y)
      (fun _ => challenge) (fun ts c => ProbComp.eval (A.respond i ts.2 (enc.challenge i c)))
      (fun ts c z => @decide (AcceptsWord P enc i y ts.1 c z) (Classical.propDecidable _)) :=
  rfl

/-- Two accepting runs with distinct challenges lead the knowledge extractor to a witness. -/
private theorem twice_le_extractionGame
    (hsound : ∀ i, (P i).SpecialSoundness (R i) (extract i))
    (hreal : ExtractorRealizedBy enc encW extract extractWord)
    (sampleChallenge : ∀ i, ProbComp (C i)) (A : MaliciousProver I) (i : I) (y : Y i)
    [DecidableEq (C i)] :
    Rewinding.twice (firstStage enc A i y) (fun _ => ProbComp.eval (sampleChallenge i))
        (fun ts c => ProbComp.eval (A.respond i ts.2 (enc.challenge i c)))
        (fun ts c z => @decide (AcceptsWord P enc i y ts.1 c z) (Classical.propDecidable _))
        true ≤
      extractionGame enc encW R (knowledgeExtractor enc sampleChallenge extractWord A) i y
        true := by
  classical
  simp only [pmf_norm, Rewinding.twice, extractionGame, knowledgeExtractor, firstStage,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_map]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun ts _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun c _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun c' _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun z _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun z' _ => ?_
  by_cases hwin : (decide (AcceptsWord P enc i y ts.1 c z) &&
      decide (AcceptsWord P enc i y ts.1 c' z') && c != c') = true
  · simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hwin
    obtain ⟨⟨⟨t₀, z₀, ht, hz, hacc⟩, ⟨t₁, z₁, ht', hz', hacc'⟩⟩, hne⟩ := hwin
    have htt : t₁ = t₀ := (enc.commitment i).injective (ht'.trans ht.symm)
    rw [htt] at hacc'
    have hR := hsound i y t₀ c z₀ c' z₁ hne hacc hacc'
    calc _ ≤ 1 := PMF.coe_le_one _ _
      _ = _ := by
        rw [← ht, ← hz, ← hz', hreal, decide_eq_true ⟨_, rfl, hR⟩, PMF.pure_apply_self]
  · simp [Bool.eq_false_iff.mpr hwin]

/-- **Extraction by rewinding**: on every statement `y`, if the prover `A` convinces the verifier
with probability `ε` when challenges are drawn by `sampleChallenge i`, and every challenge has
probability at most `κ` under that sampler, the knowledge extractor outputs a witness for `y`
with probability at least `ε ^ 2 - κ * ε`. -/
theorem sq_sub_mul_le_extractionGame [∀ i, Finite (C i)]
    (hsound : ∀ i, (P i).SpecialSoundness (R i) (extract i))
    (hreal : ExtractorRealizedBy enc encW extract extractWord)
    (sampleChallenge : ∀ i, ProbComp (C i)) (A : MaliciousProver I) (i : I) (y : Y i) {κ : ℝ}
    (hκ : ∀ c, (ProbComp.eval (sampleChallenge i) c).toReal ≤ κ) :
    (Game.succProbability (acceptanceGame P enc A i y (ProbComp.eval (sampleChallenge i))) :
        ℝ) ^ 2 -
      κ * Game.succProbability (acceptanceGame P enc A i y (ProbComp.eval (sampleChallenge i))) ≤
    Game.succProbability (extractionGame enc encW R
      (knowledgeExtractor enc sampleChallenge extractWord A) i y) := by
  classical
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  rw [acceptanceGame_eq_once]
  exact (Rewinding.sq_sub_mul_le_twice _ _ _ _ fun _ _ c => hκ c).trans
    (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
      (twice_le_extractionGame hsound hreal sampleChallenge A i y))

variable [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]

/-- **Extraction by rewinding with exactly uniform challenges**: on every statement `y`, if the
prover `A` convinces the honest verifier with probability `ε` and `sampleChallenge i` samples
uniform challenges, the knowledge extractor outputs a witness for `y` with probability at least
`ε ^ 2 - ε / |C i|`. -/
theorem sq_sub_le_extractionGame (hsound : ∀ i, (P i).SpecialSoundness (R i) (extract i))
    (hreal : ExtractorRealizedBy enc encW extract extractWord)
    {sampleChallenge : ∀ i, ProbComp (C i)} (A : MaliciousProver I) (i : I) (y : Y i)
    (huniform : ProbComp.eval (sampleChallenge i) = PMF.uniformOfFintype (C i)) :
    (Game.succProbability (acceptanceGame P enc A i y (PMF.uniformOfFintype (C i))) : ℝ) ^ 2 -
      Game.succProbability (acceptanceGame P enc A i y (PMF.uniformOfFintype (C i))) /
        Fintype.card (C i) ≤
    Game.succProbability (extractionGame enc encW R
      (knowledgeExtractor enc sampleChallenge extractWord A) i y) := by
  have h := sq_sub_mul_le_extractionGame hsound hreal sampleChallenge A i y
    (κ := (Fintype.card (C i) : ℝ)⁻¹) fun c => by
      simp only [huniform, Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, le_refl]
  rw [huniform] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- **Extraction by rewinding with approximately uniform challenges**: on every statement `y`, if
`sampleChallenge i` is within statistical distance `δ` of uniform, the honest verifier's
acceptance probability `ε` of the prover `A` and the knowledge extractor's success probability
`ε'` satisfy `ε ≤ 1 / |C i| + 2 δ + √ε'`. -/
theorem le_add_sqrt_extractionGame (hsound : ∀ i, (P i).SpecialSoundness (R i) (extract i))
    (hreal : ExtractorRealizedBy enc encW extract extractWord)
    {sampleChallenge : ∀ i, ProbComp (C i)} (A : MaliciousProver I) (i : I) (y : Y i)
    {δ : ℝ≥0}
    (hclose : CloseTo (PMF.uniformOfFintype (C i)) (ProbComp.eval (sampleChallenge i)) δ) :
    (Game.succProbability (acceptanceGame P enc A i y (PMF.uniformOfFintype (C i))) : ℝ) ≤
      1 / Fintype.card (C i) + 2 * δ +
        √(Game.succProbability (extractionGame enc encW R
          (knowledgeExtractor enc sampleChallenge extractWord A) i y)) := by
  classical
  set κ : ℝ := 1 / Fintype.card (C i) + δ with hκ_def
  -- Each challenge has probability at most `1 / |C i| + δ` under the sampler.
  have hκ (c : C i) : (ProbComp.eval (sampleChallenge i) c).toReal ≤ κ := by
    have h := hclose.symm {c}
    rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton,
      Probability.PMF.uniformOfFintype_apply] at h
    have hne : (Fintype.card (C i) : ℝ≥0∞)⁻¹ + (δ : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.inv_ne_top.mpr (by simp), ENNReal.coe_ne_top⟩
    calc (ProbComp.eval (sampleChallenge i) c).toReal
        ≤ ((Fintype.card (C i) : ℝ≥0∞)⁻¹ + δ).toReal := ENNReal.toReal_mono hne h
      _ = κ := by
        rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr (by simp)) ENNReal.coe_ne_top,
          ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.coe_toReal, hκ_def, one_div]
  -- With challenges from the sampler, the prover succeeds with probability at most `κ + √ε'`.
  have hsampled : (Game.succProbability
      (acceptanceGame P enc A i y (ProbComp.eval (sampleChallenge i))) : ℝ) ≤
      κ + √(Game.succProbability (extractionGame enc encW R
        (knowledgeExtractor enc sampleChallenge extractWord A) i y)) := by
    simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
    rw [acceptanceGame_eq_once]
    exact (Rewinding.le_add_sqrt_twice _ _ _ _ fun _ _ c => hκ c).trans
      (add_le_add le_rfl (Real.sqrt_le_sqrt (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
        (twice_le_extractionGame hsound hreal sampleChallenge A i y))))
  -- Replacing uniform challenges by the sampler changes acceptance by at most `δ`.
  have hgame : CloseTo (acceptanceGame P enc A i y (PMF.uniformOfFintype (C i)))
      (acceptanceGame P enc A i y (ProbComp.eval (sampleChallenge i))) δ := by
    simp only [acceptanceGame_eq_once, Rewinding.once]
    exact CloseTo.bind_right _ fun ts _ => hclose.bind_left _
  have hswap := Game.coe_succProbability_le_add_of_advantage_le
    (NNReal.coe_le_coe.mpr (Game.closeTo_iff_advantage_le.mp hgame))
  linarith

end Cslib.Crypto.Protocols.SigmaProtocol
