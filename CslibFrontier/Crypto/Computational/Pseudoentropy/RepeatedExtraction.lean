/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Crypto.Computational.Pseudoentropy.ExtractionSchedule
public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Probability.Entropy
public import CslibFrontier.Probability.UniversalHash
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.EntropyExtraction
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Repeated extraction with public side information

Sample a list of observation-label pairs, hash its labels, and retain the observations and the
complete independent hash seed. Labels may be arbitrary finite values, including observations
or saved sampler seeds. Boolean labels retain their ordinary word-based PPT interface.

The exact product law and conditional-entropy extraction bound are shared by all three parts of
the pseudoentropy construction. The ideal experiment preserves the original public marginal.

The statistical statements quantify over every randomized finite-output test of the complete
output, including every Boolean test, with no computational restriction. This uses the existing
finite-PMF metric without requiring a metric on the infinite ambient type of lists.

## Main definitions

* `extractLabels`: hash sampled labels under a fresh seed, keeping observations and the seed.
* `extractLabelsReal`, `extractLabelsIdeal`: the repeated real experiment and its ideal
  public-marginal counterpart.

## Main results

* `eval_replicate_extractLabels`: exact agreement with the finite product experiment.
* `eval_replicate_extractLabels_map_pair`: transport the complete experiment from a sampling law.
* `extractLabels_dist_bind_le`: conditional entropy bounds every randomized finite-output test.
* `extractLabels_indistinguishable`: statistical security for the common repetition schedule.
* `isPPTOn_extractLabels`, `isPPTOn_extractLabels_list`: strict PPT with raw or framed labels.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 3.3 and Section 5, Games 0--2.
  [Holenstein2006].
  The statistical bound uses the seed-information concentration variant documented in
  `CslibFrontier.Probability.EntropyExtraction`.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF Turing.MultiTapeTM

/-- Hash the sampled labels, retaining every public observation and the independent hash seed. -/
def extractLabels {Observation Label Seed Output : Type} (seed : ProbComp Seed)
    (hash : Seed → List Label → Output) (samples : List (Observation × Label)) :
    ProbComp (List Observation × Seed × Output) := do
  let key ← seed
  return (samples.map Prod.fst, key, hash key (samples.map Prod.snd))

/-- The real extraction experiment: draw `count` independent observation-label pairs from
`source`, then hash their labels under a fresh seed. `extractLabelsIdeal` is its ideal
counterpart. -/
abbrev extractLabelsReal {Observation Label Seed Output : Type}
    (source : ProbComp (Observation × Label)) (count : ℕ) (seed : ProbComp Seed)
    (hash : Seed → List Label → Output) : ProbComp (List Observation × Seed × Output) :=
  OracleComp.replicate count source >>= extractLabels seed hash

/-- Preserve the sampled observations and public seed, replacing the extracted labels by an
independent uniform output. The ambient observation and seed types need not be finite. -/
noncomputable def extractLabelsIdeal {Observation Seed Output : Type}
    [Fintype Output] [Nonempty Output] (source : ProbComp Observation) (count : ℕ)
    (seed : ProbComp Seed) : PMF (List Observation × Seed × Output) := do
  let observed ← ProbComp.eval (OracleComp.replicate count source)
  (do
    let s ← ProbComp.eval seed
    (PMF.uniformOfFintype Output).map (s, ·)).map (observed, ·)

/-- A sampling law for re-encoded observations transports the ideal extraction experiment. -/
theorem extractLabelsIdeal_map_observation {α β Seed Output : Type}
    [Fintype Output] [Nonempty Output] (observe : α → β) (source : ProbComp α)
    (count : ℕ) (seed : ProbComp Seed) {encoded : ProbComp β}
    (hsource : ProbComp.eval encoded = (ProbComp.eval source).map observe) :
    (extractLabelsIdeal (Output := Output) source count seed).map
      (fun result => (result.1.map observe, result.2)) =
        extractLabelsIdeal encoded count seed := by
  simp only [pmf_norm, extractLabelsIdeal, monad_bind_eq_bind, ProbComp.eval_replicate_map hsource]

/-- Forgetting side information leaves an independent public seed and uniform output. -/
theorem extractLabelsIdeal_map_snd {Observation Seed Output : Type}
    [Fintype Output] [Nonempty Output] (source : ProbComp Observation) (count : ℕ)
    (seed : ProbComp Seed) :
    (extractLabelsIdeal (Output := Output) source count seed).map Prod.snd =
      (ProbComp.eval seed).bind (fun key => (PMF.uniformOfFintype Output).map (key, ·)) := by
  simp only [pmf_norm, extractLabelsIdeal, monad_bind_eq_bind, PMF.bind_const]

/-- Re-encoding both fields changes only the hash's input representation and public output. -/
theorem extractLabels_map_pair {α β Label Value Seed Output : Type}
    (observe : α → β) (encode : Label → Value) (seed : ProbComp Seed)
    (hash : Seed → List Value → Output) (samples : List (α × Label)) :
    extractLabels seed hash (samples.map (fun sample => (observe sample.1, encode sample.2))) =
      (fun result => (result.1.map observe, result.2)) <$>
        extractLabels seed (fun key values => hash key (values.map encode)) samples := by
  simp only [extractLabels, map_bind, map_pure, List.map_map, Function.comp_def]

/-- A sampling law for re-encoded observations and hash inputs transports the full repeated
experiment. Only the output distribution matters; the sampler need not be a syntactic map. -/
theorem eval_replicate_extractLabels_map_pair {α β Label Value Seed Output : Type}
    (observe : α → β) (encode : Label → Value) (source : ProbComp (α × Label))
    (count : ℕ) (seed : ProbComp Seed) (hash : Seed → List Value → Output)
    {encoded : ProbComp (β × Value)}
    (hsource : ProbComp.eval encoded =
      (ProbComp.eval source).map (fun sample => (observe sample.1, encode sample.2))) :
    ProbComp.eval (extractLabelsReal encoded count seed hash) =
      (ProbComp.eval (extractLabelsReal source count seed
        (fun key values => hash key (values.map encode)))).map
          (fun result => (result.1.map observe, result.2)) := by
  simp only [pmf_norm, ProbComp.eval_replicate_map hsource, extractLabels_map_pair]

/-- Label extraction composes ordinary sampling, list projections, and an efficient hash. -/
theorem isPPTOn_extractLabels {Param Observation Seed Output : Type} {input : Param ↪ List Bool}
    {observation : Observation ↪ List Bool} {key : Seed ↪ List Bool} {output : Output ↪ List Bool}
    {seed : Param → ProbComp Seed} {hash : Param → Seed → List Bool → Output}
    {samples : Param → List (Observation × Bool)}
    (hseed : IsPPTOn input key seed)
    (hhash : ComputableInPolyTime (fun pair => hash pair.1.1 pair.1.2 pair.2)
      (encPair (encPair input key) encBits) output)
    (hsamples : ComputableInPolyTime samples input (encList (encPair observation encBool))) :
    IsPPTOn input (encPair (encList observation) (encPair key output))
      (fun a => extractLabels (seed a) (hash a) (samples a)) :=
  let p0 := ComputableInPolyTime.fst input key; let p1 := ComputableInPolyTime.snd input key
  let hs := p0.trans hsamples
  let hobs := hs.mapWithInput ((ComputableInPolyTime.snd _ _).trans (.fst observation encBool))
  let hlbl := hs.mapWithInput ((ComputableInPolyTime.snd _ _).trans (.snd observation encBool))
  hseed.bind_with
    (hobs.prod (p1.prod (((p0.prod p1).prod (hlbl.trans .listToBits)).trans hhash))).isPPTOn

/-- Arbitrary encoded labels use the same extractor, with list encoding charged to the hash. -/
theorem isPPTOn_extractLabels_list {Param Observation Label Seed Output : Type}
    {input : Param ↪ List Bool} {observation : Observation ↪ List Bool} {label : Label ↪ List Bool}
    {key : Seed ↪ List Bool} {output : Output ↪ List Bool}
    {seed : Param → ProbComp Seed} {hash : Param → Seed → List Label → Output}
    {samples : Param → List (Observation × Label)}
    (hseed : IsPPTOn input key seed)
    (hhash : ComputableInPolyTime (fun pair => hash pair.1.1 pair.1.2 pair.2)
      (encPair (encPair input key) (encList label)) output)
    (hsamples : ComputableInPolyTime samples input (encList (encPair observation label))) :
    IsPPTOn input (encPair (encList observation) (encPair key output))
      (fun a => extractLabels (seed a) (hash a) (samples a)) :=
  let p0 := ComputableInPolyTime.fst input key; let p1 := ComputableInPolyTime.snd input key
  let hs := p0.trans hsamples
  let hobs := hs.mapWithInput ((ComputableInPolyTime.snd _ _).trans (.fst observation label))
  let hlbl := hs.mapWithInput ((ComputableInPolyTime.snd _ _).trans (.snd observation label))
  hseed.bind_with (hobs.prod (p1.prod (((p0.prod p1).prod hlbl).trans hhash))).isPPTOn

attribute [program_certificate hseed hsamples] isPPTOn_extractLabels isPPTOn_extractLabels_list

/-- Repeated program sampling and list-based extraction have the finite product experiment's
exact law. Only the representation of the observation tuple changes. -/
theorem eval_replicate_extractLabels {Observation Label Seed Output : Type}
    [Finite Observation] [Finite Label]
    (source : ProbComp (Observation × Label)) (count : ℕ) (seed : ProbComp Seed)
    (hash : Seed → List Label → Output) :
    ProbComp.eval (extractLabelsReal source count seed hash) =
      ((PMF.pi (fun _ : Fin count => ProbComp.eval source)).bind (fun outcome =>
        (ProbComp.eval seed).map (fun s =>
          (fun i => (outcome i).1, s, hash s (List.ofFn (fun i => (outcome i).2)))))).map
        (fun result => (List.ofFn result.1, result.2)) := by
  simp only [pmf_norm, ProbComp.eval_replicate, extractLabels, bind_pure_comp, List.map_ofFn]

/-- Extraction error for the supplied test is the only loss when converting its distinguishing
advantage into a gap between original and comparison sample sequences. The hash seed is public. -/
theorem extractLabels_sequence_gap_of_extraction_le {Observation Label Seed Output : Type}
    (original comparison : ProbComp (Observation × Label)) (count : ℕ)
    (seed : ProbComp Seed) (hash : Seed → List Label → Output)
    (test : List Observation × Seed × Output → ProbComp Bool)
    (ideal : PMF (List Observation × Seed × Output)) {ε : ℝ}
    (hclose : (Game.advantage
      ((ProbComp.eval (extractLabelsReal comparison count seed hash)).bind
        (fun output => ProbComp.eval (test output)))
      (ideal.bind (fun output => ProbComp.eval (test output))) : ℝ) ≤ ε) :
    let reduced := fun samples => extractLabels seed hash samples >>= test
    (Game.advantage (ProbComp.eval (OracleComp.replicate count original >>= reduced))
        (ideal.bind (fun output => ProbComp.eval (test output))) : ℝ) - ε ≤
      (Game.advantage (ProbComp.eval (OracleComp.replicate count original >>= reduced))
        (ProbComp.eval (OracleComp.replicate count comparison >>= reduced)) : ℝ) := by
  dsimp only
  have hreal := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (ProbComp.eval (OracleComp.replicate count original >>=
      fun samples => extractLabels seed hash samples >>= test))
    ((ProbComp.eval (extractLabelsReal comparison count seed hash)).bind
      (fun output => ProbComp.eval (test output)))
    (ideal.bind (fun output => ProbComp.eval (test output))))
  rw [NNReal.coe_add] at hreal
  simpa only [ProbComp.eval_bind, PMF.bind_bind] using
    sub_le_iff_le_add.mpr (hreal.trans (add_le_add le_rfl hclose))

/-- The list-based extractor inherits the conditional Shannon-entropy bound for repeated
samples against every randomized finite-output test. The test receives all observations and
the independent seed. It has no efficiency restriction. -/
theorem extractLabels_dist_bind_le {Observation Label Seed Output : Type}
    [Finite Observation] [Finite Label]
    [Finite Seed] [Fintype Output] [Nonempty Output]
    (source : ProbComp (Observation × Label)) (count informationBits : ℕ)
    (hsource : ∀ pair ∈ (ProbComp.eval source).support,
      (2 : ℝ) ^ (-(informationBits : ℝ)) ≤ (ProbComp.eval source pair).toReal)
    (seed : ProbComp Seed) (hash : Seed → List Label → Output)
    (hhash : IsTwoUniversal (ProbComp.eval seed)
      (fun s (bits : Fin count → Label) => hash s (List.ofFn bits))) {δ slack : ℝ}
    (hentropy : δ ≤ conditionalEntropy (ProbComp.eval source)) (hslack : 0 ≤ slack)
    {Result : Type*} [Fintype Result] (test : List Observation × Seed × Output → PMF Result) :
    dist ((ProbComp.eval (extractLabelsReal source count seed hash)).bind test)
      ((extractLabelsIdeal (Output := Output) (Prod.fst <$> source) count seed).bind test) ≤
      2 * Real.exp (-2 * slack ^ 2 / (count * (informationBits : ℝ) ^ 2)) +
        Real.sqrt (Fintype.card Output * (2 * (2 : ℝ) ^ (-(count * δ - slack)))) / 2 := by
  let := Fintype.ofFinite Observation
  let := Fintype.ofFinite Seed
  have h := hhash.leftover_hash_pi_conditional (fun _ : Fin count => ProbComp.eval source)
    (bound := informationBits) (by positivity) (fun _ => hsource) hslack
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hmap := (dist_bind_le _ _
    (fun result : (Fin count → Observation) × Seed × Output =>
      test (List.ofFn result.1, result.2))).trans h
  simp only [pmf_norm, extractLabelsIdeal, eval_replicate_extractLabels, ProbComp.eval_replicate,
    monad_bind_eq_bind] at hmap ⊢
  exact hmap.trans (by gcongr; norm_num)

/-- Extracting into a singleton is exactly ideal, including its public observations and seed.
This handles a zero-bit component without requiring a positive entropy budget. -/
theorem eval_extractLabels_of_subsingleton {Observation Label Seed Output : Type}
    [Fintype Output] [Nonempty Output] [Subsingleton Output]
    (source : ProbComp (Observation × Label)) (count : ℕ) (seed : ProbComp Seed)
    (hash : Seed → List Label → Output) :
    ProbComp.eval (extractLabelsReal source count seed hash) =
      extractLabelsIdeal (Output := Output) (Prod.fst <$> source) count seed := by
  classical
  have huniform (value : Output) : PMF.uniformOfFintype Output = PMF.pure value := by
    let : Unique Output := { default := value, uniq := fun _ => Subsingleton.elim _ _ }
    ext result
    simp [PMF.uniformOfFintype_apply, PMF.pure_apply, Fintype.card_unique,
      Subsingleton.elim result value]
  simp only [pmf_norm, extractLabelsIdeal, OracleComp.replicate_map, extractLabels, bind_pure_comp,
    monad_bind_eq_bind]
  congr 1 with samples : 1; rw [PMF.map]
  congr 1 with key : 1
  rw [huniform (hash key (samples.map Prod.snd)), PMF.pure_map]
  rfl

open Filter in
/-- A shared repetition schedule makes conditional extraction statistically uniform. A
zero-bit output is always permitted; positive lengths reserve two slacks below conditional
entropy. Every randomized Boolean test is admissible, with no computability assumption on
entropy or its numerical bound. -/
theorem extractLabels_indistinguishable {Observation Label Seed : ℕ → Type}
    [∀ n, Finite (Observation n)] [∀ n, Finite (Label n)] [∀ n, Finite (Seed n)]
    (source : ∀ n, ProbComp (Observation n × Label n))
    (sourceBits inverseSlack outputBits : ℕ → ℕ)
    (hmass : ∀ n value, value ∈ (ProbComp.eval (source n)).support →
      (2 : ℝ) ^ (-(sourceBits n : ℝ)) ≤ (ProbComp.eval (source n) value).toReal)
    (seed : ∀ n, ProbComp (Seed n)) (hash : ∀ n, Seed n → List (Label n) → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (seed n))
      (fun key (values : Fin (ExtractionSchedule.count n (sourceBits n) (inverseSlack n)) →
        Label n) => hash n key (List.ofFn values)))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (sourceBits n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (sourceBits n) (inverseSlack n) *
          conditionalEntropy (ProbComp.eval (source n))) :
    Game.Indistinguishable
      (fun (test : ∀ n, List (Observation n) × Seed n × BitString (outputBits n) → Game) n =>
        (ProbComp.eval (extractLabelsReal (source n)
          (ExtractionSchedule.count n (sourceBits n) (inverseSlack n)) (seed n) (hash n))).bind
            (test n))
      (fun test n => (extractLabelsIdeal (Output := BitString (outputBits n))
        (Prod.fst <$> source n) (ExtractionSchedule.count n (sourceBits n) (inverseSlack n))
          (seed n)).bind (test n)) (fun _ => True) := by
  intro test _
  apply negligible_of_eventually_le ExtractionSchedule.error_negligible
  filter_upwards [hbudget] with n hn
  apply NNReal.coe_le_coe.mp
  rw [Game.advantage_eq_nndist, coe_nndist]
  rcases hn with hzero | hbudget
  · have : Subsingleton (BitString (outputBits n)) := by rw [hzero]; infer_instance
    rw [eval_extractLabels_of_subsingleton, dist_self]
    exact (ExtractionSchedule.error n).coe_nonneg
  · have hmass' (value) (hvalue : value ∈ (ProbComp.eval (source n)).support) :
        (2 : ℝ) ^ (-((sourceBits n + n + 2 : ℕ) : ℝ)) ≤
          (ProbComp.eval (source n) value).toReal :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (neg_le_neg (by exact_mod_cast (by lia : sourceBits n ≤ sourceBits n + n + 2)))).trans
          (hmass n value hvalue)
    have h := extractLabels_dist_bind_le (source n)
      (ExtractionSchedule.count n (sourceBits n) (inverseSlack n)) (sourceBits n + n + 2)
      hmass' (seed n) (hash n) (hhash n) le_rfl
      (Nat.cast_nonneg (ExtractionSchedule.slack n (sourceBits n) (inverseSlack n))) (test n)
    apply h.trans
    simpa only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat] using ExtractionSchedule.error_le n (sourceBits n) (inverseSlack n)
        (outputBits n) (conditionalEntropy (ProbComp.eval (source n))) hbudget

open Filter in
/-- Unconditional extraction is the constant-observation specialization. It hashes ordinary
lists and reveals the entire seed; zero-bit outputs need no entropy. -/
theorem seededHash_replicate_indistinguishable {Label Seed : ℕ → Type}
    [∀ n, Finite (Label n)] [∀ n, Finite (Seed n)]
    (source : ∀ n, ProbComp (Label n)) (sourceBits inverseSlack outputBits : ℕ → ℕ)
    (hmass : ∀ n value, value ∈ (ProbComp.eval (source n)).support →
      (2 : ℝ) ^ (-(sourceBits n : ℝ)) ≤ (ProbComp.eval (source n) value).toReal)
    (seed : ∀ n, ProbComp (Seed n)) (hash : ∀ n, Seed n → List (Label n) → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (seed n))
      (fun key (values : Fin (ExtractionSchedule.count n (sourceBits n) (inverseSlack n)) →
        Label n) => hash n key (List.ofFn values)))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (sourceBits n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (sourceBits n) (inverseSlack n) *
          entropy (ProbComp.eval (source n))) :
    Game.Indistinguishable
      (fun (test : ∀ n, Seed n × BitString (outputBits n) → Game) n =>
        (seededHash (ProbComp.eval (seed n))
          (ProbComp.eval (OracleComp.replicate
            (ExtractionSchedule.count n (sourceBits n) (inverseSlack n)) (source n)))
              (hash n)).bind (test n))
      (fun test n => do
        let result ← do
          let key ← ProbComp.eval (seed n)
          (PMF.uniformOfFintype (BitString (outputBits n))).map (key, ·)
        test n result) (fun _ => True) := by
  intro test _
  have h := extractLabels_indistinguishable
    (fun n => ((), ·) <$> source n) sourceBits inverseSlack outputBits
    (by
      intro n value hvalue
      simp only [ProbComp.eval_map] at hvalue ⊢
      obtain ⟨label, hlabel, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hvalue
      exact (hmass n label hlabel).trans (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
        (le_map_apply (ProbComp.eval (source n)) ((), ·) label))) seed hash hhash
    (by simpa only [ProbComp.eval_map, conditionalEntropy_map_const] using hbudget)
  refine (h (fun n result => test n result.2) trivial).congr'
    (Filter.Eventually.of_forall fun n => ?_)
  dsimp only
  have hideal := congrArg (fun law => law.bind (test n))
    (extractLabelsIdeal_map_snd (Output := BitString (outputBits n))
      (Prod.fst <$> (((), ·) <$> source n))
      (ExtractionSchedule.count n (sourceBits n) (inverseSlack n)) (seed n))
  simp only [PMF.bind_map, Function.comp_def] at hideal
  rw [hideal]
  refine congrArg₂ Game.advantage ?_ (by simp only [monad_bind_eq_bind, PMF.bind_bind])
  simp only [pmf_norm, OracleComp.replicate_map, extractLabels, bind_pure_comp, List.map_map,
    List.map_id_fun', id_eq, seededHash_eq_bind]

end Cslib.Crypto.Pseudoentropy
