/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Crypto.Computational.GeneratorReindex
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.Signature
public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.CoinTape
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.PMF

/-!
# Equivalence between one-way functions and one-time digital signatures, and necessity for EUF-CMA

This module establishes the foundational reductions connecting one-way functions (`OneWay`) and
uniform digital signature schemes (`SignatureScheme`):

1. **Secure signatures imply one-way functions (`SignatureScheme.OneTimeEUFCMA.exists_oneWay`,
   `SignatureScheme.EUFCMA.exists_oneWay`)**: for any digital signature scheme `S` that is
   existentially unforgeable under one-time (or full adaptive) chosen-message attack, reindexing the
   seeded key-generation evaluator `(seed ↦ (n, (evaluate n seed).1))` across all input lengths via
   `GeneratorReindex.parameter` yields a one-way function. Any PPT inverter for this function gives
   a zero-query PPT forger that recovers a valid secret key for the challenge public key and signs
   `0^n`.
2. **Lamport's one-time signature scheme from any one-way function (`lamportScheme`,
   `OneWay.oneTimeEUFCMA_lamport`, `OneWay.exists_oneTimeSignature`)**: given any polynomial-time
   function `f : List Bool → List Bool`, `lamportScheme f` samples `2n` independent `n`-bit secret
   words, publishes their `f`-images as the verification key, and signs an `n`-bit message by
   revealing one secret word per message bit. When `f` is one-way (`OneWay f`), `lamportScheme f`
   is one-time EUF-CMA secure (`OneTimeEUFCMA`): any one-time forger must forge a preimage at some
   pair `(i, msg[i])` that was never revealed by the single signing query.
3. **Equivalence (`exists_oneWay_iff_exists_oneTimeSignature`)**: a one-way function exists if and
   only if a one-time EUF-CMA secure signature scheme exists.

Together with `SignatureScheme.EUFCMA.oneTimeEUFCMA`, this establishes the necessity half of
Rompel's theorem (`(∃ S, S.EUFCMA) → ∃ f, OneWay f`) and the one-time sufficiency half
(`(∃ f, OneWay f) ↔ (∃ S, S.OneTimeEUFCMA)`). Upgrading one-time signatures to stateless many-time
EUF-CMA signatures from arbitrary one-way functions requires Rompel's construction of universal
one-way hash functions and GMR/Merkle authentication trees.

## Main definitions

* `Cslib.Crypto.lamportKeyGen`, `lamportSign`, `lamportVerify`, `lamportScheme`: Lamport's one-time
  digital signature scheme built from any polynomial-time function `f`.
* `Cslib.Crypto.lamportInverter`: reduction inverting `f` from a one-time forger against
  `lamportScheme f`.

## Main results

* `Cslib.Crypto.SignatureScheme.OneTimeEUFCMA.exists_oneWay`: any one-time EUF-CMA secure signature
  scheme implies the existence of a one-way function.
* `Cslib.Crypto.SignatureScheme.EUFCMA.exists_oneWay`: any full EUF-CMA secure signature scheme
  implies the existence of a one-way function.
* `Cslib.Crypto.OneWay.oneTimeEUFCMA_lamport`: Lamport's scheme constructed from a one-way function
  is one-time EUF-CMA secure.
* `Cslib.Crypto.OneWay.exists_oneTimeSignature`: any one-way function implies the existence of a
  one-time EUF-CMA secure signature scheme.
* `Cslib.Crypto.exists_oneWay_iff_exists_oneTimeSignature`: equivalence between one-way functions
  and one-time EUF-CMA secure signature schemes.

## References

* [L. Lamport, *Constructing Digital Signatures from a One-Way Function*][Lamport1979]
* [S. Goldwasser, S. Micali, R. L. Rivest, *A Digital Signature Scheme Secure Against Adaptive
  Chosen-Message Attacks*][GoldwasserMicaliRivest1988]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
-/

public section

namespace Cslib.Crypto

open Filter ProbComp Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

private theorem uConstMul {γ : Type} {encIn : γ ↪ List Bool} (c : ℕ) {f : γ → ℕ}
    (hf : ComputableInPolyTime f encIn encUnary) :
    ComputableInPolyTime (fun a => c * f a) encIn encUnary :=
  ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const c).prod hf)

private theorem computableInPolyTime_frames {γ : Type} {encIn : γ ↪ List Bool}
    {w : γ → List Bool} (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun a => frames (w a)) encIn (encList encBits) :=
  computableInDegree_frames.computableInPolyTime.comp hw

/-! ### Secure digital signatures imply one-way functions -/

private theorem succProbability_le_dyadicSize_mul (trial : ℕ → Game) {bound size : ℕ}
    (hlt : size < dyadicSize bound) :
    Game.succProbability (trial size) ≤
      (dyadicSize bound : ℝ≥0) *
        Game.succProbability ((PMF.uniformOfFintype (Fin (dyadicSize bound))).bind
          (fun idx => trial idx.val)) := by
  have hpos : (0 : ℝ≥0) < dyadicSize bound := by exact_mod_cast dyadicSize_pos bound
  rw [Game.succProbability_uniform, Fintype.card_fin, mul_div_cancel₀ _ hpos.ne']
  exact Finset.single_le_sum
    (f := fun i : Fin (dyadicSize bound) => Game.succProbability (trial i.val))
    (fun _ _ => zero_le) (Finset.mem_univ (⟨size, hlt⟩ : Fin (dyadicSize bound)))

private noncomputable def sigToOwfForgerBody (S : SignatureScheme)
    (evaluate : ℕ → List Bool → List Bool × List Bool) (schedule : ℕ → ℕ)
    (adversary : Inverter) (n : ℕ) (pk : List Bool) : ProbComp (List Bool × List Bool) := do
  let size ← sampleDyadicIndex (schedule (n + 1))
  let cand ← adversary size (encPair encUnary encBits (n, pk))
  let msg := List.replicate n false
  let sig ← S.sign (evaluate n cand).2 msg
  return (msg, sig)

private theorem isPPTOn_sigToOwfForgerBody (S : SignatureScheme)
    {evaluate : ℕ → List Bool → List Bool × List Bool}
    (heval : ComputableInPolyTime (fun p : ℕ × List Bool => evaluate p.1 p.2)
      (encPair encUnary encBits) (encPair encBits encBits))
    {schedule : ℕ → ℕ} (hsched : ComputableInPolyTime schedule encUnary encUnary)
    {adversary : Inverter} (hadversary : IsPPT encBits adversary) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p : ℕ × List Bool => sigToOwfForgerBody S evaluate schedule adversary p.1 p.2) := by
  unfold sigToOwfForgerBody
  have hidx : IsPPTOn (encPair encUnary encBits) encUnary
      (fun p : ℕ × List Bool => sampleDyadicIndex (schedule (p.1 + 1))) :=
    isPPTOn_sampleDyadicIndex (hsched.comp
      (ComputableInPolyTime.unary_add.comp
        ((ComputableInPolyTime.fst encUnary encBits).prod (.const 1))))
  have hprep_cand : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × ℕ => (q.2, encPair encUnary encBits (q.1.1, q.1.2)))
      (encPair (encPair encUnary encBits) encUnary) (encPair encUnary encBits) :=
    (ComputableInPolyTime.snd (encPair encUnary encBits) encUnary).prod
      (ComputableInPolyTime.fst (encPair encUnary encBits) encUnary).encoding_comp
  have hcand : IsPPTOn (encPair (encPair encUnary encBits) encUnary) encBits
      (fun q : (ℕ × List Bool) × ℕ =>
        adversary q.2 (encPair encUnary encBits (q.1.1, q.1.2))) :=
    hadversary.on.preprocess hprep_cand
  have hn : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × ℕ) × List Bool => r.1.1.1)
      (encPair (encPair (encPair encUnary encBits) encUnary) encBits) encUnary :=
    (ComputableInPolyTime.fst encUnary encBits).comp
      ((ComputableInPolyTime.fst (encPair encUnary encBits) encUnary).comp
        (ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encUnary) encBits))
  have hsk : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × ℕ) × List Bool => (evaluate r.1.1.1 r.2).2)
      (encPair (encPair (encPair encUnary encBits) encUnary) encBits) encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp (heval.comp
      (hn.prod (ComputableInPolyTime.snd
        (encPair (encPair encUnary encBits) encUnary) encBits)))
  have hmsg : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × ℕ) × List Bool => List.replicate r.1.1.1 false)
      (encPair (encPair (encPair encUnary encBits) encUnary) encBits) encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp hn
  have hsig : IsPPTOn (encPair (encPair (encPair encUnary encBits) encUnary) encBits)
      (encPair encBits encBits)
      (fun r : ((ℕ × List Bool) × ℕ) × List Bool => do
        let sig ← S.sign (evaluate r.1.1.1 r.2).2 (List.replicate r.1.1.1 false)
        return (List.replicate r.1.1.1 false, sig)) :=
    (S.isPPTOn_sign_comp hsk hmsg).bind_with
      ((hmsg.comp (ComputableInPolyTime.fst _ encBits)).prod
        (ComputableInPolyTime.snd _ encBits)).isPPTOn
  exact hidx.bind_with (hcand.bind_with hsig)

/-- Any digital signature scheme that is existentially unforgeable under one-time chosen-message
attack (`OneTimeEUFCMA`) implies the existence of a one-way function. -/
theorem SignatureScheme.OneTimeEUFCMA.exists_oneWay {S : SignatureScheme}
    (hS : S.OneTimeEUFCMA) : ∃ f, OneWay f := by
  obtain ⟨c, d, evaluate, heval, hsupp, hlaw⟩ := S.keyGen_ppt.exists_total_seeded_evaluator
  let schedule (n : ℕ) : ℕ := c * (n + 1) ^ d + n + 1
  let param (size : ℕ) : ℕ := GeneratorReindex.parameter schedule size
  let f (seed : List Bool) : List Bool :=
    encPair encUnary encBits (param seed.length, (evaluate (param seed.length) seed).1)
  have hsched : ComputableInPolyTime schedule encUnary encUnary := by
    dsimp only [schedule]
    fun_prop
  have hparam_unary : ComputableInPolyTime param encUnary encUnary :=
    GeneratorReindex.isPolyTime_parameter hsched .id'
  have hparam : ComputableInPolyTime (fun seed : List Bool => param seed.length)
      encBits encUnary :=
    hparam_unary.comp ComputableInPolyTime.length_bits
  have hpk : ComputableInPolyTime
      (fun seed : List Bool => (evaluate (param seed.length) seed).1) encBits encBits :=
    (ComputableInPolyTime.fst encBits encBits).comp (heval.comp (hparam.prod .id'))
  have hf : ComputableInPolyTime f encBits encBits :=
    (hparam.prod hpk).encoding_comp
  refine ⟨f, OneWay.of_inversion_negligible hf ?_⟩
  intro adversary hadversary
  let forger : Forger := fun n pk =>
    ProbOracleComp.sample (sigToOwfForgerBody S evaluate schedule adversary n pk)
  have hforger : IsOraclePPT (encPair encBits encBits) forger :=
    (isPPTOn_sigToOwfForgerBody S heval hsched hadversary).isOraclePPTOn.isOraclePPT
  have hforger_neg := hS.negligible forger hforger
  have hscaled : Negligible (fun n =>
      (dyadicSize (schedule (n + 1)) : ℝ≥0) *
        Game.succProbability (ProbComp.eval (S.eufOneTimeGame forger n))) :=
    hforger_neg.polynomiallyBounded_mul
      (dyadicSize_polynomiallyBounded.comp
        (hsched.polynomiallyBounded.comp (PolynomiallyBounded.id.add (.const 1))))
  have hge : ∀ n, n + 1 ≤ schedule n := fun n => by dsimp [schedule]; lia
  have hdecay := hscaled.comp_of_polynomial_bound (GeneratorReindex.parameter_tendsto schedule)
    (hsched.polynomiallyBounded.comp (PolynomiallyBounded.id.add (.const 1)))
    (Eventually.of_forall fun size => (GeneratorReindex.lt_length_succ_parameter hge size).le)
  apply negligible_of_eventually_le hdecay
  filter_upwards [eventually_ge_atTop (schedule 0)] with size hsize
  set n := param size
  have hfits : schedule n ≤ size := GeneratorReindex.parameter_fits hsize
  have hbudget : c * ((encUnary n).length + 1) ^ d ≤ size := by
    simp only [encUnary_apply, List.length_replicate]
    dsimp [schedule] at hfits
    lia
  have hlt_dyadic : size < dyadicSize (schedule (n + 1)) :=
    (GeneratorReindex.lt_length_succ_parameter hge size).trans (lt_dyadicSize (schedule (n + 1)))
  let trial (idx : ℕ) : PMF Bool := do
    let keys ← ProbComp.eval (S.keyGen n)
    let cand ← ProbComp.eval (adversary idx (encPair encUnary encBits (n, keys.1)))
    (ProbComp.eval (S.sign (evaluate n cand).2 (List.replicate n false))).map fun sig =>
      S.verify keys.1 (List.replicate n false) sig
  have hgame_eq : ProbComp.eval (S.eufOneTimeGame forger n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (schedule (n + 1))))).bind
        (fun idx => trial idx.val) := by
    simp only [pmf_norm, SignatureScheme.eufOneTimeGame, forger, sigToOwfForgerBody,
      ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_sample,
      eval_sampleDyadicIndex, List.length_replicate, beq_self_eq_true, Bool.true_and]
    rw [PMF.bind_comm]
    rfl
  have hstep1 : Game.succProbability (ProbComp.eval (inversionGame f adversary size)) ≤
      Game.succProbability (trial size) := by
    apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
    dsimp only [trial, inversionGame]
    rw [hlaw n size hbudget, PMF.monad_bind_eq_bind, PMF.bind_map]
    simp only [pmf_norm, BitString.eval_sampleList]
    refine PMF.bind_apply_mono_on_support _ true fun seed hseed => ?_
    have hseed_len : seed.length = size := BitString.length_of_mem_support_uniformList hseed
    have hf_seed : f seed = encPair encUnary encBits (n, (evaluate n seed).1) := by
      simp [f, hseed_len, n]
    rw [hf_seed]
    refine PMF.bind_apply_mono_on_support _ true fun cand _ => ?_
    by_cases hwin : (f cand == encPair encUnary encBits (n, (evaluate n seed).1)) = true
    · rw [hwin]
      have hinj := (encPair encUnary encBits).injective (beq_iff_eq.mp hwin)
      have hparam_cand : param cand.length = n := congrArg Prod.fst hinj
      have hpk_cand : (evaluate n cand).1 = (evaluate n seed).1 :=
        hparam_cand ▸ congrArg Prod.snd hinj
      rw [PMF.map]
      refine PMF.le_bind_apply_on_support _ fun sig hsig => ?_
      have hver := S.verify_sign n (evaluate n cand) (hsupp n cand)
        (List.replicate n false) (by simp) sig hsig
      simp [hpk_cand ▸ hver]
    · rw [Bool.eq_false_iff.mpr hwin]
      simp
  exact hstep1.trans (hgame_eq ▸ succProbability_le_dyadicSize_mul trial hlt_dyadic)

/-- Any digital signature scheme that is existentially unforgeable under adaptive chosen-message
attack (`EUFCMA`) implies the existence of a one-way function. -/
theorem SignatureScheme.EUFCMA.exists_oneWay {S : SignatureScheme} (hS : S.EUFCMA) :
    ∃ f, OneWay f :=
  hS.oneTimeEUFCMA.exists_oneWay

/-! ### Lamport's one-time signature scheme from any one-way function -/

/-- Lamport key generation: sample `2n` independent `n`-bit secret words, publish their `f`-images
as the framed public key, and keep the framed secret words as the signing key. -/
@[expose] noncomputable def lamportKeyGen (f : List Bool → List Bool) (n : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let skWords ← OracleComp.replicate (2 * n) (BitString.sampleList n)
  return (encList encBits (skWords.map f), encList encBits skWords)

/-- Lamport signing: decode the secret key into `2n` words and, when the message length matches,
reveal word `2 * i + msg[i].toNat` for each bit position `i < msg.length`. -/
@[expose] def lamportSign (sk msg : List Bool) : ProbComp (List Bool) :=
  let skWords := frames sk
  pure <|
    if skWords.length == 2 * msg.length then
      encList encBits ((List.range msg.length).map fun i =>
        skWords.getD (2 * i + (msg.getD i false).toNat) [])
    else
      []

/-- Lamport verification: decode the public key into `2n` blocks and the signature into `n` blocks,
and check that `f (sigWords[i]) = pkWords[2 * i + msg[i].toNat]` for every `i < msg.length`. -/
@[expose] def lamportVerify (f : List Bool → List Bool) (pk msg sig : List Bool) : Bool :=
  let pkWords := frames pk
  let sigWords := frames sig
  (pkWords.length == 2 * msg.length) && (sigWords.length == msg.length) &&
    (List.range msg.length).all fun i =>
      f (sigWords.getD i []) == pkWords.getD (2 * i + (msg.getD i false).toNat) []

private theorem computableInPolyTime_lamportSlot {γ : Type} {encIn : γ ↪ List Bool}
    {words : γ → List (List Bool)} {msg : γ → List Bool}
    (hwords : ComputableInPolyTime words encIn (encList encBits))
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    ComputableInPolyTime
      (fun a : γ × ℕ => (words a.1).getD (2 * a.2 + ((msg a.1).getD a.2 false).toNat) [])
      (encPair encIn encUnary) encBits := by
  have hp1 := ComputableInPolyTime.fst encIn encUnary
  have hi := ComputableInPolyTime.snd encIn encUnary
  exact ComputableInPolyTime.listGetDWithInput (hwords.comp hp1)
    (ComputableInPolyTime.unary_add.comp ((uConstMul 2 hi).prod
      ((ComputableInPolyTime.of_finite Bool.toNat).comp
        (ComputableInPolyTime.bitsGetDWithInput (hmsg.comp hp1) hi false))))
    []

@[program_certificate]
theorem isPPTOn_lamportKeyGen {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) :
    IsPPTOn encUnary (encPair encBits encBits) (lamportKeyGen f) := by
  unfold lamportKeyGen
  have hrep : IsPPTOn encUnary (encList encBits)
      (fun n : ℕ => OracleComp.replicate (2 * n) (BitString.sampleList n)) :=
    (ComputableInPolyTime.id'.sampleList).replicate (uConstMul 2 .id')
  have hpost : ComputableInPolyTime
      (fun skWords : List (List Bool) => (encList encBits (skWords.map f), encList encBits skWords))
      (encList encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.map hf).encoding_comp.prod ComputableInPolyTime.id'.encoding_comp
  exact hrep.bind hpost.isPPTOn

@[program_certificate]
theorem isPPTOn_lamportSign :
    IsPPTOn (encPair encBits encBits) encBits (fun p => lamportSign p.1 p.2) := by
  have hsk := computableInPolyTime_frames (ComputableInPolyTime.fst encBits encBits)
  have hmsg := ComputableInPolyTime.snd encBits encBits
  have hmsg_len := ComputableInPolyTime.length_bits.comp hmsg
  have hbody := (ComputableInPolyTime.mapWithInput (encA := encUnary)
      (f := fun (p : List Bool × List Bool) i =>
        (frames p.1).getD (2 * i + (p.2.getD i false).toNat) [])
      (ComputableInPolyTime.range.comp hmsg_len)
      (computableInPolyTime_lamportSlot hsk hmsg)).encoding_comp
  exact (ComputableInPolyTime.ite'
    (ComputableInPolyTime.unary_beq'
      ((ComputableInPolyTime.length_list encBits).comp hsk)
      (uConstMul 2 hmsg_len))
    hbody (.const [])).isPPTOn

@[program_certificate]
theorem computableInPolyTime_lamportVerify {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool => lamportVerify f p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBool := by
  let encIn := encPair encBits (encPair encBits encBits)
  have hpk := computableInPolyTime_frames
    (ComputableInPolyTime.fst encBits (encPair encBits encBits))
  have hrest := ComputableInPolyTime.snd encBits (encPair encBits encBits)
  have hmsg := (ComputableInPolyTime.fst encBits encBits).comp hrest
  have hsig := computableInPolyTime_frames
    ((ComputableInPolyTime.snd encBits encBits).comp hrest)
  have hmsg_len := ComputableInPolyTime.length_bits.comp hmsg
  have hp1 := ComputableInPolyTime.fst encIn encUnary
  have hi := ComputableInPolyTime.snd encIn encUnary
  have hall := ComputableInPolyTime.allWithInput (encA := encUnary)
    (test := fun (p : List Bool × List Bool × List Bool) i =>
      f ((frames p.2.2).getD i []) ==
        (frames p.1).getD (2 * i + (p.2.1.getD i false).toNat) [])
    (ComputableInPolyTime.range.comp hmsg_len)
    ((hf.comp (ComputableInPolyTime.listGetDWithInput (hsig.comp hp1) hi [])).beq
      (computableInPolyTime_lamportSlot hpk hmsg))
  exact ComputableInPolyTime.bool_and.comp
    ((ComputableInPolyTime.bool_and.comp
      ((ComputableInPolyTime.unary_beq'
        ((ComputableInPolyTime.length_list encBits).comp hpk)
        (uConstMul 2 hmsg_len)).prod
        (ComputableInPolyTime.unary_beq'
          ((ComputableInPolyTime.length_list encBits).comp hsig)
          hmsg_len))).prod hall)

@[simp]
private theorem frames_encList_bits (l : List (List Bool)) :
    frames (encList encBits l) = l := by
  rw [frames_encList]
  exact List.map_id l

theorem lamportVerify_lamportSign (f : List Bool → List Bool) (n : ℕ)
    (keys : List Bool × List Bool) (hkeys : keys ∈ (ProbComp.eval (lamportKeyGen f n)).support)
    (msg : List Bool) (hmsg : msg.length = n)
    (sig : List Bool) (hsig : sig ∈ (ProbComp.eval (lamportSign keys.2 msg)).support) :
    lamportVerify f keys.1 msg sig = true := by
  simp only [lamportKeyGen, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkeys
  obtain ⟨skWords, hskWords, rfl⟩ := hkeys
  obtain ⟨hskLen, _⟩ := (ProbComp.mem_support_replicate_iff _ _ _).mp hskWords
  simp only [lamportSign, frames_encList_bits, hskLen, hmsg, beq_self_eq_true, ↓reduceIte,
    ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
  subst hsig
  simp only [lamportVerify, frames_encList_bits, List.length_map, List.length_range, hskLen, hmsg,
    beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi
  have h2i : 2 * i + (msg.getD i false).toNat < (skWords.map f).length := by
    rw [List.length_map, hskLen]
    have := Bool.toNat_le (msg.getD i false)
    omega
  have h2i' : 2 * i + (msg.getD i false).toNat < skWords.length := by
    rw [List.length_map] at h2i
    exact h2i
  have hi_range : i < (List.range n).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi_range), List.getElem_map, List.getElem_range,
    List.getD_eq_getElem _ _ h2i, List.getElem_map, List.getD_eq_getElem _ _ h2i']

/-- Lamport's one-time digital signature scheme built from any polynomial-time function `f`. -/
@[expose] noncomputable def lamportScheme (f : List Bool → List Bool)
    (hf : ComputableInPolyTime f encBits encBits) : SignatureScheme where
  keyGen := lamportKeyGen f
  sign := lamportSign
  verify := lamportVerify f
  keyGen_ppt := isPPTOn_lamportKeyGen hf
  sign_ppt := isPPTOn_lamportSign
  verify_polyTime := (computableInPolyTime_lamportVerify hf)
  verify_sign := lamportVerify_lamportSign f

/-! ### Security reduction for Lamport's one-time signature scheme -/

private theorem two_mul_add_toNat_div_two (i : ℕ) (b : Bool) :
    (2 * i + b.toNat) / 2 = i := by
  have hb := Bool.toNat_le b
  omega

private theorem eval_replicate_split {α : Type} (prog : ProbComp α) {m j : ℕ} (hj : j < m) :
    ProbComp.eval (OracleComp.replicate m prog) =
      (do
        let xStar ← ProbComp.eval prog
        let front ← ProbComp.eval (OracleComp.replicate j prog)
        (ProbComp.eval (OracleComp.replicate (m - j - 1) prog)).map fun back =>
          front ++ xStar :: back) := by
  have hm : m = j + (m - j - 1 + 1) := by omega
  conv_lhs => rw [hm, OracleComp.replicate_add, OracleComp.replicate_succ]
  simp only [pmf_norm]
  rw [PMF.bind_comm]
  rfl

private def agreeAt (n j : ℕ) (req : List Bool) : Prop :=
  req.length = n → ∀ k ∈ List.range n, 2 * k + (req.getD k false).toNat ≠ j

private theorem lamportSign_eq_of_agreeAt {n j : ℕ} (hj : j < 2 * n)
    {w : List (List Bool)} (hw : w.length = 2 * n) {req : List Bool}
    (hagree : agreeAt n j req) :
    lamportSign (encList encBits w) req =
      lamportSign (encList encBits (w.take j ++ [] :: w.drop (j + 1))) req := by
  have hsplit : w = w.take j ++ w.getD j [] :: w.drop (j + 1) := by
    rw [List.getD_eq_getElem _ _ (by omega : j < w.length),
      List.getElem_cons_drop, List.take_append_drop]
  have htake_len : (w.take j).length = j := List.length_take_of_le (by omega)
  have hlen2 : (w.take j ++ [] :: w.drop (j + 1)).length = 2 * n := by
    have hlen1 : (w.take j ++ w.getD j [] :: w.drop (j + 1)).length = 2 * n := by
      rw [← hsplit, hw]
    simp only [List.length_append, List.length_cons] at hlen1 ⊢
    exact hlen1
  simp only [lamportSign, frames_encList_bits, hw, hlen2]
  split_ifs with hreq
  · have hreq_len : req.length = n := by
      have := beq_iff_eq.mp hreq
      omega
    congr 2
    refine List.map_congr_left fun k hk => ?_
    rw [hreq_len] at hk
    have hne : 2 * k + (req.getD k false).toNat ≠ (w.take j).length := by
      rw [htake_len]
      exact hagree hreq_len k hk
    conv_lhs => rw [hsplit]
    exact List.getD_append_cons_of_ne (w.take j) (w.drop (j + 1)) (w.getD j []) [] [] hne
  · rfl

private theorem exists_unqueried_index {n : ℕ} (hn : 1 ≤ n) {msg : List Bool}
    (hmsg : msg.length = n) {queried : List (List Bool)} (hqlen : queried.length ≤ 1)
    (hnot_mem : !queried.contains msg = true) :
    ∃ i < n, ∀ r ∈ queried, agreeAt n (2 * i + (msg.getD i false).toNat) r := by
  rcases queried with _ | ⟨req, _ | ⟨_, _⟩⟩
  · refine ⟨0, by omega, fun _ h => nomatch h⟩
  · by_cases hreq_len : req.length = n
    · have hne_msg : msg ≠ req := fun heq => by simp [heq] at hnot_mem
      have hex : ∃ i < n, msg.getD i false ≠ req.getD i false := by
        by_contra h_all
        refine hne_msg (List.ext_getElem (by omega) fun i hi₁ hi₂ => ?_)
        have heq_getD : msg.getD i false = req.getD i false :=
          Classical.not_not.mp fun hne => h_all ⟨i, by omega, hne⟩
        rwa [List.getD_eq_getElem _ _ hi₁, List.getD_eq_getElem _ _ hi₂] at heq_getD
      obtain ⟨i, hi, hdiff⟩ := hex
      refine ⟨i, hi, fun r hr _ k hk heq => ?_⟩
      rw [List.mem_singleton.mp hr] at heq
      simp only [List.mem_range] at hk
      have hb1 := Bool.toNat_le (req.getD k false)
      have hb2 := Bool.toNat_le (msg.getD i false)
      obtain rfl : k = i := by omega
      have htonat : (req.getD k false).toNat = (msg.getD k false).toNat := by omega
      rcases h1 : msg.getD k false <;> rcases h2 : req.getD k false <;> simp_all
    · refine ⟨0, by omega, fun r hr hlen => absurd (List.mem_singleton.mp hr ▸ hlen) hreq_len⟩
  · simp at hqlen

/-- Sample the simulated public key and dummy signing key around a challenge `y` at index `j`. -/
@[expose] noncomputable def lamportSimKeys (f : List Bool → List Bool) (n j : ℕ) (y : List Bool) :
    ProbComp (List Bool × List Bool) := do
  let front ← OracleComp.replicate j (BitString.sampleList n)
  let back ← OracleComp.replicate (2 * n - j - 1) (BitString.sampleList n)
  return (encList encBits (front.map f ++ y :: back.map f),
    encList encBits (front ++ [] :: back))

@[program_certificate]
theorem isPPTOn_lamportSimKeys {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) :
    IsPPTOn (encPair (encPair encUnary encBits) encUnary) (encPair encBits encBits)
      (fun q : (ℕ × List Bool) × ℕ => lamportSimKeys f q.1.1 q.2 q.1.2) := by
  unfold lamportSimKeys
  let encQ := encPair (encPair encUnary encBits) encUnary
  let encR := encPair encQ (encList encBits)
  have hq1 := ComputableInPolyTime.fst (encPair encUnary encBits) encUnary
  have hn := (ComputableInPolyTime.fst encUnary encBits).comp hq1
  have hj := ComputableInPolyTime.snd (encPair encUnary encBits) encUnary
  have hfront : IsPPTOn encQ (encList encBits)
      (fun q : (ℕ × List Bool) × ℕ => OracleComp.replicate q.2 (BitString.sampleList q.1.1)) :=
    hn.sampleList.replicate hj
  have hp1 := ComputableInPolyTime.fst encQ (encList encBits)
  have hn' := hn.comp hp1
  have hcnt := ComputableInPolyTime.unary_sub.comp
    ((ComputableInPolyTime.unary_sub.comp
      ((uConstMul 2 hn').prod (hj.comp hp1))).prod (.const 1))
  have hback : IsPPTOn encR (encList encBits)
      (fun r : ((ℕ × List Bool) × ℕ) × List (List Bool) =>
        OracleComp.replicate (2 * r.1.1.1 - r.1.2 - 1) (BitString.sampleList r.1.1.1)) :=
    hn'.sampleList.replicate hcnt
  have hs1 := ComputableInPolyTime.fst encR (encList encBits)
  have hfront_proj := (ComputableInPolyTime.snd encQ (encList encBits)).comp hs1
  have hback_proj := ComputableInPolyTime.snd encR (encList encBits)
  have hy_proj := (ComputableInPolyTime.snd encUnary encBits).comp (hq1.comp (hp1.comp hs1))
  have hmap_f := ComputableInPolyTime.map hf
  have hpk_list := ComputableInPolyTime.listAppend' (hmap_f.comp hfront_proj)
    (ComputableInPolyTime.cons' hy_proj (hmap_f.comp hback_proj))
  have hsk_list := ComputableInPolyTime.listAppend' hfront_proj
    (ComputableInPolyTime.cons' (ComputableInPolyTime.const []) hback_proj)
  have hpost := hpk_list.encoding_comp.prod hsk_list.encoding_comp
  exact hfront.bind_with (hback.bind_with hpost.isPPTOn)

/-- Reduction that inverts `f` on challenge `y` at security parameter `n` by embedding `y` at a
uniformly sampled index `j < dyadicSize (2 * n)`. When `j < 2 * n`, embed `y` in slot `j` of a
Lamport public key and run a one-time forger; otherwise return the empty word. -/
@[expose] noncomputable def lamportInverter (f : List Bool → List Bool)
    (hf : ComputableInPolyTime f encBits encBits) (adversary : Forger)
    (n : ℕ) (y : List Bool) : ProbComp (List Bool) := do
  let j ← sampleDyadicIndex (2 * n)
  if j < 2 * n then do
    let keys ← lamportSimKeys f n j y
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        ((lamportScheme f hf).oneTimeSigningOracle keys.2)) (adversary n keys.1)).run []
    let msig := out.1
    return (frames msig.2).getD (j / 2) []
  else
    return []

theorem isPPT_lamportInverter {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBits (lamportInverter f hf adversary) := by
  have hrun_base := (lamportScheme f hf).isPPTOn_run_oneTimeSigningOracle hadversary
  have hj : IsPPTOn (encPair encUnary encBits) encUnary
      (fun p : ℕ × List Bool => sampleDyadicIndex (2 * p.1)) :=
    isPPTOn_sampleDyadicIndex (uConstMul 2 (ComputableInPolyTime.fst encUnary encBits))
  have hkeys := isPPTOn_lamportSimKeys hf
  let encQ := encPair (encPair encUnary encBits) encUnary
  let encCallIn := encPair encQ (encPair encBits encBits)
  let encOut := encPair (encPair encBits encBits) (encList encBits)
  have hp1 := ComputableInPolyTime.fst encQ (encPair encBits encBits)
  have hq_n := (ComputableInPolyTime.fst encUnary encBits).comp
    (ComputableInPolyTime.fst (encPair encUnary encBits) encUnary)
  have hq_j := ComputableInPolyTime.snd (encPair encUnary encBits) encUnary
  have hprep := (hq_n.comp hp1).prod
    (ComputableInPolyTime.snd encQ (encPair encBits encBits))
  have hsig := (ComputableInPolyTime.snd encBits encBits).comp
    ((ComputableInPolyTime.fst (encPair encBits encBits) (encList encBits)).comp
      (ComputableInPolyTime.snd encCallIn encOut))
  have hj_proj := hq_j.comp (hp1.comp (ComputableInPolyTime.fst encCallIn encOut))
  have hpost := ComputableInPolyTime.listGetDWithInput (computableInPolyTime_frames hsig)
    ((ComputableInPolyTime.unary_div_const 2).comp hj_proj) []
  exact (hj.bind_with (IsPPTOn.ite'
    (ComputableInPolyTime.unary_lt' hq_j (uConstMul 2 hq_n))
    (hkeys.bind_with ((hrun_base.preprocess hprep).bind_with hpost.isPPTOn))
    (ComputableInPolyTime.const []).isPPTOn)).isPPT

private theorem map_true_le_sum_of_pointwise {β : Type*} {m : ℕ}
    (p : PMF β) (win : β → Bool) (q : ℕ → PMF β) (invWin : ℕ → β → Bool)
    (h : ∀ x, p x * (if win x then 1 else 0) ≤
      ∑ j : Fin (dyadicSize m),
        if j.val < m then q j.val x * (if invWin j.val x then 1 else 0) else 0) :
    (p.map win) true ≤
      ∑ j : Fin (dyadicSize m), if j.val < m then ((q j.val).map (invWin j.val)) true else 0 := by
  rw [PMF.map_apply_true]
  refine (tsum_le_tsum h).trans ?_
  rw [Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
  refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
  split_ifs
  · exact (PMF.map_apply_true _ _).symm
  · simp

private theorem bind_map_true_le_sum {α β : Type*} {m : ℕ} (μ : PMF α)
    (p : α → PMF β) (win : α → β → Bool)
    (q : α → ℕ → PMF β) (invWin : α → ℕ → β → Bool) (trial : ℕ → PMF Bool)
    (hpt : ∀ w ∈ μ.support, ∀ x, (p w) x * (if win w x then 1 else 0) ≤
      ∑ j : Fin (dyadicSize m),
        if j.val < m then (q w j.val) x * (if invWin w j.val x then 1 else 0) else 0)
    (htrial : ∀ j < m, μ.bind (fun w => (q w j).map (invWin w j)) = trial j) :
    (μ.bind (fun w => (p w).map (win w))) true ≤
      ∑ j : Fin (dyadicSize m), (trial j.val) true := by
  rw [PMF.bind_apply]
  have h1 : (∑' w, μ w * ((p w).map (win w)) true) ≤
      ∑' w, ∑ j : Fin (dyadicSize m),
        μ w * (if j.val < m then ((q w j.val).map (invWin w j.val)) true else 0) := by
    refine tsum_le_tsum fun w => ?_
    rw [← Finset.mul_sum]
    by_cases hw : w ∈ μ.support
    · exact mul_le_mul_right (map_true_le_sum_of_pointwise _ _ _ _ (hpt w hw)) (μ w)
    · simp [(PMF.apply_eq_zero_iff μ w).mpr hw]
  refine h1.trans ?_
  rw [Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with hj
  · rw [← htrial j.val hj, PMF.bind_apply]
  · simp

private noncomputable def lamportRunWith (f : List Bool → List Bool)
    (hf : ComputableInPolyTime f encBits encBits) (adversary : Forger)
    (n : ℕ) (pk sk : List Bool) : PMF ((List Bool × List Bool) × List (List Bool)) :=
  ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      ((lamportScheme f hf).oneTimeSigningOracle sk)) (adversary n pk)).run [])

private def lamportDummySk (w : List (List Bool)) (j : ℕ) : List Bool :=
  encList encBits (w.take j ++ [] :: w.drop (j + 1))

private def lamportInvWin (f : List Bool → List Bool) (w : List (List Bool)) (j : ℕ)
    (out : (List Bool × List Bool) × List (List Bool)) : Bool :=
  f ((frames out.1.2).getD (j / 2) []) == f (w.getD j [])

private theorem lamport_pointwise_le {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) (adversary : Forger)
    {n : ℕ} (hn : 1 ≤ n) {w : List (List Bool)} (hw_len : w.length = 2 * n)
    (out : (List Bool × List Bool) × List (List Bool)) :
    let pk := encList encBits (w.map f)
    lamportRunWith f hf adversary n pk (encList encBits w) out *
      (if (out.1.1.length == n) && !out.2.contains out.1.1 &&
          lamportVerify f pk out.1.1 out.1.2 then 1 else 0) ≤
      ∑ j : Fin (dyadicSize (2 * n)),
        if j.val < 2 * n then
          lamportRunWith f hf adversary n pk (lamportDummySk w j.val) out *
            (if lamportInvWin f w j.val out then 1 else 0)
        else 0 := by
  intro pk
  let win : Bool :=
    (out.1.1.length == n) && !out.2.contains out.1.1 && lamportVerify f pk out.1.1 out.1.2
  change lamportRunWith f hf adversary n pk (encList encBits w) out * (if win then 1 else 0) ≤ _
  by_cases hwin : win = true
  · by_cases hsupp : out ∈ (lamportRunWith f hf adversary n pk (encList encBits w)).support
    · have hqlen : out.2.length ≤ 1 := by
        dsimp only [lamportRunWith] at hsupp
        rw [ProbOracleComp.eval_run_interpret_eq_runWith] at hsupp
        exact (lamportScheme f hf).length_le_one_of_mem_support_run_oneTimeSigningOracle
          (encList encBits w) (adversary n pk) hsupp
      have hwin' := hwin
      dsimp only [win] at hwin'
      simp only [Bool.and_eq_true, beq_iff_eq] at hwin'
      obtain ⟨⟨hmsg_len, hnot_mem⟩, hver⟩ := hwin'
      obtain ⟨i, hi, hagree⟩ := exists_unqueried_index hn hmsg_len hqlen hnot_mem
      let jStar := 2 * i + (out.1.1.getD i false).toNat
      have hjStar_lt : jStar < 2 * n := by
        have := Bool.toNat_le (out.1.1.getD i false)
        omega
      have hrun_eq : lamportRunWith f hf adversary n pk (encList encBits w) out =
          lamportRunWith f hf adversary n pk (lamportDummySk w jStar) out := by
        dsimp only [lamportRunWith, lamportDummySk]
        rw [ProbOracleComp.eval_run_interpret_eq_runWith,
          ProbOracleComp.eval_run_interpret_eq_runWith]
        exact (lamportScheme f hf).run_oneTimeSigningOracle_apply_eq_of_agree
          (encList encBits w) (lamportDummySk w jStar)
          (fun req hreq => lamportSign_eq_of_agreeAt hjStar_lt hw_len hreq)
          (adversary n pk) [] out.1 out.2 hagree
      have hinvWin_true : lamportInvWin f w jStar out = true := by
        dsimp only [lamportInvWin, jStar]
        rw [two_mul_add_toNat_div_two]
        simp only [lamportVerify, pk, frames_encList_bits, Bool.and_eq_true,
          List.all_eq_true, List.mem_range] at hver
        have hcheck := hver.2 i (by omega)
        have hjStar_w : jStar < w.length := by omega
        have hjStar_map : jStar < (w.map f).length := by simp [hjStar_w]
        rw [List.getD_eq_getElem _ _ hjStar_map, List.getElem_map,
          ← List.getD_eq_getElem _ _ hjStar_w] at hcheck
        exact hcheck
      simp only [hwin, ↓reduceIte, mul_one, hrun_eq]
      let term (j : Fin (dyadicSize (2 * n))) : ℝ≥0∞ :=
        if j.val < 2 * n then
          lamportRunWith f hf adversary n pk (lamportDummySk w j.val) out *
            (if lamportInvWin f w j.val out then 1 else 0)
        else 0
      simpa [term, hjStar_lt, hinvWin_true] using
        Finset.single_le_sum (f := term) (fun _ _ => zero_le)
          (Finset.mem_univ ⟨jStar, hjStar_lt.trans (lt_dyadicSize (2 * n))⟩)
    · simp [(PMF.apply_eq_zero_iff _ _).mpr hsupp]
  · simp [hwin]

/-- **Lamport's one-time signature theorem**: for any one-way function `f`, `lamportScheme f` is
existentially unforgeable under one-time adaptive chosen-message attack (`OneTimeEUFCMA`). -/
theorem OneWay.oneTimeEUFCMA_lamport {f : List Bool → List Bool} (hf : OneWay f) :
    (lamportScheme f hf.polyTime).OneTimeEUFCMA := by
  let S := lamportScheme f hf.polyTime
  apply SignatureScheme.OneTimeEUFCMA.of_negligible
  intro adversary hadversary
  let inverter := lamportInverter f hf.polyTime adversary
  have hinv_neg := hf.inversion_negligible inverter (isPPT_lamportInverter hf.polyTime hadversary)
  have hscaled : Negligible (fun n =>
      (dyadicSize (2 * n) : ℝ≥0) *
        Game.succProbability (ProbComp.eval (inversionGame f inverter n))) :=
    hinv_neg.polynomiallyBounded_mul
      (dyadicSize_polynomiallyBounded.comp ((PolynomiallyBounded.const 2).mul .id))
  apply negligible_of_eventually_le hscaled
  filter_upwards [eventually_ge_atTop 1] with n hn
  let μ : PMF (List (List Bool)) :=
    ProbComp.eval (OracleComp.replicate (2 * n) (BitString.sampleList n))
  let pkOf (w : List (List Bool)) : List Bool := encList encBits (w.map f)
  let realSkOf (w : List (List Bool)) : List Bool := encList encBits w
  let dummySkOf := lamportDummySk
  let runWith := lamportRunWith f hf.polyTime adversary n
  let win (w : List (List Bool)) (out : (List Bool × List Bool) × List (List Bool)) : Bool :=
    (out.1.1.length == n) && !out.2.contains out.1.1 &&
      lamportVerify f (pkOf w) out.1.1 out.1.2
  let invWin := lamportInvWin f
  let inverterAt (j : ℕ) (y : List Bool) : ProbComp (List Bool) :=
    if j < 2 * n then do
      let keys ← lamportSimKeys f n j y
      let out ← (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (S.oneTimeSigningOracle keys.2)) (adversary n keys.1)).run []
      return (frames out.1.2).getD (j / 2) []
    else
      return []
  let trial (j : ℕ) : PMF Bool := do
    let xStar ← BitString.uniformList n
    (ProbComp.eval (inverterAt j (f xStar))).map fun cand => f cand == f xStar
  have hinv_eq : ProbComp.eval (inversionGame f inverter n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (2 * n)))).bind (fun j => trial j.val) := by
    simp only [pmf_norm, inversionGame, inverter, lamportInverter, trial, inverterAt,
      BitString.eval_sampleList, eval_sampleDyadicIndex]
    rw [PMF.bind_comm]
    rfl
  have htrial_eq : ∀ j < 2 * n,
      μ.bind (fun w => (runWith (pkOf w) (dummySkOf w j)).map (invWin w j)) = trial j := by
    intro j hj
    dsimp only [μ, trial, inverterAt]
    rw [eval_replicate_split (BitString.sampleList n) hj]
    simp only [hj, ↓reduceIte, BitString.eval_sampleList, lamportSimKeys, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, PMF.pure_bind,
      PMF.map_bind, Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun xStar _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun front hfront => ?_
    have hfront_len : front.length = j :=
      ((ProbComp.mem_support_replicate_iff _ _ _).mp hfront).1
    refine PMF.bind_congr_on_support _ _ _ fun back _ => ?_
    have hpk_eq : pkOf (front ++ xStar :: back) =
        encList encBits (front.map f ++ f xStar :: back.map f) := by
      simp [pkOf]
    have hsk_eq : dummySkOf (front ++ xStar :: back) j =
        encList encBits (front ++ [] :: back) := by
      simp [dummySkOf, lamportDummySk, ← hfront_len]
    have hget_eq : (front ++ xStar :: back).getD j [] = xStar := by
      rw [← hfront_len, List.getD_append_right _ _ _ _ le_rfl,
        Nat.sub_self, List.getD_cons_zero]
    simp only [runWith, lamportRunWith, S, invWin, lamportInvWin, hpk_eq, hsk_eq, hget_eq,
      PMF.map, PMF.pure_bind, Function.comp_def]
  have hgame_real : ProbComp.eval (S.eufOneTimeGame adversary n) =
      μ.bind (fun w => (runWith (pkOf w) (realSkOf w)).map (win w)) := by
    simp only [SignatureScheme.eufOneTimeGame, S, lamportScheme, lamportKeyGen, μ, pkOf, realSkOf,
      runWith, lamportRunWith, win, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
      PMF.pure_bind, PMF.map]
    rfl
  have htotal_ennreal : (ProbComp.eval (S.eufOneTimeGame adversary n)) true ≤
      ∑ j : Fin (dyadicSize (2 * n)), (trial j.val) true := by
    rw [hgame_real]
    exact bind_map_true_le_sum μ (fun w => runWith (pkOf w) (realSkOf w)) win
      (fun w j => runWith (pkOf w) (dummySkOf w j)) invWin trial
      (fun w hw => lamport_pointwise_le hf.polyTime adversary hn
        ((ProbComp.mem_support_replicate_iff _ _ _).mp hw).1)
      htrial_eq
  have hpos : (0 : ℝ≥0) < dyadicSize (2 * n) := by exact_mod_cast dyadicSize_pos (2 * n)
  rw [hinv_eq, Game.succProbability_uniform, Fintype.card_fin, mul_div_cancel₀ _ hpos.ne']
  have hsum_ne_top : (∑ j : Fin (dyadicSize (2 * n)), (trial j.val) true) ≠ ⊤ :=
    ne_of_lt (ENNReal.sum_lt_top.mpr fun j _ => (PMF.apply_ne_top _ _).lt_top)
  have hmono := ENNReal.toNNReal_mono hsum_ne_top htotal_ennreal
  rwa [ENNReal.toNNReal_sum fun j _ => PMF.apply_ne_top _ _] at hmono

/-- Any one-way function implies the existence of a one-time EUF-CMA secure signature scheme. -/
theorem OneWay.exists_oneTimeSignature {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ S : SignatureScheme, S.OneTimeEUFCMA :=
  ⟨lamportScheme f hf.polyTime, hf.oneTimeEUFCMA_lamport⟩

/-- **Equivalence between one-way functions and one-time digital signatures**: a one-way function
exists if and only if a one-time EUF-CMA secure uniform signature scheme exists. -/
theorem exists_oneWay_iff_exists_oneTimeSignature :
    (∃ f, OneWay f) ↔ (∃ S : SignatureScheme, S.OneTimeEUFCMA) :=
  ⟨fun ⟨_, hf⟩ => hf.exists_oneTimeSignature, fun ⟨_, hS⟩ => hS.exists_oneWay⟩

end Cslib.Crypto
