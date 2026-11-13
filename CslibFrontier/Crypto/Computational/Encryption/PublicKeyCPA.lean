/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.PairCapture
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind

/-!
# Chosen-plaintext attacks on public-key encryption

In the eavesdropping experiment `Cslib.Crypto.Encryption.gameOn` the adversary already holds the
public key, so it can encrypt any message itself. Katz and Lindell conclude that, for public-key
encryption, indistinguishability against eavesdroppers implies security against chosen-plaintext
attacks ([KatzLindell2020], Section 12.2.1, Proposition 12.3, p. 406). This module states the
chosen-plaintext experiment with an explicit encryption oracle and proves that implication.

The chosen-plaintext experiment is the public-key form of [KatzLindell2020], Definition 3.21: both
stages of the adversary may query an encryption oracle that encrypts any message under the public
key with fresh coins. For one fixed scheme `E : PKE PK SK M C`, `E.cpaOracleExperiment` is stated
with typed keys, messages and ciphertexts against a `PKE.CPAOracleAdversary`, whose stages are
oracle programs over the typed encryption oracle `E.encrypt pk`. The adversary that answers its own
queries, `A.toTwoStage E`, plays the eavesdropping experiment `E.cpaExperiment` with exactly the
same law (`PKE.cpaOracleExperiment_eq_cpaExperiment`), which is Proposition 12.3 at one scheme.

Asymptotic security quantifies over uniform strict oracle PPT adversaries, which are word-level
oracle programs: both stages of a `Cslib.Crypto.Encryption.WordCPAAdversary` query the oracle with
bit words. The challenge stage and the admissibility predicate `valid` are those of `gameOn`. At
each parameter, `cpaOracleGameOn` is the typed experiment of the scheme with the same algorithms,
played by `adversary.toCPAOracleAdversary n` (`cpaOracleGameOn_eq_cpaOracleExperiment`).

## Main definitions

* `Cslib.Crypto.PKE.CPAOracleAdversary`, `Cslib.Crypto.PKE.cpaOracleExperiment`: typed
  chosen-plaintext adversaries and the chosen-plaintext experiment of one fixed scheme.
* `Cslib.Crypto.PKE.CPAOracleAdversary.toTwoStage`: the eavesdropper that answers the oracle
  queries itself, by encrypting under the public key it saved.
* `Cslib.Crypto.Encryption.encryptionOracle`, `Cslib.Crypto.Encryption.runWithEncryption`: the
  word-level encryption oracle and the execution of an oracle program against it.
* `Cslib.Crypto.Encryption.WordCPAAdversary`, `Cslib.Crypto.Encryption.WordCPAAdversary.IsPPT`,
  `Cslib.Crypto.Encryption.encEncryptInput`: chosen-plaintext adversaries, their uniform strict
  oracle PPT admissibility, and the `(1ⁿ, pk, msg)` encryption-input encoding.
* `Cslib.Crypto.Encryption.cpaOracleGameOn`, `Cslib.Crypto.Encryption.WordINDCPAOracleOn`,
  `Cslib.Crypto.Encryption.WordINDCPAOracle`: the chosen-plaintext experiment and security, the
  latter under the equal-length rule of [KatzLindell2020], Definition 3.21.
* `Cslib.Crypto.Encryption.WordCPAAdversary.toCPAOracleAdversary`: the typed adversary that a word
  adversary plays at one parameter.
* `Cslib.Crypto.Encryption.WordCPAAdversary.toAdversary`: the word-level eavesdropper that answers
  the oracle queries itself.

## Main results

* `Cslib.Crypto.PKE.cpaOracleExperiment_eq_cpaExperiment`: the eavesdropping experiment of
  `A.toTwoStage E` is the chosen-plaintext experiment of `A` ([KatzLindell2020], Proposition 12.3,
  for one scheme).
* `Cslib.Crypto.Encryption.cpaOracleGameOn_eq_cpaOracleExperiment`: the word-level experiment at
  one parameter is the typed one.
* `Cslib.Crypto.Encryption.WordCPAAdversary.isPPT_toAdversary`: the eavesdropper is uniform
  strict PPT when the adversary and the honest encryption algorithm are.
* `Cslib.Crypto.Encryption.WordCPAAdversary.eval_gameOn_toAdversary`: its eavesdropping
  experiment has exactly the law of the chosen-plaintext experiment.
* `Cslib.Crypto.Encryption.INDCPAOn.wordINDCPAOracleOn`,
  `Cslib.Crypto.Encryption.WordINDCPA.wordINDCPAOracle`: indistinguishability against
  eavesdroppers implies security against chosen-plaintext attacks ([KatzLindell2020],
  Proposition 12.3).

The multiple-encryption form with a left-or-right oracle ([KatzLindell2020], Section 12.2.2,
Theorem 12.6, p. 408) is not formalized here.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Definition 3.21
  and Section 12.2.1 (Definition 12.2 and Proposition 12.3, pp. 405–406).
-/

public section

namespace Cslib.Crypto.PKE

variable {PK SK M C σ : Type}

/-- A chosen-plaintext adversary against a public-key scheme with public keys `PK`, messages `M`
and ciphertexts `C`. Both stages are oracle programs that may ask the encryption oracle for an
encryption of any message `m : M`; `σ` is the state saved between the stages. -/
structure CPAOracleAdversary (PK M C σ : Type) where
  /-- Receive the public key, query the oracle, and choose two challenge messages and a state. -/
  choose : PK → ProbOracleComp (fun _ : M => C) (MessagePair M × σ)
  /-- Receive the saved state and the challenge ciphertext, query the oracle, and return a
  guess. -/
  guess : σ → C → ProbOracleComp (fun _ : M => C) Bool

/-- The chosen-plaintext experiment of the scheme `E` with challenge-pair admissibility predicate
`valid` (the public-key form of [KatzLindell2020], Definition 3.21). Draw a key pair; run message
selection against the encryption oracle `E.encrypt pk`; if `valid pk m₀ m₁` holds, encrypt the
message selected by `b` and run the guessing stage against the same oracle, and otherwise return
`false`. -/
@[expose]
def cpaOracleExperiment (E : PKE PK SK M C) (valid : PK → M → M → Bool)
    (A : CPAOracleAdversary PK M C σ) (b : Bool) : Experiment := do
  let (pk, _) ← E.keyGen
  let (pair, state) ← (A.choose pk).run (E.encrypt pk)
  if valid pk pair.msg₀ pair.msg₁ then
    let challenge ← E.encrypt pk (pair.select b)
    (A.guess state challenge).run (E.encrypt pk)
  else
    return false

/-- The eavesdropper that runs `A` and answers its oracle queries by encrypting under the public
key, which it saves next to `A`'s state. -/
@[expose]
def CPAOracleAdversary.toTwoStage (E : PKE PK SK M C) (A : CPAOracleAdversary PK M C σ) :
    TwoStage PK (MessagePair M) C Bool (PK × σ) where
  choose pk := (fun out => (out.1, (pk, out.2))) <$> (A.choose pk).run (E.encrypt pk)
  guess saved challenge := (A.guess saved.2 challenge).run (E.encrypt saved.1)

/-- Against a public-key scheme, the encryption oracle gives the adversary nothing that the public
key does not: the eavesdropping experiment of `A.toTwoStage E` is the chosen-plaintext experiment
of `A` ([KatzLindell2020], Proposition 12.3, for one fixed scheme). -/
theorem cpaOracleExperiment_eq_cpaExperiment (E : PKE PK SK M C) (valid : PK → M → M → Bool)
    (A : CPAOracleAdversary PK M C σ) (b : Bool) :
    E.cpaOracleExperiment valid A b = E.cpaExperiment valid (A.toTwoStage E) b := by
  simp only [cpaOracleExperiment, cpaExperiment, lrExperiment, CPAOracleAdversary.toTwoStage,
    bind_map_left]

end Cslib.Crypto.PKE

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- The encryption oracle under public key `pk` at parameter `n`: answer each query word
`request.2` with a fresh encryption of it. The oracle keeps no state. -/
@[expose]
def encryptionOracle (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) (n : ℕ)
    (pk : List Bool) (request : Unit × List Bool) : StateT Unit ProbComp (List Bool) :=
  fun s => do
    let ciphertext ← encrypt n pk request.2
    return (ciphertext, s)

/-- Run an oracle program against `encryptionOracle encrypt n pk`, with private coins sampled
uniformly, and return its result. -/
@[expose]
noncomputable def runWithEncryption {α : Type}
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) (n : ℕ) (pk : List Bool)
    (program : WordOracleComp Unit α) : ProbComp α := do
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (encryptionOracle encrypt n pk)) program).run ()
  return out.1

/-- A chosen-plaintext adversary on bit words. Both stages may query the encryption oracle. -/
structure WordCPAAdversary where
  /-- Receive the public key, query the oracle, choose two challenge messages, and save a
  state. -/
  choose : ℕ → List Bool → WordOracleComp Unit ((List Bool × List Bool) × List Bool)
  /-- Receive the saved state and the challenge ciphertext, query the oracle, and return a
  distinguishing bit. -/
  guess : ℕ → List Bool → List Bool → WordOracleComp Unit Bool

/-- Uniform strict oracle PPT admissibility of both stages of a `WordCPAAdversary`. -/
structure WordCPAAdversary.IsPPT (adversary : WordCPAAdversary) : Prop where
  /-- Message selection is uniform strict oracle PPT on the parameter and public key. -/
  choose : IsOraclePPT (Operation := Unit) (encChoiceOut encBits) adversary.choose
  /-- Guessing is uniform strict oracle PPT on the parameter, saved state and ciphertext. -/
  guess : IsOraclePPTOn (Operation := Unit) encGuessInput encBool
    (fun ⟨n, state, ciphertext⟩ => adversary.guess n state ciphertext)

/-- The chosen-plaintext experiment with challenge-pair admissibility predicate `valid`, the
public-key form of [KatzLindell2020], Definition 3.21. Sample the key pair; run message selection
against the encryption oracle; if `valid n pk m₀ m₁` holds, encrypt the selected message and run
the guessing stage against the oracle, and otherwise return `false` in both experiments. -/
@[expose]
noncomputable def cpaOracleGameOn (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (adversary : WordCPAAdversary) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choice ← runWithEncryption encrypt n keys.1 (adversary.choose n keys.1)
  if valid n keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let ciphertext ← encrypt n keys.1
      (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
    runWithEncryption encrypt n keys.1 (adversary.guess n (ChoiceOut.state choice) ciphertext)
  else
    return false

/-- Security against chosen-plaintext attacks with admissibility predicate `valid`, against
every uniform strict oracle PPT adversary. -/
@[expose]
def WordINDCPAOracleOn (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (cpaOracleGameOn valid keyGen encrypt adversary false n))
    (fun adversary n => ProbComp.eval (cpaOracleGameOn valid keyGen encrypt adversary true n))
    WordCPAAdversary.IsPPT

/-- Security against chosen-plaintext attacks under the equal-length rule of [KatzLindell2020],
Definition 3.21. -/
abbrev WordINDCPAOracle (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) : Prop :=
  WordINDCPAOracleOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) keyGen encrypt

/-- The typed adversary that `adversary` plays at parameter `n`: each word query `(_, m)` becomes
the typed query `m`, message selection returns the chosen pair as a `MessagePair`, and the saved
state word is the typed state. -/
@[expose]
def WordCPAAdversary.toCPAOracleAdversary (adversary : WordCPAAdversary) (n : ℕ) :
    PKE.CPAOracleAdversary (List Bool) (List Bool) (List Bool) (List Bool) where
  choose pk := (fun choice : ChoiceOut (List Bool) =>
      (⟨ChoiceOut.msg₀ choice, ChoiceOut.msg₁ choice⟩, ChoiceOut.state choice)) <$>
    ProbOracleComp.simulate (fun request => ProbOracleComp.query request.2) (adversary.choose n pk)
  guess state ciphertext :=
    ProbOracleComp.simulate (fun request => ProbOracleComp.query request.2)
      (adversary.guess n state ciphertext)

/-- Running a word oracle program against `encryptionOracle encrypt n pk` runs its typed form
against the typed oracle `encrypt n pk`. -/
theorem runWithEncryption_eq_run {α : Type}
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) (n : ℕ) (pk : List Bool)
    (program : WordOracleComp Unit α) :
    runWithEncryption encrypt n pk program =
      (ProbOracleComp.simulate (fun request => ProbOracleComp.query request.2) program).run
        (encrypt n pk) := by
  have horacle : (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (encryptionOracle encrypt n pk)) =
      fun q => StateT.lift (OracleComp.sumHandler ProbComp.unifFin
        (fun request : Unit × List Bool => encrypt n pk request.2) q) := by
    funext q
    cases q <;> rfl
  rw [runWithEncryption, horacle, OracleComp.run_interpret_lift, ProbOracleComp.run_simulate]
  simp only [ProbOracleComp.run_query, map_eq_pure_bind, bind_assoc, pure_bind, bind_pure]
  rfl

/-- The chosen-plaintext experiment at parameter `n` is the typed experiment of the scheme with
key generation `keyGen n` and encryption `encrypt n`, played by
`adversary.toCPAOracleAdversary n`. The experiment never decrypts, so `decrypt` is arbitrary. -/
theorem cpaOracleGameOn_eq_cpaOracleExperiment
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : List Bool → List Bool → Option (List Bool)) (adversary : WordCPAAdversary)
    (bit : Bool) (n : ℕ) :
    cpaOracleGameOn valid keyGen encrypt adversary bit n =
      (PKE.mk (keyGen n) (encrypt n) decrypt).cpaOracleExperiment (valid n)
        (adversary.toCPAOracleAdversary n) bit := by
  cases bit <;>
    simp only [cpaOracleGameOn, PKE.cpaOracleExperiment, WordCPAAdversary.toCPAOracleAdversary,
      runWithEncryption_eq_run, ProbOracleComp.run_map, bind_map_left, MessagePair.select_false,
      MessagePair.select_true, Bool.false_eq_true, ↓reduceIte]

/-- The eavesdropper that runs a chosen-plaintext adversary and answers its oracle queries by
encrypting under the public key. Message selection saves the public key in front of the
adversary's state; guessing reads it back. -/
@[expose]
noncomputable def WordCPAAdversary.toAdversary
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (adversary : WordCPAAdversary) : WordAdversary where
  choose n pk := do
    let choice ← runWithEncryption encrypt n pk (adversary.choose n pk)
    return (choice.1, encPair encBits encBits (pk, choice.2))
  guess n state ciphertext :=
    runWithEncryption encrypt n (unframe state) (adversary.guess n (dropFrame state) ciphertext)

/-- Encryption-algorithm input `(1ⁿ, pk, msg)`: the security parameter `n` in unary, then the
public key and the plaintext, both as bit words. -/
abbrev encEncryptInput : ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

/-- Running an oracle PPT program against the encryption oracle is PPT, when the parameter, the
public key and the program input are computed in polynomial time from the caller's input. -/
theorem isPPTOn_runWithEncryption {Caller α β : Type} {input : Caller ↪ List Bool}
    {source : α ↪ List Bool} {output : β ↪ List Bool}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {param : Caller → ℕ} {pk : Caller → List Bool} {prepare : Caller → α}
    {program : α → WordOracleComp Unit β}
    (hencrypt : IsPPTOn encEncryptInput encBits (fun p => encrypt p.1 p.2.1 p.2.2))
    (hparam : ComputableInPolyTime param input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hprepare : ComputableInPolyTime prepare input source)
    (hprogram : IsOraclePPTOn source output program) :
    IsPPTOn input output
      (fun a => runWithEncryption encrypt (param a) (pk a) (program (prepare a))) := by
  obtain ⟨c, d, hlen⟩ := hencrypt.length_le
  let Call := Caller × ((Unit × List Bool) × Unit)
  let encCall : Call ↪ List Bool := encHandlerCall input (encFinEnum Unit) (encFinEnum Unit)
  have hhandler : IsPPTOn encCall (encPair encBits (encFinEnum Unit))
      (fun call : Call => encryptionOracle encrypt (param call.1) (pk call.1) call.2.1 call.2.2) :=
    by
    have hargs : ComputableInPolyTime (fun call : Call => (param call.1, pk call.1, call.2.1.2))
        encCall (encPair encUnary (encPair encBits encBits)) :=
      (hparam.comp' (ComputableInPolyTime.fst _ _)).prod
        ((hpk.comp' (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _).fst'.snd')
    exact (hencrypt.preprocess hargs).map_pair (second := fun q => (q.2, q.1.2.2))
      (ComputableInPolyTime.prod (g := fun _ => ())
        (ComputableInPolyTime.snd encCall encBits) (ComputableInPolyTime.const ()))
  have hresources : PolyBounded (fun pair => (encPair input encBits pair).length)
      (fun pair : Caller × List Bool =>
        c * (2 * param pair.1 + 2 * (pk pair.1).length + pair.2.length + 5) ^ d) := by
    growth_poly [hparam.comp' (ComputableInPolyTime.fst input encBits),
      hpk.comp' (ComputableInPolyTime.fst input encBits), ComputableInPolyTime.snd input encBits]
  have hrun : IsPPTOn input (encPair output (encFinEnum Unit)) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (encryptionOracle encrypt (param a) (pk a))) (program (prepare a))).run ()) := by
    refine ((hprogram.run_interpret_preprocess_open_of_polyBounded (External := Empty)
      (handler := fun a request state =>
        ProbOracleComp.sample (encryptionOracle encrypt (param a) (pk a) request state))
      (initial := fun _ => ())
      (resources := fun a query =>
        c * (2 * param a + 2 * (pk a).length + query.length + 5) ^ d)
      hprepare hhandler.isOraclePPTOn (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hresources
      (fun a request _ _ result hresult => ?_)).congr fun _ _ _ _ => ?_).isPPTOn
    · have hsupp := (ProbOracleComp.support_sample _).subset hresult
      simp only [encryptionOracle, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsupp
      obtain ⟨ciphertext, hciphertext, rfl⟩ := hsupp
      have hsize : (encPair encUnary (encPair encBits encBits)
          (param a, pk a, request.2)).length + 1 ≤
          2 * param a + 2 * (pk a).length + request.2.length + 5 := by
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
        lia
      refine ⟨trivial, ?_, Nat.le_add_right _ _⟩
      exact (hlen (param a, pk a, request.2) ciphertext hciphertext).trans
        (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hsize d))
    · rw [ProbOracleComp.sample_run_interpret]
  exact hrun.bind_with (second := fun _ out => pure out.1)
    (ComputableInPolyTime.snd input (encPair output (encFinEnum Unit))).fst'.isPPTOn

/-- The eavesdropper `adversary.toAdversary encrypt` is uniform strict PPT, including its saved
public key, when the adversary and the honest encryption algorithm are. -/
theorem WordCPAAdversary.isPPT_toAdversary
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {adversary : WordCPAAdversary}
    (hencrypt : IsPPTOn encEncryptInput encBits (fun p => encrypt p.1 p.2.1 p.2.2))
    (hadversary : adversary.IsPPT) :
    (adversary.toAdversary encrypt).IsPPT := by
  let hp1 := ComputableInPolyTime.fst encUnary encBits
  let hp2 := ComputableInPolyTime.snd encUnary encBits
  let hg1 := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  let hg2 := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  have hrun := isPPTOn_runWithEncryption (prepare := fun p => (p.1, p.2)) hencrypt hp1 hp2
    (hp1.prod hp2) hadversary.choose.on
  let E := encPair (encPair encUnary encBits) (encChoiceOut encBits)
  have hsave : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × ((List Bool × List Bool) × List Bool) =>
        (q.2.1, encPair encBits encBits (q.1.2, q.2.2))) E (encChoiceOut encBits) :=
    (ComputableInPolyTime.snd _ _).fst'.prod
      (((ComputableInPolyTime.fst _ _).snd'.prod (ComputableInPolyTime.snd _ _).snd').encoding_comp)
  refine ⟨(hrun.bind_with (second := fun p choice => pure (choice.1,
    encPair encBits encBits (p.2, choice.2))) hsave.isPPTOn).isPPT, ?_⟩
  exact isPPTOn_runWithEncryption hencrypt hg1 (ComputableInPolyTime.unframe.comp' hg2.fst')
    (hg1.prod ((ComputableInPolyTime.dropFrame.comp' hg2.fst').prod hg2.snd')) hadversary.guess

/-- The eavesdropping experiment of `adversary.toAdversary encrypt` is the chosen-plaintext
experiment of `adversary`. -/
theorem WordCPAAdversary.eval_gameOn_toAdversary
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (adversary : WordCPAAdversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (gameOn valid keyGen encrypt (adversary.toAdversary encrypt) bit n) =
      ProbComp.eval (cpaOracleGameOn valid keyGen encrypt adversary bit n) := by
  simp only [pmf_norm, gameOn, cpaOracleGameOn, toAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁,
    ChoiceOut.msgs, ChoiceOut.state, encPair_apply, encBits_apply, unframe_frame_append,
    dropFrame_frame_append, apply_ite ProbComp.eval, PMF.bind_bind, PMF.pure_bind]

/-- Indistinguishability against eavesdroppers implies security against chosen-plaintext
attacks, for any admissibility predicate ([KatzLindell2020], Proposition 12.3). -/
theorem INDCPAOn.wordINDCPAOracleOn {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hencrypt : IsPPTOn encEncryptInput encBits (fun p => encrypt p.1 p.2.1 p.2.2))
    (hsecure : INDCPAOn valid encBits keyGen encrypt) :
    WordINDCPAOracleOn valid keyGen encrypt := by
  intro adversary hadversary
  simpa only [WordCPAAdversary.eval_gameOn_toAdversary] using
    hsecure (adversary.toAdversary encrypt) (adversary.isPPT_toAdversary hencrypt hadversary)

/-- Indistinguishability against eavesdroppers implies security against chosen-plaintext
attacks, under the equal-length rule ([KatzLindell2020], Proposition 12.3). -/
theorem WordINDCPA.wordINDCPAOracle {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hencrypt : IsPPTOn encEncryptInput encBits (fun p => encrypt p.1 p.2.1 p.2.2))
    (hsecure : WordINDCPA keyGen encrypt) :
    WordINDCPAOracle keyGen encrypt :=
  INDCPAOn.wordINDCPAOracleOn hencrypt hsecure

end Cslib.Crypto.Encryption
