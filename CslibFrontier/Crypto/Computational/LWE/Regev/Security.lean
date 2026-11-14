/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.LoRCPA
public import CslibFrontier.Crypto.Computational.Encryption.PublicKeyReplacement
public import CslibFrontier.Crypto.Computational.LWE.KeyGen
public import CslibFrontier.Crypto.Computational.LWE.Regev
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
public import CslibFrontier.Languages.Probabilistic.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Tactic.PPT

/-!
# Generated-key Regev security from decision LWE

The serialized Regev encryption program reads a public word with the fixed-width row-major
encoding of `Matrix.toBinary`, samples `m` fair coins and writes the `n + 1` ciphertext residues
with `w` bits each. Missing bits and coins are zero and excess data is ignored, so the program is
total. Key generation is the shared serialized LWE key generator `LWE.keyGenSerialized`, whose
public word is exactly a decision-LWE sample, and `Regev.decryptSerialized` rounds the inner
product residue with `(1, -t)` in polynomial time.

All honest programs are strict PPT / polynomial-time. For single-challenge IND-CPA, the reduction
to decision LWE is one uniform strict PPT distinguisher with loss two, and the remaining
statistical term is the leftover-hash bound `sqrt(2 ^ ((n + 1) * w) / 2 ^ m)` of
`Regev.challengeGame_uniform_advantage_le` ([Regev2009, Section 5]; [Peikert2016, Section 5.2.1]).
For adaptive `Q`-query left-or-right security (`Encryption.LoRAdversary`, `lorGameSerialized`),
both the per-bit reductions `lorDistinguisherSerialized` (matching `Regev.lorDistinguisher`) and
the single hidden-bit reduction `lorLweDistinguisher` (`Encryption.lorKeyDistinguisher`) are
uniform strict PPT whenever `Q` is polynomial-time computable (`isPPT_lorDistinguisherSerialized`,
`isPPT_lorLweDistinguisher`), yielding asymptotic `Q`-query left-or-right security under
`DecisionLWE` (`lorIndCPA_of_decisionLWE`).

## Main definitions

* `Regev.serializeCiphertext`, `Regev.decodeCiphertext`: canonical ciphertext words and total
  decoder.
* `Regev.encryptWithCoinsSerialized`, `Regev.encryptSerialized`, `Regev.decryptResidue`,
  `Regev.decryptSerialized`: word-level encryption and decryption.
* `Regev.lweDistinguisher`: the uniform single-challenge hidden-bit reduction.
* `Regev.typedAdversary`: a word-level adversary at one parameter, as a typed two-stage adversary
  on public matrices and ciphertexts through their canonical encodings.
* `Regev.hidingError`: the explicit statistical term.
* `Regev.typedLoRAdversary`, `Regev.lorStepSerialized`, `Regev.lorRunSerialized`,
  `Regev.lorDistinguisherSerialized`, `Regev.lorLweDistinguisher`, `Regev.lorGameSerialized`,
  `Regev.LoRINDCPA`: word-level adaptive `Q`-query left-or-right experiments, `DecisionLWE`
  reductions, and asymptotic security notion over `Encryption.LoRAdversary`.

## Main results

* `Regev.decodeCiphertext_serializeCiphertext`, `Regev.encryptWithCoinsSerialized_eq`,
  `Regev.eval_encryptSerialized_toBinary`, `Regev.decryptSerialized_eq`,
  `Regev.keyGenSerialized_encryptSerialized_correct`: exact bridges to typed encryption and
  decryption, and zero-error decryption correctness.
* `Regev.isPPTOn_encryptSerialized`, `Regev.computableInPolyTime_decryptSerialized`,
  `Regev.isPPT_lweDistinguisher`, `Regev.isPPT_lorDistinguisherSerialized`,
  `Regev.isPPT_lorLweDistinguisher`: native polynomial-time / strict PPT certificates.
* `Regev.advantage_game_le`, `Regev.indCPA_of_decisionLWE`: single-challenge concrete bound and
  IND-CPA under decision LWE with an eventual entropy margin.
* `Regev.lorGameSerialized_advantage_le`, `Regev.lorGameSerialized_advantage_le_two_mul`,
  `Regev.lorIndCPA_of_decisionLWE`: adaptive `Q`-query concrete bounds and asymptotic
  left-or-right security under decision LWE.

## References

* [O. Regev, *On Lattices, Learning with Errors, Random Linear Codes, and Cryptography*,
  Section 5][Regev2009]
* [C. Peikert, *A Decade of Lattice Cryptography*, Section 5.2.1][Peikert2016]
-/

@[expose] public section

namespace Cslib.Crypto.Regev

open Probability BitString Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped BigOperators NNReal

/-- Canonical ciphertext words: `n + 1` residues, `w` low-order-first bits each. -/
def serializeCiphertext {n w : ℕ} (c : Ciphertext n w) : List Bool :=
  Cslib.Matrix.toBinary (Matrix.of fun _ : Fin 1 => c)

/-- Total ciphertext decoder reading `n + 1` residue words of width `w`, padding absent bits with
zero. -/
def decodeCiphertext (n w : ℕ) (word : List Bool) : Ciphertext n w :=
  Cslib.Matrix.ofBinary 1 (n + 1) w word 0

/-- Canonical ciphertext words roundtrip through `decodeCiphertext`. -/
@[simp] theorem decodeCiphertext_serializeCiphertext {n w : ℕ} (c : Ciphertext n w) :
    decodeCiphertext n w (serializeCiphertext c) = c :=
  congrArg (fun M => M 0) (Cslib.Matrix.ofBinary_toBinary (Matrix.of fun _ : Fin 1 => c))

/-- A serialized ciphertext has exact bit length `(n + 1) * w`. -/
@[simp] theorem length_serializeCiphertext {n w : ℕ} (c : Ciphertext n w) :
    (serializeCiphertext c).length = (n + 1) * w := by
  simpa only [serializeCiphertext, Nat.one_mul] using
    Cslib.Matrix.length_toBinary (Matrix.of fun _ : Fin 1 => c)

/-- Column `j` of `xᵀ A + (μ * 2 ^ (w - 1), 0, …, 0)`, read from an arbitrary public word and
arbitrary coins, as a canonical residue. -/
def encryptEntry (n m w : ℕ) (publicWord : List Bool) (message : Bool) (coins : List Bool)
    (j : ℕ) : ℕ :=
  (((List.range m).map fun r =>
      if coins.getD r false then Cslib.Matrix.binaryEntry (n + 1) w publicWord r j else 0).sum +
    if j = 0 then message.toNat * 2 ^ (w - 1) else 0) % 2 ^ w

/-- Compute every ciphertext bit from the public word, the message and the coins. -/
def encryptWithCoinsSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : List Bool) : List Bool :=
  (List.range (n + 1)).flatMap fun j => lowBits w (encryptEntry n m w publicWord message coins j)

/-- Sample `m` fair coins and run the word encryption. -/
noncomputable def encryptSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool) :
    ProbComp (List Bool) := do
  let coins ← OracleComp.replicate m (ProbComp.uniform Bool)
  return encryptWithCoinsSerialized n m w publicWord message coins

/-- A computed entry is the canonical residue of the typed ciphertext entry. -/
theorem encryptEntry_eq (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : List Bool) (j : Fin (n + 1)) :
    encryptEntry n m w publicWord message coins j.val =
      (encryptWithCoins (Cslib.Matrix.ofBinary m (n + 1) w publicWord) message
        (fun r => coins.getD r.val false) j).val := by
  unfold encryptEntry
  rw [List.map_range_eq_ofFn, List.sum_ofFn, ← ZMod.val_natCast]
  congr 1
  rw [Nat.cast_add, Nat.cast_sum, encryptWithCoins, Pi.add_apply]
  congr 1
  · simp only [Matrix.vecMul, dotProduct, coinVector]
    apply Finset.sum_congr rfl
    intro r _
    rw [Cslib.Matrix.ofBinary_apply]
    cases coins.getD r.val false <;> simp
  · by_cases hj : j = 0
    · subst hj
      simp [LWE.encodeBit]
    · have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [hj, hv]

/-- The word encryption is the typed encryption of the decoded public matrix and coins. -/
theorem encryptWithCoinsSerialized_eq (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : List Bool) :
    encryptWithCoinsSerialized n m w publicWord message coins = serializeCiphertext
      (encryptWithCoins (Cslib.Matrix.ofBinary m (n + 1) w publicWord) message
        (fun r => coins.getD r.val false)) := by
  unfold encryptWithCoinsSerialized serializeCiphertext
  rw [Cslib.Matrix.toBinary_eq]
  simp only [List.flatMap_def, List.map_range_eq_ofFn, lowBits_eq_ofFn, encryptEntry_eq,
    Matrix.of_apply, List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil]

/-- On canonical public words, the word encryption has the typed encryption law. -/
theorem eval_encryptSerialized_toBinary {n m w : ℕ} (A : PublicKey n m w) (message : Bool) :
    ProbComp.eval (encryptSerialized n m w (Cslib.Matrix.toBinary A) message) =
      (ProbComp.eval (encrypt A message)).map serializeCiphertext := by
  rw [eval_encrypt, PMF.map_comp, ← PMF.pi_uniformOfFintype]
  simp only [encryptSerialized, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_replicate,
    ProbComp.eval_uniform, PMF.bind_map, Function.comp_def, encryptWithCoinsSerialized_eq,
    Cslib.Matrix.ofBinary_toBinary]
  congr 1 with x : 1
  simp [List.getD_eq_getElem?_getD]

/-- Every serialized ciphertext produced by `encryptWithCoinsSerialized` has exact bit length
`(n + 1) * w`. -/
@[simp] theorem length_encryptWithCoinsSerialized (n m w : ℕ) (publicWord : List Bool)
    (message : Bool) (coins : List Bool) :
    (encryptWithCoinsSerialized n m w publicWord message coins).length = (n + 1) * w := by
  rw [encryptWithCoinsSerialized_eq, length_serializeCiphertext]

/-- Every ciphertext in the support of `encryptSerialized n m w publicWord message` has exact bit
length `(n + 1) * w`. -/
theorem length_of_mem_support_encryptSerialized {n m w : ℕ} {publicWord : List Bool}
    {message : Bool} {c : List Bool}
    (hc : c ∈ (ProbComp.eval (encryptSerialized n m w publicWord message)).support) :
    c.length = (n + 1) * w := by
  simp only [encryptSerialized, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hc
  obtain ⟨coins, -, rfl⟩ := hc
  exact length_encryptWithCoinsSerialized n m w publicWord message coins

/-- Compute the canonical residue of `c ⬝ᵥ (1, -t)` modulo `2 ^ w` from raw secret and ciphertext
words using signed binary subtraction. -/
def decryptResidue (n w : ℕ) (secretWord ciphertextWord : List Bool) : ℕ :=
  LWE.secretProductResidue n w 0 secretWord ciphertextWord

/-- Decrypt a serialized Regev ciphertext word under a serialized secret word by rounding
`decryptResidue` via `LWE.decodeResidue`. -/
def decryptSerialized (n w : ℕ) (secretWord ciphertextWord : List Bool) : Bool :=
  LWE.decodeResidue w (decryptResidue n w secretWord ciphertextWord)

/-- Signed word arithmetic computes the canonical residue of `c ⬝ᵥ (1, -t)` on the decoded secret
and ciphertext. -/
theorem decryptResidue_eq (n w : ℕ) (secretWord ciphertextWord : List Bool) :
    decryptResidue n w secretWord ciphertextWord =
      (decodeCiphertext n w ciphertextWord ⬝ᵥ
        LWE.secretVector (LWE.decodeSecret n w secretWord)).val :=
  LWE.secretProductResidue_eq_dotProduct n w (0 : Fin 1) secretWord ciphertextWord

/-- Serialized Regev decryption agrees with typed `Regev.decrypt` on the decoded secret and
ciphertext for all dimensions and widths. -/
theorem decryptSerialized_eq (n w : ℕ) (secretWord ciphertextWord : List Bool) :
    decryptSerialized n w secretWord ciphertextWord =
      decrypt (LWE.decodeSecret n w secretWord) (decodeCiphertext n w ciphertextWord) := by
  simp only [decryptSerialized, decrypt, LWE.decode, decryptResidue_eq]

/-- Canonical secret and ciphertext words decrypt identically to their typed counterparts. -/
@[simp] theorem decryptSerialized_serialize {n w : ℕ} (secret : Fin n → ZMod (2 ^ w))
    (ciphertext : Ciphertext n w) :
    decryptSerialized n w (LWE.serializeSecret secret) (serializeCiphertext ciphertext) =
      decrypt secret ciphertext := by
  rw [decryptSerialized_eq, LWE.decode_serializeSecret, decodeCiphertext_serializeCiphertext]

/-- Every key pair generated by `LWE.keyGenSerialized` and every supported ciphertext of
`Regev.encryptSerialized` decrypt with zero error when `4 * (m * η) < 2 ^ w`. -/
theorem keyGenSerialized_encryptSerialized_correct {n m w η : ℕ} (hw : 0 < w)
    (hmargin : 4 * (m * η) < 2 ^ w) {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (LWE.keyGenSerialized n m w η)).support) (μ : Bool)
    {ciphertext : List Bool}
    (hc : ciphertext ∈ (ProbComp.eval (encryptSerialized n m w keys.1 μ)).support) :
    decryptSerialized n w keys.2 ciphertext = μ := by
  rw [LWE.eval_keyGenSerialized, PMF.mem_support_map_iff] at hkeys
  obtain ⟨typedKeys, htypedKeys, rfl⟩ := hkeys
  rw [LWE.serializePublicMatrix, eval_encryptSerialized_toBinary, PMF.mem_support_map_iff] at hc
  obtain ⟨typedCiphertext, htypedCiphertext, rfl⟩ := hc
  rw [decryptSerialized_serialize]
  exact keyGen_encrypt_correct hw hmargin htypedKeys μ htypedCiphertext

variable {α : Type} {input : α ↪ List Bool} {n m w j : α → ℕ}

/-- One ciphertext entry is polynomial-time in the dimensions, the public word and the coins. -/
@[fun_prop]
theorem computableInPolyTime_encryptEntry
    {publicWord : α → List Bool} {message : α → Bool} {coins : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool)
    (hcoins : ComputableInPolyTime coins input encBits)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime
      (fun a => encryptEntry (n a) (m a) (w a) (publicWord a) (message a) (coins a) (j a))
      input encNat := by
  unfold encryptEntry
  have hterm : ComputableInPolyTime
      (fun p : α × ℕ => if (coins p.1).getD p.2 false
        then Cslib.Matrix.binaryEntry (n p.1 + 1) (w p.1) (publicWord p.1) p.2 (j p.1) else 0)
      (encPair input encUnary) encNat := by
    apply ((bitsGetD false).comp
      ((hcoins.comp (fst input encUnary)).prod (snd input encUnary))).ite'
    · exact matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop)
        (snd input encUnary) (by fun_prop)
    · exact const 0
  have hsum := (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
    (mapWithInput
      (f := fun a r => if (coins a).getD r false
        then Cslib.Matrix.binaryEntry (n a + 1) (w a) (publicWord a) r (j a) else 0)
      (range.comp hm) hterm)
  have hboolUnary : ComputableInPolyTime Bool.toNat encBool encUnary := of_finite Bool.toNat
  have hhalf : ComputableInPolyTime (fun a => w a - 1) input encUnary := by fun_prop
  have hmessageTerm : ComputableInPolyTime
      (fun a => if j a = 0 then (message a).toNat * 2 ^ (w a - 1) else 0) input encNat := by
    simpa only [Function.comp_apply, beq_iff_eq] using (beq hj (const 0)).ite'
      (binary_mul' (unary_to_binary.comp (hboolUnary.comp hmessage))
        (binary_pow' (const 2) hhalf)) (const 0)
  exact binary_mod.comp
    ((binary_add.comp (hsum.prod hmessageTerm)).prod (binary_pow' (const 2) hw))

/-- The word encryption is polynomial-time on arbitrary public words and coins, charging the
complete ciphertext output. -/
@[fun_prop]
theorem computableInPolyTime_encryptWithCoinsSerialized
    {publicWord : α → List Bool} {message : α → Bool} {coins : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool)
    (hcoins : ComputableInPolyTime coins input encBits) :
    ComputableInPolyTime
      (fun a => encryptWithCoinsSerialized (n a) (m a) (w a) (publicWord a) (message a)
        (coins a)) input encBits := by
  unfold encryptWithCoinsSerialized
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  fun_prop

/-- The complete encryption program is strict PPT on arbitrary public words and messages. -/
@[fun_prop]
theorem isPPTOn_encryptSerialized {publicWord : α → List Bool} {message : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool) :
    IsPPTOn input encBits
      (fun a => encryptSerialized (n a) (m a) (w a) (publicWord a) (message a)) := by
  have hsample := (isPPTOn_uniform_bool input).replicate_bool hm
  unfold encryptSerialized
  ppt

/-- Compute the Regev decryption residue `c ⬝ᵥ (1, -t)` modulo `2 ^ w` in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_decryptResidue
    {secretWord ciphertextWord : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hsecretWord : ComputableInPolyTime secretWord input encBits)
    (hciphertextWord : ComputableInPolyTime ciphertextWord input encBits) :
    ComputableInPolyTime
      (fun a => decryptResidue (n a) (w a) (secretWord a) (ciphertextWord a))
      input encNat := by
  unfold decryptResidue
  fun_prop

/-- Serialized Regev decryption is computable in polynomial time on arbitrary secret and
ciphertext words. -/
@[fun_prop]
theorem computableInPolyTime_decryptSerialized
    {secretWord ciphertextWord : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hsecretWord : ComputableInPolyTime secretWord input encBits)
    (hciphertextWord : ComputableInPolyTime ciphertextWord input encBits) :
    ComputableInPolyTime
      (fun a => decryptSerialized (n a) (w a) (secretWord a) (ciphertextWord a))
      input encBool := by
  unfold decryptSerialized
  fun_prop

/-- The single-challenge leftover-hash term `sqrt(2 ^ ((n + 1) * w) / 2 ^ m)`. -/
noncomputable def hidingError (n m w : ℕ) : ℝ≥0 :=
  NNReal.sqrt ((2 : ℝ≥0) ^ ((n + 1) * w) / 2 ^ m)

/-- The uniform hidden-bit reduction running the actual word encryption. -/
noncomputable def lweDistinguisher (n m w : ℕ → ℕ) (adversary : Encryption.Adversary) :
    Distinguisher :=
  Encryption.keyDistinguisher
    (fun security => encryptSerialized (n security) (m security) (w security)) adversary

/-- Efficient dimensions make the reduction one uniform strict PPT distinguisher. -/
theorem isPPT_lweDistinguisher {n m w : ℕ → ℕ} {adversary : Encryption.Adversary}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hadversary : adversary.IsPPT) : IsPPT encBool (lweDistinguisher n m w adversary) := by
  apply Encryption.isPPT_keyDistinguisher ?_ hadversary
  exact isPPTOn_encryptSerialized (hn.comp (by fun_prop)) (hm.comp (by fun_prop))
    (hw.comp (by fun_prop)) (by fun_prop) (by fun_prop)

/-- The word-level adversary at parameter `security` as a typed two-stage adversary: it reads the
public matrix through `Matrix.toBinary` and the challenge ciphertext through
`serializeCiphertext`. -/
noncomputable def typedAdversary {n m w : ℕ} (adversary : Encryption.Adversary) (security : ℕ) :
    TwoStage (PublicKey n m w) (MessagePair Bool) (Ciphertext n w) Bool (List Bool) where
  choose A := (adversary.toTwoStage security).choose (Cslib.Matrix.toBinary A)
  guess state c := (adversary.toTwoStage security).guess state (serializeCiphertext c)

/-- Under the uniform decision-LWE ensemble, the word experiment is the typed single-challenge
experiment of `typedAdversary`. -/
theorem publicKeyGame_uniformEnsemble (n m w : ℕ → ℕ) (adversary : Encryption.Adversary)
    (bit : Bool) (security : ℕ) :
    Encryption.publicKeyGame (LWE.uniformEnsemble n m w security)
      (fun k => encryptSerialized (n k) (m k) (w k)) adversary bit security =
        challengeGame (PMF.uniformOfFintype (PublicKey (n security) (m security) (w security)))
          (typedAdversary adversary security) bit := by
  cases bit <;>
    simp only [Encryption.publicKeyGame, Encryption.publicKeyGameOn, LWE.uniformEnsemble,
      challengeGame, Game.withSetup, lrExperiment, typedAdversary,
      Encryption.AdversaryOf.toTwoStage,
      MessagePair.select_false, MessagePair.select_true, Bool.false_eq_true, ↓reduceIte,
      PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, ProbComp.eval_bind,
      ProbComp.eval_map, eval_encryptSerialized_toBinary]

/-- Under the uniform ensemble, the advantage is at most the leftover-hash term. -/
theorem advantage_uniformEnsemble_le (n m w : ℕ → ℕ) (adversary : Encryption.Adversary)
    (security : ℕ) :
    Game.advantage
      (Encryption.publicKeyGame (LWE.uniformEnsemble n m w security)
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary false security)
      (Encryption.publicKeyGame (LWE.uniformEnsemble n m w security)
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary true security) ≤
          hidingError (n security) (m security) (w security) := by
  apply NNReal.coe_le_coe.mp
  rw [publicKeyGame_uniformEnsemble, publicKeyGame_uniformEnsemble]
  simpa only [hidingError, Real.coe_sqrt, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using
    challengeGame_uniform_advantage_le _

/-- One uniform reduction bounds the actual IND-CPA advantage by twice its decision-LWE
advantage plus the leftover-hash term. No efficiency is needed for this inequality. -/
theorem advantage_game_le (n m w η : ℕ → ℕ) (adversary : Encryption.Adversary) (security : ℕ) :
    Encryption.advantage
      (Encryption.game (fun k => LWE.keyGenSerialized (n k) (m k) (w k) (η k))
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary) security ≤
      2 * Game.advantage
        (distinguishingGame
          (LWE.realEnsemble n m w (fun k => LWE.noiseLaw (w k) (η k)) security)
          (lweDistinguisher n m w adversary security))
        (distinguishingGame (LWE.uniformEnsemble n m w security)
          (lweDistinguisher n m w adversary security)) +
        hidingError (n security) (m security) (w security) := by
  simp only [Encryption.advantage, Encryption.eval_game_eq_publicKeyGame,
    LWE.eval_keyGenSerialized_publicWord]
  exact (Encryption.advantage_publicKeyGame_le _ (LWE.uniformEnsemble n m w security)
    _ adversary security).trans
      (add_le_add le_rfl (advantage_uniformEnsemble_le n m w adversary security))

open Filter in
/-- Regev encryption is IND-CPA secure under decision LWE for its exact centered-binomial error
law, for efficient dimensions with an eventual entropy surplus of twice the security parameter. -/
theorem indCPA_of_decisionLWE {n m w η : ℕ → ℕ}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hmargin : ∀ᶠ security in atTop, (n security + 1) * w security + 2 * security ≤ m security)
    (hLWE : DecisionLWE n m w (fun k => LWE.noiseLaw (w k) (η k))) :
    Encryption.INDCPA (fun k => LWE.keyGenSerialized (n k) (m k) (w k) (η k))
      (fun k => encryptSerialized (n k) (m k) (w k)) := by
  intro adversary hadversary
  have hsource := hLWE.encoded (lweDistinguisher n m w adversary)
    (isPPT_lweDistinguisher hn hm hw hadversary)
  have herror := negligible_mul_sqrt_pow_two_div_pow_two
    (count := fun _ => 1) (outputBits := fun k => (n k + 1) * w k) (by fun_prop) hmargin
  apply negligible_of_le
    ((hsource.polynomiallyBounded_mul (p := fun _ => 2) (by fun_prop)).add herror)
  intro security
  refine (advantage_game_le n m w η adversary security).trans (le_of_eq ?_)
  simp [hidingError]

/-! ### Adaptive multi-challenge left-or-right security -/

/-- View a stateful `Encryption.LoRAdversary` at security parameter `security` as a typed
`Regev.LoRAdversary` whose state `(state, transcript)` pairs the adversary's saved state word with
the reverse list of serialized challenge ciphertexts. -/
noncomputable def typedLoRAdversary {n m w : ℕ} (adversary : Encryption.LoRAdversary)
    (security : ℕ) : LoRAdversary n m w (List Bool × List (List Bool)) where
  start A := (ProbComp.eval (adversary.start security (Cslib.Matrix.toBinary A))).map
    fun st₀ => (st₀, [])
  query st := (ProbComp.eval (adversary.query security st.1 st.2)).map
    fun choice => (⟨Encryption.ChoiceOut.msg₀ choice, Encryption.ChoiceOut.msg₁ choice⟩,
      (Encryption.ChoiceOut.state choice, st.2))
  receive st c := (st.1, serializeCiphertext c :: st.2)
  guess st := ProbComp.eval (adversary.guess security st.1 st.2)

/-- One adaptive query step: ask `adversary.query` on the current state word and reverse
ciphertext transcript, encrypt the selected bit under `publicWord`, and return the updated state
word paired with the extended ciphertext transcript. -/
noncomputable abbrev lorStepSerialized (n m w : ℕ → ℕ) (adversary : Encryption.LoRAdversary)
    (security : ℕ) (publicWord : List Bool) (bit : Bool)
    (loopState : List Bool × List (List Bool)) : ProbComp (List Bool × List (List Bool)) :=
  Encryption.lorStep (fun k => encryptSerialized (n k) (m k) (w k)) adversary
    security publicWord bit loopState

/-- Answer `q` adaptive queries starting from `loopState = (state, transcript)`. -/
noncomputable abbrev lorRunSerialized (n m w : ℕ → ℕ) (adversary : Encryption.LoRAdversary)
    (security : ℕ) (publicWord : List Bool) (bit : Bool) (q : ℕ)
    (loopState : List Bool × List (List Bool)) : ProbComp (List Bool × List (List Bool)) :=
  Encryption.lorRun (fun k => encryptSerialized (n k) (m k) (w k)) adversary
    security publicWord bit q loopState

/-- The serialized `Q`-query decision-LWE distinguisher for challenge bit `bit`, directly realizing
`Regev.lorDistinguisher`. -/
noncomputable abbrev lorDistinguisherSerialized (n m w Q : ℕ → ℕ)
    (adversary : Encryption.LoRAdversary) (bit : Bool) : Distinguisher :=
  Encryption.lorDistinguisher (fun k => encryptSerialized (n k) (m k) (w k)) Q adversary bit

/-- The single uniform hidden-bit `DecisionLWE` distinguisher for `Q`-query left-or-right security:
sample a random challenge bit `bit`, run `lorDistinguisherSerialized` with `bit`, and output
`guess ^^ bit`. -/
noncomputable abbrev lorLweDistinguisher (n m w Q : ℕ → ℕ)
    (adversary : Encryption.LoRAdversary) : Distinguisher :=
  Encryption.lorKeyDistinguisher (fun k => encryptSerialized (n k) (m k) (w k)) Q adversary

/-- The executable adaptive `Q`-query left-or-right experiment with generated LWE keys. -/
noncomputable abbrev lorGameSerialized (n m w η Q : ℕ → ℕ)
    (adversary : Encryption.LoRAdversary) (bit : Bool) (security : ℕ) : ProbComp Bool :=
  Encryption.lorGame (fun k => LWE.keyGenSerialized (n k) (m k) (w k) (η k))
    (fun k => encryptSerialized (n k) (m k) (w k)) Q adversary bit security

/-- On canonical public-matrix words, `lorRunSerialized` has the exact distribution of typed
`Regev.lorRun` on `typedLoRAdversary`. -/
theorem eval_lorRunSerialized_toBinary (n m w : ℕ → ℕ) (adversary : Encryption.LoRAdversary)
    (security : ℕ) (A : PublicKey (n security) (m security) (w security)) (bit : Bool) (q : ℕ)
    (loopState : List Bool × List (List Bool)) :
    ProbComp.eval (lorRunSerialized n m w adversary security (Cslib.Matrix.toBinary A)
        bit q loopState) =
      lorRun (m := m security) (fun μ => ProbComp.eval (encrypt A μ))
        (typedLoRAdversary adversary security) bit q loopState := by
  induction q generalizing loopState with
  | zero =>
    simp [lorRunSerialized, Encryption.lorRun, lorRun]
  | succ q ih =>
    unfold lorRunSerialized Encryption.lorRun
    rw [OracleComp.iterate_succ_bind]
    simp only [Encryption.lorStep, lorRun, typedLoRAdversary, bind_assoc, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.bind_map, PMF.pure_bind,
      Function.comp_def, eval_encryptSerialized_toBinary]
    congr 1 with choice : 1
    have hsel :
        (⟨Encryption.ChoiceOut.msg₀ choice, Encryption.ChoiceOut.msg₁ choice⟩ :
          MessagePair Bool).select bit =
        (if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice) := by
      cases bit <;> rfl
    rw [hsel]
    congr 1 with c : 1
    exact ih (Encryption.ChoiceOut.state choice, serializeCiphertext c :: loopState.2)

/-- On canonical public-matrix words, `lorDistinguisherSerialized` has the exact distribution of
typed `Regev.lorDistinguisher`. -/
theorem eval_lorDistinguisherSerialized_toBinary (n m w Q : ℕ → ℕ)
    (adversary : Encryption.LoRAdversary) (bit : Bool) (security : ℕ)
    (A : PublicKey (n security) (m security) (w security)) :
    ProbComp.eval (lorDistinguisherSerialized n m w Q adversary bit security
        (Cslib.Matrix.toBinary A)) =
      lorDistinguisher (Q security) (typedLoRAdversary adversary security) bit A := by
  unfold lorDistinguisherSerialized Encryption.lorDistinguisher lorDistinguisher lorGame
  simp only [ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.pure_bind]
  rw [show (typedLoRAdversary adversary security).start A =
    (ProbComp.eval (adversary.start security (Cslib.Matrix.toBinary A))).map (fun st₀ => (st₀, []))
    from rfl, PMF.bind_map]
  congr 1 with st₀ : 1
  dsimp only [Function.comp_def]
  rw [eval_lorRunSerialized_toBinary n m w adversary security A bit (Q security) (st₀, [])]
  rfl

/-- Under the real `DecisionLWE` ensemble, `lorDistinguisherSerialized` realizes the real side of
`Regev.lorGame_advantage_le`. -/
theorem distinguishingGame_realEnsemble_lorDistinguisherSerialized (n m w η Q : ℕ → ℕ)
    (adversary : Encryption.LoRAdversary) (bit : Bool) (security : ℕ) :
    distinguishingGame (LWE.realEnsemble n m w (fun k => LWE.noiseLaw (w k) (η k)) security)
        (lorDistinguisherSerialized n m w Q adversary bit security) =
      (LWE.publicMatrixLaw (n security) (m security) (w security)
          (LWE.noiseLaw (w security) (η security))).bind
        (lorDistinguisher (Q security) (typedLoRAdversary adversary security) bit) := by
  simp [distinguishingGame, Game.withSetup, LWE.realEnsemble, PMF.bind_map, Function.comp_def,
    eval_lorDistinguisherSerialized_toBinary]

/-- Under the uniform `DecisionLWE` ensemble, `lorDistinguisherSerialized` realizes the ideal
uniform side of `Regev.lorGame_advantage_le`. -/
theorem distinguishingGame_uniformEnsemble_lorDistinguisherSerialized (n m w Q : ℕ → ℕ)
    (adversary : Encryption.LoRAdversary) (bit : Bool) (security : ℕ) :
    distinguishingGame (LWE.uniformEnsemble n m w security)
        (lorDistinguisherSerialized n m w Q adversary bit security) =
      (PMF.uniformOfFintype (PublicKey (n security) (m security) (w security))).bind
        (lorDistinguisher (Q security) (typedLoRAdversary adversary security) bit) := by
  simp [distinguishingGame, Game.withSetup, LWE.uniformEnsemble, PMF.bind_map, Function.comp_def,
    eval_lorDistinguisherSerialized_toBinary]

/-- Evaluating `lorGameSerialized` matches the typed `Regev.lorGame` on `typedLoRAdversary`. -/
theorem eval_lorGameSerialized (n m w η Q : ℕ → ℕ) (adversary : Encryption.LoRAdversary)
    (bit : Bool) (security : ℕ) :
    ProbComp.eval (lorGameSerialized n m w η Q adversary bit security) =
      lorGame (LWE.publicMatrixLaw (n security) (m security) (w security)
          (LWE.noiseLaw (w security) (η security)))
        (Q security) (typedLoRAdversary adversary security) bit := by
  rw [lorGameSerialized, Encryption.eval_lorGame_eq_distinguishingGame,
    LWE.eval_keyGenSerialized_publicWord,
    distinguishingGame_realEnsemble_lorDistinguisherSerialized,
    ← lorGame_eq_bind_lorDistinguisher]

private theorem polynomiallyBounded_ciphertextLength {n w : ℕ → ℕ}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary) :
    Cslib.PolynomiallyBounded (fun k => (n k + 1) * w k) := by
  have h : ComputableInPolyTime (fun k => (n k + 1) * w k) encUnary encUnary := by fun_prop
  have hp : PolyBounded (fun x => x) (fun k => (n k + 1) * w k) := by
    simpa only [encUnary_apply, List.length_replicate] using h.tidy.polyBounded
  exact PolyBounded.polynomiallyBounded hp

private theorem isPPTOn_encryptSerialized_keyed {n m w : ℕ → ℕ}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary) :
    IsPPTOn (encKeyedInput encBool) encBits
      (fun ⟨security, pk, msg⟩ =>
        encryptSerialized (n security) (m security) (w security) pk msg) :=
  isPPTOn_encryptSerialized (hn.comp (by fun_prop)) (hm.comp (by fun_prop))
    (hw.comp (by fun_prop)) (by fun_prop) (by fun_prop)

/-- Parameterized strict PPT certificate for `lorDistinguisherSerialized` with a computed challenge
bit. -/
theorem isPPTOn_lorDistinguisherSerialized {n m w Q : ℕ → ℕ} {adversary : Encryption.LoRAdversary}
    {security : α → ℕ} {publicWord : α → List Bool} {bit : α → Bool}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hadversary : adversary.IsPPT)
    (hsecurity : ComputableInPolyTime security input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool
      (fun a => lorDistinguisherSerialized n m w Q adversary (bit a)
        (security a) (publicWord a)) :=
  Encryption.isPPTOn_lorDistinguisher
    (isPPTOn_encryptSerialized_keyed hn hm hw)
    (polynomiallyBounded_ciphertextLength hn hw)
    (fun _ _ _ _ hc => le_of_eq (length_of_mem_support_encryptSerialized hc))
    hQ hadversary hsecurity hpublicWord hbit

/-- Efficient dimension and query-count schedules make `lorDistinguisherSerialized` one uniform
strict PPT distinguisher. -/
theorem isPPT_lorDistinguisherSerialized {n m w Q : ℕ → ℕ} {adversary : Encryption.LoRAdversary}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hadversary : adversary.IsPPT) (bit : Bool) :
    IsPPT encBool (lorDistinguisherSerialized n m w Q adversary bit) :=
  Encryption.isPPT_lorDistinguisher
    (isPPTOn_encryptSerialized_keyed hn hm hw)
    (polynomiallyBounded_ciphertextLength hn hw)
    (fun _ _ _ _ hc => le_of_eq (length_of_mem_support_encryptSerialized hc))
    hQ hadversary bit

/-- Efficient dimension and query-count schedules make `lorLweDistinguisher` one uniform strict PPT
distinguisher. -/
theorem isPPT_lorLweDistinguisher {n m w Q : ℕ → ℕ} {adversary : Encryption.LoRAdversary}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hadversary : adversary.IsPPT) :
    IsPPT encBool (lorLweDistinguisher n m w Q adversary) :=
  Encryption.isPPT_lorKeyDistinguisher
    (isPPTOn_encryptSerialized_keyed hn hm hw)
    (polynomiallyBounded_ciphertextLength hn hw)
    (fun _ _ _ _ hc => le_of_eq (length_of_mem_support_encryptSerialized hc))
    hQ hadversary

/-- Concrete adaptive `Q`-query left-or-right security for `lorGameSerialized`: the advantage is at
most the sum of the `DecisionLWE` advantages of `lorDistinguisherSerialized` at `false` and `true`
plus `Q * hidingError`. -/
theorem lorGameSerialized_advantage_le (n m w η Q : ℕ → ℕ) (adversary : Encryption.LoRAdversary)
    (security : ℕ) :
    Game.advantage (ProbComp.eval (lorGameSerialized n m w η Q adversary false security))
        (ProbComp.eval (lorGameSerialized n m w η Q adversary true security)) ≤
      Game.advantage
          (distinguishingGame
            (LWE.realEnsemble n m w (fun k => LWE.noiseLaw (w k) (η k)) security)
            (lorDistinguisherSerialized n m w Q adversary false security))
          (distinguishingGame (LWE.uniformEnsemble n m w security)
            (lorDistinguisherSerialized n m w Q adversary false security)) +
        Game.advantage
          (distinguishingGame
            (LWE.realEnsemble n m w (fun k => LWE.noiseLaw (w k) (η k)) security)
            (lorDistinguisherSerialized n m w Q adversary true security))
          (distinguishingGame (LWE.uniformEnsemble n m w security)
            (lorDistinguisherSerialized n m w Q adversary true security)) +
        Q security * hidingError (n security) (m security) (w security) := by
  apply NNReal.coe_le_coe.mp
  rw [eval_lorGameSerialized, eval_lorGameSerialized,
    distinguishingGame_realEnsemble_lorDistinguisherSerialized,
    distinguishingGame_uniformEnsemble_lorDistinguisherSerialized,
    distinguishingGame_realEnsemble_lorDistinguisherSerialized,
    distinguishingGame_uniformEnsemble_lorDistinguisherSerialized]
  simpa only [hidingError, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, Real.coe_sqrt,
    NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using
    lorGame_advantage_le (LWE.noiseLaw (w security) (η security)) (Q security)
      (typedLoRAdversary adversary security)

/-- Concrete adaptive `Q`-query left-or-right security for `lorGameSerialized` via the single
hidden-bit reduction `lorLweDistinguisher`: the advantage is at most twice its `DecisionLWE`
advantage plus `Q * hidingError`. -/
theorem lorGameSerialized_advantage_le_two_mul (n m w η Q : ℕ → ℕ)
    (adversary : Encryption.LoRAdversary) (security : ℕ) :
    Game.advantage (ProbComp.eval (lorGameSerialized n m w η Q adversary false security))
        (ProbComp.eval (lorGameSerialized n m w η Q adversary true security)) ≤
      2 * Game.advantage
          (distinguishingGame
            (LWE.realEnsemble n m w (fun k => LWE.noiseLaw (w k) (η k)) security)
            (lorLweDistinguisher n m w Q adversary security))
          (distinguishingGame (LWE.uniformEnsemble n m w security)
            (lorLweDistinguisher n m w Q adversary security)) +
        Q security * hidingError (n security) (m security) (w security) := by
  have huniform : Game.advantage
      (distinguishingGame (LWE.uniformEnsemble n m w security)
        (lorDistinguisherSerialized n m w Q adversary false security))
      (distinguishingGame (LWE.uniformEnsemble n m w security)
        (lorDistinguisherSerialized n m w Q adversary true security)) ≤
      Q security * hidingError (n security) (m security) (w security) := by
    apply NNReal.coe_le_coe.mp
    rw [distinguishingGame_uniformEnsemble_lorDistinguisherSerialized,
      distinguishingGame_uniformEnsemble_lorDistinguisherSerialized,
      ← lorGame_eq_bind_lorDistinguisher, ← lorGame_eq_bind_lorDistinguisher]
    simpa only [hidingError, NNReal.coe_mul, NNReal.coe_natCast, Real.coe_sqrt,
      NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using
      lorGame_uniform_advantage_le (Q security) (typedLoRAdversary adversary security)
  rw [lorGameSerialized, Encryption.eval_lorGame_eq_distinguishingGame,
    Encryption.eval_lorGame_eq_distinguishingGame, LWE.eval_keyGenSerialized_publicWord]
  exact (Encryption.advantage_lorDistinguisher_le _ (LWE.uniformEnsemble n m w security)
    _ Q adversary security).trans (add_le_add le_rfl huniform)

/-- Adaptive `Q`-query left-or-right IND-CPA security for serialized Regev encryption against all
uniform strict PPT `Encryption.LoRAdversary` adversaries. -/
abbrev LoRINDCPA (n m w η Q : ℕ → ℕ) : Prop :=
  Encryption.LoRINDCPA (fun k => LWE.keyGenSerialized (n k) (m k) (w k) (η k))
    (fun k => encryptSerialized (n k) (m k) (w k)) Q

open Filter in
/-- Adaptive `Q`-query left-or-right security of serialized Regev encryption under `DecisionLWE`
for any polynomial-time query schedule `Q`. -/
theorem lorIndCPA_of_decisionLWE {n m w η Q : ℕ → ℕ}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hmargin : ∀ᶠ security in atTop, (n security + 1) * w security + 2 * security ≤ m security)
    (hLWE : DecisionLWE n m w (fun k => LWE.noiseLaw (w k) (η k))) :
    LoRINDCPA n m w η Q := by
  intro adversary hadversary
  have hsource := hLWE.encoded (lorLweDistinguisher n m w Q adversary)
    (isPPT_lorLweDistinguisher hn hm hw hQ hadversary)
  have herror := negligible_mul_sqrt_pow_two_div_pow_two
    (count := Q) (outputBits := fun k => (n k + 1) * w k) hQ.polynomiallyBounded hmargin
  apply negligible_of_le
    ((hsource.polynomiallyBounded_mul (p := fun _ => 2) (by fun_prop)).add herror)
  intro security
  refine (lorGameSerialized_advantage_le_two_mul n m w η Q adversary security).trans (le_of_eq ?_)
  simp [hidingError]

end Cslib.Crypto.Regev
