/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Parameters
import CslibFrontier.Crypto.Computational.LWE.DualRegev.Security
import CslibFrontier.Crypto.Computational.LWE.Regev.Security
import CslibFrontier.Tactic.PPT
import Mathlib.Tactic.NormNum

/-!
Regression clients for Regev and dual-Regev encryption: concrete encryptions and decryptions with
nonzero errors, a gadget preimage sampler satisfying the trapdoor interface, and the growing
GSW parameter family, which satisfies every correctness and security premise apart from its
decision-LWE assumption.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Regev

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Regev Turing.MultiTapeTM
open scoped Matrix

/-! ### Regev -/

private def toyB : Matrix (Fin 2) (Fin 1) (ZMod (2 ^ 4)) := !![3; 7]
private def toySecret : Fin 1 → ZMod (2 ^ 4) := ![5]
private def toyError : Fin 2 → ℤ := ![1, -1]

-- Both bits round-trip with nonzero errors of both signs, and the coins select the noise.
example : decrypt toySecret
      (encryptWithCoins (LWE.publicMatrixInt toyB toySecret toyError) false ![true, false])
      = false ∧
    decrypt toySecret
      (encryptWithCoins (LWE.publicMatrixInt toyB toySecret toyError) true ![true, true])
      = true ∧
    noise ![true, false] toyError = 1 := by
  decide +kernel

-- The generic correctness theorem covers this instance: `4 * (2 * 1) < 2 ^ 4`.
example (μ : Bool) (x : Fin 2 → Bool) :
    decrypt toySecret (encryptWithCoins (LWE.publicMatrixInt toyB toySecret toyError) μ x)
      = μ :=
  decrypt_encryptWithCoins toyB toySecret toyError μ x (by norm_num) (bound := 1)
    (by decide) (by norm_num)

-- Without a noise margin, decryption can fail: errors of `±4` cross the quarter boundary.
example : decrypt toySecret
    (encryptWithCoins (LWE.publicMatrixInt toyB toySecret ![4, 0]) false ![true, false])
      = true := by
  decide +kernel

-- The parameter family's fresh-noise margin gives zero-error correctness for every generated key.
example (security : ℕ) (μ : Bool)
    {keys : PublicKey (Homomorphic.GSW.Parameters.dimension security)
        (Homomorphic.GSW.Parameters.samples security) (Homomorphic.GSW.Parameters.width security) ×
      (Fin (Homomorphic.GSW.Parameters.dimension security) →
        ZMod (2 ^ Homomorphic.GSW.Parameters.width security))}
    (hkeys : keys ∈ (ProbComp.eval (LWE.keyGen
      (Homomorphic.GSW.Parameters.dimension security) (Homomorphic.GSW.Parameters.samples security)
      (Homomorphic.GSW.Parameters.width security)
      (Homomorphic.GSW.Parameters.noise security))).support)
    {c : Ciphertext (Homomorphic.GSW.Parameters.dimension security)
      (Homomorphic.GSW.Parameters.width security)}
    (hc : c ∈ (ProbComp.eval (encrypt keys.1 μ)).support) : decrypt keys.2 c = μ := by
  have hmargin := Homomorphic.GSW.Parameters.fresh_margin security
  rw [Nat.mul_assoc] at hmargin
  exact keyGen_encrypt_correct (Homomorphic.GSW.Parameters.width_pos security) hmargin hkeys μ hc

-- An adaptive two-query adversary: the second query depends on the first ciphertext.
private noncomputable def adaptiveAdversary :
    LoRAdversary 1 2 4 (List (Ciphertext 1 4)) where
  start _ := PMF.pure []
  query transcript := PMF.pure (⟨false, (transcript.headD 0) 0 == 0⟩, transcript)
  receive transcript c := c :: transcript
  guess transcript := PMF.pure ((transcript.headD 0) 0 == 0)

-- The two-query bound applies to this adaptive adversary (numerically trivial at these sizes).
example : (Game.advantage
      (lorGame (PMF.uniformOfFintype (PublicKey 1 2 4)) 2 adaptiveAdversary false)
      (lorGame (PMF.uniformOfFintype (PublicKey 1 2 4)) 2 adaptiveAdversary true) : ℝ) ≤
    2 * Real.sqrt ((2 : ℝ) ^ ((1 + 1) * 4) / (2 : ℝ) ^ 2) := by
  exact_mod_cast lorGame_uniform_advantage_le 2 adaptiveAdversary

-- The reduction covers this adversary under the generated-key law with the actual noise law.
example : (Game.advantage
      (lorGame (LWE.publicMatrixLaw 1 2 4 (LWE.noiseLaw 4 1)) 2 adaptiveAdversary false)
      (lorGame (LWE.publicMatrixLaw 1 2 4 (LWE.noiseLaw 4 1)) 2 adaptiveAdversary
        true) : ℝ) ≤
    Game.advantage
        ((LWE.publicMatrixLaw 1 2 4 (LWE.noiseLaw 4 1)).bind
          (lorDistinguisher 2 adaptiveAdversary false))
        ((PMF.uniformOfFintype (PublicKey 1 2 4)).bind (lorDistinguisher 2 adaptiveAdversary false))
      + Game.advantage
        ((LWE.publicMatrixLaw 1 2 4 (LWE.noiseLaw 4 1)).bind
          (lorDistinguisher 2 adaptiveAdversary true))
        ((PMF.uniformOfFintype (PublicKey 1 2 4)).bind (lorDistinguisher 2 adaptiveAdversary true))
      + 2 * Real.sqrt ((2 : ℝ) ^ ((1 + 1) * 4) / (2 : ℝ) ^ 2) := by
  exact_mod_cast lorGame_advantage_le (LWE.noiseLaw 4 1) 2 adaptiveAdversary

-- A uniform PPT adversary choosing its messages from the public key and keeping it as state.
private def keyAdversary : Encryption.Adversary where
  choose _ pk := pure ((pk.headD false, !pk.headD false), pk)
  guess _ state ciphertext := pure (state.headD false ^^ ciphertext.headD false)

private theorem keyAdversary_isPPT : keyAdversary.IsPPT := by
  constructor <;> simp only [keyAdversary] <;> ppt

-- The honest encryption and decryption programs are strict PPT / polynomial-time for the
-- growing parameter family, and decrypt every generated key and ciphertext with zero error.
example : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => encryptSerialized (Homomorphic.GSW.Parameters.dimension p.1)
      (Homomorphic.GSW.Parameters.samples p.1) (Homomorphic.GSW.Parameters.width p.1)
      p.2.1 p.2.2) :=
  isPPTOn_encryptSerialized (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

example : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool =>
      decryptSerialized (Homomorphic.GSW.Parameters.dimension p.1)
        (Homomorphic.GSW.Parameters.width p.1) p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) encBool :=
  computableInPolyTime_decryptSerialized (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

-- Both bits round-trip on raw serialized keys and noisy ciphertexts via `decryptSerialized`.
example :
    decryptSerialized 1 4 (LWE.serializeSecret toySecret)
      (encryptWithCoinsSerialized 1 2 4
        (LWE.serializePublicMatrix (LWE.publicMatrixInt toyB toySecret toyError))
        false [true, false]) = false ∧
    decryptSerialized 1 4 (LWE.serializeSecret toySecret)
      (encryptWithCoinsSerialized 1 2 4
        (LWE.serializePublicMatrix (LWE.publicMatrixInt toyB toySecret toyError))
        true [true, true]) = true ∧
    decodeCiphertext 1 4
      (serializeCiphertext
        (encryptWithCoins (LWE.publicMatrixInt toyB toySecret toyError) true ![true, true])) =
      encryptWithCoins (LWE.publicMatrixInt toyB toySecret toyError) true ![true, true] := by
  decide +kernel

example (security : ℕ) (μ : Bool) {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (LWE.keyGenSerialized
      (Homomorphic.GSW.Parameters.dimension security) (Homomorphic.GSW.Parameters.samples security)
      (Homomorphic.GSW.Parameters.width security)
      (Homomorphic.GSW.Parameters.noise security))).support)
    {ciphertext : List Bool}
    (hc : ciphertext ∈ (ProbComp.eval (encryptSerialized
      (Homomorphic.GSW.Parameters.dimension security) (Homomorphic.GSW.Parameters.samples security)
      (Homomorphic.GSW.Parameters.width security) keys.1 μ)).support) :
    decryptSerialized (Homomorphic.GSW.Parameters.dimension security)
      (Homomorphic.GSW.Parameters.width security) keys.2 ciphertext = μ := by
  have hmargin := Homomorphic.GSW.Parameters.fresh_margin security
  rw [Nat.mul_assoc] at hmargin
  exact keyGenSerialized_encryptSerialized_correct
    (Homomorphic.GSW.Parameters.width_pos security) hmargin hkeys μ hc

-- The asymptotic theorem applies to an actual family; only decision LWE remains assumed.
example (hLWE : DecisionLWE Homomorphic.GSW.Parameters.dimension
      Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
      (fun k => LWE.noiseLaw (Homomorphic.GSW.Parameters.width k)
        (Homomorphic.GSW.Parameters.noise k))) :
    Negligible (fun k => Encryption.advantage
      (Encryption.game
        (fun k => LWE.keyGenSerialized (Homomorphic.GSW.Parameters.dimension k)
          (Homomorphic.GSW.Parameters.samples k) (Homomorphic.GSW.Parameters.width k)
          (Homomorphic.GSW.Parameters.noise k))
        (fun k => encryptSerialized (Homomorphic.GSW.Parameters.dimension k)
          (Homomorphic.GSW.Parameters.samples k) (Homomorphic.GSW.Parameters.width k))
        keyAdversary) k) :=
  indCPA_of_decisionLWE Homomorphic.GSW.Parameters.computableInPolyTime_dimension
    Homomorphic.GSW.Parameters.computableInPolyTime_samples
    Homomorphic.GSW.Parameters.computableInPolyTime_width
    (Filter.Eventually.of_forall Homomorphic.GSW.Parameters.entropy_margin) hLWE
    keyAdversary keyAdversary_isPPT

-- A stateful word-level adaptive multi-challenge adversary whose queries depend on the saved
-- state and latest ciphertext word in the reverse transcript, updating the saved state at every
-- query step.
private def wordAdaptiveAdversary : Encryption.LoRAdversary where
  start _ pk := pure pk
  query _ st transcript :=
    let b := (transcript.headD []).headD false
    pure ((st.headD false, b), b :: st)
  guess _ st transcript :=
    pure (st.headD false ^^ (transcript.headD []).headD false)

private theorem wordAdaptiveAdversary_isPPT : wordAdaptiveAdversary.IsPPT := by
  have htr : ComputableInPolyTime
      (fun x : ℕ × List Bool × List (List Bool) => x.2.2.headD [])
      Encryption.encLoRStageInput encBits :=
    (ComputableInPolyTime.headD (encA := encBits) (encL := encList encBits) []).comp
      (by fun_prop)
  refine ⟨?_, ?_, ?_, ⟨fun _ => 1, by fun_prop, ?_⟩⟩
  · simp only [wordAdaptiveAdversary]; ppt
  · simp only [wordAdaptiveAdversary]; ppt
  · simp only [wordAdaptiveAdversary]; ppt
  · intro _ st tr choice hchoice
    simp only [wordAdaptiveAdversary, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hchoice
    subst hchoice
    simp

-- Both the per-bit and hidden-bit multi-challenge Decision-LWE distinguishers are uniform strict
-- PPT for any polynomial-time query schedule, and yield asymptotic Q-query security.
example (bit : Bool) :
    IsPPT encBool (lorDistinguisherSerialized Homomorphic.GSW.Parameters.dimension
      Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
      (fun k => k + 2) wordAdaptiveAdversary bit) :=
  isPPT_lorDistinguisherSerialized (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    wordAdaptiveAdversary_isPPT bit

example :
    IsPPT encBool (lorLweDistinguisher Homomorphic.GSW.Parameters.dimension
      Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
      (fun k => k + 2) wordAdaptiveAdversary) :=
  isPPT_lorLweDistinguisher (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    wordAdaptiveAdversary_isPPT

example (hLWE : DecisionLWE Homomorphic.GSW.Parameters.dimension
      Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
      (fun k => LWE.noiseLaw (Homomorphic.GSW.Parameters.width k)
        (Homomorphic.GSW.Parameters.noise k))) :
    Negligible (fun k => Game.advantage
      (ProbComp.eval (lorGameSerialized Homomorphic.GSW.Parameters.dimension
        Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
        Homomorphic.GSW.Parameters.noise (fun k => k + 2) wordAdaptiveAdversary false k))
      (ProbComp.eval (lorGameSerialized Homomorphic.GSW.Parameters.dimension
        Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
        Homomorphic.GSW.Parameters.noise (fun k => k + 2) wordAdaptiveAdversary true k))) :=
  lorIndCPA_of_decisionLWE Homomorphic.GSW.Parameters.computableInPolyTime_dimension
    Homomorphic.GSW.Parameters.computableInPolyTime_samples
    Homomorphic.GSW.Parameters.computableInPolyTime_width (by fun_prop)
    (Filter.Eventually.of_forall Homomorphic.GSW.Parameters.entropy_margin) hLWE
    wordAdaptiveAdversary wordAdaptiveAdversary_isPPT

/-! ### Dual Regev -/

open Cslib.Crypto.DualRegev in
private def dualA : Matrix (Fin 2) (Fin 1) (ZMod (2 ^ 4)) := !![3; 6]

open Cslib.Crypto.DualRegev in
-- Both bits round-trip with a short secret and nonzero errors.
example : DualRegev.decrypt ![1, -1]
      (DualRegev.encryptWithCoins (publicKeyOf dualA ![1, -1]) false ![5] ![1, -1] 1) = false ∧
    DualRegev.decrypt ![1, -1]
      (DualRegev.encryptWithCoins (publicKeyOf dualA ![1, -1]) true ![5] ![1, 0] (-1)) = true := by
  decide +kernel

/-- The gadget matrix `(1, 2, 4)ᵀ` with binary decomposition as its preimage sampler. -/
private def gadgetTrapdoor : DualRegev.GPVTrapdoor 1 3 3 Unit where
  trapGen := pure (!![1; 2; 4], ())
  samplePre _ u := pure fun k => ((u 0).val.testBit k.val).toNat

private theorem gadget_preimage (u : Fin 1 → ZMod (2 ^ 3)) :
    DualRegev.castVector 3 (fun k : Fin 3 => (((u 0).val.testBit k.val).toNat : ℤ)) ᵥ*
      !![1; 2; 4] = u := by
  revert u
  decide +kernel

-- The trapdoor interface is satisfiable with entry bound one (a non-uniform gadget matrix).
example : gadgetTrapdoor.SamplesShortPreimages 1 := by
  intro keys hkeys u e he
  simp only [gadgetTrapdoor, ProbComp.eval_pure,
    PMF.mem_support_pure_iff] at hkeys he
  subst hkeys he
  exact ⟨gadget_preimage u, fun k => by simpa using Bool.toNat_le _⟩

open Cslib.Crypto.DualRegev in
private def dualToyPK : DualRegev.PublicKey 1 2 4 :=
  (dualA, ![3])

open Cslib.Crypto.DualRegev in
private def dualToyCT : DualRegev.Ciphertext 2 4 :=
  (![2, 9], 11)

open Cslib.Crypto.DualRegev in
-- Canonical serialization and zero-padded decoding roundtrip for public keys, secrets, and
-- ciphertexts, including empty inputs, excess trailing padding, and concrete `decryptSerialized`
-- round-trips on `false` and `true` with nonzero errors.
example :
    DualRegev.decodePublicKey 1 2 4 (DualRegev.serializePublicKey dualToyPK) = dualToyPK ∧
      (DualRegev.serializePublicKey dualToyPK).length = 12 ∧
      DualRegev.decodePublicKey 1 2 4 [] = (0, 0) ∧
      DualRegev.decodePublicKey 1 2 4
        (DualRegev.serializePublicKey dualToyPK ++ [true, true]) = dualToyPK ∧
      DualRegev.decodeCiphertext 2 4 (DualRegev.serializeCiphertext dualToyCT) = dualToyCT ∧
      (DualRegev.serializeCiphertext dualToyCT).length = 12 ∧
      DualRegev.decodeSecret 2 (DualRegev.serializeSecret ![1, 0]) = ![1, 0] ∧
      (DualRegev.serializeSecret ![1, 0]).length = 2 ∧
      DualRegev.decryptSerialized 2 4 (DualRegev.serializeSecret ![1, 0])
        (DualRegev.encryptWithCoinsSerialized 1 2 4
          (DualRegev.serializePublicKey (DualRegev.publicKeyOf dualA ![1, 0]))
          false ⟨[5], [1, -1], 1⟩) = false ∧
      DualRegev.decryptSerialized 2 4 (DualRegev.serializeSecret ![1, 0])
        (DualRegev.encryptWithCoinsSerialized 1 2 4
          (DualRegev.serializePublicKey (DualRegev.publicKeyOf dualA ![1, 0]))
          true ⟨[5], [1, 0], -1⟩) = true := by
  decide +kernel

-- Distributional bridges connect the serialized algorithms to the typed key and encryption laws.
example :
    (ProbComp.eval (DualRegev.keyGenSerialized 1 2 4)).map Prod.fst =
      (ProbComp.eval (DualRegev.keyGen 1 2 4)).map
        (fun keys => DualRegev.serializePublicKey keys.1) :=
  DualRegev.eval_keyGenSerialized_fst 1 2 4

example (μ : Bool) :
    ProbComp.eval (DualRegev.encryptSerialized 1 2 4 1
        (DualRegev.serializePublicKey dualToyPK) μ) =
      (ProbComp.eval (DualRegev.encrypt 1 dualToyPK μ)).map DualRegev.serializeCiphertext :=
  DualRegev.eval_encryptSerialized_serializePublicKey dualToyPK μ

-- Serialized dual-Regev key generation and encryption satisfy strict uniform PPT certificates
-- on the GSW parameter family.
example :
    IsPPTOn encUnary (encPair encBits encBits) (fun k => DualRegev.keyGenSerialized
      (Homomorphic.GSW.Parameters.dimension k) (Homomorphic.GSW.Parameters.samples k)
      (Homomorphic.GSW.Parameters.width k)) :=
  DualRegev.isPPTOn_keyGenSerialized (by fun_prop) (by fun_prop) (by fun_prop)

example :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits (fun p =>
      DualRegev.encryptSerialized (Homomorphic.GSW.Parameters.dimension p.1)
        (Homomorphic.GSW.Parameters.samples p.1) (Homomorphic.GSW.Parameters.width p.1)
        (Homomorphic.GSW.Parameters.noise p.1) p.2.1 p.2.2) :=
  DualRegev.isPPTOn_encryptSerialized (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)

example :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        DualRegev.decryptSerialized (Homomorphic.GSW.Parameters.samples p.1)
          (Homomorphic.GSW.Parameters.width p.1) p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool :=
  DualRegev.computableInPolyTime_decryptSerialized (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop)

example (μ : Bool) {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (DualRegev.keyGenSerialized 1 2 4)).support)
    {ciphertext : List Bool}
    (hc : ciphertext ∈ (ProbComp.eval (DualRegev.encryptSerialized 1 2 4 1 keys.1 μ)).support) :
    DualRegev.decryptSerialized 2 4 keys.2 ciphertext = μ :=
  DualRegev.keyGenSerialized_encryptSerialized_correct (by decide) (by decide) hkeys μ hc

-- The uniform hidden-bit (m + 1)-sample Decision-LWE reduction is uniform strict PPT.
example :
    IsPPT encBool (DualRegev.lweDistinguisher Homomorphic.GSW.Parameters.dimension
      Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width keyAdversary) :=
  DualRegev.isPPT_lweDistinguisher (by fun_prop) (by fun_prop) (by fun_prop) keyAdversary_isPPT

-- Concrete and asymptotic IND-CPA security instantiate on the GSW parameter family, assuming only
-- (m + 1)-sample Decision LWE.
example (security : ℕ) :
    Encryption.advantage
      (Encryption.game
        (fun k => DualRegev.keyGenSerialized (Homomorphic.GSW.Parameters.dimension k)
          (Homomorphic.GSW.Parameters.samples k) (Homomorphic.GSW.Parameters.width k))
        (fun k => DualRegev.encryptSerialized (Homomorphic.GSW.Parameters.dimension k)
          (Homomorphic.GSW.Parameters.samples k) (Homomorphic.GSW.Parameters.width k)
          (Homomorphic.GSW.Parameters.noise k))
        keyAdversary) security ≤
      2 * Game.advantage
        (distinguishingGame
          (LWE.realEnsemble Homomorphic.GSW.Parameters.dimension
            (fun k => Homomorphic.GSW.Parameters.samples k + 1)
            Homomorphic.GSW.Parameters.width
            (fun k => LWE.noiseLaw (Homomorphic.GSW.Parameters.width k)
              (Homomorphic.GSW.Parameters.noise k)) security)
          (DualRegev.lweDistinguisher Homomorphic.GSW.Parameters.dimension
            Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
            keyAdversary security))
        (distinguishingGame
          (LWE.uniformEnsemble Homomorphic.GSW.Parameters.dimension
            (fun k => Homomorphic.GSW.Parameters.samples k + 1)
            Homomorphic.GSW.Parameters.width security)
          (DualRegev.lweDistinguisher Homomorphic.GSW.Parameters.dimension
            Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
            keyAdversary security)) +
        DualRegev.hidingError (Homomorphic.GSW.Parameters.dimension security)
          (Homomorphic.GSW.Parameters.samples security)
          (Homomorphic.GSW.Parameters.width security) :=
  DualRegev.advantage_game_le Homomorphic.GSW.Parameters.dimension
    Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
    Homomorphic.GSW.Parameters.noise keyAdversary security

private theorem dualRegev_entropy_margin (security : ℕ) :
    Homomorphic.GSW.Parameters.width security * Homomorphic.GSW.Parameters.dimension security +
      2 * security ≤ Homomorphic.GSW.Parameters.samples security := by
  have hm := Homomorphic.GSW.Parameters.entropy_margin security
  rw [Homomorphic.GSW.Parameters.rows] at hm
  nlinarith

example (hLWE : DecisionLWE Homomorphic.GSW.Parameters.dimension
      (fun k => Homomorphic.GSW.Parameters.samples k + 1) Homomorphic.GSW.Parameters.width
      (fun k => LWE.noiseLaw (Homomorphic.GSW.Parameters.width k)
        (Homomorphic.GSW.Parameters.noise k))) :
    Negligible (fun k => Encryption.advantage
      (Encryption.game
        (fun k => DualRegev.keyGenSerialized (Homomorphic.GSW.Parameters.dimension k)
          (Homomorphic.GSW.Parameters.samples k) (Homomorphic.GSW.Parameters.width k))
        (fun k => DualRegev.encryptSerialized (Homomorphic.GSW.Parameters.dimension k)
          (Homomorphic.GSW.Parameters.samples k) (Homomorphic.GSW.Parameters.width k)
          (Homomorphic.GSW.Parameters.noise k))
        keyAdversary) k) :=
  DualRegev.indCPA_of_decisionLWE Homomorphic.GSW.Parameters.computableInPolyTime_dimension
    Homomorphic.GSW.Parameters.computableInPolyTime_samples
    Homomorphic.GSW.Parameters.computableInPolyTime_width
    (Filter.Eventually.of_forall dualRegev_entropy_margin) hLWE
    keyAdversary keyAdversary_isPPT

example (a b : DualRegev.SerializedKeyInputs) (hp : a.publicPart = b.publicPart)
    (hb : a.bits = b.bits) : a = b :=
  DualRegev.SerializedKeyInputs.ext hp hb

example (a b : DualRegev.SerializedEncCoins) (hs : a.secret = b.secret)
    (he : a.error = b.error) (hs0 : a.scalarError = b.scalarError) : a = b :=
  DualRegev.SerializedEncCoins.ext hs he hs0

section DualRegevOpened

open Cslib.Crypto.DualRegev (SerializedKeyInputs encSerializedKeyInputs SerializedEncCoins
  encSerializedEncCoins)

example : ComputableInPolyTime
    (fun inputs : SerializedKeyInputs =>
      ({ publicPart := inputs.publicPart, bits := inputs.bits } : SerializedKeyInputs))
    encSerializedKeyInputs encSerializedKeyInputs := by
  fun_prop

example : ComputableInPolyTime
    (fun coins : SerializedEncCoins =>
      ({ secret := coins.secret, error := coins.error,
         scalarError := coins.scalarError } : SerializedEncCoins))
    encSerializedEncCoins encSerializedEncCoins := by
  fun_prop

end DualRegevOpened

end CslibFrontierTests.Regev

namespace CslibFrontierTests.RegevUnopened

example : Turing.MultiTapeTM.ComputableInPolyTime
    (fun inputs : Cslib.Crypto.DualRegev.SerializedKeyInputs =>
      ({ publicPart := inputs.publicPart, bits := inputs.bits } :
        Cslib.Crypto.DualRegev.SerializedKeyInputs))
    Cslib.Crypto.DualRegev.encSerializedKeyInputs
    Cslib.Crypto.DualRegev.encSerializedKeyInputs := by
  fun_prop

example : Turing.MultiTapeTM.ComputableInPolyTime
    (fun coins : Cslib.Crypto.DualRegev.SerializedEncCoins =>
      ({ secret := coins.secret, error := coins.error,
         scalarError := coins.scalarError } : Cslib.Crypto.DualRegev.SerializedEncCoins))
    Cslib.Crypto.DualRegev.encSerializedEncCoins
    Cslib.Crypto.DualRegev.encSerializedEncCoins := by
  fun_prop

end CslibFrontierTests.RegevUnopened
