/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Encryption.Hybrid.CompositionCCA
import CslibFrontier.Computability.Probabilistic.CoinTape
import CslibFrontier.Crypto.Computational.Encryption.KEMFromPKE.CCA
import CslibFrontierTests.Crypto.HybridDEMCCA
import CslibFrontierTests.Crypto.KEMFromPKECCA
import CslibFrontier.Tactic.PPT

/-!
# Full hybrid CCA composition clients

Check actual saved-coins key generation, the PRF Encrypt-then-MAC 3n-bit sampler and an
end-to-end encrypted-key KEM client. Native adaptive traces cover prechallenge overrides,
changed KEM components, malformed encodings, rejected replies and accepted empty values.
-/

namespace CslibFrontierTests.Crypto.HybridCompositionCCA

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.AuthenticatedEncryption
open CslibFrontierTests.Crypto.HybridDEMCCA
open CslibFrontierTests.Crypto.KEMFromPKECCA

/-- Every actual strict-PPT key generator has one native unary seed schedule and total native
postprocessor. Support holds for every seed, not merely for seeds of the selected width. -/
example (E : SymmetricCipher) : ∃ (keyLen : ℕ → ℕ) (F : ℕ → List Bool → List Bool),
    ComputableInPolyTime keyLen encUnary encUnary ∧
    ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2)
      (encPair encUnary encBits) encBits ∧
    (∀ n seed, F n seed ∈ (ProbComp.eval (E.keyGen n)).support) ∧
    ∀ n, (BitString.uniformList (keyLen n)).map (F n) = ProbComp.eval (E.keyGen n) := by
  obtain ⟨c, d, F, hF, hsupp, hlaw⟩ := E.keyGen_ppt.exists_total_seeded_evaluator
  refine ⟨fun n => c * (n + 1) ^ d, F, by fun_prop, hF, hsupp, ?_⟩
  intro n
  simpa only [encUnary_apply, List.length_replicate] using (hlaw n _ (le_refl _)).symm

/-- The actual framed EtM key consumes 3n independent random bits. -/
def splitKey (n : ℕ) (seed : List Bool) : List Bool :=
  encPair encBits encBits (seed.take n, seed.drop n)

theorem splitKey_polyTime : ComputableInPolyTime (fun p : ℕ × List Bool => splitKey p.1 p.2)
    (encPair encUnary encBits) encBits := by
  unfold splitKey
  fun_prop

theorem splitKey_law {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) (n : ℕ) :
    (BitString.uniformList (3 * n)).map (splitKey n) =
      ProbComp.eval ((prfEncryptThenMAC family hprf.polyTime hprf.length_eq).keyGen n) := by
  change (BitString.uniformList (3 * n)).map (splitKey n) = ProbComp.eval (do
    let ke ← BitString.sampleList n
    let km ← BitString.sampleList (2 * n)
    return encPair encBits encBits (ke, km))
  simp only [ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
  change (BitString.uniformList (3 * n)).bind (fun seed => PMF.pure (splitKey n seed)) = _
  rw [show 3 * n = n + 2 * n by omega]
  exact BitString.uniformList_bind_split n (2 * n)
    (fun ke km => PMF.pure (encPair encBits encBits (ke, km)))

theorem splitKey_supported {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) (n : ℕ) (seed : List Bool)
    (hlen : seed.length = 3 * n) :
    splitKey n seed ∈
      (ProbComp.eval
        ((prfEncryptThenMAC family hprf.polyTime hprf.length_eq).keyGen n)).support := by
  rw [← splitKey_law hprf n, PMF.mem_support_map_iff]
  exact ⟨seed, BitString.mem_support_uniformList_iff.mpr hlen, rfl⟩

/-- The sampler law is not a claim that the encoded 4n+1-bit key is uniform. At width zero,
actual keys are `[false]`; the uniform one-bit distribution also supports `[true]`. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    splitKey 0 [] = [false] ∧
      (BitString.uniformList 1) ≠
        ProbComp.eval ((prfEncryptThenMAC family hprf.polyTime hprf.length_eq).keyGen 0) := by
  constructor
  · rfl
  · intro h
    have hs : [true] ∈ (BitString.uniformList 1).support :=
      BitString.mem_support_uniformList_iff.mpr rfl
    rw [h, eval_prfKeyGen_zero hprf] at hs
    simp at hs

/-- Genuine end-to-end positive client: a CCA-secure PKE encapsulates 3n random bits, which
produce the existing PRF EtM cipher's actual keys. The conclusion is n-bit INDCCA2On. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (hsecure : WordINDCCA2 keyGen encrypt decrypt)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decrypt p.1 p.2.1 p.2.2) (encPair encUnary (encPair encBits encBits)) (encOption encBits))
    (hcorrect : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
      ∀ m ct, ct ∈ (ProbComp.eval (encrypt n keys.1 m)).support → decrypt n keys.2 ct = some m) :
    let E := prfEncryptThenMAC family hprf.polyTime hprf.length_eq
    INDCCA2On (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits encBits keyGen
      (hybridEncrypt (fun n pk => (fun kc => (splitKey n kc.1, kc.2)) <$>
        encryptKeyEncaps (fun n => 3 * n) encrypt n pk) E.encrypt)
      (hybridDecrypt (fun n sk ct => (decrypt n sk ct).map (splitKey n)) E.decrypt) := by
  apply hybrid_indcca2On _ (hsecure.indistinguishable_encryptKeyEncaps (by fun_prop))
    hprf.indcca_prfEncryptThenMAC.oneTimeINDCCA hkeyGen
    (isPPTOn_encryptKeyEncaps (by fun_prop) hencrypt) hdecrypt splitKey_polyTime (splitKey_law hprf)
  intro n keys hkeys kc hkc
  exact decrypt_encryptKeyEncaps_some decrypt (fun m ct _ hc => hcorrect n keys hkeys m ct hc) hkc

/-- The tight split map's correctness is checked on actual 3n-bit encapsulations. No real-key
length is silently inferred from asymptotic KEM security. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    (n : ℕ) (pk sk msg ct : List Bool) (hmsg : msg.length = n)
    (hct : ct ∈ (ProbComp.eval (hybridEncrypt
      (fun n pk => (fun kc => (splitKey n kc.1, kc.2)) <$>
        encryptKeyEncaps (fun n => 3 * n) tagEncrypt n pk)
      (prfEncryptThenMAC family hprf.polyTime hprf.length_eq).encrypt n pk msg)).support) :
    hybridDecrypt (fun n sk ct => (tagDecrypt n sk ct).map (splitKey n))
      (prfEncryptThenMAC family hprf.polyTime hprf.length_eq).decrypt n sk ct = some msg := by
  apply hybridDecrypt_postprocessed_hybridEncrypt _ (hct := hct) (hmsg := hmsg)
  · intro kc hkc
    apply decrypt_encryptKeyEncaps_some tagDecrypt (fun m c _ hc => ?_) hkc
    simp only [tagEncrypt, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hc
    subst c
    simp [tagDecrypt]
  · intro kc hkc
    apply splitKey_supported hprf
    simp only [encryptKeyEncaps, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkc
    obtain ⟨k, hk, c, _, hkc⟩ := hkc
    cases hkc
    exact BitString.length_of_mem_support_uniformList hk

/-- Both adaptive phases exercise the actual KEM reduction at width zero. The prechallenge
query succeeds with an empty message, the exact challenge rejects, and the changed component
is decapsulated through the external KEM oracle. -/
example (bit : Bool) :
    ProbComp.eval (kemCCARealGame fixedKeyGen fixedEncaps identityDecaps
      (hybridToKEMCCA echoCipher (fun _ _ => []) (fun _ ct => ct.length + 1)
        phaseAdversary bit) 0) = PMF.pure true := by
  cases bit <;> rfl

example (bit : Bool) :
    ProbComp.eval (kemCCAIdealGame (fun _ => 0) fixedKeyGen fixedEncaps identityDecaps
      (hybridToKEMCCA echoCipher (fun _ _ => []) (fun _ ct => ct.length + 1)
        phaseAdversary bit) 0) = PMF.pure true := by
  cases bit <;> rfl

example : IsOraclePPT encBool (hybridToKEMCCAHiddenBit echoCipher (fun _ _ => [])
    (fun _ ct => ct.length + 1) phaseAdversary) :=
  isOraclePPT_hybridToKEMCCAHiddenBit echoCipher (by fun_prop) (by fun_prop) phaseAdversary_ppt

example (bit : Bool) : IsPPTOn encUnary encBool (cca2GameOn
    (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits fixedKeyGen
    (hybridEncrypt (fun n pk => (fun kc => (([] : List Bool), kc.2)) <$> fixedEncaps n pk)
      echoCipher.encrypt)
    (hybridDecrypt (fun n sk ct => (identityDecaps n sk ct).map (fun _ => [])) echoCipher.decrypt)
    phaseAdversary bit) :=
  isPPTOn_hybridCCAGame echoCipher fixedKeyGen_ppt fixedEncaps_ppt identityDecaps_polyTime
    (by fun_prop) phaseAdversary_ppt bit

/-- Malformed aliases reject before any external call. -/
example : hybridKEMCCAHandler echoCipher (fun _ k => k) (fun _ ct => ct.length + 1)
    0 [] [true] ((), [true, true]) = pure [] := rfl

/-- A returned `none` remains failure even though the underlying echo cipher accepts empty
messages. A returned `some []` is accepted and encoded as `[true]`. -/
example :
    (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin (fun _ => pure []))
      (hybridKEMCCAHandler echoCipher (fun _ k => k) (fun _ ct => ct.length + 1)
        0 [] [] ((), encPair encBits encBits ([true], [])))) = pure [] ∧
    (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin (fun _ => pure [true]))
      (hybridKEMCCAHandler echoCipher (fun _ k => k) (fun _ ct => ct.length + 1)
        0 [] [] ((), encPair encBits encBits ([true], [])))) = pure [true] := by
  constructor <;> rfl

/-- Isolate the prechallenge reply so the real-hop correctness failure is observable. -/
def preOnlyAdversary : WordCCA2Adversary where
  choose := phaseAdversary.choose
  guess _ saved _ := pure (saved == [true])

example : preOnlyAdversary.IsPPT := by
  constructor
  · exact phaseAdversary_ppt.choose
  · exact (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => p.2.1 == [true])
      (encPair encUnary (encPair encBits encBits)) encBool).isOraclePPTOn

/-- The real-hop correctness premise matters: making decapsulation reject the distinguished
component changes a prechallenge reply, while the KEM reduction must answer it locally. -/
example :
    ProbComp.eval (cca2GameOn
      (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits fixedKeyGen
      (hybridEncrypt fixedEncaps echoCipher.encrypt)
      (hybridDecrypt (fun _ _ _ => none) echoCipher.decrypt) preOnlyAdversary false 0) =
        PMF.pure false ∧
    ProbComp.eval (kemCCARealGame fixedKeyGen fixedEncaps (fun _ _ _ => none)
      (hybridToKEMCCA echoCipher (fun _ _ => []) (fun _ ct => ct.length + 1)
        preOnlyAdversary false) 0) = PMF.pure true := by
  constructor <;> rfl

/-- An invalid n-bit challenge contributes false in both worlds. -/
example (bit : Bool) : ProbComp.eval (kemCCARealGame fixedKeyGen fixedEncaps identityDecaps
    (hybridToKEMCCA echoCipher (fun _ _ => []) (fun _ ct => ct.length + 1)
      phaseAdversary bit) 1) = PMF.pure false := rfl

noncomputable def keyCheckedCipher : SymmetricCipher where
  keyGen _ := pure []
  encrypt _ _ msg := pure msg
  decrypt _ key ct := if key == [] then some ct else none
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by fun_prop
  decrypt_encrypt := by
    intro n key hk msg _ ct hc
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hk hc
    subst key
    subst ct
    rfl

/-- Every successful forwarded raw key is postprocessed too: mapping the returned nonempty
key to `[]` succeeds, while omitting that map would fail in this key-sensitive cipher. -/
example :
    (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin (fun _ => pure [true, true]))
      (hybridKEMCCAHandler keyCheckedCipher (fun _ _ => []) (fun _ ct => ct.length + 1)
        0 [] [] ((), encPair encBits encBits ([true], [])))) = pure [true] ∧
    (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin (fun _ => pure [true, true]))
      (hybridKEMCCAHandler keyCheckedCipher (fun _ k => k) (fun _ ct => ct.length + 1)
        0 [] [] ((), encPair encBits encBits ([true], [])))) = pure [] := by
  constructor <;> rfl

/-- A zero-width KEM has identical actual real/ideal experiments for every adaptive adversary. -/
example : Game.Indistinguishable
    (fun B n => ProbComp.eval (kemCCARealGame fixedKeyGen fixedEncaps identityDecaps B n))
    (fun B n => ProbComp.eval (kemCCAIdealGame (fun _ => 0)
      fixedKeyGen fixedEncaps identityDecaps B n)) (IsOraclePPT encBool) := by
  intro B _
  have h : ∀ n, ProbComp.eval (kemCCARealGame fixedKeyGen fixedEncaps identityDecaps B n) =
      ProbComp.eval (kemCCAIdealGame (fun _ => 0) fixedKeyGen fixedEncaps identityDecaps B n) := by
    intro n
    simp [kemCCARealGame, kemCCAIdealGame, kemIdealGameWith, kemRealGameWith,
      fixedKeyGen, fixedEncaps, BitString.sampleList]
  simpa only [h, Game.advantage_self] using negligible_zero

/-- A perfect KEM alone does not secure the hybrid: the echo DEM reveals the message bit. -/
example (n : ℕ) : Game.advantage
    (ProbComp.eval (cca2GameOn
      (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits fixedKeyGen
      (hybridEncrypt fixedEncaps echoCipher.encrypt)
      (hybridDecrypt identityDecaps echoCipher.decrypt) headAdversary false (n + 1)))
    (ProbComp.eval (cca2GameOn
      (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits fixedKeyGen
      (hybridEncrypt fixedEncaps echoCipher.encrypt)
      (hybridDecrypt identityDecaps echoCipher.decrypt) headAdversary true (n + 1))) = 1 := by
  simp [cca2GameOn, fixedKeyGen, fixedEncaps, hybridEncrypt, echoCipher, headAdversary,
    ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state, encPair_apply, encBits_apply,
    dropFrame, List.replicate_succ, Game.advantage, Game.succProbability]

end CslibFrontierTests.Crypto.HybridCompositionCCA
