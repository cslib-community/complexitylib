/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.SchnorrSignature
import CslibFrontier.Foundations.Data.Nat.Bits

/-!
# Canonical word Schnorr in the random-oracle model

The statement remains an actual group element, while commitments and responses are arbitrary
words. Verification calls `schnorrSigVerifyBits` with the canonical public-key encoding. An accepted
commitment therefore has a group meaning without a group decoder. Response words are interpreted
modulo the group order, including noncanonical scalar representations.

The Fiat–Shamir instance retains the entire word hash domain. Only signer/verifier hash points use
`encPair encBits encBits`; other words remain ordinary keys in the same random oracle. The finite
bound uses ideal uniform scalar sampling. Native forger composition, efficient forking and the
actual key-generation/signing approximation hops are separate obligations.

## Main definitions

* `schnorrWordSigma`: the existing Schnorr algorithms with arbitrary word transcripts.
* `schnorrWordSimulate`, `schnorrWordExtract`: the encoded simulator and scalar extractor.
* `schnorrWordROMScheme`: the shared-ROM scheme with the entire word query domain.

## Main results

* `schnorrWordSigma_specialSoundness`: extraction from arbitrary accepting word transcripts.
* `schnorrWordSigma_specialHVZK`: perfect simulation of canonical honest transcripts.
* `succProbability_eufCmaGame_schnorrWordROMScheme_le`: the finite-query word ROM bound.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Sections 19.2 and 19.4. This module instantiates the existing Schnorr and Fiat–Shamir results.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Protocols.ROMSignature
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily) (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d)

/-- Schnorr with word commitments and responses, using the sole native verifier at a canonical
public key. The message argument of this explicit-challenge arithmetic verifier is immaterial;
the surrounding Fiat–Shamir scheme enforces the message/commitment hash point. -/
noncomputable def schnorrWordSigma :
    SigmaProtocol (ZMod (F.order d)) (F.Carrier d) (List Bool) (BitString m) (List Bool) where
  State := (F.schnorrBitSigma d hm).State
  commit x y := ((F.schnorrBitSigma d hm).commit x y).map (Prod.map (F.encode d) id)
  respond x y r c := F.encScalar d ((F.schnorrBitSigma d hm).respond x y r c)
  verify y t c z := F.schnorrSigVerifyBits (d, F.encode d y, [], (t, z), List.ofFn c)

/-- Acceptance recovers a canonical commitment for every response word. -/
theorem schnorrWordSigma_accepts_iff (u : F.Carrier d) (t z : List Bool) (c : BitString m) :
    (F.schnorrWordSigma d hm).Accepts u t c z ↔
      t = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
        F.challengeEmbedding d hm c • u) := by
  exact F.schnorrSigVerifyBits_eq_true_iff d u [] t z (List.ofFn c)

/-- On encoded commitments, the word verifier agrees with typed Schnorr after interpreting the
response scalar. No assumption on the response word is required. -/
theorem schnorrWordSigma_accepts_encode_iff (u t : F.Carrier d) (z : List Bool)
    (c : BitString m) :
    (F.schnorrWordSigma d hm).Accepts u (F.encode d t) c z ↔
      (F.schnorrBitSigma d hm).Accepts u t c (ofBits z : ZMod (F.order d)) := by
  rw [F.schnorrWordSigma_accepts_iff, (F.encode_injective d).eq_iff]
  change t = _ ↔ (schnorr _ _).Accepts _ _ _ _
  rw [schnorr_accepts_iff]
  constructor
  · intro h
    rw [h, sub_add_cancel]
  · intro h
    exact eq_sub_iff_add_eq.mpr h.symm

/-- Honest word transcripts are exactly the encodings of the existing typed transcripts. -/
theorem schnorrWordSigma_transcript (x : ZMod (F.order d)) (u : F.Carrier d)
    (c : BitString m) :
    (F.schnorrWordSigma d hm).transcript x u c =
      ((F.schnorrBitSigma d hm).transcript x u c).map
        (Prod.map (F.encode d) (F.encScalar d)) := by
  simp only [SigmaProtocol.transcript, schnorrWordSigma, PMF.map_comp]
  rfl

/-- The word instance retains honest completeness. -/
theorem schnorrWordSigma_complete :
    (F.schnorrWordSigma d hm).Complete fun x u => x • F.generator d = u := by
  intro x u hxu c tz htz
  rw [F.schnorrWordSigma_transcript] at htz
  obtain ⟨⟨t, z⟩, htz', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htz
  simp only [Prod.map_apply] at *
  rw [F.schnorrWordSigma_accepts_encode_iff]
  simpa only [schnorrBitSigma, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits,
    Nat.foldr_bit_bits, ZMod.natCast_zmod_val] using
    (schnorr_complete x u hxu c (t, z) htz')

/-- The existing linear extractor applied to scalar interpretations of the two response words.
It neither decodes the commitment nor assumes canonical responses. -/
def schnorrWordExtract (u : F.Carrier d) (_t : List Bool) (c : BitString m) (z : List Bool)
    (c' : BitString m) (z' : List Bool) : ZMod (F.order d) :=
  linearExtract (F.challengeEmbedding d hm) u (0 : F.Carrier d)
    c (ofBits z : ZMod (F.order d)) c' (ofBits z' : ZMod (F.order d))

/-- Special soundness for all word commitments and responses, at group-valued statements. -/
theorem schnorrWordSigma_specialSoundness :
    (F.schnorrWordSigma d hm).SpecialSoundness (fun x u => x • F.generator d = u)
      (F.schnorrWordExtract d hm) := by
  intro u t c z c' z' hc hz hz'
  have ht := (F.schnorrWordSigma_accepts_iff d hm u t z c).mp hz
  rw [ht, F.schnorrWordSigma_accepts_encode_iff] at hz hz'
  simpa only [schnorrWordExtract, linearExtract] using
    (schnorr_specialSoundness u _ c _ c' _ hc hz hz')

/-- Encode the existing perfect Schnorr simulator. -/
noncomputable def schnorrWordSimulate (u : F.Carrier d) (c : BitString m) :
    PMF (List Bool × List Bool) :=
  (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order d))
    (F.Carrier d) (F.generator d)) id (F.challengeEmbedding d hm) u c).map
      (Prod.map (F.encode d) (F.encScalar d))

/-- Perfect special honest-verifier zero knowledge of the actual word instance. -/
theorem schnorrWordSigma_specialHVZK :
    (F.schnorrWordSigma d hm).SpecialHVZK (fun x u => x • F.generator d = u)
      (F.schnorrWordSimulate d hm) where
  accepts u c tz htz := by
    obtain ⟨⟨t, z⟩, htz', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htz
    simp only [Prod.map_apply] at *
    rw [F.schnorrWordSigma_accepts_encode_iff]
    simpa only [schnorrBitSigma, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits,
      Nat.foldr_bit_bits, ZMod.natCast_zmod_val] using
      (schnorr_specialHVZK.accepts u c (t, z) htz')
  transcript_eq x u hxu c := by
    rw [schnorrWordSimulate, F.schnorrWordSigma_transcript,
      schnorr_specialHVZK.transcript_eq x u hxu c]
    rfl

/-- Encoding preserves the Schnorr commitment bound for every word, with zero mass outside the
canonical encoding range. -/
theorem schnorrWordSigma_commit_map_fst_le (x : ZMod (F.order d)) (u : F.Carrier d)
    (t : List Bool) :
    ((F.schnorrWordSigma d hm).commit x u).map Prod.fst t ≤ (F.order d : ℝ≥0∞)⁻¹ := by
  classical
  have hmap : ((F.schnorrWordSigma d hm).commit x u).map Prod.fst =
      (((F.schnorrBitSigma d hm).commit x u).map Prod.fst).map (F.encode d) := by
    simp only [schnorrWordSigma, PMF.map_comp]
    rfl
  rw [hmap, PMF.map_apply]
  by_cases ht : ∃ v, F.encode d v = t
  · obtain ⟨v, rfl⟩ := ht
    simp only [(F.encode_injective d).eq_iff, tsum_ite_eq']
    exact schnorr_commit_map_fst_le (F.generator_ne_zero d) x u v
  · have hne (v : F.Carrier d) : t ≠ F.encode d v := fun h => ht ⟨v, h.symm⟩
    simp only [hne, ite_false, tsum_zero, zero_le]

/-- Canonical word Schnorr signatures in the existing shared random-oracle game. Public keys
remain actual group elements; messages, signature components and every hash query are words.
Key generation and signing randomness use the ideal uniform scalar law. -/
noncomputable def schnorrWordROMScheme :
    Scheme (F.Carrier d) (ZMod (F.order d) × F.Carrier d) (List Bool)
      (List Bool × List Bool) (List Bool) (BitString m) :=
  fiatShamir (encPair encBits encBits) (F.schnorrWordSigma d hm)
    (schnorrKeyGen (F.generator d))

/-- Final verification queries the encoded message/commitment pair and invokes the native verifier.
Every other hash word remains available to the adversary. -/
theorem schnorrWordROMScheme_verify (u : F.Carrier d) (msg : List Bool)
    (sig : List Bool × List Bool) :
    (F.schnorrWordROMScheme d hm).verify u msg sig =
      (fun c => F.schnorrSigVerifyBits (d, F.encode d u, msg, sig, List.ofFn c)) <$>
        OracleComp.query (encPair encBits encBits (msg, sig.1)) := rfl

/-- With canonical commitment coins, signing invokes the existing native signing arithmetic on
exactly the challenge returned by the shared random oracle. -/
theorem schnorrWordROMScheme_sign (x r : ZMod (F.order d)) (u : F.Carrier d)
    (msg : List Bool) :
    (F.schnorrWordROMScheme d hm).sign (x, u) msg (F.encode d (r • F.generator d), r) =
      (fun c => F.schnorrSignCoins (d, F.encScalar d x, msg, F.encScalar d r, List.ofFn c)) <$>
        OracleComp.query (encPair encBits encBits (msg, F.encode d (r • F.generator d))) := by
  simp only [schnorrWordROMScheme, fiatShamir, schnorrWordSigma, schnorrBitSigma, schnorr,
    linear, schnorrSignCoins_encScalar, challengeEmbedding, smul_eq_mul]
  rfl

/-- Honest word signatures verify in the shared cache. -/
theorem schnorrWordROMScheme_correct : (F.schnorrWordROMScheme d hm).Correct :=
  fiatShamir_correct (encPair encBits encBits) (F.schnorrWordSigma_complete d hm)
    fun _ h => mem_support_schnorrKeyGen h

/-- The existing generic forking reduction instantiated with arbitrary word transcripts and hash
queries, returning zero on a failed fork. This is a distribution-level reduction, without a
native efficiency certificate. -/
noncomputable def schnorrWordROMSchemeReduction
    (A : Forger (F.Carrier d) (List Bool) (List Bool × List Bool) (List Bool) (BitString m))
    (Qs Qro : ℕ) : F.Carrier d → PMF (ZMod (F.order d)) :=
  FiatShamir.reduction (encPair encBits encBits) (F.schnorrWordSigma d hm)
    (F.schnorrWordSimulate d hm) (F.schnorrWordExtract d hm) 0 A Qs Qro

/-- The finite-query Schnorr bound for the actual word verifier. All hash words count, including
those outside the pair-encoding image. The challenge term uses `2 ^ m` injectively embedded
challenges, and the commitment term uses the prime group order. The one-way success term belongs
to the displayed distribution-level reduction; native efficiency and sampling approximation are
separate obligations. -/
theorem succProbability_eufCmaGame_schnorrWordROMScheme_le
    (A : Forger (F.Carrier d) (List Bool) (List Bool × List Bool) (List Bool) (BitString m))
    {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro) :
    (Game.succProbability (eufCmaGame (F.schnorrWordROMScheme d hm) A) : ℝ) ≤
      Qs * (Qs + Qro) / F.order d + (Qro + 1) / 2 ^ m +
        √((Qro + 1) * Game.succProbability (oneWayGame (schnorrKeyGen (F.generator d))
          (fun α u => α • F.generator d = u) (F.schnorrWordROMSchemeReduction d hm A Qs Qro))) := by
  have hq : (F.order d : ℝ≥0) ≠ 0 := by exact_mod_cast (F.prime_order d).ne_zero
  have h := succProbability_eufCmaGame_le (P := F.schnorrWordSigma d hm)
    (δ := (F.order d : ℝ≥0)⁻¹) (encPair encBits encBits)
    (fun _ h => mem_support_schnorrKeyGen h)
    ((F.schnorrWordSigma_specialSoundness d hm).specialSoundOn (schnorrKeyGen (F.generator d)))
    (F.schnorrWordSigma_specialHVZK d hm)
    (fun key _ t => by
      rw [ENNReal.coe_inv hq, ENNReal.coe_natCast]
      exact F.schnorrWordSigma_commit_map_fst_le d hm key.1 key.2 t) 0 A hA
  simpa only [schnorrWordROMScheme, schnorrWordROMSchemeReduction, NNReal.coe_inv,
    NNReal.coe_natCast, ← div_eq_mul_inv, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

end Cslib.Crypto.PrimeOrderGroupFamily
