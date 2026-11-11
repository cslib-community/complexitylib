/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.SchnorrSignature.NativeROM
import Complexity.Probability.PMF.Bind

/-!
# Encoded Schnorr signatures in the shared random-oracle game

The existing `ROMSignature.Scheme` can expose word public keys and outer signature words while
retaining the sole native verifier. Key and nonce laws are explicit: the representation bridge
does not identify actual sampling with uniform sampling. A forger receives encoded canonical
public keys and signing replies; all hash words remain unchanged, and every final signature word
is processed by the existing total pair decoder, without a framing rejection.

## Main definitions

* `schnorrEncodedROMScheme`: the existing scheme model with word keys and signatures.
* `schnorrDecodedForger`: canonical public-key input and total signature-output decoding.

## Main results

* `callBounded_schnorrDecodedForger`: both call budgets are preserved.
* `runWith_schnorrROMSign_encoded`, `runWith_schnorrROMVerify_encoded`: joint native realization
  with the actual nonce law and typed-width hash replies.
* `runWith_schnorrDecodedForger`: the ideal shared cache and signing-message log are preserved.
* `eufCmaGame_schnorrEncodedROMScheme_eq`: exact ideal game equality for every word forger.

Actual key-generation and adaptive signing errors, and native realization of the full forking
reduction, remain separate obligations. No efficient public-key decoder is assumed or introduced.

## References

Original representation adapters for the existing Schnorr ROM scheme and native algorithms.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Protocols Protocols.SigmaProtocol Protocols.ROMSignature OracleComp
open Turing.MultiTapeTM

variable (F : PrimeOrderGroupFamily)

/-- The concrete word interface with explicit key and scalar-nonce laws. Verification accepts
exactly what the existing native verifier accepts after total pair decoding, even when the outer
signature is not a pair encoding. Malformed public keys receive the native algorithm's behavior;
the representation theorem uses only encoded group public keys. -/
noncomputable def schnorrEncodedROMScheme (d : F.Desc) (m : ℕ)
    (keyLaw : PMF (List Bool × List Bool)) (nonceLaw : PMF (ZMod (F.order d))) :
    Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) (BitString m) where
  keyGen := keyLaw
  SignCoins := ZMod (F.order d)
  signCoins _ _ := nonceLaw
  sign sk msg r :=
    (fun c => encPair encBits encBits
      (F.schnorrSignCoins (d, sk, msg, F.encScalar d r, List.ofFn c))) <$>
      query (encPair encBits encBits (msg, F.schnorrCommitBits (d, F.encScalar d r)))
  verify pk msg sig :=
    let tz := (Decoder.bits.pair Decoder.bits).decode sig
    (fun c => F.schnorrSigVerifyBits (d, pk, msg, tz, List.ofFn c)) <$>
      query (encPair encBits encBits (msg, tz.1))

/-- Adapt an existing word forger without changing its coins or hash queries. Signing replies
are encoded, the public key is encoded, and the final outer signature is total-decoded. -/
def schnorrDecodedForger (d : F.Desc) {Digest : Type}
    (A : Forger (List Bool) (List Bool) (List Bool) (List Bool) Digest) :
    Forger (F.Carrier d) (List Bool) (List Bool × List Bool) (List Bool) Digest where
  Coins := A.Coins
  coins := A.coins
  forge u coins := Prod.map id (Decoder.bits.pair Decoder.bits).decode <$>
    interpret (sumHandler
      (fun msg => encPair encBits encBits <$>
        query (spec := ForgerSpec _ _ _ Digest) (Sum.inl msg))
      (fun word => query (spec := ForgerSpec _ _ _ Digest) (Sum.inr word)))
      (A.forge (F.encode d u) coins)

/-- Both call budgets are preserved on every public key and every forger coin value. -/
theorem callBounded_schnorrDecodedForger (d : F.Desc) {Digest : Type}
    {A : Forger (List Bool) (List Bool) (List Bool) (List Bool) Digest} {Qs Qro : ℕ}
    (hA : A.CallBounded Qs Qro) : (F.schnorrDecodedForger d A).CallBounded Qs Qro := by
  intro u coins
  let route : (q : List Bool ⊕ List Bool) →
      OracleComp (ForgerSpec (List Bool) (List Bool) (List Bool × List Bool) Digest)
        (ForgerSpec (List Bool) (List Bool) (List Bool) Digest q) :=
    sumHandler (fun msg => encPair encBits encBits <$> query (Sum.inl msg))
      (fun word => query (Sum.inr word))
  have hroute (cost : List Bool ⊕ List Bool → ℕ) (q : List Bool ⊕ List Bool) :
      IsCostBounded cost (route q) (cost q) := by
    cases q with
    | inl msg => exact (isCostBounded_map_iff _ _ _).mpr (IsCostBounded.query _)
    | inr word => exact IsCostBounded.query _
  constructor
  · exact (isCostBounded_map_iff _ _ _).mpr (IsCostBounded.interpret (hroute signingCost)
      (hA (F.encode d u) coins).1)
  · exact (isCostBounded_map_iff _ _ _).mpr (IsCostBounded.interpret (hroute hashCost)
      (hA (F.encode d u) coins).2)

variable (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d)
  (keyLaw : PMF (List Bool × List Bool)) (nonceLaw : PMF (ZMod (F.order d)))

/-- Canonical scalar keys make encoded signing exactly the encoding of word-pair signing. -/
theorem schnorrEncodedROMScheme_sign_encScalar (x r : ZMod (F.order d)) (u : F.Carrier d)
    (msg : List Bool) :
    (F.schnorrEncodedROMScheme d m keyLaw nonceLaw).sign (F.encScalar d x) msg r =
      encPair encBits encBits <$>
        (F.schnorrWordROMScheme d hm).sign (x, u) msg
          (F.encode d (r • F.generator d), r) := by
  rw [F.schnorrWordROMScheme_sign d hm]
  simp only [schnorrEncodedROMScheme, F.schnorrCommitBits_encScalar, Functor.map_map]

/-- Total signature decoding agrees with the word-pair verifier for every outer word. -/
theorem schnorrEncodedROMScheme_verify_encode (u : F.Carrier d) (msg sig : List Bool) :
    (F.schnorrEncodedROMScheme d m keyLaw nonceLaw).verify (F.encode d u) msg sig =
      (F.schnorrWordROMScheme d hm).verify u msg
        ((Decoder.bits.pair Decoder.bits).decode sig) := rfl

include hm in
/-- The native signer realizes the encoded scheme with the actual scalar-nonce law, retaining
arbitrary external state. This is an exact actual-sampling law, not a uniform-sampling claim. -/
theorem runWith_schnorrROMSign_encoded (n : ℕ) (x : ZMod (F.order d))
    {Store : Type} (reply : List Bool → StateT Store PMF (BitString m))
    (msg : List Bool) (state : Store) :
    ProbOracleComp.runWith
      (fun (q : Unit × List Bool) st => (reply q.2 st).map (Prod.map List.ofFn id))
      (F.schnorrROMSign n d m (F.encScalar d x) msg) state =
      ((F.schnorrEncodedROMScheme d m keyLaw
        ((ProbComp.eval (F.sampleExp n d)).map Nat.cast)).signCoins (F.encScalar d x) msg).bind
          fun r => OracleComp.runWith reply
            ((F.schnorrEncodedROMScheme d m keyLaw
              ((ProbComp.eval (F.sampleExp n d)).map Nat.cast)).sign (F.encScalar d x) msg r)
            state := by
  rw [F.runWith_schnorrROMSign d hm reply n x 0 msg state]
  apply PMF.bind_congr_on_support
  intro r _
  rw [F.schnorrEncodedROMScheme_sign_encScalar d hm keyLaw _ x r 0 msg, runWith_map]

include hm in
/-- The native verifier realizes the encoded scheme for every outer signature word and every
starting state, under canonical public keys and typed-width hash replies. -/
theorem runWith_schnorrROMVerify_encoded (u : F.Carrier d) {Store : Type}
    (reply : List Bool → StateT Store PMF (BitString m)) (msg sig : List Bool) (state : Store) :
    ProbOracleComp.runWith
      (fun (q : Unit × List Bool) st => (reply q.2 st).map (Prod.map List.ofFn id))
      (F.schnorrROMVerify d m (F.encode d u) msg sig) state =
      OracleComp.runWith reply
        ((F.schnorrEncodedROMScheme d m keyLaw nonceLaw).verify (F.encode d u) msg sig) state := by
  rw [F.runWith_schnorrROMVerify d hm reply u msg sig state,
    F.schnorrEncodedROMScheme_verify_encode d hm]

/-- Ideal key generation is exactly the encoding of the canonical word-ROM key law. The actual
native key law remains separate and is compared by `closeTo_schnorrSigKeyGen`. -/
theorem schnorrEncodedROMScheme_keyGen_ideal :
    (F.schnorrEncodedROMScheme d m (F.schnorrIdealKeyGen d) nonceLaw).keyGen =
      ((F.schnorrWordROMScheme d hm).keyGen).map
        (fun keys => (F.encode d keys.1, F.encScalar d keys.2.1)) := by
  simp only [schnorrEncodedROMScheme, schnorrIdealKeyGen, schnorrWordROMScheme, fiatShamir,
    schnorrKeyGen, PMF.map_comp]
  rfl

/-- Ideal signing preserves the joint encoded signature and external state. The hash handler
is arbitrary, so the law applies to every starting shared cache, including junk query entries. -/
theorem runWith_schnorrEncodedROMScheme_sign_ideal (x : ZMod (F.order d)) (u : F.Carrier d)
    {Store : Type} (reply : List Bool → StateT Store PMF (BitString m))
    (msg : List Bool) (state : Store) :
    ((F.schnorrEncodedROMScheme d m keyLaw (PMF.uniformOfFintype (ZMod (F.order d)))).signCoins
      (F.encScalar d x) msg).bind (fun r => runWith reply
        ((F.schnorrEncodedROMScheme d m keyLaw (PMF.uniformOfFintype (ZMod (F.order d)))).sign
          (F.encScalar d x) msg r) state) =
      (((F.schnorrWordROMScheme d hm).signCoins (x, u) msg).bind fun coins =>
        runWith reply ((F.schnorrWordROMScheme d hm).sign (x, u) msg coins) state).map
          (Prod.map (encPair encBits encBits) id) := by
  change (PMF.uniformOfFintype (ZMod (F.order d))).bind (fun r => runWith reply
    ((F.schnorrEncodedROMScheme d m keyLaw (PMF.uniformOfFintype (ZMod (F.order d)))).sign
      (F.encScalar d x) msg r) state) = _
  simp only [schnorrWordROMScheme, fiatShamir, schnorrWordSigma, schnorrBitSigma, schnorr,
    linear, PMF.map_comp, PMF.map_bind, PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro r _
  rw [F.schnorrEncodedROMScheme_sign_encScalar d hm keyLaw _ x r u msg, runWith_map]
  rfl

/-- In the ideal specialization the adapted forger preserves the complete shared cache and
message log. Every final signature word is decoded, with no image or canonicality premise. -/
theorem runWith_schnorrDecodedForger
    (A : Forger (List Bool) (List Bool) (List Bool) (List Bool) (BitString m))
    (x : ZMod (F.order d)) (u pk : F.Carrier d) (coins : A.Coins)
    (state : List (List Bool × BitString m) × List (List Bool)) :
    runWith (handler (F.schnorrWordROMScheme d hm) (x, u))
      ((F.schnorrDecodedForger d A).forge pk coins) state =
      (runWith (handler (F.schnorrEncodedROMScheme d m keyLaw
        (PMF.uniformOfFintype (ZMod (F.order d)))) (F.encScalar d x))
        (A.forge (F.encode d pk) coins) state).map
          (Prod.map (Prod.map id (Decoder.bits.pair Decoder.bits).decode) id) := by
  unfold schnorrDecodedForger
  rw [runWith_map]
  congr 1
  unfold runWith
  rw [interpret_interpret]
  congr 2 with q : 1
  cases q with
  | inl msg =>
    funext st
    simp only [sumHandler, interpret_map, interpret_query]
    change ((encPair encBits encBits <$>
      handler (F.schnorrWordROMScheme d hm) (x, u) (Sum.inl msg)).run st) = _
    rw [StateT.run_map]
    have h := F.runWith_schnorrEncodedROMScheme_sign_ideal d hm keyLaw x u
      (oracle (BitString m)) msg st.1
    have hlog := congrArg (PMF.map (fun out => (out.1, (out.2, msg :: st.2)))) h.symm
    simpa only [StateT.run,
      handler, PMF.monad_map_eq_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, Prod.map, id_eq,
      runWith] using hlog
  | inr word => simp [sumHandler, interpret_query, handler]

/-- Exact equality of the existing ideal EUF-CMA games after changing key and signature
representations. All outer signature words are total-decoded, every hash word remains distinct,
and freshness depends only on the unchanged final message and signing log. Actual key and nonce
sampling require separate statistical transport. -/
theorem eufCmaGame_schnorrEncodedROMScheme_eq
    (A : Forger (List Bool) (List Bool) (List Bool) (List Bool) (BitString m)) :
    eufCmaGame (F.schnorrEncodedROMScheme d m (F.schnorrIdealKeyGen d)
      (PMF.uniformOfFintype (ZMod (F.order d)))) A =
      eufCmaGame (F.schnorrWordROMScheme d hm) (F.schnorrDecodedForger d A) := by
  unfold eufCmaGame
  rw [F.schnorrEncodedROMScheme_keyGen_ideal d hm]
  simp only [PMF.monad_bind_eq_bind, PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro keys _
  apply PMF.bind_congr_on_support
  intro coins _
  change (runWith _ (A.forge (F.encode d keys.1) coins) ([], [])).bind _ =
    (runWith _ ((F.schnorrDecodedForger d A).forge keys.1 coins) ([], [])).bind _
  rw [F.runWith_schnorrDecodedForger d hm (F.schnorrIdealKeyGen d) A
    keys.2.1 keys.2.2 keys.1 coins ([], []), PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro out _
  simp only [Function.comp_def, Prod.map, id_eq,
    F.schnorrEncodedROMScheme_verify_encode d hm]

end Cslib.Crypto.PrimeOrderGroupFamily
