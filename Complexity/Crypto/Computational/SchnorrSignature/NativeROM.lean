/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Crypto.Computational.SchnorrSignature.WordROM
public import Complexity.Computability.Probabilistic.Oracle.Composition
public import Complexity.Languages.Probabilistic.Oracle.Interaction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PPT

/-!
# Native sampled Schnorr signing and verification in the ROM

The actual signer samples `sampleExp`, normalizes the nonce, hashes the encoded message/commitment
pair, reads at most the challenge width, and invokes the existing response arithmetic. The verifier
uses the existing total signature-pair decoder and sole canonical-recovery verifier. Runtime
certificates charge the full inputs and apply even to arbitrary external replies.

The semantic comparison uses caches whose answers are `BitString m`; every cached answer therefore
has exactly the required width. It does not identify arbitrary raw-word caches with that typed
oracle. The per-signature error comes from the actual nonce sampler, separately from the existing
key-generation error `closeTo_schnorrSigKeyGen`, also at most `2⁻ⁿ`. Adaptive game composition and
efficient forking remain separate obligations.

## Main definitions

* `schnorrROMSign`: sampled native signing with one bounded hash-reply read.
* `schnorrROMVerify`: native verification using the existing total pair decoder.

## Main results

* `isOraclePPTOn_schnorrROMSign`, `isOraclePPTOn_schnorrROMVerify`: full-input native certificates.
* `runWith_schnorrROMSign`, `runWith_schnorrROMVerify`: exact joint realization laws.
* `closeTo_runWith_schnorrROMSign`: per-signature nonce-sampling error with external state retained.

## References

Original native realization of the existing Schnorr ROM instance, using the sampling law already
proved for `sampleExp` and the arithmetic algorithms from `SchnorrSignature.lean`.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Protocols.ROMSignature
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- Sample a nonce, normalize it modulo the actual group order, and sign using one hash query.
Only the first `m` reply bits are read, including for arbitrary malformed or overlong replies. -/
noncomputable def schnorrROMSign (n : ℕ) (d : F.Desc) (m : ℕ) (sk msg : List Bool) :
    WordOracleComp Unit (List Bool) := do
  let r ← ProbOracleComp.sample (F.sampleExp n d)
  let nonce := (r % F.order d).bits
  let t := F.schnorrCommitBits (d, nonce)
  let c ← List.take m <$> ProbOracleComp.query ((), encPair encBits encBits (msg, t))
  return encPair encBits encBits (t, F.schnorrRespondBits (d, sk, nonce, c))

/-- Decode the signature with the existing total pair decoder, hash its message/commitment point,
and invoke the sole native verifier. Only the first `m` reply bits are read. -/
def schnorrROMVerify (d : F.Desc) (m : ℕ) (pk msg sig : List Bool) :
    WordOracleComp Unit Bool := do
  let tz := (Decoder.bits.pair Decoder.bits).decode sig
  let c ← List.take m <$> ProbOracleComp.query ((), encPair encBits encBits (msg, tz.1))
  return F.schnorrSigVerifyBits (d, pk, msg, tz, c)

/-- The actual signer is uniformly strict oracle-PPT in the full security parameter, group
description, challenge width, secret key and message. Both numeric parameters are unary. -/
theorem isOraclePPTOn_schnorrROMSign :
    IsOraclePPTOn
      (encPair encUnary (encPair F.encDesc (encPair encUnary (encPair encBits encBits)))) encBits
      (fun p : ℕ × F.Desc × ℕ × List Bool × List Bool =>
        F.schnorrROMSign p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let E := encPair encUnary (encPair F.encDesc (encPair encUnary (encPair encBits encBits)))
  have hn : ComputableInPolyTime
      (fun p : ℕ × F.Desc × ℕ × List Bool × List Bool => p.1) E encUnary := by fun_prop
  have hd : ComputableInPolyTime
      (fun p : ℕ × F.Desc × ℕ × List Bool × List Bool => p.2.1) E F.encDesc := by fun_prop
  unfold schnorrROMSign
  apply (F.isPPTOn_sampleExp hn hd).isOraclePPTOn.bind_with
  let EM := encPair E encNat
  have hinput := ComputableInPolyTime.fst E encNat
  have hd' := hd.comp hinput
  have hr := ComputableInPolyTime.snd E encNat
  have hq := F.computableInPolyTime_order.comp hd'
  have hnonce := (ComputableInPolyTime.binary_mod.comp (hr.prod hq)).encoding_comp
  have ht := F.computableInPolyTime_schnorrCommitBits.comp (hd'.prod hnonce)
  have hm : ComputableInPolyTime
      (fun p : (ℕ × F.Desc × ℕ × List Bool × List Bool) × ℕ => p.1.2.2.1) EM encUnary := by
    fun_prop
  have hsk : ComputableInPolyTime
      (fun p : (ℕ × F.Desc × ℕ × List Bool × List Bool) × ℕ => p.1.2.2.2.1) EM encBits := by
    fun_prop
  have hmsg : ComputableInPolyTime
      (fun p : (ℕ × F.Desc × ℕ × List Bool × List Bool) × ℕ => p.1.2.2.2.2) EM encBits := by
    fun_prop
  have hquery := IsOraclePPTOn.query_take' () (hmsg.prod ht).encoding_comp hm
  simp only [bind_pure_comp]
  apply hquery.map_with'
  have hfst := ComputableInPolyTime.fst EM encBits
  have hc := ComputableInPolyTime.snd EM encBits
  have hz := F.computableInPolyTime_schnorrRespondBits.comp
    ((hd'.comp hfst).prod ((hsk.comp hfst).prod ((hnonce.comp hfst).prod hc)))
  exact ((ht.comp hfst).prod hz).encoding_comp

/-- The native verifier is uniformly strict oracle-PPT in the full description, unary challenge
width, public key, message and signature word, for every external oracle reply. -/
theorem isOraclePPTOn_schnorrROMVerify :
    IsOraclePPTOn
      (encPair F.encDesc (encPair encUnary (encPair encBits (encPair encBits encBits)))) encBool
      (fun p : F.Desc × ℕ × List Bool × List Bool × List Bool =>
        F.schnorrROMVerify p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let E := encPair F.encDesc (encPair encUnary (encPair encBits (encPair encBits encBits)))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × ℕ × List Bool × List Bool × List Bool => p.1) E F.encDesc := by fun_prop
  have hm : ComputableInPolyTime
      (fun p : F.Desc × ℕ × List Bool × List Bool × List Bool => p.2.1) E encUnary := by fun_prop
  have hpk : ComputableInPolyTime
      (fun p : F.Desc × ℕ × List Bool × List Bool × List Bool => p.2.2.1) E encBits := by fun_prop
  have hmsg : ComputableInPolyTime
      (fun p : F.Desc × ℕ × List Bool × List Bool × List Bool => p.2.2.2.1) E encBits := by
    fun_prop
  have hsig : ComputableInPolyTime
      (fun p : F.Desc × ℕ × List Bool × List Bool × List Bool => p.2.2.2.2) E encBits := by
    fun_prop
  have htz := (Decoder.bits.pair Decoder.bits).computableInPolyTime.comp hsig
  have hquery := IsOraclePPTOn.query_take' () (hmsg.prod htz.fst').encoding_comp hm
  unfold schnorrROMVerify
  simp only [bind_pure_comp]
  apply hquery.map_with'
  have hfst := ComputableInPolyTime.fst E encBits
  have hc := ComputableInPolyTime.snd E encBits
  exact F.computableInPolyTime_schnorrSigVerifyBits.comp
    ((hd.comp hfst).prod ((hpk.comp hfst).prod ((hmsg.comp hfst).prod
      ((htz.comp hfst).prod hc))))

variable (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d)
  {Store : Type} (reply : List Bool → StateT Store PMF (BitString m))

/-- Exact joint realization of sampled signing under any stateful `m`-bit hash oracle. The nonce
law is the actual sampler mapped modulo the order; no coupling or uniform-sampling equality is
assumed. The external state is retained alongside the encoded signature. -/
theorem runWith_schnorrROMSign (n : ℕ) (x : ZMod (F.order d)) (u : F.Carrier d)
    (msg : List Bool) (state : Store) :
    ProbOracleComp.runWith
      (fun (q : Unit × List Bool) st => (reply q.2 st).map (Prod.map List.ofFn id))
      (F.schnorrROMSign n d m (F.encScalar d x) msg) state =
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).bind fun r =>
        (OracleComp.runWith reply ((F.schnorrWordROMScheme d hm).sign (x, u) msg
          (F.encode d (r • F.generator d), r)) state).map
            (Prod.map (encPair encBits encBits) id) := by
  unfold schnorrROMSign
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, PMF.bind_map, PMF.bind_map]
  congr 1 with r : 1
  have hnonce : (r % F.order d).bits = F.encScalar d (r : ZMod (F.order d)) := by
    simp only [encScalar, Function.Embedding.coeFn_mk, encNat_apply, ZMod.val_natCast]
  simp only [Function.comp_def, hnonce, schnorrCommitBits_encScalar,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    ProbOracleComp.runWith_pure, PMF.bind_map,
    PMF.map_comp, schnorrWordROMScheme_sign,
    OracleComp.runWith_map, OracleComp.runWith_query]
  congr 1 with answer : 1
  rcases answer with ⟨c, st⟩
  have hc : (List.ofFn c).take m = List.ofFn c := List.take_of_length_le (by simp)
  simp [hc, schnorrSignCoins_encScalar, Prod.map_apply]

/-- Verification agrees exactly with the word ROM scheme after the existing total outer-signature
pair decoder. The equality retains all external state and permits arbitrary signature words. -/
theorem runWith_schnorrROMVerify (u : F.Carrier d) (msg sig : List Bool) (state : Store) :
    ProbOracleComp.runWith
      (fun (q : Unit × List Bool) st => (reply q.2 st).map (Prod.map List.ofFn id))
      (F.schnorrROMVerify d m (F.encode d u) msg sig) state =
      OracleComp.runWith reply ((F.schnorrWordROMScheme d hm).verify u msg
        ((Decoder.bits.pair Decoder.bits).decode sig)) state := by
  simp only [schnorrROMVerify, Function.comp_def, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
    PMF.bind_map, PMF.map_comp,
    schnorrWordROMScheme_verify, OracleComp.runWith_map, OracleComp.runWith_query]
  congr 1 with answer : 1
  rcases answer with ⟨c, st⟩
  have hc : (List.ofFn c).take m = List.ofFn c := List.take_of_length_le (by simp)
  simp [hc, Prod.map_apply]

/-- Replacing the actual nonce sampler by the ideal word-ROM signing law changes the joint
signature/external-state law by at most `2⁻ⁿ`. This holds for every stateful `m`-bit reply handler,
so in particular for the shared memoized oracle at every typed cache. The error is paid once,
through a common continuation; no assumption about a coupling is needed. -/
theorem closeTo_runWith_schnorrROMSign (n : ℕ) (x : ZMod (F.order d)) (u : F.Carrier d)
    (msg : List Bool) (state : Store) :
    CloseTo
      (((F.schnorrWordROMScheme d hm).signCoins (x, u) msg).bind fun coins =>
        (OracleComp.runWith reply ((F.schnorrWordROMScheme d hm).sign (x, u) msg coins)
          state).map (Prod.map (encPair encBits encBits) id))
      (ProbOracleComp.runWith
        (fun (q : Unit × List Bool) st => (reply q.2 st).map (Prod.map List.ofFn id))
        (F.schnorrROMSign n d m (F.encScalar d x) msg) state)
      (1 / 2 ^ n : ℝ≥0) := by
  rw [F.runWith_schnorrROMSign d hm reply n x u msg state]
  have h := (F.closeTo_uniform_sampleExp n d).bind_left fun r =>
    (OracleComp.runWith reply ((F.schnorrWordROMScheme d hm).sign (x, u) msg
      (F.encode d (r • F.generator d), r)) state).map
        (Prod.map (encPair encBits encBits) id)
  simpa only [schnorrWordROMScheme, fiatShamir, schnorrWordSigma, schnorrBitSigma, schnorr,
    linear, PMF.bind_map, PMF.map_comp, Function.comp_def, Prod.map_apply, id_eq,
    LinearMap.toSpanSingleton_apply] using h

end Cslib.Crypto.PrimeOrderGroupFamily
