/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Signature
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Crypto.Negligible.Basic
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind
import Complexity.Tactic.PPT

/-!
# Stateless digital signature schemes on arbitrary-length bit words

`SignatureScheme` fixes the message space at security parameter `n` to exact `n`-bit words
(`msg.length = n`). Mirroring `Encryption.WordINDCPA`, this module defines uniform stateless
digital signature schemes (`WordSignatureScheme`) whose signing algorithm, verification algorithm,
and adaptive EUF-CMA experiment (`WordSignatureScheme.eufCmaGame`, `WordSignatureScheme.EUFCMA`)
operate on **unrestricted bit strings** (`msg : List Bool`), with no message-length restriction at
any security parameter:

* **Completeness (`WordSignatureScheme.verify_sign`)**: for every security parameter `n`, supported
  key pair `(pk, sk) ∈ (ProbComp.eval (S.keyGen n)).support`, arbitrary bit string
  `msg : List Bool`, and signature `sig ∈ (ProbComp.eval (S.sign sk msg)).support`,
  `S.verify pk msg sig = true`.
* **Adaptive chosen-message security (`WordSignatureScheme.eufCmaGame`,
  `WordSignatureScheme.EUFCMA`)**: an adaptive `IsOraclePPT` forger receives unary `n` and `pk`,
  queries `S.signingOracle sk` on arbitrary messages, and wins by outputting any valid `(msg, sig)`
  pair whose message `msg` was never queried to the signing oracle
  (`[GoldwasserMicaliRivest1988]`, Section 3; `[Rompel1990]`; `[BonehShoup2023]`, Section 13.1,
  Attack Game 13.1 and Definition 13.1).
* **Restriction to `n`-bit messages (`WordSignatureScheme.toSignatureScheme`,
  `WordSignatureScheme.EUFCMA.toSignatureScheme`)**: every `WordSignatureScheme` restricts to a
  `SignatureScheme` with the same `keyGen`, `sign`, and `verify`; because
  `SignatureScheme.eufCmaGame` additionally requires `msg.length == n`, its forging probability is
  pointwise at most that of `WordSignatureScheme.eufCmaGame`, so `WordSignatureScheme.EUFCMA`
  implies `SignatureScheme.EUFCMA`.

## Main definitions

* `Cslib.Crypto.WordSignatureScheme`: uniform stateless digital signature scheme on arbitrary
  `List Bool` messages.
* `Cslib.Crypto.WordSignatureScheme.signingOracle`, `Cslib.Crypto.WordSignatureScheme.eufCmaGame`,
  `Cslib.Crypto.WordSignatureScheme.EUFCMA`: adaptive chosen-message security experiment and
  security predicate for unrestricted `List Bool` messages.
* `Cslib.Crypto.WordSignatureScheme.toSignatureScheme`: restriction of a `WordSignatureScheme` to
  `SignatureScheme`'s `n`-bit message interface.

## Main results

* `Cslib.Crypto.WordSignatureScheme.isPPTOn_run_signingOracle`,
  `Cslib.Crypto.WordSignatureScheme.isPPTOn_eufCmaGame`,
  `Cslib.Crypto.WordSignatureScheme.isPPT_eufCmaGame`: uniform strict PPT certificates for the
  signing-oracle execution and full EUF-CMA experiment, proved directly in the plain polynomial-time
  calculus.
* `Cslib.Crypto.WordSignatureScheme.succProbability_toSignatureScheme_eufCmaGame_le`,
  `Cslib.Crypto.WordSignatureScheme.EUFCMA.toSignatureScheme`: `WordSignatureScheme.EUFCMA` implies
  `SignatureScheme.EUFCMA` on the induced `n`-bit `SignatureScheme`.

## References

* [S. Goldwasser, S. Micali, R. L. Rivest, *A Digital Signature Scheme Secure Against Adaptive
  Chosen-Message Attacks*][GoldwasserMicaliRivest1988]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 13.1 (Attack Game 13.1 and Definition 13.1) and Section 13.2.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- A uniform stateless digital signature scheme on arbitrary bit strings (`List Bool`), with
strict polynomial-time key generation and signing, deterministic polynomial-time verification, and
perfect completeness on all supported key pairs, arbitrary `List Bool` messages, and signatures. -/
structure WordSignatureScheme where
  /-- Sample a public verification key and secret signing key `(pk, sk)` at unary parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Sign an arbitrary bit-string message `msg` using the secret signing key `sk`. -/
  sign : List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically verify a candidate signature `sig` on `msg` under public key `pk`. -/
  verify : List Bool → List Bool → List Bool → Bool
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) keyGen
  /-- Signing is uniformly strict PPT in the encoded secret key and message. -/
  sign_ppt : IsPPTOn (encPair encBits encBits) encBits (fun ⟨sk, msg⟩ => sign sk msg)
  /-- Verification is computable in plain polynomial time on `(pk, msg, sig)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun ⟨pk, msg, sig⟩ => verify pk msg sig)
    (encPair encBits (encPair encBits encBits)) encBool
  /-- Every signature produced by `sign` on any bit-string message under a supported key pair at
  security parameter `n` is accepted by `verify`. -/
  verify_sign : ∀ n pk sk, (pk, sk) ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg sig, sig ∈ (ProbComp.eval (sign sk msg)).support →
    verify pk msg sig = true

namespace WordSignatureScheme

attribute [program_certificate] keyGen_ppt sign_ppt verify_polyTime

@[program_certificate, fun_prop]
theorem isPPTOn_keyGen_comp (S : WordSignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn (encPair encBits encBits) (fun a => S.keyGen (n a)) :=
  S.keyGen_ppt.preprocess hn

@[program_certificate, fun_prop]
theorem isPPTOn_sign_comp (S : WordSignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => S.sign (sk a) (msg a)) :=
  S.sign_ppt.preprocess (hsk.prod hmsg)

@[program_certificate, fun_prop]
theorem computableInPolyTime_verify_comp (S : WordSignatureScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {pk msg sig : γ → List Bool}
    (hpk : ComputableInPolyTime pk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (hsig : ComputableInPolyTime sig encIn encBits) :
    ComputableInPolyTime (fun a => S.verify (pk a) (msg a) (sig a)) encIn encBool :=
  S.verify_polyTime.comp (hpk.prod (hmsg.prod hsig))

/-! ### Adaptive chosen-message security on unrestricted bit words (`EUFCMA`) -/

/-- Stateful signing oracle that signs any requested `List Bool` message under `sk` and prepends
the message to the list of queried messages. -/
def signingOracle (S : WordSignatureScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried => do
    let sig ← S.sign sk request.2
    return (sig, request.2 :: queried)

/-- The unrestricted-message EUF-CMA experiment: sample `(pk, sk) ← S.keyGen n`, run the adaptive
forger on `(n, pk)` with oracle access to `S.signingOracle sk`, and accept when the forger outputs
a valid signature on any `List Bool` message that was never queried to the signing oracle. -/
def eufCmaGame (S : WordSignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.signingOracle keys.2)) (adversary n keys.1)).run []
  let (msg, sig) := out.1
  return !out.2.contains msg && S.verify keys.1 msg sig

/-- Running an oracle-PPT forger against `signingOracle` is uniformly strict PPT in `(n, (pk, sk))`.
-/
@[program_certificate]
theorem isPPTOn_run_signingOracle (S : WordSignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair (encPair encBits encBits) (encList encBits))
      (fun ⟨n, pk, sk⟩ =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.signingOracle sk)) (adversary n pk)).run []) := by
  obtain ⟨c, d, hlen⟩ := S.sign_ppt.length_le
  let Caller := ℕ × (List Bool × List Bool)
  let encCaller : Caller ↪ List Bool := encPair encUnary (encPair encBits encBits)
  let HIn := Caller × ((Unit × List Bool) × List (List Bool))
  let encHIn : HIn ↪ List Bool :=
    encPair encCaller (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  have hhandler : IsPPTOn encHIn (encPair encBits (encList encBits))
      (fun pair : HIn => S.signingOracle pair.1.2.2 pair.2.1 pair.2.2) := by
    have hsk : ComputableInPolyTime (fun pair : HIn => pair.1.2.2) encHIn encBits :=
      (ComputableInPolyTime.fst _ _).snd'.snd'
    have hreq : ComputableInPolyTime (fun pair : HIn => pair.2.1.2) encHIn encBits :=
      (ComputableInPolyTime.snd _ _).fst'.snd'
    have hqueried : ComputableInPolyTime (fun pair : HIn => pair.2.2) encHIn (encList encBits) :=
      (ComputableInPolyTime.snd _ _).snd'
    have hsign := S.isPPTOn_sign_comp hsk hreq
    have hpost : ComputableInPolyTime
        (fun q : HIn × List Bool => (q.2, q.1.2.1.2 :: q.1.2.2))
        (encPair encHIn encBits) (encPair encBits (encList encBits)) := by
      have hqIn := ComputableInPolyTime.fst encHIn encBits
      have hqSig := ComputableInPolyTime.snd encHIn encBits
      exact hqSig.prod ((hqIn.trans hreq).cons' (hqIn.trans hqueried))
    exact hsign.bind_with
      (second := fun (pair : HIn) sig => pure (sig, pair.2.1.2 :: pair.2.2))
      hpost.isPPTOn
  have hprepare : ComputableInPolyTime (fun caller : Caller => (caller.1, caller.2.1))
      encCaller (encPair encUnary encBits) :=
    (ComputableInPolyTime.fst _ _).prod (ComputableInPolyTime.snd _ _).fst'
  have hinitial : ComputableInPolyTime (fun _ : Caller => ([] : List (List Bool)))
      encCaller (encList encBits) :=
    ComputableInPolyTime.const []
  have hresources : PolyBounded (fun pair => (encPair encCaller encBits pair).length)
      (fun pair : Caller × List Bool =>
        c * (2 * pair.1.2.2.length + pair.2.length + 2) ^ d + 2 * pair.2.length + 2) := by
    growth_poly [(ComputableInPolyTime.fst encCaller encBits).snd'.snd',
      ComputableInPolyTime.snd encCaller encBits]
  refine ((hadversary.run_interpret_preprocess_open_of_polyBounded (External := Empty)
    (handler := fun (caller : Caller) request state =>
      ProbOracleComp.sample (S.signingOracle caller.2.2 request state))
    (prepare := fun caller : Caller => (caller.1, caller.2.1))
    (initial := fun _ : Caller => ([] : List (List Bool)))
    (resources := fun (caller : Caller) query =>
      c * (2 * caller.2.2.length + query.length + 2) ^ d + 2 * query.length + 2)
    hprepare hhandler.isOraclePPTOn hinitial
    (fun _ _ => True) (fun _ => trivial) hresources
    (fun caller request queried _ result hresult => ?_)).congr
      fun caller _ _ _ => ?_).isPPTOn
  · have hsupp := (ProbOracleComp.support_sample _).subset hresult
    simp only [signingOracle, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsupp
    obtain ⟨sig, hsig, rfl⟩ := hsupp
    have hsigLen := hlen (caller.2.2, request.2) sig hsig
    simp only [encBits_apply, length_encPair] at hsigLen
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]
    lia
  · rw [ProbOracleComp.sample_run_interpret]

/-- Run the complete unrestricted-message EUF-CMA experiment on its unary security parameter for
any oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_eufCmaGame (S : WordSignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (S.eufCmaGame adversary) := by
  have hrun := S.isPPTOn_run_signingOracle hadversary
  let P := (ℕ × (List Bool × List Bool)) × ((List Bool × List Bool) × List (List Bool))
  let encP : P ↪ List Bool :=
    encPair (encPair encUnary (encPair encBits encBits))
      (encPair (encPair encBits encBits) (encList encBits))
  have hpost : ComputableInPolyTime
      (fun pair : P =>
        !pair.2.2.contains pair.2.1.1 && S.verify pair.1.2.1 pair.2.1.1 pair.2.1.2)
      encP encBool := by
    have hpk : ComputableInPolyTime (fun pair : P => pair.1.2.1) encP encBits :=
      (ComputableInPolyTime.fst _ _).snd'.fst'
    have hmsg : ComputableInPolyTime (fun pair : P => pair.2.1.1) encP encBits :=
      (ComputableInPolyTime.snd _ _).fst'.fst'
    have hsig : ComputableInPolyTime (fun pair : P => pair.2.1.2) encP encBits :=
      (ComputableInPolyTime.snd _ _).fst'.snd'
    have hqueried : ComputableInPolyTime (fun pair : P => pair.2.2) encP (encList encBits) :=
      (ComputableInPolyTime.snd _ _).snd'
    have hfresh : ComputableInPolyTime (fun pair : P => !pair.2.2.contains pair.2.1.1)
        encP encBool := by
      refine (ComputableInPolyTime.decide_not
        (ComputableInPolyTime.decide_mem hqueried hmsg)).of_enc_eq fun pair => ?_
      apply congrArg encBool
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
    exact hfresh.bool_and' (S.computableInPolyTime_verify_comp hpk hmsg hsig)
  exact S.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The unrestricted-message EUF-CMA experiment is uniformly strict PPT, independently of unused
auxiliary input. -/
@[program_certificate]
theorem isPPT_eufCmaGame (S : WordSignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => S.eufCmaGame adversary n) :=
  ((S.isPPTOn_eufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Existential unforgeability under adaptive chosen-message attack (`EUFCMA`) on arbitrary
`List Bool` messages against uniform strict oracle-PPT adversaries. -/
def EUFCMA (S : WordSignatureScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.eufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Unrestricted-message EUF-CMA security gives negligible forgery probability for every oracle-PPT
forger. -/
theorem EUFCMA.negligible {S : WordSignatureScheme} (h : S.EUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish unrestricted-message EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem EUFCMA.of_negligible {S : WordSignatureScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n)))) :
    S.EUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-! ### Restriction to fixed-length `SignatureScheme` -/

/-- Restrict a `WordSignatureScheme` to `SignatureScheme`'s `n`-bit message interface. -/
def toSignatureScheme (S : WordSignatureScheme) : SignatureScheme where
  keyGen := S.keyGen
  sign := S.sign
  verify := S.verify
  keyGen_ppt := S.keyGen_ppt
  sign_ppt := S.sign_ppt
  verify_polyTime := S.verify_polyTime
  verify_sign n keys hkeys msg _ sig hsig := S.verify_sign n keys.1 keys.2 hkeys msg sig hsig

@[simp] theorem toSignatureScheme_keyGen (S : WordSignatureScheme) :
    S.toSignatureScheme.keyGen = S.keyGen := rfl

@[simp] theorem toSignatureScheme_sign (S : WordSignatureScheme) :
    S.toSignatureScheme.sign = S.sign := rfl

@[simp] theorem toSignatureScheme_verify (S : WordSignatureScheme) :
    S.toSignatureScheme.verify = S.verify := rfl

@[simp] theorem toSignatureScheme_signingOracle (S : WordSignatureScheme) :
    S.toSignatureScheme.signingOracle = S.signingOracle := rfl

/-- Because `SignatureScheme.eufCmaGame` imposes the additional check `msg.length == n`, every
forger's success probability against `S.toSignatureScheme` is at most its success probability
against `S`. -/
theorem succProbability_toSignatureScheme_eufCmaGame_le (S : WordSignatureScheme)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (S.toSignatureScheme.eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n)) := by
  unfold Game.succProbability
  have hle :
      (ProbComp.eval (S.toSignatureScheme.eufCmaGame adversary n)) true ≤
        (ProbComp.eval (S.eufCmaGame adversary n)) true := by
    simp only [SignatureScheme.eufCmaGame, eufCmaGame, toSignatureScheme_keyGen,
      toSignatureScheme_signingOracle, toSignatureScheme_verify, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_apply]
    refine tsum_le_tsum fun keys => mul_le_mul_right ?_ _
    refine tsum_le_tsum fun out => mul_le_mul_right ?_ _
    rcases out with ⟨⟨msg, sig⟩, queried⟩
    dsimp only
    rw [PMF.pure_apply, PMF.pure_apply]
    split_ifs <;> simp_all
  exact ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) hle

/-- Unrestricted-message `EUFCMA` security implies `SignatureScheme.EUFCMA` security on `n`-bit
messages. -/
theorem EUFCMA.toSignatureScheme {S : WordSignatureScheme} (h : S.EUFCMA) :
    S.toSignatureScheme.EUFCMA := by
  apply SignatureScheme.EUFCMA.of_negligible
  intro adversary hadversary
  exact negligible_of_le (h.negligible adversary hadversary)
    (S.succProbability_toSignatureScheme_eufCmaGame_le adversary)

end WordSignatureScheme

end Cslib.Crypto
