/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Crypto.Game
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Uniform digital signature schemes and existential unforgeability

A uniform digital signature scheme (`SignatureScheme`) consists of a strict probabilistic
polynomial-time key generator `keyGen`, a strict probabilistic polynomial-time signing algorithm
`sign`, and a deterministic polynomial-time verification algorithm `verify` that accepts every
signature produced by `sign` on an `n`-bit message under a key pair sampled at security parameter
`n`. The message space at parameter `n` is exactly the `n`-bit words; this module does not
claim security for arbitrary polynomial-length message families.

We formalize two adaptive chosen-message security notions against uniform strict oracle-PPT forgers
(`IsOraclePPT`):

* **Existential unforgeability under adaptive chosen-message attack (`eufCmaGame`, `EUFCMA`)**:
  the forger receives the unary security parameter `n` and public verification key `pk`, has
  adaptive oracle access to `signingOracle sk` on arbitrary messages, and wins by outputting a valid
  `(msg, sig)` pair with `msg.length = n` such that `msg` was never queried to the signing oracle.
* **Existential unforgeability under one-time adaptive chosen-message attack (`eufOneTimeGame`,
  `OneTimeEUFCMA`)**: the signing oracle `oneTimeSigningOracle sk` answers at most the first
  signing query and returns the empty word on any subsequent query. Every `EUFCMA`-secure scheme is
  a fortiori `OneTimeEUFCMA`-secure (`SignatureScheme.EUFCMA.oneTimeEUFCMA`).

## Main definitions

* `Cslib.Crypto.Forger`: adaptive oracle adversary outputting a `(message, signature)` pair.
* `Cslib.Crypto.encForgeryLog`: the encoding of a forgery with the list of queried messages.
* `Cslib.Crypto.SignatureScheme`: uniform digital signature scheme on `n`-bit messages.
* `Cslib.Crypto.SignatureScheme.signingOracleOf`, `Cslib.Crypto.SignatureScheme.signingOracle`,
  `eufCmaGame`, `EUFCMA`: message-logging signing oracle and full adaptive EUF-CMA experiment and
  security predicate.
* `Cslib.Crypto.SignatureScheme.oneTimeSigningOracleOf`,
  `Cslib.Crypto.SignatureScheme.oneTimeSigningOracle`, `eufOneTimeGame`, `OneTimeEUFCMA`: one-time
  message-logging signing oracle and one-time adaptive EUF-CMA experiment and security predicate.

## Main results

* `Cslib.Crypto.SignatureScheme.isPPTOn_run_signingOracleOf`,
  `Cslib.Crypto.SignatureScheme.isPPTOn_run_signingOracle`,
  `Cslib.Crypto.SignatureScheme.isPPTOn_eufCmaGame`, `isPPT_eufCmaGame`: strict PPT certificates
  for the message-logging signing oracle and full EUF-CMA experiment.
* `Cslib.Crypto.SignatureScheme.isPPTOn_run_oneTimeSigningOracleOf`,
  `Cslib.Crypto.SignatureScheme.isPPTOn_run_oneTimeSigningOracle`,
  `Cslib.Crypto.SignatureScheme.isPPTOn_eufOneTimeGame`, `isPPT_eufOneTimeGame`: strict PPT
  certificates for the one-time signing oracle and one-time EUF-CMA experiment.
* `Cslib.Crypto.SignatureScheme.run_limitToOneQuery_eq_oneTimeSigningOracleOf`,
  `Cslib.Crypto.SignatureScheme.EUFCMA.oneTimeEUFCMA`: one-query filter simulation and implication
  from full EUF-CMA security to one-time EUF-CMA security.

## References

* [S. Goldwasser, S. Micali, R. L. Rivest, *A Digital Signature Scheme Secure Against Adaptive
  Chosen-Message Attacks*][GoldwasserMicaliRivest1988]
* [L. Lamport, *Constructing Digital Signatures from a One-Way Function*][Lamport1979]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- An adaptive forger receives a unary security parameter and a public verification key, queries a
signing oracle on chosen messages, and outputs a candidate `(message, signature)` pair. -/
abbrev Forger := ℕ → List Bool → WordOracleComp Unit (List Bool × List Bool)

/-- Output `((msg, sig), queried)` of a forger run against a message-logging signing oracle: the
candidate forgery `(msg, sig)` as bit words, then the list of queried messages. The forgery is
framed, with `msg` framed again inside it, and so is each queried message. -/
abbrev encForgeryLog : (List Bool × List Bool) × List (List Bool) ↪ List Bool :=
  encPair (encPair encBits encBits) (encList encBits)

/-- A uniform digital signature scheme on `n`-bit messages at security parameter `n`, with strict
polynomial-time key generation and signing, deterministic polynomial-time verification, and perfect
completeness on supported key pairs, `n`-bit messages, and signatures. -/
structure SignatureScheme where
  /-- Sample a public verification key and secret signing key `(pk, sk)` at unary parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Sign a message `msg` using the secret signing key `sk`. -/
  sign : List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically verify a candidate signature `sig` on `msg` under public key `pk`. -/
  verify : List Bool → List Bool → List Bool → Bool
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) keyGen
  /-- Signing is uniformly strict PPT in the encoded secret key and message. -/
  sign_ppt : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2)
  /-- Verification is computable in plain polynomial time on `(pk, msg, sig)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool => verify p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool
  /-- Every signature produced by `sign` on an `n`-bit message under a supported key pair at
  security parameter `n` is accepted by `verify`. -/
  verify_sign : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = n →
    ∀ sig, sig ∈ (ProbComp.eval (sign keys.2 msg)).support →
    verify keys.1 msg sig = true

namespace SignatureScheme

attribute [program_certificate] keyGen_ppt sign_ppt verify_polyTime

@[program_certificate, fun_prop]
theorem isPPTOn_keyGen_comp (S : SignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn (encPair encBits encBits) (fun a => S.keyGen (n a)) :=
  S.keyGen_ppt.preprocess hn

@[program_certificate, fun_prop]
theorem isPPTOn_sign_comp (S : SignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => S.sign (sk a) (msg a)) :=
  S.sign_ppt.preprocess (hsk.prod hmsg)

@[program_certificate, fun_prop]
theorem computableInPolyTime_verify_comp (S : SignatureScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {pk msg sig : γ → List Bool}
    (hpk : ComputableInPolyTime pk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (hsig : ComputableInPolyTime sig encIn encBits) :
    ComputableInPolyTime (fun a => S.verify (pk a) (msg a) (sig a)) encIn encBool :=
  .of_tidy (S.verify_polyTime.tidy.comp (hpk.tidy.prod (hmsg.tidy.prod hsig.tidy)))

private theorem computableInPolyTime_signResources (c d : ℕ) :
    ComputableInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) × List Bool =>
        c * (2 * pair.1.2.2.length + pair.2.length + 2) ^ d + 2 * pair.2.length + 2)
      (encPair encKeyPairInput encBits) encUnary := by
  have hskLen := (ComputableInPolyTime.fst
    (encPair encUnary (encPair encBits encBits)) encBits).snd'.snd'.length_bits_comp
  have hqLen := (ComputableInPolyTime.snd
    (encPair encUnary (encPair encBits encBits)) encBits).length_bits_comp
  exact (((ComputableInPolyTime.const c).unary_mul' ((ComputableInPolyTime.unary_pow d).comp
    ((((ComputableInPolyTime.const 2).unary_mul' hskLen).unary_add' hqLen).unary_add'
      (.const 2)))).unary_add' ((ComputableInPolyTime.const 2).unary_mul' hqLen)).unary_add'
    (.const 2)

private theorem computableTidilyInPolyTime_eufPost (S : SignatureScheme) :
    ComputableTidilyInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) × ((List Bool × List Bool) × List (List Bool)) =>
        (pair.2.1.1.length == pair.1.1) && !pair.2.2.contains pair.2.1.1 &&
          S.verify pair.1.2.1 pair.2.1.1 pair.2.1.2)
      (encPair encKeyPairInput encForgeryLog) encBool := by
  have hcaller := ComputableTidilyInPolyTime.fst
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair encBits encBits) (encList encBits))
  have hout := ComputableTidilyInPolyTime.snd
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair encBits encBits) (encList encBits))
  have hmsg := hout.fst'.fst'
  have hcontains : (fun pair :
      (ℕ × (List Bool × List Bool)) × ((List Bool × List Bool) × List (List Bool)) =>
      pair.2.2.contains pair.2.1.1) =
      (fun pair => pair.2.2.any (fun x => pair.2.1.1 == x)) := by
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.any_eq_true]
    simp only [beq_iff_eq]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, heq⟩ => heq ▸ h⟩
  exact (((ComputableTidilyInPolyTime.length_bits.comp hmsg).beq hcaller.fst').bool_and'
    (ComputableTidilyInPolyTime.bool_not.comp (hcontains ▸
      ComputableTidilyInPolyTime.anyWithInput (test := fun pair x => pair.2.1.1 == x) hout.snd'
        ((hmsg.comp (.fst _ _)).beq (.snd _ _))))).bool_and'
    (S.verify_polyTime.tidy.comp (hcaller.snd'.fst'.prod (hmsg.prod hout.fst'.snd')))

/-! ### Full adaptive chosen-message security (`EUFCMA`) -/

/-- Stateful signing/tagging oracle that invokes `sign sk` on the requested message and prepends
the message to the list of queried messages. -/
abbrev signingOracleOf (sign : List Bool → List Bool → ProbComp (List Bool)) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried => do
    let sig ← sign sk request.2
    return (sig, request.2 :: queried)

/-- Stateful signing oracle that signs the requested message under `sk` and prepends the message to
the list of queried messages. -/
def signingOracle (S : SignatureScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried => do
    let sig ← S.sign sk request.2
    return (sig, request.2 :: queried)

/-- The EUF-CMA experiment: sample `(pk, sk) ← S.keyGen n`, run the adaptive forger on `(n, pk)`
with oracle access to `S.signingOracle sk`, and accept when the forger outputs a valid signature on
an `n`-bit message that was never queried to the signing oracle. -/
def eufCmaGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.signingOracle keys.2)) (adversary n keys.1)).run []
  let msig := out.1
  return (msig.1.length == n) && !out.2.contains msig.1 &&
    S.verify keys.1 msig.1 msig.2

/-- Running an oracle-PPT forger against `signingOracleOf sign` is uniformly strict PPT in the
unary security parameter, public/auxiliary input, and secret key. -/
@[program_certificate]
theorem isPPTOn_run_signingOracleOf {sign : List Bool → List Bool → ProbComp (List Bool)}
    (hsign : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2))
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (signingOracleOf sign caller.2.2)) (adversary caller.1 caller.2.1)).run []) := by
  obtain ⟨c, d, hlen⟩ := hsign.length_le
  have hcaller := ComputableTidilyInPolyTime.fst
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  have hstate := ComputableTidilyInPolyTime.snd
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  apply hadversary.run_interpret_preprocess' (operationEncoding := encFinEnum Unit)
    (handler := fun caller : ℕ × (List Bool × List Bool) => signingOracleOf sign caller.2.2)
    (prepare := fun caller : ℕ × (List Bool × List Bool) => (caller.1, caller.2.1))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      c * (2 * caller.2.2.length + query.length + 2) ^ d + 2 * query.length + 2)
    ((ComputableInPolyTime.fst _ _).prod (ComputableInPolyTime.snd _ _).fst')
    ((hsign.preprocess
      ((ComputableInPolyTime.of_tidy hcaller.snd'.snd').prod
        (.of_tidy hstate.fst'.snd'))).bind_with
      (ComputableTidilyInPolyTime.prod (.snd _ _)
        (ComputableTidilyInPolyTime.cons' (hstate.fst'.snd'.comp (.fst _ _))
          (hstate.snd'.comp (.fst _ _)))).isPPTOn)
    (.const []) (fun _ _ => True) (fun _ => trivial)
    (computableInPolyTime_signResources c d)
  intro caller request queried _ result hresult
  simp only [signingOracleOf, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
  obtain ⟨sig, hsig, rfl⟩ := hresult
  have hsigLen := hlen (caller.2.2, request.2) sig hsig
  simp only [encBits_apply, length_encPair] at hsigLen
  refine ⟨trivial, by lia, ?_⟩
  simp only [encList_cons, List.length_append, length_frame, encBits_apply]
  lia

/-- Running an oracle-PPT forger against `S.signingOracle` is uniformly strict PPT in the unary
security parameter, public key, and secret key. -/
@[program_certificate]
theorem isPPTOn_run_signingOracle (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.signingOracle caller.2.2)) (adversary caller.1 caller.2.1)).run []) :=
  isPPTOn_run_signingOracleOf S.sign_ppt hadversary

/-- Run the complete EUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_eufCmaGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (S.eufCmaGame adversary) :=
  S.keyGen_ppt.bind_with
    ((S.isPPTOn_run_signingOracle hadversary).bind_with
      (computableTidilyInPolyTime_eufPost S).isPPTOn)

/-- The EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_eufCmaGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => S.eufCmaGame adversary n) :=
  ((S.isPPTOn_eufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Existential unforgeability under adaptive chosen-message attack (EUF-CMA) against uniform
strict oracle-PPT adversaries. -/
def EUFCMA (S : SignatureScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.eufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Full EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem EUFCMA.negligible {S : SignatureScheme} (h : S.EUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish EUF-CMA security by bounding every oracle-PPT forger's success probability. -/
theorem EUFCMA.of_negligible {S : SignatureScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n)))) :
    S.EUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

/-! ### One-time adaptive chosen-message security (`OneTimeEUFCMA`) -/

/-- One-time signing/tagging oracle that answers at most the first query using `sign sk` and
returns the empty word without signing on any subsequent query. -/
abbrev oneTimeSigningOracleOf (sign : List Bool → List Bool → ProbComp (List Bool)) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried =>
    if queried.isEmpty then do
      let sig ← sign sk request.2
      return (sig, [request.2])
    else
      return ([], queried)

/-- One-time signing oracle that answers at most the first signing query using `S.sign sk` and
returns the empty word without signing on any subsequent query. -/
def oneTimeSigningOracle (S : SignatureScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried =>
    if queried.isEmpty then do
      let sig ← S.sign sk request.2
      return (sig, [request.2])
    else
      return ([], queried)

/-- The one-time EUF-CMA experiment: sample `(pk, sk) ← S.keyGen n`, run the adaptive forger on
`(n, pk)` with oracle access to `S.oneTimeSigningOracle sk` (which answers at most one signing
query), and accept when the forger outputs a valid signature on an `n`-bit message distinct from
the queried message (if any). -/
def eufOneTimeGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.oneTimeSigningOracle keys.2)) (adversary n keys.1)).run []
  let msig := out.1
  return (msig.1.length == n) && !out.2.contains msig.1 &&
    S.verify keys.1 msig.1 msig.2

/-- Running an oracle-PPT forger against `oneTimeSigningOracleOf sign` is uniformly strict PPT in
the unary security parameter, public/auxiliary input, and secret key. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeSigningOracleOf {sign : List Bool → List Bool → ProbComp (List Bool)}
    (hsign : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2))
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (oneTimeSigningOracleOf sign caller.2.2)) (adversary caller.1 caller.2.1)).run []) := by
  obtain ⟨c, d, hlen⟩ := hsign.length_le
  have hcaller := ComputableTidilyInPolyTime.fst
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  have hstate := ComputableTidilyInPolyTime.snd
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  apply hadversary.run_interpret_preprocess' (operationEncoding := encFinEnum Unit)
    (handler := fun caller : ℕ × (List Bool × List Bool) => oneTimeSigningOracleOf sign caller.2.2)
    (prepare := fun caller : ℕ × (List Bool × List Bool) => (caller.1, caller.2.1))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      c * (2 * caller.2.2.length + query.length + 2) ^ d + 2 * query.length + 2)
    ((ComputableInPolyTime.fst _ _).prod (ComputableInPolyTime.snd _ _).fst')
    (IsPPTOn.cond ((ComputableTidilyInPolyTime.listIsEmpty' encBits).comp hstate.snd')
      ((hsign.preprocess
        ((ComputableInPolyTime.of_tidy hcaller.snd'.snd').prod
          (.of_tidy hstate.fst'.snd'))).bind_with
        (ComputableTidilyInPolyTime.prod (.snd _ _)
          (ComputableTidilyInPolyTime.cons' (hstate.fst'.snd'.comp (.fst _ _))
            (.const []))).isPPTOn)
      ((ComputableTidilyInPolyTime.const ([] : List Bool)).prod hstate.snd').isPPTOn)
    (.const []) (fun _ _ => True) (fun _ => trivial)
    (computableInPolyTime_signResources c d)
  intro caller request queried _ result hresult
  unfold oneTimeSigningOracleOf at hresult
  split_ifs at hresult with hempty
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨sig, hsig, rfl⟩ := hresult
    have hsigLen := hlen (caller.2.2, request.2) sig hsig
    simp only [encBits_apply, length_encPair] at hsigLen
    refine ⟨trivial, by lia, ?_⟩
    rw [List.isEmpty_iff.mp hempty]
    simp only [encList_cons, encList_nil, List.length_append, List.length_nil, length_frame,
      encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- Running an oracle-PPT forger against `oneTimeSigningOracle` is uniformly strict PPT in the
unary security parameter, public key, and secret key. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeSigningOracle (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.oneTimeSigningOracle caller.2.2)) (adversary caller.1 caller.2.1)).run []) :=
  isPPTOn_run_oneTimeSigningOracleOf S.sign_ppt hadversary

/-- Run the complete one-time EUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_eufOneTimeGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (S.eufOneTimeGame adversary) :=
  S.keyGen_ppt.bind_with
    ((S.isPPTOn_run_oneTimeSigningOracle hadversary).bind_with
      (computableTidilyInPolyTime_eufPost S).isPPTOn)

/-- The one-time EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_eufOneTimeGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => S.eufOneTimeGame adversary n) :=
  ((S.isPPTOn_eufOneTimeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Existential unforgeability under one-time adaptive chosen-message attack against uniform strict
oracle-PPT adversaries. -/
def OneTimeEUFCMA (S : SignatureScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.eufOneTimeGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- One-time EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem OneTimeEUFCMA.negligible {S : SignatureScheme} (h : S.OneTimeEUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufOneTimeGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish one-time EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem OneTimeEUFCMA.of_negligible {S : SignatureScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufOneTimeGame adversary n)))) :
    S.OneTimeEUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

/-- Starting from the empty query log, `oneTimeSigningOracle` records at most one queried
message. -/
theorem length_le_one_of_mem_support_run_oneTimeSigningOracle (S : SignatureScheme) {α : Type}
    (sk : List Bool) (prog : WordOracleComp Unit α) {result : α} {queried : List (List Bool)}
    (h : (result, queried) ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s))) prog).run []).support) :
    queried.length ≤ 1 := by
  refine ProbOracleComp.runWith_invariant
    (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s))
    (fun s => s.length ≤ 1) ?_ prog [] (by simp) result queried h
  intro ⟨⟨⟩, req⟩ s hs a s' hmem
  rw [oneTimeSigningOracle] at hmem
  split_ifs at hmem with hempty
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hmem
    obtain ⟨_, _, heq⟩ := hmem
    cases heq
    simp
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hmem
    exact (Prod.mk.inj hmem).2 ▸ hs

private theorem run_oneTimeSigningOracle_apply_eq_zero_of_not_agree (S : SignatureScheme)
    {α : Type} (sk : List Bool) {agree : List Bool → Prop} (prog : WordOracleComp Unit α)
    {s queried' : List (List Bool)} (hs : ¬ ∀ r ∈ s, agree r) (hq' : ∀ r ∈ queried', agree r)
    (a : α) :
    (ProbOracleComp.runWith (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s)) prog s)
      (a, queried') = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hmem
  refine ProbOracleComp.runWith_invariant
    (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s))
    (fun state => ¬ ∀ r ∈ state, agree r) ?_ prog s hs a queried' hmem hq'
  intro ⟨⟨⟩, req⟩ state hstate val next hnext
  rw [oneTimeSigningOracle] at hnext
  split_ifs at hnext with hempty
  · rw [List.isEmpty_iff] at hempty
    subst hempty
    exact absurd (fun _ h => nomatch h) hstate
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
    exact (Prod.mk.inj hnext).2 ▸ hstate

/-- If `S.sign sk₁` and `S.sign sk₂` agree on all requests satisfying `agree`, then running any
adaptive program against `oneTimeSigningOracle` under `sk₁` and `sk₂` assigns the same probability
to every outcome `(a, queried')` whose recorded query log satisfies `agree`. -/
theorem run_oneTimeSigningOracle_apply_eq_of_agree (S : SignatureScheme) {α : Type}
    (sk₁ sk₂ : List Bool) {agree : List Bool → Prop}
    (hagree : ∀ req, agree req → S.sign sk₁ req = S.sign sk₂ req)
    (prog : WordOracleComp Unit α) (s : List (List Bool)) (a : α)
    (queried' : List (List Bool)) (hq' : ∀ r ∈ queried', agree r) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk₁ q s))) prog).run s) (a, queried') =
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk₂ q s))) prog).run s)
      (a, queried') := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => rfl
  | lift_bind q cont ih =>
    change (((OracleComp.interpret (m := StateT (List (List Bool)) PMF) _
        (OracleComp.query q >>= cont)).run s) (a, queried')) =
      (((OracleComp.interpret (m := StateT (List (List Bool)) PMF) _
        (OracleComp.query q >>= cont)).run s) (a, queried'))
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      PMF.monad_bind_eq_bind]
    cases q with
    | inl k =>
      change (((ProbComp.unifOracle k).map (·, s)).bind _) (a, queried') =
        (((ProbComp.unifOracle k).map (·, s)).bind _) (a, queried')
      simp only [PMF.bind_map, Function.comp_def, PMF.bind_apply]
      exact tsum_congr fun r => congrArg _ (ih r s)
    | inr req =>
      rcases req with ⟨⟨⟩, msg⟩
      change ((ProbComp.eval (S.oneTimeSigningOracle sk₁ ((), msg) s)).bind _) (a, queried') =
        ((ProbComp.eval (S.oneTimeSigningOracle sk₂ ((), msg) s)).bind _) (a, queried')
      rw [oneTimeSigningOracle, oneTimeSigningOracle]
      split_ifs with hempty
      · by_cases hmsg : agree msg
        · rw [hagree msg hmsg]
          simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
            PMF.bind_apply]
          exact tsum_congr fun sig => congrArg _ (ih sig [msg])
        · have hnot : ¬ ∀ r ∈ [msg], agree r := fun h => hmsg (h msg (List.mem_singleton_self _))
          have hzero (sk : List Bool) (sig : List Bool) :
              ((OracleComp.interpret
                (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
                  (fun q s => ProbComp.eval (S.oneTimeSigningOracle sk q s)))
                (cont sig)).run [msg]) (a, queried') = 0 :=
            run_oneTimeSigningOracle_apply_eq_zero_of_not_agree S sk (cont sig) hnot hq' a
          simp [PMF.bind_apply, hzero]
      · simp only [ProbComp.eval_pure, PMF.pure_bind]
        exact ih [] s

/-! ### Reduction from one-time EUF-CMA to full EUF-CMA -/

/-- Open stateful handler that forwards at most the first signing request to the external signing
oracle (truncating the reply to `bound n msg.length`) and answers subsequent requests with `[]`. -/
def oneTimeFilterHandler (bound : ℕ → ℕ → ℕ) (caller : ℕ × List Bool)
    (request : Unit × List Bool) : StateT Bool (WordOracleComp Unit) (List Bool) :=
  fun alreadyQueried =>
    if alreadyQueried then
      pure ([], true)
    else
      (fun sig => (sig, true)) <$> (List.take (bound caller.1 request.2.length) <$>
        ProbOracleComp.query ((), request.2))

/-- Wrap an adaptive forger so that it issues at most one external signing query. -/
def limitToOneQuery (bound : ℕ → ℕ → ℕ) (adversary : Forger) : Forger :=
  fun n pk =>
    Prod.fst <$> (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (oneTimeFilterHandler bound (n, pk)))
      (adversary n pk)).run false

theorem isOraclePPT_limitToOneQuery {bound : ℕ → ℕ → ℕ}
    (hbound : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (limitToOneQuery bound adversary) := by
  have hbound := hbound.tidy
  have hcaller := ComputableTidilyInPolyTime.fst (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hstate := ComputableTidilyInPolyTime.snd (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hreq := hstate.fst'.snd'
  have hrun : IsOraclePPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (oneTimeFilterHandler bound caller))
          (adversary caller.1 caller.2)).run false) := by
    apply hadversary.run_interpret_preprocess_open (operationEncoding := encFinEnum Unit)
      (handler := oneTimeFilterHandler bound)
      (prepare := id)
      (initial := fun _ => false)
      (resources := fun caller query => bound caller.1 query.length + 1)
      ComputableTidilyInPolyTime.id'
      (IsOraclePPTOn.cond hstate.snd'
        ((ComputableTidilyInPolyTime.const ([], true)).isOraclePPTOn (Operation := Unit))
        ((IsOraclePPTOn.query_take () hreq
          (hbound.comp (hcaller.fst'.prod (ComputableTidilyInPolyTime.length_bits.comp hreq)))).map
          (ComputableTidilyInPolyTime.id'.prod (.const true))))
      (.const false)
      (fun _ _ => True) (fun _ => trivial)
      (ComputableTidilyInPolyTime.unary_add.comp
        ((hbound.comp ((ComputableTidilyInPolyTime.fst (encPair encUnary encBits) encBits).fst'.prod
          (ComputableTidilyInPolyTime.length_bits.comp
            (ComputableTidilyInPolyTime.snd (encPair encUnary encBits) encBits)))).prod
          (.const 1)))
    intro caller request state _ result hresult
    unfold oneTimeFilterHandler at hresult
    split_ifs at hresult with hstate
    · have heq := OracleComp.eq_of_mem_supportWith_pure hresult
      subst heq
      simp [encBool_apply]
    · obtain ⟨sig, hsig, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨rawSig, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hsig
      refine ⟨trivial, (List.length_take_le _ _).trans (by lia), ?_⟩
      simp [encBool_apply]
  exact (hrun.map (ComputableTidilyInPolyTime.fst _ _)).isOraclePPT

/-- Running an adaptive program filtered through `oneTimeFilterHandler` against
`signingOracleOf sign` produces the same distribution as running it against
`oneTimeSigningOracleOf sign` whenever all outputs of `sign sk msg` have length at most
`bound n msg.length`. -/
theorem run_limitToOneQuery_eq_oneTimeSigningOracleOf
    (sign : List Bool → List Bool → ProbComp (List Bool))
    (bound : ℕ → ℕ → ℕ) (n : ℕ) (pk sk : List Bool)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (sign sk msg)).support →
      sig.length ≤ bound n msg.length)
    (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval (Prod.map Prod.fst id <$> ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (signingOracleOf sign sk))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (oneTimeFilterHandler bound (n, pk)))
        prog).run false)).run [])) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (oneTimeSigningOracleOf sign sk)) prog).run []) := by
  rw [ProbComp.eval_map, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_run_interpret,
    PMF.map_comp]
  -- Reconstruct the filter flag from the query log, so no state invariant is needed.
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun q s => ProbComp.eval (oneTimeSigningOracleOf sign sk q s))
    (oracle' := fun q (state : Bool × List (List Bool)) =>
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (signingOracleOf sign sk q s))
          ((oneTimeFilterHandler bound (n, pk) q).run state.1) state.2).map
          (fun result => (result.1.1, result.1.2, result.2)))
    (represent := fun queried => (!queried.isEmpty, queried))
    (step := by
      intro ⟨⟨⟩, msg⟩ queried
      change _ = ((OracleComp.interpret (m := StateT (List (List Bool)) PMF) _
        (oneTimeFilterHandler bound (n, pk) ((), msg) (!queried.isEmpty))).run queried).map _
      cases queried with
      | nil =>
        simp only [oneTimeSigningOracleOf, List.isEmpty_nil, ↓reduceIte, Bool.not_true,
          oneTimeFilterHandler, Bool.false_eq_true, Functor.map_map,
          OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, signingOracleOf,
          ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind]
        simp only [StateT.run, PMF.map_bind]
        refine PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_
        simp [List.take_of_length_le (hbound msg sig hsig)]
      | cons head tail =>
        simp [oneTimeSigningOracleOf, oneTimeFilterHandler, OracleComp.interpret_pure,
          StateT.run_pure, ProbComp.eval_pure])
    prog []
  have hproj := congrArg (PMF.map (fun result => (result.1, result.2.2))) hsim
  rw [PMF.map_comp] at hproj
  exact hproj.symm.trans (PMF.map_id _)

theorem run_limitToOneQuery_eq_oneTimeSigningOracle (S : SignatureScheme)
    (bound : ℕ → ℕ → ℕ) (n : ℕ) (pk sk : List Bool)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (S.sign sk msg)).support →
      sig.length ≤ bound n msg.length)
    (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval (Prod.map Prod.fst id <$> ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (S.signingOracle sk))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (oneTimeFilterHandler bound (n, pk)))
        prog).run false)).run [])) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (S.oneTimeSigningOracle sk)) prog).run []) :=
  run_limitToOneQuery_eq_oneTimeSigningOracleOf S.sign bound n pk sk hbound prog

/-- Full EUF-CMA security implies one-time EUF-CMA security. -/
theorem EUFCMA.oneTimeEUFCMA {S : SignatureScheme} (h : S.EUFCMA) : S.OneTimeEUFCMA := by
  obtain ⟨ck, dk, hlenk⟩ := S.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := S.sign_ppt.length_le
  let skBound (n : ℕ) : ℕ := ck * (n + 1) ^ dk
  let bound (n msgLen : ℕ) : ℕ := cs * (2 * skBound n + msgLen + 2) ^ ds
  have hsk : ComputableInPolyTime (fun p : ℕ × ℕ => skBound p.1)
      (encPair encUnary encUnary) encUnary :=
    (ComputableInPolyTime.const ck).unary_mul' ((ComputableInPolyTime.unary_pow dk).comp
      ((ComputableInPolyTime.fst encUnary encUnary).unary_add' (.const 1)))
  have hbound_poly : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary :=
    (ComputableInPolyTime.const cs).unary_mul' ((ComputableInPolyTime.unary_pow ds).comp
      ((((ComputableInPolyTime.const 2).unary_mul' hsk).unary_add' (.snd _ _)).unary_add'
        (.const 2)))
  refine h.of_succProbability_reduction (limitToOneQuery bound)
    (fun _ => isOraclePPT_limitToOneQuery hbound_poly) fun adversary _ n => ?_
  refine le_of_eq (congrArg Game.succProbability ?_)
  simp only [eufOneTimeGame, eufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  have hkeysLen := hlenk n keys hkeys
  simp only [encUnary_apply, List.length_replicate, length_encPair, encBits_apply] at hkeysLen
  have hsigBound (msg sig : List Bool) (hsig : sig ∈ (ProbComp.eval (S.sign keys.2 msg)).support) :
      sig.length ≤ bound n msg.length := by
    have h1 := hlens (keys.2, msg) sig hsig
    simp only [length_encPair, encBits_apply] at h1
    have h2 : 2 * keys.2.length + 1 + msg.length + 1 ≤ 2 * skBound n + msg.length + 2 := by
      dsimp [skBound]; lia
    exact h1.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left h2 ds))
  have hrun := run_limitToOneQuery_eq_oneTimeSigningOracle S bound n keys.1 keys.2 hsigBound
    (adversary n keys.1)
  dsimp only [limitToOneQuery]
  rw [OracleComp.interpret_map, StateT.run_map]
  exact (congrArg (fun p : PMF ((List Bool × List Bool) × List (List Bool)) =>
    p.bind fun x => PMF.pure
      ((x.1.1.length == n) && !x.2.contains x.1.1 && S.verify keys.1 x.1.1 x.1.2)) hrun).symm

end SignatureScheme

end Cslib.Crypto
