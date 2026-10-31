/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Computational.PseudorandomFunction
public import Complexity.Crypto.Game.UntilBad
public import Complexity.Languages.Probabilistic.UniformNat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Tidy
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Crypto.Game.Hybrid
import Complexity.Crypto.Negligible.Basic
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Authenticated Encryption and Adaptive Chosen-Ciphertext Security

This module formalizes symmetric authenticated encryption (`AuthenticatedEncryption`) and adaptive
chosen-ciphertext security (`INDCCA`) following
[Boneh and Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
Chapter 5 (Sections 5.3 and 5.10) and Chapter 9 (Sections 9.1 and 9.2.2–9.2.3):

1. **Symmetric ciphers and adaptive/one-time CPA security (`SymmetricCipher`, `cpaGame`, `INDCPA`,
   `cpaOneTimeGame`, `OneTimeINDCPA`, `not_indcpa_of_ciphertext_length_eq`)**
   ([BonehShoup2023], Section 2.2, Attack Game 2.1 and Definition 2.2; Section 5.3, Attack Game 5.2,
   Definition 5.2, and Example 5.1, printed pp. 181–182; Exercise 5.10(a), printed p. 211):
   a uniform symmetric cipher on `n`-bit messages at security parameter `n` consists of strict PPT
   key generation `keyGen`, strict PPT encryption `encrypt`, and deterministic polynomial-time
   decryption `decrypt` returning `Option (List Bool)` (encoded via `encOption encBits`). In
   `cpaGame`, an adaptive `OracleDistinguisher` submits left-or-right pairs `(m0, m1)` of `n`-bit
   messages and receives `encrypt n k (if bit then m1 else m0)`; `cpaOneTimeGame` and
   `OneTimeINDCPA` restrict the oracle to at most one valid encryption query. We also formalize
   Example 5.1 and Exercise 5.10(a) (`not_indcpa_of_ciphertext_length_eq`): if every supported
   ciphertext of an `n`-bit message has length `n`, decryption completeness forces `encrypt` to be a
   deterministic permutation on `n`-bit strings, which a 2-query CPA adversary (`detCPAAdversary`)
   breaks with advantage `1`.
2. **Ciphertext integrity and authenticated encryption (`ciGame`, `CiphertextIntegrity`,
   `AuthenticatedEncryption`, `ciOneTimeGame`, `OneTimeCiphertextIntegrity`,
   `OneTimeAuthenticatedEncryption`)** ([BonehShoup2023], Section 9.1, Attack Game 9.1 and
   Definitions 9.1–9.4, printed pp. 358–360): in `ciGame` (and its single-query counterpart
   `ciOneTimeGame`), an adaptive `CIAdversary` queries an encryption oracle on `n`-bit messages
   (logging returned ciphertexts in `queriedCiphertexts`) and wins by outputting a candidate
   ciphertext `ct` such that `!queriedCiphertexts.contains ct` and `(decrypt n k ct).isSome`. A
   cipher provides `AuthenticatedEncryption` when it satisfies both `INDCPA` and
   `CiphertextIntegrity`, and `OneTimeAuthenticatedEncryption` (`1AE`) when it satisfies both
   `OneTimeINDCPA` and `OneTimeCiphertextIntegrity`.
3. **Adaptive chosen-ciphertext security, AE $\Rightarrow$ CCA, 1AE $\Rightarrow$ 1CCA, and
   encryption-query preservation (`ccaGame`, `INDCCA`, `ccaOneTimeGame`, `OneTimeINDCCA`,
   `ccaToCPAAdversary`, `ccaToCIAdversary`, `ccaToCIHiddenBitAdversary`,
   `IsEncryptionQueryBounded`, `isQueryBounded_ccaToCPAAdversary_of_isEncryptionQueryBounded`,
   `isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded`,
   `advantage_ccaGame_le`, `advantage_ccaGame_le_two_mul`, `AuthenticatedEncryption.indcca`,
   `advantage_ccaOneTimeGame_le`, `advantage_ccaOneTimeGame_le_two_mul`,
   `OneTimeAuthenticatedEncryption.oneTimeINDCCA`)**
   ([BonehShoup2023], Sections 9.2.2–9.2.3, Attack Game 9.2, Definitions 9.5–9.6, and Theorem 9.1,
   printed pp. 362–365): in `ccaGame` (and its single-encryption-query counterpart
   `ccaOneTimeGame`), a two-channel `CCAAdversary` (`Operation = Bool`) may interleave
   left-or-right encryption queries (`false`, recording challenge ciphertexts) with decryption
   queries (`true`, rejecting recorded challenge ciphertexts and returning
   `encOption encBits (decrypt n k ct)` on all other ciphertexts). Using the difference lemma
   (`OracleComp.IdenticalUntilBad.advantage_le`, [BonehShoup2023], Theorem 4.7) between `ccaGame`
   and `ccaRejectGame` (and between `ccaOneTimeGame` and `ccaOneTimeRejectGame`), we prove both
   `AE ⇒ CCA` (`AuthenticatedEncryption.indcca`) and `1AE ⇒ 1CCA`
   (`OneTimeAuthenticatedEncryption.oneTimeINDCCA`), as well as encryption-query count preservation
   for the reductions $B_{\mathrm{cpa}}$ and $B_{\mathrm{ci}}$.

The generic **Encrypt-then-MAC** composition ([BonehShoup2023], Section 9.4.1, Theorem 9.2,
printed pp. 367–368) and its concrete non-vacuous PRF-based cipher instance ([BonehShoup2023],
Section 5.4.1, Example 5.2 and Theorem 5.2, printed pp. 183–187) are formalized in
`Complexity.Crypto.Computational.Encryption.EncryptThenMAC`.

## Specializations and losses relative to Boneh–Shoup Chapter 9

* **Fixed `n`-bit plaintext domain at security parameter `n`**: encryption queries take `n`-bit
  messages (`msg.length = n` in `ciGame`, `m0.length = n ∧ m1.length = n` in `cpaGame` and
  `ccaGame`). Malformed encryption queries return `[]` without invoking `encrypt` or recording a
  challenge ciphertext.
* **Challenge-ciphertext decryption queries in `ccaOracle`**: in Section 9.2.2 (printed p. 362),
  the text stipulates that "The restriction we impose is that the adversary may not ask for the
  decryptions of any of these ciphertexts." In
  `ccaOracle`, decryption queries on previously returned challenge ciphertexts
  (`queriedCiphertexts`) are instead answered with `[] = encOption encBits none` (rejection), which
  is equivalent for adversaries respecting the restriction and makes `ccaOracle` a total function on
  all queries.
* **Total-query budget in Theorem 9.1**: in equation (9.3) of [BonehShoup2023] (printed p. 363),
  the CI term has coefficient `2 * Qd` (where `Qd` bounds decryption queries). Here
  `ccaToCIAdversary` samples a query index uniformly from `{0, ..., dyadicSize (Q n) - 1}` via
  `ProbComp.sampleDyadicIndex (Q n)` (where `Q n < dyadicSize (Q n) ≤ 2 * Q n + 2`) and decrements
  the countdown on every external oracle call (`Sum.inr`) of
  `(adversary n []).IsQueryBounded (Q n)`, where `Q n` bounds total queries `Qe + Qd`. This yields
  factor `dyadicSize (Q n)` in `advantage_ccaGame_le` and `2 * dyadicSize (Q n) ≤ 4 * Q n + 4` in
  `advantage_ccaGame_le_two_mul`, which remains polynomial in `n` for
  `AuthenticatedEncryption.indcca` and `OneTimeAuthenticatedEncryption.oneTimeINDCCA`.

## Main definitions

* `Cslib.Crypto.CIAdversary`, `Cslib.Crypto.CCAAdversary`: adaptive ciphertext-integrity and
  chosen-ciphertext adversaries.
* `Cslib.Crypto.SymmetricCipher`: uniform symmetric cipher on `n`-bit messages.
* `Cslib.Crypto.SymmetricCipher.cpaGame`, `INDCPA`, `cpaOneTimeGame`, `OneTimeINDCPA`,
  `detCPAAdversary`: adaptive and one-time symmetric CPA games, security predicates, and 2-query
  determinism distinguisher ([BonehShoup2023], Attack Game 5.2 / Definition 5.2 / Example 5.1 /
  Definition 9.4).
* `Cslib.Crypto.SymmetricCipher.ciGame`, `CiphertextIntegrity`, `AuthenticatedEncryption`,
  `ciOneTimeGame`, `OneTimeCiphertextIntegrity`, `OneTimeAuthenticatedEncryption`:
  multi-query and one-time ciphertext-integrity games, CI predicates, and AE predicates
  ([BonehShoup2023], Attack Game 9.1 / Definitions 9.1–9.4).
* `Cslib.Crypto.SymmetricCipher.ccaGame`, `ccaRejectGame`, `INDCCA`, `ccaOneTimeGame`,
  `ccaOneTimeRejectGame`, `OneTimeINDCCA`: adaptive and one-time CCA games, all-reject hybrid
  games, and CCA security predicates ([BonehShoup2023], Attack Game 9.2 / Definitions 9.5–9.6).
* `Cslib.Crypto.SymmetricCipher.ccaToCPAAdversary`, `ccaToCIAdversary`,
  `ccaToCIHiddenBitAdversary`, `IsEncryptionQueryBounded`: Theorem 9.1 reductions from CCA to CPA
  and CI and structural encryption-query budget predicate.

## Main results

* `Cslib.Crypto.SymmetricCipher.isPPTOn_cpaGame`, `isPPT_cpaGame`, `isPPTOn_cpaOneTimeGame`,
  `isPPT_cpaOneTimeGame`, `isPPTOn_ciGame`, `isPPT_ciGame`, `isPPTOn_ciOneTimeGame`,
  `isPPT_ciOneTimeGame`, `isPPTOn_ccaGame`, `isPPT_ccaGame`, `isPPTOn_ccaOneTimeGame`,
  `isPPT_ccaOneTimeGame`: strict PPT certificates for the multi-query and one-time CPA, CI, and CCA
  experiments.
* `Cslib.Crypto.SymmetricCipher.encrypt_eq_of_ciphertext_length_eq`,
  `Cslib.Crypto.SymmetricCipher.advantage_cpaGame_detCPAAdversary`,
  `Cslib.Crypto.SymmetricCipher.not_indcpa_of_ciphertext_length_eq`: any cipher whose ciphertexts on
  `n`-bit messages have length `n` is forced by decryption completeness to be deterministic and
  hence cannot satisfy `INDCPA` ([BonehShoup2023], Example 5.1 and Exercise 5.10(a)).
* `Cslib.Crypto.SymmetricCipher.isOraclePPT_ccaToCPAAdversary`,
  `Cslib.Crypto.SymmetricCipher.isOraclePPT_ccaToCIAdversary`,
  `Cslib.Crypto.SymmetricCipher.isOraclePPT_ccaToCIHiddenBitAdversary`,
  `Cslib.Crypto.SymmetricCipher.isQueryBounded_ccaToCPAAdversary_of_isEncryptionQueryBounded`,
  `Cslib.Crypto.SymmetricCipher.isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded`:
  `IsOraclePPT` and encryption-query preservation certificates for the Theorem 9.1 reductions.
* `Cslib.Crypto.SymmetricCipher.advantage_ccaGame_le`,
  `Cslib.Crypto.SymmetricCipher.advantage_ccaGame_le_two_mul`,
  `Cslib.Crypto.SymmetricCipher.AuthenticatedEncryption.indcca`,
  `Cslib.Crypto.SymmetricCipher.advantage_ccaOneTimeGame_le`,
  `Cslib.Crypto.SymmetricCipher.advantage_ccaOneTimeGame_le_two_mul`,
  `Cslib.Crypto.SymmetricCipher.OneTimeAuthenticatedEncryption.oneTimeINDCCA`: quantitative and
  asymptotic AE $\Rightarrow$ CCA and 1AE $\Rightarrow$ 1CCA security
  ([BonehShoup2023], Theorem 9.1).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 5.3 (pp. 181–182), Exercise 5.10(a) (p. 211), and Chapter 9,
  Sections 9.1 and 9.2.2–9.2.3 (pp. 357–365).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- An adaptive ciphertext-integrity adversary receives the unary security parameter and an
auxiliary word, queries an encryption oracle on chosen messages, and outputs a candidate
ciphertext. -/
abbrev CIAdversary := ℕ → List Bool → WordOracleComp Unit (List Bool)

/-- An adaptive chosen-ciphertext distinguisher receives the unary security parameter and an
auxiliary word, queries a left-or-right encryption oracle (`false`) and a decryption oracle
(`true`), and outputs a distinguishing bit. -/
abbrev CCAAdversary := ℕ → List Bool → WordOracleComp Bool Bool

/-- A uniform symmetric cipher on `n`-bit messages at security parameter `n`, with strict
probabilistic polynomial-time key generation and encryption, deterministic polynomial-time
decryption (returning `Option (List Bool)`), and perfect decryption completeness on supported keys,
`n`-bit messages, and ciphertexts ([BonehShoup2023], Sections 5.3 and 9.1). -/
structure SymmetricCipher where
  /-- Sample a symmetric secret key `k` at unary security parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool)
  /-- Probabilistically encrypt a message `msg` under secret key `k` at security parameter `n`. -/
  encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically decrypt a candidate ciphertext `ct` under secret key `k` at parameter `n`,
  returning `none` on rejection and `some msg` on acceptance. -/
  decrypt : ℕ → List Bool → List Bool → Option (List Bool)
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary encBits keyGen
  /-- Encryption is uniformly strict PPT in `(n, k, msg)`. -/
  encrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
    (fun p => encrypt p.1 p.2.1 p.2.2)
  /-- Decryption is computable in plain polynomial time on `(n, k, ct)`. -/
  decrypt_polyTime : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) (encOption encBits)
  /-- Every ciphertext produced by `encrypt` on an `n`-bit message under a supported secret key at
  security parameter `n` decrypts to `some msg`. -/
  decrypt_encrypt : ∀ n k, k ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = n →
    ∀ ct, ct ∈ (ProbComp.eval (encrypt n k msg)).support →
    decrypt n k ct = some msg

namespace SymmetricCipher

attribute [program_certificate] keyGen_ppt encrypt_ppt decrypt_polyTime

/-- `E.keyGen` composed with a plain polynomial-time parameter selector is uniformly strict PPT. -/
@[program_certificate, fun_prop]
theorem isPPTOn_keyGen_comp (E : SymmetricCipher) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn encBits (fun a => E.keyGen (n a)) :=
  E.keyGen_ppt.preprocess hn

/-- `E.encrypt` composed with plain polynomial-time parameter, key, and message selectors is
uniformly strict PPT. -/
@[program_certificate, fun_prop]
theorem isPPTOn_encrypt_comp (E : SymmetricCipher) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {k msg : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hk : ComputableInPolyTime k encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => E.encrypt (n a) (k a) (msg a)) :=
  E.encrypt_ppt.preprocess (.of_tidy (hn.tidy.prod (hk.tidy.prod hmsg.tidy)))

/-- `E.decrypt` composed with plain polynomial-time parameter, key, and ciphertext selectors is
computable in plain polynomial time. -/
@[program_certificate, fun_prop]
theorem computableInPolyTime_decrypt_comp (E : SymmetricCipher)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {k ct : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hk : ComputableInPolyTime k encIn encBits)
    (hct : ComputableInPolyTime ct encIn encBits) :
    ComputableInPolyTime (fun a => E.decrypt (n a) (k a) (ct a)) encIn (encOption encBits) :=
  .of_tidy (E.decrypt_polyTime.tidy.comp (hn.tidy.prod (hk.tidy.prod hct.tidy)))

/-! ### Adaptive Chosen-Plaintext Security (`cpaGame`, `INDCPA`) -/

/-- Stateful left-or-right CPA encryption oracle ([BonehShoup2023], Section 5.3, Attack Game 5.2):
decode the request into `m0 = unframe request.2` and `m1 = dropFrame request.2`; if both have
length `n`, encrypt `if bit then m1 else m0` under `k`, and otherwise return `[]`. -/
noncomputable def cpaEncryptionOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Unit × List Bool) : StateT Unit ProbComp (List Bool) :=
  fun _ =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if (m0.length == n) && (m1.length == n) then do
      let ct ← E.encrypt n k (if bit then m1 else m0)
      return (ct, ())
    else
      return ([], ())

/-- The adaptive symmetric IND-CPA experiment ([BonehShoup2023], Section 5.3, Attack Game 5.2):
sample `k ← E.keyGen n` and run `adversary n []` against `E.cpaEncryptionOracle n k bit`. -/
noncomputable def cpaGame (E : SymmetricCipher) (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.cpaEncryptionOracle n k bit)) (adversary n [])).run ()
  return out.1

/-- Running an oracle-PPT distinguisher against `cpaEncryptionOracle` is uniformly strict PPT in
`(n, k)` for each challenge bit `bit`. -/
@[program_certificate]
theorem isPPTOn_run_cpaEncryptionOracle (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool (encFinEnum Unit))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.cpaEncryptionOracle caller.1 caller.2 bit)) (adversary caller.1 [])).run ()) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hm0 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => unframe p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [EIn]; fun_prop)
  have hm1 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => dropFrame p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [EIn]; fun_prop)
  have hcond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hmsg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        (p.1.1, p.1.2, if bit then dropFrame p.2.1.2 else unframe p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop)
      (ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop) hmsg)
  have hyes : IsPPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => do
        let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
        return (ct, ())) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((ComputableTidilyInPolyTime.prod (by fun_prop)
        (ComputableTidilyInPolyTime.const ())).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun _ => pure ([], ())) :=
    (ComputableTidilyInPolyTime.const ([], ())).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        E.cpaEncryptionOracle pair.1.1 pair.1.2 bit pair.2.1 pair.2.2) := by
    unfold cpaEncryptionOracle
    exact IsPPTOn.cond hcond hyes hno
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ())
    (resources := fun caller _ =>
      c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d + 1)
    (by fun_prop) hhandler (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) (by polytime)
  intro caller request _ _ result hresult
  unfold cpaEncryptionOracle at hresult
  by_cases hlenEq : ((unframe request.2).length == caller.1 &&
      (dropFrame request.2).length == caller.1) = true
  · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨ct, hct, rfl⟩ := hresult
    simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
    have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = caller.1 := by
      cases bit <;> simp [hlenEq]
    have hctLen := hlen (caller.1, caller.2, if bit then dropFrame request.2 else unframe request.2)
      ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmbLen] at hctLen
    have hbound : ct.length ≤ c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d :=
      hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    exact ⟨trivial, by lia, by lia⟩
  · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- The symmetric CPA experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_cpaGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.cpaGame adversary bit) := by
  have hrun := E.isPPTOn_run_cpaEncryptionOracle hadversary bit
  unfold cpaGame
  exact E.keyGen_ppt.bind_with (hrun.bind (ComputableTidilyInPolyTime.fst _ _).isPPTOn)

/-- The symmetric CPA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_cpaGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.cpaGame adversary bit n) :=
  ((E.isPPTOn_cpaGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Adaptive chosen-plaintext security (`INDCPA`) for a symmetric cipher ([BonehShoup2023],
Section 5.3, Attack Game 5.2 and Definition 5.2): every uniform strict `IsOraclePPT encBool`
distinguisher has negligible advantage between `E.cpaGame adversary false` and
`E.cpaGame adversary true`. -/
def INDCPA (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.cpaGame adversary false n))
    (fun adversary n => ProbComp.eval (E.cpaGame adversary true n))
    (IsOraclePPT encBool)

/-- Stateful one-time left-or-right CPA encryption oracle ([BonehShoup2023], Section 2.2,
Attack Game 2.1 and Definition 2.2; Section 9.1.1, Definition 9.4, printed p. 360): answers at most
one valid `n`-bit left-or-right encryption query (`!alreadyQueried && m0.length == n &&
m1.length == n`), transitioning `alreadyQueried` from `false` to `true`, and returns `[]` on all
subsequent or malformed queries. -/
noncomputable def oneTimeCPAEncryptionOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Unit × List Bool) : StateT Bool ProbComp (List Bool) :=
  fun alreadyQueried =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if !alreadyQueried && (m0.length == n) && (m1.length == n) then do
      let ct ← E.encrypt n k (if bit then m1 else m0)
      return (ct, true)
    else
      return ([], alreadyQueried)

/-- The one-time symmetric CPA (semantic security) experiment ([BonehShoup2023], Section 2.2,
Attack Game 2.1 and Section 9.1.1, Definition 9.4): sample `k ← E.keyGen n` and run `adversary n []`
against `E.oneTimeCPAEncryptionOracle n k bit` starting from `alreadyQueried = false`. -/
noncomputable def cpaOneTimeGame (E : SymmetricCipher) (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.oneTimeCPAEncryptionOracle n k bit)) (adversary n [])).run false
  return out.1

/-- Running an oracle-PPT distinguisher against `oneTimeCPAEncryptionOracle` is uniformly strict PPT
in `(n, k)` for each challenge bit `bit`. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeCPAEncryptionOracle (E : SymmetricCipher)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.oneTimeCPAEncryptionOracle caller.1 caller.2 bit))
          (adversary caller.1 [])).run false) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hm0 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => unframe p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [EIn]; fun_prop)
  have hm1 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => dropFrame p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [EIn]; fun_prop)
  have hcond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        !p.2.2 && ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hmsg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        (p.1.1, p.1.2, if bit then dropFrame p.2.1.2 else unframe p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop)
      (ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop) hmsg)
  have hyes : IsPPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => do
        let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
        return (ct, true)) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((ComputableTidilyInPolyTime.prod (by fun_prop)
        (ComputableTidilyInPolyTime.const true)).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => pure ([], p.2.2)) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        E.oneTimeCPAEncryptionOracle pair.1.1 pair.1.2 bit pair.2.1 pair.2.2) := by
    unfold oneTimeCPAEncryptionOracle
    exact IsPPTOn.cond hcond hyes hno
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => false)
    (resources := fun caller _ =>
      c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d + 1)
    (by fun_prop) hhandler (ComputableTidilyInPolyTime.const false)
    (fun _ _ => True) (fun _ => trivial) (by polytime)
  intro caller request alreadyQueried _ result hresult
  unfold oneTimeCPAEncryptionOracle at hresult
  by_cases hlenEq : (!alreadyQueried && ((unframe request.2).length == caller.1) &&
      ((dropFrame request.2).length == caller.1)) = true
  · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨ct, hct, rfl⟩ := hresult
    simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
    have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = caller.1 := by
      cases bit <;> simp [hlenEq]
    have hctLen := hlen (caller.1, caller.2, if bit then dropFrame request.2 else unframe request.2)
      ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmbLen] at hctLen
    have hbound : ct.length ≤ c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d :=
      hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    exact ⟨trivial, by lia, by simp [encBool_apply]⟩
  · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by simp [encBool_apply]⟩

/-- The one-time symmetric CPA experiment is uniformly strict PPT in the unary security
parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_cpaOneTimeGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.cpaOneTimeGame adversary bit) := by
  have hrun := E.isPPTOn_run_oneTimeCPAEncryptionOracle hadversary bit
  unfold cpaOneTimeGame
  exact E.keyGen_ppt.bind_with (hrun.bind (ComputableTidilyInPolyTime.fst _ _).isPPTOn)

/-- The one-time symmetric CPA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_cpaOneTimeGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.cpaOneTimeGame adversary bit n) :=
  ((E.isPPTOn_cpaOneTimeGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- One-time chosen-plaintext security (semantic security under a single encryption query,
`OneTimeINDCPA`) for a symmetric cipher ([BonehShoup2023], Section 2.2, Attack Game 2.1 and
Definition 2.2; Section 9.1.1, Definition 9.4, printed p. 360): every uniform strict
`IsOraclePPT encBool` distinguisher has negligible advantage between
`E.cpaOneTimeGame adversary false` and `E.cpaOneTimeGame adversary true`. -/
def OneTimeINDCPA (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.cpaOneTimeGame adversary false n))
    (fun adversary n => ProbComp.eval (E.cpaOneTimeGame adversary true n))
    (IsOraclePPT encBool)

/-- Stateful filter handler that forwards at most one valid `n`-bit CPA query to an external
multi-query CPA encryption oracle (truncating replies to `ctBound`). -/
noncomputable def cpaOneTimeFilterHandler (n ctBound : ℕ) (request : Unit × List Bool) :
    StateT Bool (WordOracleComp Unit) (List Bool) :=
  fun alreadyQueried =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if !alreadyQueried && (m0.length == n) && (m1.length == n) then
      (fun ct => (ct, true)) <$> (List.take ctBound <$> ProbOracleComp.query ((), request.2))
    else
      pure ([], alreadyQueried)

/-- Reduction from `cpaOneTimeGame` to `cpaGame`: run `adversary n []` against
`cpaOneTimeFilterHandler n (ctBound n)` starting from `alreadyQueried = false`. -/
noncomputable def cpaLimitToOneQuery (ctBound : ℕ → ℕ) (adversary : OracleDistinguisher) :
    OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (cpaOneTimeFilterHandler n (ctBound n)))
      (adversary n [])).run false
    return out.1

/-- `cpaLimitToOneQuery` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_cpaLimitToOneQuery {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (cpaLimitToOneQuery ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        !p.2.2 && ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hlimit : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => ctBound p.1.1)
      EIn encUnary :=
    hctBound.comp (by dsimp only [EIn]; fun_prop)
  have hquery : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        (fun ct => (ct, true)) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query ((), p.2.1.2))) :=
    (IsOraclePPTOn.query_take' () (by dsimp only [EIn]; fun_prop) hlimit).map'
      (ComputableInPolyTime.prod (by fun_prop) (ComputableInPolyTime.const true))
  have hnoReply : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        cpaOneTimeFilterHandler pair.1.1 (ctBound pair.1.1) pair.2.1 pair.2.2) := by
    unfold cpaOneTimeFilterHandler
    exact IsOraclePPTOn.cond' hcond hquery hnoReply
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add' (hctBound.comp (by fun_prop)) (ComputableInPolyTime.const 1)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (cpaOneTimeFilterHandler caller.1 (ctBound caller.1)))
          (adversary caller.1 [])).run false) := by
    apply hadversary.run_interpret_preprocess_open'
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => false)
      (resources := fun caller _ => ctBound caller.1 + 1)
      (by fun_prop) hhandler (ComputableInPolyTime.const false)
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request alreadyQueried _ result hresult
    unfold cpaOneTimeFilterHandler at hresult
    dsimp only at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨ct, hct, rfl⟩ := ProbOracleComp.mem_support_map hresult
      obtain ⟨rawCt, _, rfl⟩ := ProbOracleComp.mem_support_map hct
      exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by simp [encBool_apply]⟩
    · cases ProbOracleComp.eq_of_mem_support_pure hresult
      exact ⟨trivial, by simp, by simp [encBool_apply]⟩
  unfold cpaLimitToOneQuery
  simpa only [bind_pure_comp] using (hrun.map' (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `cpaLimitToOneQuery ctBound adversary` in `cpaGame` has the exact same output distribution
as `cpaOneTimeGame adversary`. -/
theorem eval_cpaGame_cpaLimitToOneQuery (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.cpaGame (cpaLimitToOneQuery ctBound adversary) bit n) =
      ProbComp.eval (E.cpaOneTimeGame adversary bit n) := by
  simp only [cpaGame, cpaOneTimeGame, cpaLimitToOneQuery, ProbComp.eval_bind, ProbComp.eval_pure]
  apply PMF.bind_congr_on_support
  intro k hk
  simp only [ProbOracleComp.eval_run_interpret]
  rw [OracleComp.interpret_bind, StateT.run_bind]
  simp only [StateT.run_pure, OracleComp.interpret_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.run_interpret_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (fun request alreadyQueried =>
      ProbComp.eval (E.oneTimeCPAEncryptionOracle n k bit request alreadyQueried))
    (fun request state =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.cpaEncryptionOracle n k bit q s)))
        ((cpaOneTimeFilterHandler n (ctBound n) request).run state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun alreadyQueried : Bool => (alreadyQueried, ()))
    (fun request alreadyQueried => by
      change (ProbComp.eval (E.oneTimeCPAEncryptionOracle n k bit request alreadyQueried)).map
          (fun x => (x.1, x.2, ())) =
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.cpaEncryptionOracle n k bit q s)))
          (cpaOneTimeFilterHandler n (ctBound n) request alreadyQueried)).run ()).map
          (fun result => (result.1.1, result.1.2, result.2))
      simp only [oneTimeCPAEncryptionOracle, cpaOneTimeFilterHandler]
      by_cases hcond : (!alreadyQueried && ((unframe request.2).length == n) &&
          ((dropFrame request.2).length == n)) = true
      · simp only [hcond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
          Functor.map_map, OracleComp.interpret_map, StateT.run_map,
          ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map, cpaEncryptionOracle]
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        have hlenEq : (((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true := by
          simp [hcond.1.2, hcond.2]
        dsimp only [StateT.run]
        simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
          PMF.map_bind, PMF.pure_map]
        have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
          cases bit <;> simp [hcond.1.2, hcond.2]
        apply PMF.bind_congr_on_support
        intro ct hct
        rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
          OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
          PMF.pure_map])
    (adversary n []) false
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

/-- Multi-query `INDCPA` security implies one-time `OneTimeINDCPA` security. -/
theorem INDCPA.oneTimeINDCPA {E : SymmetricCipher} (hcpa : E.INDCPA) :
    E.OneTimeINDCPA := by
  intro adversary hadversary
  obtain ⟨ck, dk, hlenKey⟩ := E.keyGen_ppt.length_le
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  let ctBound : ℕ → ℕ := fun n => ce * (3 * n + 2 * (ck * (n + 1) ^ dk) + 4) ^ de
  have hctBoundPoly : ComputableInPolyTime ctBound encUnary encUnary := by
    dsimp only [ctBound]; polytime
  have hctBound (n : ℕ) (k : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
      (msg : List Bool) (hmsg : msg.length = n) (ct : List Bool)
      (hct : ct ∈ (ProbComp.eval (E.encrypt n k msg)).support) : ct.length ≤ ctBound n := by
    have hkLen := hlenKey n k hk
    have hctLen := hlenEnc (n, k, msg) ct hct
    simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkLen
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmsg] at hctLen
    exact hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
  have hneg := hcpa (cpaLimitToOneQuery ctBound adversary)
    (isOraclePPT_cpaLimitToOneQuery hctBoundPoly hadversary)
  refine hneg.congr fun n => ?_
  dsimp only
  rw [eval_cpaGame_cpaLimitToOneQuery E ctBound adversary false n (hctBound n),
    eval_cpaGame_cpaLimitToOneQuery E ctBound adversary true n (hctBound n)]

/-! #### Impossibility of Zero-Expansion CPA Security (Boneh–Shoup Example 5.1 & Exercise 5.10(a))
-/

/-- **Zero ciphertext expansion forces deterministic encryption** ([BonehShoup2023],
Exercise 5.10(a), printed p. 211): if every supported ciphertext of an `n`-bit message under a
supported key `ke` at parameter `n` has length `n`, then decryption completeness
(`E.decrypt_encrypt`) gives an injection from the `2^n` plaintexts `BitString n` into `BitString n`
by choosing one supported ciphertext per plaintext; by finiteness of `BitString n`, this map is
surjective, forcing all supported ciphertexts of any `n`-bit plaintext `msg` under `ke` to
coincide. -/
theorem encrypt_eq_of_ciphertext_length_eq (E : SymmetricCipher) {n : ℕ} {ke : List Bool}
    (hke : ke ∈ (ProbComp.eval (E.keyGen n)).support)
    (hctLen : ∀ msg : List Bool, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    {msg : List Bool} (hmsg : msg.length = n)
    {c₁ c₂ : List Bool}
    (hc₁ : c₁ ∈ (ProbComp.eval (E.encrypt n ke msg)).support)
    (hc₂ : c₂ ∈ (ProbComp.eval (E.encrypt n ke msg)).support) :
    c₁ = c₂ := by
  let toBS : (l : List Bool) → l.length = n → BitString n :=
    fun l hl i => l[i.val]'(hl ▸ i.isLt)
  have hofFn_toBS (l : List Bool) (hl : l.length = n) : List.ofFn (toBS l hl) = l := by
    apply List.ext_getElem (by simp [hl])
    intro i hi₁ hi₂
    simp [toBS]
  let chooseCt (v : BitString n) : List Bool :=
    (ProbComp.eval (E.encrypt n ke (List.ofFn v))).support_nonempty.some
  have hchooseMem (v : BitString n) :
      chooseCt v ∈ (ProbComp.eval (E.encrypt n ke (List.ofFn v))).support :=
    (ProbComp.eval (E.encrypt n ke (List.ofFn v))).support_nonempty.some_mem
  have hchooseLen (v : BitString n) : (chooseCt v).length = n :=
    hctLen (List.ofFn v) (List.length_ofFn) (chooseCt v) (hchooseMem v)
  have hchooseDec (v : BitString n) : E.decrypt n ke (chooseCt v) = some (List.ofFn v) :=
    E.decrypt_encrypt n ke hke (List.ofFn v) (List.length_ofFn) (chooseCt v) (hchooseMem v)
  let g : BitString n → BitString n := fun v => toBS (chooseCt v) (hchooseLen v)
  have hgInj : Function.Injective g := by
    intro v₁ v₂ hgv
    have hctEq : chooseCt v₁ = chooseCt v₂ := by
      rw [← hofFn_toBS (chooseCt v₁) (hchooseLen v₁),
        ← hofFn_toBS (chooseCt v₂) (hchooseLen v₂)]
      exact congrArg List.ofFn hgv
    have hdecEq : some (List.ofFn v₁) = some (List.ofFn v₂) := by
      rw [← hchooseDec v₁, ← hchooseDec v₂, hctEq]
    exact List.ofFn_injective (Option.some.inj hdecEq)
  have hgSurj : Function.Surjective g := Finite.injective_iff_surjective.mp hgInj
  have huniq (c : List Bool) (hc : c ∈ (ProbComp.eval (E.encrypt n ke msg)).support) :
      c = chooseCt (toBS msg hmsg) := by
    have hlen : c.length = n := hctLen msg hmsg c hc
    obtain ⟨v, hv⟩ := hgSurj (toBS c hlen)
    have hcv : chooseCt v = c := by
      rw [← hofFn_toBS (chooseCt v) (hchooseLen v), ← hofFn_toBS c hlen]
      exact congrArg List.ofFn hv
    have hdec : some (List.ofFn v) = some msg := by
      rw [← hchooseDec v, hcv, E.decrypt_encrypt n ke hke msg hmsg c hc]
    have hvEq : v = toBS msg hmsg := by
      apply List.ofFn_injective
      rw [Option.some.inj hdec, hofFn_toBS msg hmsg]
    rw [← hvEq, hcv]
  rw [huniq c₁ hc₁, huniq c₂ hc₂]

/-- Two-query CPA distinguisher against any deterministic symmetric cipher
([BonehShoup2023], Example 5.1, printed p. 182): queries `(0^n, 1^n)` followed by `(0^n, 0^n)` and
outputs `true` iff the two returned ciphertexts are equal (`c₁ == c₂`). -/
def detCPAAdversary : OracleDistinguisher :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let c₁ ← List.take n <$> ProbOracleComp.query ((), encPair encBits encBits (m0, m1))
    let c₂ ← List.take n <$> ProbOracleComp.query ((), encPair encBits encBits (m0, m0))
    return (c₁ == c₂)

/-- `detCPAAdversary` is uniformly strict oracle-PPT (`IsOraclePPT encBool`). -/
theorem isOraclePPT_detCPAAdversary : IsOraclePPT encBool detCPAAdversary := by
  have hq1 : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        encPair encBits encBits (List.replicate p.1 false, List.replicate p.1 true))
      (encPair encUnary encBits) encBits := by
    polytime
  have hlim1 : ComputableInPolyTime
      (fun p : ℕ × List Bool => p.1) (encPair encUnary encBits) encUnary := by
    fun_prop
  have hq2 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        encPair encBits encBits (List.replicate p.1.1 false, List.replicate p.1.1 false))
      (encPair (encPair encUnary encBits) encBits) encBits := by
    polytime
  have hlim2 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => p.1.1)
      (encPair (encPair encUnary encBits) encBits) encUnary := by
    fun_prop
  have hout : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × List Bool => p.1.2 == p.2)
      (encPair (encPair (encPair encUnary encBits) encBits) encBits) encBool := by
    polytime
  unfold detCPAAdversary
  exact ((IsOraclePPTOn.query_take' () hq1 hlim1).bind_with
    ((IsOraclePPTOn.query_take' () hq2 hlim2).bind_with
      hout.isOraclePPTOn)).isOraclePPT

/-- In Experiment `false`, `detCPAAdversary` receives two encryptions of `0^n`; when all supported
ciphertexts of `n`-bit plaintexts have length `n`, both encryptions return the same ciphertext and
`detCPAAdversary` outputs `true` with probability `1`. -/
theorem eval_cpaGame_detCPAAdversary_false (E : SymmetricCipher) (n : ℕ)
    (hctLen : ∀ ke ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg : List Bool, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n) :
    ProbComp.eval (E.cpaGame detCPAAdversary false n) = PMF.pure true := by
  simp only [cpaGame, detCPAAdversary, OracleComp.interpret_bind, OracleComp.interpret_map,
    OracleComp.interpret_pure, ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map,
    StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  have hpair1 : unframe (encPair encBits encBits (List.replicate n false, List.replicate n true)) =
      List.replicate n false ∧
      dropFrame (encPair encBits encBits (List.replicate n false, List.replicate n true)) =
      List.replicate n true := by
    simp [encPair_apply, unframe_frame_append, dropFrame_frame_append]
  have hpair2 : unframe (encPair encBits encBits (List.replicate n false, List.replicate n false)) =
      List.replicate n false ∧
      dropFrame (encPair encBits encBits (List.replicate n false, List.replicate n false)) =
      List.replicate n false := by
    simp [encPair_apply, unframe_frame_append, dropFrame_frame_append]
  trans (ProbComp.eval (E.keyGen n)).bind (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
    unfold cpaEncryptionOracle
    dsimp only [StateT.run]
    simp only [hpair1.1, hpair1.2, hpair2.1, hpair2.2, List.length_replicate, beq_self_eq_true,
      Bool.and_self, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    trans (ProbComp.eval (E.encrypt n ke (List.replicate n false))).bind (fun _ => PMF.pure true)
    · refine PMF.bind_congr_on_support _ _ _ fun c₁ hc₁ => ?_
      trans (ProbComp.eval (E.encrypt n ke (List.replicate n false))).bind (fun _ => PMF.pure true)
      · refine PMF.bind_congr_on_support _ _ _ fun c₂ hc₂ => ?_
        have heq : c₁ = c₂ :=
          E.encrypt_eq_of_ciphertext_length_eq hke (hctLen ke hke) (List.length_replicate) hc₁ hc₂
        simp [heq]
      · exact PMF.bind_const _ _
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- In Experiment `true` for `n ≥ 1`, `detCPAAdversary` receives an encryption of `1^n` followed by
an encryption of `0^n`; by decryption completeness the two ciphertexts are distinct, so
`detCPAAdversary` outputs `false` with probability `1`. -/
theorem eval_cpaGame_detCPAAdversary_true (E : SymmetricCipher) {n : ℕ} (hn : 1 ≤ n)
    (hctLen : ∀ ke ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg : List Bool, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n) :
    ProbComp.eval (E.cpaGame detCPAAdversary true n) = PMF.pure false := by
  simp only [cpaGame, detCPAAdversary, OracleComp.interpret_bind, OracleComp.interpret_map,
    OracleComp.interpret_pure, ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map,
    StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  have hpair1 : unframe (encPair encBits encBits (List.replicate n false, List.replicate n true)) =
      List.replicate n false ∧
      dropFrame (encPair encBits encBits (List.replicate n false, List.replicate n true)) =
      List.replicate n true := by
    simp [encPair_apply, unframe_frame_append, dropFrame_frame_append]
  have hpair2 : unframe (encPair encBits encBits (List.replicate n false, List.replicate n false)) =
      List.replicate n false ∧
      dropFrame (encPair encBits encBits (List.replicate n false, List.replicate n false)) =
      List.replicate n false := by
    simp [encPair_apply, unframe_frame_append, dropFrame_frame_append]
  have hneMsg : List.replicate n true ≠ List.replicate n false := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
    simp
  trans (ProbComp.eval (E.keyGen n)).bind (fun _ => PMF.pure false)
  · refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
    unfold cpaEncryptionOracle
    dsimp only [StateT.run]
    simp only [hpair1.1, hpair1.2, hpair2.1, hpair2.2, List.length_replicate, beq_self_eq_true,
      Bool.and_self, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    trans (ProbComp.eval (E.encrypt n ke (List.replicate n true))).bind (fun _ => PMF.pure false)
    · refine PMF.bind_congr_on_support _ _ _ fun c₁ hc₁ => ?_
      have hc₁Len : c₁.length = n :=
        hctLen ke hke (List.replicate n true) (List.length_replicate) c₁ hc₁
      trans (ProbComp.eval (E.encrypt n ke (List.replicate n false))).bind (fun _ => PMF.pure false)
      · refine PMF.bind_congr_on_support _ _ _ fun c₂ hc₂ => ?_
        have hc₂Len : c₂.length = n :=
          hctLen ke hke (List.replicate n false) (List.length_replicate) c₂ hc₂
        have hne : c₁ ≠ c₂ := by
          intro hEq
          have hdec1 := E.decrypt_encrypt n ke hke (List.replicate n true)
            (List.length_replicate) c₁ hc₁
          have hdec2 := E.decrypt_encrypt n ke hke (List.replicate n false)
            (List.length_replicate) c₂ hc₂
          rw [hEq, hdec2] at hdec1
          exact hneMsg (Option.some.inj hdec1).symm
        rw [List.take_of_length_le hc₁Len.le, List.take_of_length_le hc₂Len.le]
        simp [beq_eq_false_iff_ne.mpr hne]
      · exact PMF.bind_const _ _
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- At every security parameter `n ≥ 1` where supported ciphertexts of `n`-bit plaintexts have
length `n`, `detCPAAdversary` achieves CPA advantage `1` ([BonehShoup2023], Example 5.1). -/
theorem advantage_cpaGame_detCPAAdversary (E : SymmetricCipher) {n : ℕ} (hn : 1 ≤ n)
    (hctLen : ∀ ke ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg : List Bool, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n) :
    Game.advantage (ProbComp.eval (E.cpaGame detCPAAdversary false n))
      (ProbComp.eval (E.cpaGame detCPAAdversary true n)) = 1 := by
  rw [eval_cpaGame_detCPAAdversary_false E n hctLen,
    eval_cpaGame_detCPAAdversary_true E hn hctLen, Game.advantage]
  simp [Game.succProbability]

/-- **No zero-expansion symmetric cipher is CPA-secure** ([BonehShoup2023], Example 5.1 and
Exercise 5.10(a), printed pp. 182, 211): if for every security parameter `n`, every supported key
`ke`, and every `n`-bit message `msg`, every supported ciphertext of `msg` has length `n`, then `E`
cannot satisfy `INDCPA`. -/
theorem not_indcpa_of_ciphertext_length_eq (E : SymmetricCipher)
    (hctLen : ∀ n, ∀ ke ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg : List Bool, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n) :
    ¬ E.INDCPA := by
  intro hcpa
  have hneg := hcpa detCPAAdversary isOraclePPT_detCPAAdversary
  have hcomp : Negligible (fun n =>
      Game.advantage (ProbComp.eval (E.cpaGame detCPAAdversary false (n + 1)))
        (ProbComp.eval (E.cpaGame detCPAAdversary true (n + 1)))) :=
    hneg.comp_of_polynomial_bound (bound := fun m => m) (Filter.tendsto_add_atTop_nat 1)
      (by fun_prop) (Filter.Eventually.of_forall fun n => by lia)
  have hcongr : Negligible (fun _ : ℕ => (1 : ℝ≥0)) :=
    hcomp.congr fun n => advantage_cpaGame_detCPAAdversary E (by lia) (hctLen (n + 1))
  exact not_negligible_const one_ne_zero hcongr

/-! ### Ciphertext Integrity and Authenticated Encryption (`ciGame`, `CiphertextIntegrity`,
`AuthenticatedEncryption`) -/

/-- Stateful encryption oracle for the ciphertext-integrity game ([BonehShoup2023], Section 9.1,
Attack Game 9.1): if `request.2.length == n`, encrypt `request.2` under `k`, prepend the resulting
ciphertext to `queriedCiphertexts`, and return it; otherwise return `[]` without modifying the
ciphertext log. -/
noncomputable def ciEncryptionOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.2.length == n then do
      let ct ← E.encrypt n k request.2
      return (ct, ct :: queriedCiphertexts)
    else
      return ([], queriedCiphertexts)

/-- The ciphertext-integrity experiment ([BonehShoup2023], Section 9.1, Attack Game 9.1):
sample `k ← E.keyGen n`, run `adversary n []` with oracle access to `E.ciEncryptionOracle n k`, and
accept when the adversary outputs a candidate ciphertext `ct` that was never returned by the
encryption oracle (`!out.2.contains out.1`) and decrypts without rejection
(`(E.decrypt n k out.1).isSome`). -/
noncomputable def ciGame (E : SymmetricCipher) (adversary : CIAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ciEncryptionOracle n k)) (adversary n [])).run []
  return !out.2.contains out.1 && (E.decrypt n k out.1).isSome

/-- Running an oracle-PPT CI adversary against `ciEncryptionOracle` is uniformly strict PPT in
`(n, k)`. -/
@[program_certificate]
theorem isPPTOn_run_ciEncryptionOracle (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.ciEncryptionOracle caller.1 caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  have hcond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        p.2.1.2.length == p.1.1)
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hyes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 p.2.1.2
        return (ct, ct :: p.2.2)) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((by dsimp only [EIn]; polytime : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × List (List Bool))) × List Bool =>
          (q.2, q.2 :: q.1.2.2))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        E.ciEncryptionOracle pair.1.1 pair.1.2 pair.2.1 pair.2.2) := by
    unfold ciEncryptionOracle
    exact IsPPTOn.cond hcond hyes hno
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      2 * (c * (2 * caller.1 + 2 * caller.2.length + query.length + 4) ^ d) + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by polytime)
  intro caller request queried _ result hresult
  unfold ciEncryptionOracle at hresult
  split_ifs at hresult with hlenEq
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨ct, hct, rfl⟩ := hresult
    have hctLen := hlen (caller.1, caller.2, request.2) ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hctLen
    have hbound : ct.length ≤ c * (2 * caller.1 + 2 * caller.2.length + request.2.length + 4) ^ d :=
      hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- The ciphertext-integrity experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ciGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn encUnary encBool (E.ciGame adversary) := by
  have hrun := E.isPPTOn_run_ciEncryptionOracle hadversary
  let EOut := encPair (encPair encUnary encBits) (encPair encBits (encList encBits))
  have hcontains : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        pair.2.2.contains pair.2.1)
      EOut encBool := by
    have hlist : ComputableTidilyInPolyTime
        (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) => pair.2.2)
        EOut (encList encBits) := by dsimp only [EOut]; fun_prop
    have helem : ComputableTidilyInPolyTime
        (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) => pair.2.1)
        EOut encBits := by dsimp only [EOut]; fun_prop
    classical
    convert ComputableTidilyInPolyTime.decide_mem hlist helem using 1
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_eq]
  have hdecArg : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (pair.1.1, pair.1.2, pair.2.1))
      EOut (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EOut]; fun_prop
  have hdec : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome)
      EOut encBool :=
    (E.decrypt_polyTime.tidy.comp hdecArg).optionIsSome
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        !pair.2.2.contains pair.2.1 && (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome)
      EOut encBool := by
    dsimp only [EOut]; polytime
  unfold ciGame
  exact E.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The ciphertext-integrity experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_ciGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPT encBool (fun n _ => E.ciGame adversary n) :=
  ((E.isPPTOn_ciGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Ciphertext integrity (`CiphertextIntegrity`, or CI) for a symmetric cipher
([BonehShoup2023], Section 9.1, Attack Game 9.1 and Definition 9.1): every uniform strict
`IsOraclePPT encBits` adversary has negligible probability of outputting a fresh valid
ciphertext. -/
def CiphertextIntegrity (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ciGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encBits)

/-- Ciphertext integrity gives negligible winning probability in `ciGame` for every oracle-PPT CI
adversary. -/
theorem CiphertextIntegrity.negligible {E : SymmetricCipher} (h : E.CiphertextIntegrity)
    (adversary : CIAdversary) (hadversary : IsOraclePPT encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish `CiphertextIntegrity` by bounding every oracle-PPT CI adversary's winning
probability. -/
theorem CiphertextIntegrity.of_negligible {E : SymmetricCipher}
    (h : ∀ adversary, IsOraclePPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciGame adversary n)))) :
    E.CiphertextIntegrity := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Authenticated encryption (`AuthenticatedEncryption`, or AE-security) for a symmetric cipher
([BonehShoup2023], Section 9.1, Definition 9.2): the cipher satisfies both `INDCPA` and
`CiphertextIntegrity`. -/
def AuthenticatedEncryption (E : SymmetricCipher) : Prop :=
  E.INDCPA ∧ E.CiphertextIntegrity

/-- Stateful one-time encryption oracle for the one-time ciphertext-integrity game
([BonehShoup2023], Section 9.1.1, Definition 9.3, printed p. 360): if no ciphertext has been
returned yet (`queriedCiphertexts.isEmpty`) and `request.2.length == n`, encrypt `request.2` under
`k`, record `[ct]`, and return `ct`; otherwise return `[]` without modifying
`queriedCiphertexts`. -/
noncomputable def oneTimeCIEncryptionOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if queriedCiphertexts.isEmpty && (request.2.length == n) then do
      let ct ← E.encrypt n k request.2
      return (ct, [ct])
    else
      return ([], queriedCiphertexts)

/-- The one-time ciphertext-integrity experiment ([BonehShoup2023], Section 9.1.1,
Definition 9.3, printed p. 360): sample `k ← E.keyGen n`, run `adversary n []` with oracle access
to `E.oneTimeCIEncryptionOracle n k`, and accept when the adversary outputs a candidate ciphertext
`ct` that was not returned by the encryption oracle (`!out.2.contains out.1`) and decrypts without
rejection (`(E.decrypt n k out.1).isSome`). -/
noncomputable def ciOneTimeGame (E : SymmetricCipher) (adversary : CIAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.oneTimeCIEncryptionOracle n k)) (adversary n [])).run []
  return !out.2.contains out.1 && (E.decrypt n k out.1).isSome

/-- Running an oracle-PPT CI adversary against `oneTimeCIEncryptionOracle` is uniformly strict PPT
in `(n, k)`. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeCIEncryptionOracle (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.oneTimeCIEncryptionOracle caller.1 caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  have hcond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        p.2.2.isEmpty && (p.2.1.2.length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hyes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 p.2.1.2
        return (ct, [ct])) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((by dsimp only [EIn]; polytime : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × List (List Bool))) × List Bool =>
          (q.2, [q.2]))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        E.oneTimeCIEncryptionOracle pair.1.1 pair.1.2 pair.2.1 pair.2.2) := by
    unfold oneTimeCIEncryptionOracle
    exact IsPPTOn.cond hcond hyes hno
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      2 * (c * (2 * caller.1 + 2 * caller.2.length + query.length + 4) ^ d) + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by polytime)
  intro caller request queried _ result hresult
  unfold oneTimeCIEncryptionOracle at hresult
  split_ifs at hresult with hlenEq
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨ct, hct, rfl⟩ := hresult
    have hctLen := hlen (caller.1, caller.2, request.2) ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hctLen
    have hbound : ct.length ≤ c * (2 * caller.1 + 2 * caller.2.length + request.2.length + 4) ^ d :=
      hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, encList_nil, List.length_append, List.length_nil, length_frame,
      encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- The one-time ciphertext-integrity experiment is uniformly strict PPT in the unary security
parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ciOneTimeGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn encUnary encBool (E.ciOneTimeGame adversary) := by
  have hrun := E.isPPTOn_run_oneTimeCIEncryptionOracle hadversary
  let EOut := encPair (encPair encUnary encBits) (encPair encBits (encList encBits))
  have hcontains : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        pair.2.2.contains pair.2.1)
      EOut encBool := by
    have hlist : ComputableTidilyInPolyTime
        (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) => pair.2.2)
        EOut (encList encBits) := by dsimp only [EOut]; fun_prop
    have helem : ComputableTidilyInPolyTime
        (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) => pair.2.1)
        EOut encBits := by dsimp only [EOut]; fun_prop
    classical
    convert ComputableTidilyInPolyTime.decide_mem hlist helem using 1
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_eq]
  have hdecArg : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (pair.1.1, pair.1.2, pair.2.1))
      EOut (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EOut]; fun_prop
  have hdec : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome)
      EOut encBool :=
    (E.decrypt_polyTime.tidy.comp hdecArg).optionIsSome
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        !pair.2.2.contains pair.2.1 && (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome)
      EOut encBool := by
    dsimp only [EOut]; polytime
  unfold ciOneTimeGame
  exact E.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The one-time ciphertext-integrity experiment is uniformly strict PPT, independently of unused
auxiliary input. -/
@[program_certificate]
theorem isPPT_ciOneTimeGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPT encBool (fun n _ => E.ciOneTimeGame adversary n) :=
  ((E.isPPTOn_ciOneTimeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- One-time ciphertext integrity (`OneTimeCiphertextIntegrity`, or 1CI) for a symmetric cipher
([BonehShoup2023], Section 9.1.1, Definition 9.3, printed p. 360): every uniform strict
`IsOraclePPT encBits` adversary has negligible probability of outputting a fresh valid ciphertext
in `ciOneTimeGame`. -/
def OneTimeCiphertextIntegrity (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ciOneTimeGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encBits)

/-- One-time ciphertext integrity gives negligible winning probability in `ciOneTimeGame` for every
oracle-PPT CI adversary. -/
theorem OneTimeCiphertextIntegrity.negligible {E : SymmetricCipher}
    (h : E.OneTimeCiphertextIntegrity) (adversary : CIAdversary)
    (hadversary : IsOraclePPT encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciOneTimeGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish `OneTimeCiphertextIntegrity` by bounding every oracle-PPT CI adversary's winning
probability in `ciOneTimeGame`. -/
theorem OneTimeCiphertextIntegrity.of_negligible {E : SymmetricCipher}
    (h : ∀ adversary, IsOraclePPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciOneTimeGame adversary n)))) :
    E.OneTimeCiphertextIntegrity := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Stateful filter handler that forwards at most one valid `n`-bit CI encryption query to an
external multi-query CI encryption oracle (truncating replies to `ctBound`). -/
noncomputable def ciOneTimeFilterHandler (n ctBound : ℕ) (request : Unit × List Bool) :
    StateT Bool (WordOracleComp Unit) (List Bool) :=
  fun alreadyQueried =>
    if !alreadyQueried && (request.2.length == n) then
      (fun ct => (ct, true)) <$> (List.take ctBound <$> ProbOracleComp.query ((), request.2))
    else
      pure ([], alreadyQueried)

/-- Reduction from `ciOneTimeGame` to `ciGame`: run `adversary n []` against
`ciOneTimeFilterHandler n (ctBound n)` starting from `alreadyQueried = false`. -/
noncomputable def ciLimitToOneQuery (ctBound : ℕ → ℕ) (adversary : CIAdversary) : CIAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ciOneTimeFilterHandler n (ctBound n)))
      (adversary n [])).run false
    return out.1

/-- `ciLimitToOneQuery` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ciLimitToOneQuery {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBits (ciLimitToOneQuery ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        !p.2.2 && (p.2.1.2.length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hlimit : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => ctBound p.1.1)
      EIn encUnary :=
    hctBound.comp (by dsimp only [EIn]; fun_prop)
  have hquery : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        (fun ct => (ct, true)) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query ((), p.2.1.2))) :=
    (IsOraclePPTOn.query_take' () (by dsimp only [EIn]; fun_prop) hlimit).map'
      (ComputableInPolyTime.prod (by fun_prop) (ComputableInPolyTime.const true))
  have hnoReply : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        ciOneTimeFilterHandler pair.1.1 (ctBound pair.1.1) pair.2.1 pair.2.2) := by
    unfold ciOneTimeFilterHandler
    exact IsOraclePPTOn.cond' hcond hquery hnoReply
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add' (hctBound.comp (by fun_prop)) (ComputableInPolyTime.const 1)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBits encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ciOneTimeFilterHandler caller.1 (ctBound caller.1)))
          (adversary caller.1 [])).run false) := by
    apply hadversary.run_interpret_preprocess_open'
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => false)
      (resources := fun caller _ => ctBound caller.1 + 1)
      (by fun_prop) hhandler (ComputableInPolyTime.const false)
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request alreadyQueried _ result hresult
    unfold ciOneTimeFilterHandler at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨ct, hct, rfl⟩ := ProbOracleComp.mem_support_map hresult
      obtain ⟨rawCt, _, rfl⟩ := ProbOracleComp.mem_support_map hct
      exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by simp [encBool_apply]⟩
    · cases ProbOracleComp.eq_of_mem_support_pure hresult
      exact ⟨trivial, by simp, by simp [encBool_apply]⟩
  unfold ciLimitToOneQuery
  simpa only [bind_pure_comp] using (hrun.map' (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ciLimitToOneQuery ctBound adversary` in `ciGame` has the exact same output distribution as
`ciOneTimeGame adversary`. -/
theorem eval_ciGame_ciLimitToOneQuery (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CIAdversary) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.ciGame (ciLimitToOneQuery ctBound adversary) n) =
      ProbComp.eval (E.ciOneTimeGame adversary n) := by
  simp only [ciGame, ciOneTimeGame, ciLimitToOneQuery, ProbComp.eval_bind, ProbComp.eval_pure]
  apply PMF.bind_congr_on_support
  intro k hk
  simp only [ProbOracleComp.eval_run_interpret]
  rw [OracleComp.interpret_bind, StateT.run_bind]
  simp only [StateT.run_pure, OracleComp.interpret_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.run_interpret_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (fun request queried =>
      ProbComp.eval (E.oneTimeCIEncryptionOracle n k request queried))
    (fun request state =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
        ((ciOneTimeFilterHandler n (ctBound n) request).run state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun queried : List (List Bool) => (!queried.isEmpty, queried))
    (fun request queried => by
      change (ProbComp.eval (E.oneTimeCIEncryptionOracle n k request queried)).map
          (fun x => (x.1, !x.2.isEmpty, x.2)) =
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
          (ciOneTimeFilterHandler n (ctBound n) request (!queried.isEmpty))).run queried).map
          (fun result => (result.1.1, result.1.2, result.2))
      simp only [oneTimeCIEncryptionOracle, ciOneTimeFilterHandler, Bool.not_not]
      by_cases hcond : (queried.isEmpty && (request.2.length == n)) = true
      · simp only [hcond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
          Functor.map_map, OracleComp.interpret_map, StateT.run_map,
          ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map, ciEncryptionOracle]
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hcond
        rcases hcond with ⟨rfl, hmsgLen⟩
        have hlenEq : (request.2.length == n) = true := beq_iff_eq.mpr hmsgLen
        dsimp only [StateT.run]
        simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
          PMF.map_bind, PMF.pure_map, List.isEmpty_cons, Bool.not_false]
        apply PMF.bind_congr_on_support
        intro ct hct
        rw [List.take_of_length_le (hctBound k hk _ hmsgLen ct hct)]
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
          OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
          PMF.pure_map])
    (adversary n []) []
  dsimp only [List.isEmpty, not] at hsim
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

/-- Multi-query `CiphertextIntegrity` implies `OneTimeCiphertextIntegrity`. -/
theorem CiphertextIntegrity.oneTimeCiphertextIntegrity {E : SymmetricCipher}
    (hci : E.CiphertextIntegrity) : E.OneTimeCiphertextIntegrity := by
  apply OneTimeCiphertextIntegrity.of_negligible
  intro adversary hadversary
  obtain ⟨ck, dk, hlenKey⟩ := E.keyGen_ppt.length_le
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  let ctBound : ℕ → ℕ := fun n => ce * (3 * n + 2 * (ck * (n + 1) ^ dk) + 4) ^ de
  have hctBoundPoly : ComputableInPolyTime ctBound encUnary encUnary := by
    dsimp only [ctBound]; polytime
  have hctBound (n : ℕ) (k : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
      (msg : List Bool) (hmsg : msg.length = n) (ct : List Bool)
      (hct : ct ∈ (ProbComp.eval (E.encrypt n k msg)).support) : ct.length ≤ ctBound n := by
    have hkLen := hlenKey n k hk
    have hctLen := hlenEnc (n, k, msg) ct hct
    simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkLen
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmsg] at hctLen
    exact hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
  have hneg := hci.negligible (ciLimitToOneQuery ctBound adversary)
    (isOraclePPT_ciLimitToOneQuery hctBoundPoly hadversary)
  refine hneg.congr fun n => ?_
  rw [eval_ciGame_ciLimitToOneQuery E ctBound adversary n (hctBound n)]

/-- One-time authenticated encryption (`OneTimeAuthenticatedEncryption`, or `1AE`-security) for a
symmetric cipher ([BonehShoup2023], Section 9.1.1, Definition 9.4, printed p. 360): the cipher
satisfies both `OneTimeINDCPA` (semantic security under a single encryption query) and
`OneTimeCiphertextIntegrity`. -/
def OneTimeAuthenticatedEncryption (E : SymmetricCipher) : Prop :=
  E.OneTimeINDCPA ∧ E.OneTimeCiphertextIntegrity

/-- Multi-query `AuthenticatedEncryption` implies `OneTimeAuthenticatedEncryption`. -/
theorem AuthenticatedEncryption.oneTimeAuthenticatedEncryption {E : SymmetricCipher}
    (h : E.AuthenticatedEncryption) : E.OneTimeAuthenticatedEncryption :=
  ⟨h.1.oneTimeINDCPA, h.2.oneTimeCiphertextIntegrity⟩

/-! ### Adaptive Chosen-Ciphertext Security (`ccaGame`, `ccaRejectGame`, `INDCCA`) -/

/-- Stateful two-channel oracle for the adaptive chosen-ciphertext experiment
([BonehShoup2023], Section 9.2.2, Attack Game 9.2):
* On an encryption query `(false, req)`: decode `m0 = unframe req` and `m1 = dropFrame req`; if
  both have length `n`, encrypt `if bit then m1 else m0` under `k`, prepend the resulting
  ciphertext `ct` to `queriedCiphertexts`, and return `ct`; otherwise return `[]`.
* On a decryption query `(true, ct)`: if `queriedCiphertexts.contains ct` is `true`, return `[]`
  (prohibited challenge ciphertext); otherwise return `encOption encBits (E.decrypt n k ct)`. -/
noncomputable def ccaOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      if queriedCiphertexts.contains request.2 then
        return ([], queriedCiphertexts)
      else
        return (encOption encBits (E.decrypt n k request.2), queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ct :: queriedCiphertexts)
      else
        return ([], queriedCiphertexts)

/-- The adaptive chosen-ciphertext experiment ([BonehShoup2023], Section 9.2.2, Attack Game 9.2):
sample `k ← E.keyGen n` and run `adversary n []` against `E.ccaOracle n k bit`. -/
noncomputable def ccaGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ccaOracle n k bit)) (adversary n [])).run []
  return out.1

/-- Running an oracle-PPT CCA adversary against `ccaOracle` is uniformly strict PPT in `(n, k)` for
each challenge bit `bit`. -/
@[program_certificate]
theorem isPPTOn_run_ccaOracle (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.ccaOracle caller.1 caller.2 bit)) (adversary caller.1 [])).run []) := by
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  obtain ⟨cd, dd, hlenDec⟩ := E.decrypt_polyTime.tidy.polyBounded_length.exists_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Bool) encBits) (encList encBits))
  have hop : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.1.1)
      EIn encBool :=
    (ComputableTidilyInPolyTime.of_finite id).comp (by dsimp only [EIn]; fun_prop)
  have hcontains : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        p.2.2.contains p.2.1.2)
      EIn encBool := by
    have hlist : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.2)
        EIn (encList encBits) := by dsimp only [EIn]; fun_prop
    have helem : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.1.2)
        EIn encBits := by dsimp only [EIn]; fun_prop
    classical
    convert ComputableTidilyInPolyTime.decide_mem hlist helem using 1
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_eq]
  have hdecArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hdecWord : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        encOption encBits (E.decrypt p.1.1 p.1.2 p.2.1.2))
      EIn encBits :=
    (ComputableTidilyInPolyTime.encode (encOption encBits)).comp
      (E.decrypt_polyTime.tidy.comp hdecArg)
  have hnoReply : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hdecBranch : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if p.2.2.contains p.2.1.2 then
          pure ([], p.2.2)
        else
          pure (encOption encBits (E.decrypt p.1.1 p.1.2 p.2.1.2), p.2.2)) :=
    IsPPTOn.cond hcontains hnoReply
      ((ComputableTidilyInPolyTime.prod hdecWord (by dsimp only [EIn]; fun_prop)).isPPTOn)
  have hm0 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => unframe p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [EIn]; fun_prop)
  have hm1 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => dropFrame p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [EIn]; fun_prop)
  have hencCond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hmsg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, if bit then dropFrame p.2.1.2 else unframe p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop)
      (ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop) hmsg)
  have hencYes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
        return (ct, ct :: p.2.2)) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((by dsimp only [EIn]; polytime : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × ((Bool × List Bool) × List (List Bool))) × List Bool =>
          (q.2, q.2 :: q.1.2.2))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hencBranch : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1) then do
          let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
          return (ct, ct :: p.2.2)
        else
          pure ([], p.2.2)) :=
    IsPPTOn.cond hencCond hencYes hnoReply
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        E.ccaOracle pair.1.1 pair.1.2 bit pair.2.1 pair.2.2) := by
    unfold ccaOracle
    exact IsPPTOn.cond hop hdecBranch hencBranch
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      2 * (ce * (3 * caller.1 + 2 * caller.2.length + 4) ^ de) +
      cd * (2 * caller.1 + 2 * caller.2.length + query.length + 4) ^ dd + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by polytime)
  intro caller request queried _ result hresult
  unfold ccaOracle at hresult
  cases hreq : request.1
  · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
    by_cases hlenEq : ((unframe request.2).length == caller.1 &&
        (dropFrame request.2).length == caller.1) = true
    · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
      obtain ⟨ct, hct, rfl⟩ := hresult
      simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
      have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = caller.1 := by
        cases bit <;> simp [hlenEq]
      have hctLen := hlenEnc
        (caller.1, caller.2, if bit then dropFrame request.2 else unframe request.2) ct hct
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
        hmbLen] at hctLen
      have hbound : ct.length ≤ ce * (3 * caller.1 + 2 * caller.2.length + 4) ^ de :=
        hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
      refine ⟨trivial, by lia, ?_⟩
      simp only [encList_cons, List.length_append, length_frame, encBits_apply]
      lia
    · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨trivial, by simp, by lia⟩
  · simp only [hreq, ↓reduceIte] at hresult
    split_ifs at hresult with hmem
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨trivial, by simp, by lia⟩
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      have hdecLen := hlenDec (caller.1, caller.2, request.2)
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hdecLen
      have hbound : (encOption encBits (E.decrypt caller.1 caller.2 request.2)).length ≤
          cd * (2 * caller.1 + 2 * caller.2.length + request.2.length + 4) ^ dd :=
        hdecLen.trans (Nat.mul_le_mul_left cd (Nat.pow_le_pow_left (by lia) dd))
      exact ⟨trivial, by lia, by lia⟩

/-- The adaptive CCA experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ccaGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.ccaGame adversary bit) := by
  have hrun := E.isPPTOn_run_ccaOracle hadversary bit
  unfold ccaGame
  exact E.keyGen_ppt.bind_with (hrun.bind (ComputableTidilyInPolyTime.fst _ _).isPPTOn)

/-- The adaptive CCA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_ccaGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.ccaGame adversary bit n) :=
  ((E.isPPTOn_ccaGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Adaptive chosen-ciphertext security (`INDCCA`, or CCA-security) for a symmetric cipher
([BonehShoup2023], Section 9.2.2, Attack Game 9.2 and Definition 9.5, printed p. 362): every
uniform strict `IsOraclePPT encBool` CCA adversary has negligible advantage between
`E.ccaGame adversary false` and `E.ccaGame adversary true`.

In [BonehShoup2023], Section 9.2.2, Definition 9.5 defines adaptive multi-query CCA security,
whereas one-time CCA security (`OneTimeINDCCA`, or `1CCA`) is defined in Definition 9.6
(printed p. 363). -/
def INDCCA (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ccaGame adversary false n))
    (fun adversary n => ProbComp.eval (E.ccaGame adversary true n))
    (IsOraclePPT encBool)

/-- Stateful two-channel oracle for the one-time adaptive chosen-ciphertext experiment
([BonehShoup2023], Section 9.2.2, Attack Game 9.2 and Definition 9.6, printed pp. 362–363):
* On an encryption query `(false, req)`: decode `m0 = unframe req` and `m1 = dropFrame req`; if
  no challenge ciphertext has been returned yet (`queriedCiphertexts.isEmpty`) and both messages
  have length `n`, encrypt `if bit then m1 else m0` under `k`, record `[ct]`, and return `ct`;
  otherwise return `[]`.
* On a decryption query `(true, ct)`: if `queriedCiphertexts.contains ct` is `true`, return `[]`
  (prohibited challenge ciphertext); otherwise return `encOption encBits (E.decrypt n k ct)`. -/
noncomputable def oneTimeCCAOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      if queriedCiphertexts.contains request.2 then
        return ([], queriedCiphertexts)
      else
        return (encOption encBits (E.decrypt n k request.2), queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if queriedCiphertexts.isEmpty && (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, [ct])
      else
        return ([], queriedCiphertexts)

/-- The one-time adaptive chosen-ciphertext experiment ([BonehShoup2023], Section 9.2.2,
Attack Game 9.2 and Definition 9.6, printed pp. 362–363): sample `k ← E.keyGen n` and run
`adversary n []` against `E.oneTimeCCAOracle n k bit`. -/
noncomputable def ccaOneTimeGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.oneTimeCCAOracle n k bit)) (adversary n [])).run []
  return out.1

/-- Running an oracle-PPT CCA adversary against `oneTimeCCAOracle` is uniformly strict PPT in
`(n, k)` for each challenge bit `bit`. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeCCAOracle (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.oneTimeCCAOracle caller.1 caller.2 bit)) (adversary caller.1 [])).run []) := by
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  obtain ⟨cd, dd, hlenDec⟩ := E.decrypt_polyTime.tidy.polyBounded_length.exists_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Bool) encBits) (encList encBits))
  have hop : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.1.1)
      EIn encBool :=
    (ComputableTidilyInPolyTime.of_finite id).comp (by dsimp only [EIn]; fun_prop)
  have hcontains : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        p.2.2.contains p.2.1.2)
      EIn encBool := by
    have hlist : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.2)
        EIn (encList encBits) := by dsimp only [EIn]; fun_prop
    have helem : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.1.2)
        EIn encBits := by dsimp only [EIn]; fun_prop
    classical
    convert ComputableTidilyInPolyTime.decide_mem hlist helem using 1
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_eq]
  have hdecArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hdecWord : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        encOption encBits (E.decrypt p.1.1 p.1.2 p.2.1.2))
      EIn encBits :=
    (ComputableTidilyInPolyTime.encode (encOption encBits)).comp
      (E.decrypt_polyTime.tidy.comp hdecArg)
  have hnoReply : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hdecBranch : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if p.2.2.contains p.2.1.2 then
          pure ([], p.2.2)
        else
          pure (encOption encBits (E.decrypt p.1.1 p.1.2 p.2.1.2), p.2.2)) :=
    IsPPTOn.cond hcontains hnoReply
      ((ComputableTidilyInPolyTime.prod hdecWord (by dsimp only [EIn]; fun_prop)).isPPTOn)
  have hm0 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => unframe p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [EIn]; fun_prop)
  have hm1 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => dropFrame p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [EIn]; fun_prop)
  have hencCond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        p.2.2.isEmpty && ((unframe p.2.1.2).length == p.1.1) &&
          ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hmsg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, if bit then dropFrame p.2.1.2 else unframe p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop)
      (ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop) hmsg)
  have hencYes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
        return (ct, [ct])) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((by dsimp only [EIn]; polytime : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × ((Bool × List Bool) × List (List Bool))) × List Bool =>
          (q.2, [q.2]))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hencBranch : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if p.2.2.isEmpty && ((unframe p.2.1.2).length == p.1.1) &&
            ((dropFrame p.2.1.2).length == p.1.1) then do
          let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
          return (ct, [ct])
        else
          pure ([], p.2.2)) :=
    IsPPTOn.cond hencCond hencYes hnoReply
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        E.oneTimeCCAOracle pair.1.1 pair.1.2 bit pair.2.1 pair.2.2) := by
    unfold oneTimeCCAOracle
    exact IsPPTOn.cond hop hdecBranch hencBranch
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      2 * (ce * (3 * caller.1 + 2 * caller.2.length + 4) ^ de) +
      cd * (2 * caller.1 + 2 * caller.2.length + query.length + 4) ^ dd + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by polytime)
  intro caller request queried _ result hresult
  unfold oneTimeCCAOracle at hresult
  cases hreq : request.1
  · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
    by_cases hlenEq : (queried.isEmpty && ((unframe request.2).length == caller.1) &&
        ((dropFrame request.2).length == caller.1)) = true
    · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
      obtain ⟨ct, hct, rfl⟩ := hresult
      simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
      have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = caller.1 := by
        cases bit <;> simp [hlenEq]
      have hctLen := hlenEnc
        (caller.1, caller.2, if bit then dropFrame request.2 else unframe request.2) ct hct
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
        hmbLen] at hctLen
      have hbound : ct.length ≤ ce * (3 * caller.1 + 2 * caller.2.length + 4) ^ de :=
        hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
      refine ⟨trivial, by lia, ?_⟩
      simp only [encList_cons, encList_nil, List.length_append, List.length_nil, length_frame,
        encBits_apply]
      lia
    · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨trivial, by simp, by lia⟩
  · simp only [hreq, ↓reduceIte] at hresult
    split_ifs at hresult with hmem
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨trivial, by simp, by lia⟩
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      have hdecLen := hlenDec (caller.1, caller.2, request.2)
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hdecLen
      have hbound : (encOption encBits (E.decrypt caller.1 caller.2 request.2)).length ≤
          cd * (2 * caller.1 + 2 * caller.2.length + request.2.length + 4) ^ dd :=
        hdecLen.trans (Nat.mul_le_mul_left cd (Nat.pow_le_pow_left (by lia) dd))
      exact ⟨trivial, by lia, by lia⟩

/-- The one-time adaptive CCA experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ccaOneTimeGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.ccaOneTimeGame adversary bit) := by
  have hrun := E.isPPTOn_run_oneTimeCCAOracle hadversary bit
  unfold ccaOneTimeGame
  exact E.keyGen_ppt.bind_with (hrun.bind (ComputableTidilyInPolyTime.fst _ _).isPPTOn)

/-- The one-time adaptive CCA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_ccaOneTimeGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.ccaOneTimeGame adversary bit n) :=
  ((E.isPPTOn_ccaOneTimeGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- One-time adaptive chosen-ciphertext security (`OneTimeINDCCA`, or `1CCA`-security) for a
symmetric cipher ([BonehShoup2023], Section 9.2.2, Attack Game 9.2 and Definition 9.6,
printed p. 363): every uniform strict `IsOraclePPT encBool` CCA adversary has negligible advantage
between `E.ccaOneTimeGame adversary false` and `E.ccaOneTimeGame adversary true`. -/
def OneTimeINDCCA (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ccaOneTimeGame adversary false n))
    (fun adversary n => ProbComp.eval (E.ccaOneTimeGame adversary true n))
    (IsOraclePPT encBool)

/-- Stateful filter handler that forwards all decryption queries `(true, ct)` (truncating replies to
`decBound n ct`) and at most one valid `n`-bit encryption query `(false, req)` (truncating replies
to `ctBound`) to an external multi-query CCA oracle. -/
noncomputable def ccaOneTimeFilterHandler (n ctBound : ℕ) (decBound : ℕ → List Bool → ℕ)
    (request : Bool × List Bool) : StateT Bool (WordOracleComp Bool) (List Bool) :=
  fun alreadyEncrypted =>
    if request.1 then
      (fun reply => (reply, alreadyEncrypted)) <$>
        (List.take (decBound n request.2) <$> ProbOracleComp.query (true, request.2))
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if !alreadyEncrypted && (m0.length == n) && (m1.length == n) then
        (fun ct => (ct, true)) <$>
          (List.take ctBound <$> ProbOracleComp.query (false, request.2))
      else
        pure ([], alreadyEncrypted)

/-- Reduction from `ccaOneTimeGame` to `ccaGame`: run `adversary n []` against
`ccaOneTimeFilterHandler n (ctBound n) decBound` starting from `alreadyEncrypted = false`. -/
noncomputable def ccaLimitToOneEncryptionQuery (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : CCAAdversary) : CCAAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ccaOneTimeFilterHandler n (ctBound n) decBound))
      (adversary n [])).run false
    return out.1

/-- `ccaLimitToOneEncryptionQuery` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaLimitToOneEncryptionQuery {ctBound : ℕ → ℕ}
    {decBound : ℕ → List Bool → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (ccaLimitToOneEncryptionQuery ctBound decBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair encBool encBits) encBool)
  have hop : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => p.2.1.1)
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hencCond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) =>
        !p.2.2 && ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hctLimit : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => ctBound p.1.1)
      EIn encUnary :=
    hctBound.comp (by dsimp only [EIn]; fun_prop)
  have hdecArg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => (p.1.1, p.2.1.2))
      EIn (encPair encUnary encBits) := by
    dsimp only [EIn]; fun_prop
  have hdecLimit : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => decBound p.1.1 p.2.1.2)
      EIn encUnary :=
    hdecBound.comp hdecArg
  have hdecQuery : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) =>
        (fun reply => (reply, p.2.2)) <$>
          (List.take (decBound p.1.1 p.2.1.2) <$> ProbOracleComp.query (true, p.2.1.2))) :=
    (IsOraclePPTOn.query_take' true (by dsimp only [EIn]; fun_prop) hdecLimit).map_with'
      (ComputableInPolyTime.prod (by fun_prop)
        ((by dsimp only [EIn]; fun_prop : ComputableInPolyTime
          (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => p.2.2) EIn encBool).comp
          (ComputableInPolyTime.fst EIn encBits)))
  have hencQuery : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) =>
        (fun ct => (ct, true)) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query (false, p.2.1.2))) :=
    (IsOraclePPTOn.query_take' false (by dsimp only [EIn]; fun_prop) hctLimit).map'
      (ComputableInPolyTime.prod (by fun_prop) (ComputableInPolyTime.const true))
  have hnoReply : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isOraclePPTOn (Operation := Bool)
  have hhandler : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × Bool) =>
        ccaOneTimeFilterHandler pair.1.1 (ctBound pair.1.1) decBound pair.2.1 pair.2.2) := by
    unfold ccaOneTimeFilterHandler
    exact IsOraclePPTOn.cond' hop hdecQuery (IsOraclePPTOn.cond' hencCond hencQuery hnoReply)
  have hresCtArg : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => pair.1.1)
      (encPair (encPair encUnary encBits) encBits) encUnary := by
    fun_prop
  have hresDecArg : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => (pair.1.1, pair.2))
      (encPair (encPair encUnary encBits) encBits) (encPair encUnary encBits) := by
    fun_prop
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool =>
        ctBound pair.1.1 + decBound pair.1.1 pair.2 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add'
        (hctBound.comp hresCtArg)
        (hdecBound.comp hresDecArg))
      (ComputableInPolyTime.const 1)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ccaOneTimeFilterHandler caller.1 (ctBound caller.1) decBound))
          (adversary caller.1 [])).run false) := by
    apply hadversary.run_interpret_preprocess_open'
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => false)
      (resources := fun caller query => ctBound caller.1 + decBound caller.1 query + 1)
      (by fun_prop) hhandler (ComputableInPolyTime.const false)
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request alreadyEncrypted _ result hresult
    unfold ccaOneTimeFilterHandler at hresult
    cases hreq : request.1
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
      split_ifs at hresult with hlenEq
      · obtain ⟨ct, hct, rfl⟩ := ProbOracleComp.mem_support_map hresult
        obtain ⟨rawCt, _, rfl⟩ := ProbOracleComp.mem_support_map hct
        exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by simp [encBool_apply]⟩
      · cases ProbOracleComp.eq_of_mem_support_pure hresult
        exact ⟨trivial, by simp, by simp [encBool_apply]⟩
    · simp only [hreq, ↓reduceIte] at hresult
      obtain ⟨reply, hreply, rfl⟩ := ProbOracleComp.mem_support_map hresult
      obtain ⟨rawReply, _, rfl⟩ := ProbOracleComp.mem_support_map hreply
      exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by simp [encBool_apply]⟩
  unfold ccaLimitToOneEncryptionQuery
  simpa only [bind_pure_comp] using (hrun.map' (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages
and `decBound n ct` bounds all encoded decryption replies `encOption encBits (E.decrypt n k ct)`,
running `ccaLimitToOneEncryptionQuery ctBound decBound adversary` in `ccaGame` has the exact same
output distribution as `ccaOneTimeGame adversary`. -/
theorem eval_ccaGame_ccaLimitToOneEncryptionQuery (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (decBound : ℕ → List Bool → ℕ) (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    (hdecBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct) :
    ProbComp.eval (E.ccaGame (ccaLimitToOneEncryptionQuery ctBound decBound adversary) bit n) =
      ProbComp.eval (E.ccaOneTimeGame adversary bit n) := by
  simp only [ccaGame, ccaOneTimeGame, ccaLimitToOneEncryptionQuery, ProbComp.eval_bind,
    ProbComp.eval_pure]
  apply PMF.bind_congr_on_support
  intro k hk
  simp only [ProbOracleComp.eval_run_interpret]
  rw [OracleComp.interpret_bind, StateT.run_bind]
  simp only [StateT.run_pure, OracleComp.interpret_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.run_interpret_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (fun request queried =>
      ProbComp.eval (E.oneTimeCCAOracle n k bit request queried))
    (fun request state =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaOracle n k bit q s)))
        ((ccaOneTimeFilterHandler n (ctBound n) decBound request).run state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun queried : List (List Bool) => (!queried.isEmpty, queried))
    (fun request queried => by
      change (ProbComp.eval (E.oneTimeCCAOracle n k bit request queried)).map
          (fun x => (x.1, !x.2.isEmpty, x.2)) =
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ccaOracle n k bit q s)))
          (ccaOneTimeFilterHandler n (ctBound n) decBound request (!queried.isEmpty))).run
            queried).map
          (fun result => (result.1.1, result.1.2, result.2))
      cases hreq : request.1
      · simp only [oneTimeCCAOracle, ccaOneTimeFilterHandler, hreq, Bool.false_eq_true,
          ↓reduceIte, Bool.not_not]
        by_cases hcond : (queried.isEmpty && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true
        · simp only [hcond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            Functor.map_map, OracleComp.interpret_map, StateT.run_map,
            ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map, ccaOracle]
          simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hcond
          rcases hcond with ⟨⟨rfl, hm0⟩, hm1⟩
          have hlenEq : (((unframe request.2).length == n) &&
              ((dropFrame request.2).length == n)) = true := by
            simp [hm0, hm1]
          dsimp only [StateT.run]
          simp only [Bool.false_eq_true, ↓reduceIte, hlenEq, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.map_bind, PMF.pure_map, List.isEmpty_cons, Bool.not_false]
          have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
            cases bit <;> simp [hm0, hm1]
          apply PMF.bind_congr_on_support
          intro ct hct
          rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
        · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
            PMF.pure_map]
      · simp only [oneTimeCCAOracle, ccaOneTimeFilterHandler, hreq, ↓reduceIte,
          Functor.map_map, OracleComp.interpret_map, StateT.run_map,
          ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map, ccaOracle]
        dsimp only [StateT.run]
        split_ifs with hmem
        · simp only [ProbComp.eval_pure, PMF.pure_map, List.take_nil]
        · simp only [ProbComp.eval_pure, PMF.pure_map,
            List.take_of_length_le (hdecBound k hk request.2)])
    (adversary n []) []
  dsimp only [List.isEmpty, not] at hsim
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

/-- Multi-query `INDCCA` security implies one-time `OneTimeINDCCA` security. -/
theorem INDCCA.oneTimeINDCCA {E : SymmetricCipher} (hcca : E.INDCCA) :
    E.OneTimeINDCCA := by
  intro adversary hadversary
  obtain ⟨ck, dk, hlenKey⟩ := E.keyGen_ppt.length_le
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  obtain ⟨cd, dd, hlenDec⟩ := E.decrypt_polyTime.tidy.polyBounded_length.exists_le
  let ctBound : ℕ → ℕ := fun n => ce * (3 * n + 2 * (ck * (n + 1) ^ dk) + 4) ^ de
  let decBound : ℕ → List Bool → ℕ :=
    fun n ct => cd * (2 * n + 2 * (ck * (n + 1) ^ dk) + ct.length + 4) ^ dd
  have hctBoundPoly : ComputableInPolyTime ctBound encUnary encUnary := by
    dsimp only [ctBound]; polytime
  have hdecBoundPoly : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary := by
    dsimp only [decBound]; polytime
  have hctBound (n : ℕ) (k : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
      (msg : List Bool) (hmsg : msg.length = n) (ct : List Bool)
      (hct : ct ∈ (ProbComp.eval (E.encrypt n k msg)).support) : ct.length ≤ ctBound n := by
    have hkLen := hlenKey n k hk
    have hctLen := hlenEnc (n, k, msg) ct hct
    simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkLen
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmsg] at hctLen
    exact hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
  have hdecBound (n : ℕ) (k : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
      (ct : List Bool) :
      (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct := by
    have hkLen := hlenKey n k hk
    have hdecLen := hlenDec (n, k, ct)
    simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkLen
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hdecLen
    exact hdecLen.trans (Nat.mul_le_mul_left cd (Nat.pow_le_pow_left (by lia) dd))
  have hneg := hcca (ccaLimitToOneEncryptionQuery ctBound decBound adversary)
    (isOraclePPT_ccaLimitToOneEncryptionQuery hctBoundPoly hdecBoundPoly hadversary)
  refine hneg.congr fun n => ?_
  dsimp only
  rw [eval_ccaGame_ccaLimitToOneEncryptionQuery E ctBound decBound adversary false n
      (hctBound n) (hdecBound n),
    eval_ccaGame_ccaLimitToOneEncryptionQuery E ctBound decBound adversary true n
      (hctBound n) (hdecBound n)]

/-! ### Authenticated Encryption Implies Adaptive CCA Security (Boneh–Shoup Theorem 9.1) -/

/-- Hybrid two-channel oracle for Game 1 in the proof of [BonehShoup2023], Theorem 9.1
(Section 9.2.3, printed pp. 363–364): encryption queries `(false, req)` behave identically to
`ccaOracle`, whereas every decryption query `(true, _)` immediately returns `[]` (rejection) without
invoking `decrypt`. -/
noncomputable def ccaRejectOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      return ([], queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ct :: queriedCiphertexts)
      else
        return ([], queriedCiphertexts)

/-- The all-reject hybrid CCA experiment (Game 1 in [BonehShoup2023], Section 9.2.3,
Theorem 9.1): sample `k ← E.keyGen n` and run `adversary n []` against
`E.ccaRejectOracle n k bit`. -/
noncomputable def ccaRejectGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ccaRejectOracle n k bit)) (adversary n [])).run []
  return out.1

/-- Stateful handler for `ccaToCPAAdversary` ([BonehShoup2023], Section 9.2.3, Theorem 9.1):
reject all decryption queries `(true, _)` with `[]`, and forward valid left-or-right encryption
queries `(false, req)` to the external CPA encryption oracle (truncating replies to `ctBound`). -/
noncomputable def ccaToCPAHandler (n ctBound : ℕ) (request : Bool × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    if request.1 then
      pure ([], ())
    else
      if ((unframe request.2).length == n) && ((dropFrame request.2).length == n) then
        (fun ct => (ct, ())) <$> (List.take ctBound <$> ProbOracleComp.query ((), request.2))
      else
        pure ([], ())

/-- Reduction from the all-reject hybrid `ccaRejectGame` to the adaptive CPA experiment `cpaGame`
([BonehShoup2023], Section 9.2.3, adversary $B_{\mathrm{cpa}}$ in Theorem 9.1): run `adversary n []`
against `ccaToCPAHandler n (ctBound n)`. -/
noncomputable def ccaToCPAAdversary (ctBound : ℕ → ℕ) (adversary : CCAAdversary) :
    OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ccaToCPAHandler n (ctBound n)))
      (adversary n [])).run ()
    return out.1

/-- `ccaToCPAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaToCPAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (ccaToCPAAdversary ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair encBool encBits) (encFinEnum Unit))
  have hop : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) => p.2.1.1)
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hencCond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hlimit : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) => ctBound p.1.1)
      EIn encUnary :=
    hctBound.comp (by dsimp only [EIn]; fun_prop)
  have hquery : IsOraclePPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        (fun ct => (ct, ())) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query ((), p.2.1.2))) :=
    (IsOraclePPTOn.query_take' () (by dsimp only [EIn]; fun_prop) hlimit).map'
      (ComputableInPolyTime.prod (by fun_prop) (ComputableInPolyTime.const ()))
  have hnoReply : IsOraclePPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun _ => pure ([], ())) :=
    (ComputableInPolyTime.const ([], ())).isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        ccaToCPAHandler pair.1.1 (ctBound pair.1.1) pair.2.1 pair.2.2) := by
    unfold ccaToCPAHandler
    exact IsOraclePPTOn.cond' hop hnoReply (IsOraclePPTOn.cond' hencCond hquery hnoReply)
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add' (hctBound.comp (by fun_prop)) (ComputableInPolyTime.const 1)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool (encFinEnum Unit))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ccaToCPAHandler caller.1 (ctBound caller.1)))
          (adversary caller.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open'
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller _ => ctBound caller.1 + 1)
      (by fun_prop) hhandler (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request _ _ result hresult
    unfold ccaToCPAHandler at hresult
    cases hreq : request.1
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
      split_ifs at hresult with hlenEq
      · obtain ⟨ct, hct, rfl⟩ := ProbOracleComp.mem_support_map hresult
        obtain ⟨rawCt, _, rfl⟩ := ProbOracleComp.mem_support_map hct
        exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by lia⟩
      · cases ProbOracleComp.eq_of_mem_support_pure hresult
        exact ⟨trivial, by simp, by lia⟩
    · simp only [hreq, ↓reduceIte] at hresult
      cases ProbOracleComp.eq_of_mem_support_pure hresult
      exact ⟨trivial, by simp, by lia⟩
  unfold ccaToCPAAdversary
  simpa only [bind_pure_comp] using (hrun.map' (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ccaToCPAAdversary ctBound adversary` in `cpaGame` has the exact same output distribution as
`ccaRejectGame adversary` ([BonehShoup2023], Section 9.2.3, equation (9.7) in the proof of
Theorem 9.1, printed p. 365). -/
theorem eval_cpaGame_ccaToCPAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.ccaRejectGame adversary bit n) := by
  simp only [cpaGame, ccaRejectGame, ccaToCPAAdversary, ProbComp.eval_bind, ProbComp.eval_pure]
  apply PMF.bind_congr_on_support
  intro k hk
  simp only [ProbOracleComp.eval_run_interpret]
  rw [OracleComp.interpret_bind, StateT.run_bind]
  simp only [StateT.run_pure, OracleComp.interpret_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.run_interpret_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (fun request queried => ProbComp.eval (E.ccaRejectOracle n k bit request queried))
    (fun request state =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.cpaEncryptionOracle n k bit q s)))
        ((ccaToCPAHandler n (ctBound n) request).run state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun _ : List (List Bool) => ((), ()))
    (fun request queried => by
      change (ProbComp.eval (E.ccaRejectOracle n k bit request queried)).map
          (fun x => (x.1, (), ())) =
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.cpaEncryptionOracle n k bit q s)))
          (ccaToCPAHandler n (ctBound n) request ())).run ()).map
          (fun result => (result.1.1, result.1.2, result.2))
      cases hreq : request.1
      · simp only [ccaRejectOracle, ccaToCPAHandler, hreq, Bool.false_eq_true, ↓reduceIte]
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            Functor.map_map, OracleComp.interpret_map, StateT.run_map,
            ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map,
            cpaEncryptionOracle]
          dsimp only [StateT.run]
          simp only [PMF.map_bind, PMF.pure_map]
          simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
          have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
            cases bit <;> simp [hlenEq]
          apply PMF.bind_congr_on_support
          intro ct hct
          rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
            PMF.pure_map]
      · simp only [ccaRejectOracle, ccaToCPAHandler, hreq, ↓reduceIte, ProbComp.eval_pure,
          OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
          PMF.pure_map])
    (adversary n []) []
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

/-- Stateful handler for `ccaToCIAtIndexAdversary` and `ccaToCIAdversary`
([BonehShoup2023], Section 9.2.3, adversary $B_{\mathrm{ci}}$ in Theorem 9.1):
maintains `(rem, (hasCaptured, capturedCt)) : ℕ × (Bool × List Bool)`.
* Once `hasCaptured = true`, all subsequent queries return `[]` without calling the external CI
  encryption oracle.
* While `hasCaptured = false`:
  - if `rem == 0`, a decryption query `(true, ct)` captures `(0, (true, ct))` and an encryption
    query `(false, _)` captures `(0, (true, []))`, both returning `[]` without calling the external
    CI oracle;
  - if `rem != 0`, a decryption query `(true, _)` returns `([], (rem - 1, (false, [])))`, and an
    encryption query `(false, req)` with `(unframe req).length == n && (dropFrame req).length == n`
    queries the external CI encryption oracle on `if bit then dropFrame req else unframe req`
    (truncating the reply to `ctBound`) and transitions to `(rem - 1, (false, []))`. -/
noncomputable def ccaToCIHandler (n ctBound : ℕ) (bit : Bool) (request : Bool × List Bool) :
    StateT (ℕ × (Bool × List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun state =>
    if state.2.1 then
      pure ([], (state.1, (true, state.2.2)))
    else
      if state.1 == 0 then
        if request.1 then
          pure ([], (0, (true, request.2)))
        else
          pure ([], (0, (true, [])))
      else
        if request.1 then
          pure ([], (state.1 - 1, (false, [])))
        else
          if ((unframe request.2).length == n) && ((dropFrame request.2).length == n) then
            (fun ct => (ct, (state.1 - 1, (false, [])))) <$>
              (List.take ctBound <$>
                ProbOracleComp.query ((), if bit then dropFrame request.2 else unframe request.2))
          else
            pure ([], (state.1 - 1, (false, [])))

/-- Deterministic-index ciphertext-integrity reduction at query countdown `j`
([BonehShoup2023], Section 9.2.3, Theorem 9.1): run `adversary n []` against
`ccaToCIHandler n (ctBound n) bit` starting from `(j, (false, []))` and output the captured
ciphertext candidate `out.2.2.2`. -/
noncomputable def ccaToCIAtIndexAdversary (ctBound : ℕ → ℕ) (j : ℕ) (bit : Bool)
    (adversary : CCAAdversary) : CIAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ccaToCIHandler n (ctBound n) bit))
      (adversary n [])).run (j, (false, []))
    return out.2.2.2

/-- Reduction from decryption-oracle forgery in `ccaRejectGame` to the ciphertext-integrity game
`ciGame` for fixed challenge bit `bit` ([BonehShoup2023], Section 9.2.3, adversary $B_{\mathrm{ci}}$
in Theorem 9.1): sample a uniform dyadic query countdown
`j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))` and run
`ccaToCIAtIndexAdversary ctBound j bit adversary`. -/
noncomputable def ccaToCIAdversary (ctBound Q : ℕ → ℕ) (bit : Bool)
    (adversary : CCAAdversary) : CIAdversary :=
  fun n aux => do
    let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))
    ccaToCIAtIndexAdversary ctBound j bit adversary n aux

/-- Single-adversary ciphertext-integrity reduction that samples a hidden challenge bit uniformly
via `BitString.sampleList 1` and invokes `ccaToCIAdversary` ([BonehShoup2023], Section 9.2.3,
proof of Theorem 9.1, printed p. 364). -/
noncomputable def ccaToCIHiddenBitAdversary (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) : CIAdversary :=
  fun n aux => do
    let bits ← ProbOracleComp.sample (BitString.sampleList 1)
    if bits == [true] then
      ccaToCIAdversary ctBound Q true adversary n aux
    else
      ccaToCIAdversary ctBound Q false adversary n aux

/-- `ccaToCIAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaToCIAdversary {ctBound Q : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary) (bit : Bool)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBits (ccaToCIAdversary ctBound Q bit adversary) := by
  let ECaller := encPair (encPair encUnary encBits) encUnary
  let EState := encPair encUnary (encPair encBool encBits)
  let EIn := encPair ECaller (encPair (encPair encBool encBits) EState)
  have hcaptured : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.2.2.1)
      EIn encBool := by
    dsimp only [EIn, ECaller, EState]; fun_prop
  have hremZero : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.2.1 == 0)
      EIn encBool := by
    dsimp only [EIn, ECaller, EState]; polytime
  have hop : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.1.1)
      EIn encBool := by
    dsimp only [EIn, ECaller, EState]; fun_prop
  have hencCond : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        ((unframe p.2.1.2).length == p.1.1.1) && ((dropFrame p.2.1.2).length == p.1.1.1))
      EIn encBool := by
    dsimp only [EIn, ECaller, EState]; polytime
  have hm0 : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        unframe p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.unframe.comp (by dsimp only [EIn, ECaller, EState]; fun_prop)
  have hm1 : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        dropFrame p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.dropFrame.comp (by dsimp only [EIn, ECaller, EState]; fun_prop)
  have hmsg : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hlimit : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        ctBound p.1.1.1)
      EIn encUnary :=
    hctBound.comp (by dsimp only [EIn, ECaller, EState]; fun_prop)
  have hdecRem : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        (p.2.2.1 - 1, (false, ([] : List Bool))))
      EIn EState := by
    dsimp only [EIn, ECaller, EState]
    exact ComputableInPolyTime.prod
      (ComputableInPolyTime.unary_sub.comp
        (ComputableInPolyTime.prod (by fun_prop) (ComputableInPolyTime.const 1)))
      (ComputableInPolyTime.const (false, []))
  have hbranchCaptured : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        pure ([], (p.2.2.1, (true, p.2.2.2.2)))) := by
    dsimp only [EIn, ECaller, EState]
    exact (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (ComputableInPolyTime.prod (by fun_prop)
        (ComputableInPolyTime.prod (ComputableInPolyTime.const true)
          (by fun_prop)))).isOraclePPTOn
  have hbranchZeroDec : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        pure ([], (0, (true, p.2.1.2)))) := by
    dsimp only [EIn, ECaller, EState]
    exact (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (ComputableInPolyTime.prod (ComputableInPolyTime.const 0)
        (ComputableInPolyTime.prod (ComputableInPolyTime.const true)
          (by fun_prop)))).isOraclePPTOn
  have hbranchZeroEnc : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun _ => pure ([], (0, (true, ([] : List Bool))))) :=
    (ComputableInPolyTime.const ([], (0, (true, [])))).isOraclePPTOn
  have hbranchStepNo : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun p => pure ([], (p.2.2.1 - 1, (false, ([] : List Bool))))) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      hdecRem).isOraclePPTOn
  have hbranchStepQuery : IsOraclePPTOn EIn (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        (fun ct => (ct, (p.2.2.1 - 1, (false, ([] : List Bool))))) <$>
          (List.take (ctBound p.1.1.1) <$>
            ProbOracleComp.query ((), if bit then dropFrame p.2.1.2 else unframe p.2.1.2))) :=
    (IsOraclePPTOn.query_take' (Operation := Unit) () hmsg hlimit).map_with'
      (ComputableInPolyTime.prod (by fun_prop)
        (hdecRem.comp (ComputableInPolyTime.fst EIn encBits)))
  have hhandler : IsOraclePPTOn EIn (encPair encBits EState)
      (fun pair : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        ccaToCIHandler pair.1.1.1 (ctBound pair.1.1.1) bit pair.2.1 pair.2.2) := by
    unfold ccaToCIHandler
    exact IsOraclePPTOn.cond' hcaptured hbranchCaptured
      (IsOraclePPTOn.cond' hremZero
        (IsOraclePPTOn.cond' hop hbranchZeroDec hbranchZeroEnc)
        (IsOraclePPTOn.cond' hop hbranchStepNo
          (IsOraclePPTOn.cond' hencCond hbranchStepQuery hbranchStepNo)))
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × ℕ) × List Bool => ctBound pair.1.1.1 + pair.2.length + 4)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]
    have hct : ComputableInPolyTime
        (fun pair : ((ℕ × List Bool) × ℕ) × List Bool => ctBound pair.1.1.1)
        (encPair (encPair (encPair encUnary encBits) encUnary) encBits) encUnary :=
      hctBound.comp (by fun_prop)
    have hqlen : ComputableInPolyTime
        (fun pair : ((ℕ × List Bool) × ℕ) × List Bool => pair.2.length + 4)
        (encPair (encPair (encPair encUnary encBits) encUnary) encBits) encUnary := by
      polytime
    exact ComputableInPolyTime.unary_add.comp (ComputableInPolyTime.prod hct hqlen)
  have hinit : ComputableInPolyTime
      (fun caller : (ℕ × List Bool) × ℕ => (caller.2, (false, ([] : List Bool))))
      ECaller EState := by
    dsimp only [ECaller, EState]
    exact ComputableInPolyTime.prod (by fun_prop)
      (ComputableInPolyTime.const (false, []))
  have hrun : IsOraclePPTOn ECaller (encPair encBool EState)
      (fun caller : (ℕ × List Bool) × ℕ =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ccaToCIHandler caller.1.1 (ctBound caller.1.1) bit))
          (adversary caller.1.1 [])).run (caller.2, (false, []))) := by
    apply hadversary.run_interpret_preprocess_open'
      (prepare := fun caller : (ℕ × List Bool) × ℕ => (caller.1.1, ([] : List Bool)))
      (initial := fun caller : (ℕ × List Bool) × ℕ => (caller.2, (false, ([] : List Bool))))
      (resources := fun caller query => ctBound caller.1.1 + query.length + 4)
      (by dsimp only [ECaller]; fun_prop) hhandler hinit
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold ccaToCIHandler at hresult
    by_cases hcap : state.2.1 = true
    · simp only [hcap, ↓reduceIte] at hresult
      cases ProbOracleComp.eq_of_mem_support_pure hresult
      refine ⟨trivial, by simp, ?_⟩
      simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton, encBits_apply]
      lia
    · simp only [hcap, Bool.false_eq_true, ↓reduceIte] at hresult
      by_cases hzero : (state.1 == 0) = true
      · simp only [hzero, ↓reduceIte] at hresult
        cases hreq : request.1 <;>
          simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult <;>
          cases ProbOracleComp.eq_of_mem_support_pure hresult <;>
          refine ⟨trivial, by simp, ?_⟩ <;>
          simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
            encBool_apply, List.length_singleton, encBits_apply, List.length_nil] <;>
          lia
      · simp only [hzero, Bool.false_eq_true, ↓reduceIte] at hresult
        cases hreq : request.1
        · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
          by_cases hlenEq : ((unframe request.2).length == caller.1.1 &&
              (dropFrame request.2).length == caller.1.1) = true
          · simp only [hlenEq, ↓reduceIte] at hresult
            obtain ⟨ct, hct, rfl⟩ := ProbOracleComp.mem_support_map hresult
            obtain ⟨rawCt, _, rfl⟩ := ProbOracleComp.mem_support_map hct
            refine ⟨trivial, (List.length_take_le _ _).trans (by lia), ?_⟩
            simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
              encBool_apply, List.length_singleton, encBits_apply, List.length_nil]
            lia
          · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte] at hresult
            cases ProbOracleComp.eq_of_mem_support_pure hresult
            refine ⟨trivial, by simp, ?_⟩
            simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
              encBool_apply, List.length_singleton, encBits_apply, List.length_nil]
            lia
        · simp only [hreq, ↓reduceIte] at hresult
          cases ProbOracleComp.eq_of_mem_support_pure hresult
          refine ⟨trivial, by simp, ?_⟩
          simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
            encBool_apply, List.length_singleton, encBits_apply, List.length_nil]
          lia
  have hsample : IsOraclePPTOn (encPair encUnary encBits) encUnary
      (fun caller : ℕ × List Bool =>
        ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q caller.1))) :=
    (isPPTOn_sampleDyadicIndex (hQ.comp (by fun_prop))).isOraclePPTOn (Operation := Unit)
  have hpost : ComputableInPolyTime
      (fun out : Bool × (ℕ × (Bool × List Bool)) => out.2.2.2)
      (encPair encBool EState) encBits := by
    dsimp only [EState]; fun_prop
  unfold ccaToCIAdversary ccaToCIAtIndexAdversary
  simpa only [bind_pure_comp] using (hsample.bind_with (hrun.map' hpost)).isOraclePPT

/-- `ccaToCIHiddenBitAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaToCIHiddenBitAdversary {ctBound Q : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBits (ccaToCIHiddenBitAdversary ctBound Q adversary) := by
  have hsample : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun _ : ℕ × List Bool => ProbOracleComp.sample (BitString.sampleList 1)) :=
    (ComputableInPolyTime.sampleList
      (ComputableInPolyTime.const 1)).isOraclePPTOn (Operation := Unit)
  have hcond : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => pair.2 == [true])
      (encPair (encPair encUnary encBits) encBits) encBool :=
    ComputableInPolyTime.beq (by fun_prop) (ComputableInPolyTime.const [true])
  have htrue : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun pair : (ℕ × List Bool) × List Bool =>
        ccaToCIAdversary ctBound Q true adversary pair.1.1 pair.1.2) :=
    (isOraclePPT_ccaToCIAdversary hctBound hQ true hadversary).on.preprocess (by fun_prop)
  have hfalse : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun pair : (ℕ × List Bool) × List Bool =>
        ccaToCIAdversary ctBound Q false adversary pair.1.1 pair.1.2) :=
    (isOraclePPT_ccaToCIAdversary hctBound hQ false hadversary).on.preprocess (by fun_prop)
  unfold ccaToCIHiddenBitAdversary
  exact (hsample.bind_with (IsOraclePPTOn.cond' hcond htrue hfalse)).isOraclePPT

/-! #### Difference-Lemma Hop and Query-Budget Induction for Theorem 9.1 -/

/-- `ccaOracle` instrumented with a sticky Boolean flag `bad` that becomes `true` whenever the
adversary submits a fresh ciphertext `ct` (`!queried.contains ct`) that decrypts to `some _`
([BonehShoup2023], Section 9.2.3, event $Z$ in Theorem 9.1). -/
private noncomputable def ccaWithBadOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) :
    StateT (List (List Bool) × Bool) ProbComp (List Bool) :=
  fun state =>
    if request.1 then
      if state.1.contains request.2 then
        return ([], state)
      else
        let dec := E.decrypt n k request.2
        return (encOption encBits dec, (state.1, state.2 || dec.isSome))
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, (ct :: state.1, state.2))
      else
        return ([], state)

/-- `ccaRejectOracle` instrumented with the same sticky Boolean flag `bad`
([BonehShoup2023], Section 9.2.3, Game 1 with event $Z$ in Theorem 9.1). -/
private noncomputable def ccaRejectWithBadOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) :
    StateT (List (List Bool) × Bool) ProbComp (List Bool) :=
  fun state =>
    if request.1 then
      if state.1.contains request.2 then
        return ([], state)
      else
        let dec := E.decrypt n k request.2
        return ([], (state.1, state.2 || dec.isSome))
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, (ct :: state.1, state.2))
      else
        return ([], state)

private theorem run_ccaWithBadOracle_map_fst (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (program : WordOracleComp Bool Bool) (queried : List (List Bool)) (bad : Bool) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s)))
      program).run (queried, bad)).map (fun (a, s) => (a, s.1)) =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaOracle n k bit q s)))
        program).run queried := by
  refine ProbOracleComp.run_interpret_map_state
    (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s))
    (fun q s => ProbComp.eval (E.ccaOracle n k bit q s))
    Prod.fst ?_ program (queried, bad)
  intro request state
  cases hreq : request.1
  · simp only [ccaWithBadOracle, ccaOracle, hreq, Bool.false_eq_true, ↓reduceIte]
    by_cases hlenEq : ((unframe request.2).length == n &&
        (dropFrame request.2).length == n) = true
    · simp [hlenEq, PMF.map_comp, Function.comp_def]
    · simp [hlenEq, PMF.pure_map]
  · simp only [ccaWithBadOracle, ccaOracle, hreq, ↓reduceIte]
    split_ifs <;> simp [PMF.pure_map]

private theorem run_ccaRejectWithBadOracle_map_fst (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (program : WordOracleComp Bool Bool) (queried : List (List Bool)) (bad : Bool) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
      program).run (queried, bad)).map (fun (a, s) => (a, s.1)) =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaRejectOracle n k bit q s)))
        program).run queried := by
  refine ProbOracleComp.run_interpret_map_state
    (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s))
    (fun q s => ProbComp.eval (E.ccaRejectOracle n k bit q s))
    Prod.fst ?_ program (queried, bad)
  intro request state
  cases hreq : request.1
  · simp only [ccaRejectWithBadOracle, ccaRejectOracle, hreq, Bool.false_eq_true, ↓reduceIte]
    by_cases hlenEq : ((unframe request.2).length == n &&
        (dropFrame request.2).length == n) = true
    · simp [hlenEq, PMF.map_comp, Function.comp_def]
    · simp [hlenEq, PMF.pure_map]
  · simp only [ccaRejectWithBadOracle, ccaRejectOracle, hreq, ↓reduceIte]
    split_ifs <;> simp [PMF.pure_map]

private theorem identicalUntilBad_ccaRejectWithBad_ccaWithBad (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) :
    OracleComp.IdenticalUntilBad
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s)))
      (fun s => s.2 = true) where
  agree q s hs a s' hs' := by
    cases q with
    | inl m => rfl
    | inr request =>
      simp only [ProbOracleComp.handler]
      cases hreq : request.1
      · simp only [ccaRejectWithBadOracle, ccaWithBadOracle, hreq, Bool.false_eq_true, ↓reduceIte]
      · simp only [ccaRejectWithBadOracle, ccaWithBadOracle, hreq, ↓reduceIte]
        split_ifs with hmem
        · rfl
        · cases hdec : E.decrypt n k request.2 with
          | none =>
            simp [Option.isSome, encOption]
          | some msg =>
            have hne : s' ≠ (s.1, true) := fun h => hs' (congrArg Prod.snd h)
            simp [Option.isSome, ProbComp.eval_pure, PMF.pure_apply, hne]
  absorb_first q s hs x hx := by
    cases q with
    | inl m =>
      change x ∈ ((ProbComp.unifOracle m).map (·, s)).support at hx
      obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr request =>
      simp only [ProbOracleComp.handler, ccaRejectWithBadOracle] at hx
      cases hreq : request.1
      · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hx
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hx
          obtain ⟨_, _, rfl⟩ := hx
          exact hs
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            PMF.mem_support_pure_iff] at hx
          subst x
          exact hs
      · simp only [hreq, ↓reduceIte] at hx
        split_ifs at hx <;>
          simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx <;>
          subst x <;>
          simp [hs]
  absorb_second q s hs x hx := by
    cases q with
    | inl m =>
      change x ∈ ((ProbComp.unifOracle m).map (·, s)).support at hx
      obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr request =>
      simp only [ProbOracleComp.handler, ccaWithBadOracle] at hx
      cases hreq : request.1
      · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hx
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hx
          obtain ⟨_, _, rfl⟩ := hx
          exact hs
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            PMF.mem_support_pure_iff] at hx
          subst x
          exact hs
      · simp only [hreq, ↓reduceIte] at hx
        split_ifs at hx <;>
          simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx <;>
          subst x <;>
          simp [hs]

/-- Combined single-step stateful oracle representing `ccaToCIHandler` composed with
`ciEncryptionOracle` on joint state `(rem, (hasCaptured, capturedCt)) × queriedCiphertexts`. -/
private noncomputable def ccaToCICombinedOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) :
    StateT ((ℕ × (Bool × List Bool)) × List (List Bool)) ProbComp (List Bool) :=
  fun state =>
    if state.1.2.1 then
      return ([], ((state.1.1, (true, state.1.2.2)), state.2))
    else
      if state.1.1 == 0 then
        if request.1 then
          return ([], ((0, (true, request.2)), state.2))
        else
          return ([], ((0, (true, [])), state.2))
      else
        if request.1 then
          return ([], ((state.1.1 - 1, (false, [])), state.2))
        else
          let m0 := unframe request.2
          let m1 := dropFrame request.2
          if (m0.length == n) && (m1.length == n) then do
            let ct ← E.encrypt n k (if bit then m1 else m0)
            return (ct, ((state.1.1 - 1, (false, [])), ct :: state.2))
          else
            return ([], ((state.1.1 - 1, (false, [])), state.2))

/-- Once `hasCaptured = true` holds in `ccaToCICombinedOracle`, both `capturedCt` and `queried`
remain frozen across any subsequent computation `program`. -/
private theorem ciCombined_captured_bind_eq_one {α : Type} (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) (program : WordOracleComp Bool α) (rem : ℕ)
    (ct : List Bool) (queried : List (List Bool))
    (hwin : (!queried.contains ct && (E.decrypt n k ct).isSome) = true) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
      program).run ((rem, (true, ct)), queried)).bind
      (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome)) true =
      1 := by
  refine le_antisymm (PMF.coe_le_one _ _) (PMF.le_bind_apply_on_support _ fun x hx => ?_)
  have hinv := ProbOracleComp.run_interpret_invariant
    (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s))
    (fun s => s.1.2 = (true, ct) ∧ s.2 = queried)
    (fun q s ⟨hcap, hq⟩ a s' hs' => by
      have hcap1 : s.1.2.1 = true := by rw [hcap]
      have hcap2 : s.1.2.2 = ct := by rw [hcap]
      simp only [ccaToCICombinedOracle, hcap1, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hs'
      cases hs'
      exact ⟨by simp [hcap2], hq⟩)
    program ((rem, (true, ct)), queried) ⟨rfl, rfl⟩ x.1 x.2 hx
  have hct : x.2.1.2.2 = ct := by rw [hinv.1]
  rw [hct, hinv.2, hwin, PMF.pure_apply_self]

private theorem ennreal_tsum_finsetSum {α β : Type*}
    (s : Finset β) (f : α → β → ℝ≥0∞) :
    (∑' a, ∑ b ∈ s, f a b) = ∑ b ∈ s, ∑' a, f a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb, tsum_add, ih]

private theorem eval_ccaRejectWithBadOracle_false (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) (queried : List (List Bool)) :
    ProbComp.eval (E.ccaRejectWithBadOracle n k bit request (queried, false)) =
      if request.1 then
        if queried.contains request.2 then
          PMF.pure ([], (queried, false))
        else
          PMF.pure ([], (queried, (E.decrypt n k request.2).isSome))
      else
        if ((unframe request.2).length == n && (dropFrame request.2).length == n) = true then
          (ProbComp.eval (E.encrypt n k
            (if bit then dropFrame request.2 else unframe request.2))).bind
            (fun ct => PMF.pure (ct, (ct :: queried, false)))
        else
          PMF.pure ([], (queried, false)) := by
  unfold ccaRejectWithBadOracle
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  · simp only [↓reduceIte, Bool.false_or]
    split_ifs <;> simp only [ProbComp.eval_pure]

private theorem eval_ccaToCICombinedOracle_succ_false (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) (j : ℕ) (queried : List (List Bool)) :
    ProbComp.eval (E.ccaToCICombinedOracle n k bit request ((j + 1, (false, [])), queried)) =
      if request.1 then
        PMF.pure ([], ((j, (false, [])), queried))
      else
        if ((unframe request.2).length == n && (dropFrame request.2).length == n) = true then
          (ProbComp.eval (E.encrypt n k
            (if bit then dropFrame request.2 else unframe request.2))).bind
            (fun ct => PMF.pure (ct, ((j, (false, [])), ct :: queried)))
        else
          PMF.pure ([], ((j, (false, [])), queried)) := by
  have hne : ((j + 1 == 0) = true) ↔ False := by simp
  unfold ccaToCICombinedOracle
  simp only [Bool.false_eq_true, ↓reduceIte, hne, Nat.add_sub_cancel]
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  · simp only [↓reduceIte, ProbComp.eval_pure]

private theorem eval_ccaToCICombinedOracle_zero_false (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) (queried : List (List Bool)) :
    ProbComp.eval (E.ccaToCICombinedOracle n k bit request ((0, (false, [])), queried)) =
      if request.1 then
        PMF.pure ([], ((0, (true, request.2)), queried))
      else
        PMF.pure ([], ((0, (true, [])), queried)) := by
  unfold ccaToCICombinedOracle
  cases hreq : request.1 <;>
    simp [ProbComp.eval_pure]

/-- Query-budget induction for [BonehShoup2023], Theorem 9.1: for any program `program` making at
most `Q` external oracle queries, the probability of reaching `bad = true` under
`ccaRejectWithBadOracle` from `(queried, false)` is bounded by the sum over countdown indices
`j ∈ Finset.range (Q + 1)` of the CI winning probability under `ccaToCICombinedOracle` from
`((j, (false, [])), queried)`. -/
private theorem bad_ccaRejectWithBad_le_sum_ciCombined {α : Type} (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) {program : WordOracleComp Bool α} {Q : ℕ}
    (hq : program.IsQueryBounded Q) (queried : List (List Bool)) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
      program).run (queried, false)).toOuterMeasure {x | x.2.2 = true} ≤
      ∑ j ∈ Finset.range (Q + 1),
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
          program).run ((j, (false, [])), queried)).bind
          (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome))
          true := by
  induction hq generalizing queried with
  | pure a Q =>
    simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte, zero_le]
  | liftBind q cont Q hcont ih =>
    cases q with
    | inl m =>
      simp only [Sum.elim_inl, Nat.add_zero, OracleComp.run_interpret_bind,
        OracleComp.run_interpret_query, ProbOracleComp.handler, StateT.lift,
        Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.toOuterMeasure_bind_apply, PMF.bind_apply]
      calc ∑' a : Fin (m + 1), ProbComp.unifOracle m a *
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
              (cont a)).run (queried, false)).toOuterMeasure {x | x.2.2 = true}
          ≤ ∑' a : Fin (m + 1), ProbComp.unifOracle m a *
              ∑ j ∈ Finset.range (Q + 1),
                ((OracleComp.interpret
                  (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                    (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
                  (cont a)).run ((j, (false, [])), queried)).bind
                  (fun x =>
                    PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome))
                  true :=
            tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (ih a queried) zero_le
        _ = _ := by
          simp only [Finset.mul_sum]
          rw [ennreal_tsum_finsetSum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [← PMF.bind_apply]
    | inr request =>
      simp only [Sum.elim_inr, OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        ProbOracleComp.handler]
      rw [Finset.sum_range_succ']
      simp only [eval_ccaRejectWithBadOracle_false, eval_ccaToCICombinedOracle_succ_false,
        eval_ccaToCICombinedOracle_zero_false]
      cases hreq : request.1
      · -- Encryption query: `request.1 = false`
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte,
            Probability.PMF.monad_bind_eq_bind,
            PMF.bind_bind, PMF.pure_bind, PMF.toOuterMeasure_bind_apply]
          have hle : ∑' ct : List Bool,
              ProbComp.eval
                (E.encrypt n k (if bit then dropFrame request.2 else unframe request.2)) ct *
                ((OracleComp.interpret
                  (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                    (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
                  (cont ct)).run (ct :: queried, false)).toOuterMeasure {x | x.2.2 = true} ≤
              ∑ j ∈ Finset.range (Q + 1),
                (ProbComp.eval (E.encrypt n k
                  (if bit then dropFrame request.2 else unframe request.2))).bind (fun ct =>
                    ((OracleComp.interpret
                      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                        (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
                      (cont ct)).run ((j, (false, [])), ct :: queried)).bind
                      (fun x =>
                        PMF.pure (!x.2.2.contains x.2.1.2.2 &&
                          (E.decrypt n k x.2.1.2.2).isSome)))
                  true := by
            calc ∑' ct : List Bool,
                  ProbComp.eval
                    (E.encrypt n k (if bit then dropFrame request.2 else unframe request.2)) ct *
                    ((OracleComp.interpret
                      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                        (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
                      (cont ct)).run (ct :: queried, false)).toOuterMeasure {x | x.2.2 = true}
                ≤ ∑' ct : List Bool,
                    ProbComp.eval
                      (E.encrypt n k (if bit then dropFrame request.2 else unframe request.2)) ct *
                      ∑ j ∈ Finset.range (Q + 1),
                        ((OracleComp.interpret
                          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                            (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
                          (cont ct)).run ((j, (false, [])), ct :: queried)).bind
                          (fun x =>
                            PMF.pure (!x.2.2.contains x.2.1.2.2 &&
                              (E.decrypt n k x.2.1.2.2).isSome))
                          true :=
                  tsum_le_tsum fun ct =>
                    mul_le_mul_of_nonneg_left (ih ct (ct :: queried)) zero_le
              _ = _ := by
                simp only [Finset.mul_sum]
                rw [ennreal_tsum_finsetSum]
                refine Finset.sum_congr rfl fun j _ => ?_
                simp only [PMF.bind_apply]
          exact hle.trans le_self_add
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte,
            Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
          exact (ih [] queried).trans le_self_add
      · -- Decryption query: `request.1 = true`
        simp only [↓reduceIte,
          Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
        by_cases hmem : queried.contains request.2 = true
        · simp only [hmem, ↓reduceIte, PMF.pure_bind]
          exact (ih [] queried).trans le_self_add
        · simp only [hmem, Bool.false_eq_true, ↓reduceIte, PMF.pure_bind]
          by_cases hsome : (E.decrypt n k request.2).isSome = true
          · simp only [hsome]
            have hwin :
                (!queried.contains request.2 && (E.decrypt n k request.2).isSome) = true := by
              rw [Bool.eq_false_iff.mpr hmem, hsome]
              rfl
            rw [ciCombined_captured_bind_eq_one E n k bit (cont []) 0 request.2 queried hwin]
            exact (Cslib.Probability.PMF.toOuterMeasure_le_one _ _).trans le_add_self
          · have hnotSome : (E.decrypt n k request.2).isSome = false :=
              Bool.eq_false_iff.mpr hsome
            simp only [hnotSome]
            exact (ih [] queried).trans le_self_add

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ccaToCIAtIndexAdversary ctBound j bit adversary` in `ciGame` under key `k` has the same
winning distribution as `ccaToCICombinedOracle` from `((j, (false, [])), [])`. -/
private theorem eval_ciGame_ccaToCIAtIndexAdversary_key (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (j : ℕ) (bit : Bool) (adversary : CCAAdversary) (n : ℕ) (k : List Bool)
    (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
      (ccaToCIAtIndexAdversary ctBound j bit adversary n [])).run []).bind
      (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
        (adversary n [])).run ((j, (false, [])), [])).bind
        (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome)) := by
  unfold ccaToCIAtIndexAdversary
  rw [OracleComp.interpret_bind, StateT.run_bind]
  simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.run_interpret_run_interpret]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  congr 2
  funext q state
  cases q with
  | inl m => rfl
  | inr request =>
    simp only [ProbOracleComp.handler]
    change ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
      (ccaToCIHandler n (ctBound n) bit request state.1)).run state.2).map
      (fun result => (result.1.1, result.1.2, result.2)) =
      ProbComp.eval (E.ccaToCICombinedOracle n k bit request state)
    unfold ccaToCIHandler ccaToCICombinedOracle
    by_cases hcap : state.1.2.1 = true
    · simp only [hcap, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]
    · simp only [hcap, Bool.false_eq_true, ↓reduceIte]
      by_cases hzero : (state.1.1 == 0) = true
      · simp only [hzero, ↓reduceIte]
        cases hreq : request.1 <;>
          simp only [Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure,
            StateT.run_pure, Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]
      · simp only [hzero, Bool.false_eq_true, ↓reduceIte]
        cases hreq : request.1
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hlenEq : ((unframe request.2).length == n &&
              (dropFrame request.2).length == n) = true
          · simp only [hlenEq, ↓reduceIte, Functor.map_map, OracleComp.interpret_map,
              StateT.run_map, ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map,
              ProbComp.eval_bind, ProbComp.eval_pure, ciEncryptionOracle]
            simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
            have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
              cases bit <;> simp [hlenEq]
            have hmbEq : ((if bit then dropFrame request.2 else unframe request.2).length == n) =
                true := beq_iff_eq.mpr hmbLen
            dsimp only [StateT.run]
            simp only [hmbEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
              PMF.map_bind, PMF.pure_map]
            apply PMF.bind_congr_on_support
            intro ct hct
            rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
          · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure,
              StateT.run_pure, Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]
        · simp only [↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
            Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]

/-- Advantage between `ccaGame` and `ccaRejectGame` at challenge bit `bit` is bounded by the sum
over `j ∈ Finset.range (Q n + 1)` of the CI winning probabilities of
`ccaToCIAtIndexAdversary ctBound j bit adversary`. -/
private theorem advantage_ccaGame_ccaRejectGame_le_sum (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaGame adversary bit n))
        (ProbComp.eval (E.ccaRejectGame adversary bit n)) : ℝ) ≤
      ∑ j ∈ Finset.range (Q n + 1),
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) : ℝ) := by
  have hccaEq (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaOracle n k bit q s)))
        (adversary n [])).run []).bind (fun out => PMF.pure out.1) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) := by
    rw [← run_ccaWithBadOracle_map_fst E n k bit (adversary n []) [] false,
      PMF.bind_map, Function.comp_def]
  have hrejEq (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaRejectOracle n k bit q s)))
        (adversary n [])).run []).bind (fun out => PMF.pure out.1) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) := by
    rw [← run_ccaRejectWithBadOracle_map_fst E n k bit (adversary n []) [] false,
      PMF.bind_map, Function.comp_def]
  set pCCA := ProbComp.eval (E.ccaGame adversary bit n) true
  set pRej := ProbComp.eval (E.ccaRejectGame adversary bit n) true
  set pSum : ℝ≥0∞ := ∑ j ∈ Finset.range (Q n + 1),
    ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n) true
  have hsum_eq : pSum = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ∑ j ∈ Finset.range (Q n + 1),
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
          (ccaToCIAtIndexAdversary ctBound j bit adversary n [])).run []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) true := by
    simp only [pSum, ciGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret]
    conv_lhs =>
      arg 2; ext j
      rw [PMF.bind_apply]
    rw [← ennreal_tsum_finsetSum]
    refine tsum_congr fun k => ?_
    rw [Finset.mul_sum]
  have hCCA_eq : pCCA = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) true := by
    simp only [pCCA, ccaGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret, hccaEq]
    exact PMF.bind_apply _ _ _
  have hRej_eq : pRej = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) true := by
    simp only [pRej, ccaRejectGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret, hrejEq]
    exact PMF.bind_apply _ _ _
  have hle1 : pCCA ≤ pRej + pSum := by
    rw [hCCA_eq, hRej_eq, hsum_eq, ← tsum_add]
    refine tsum_le_tsum fun k => ?_
    rw [← mul_add]
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hiub := (identicalUntilBad_ccaRejectWithBad_ccaWithBad E n k bit).symm
      have hstep := hiub.bind_apply_le (adversary n []) ([], false) (fun out => PMF.pure out.1) true
      rw [← (identicalUntilBad_ccaRejectWithBad_ccaWithBad E n k bit).bad_eq] at hstep
      refine hstep.trans (add_le_add le_rfl ?_)
      refine (bad_ccaRejectWithBad_le_sum_ciCombined E n k bit hq []).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eval_ciGame_ccaToCIAtIndexAdversary_key E ctBound j bit adversary n k hk hctBound]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hk, zero_mul, zero_mul]
  have hle2 : pRej ≤ pCCA + pSum := by
    rw [hCCA_eq, hRej_eq, hsum_eq, ← tsum_add]
    refine tsum_le_tsum fun k => ?_
    rw [← mul_add]
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hiub := identicalUntilBad_ccaRejectWithBad_ccaWithBad E n k bit
      have hstep := hiub.bind_apply_le (adversary n []) ([], false) (fun out => PMF.pure out.1) true
      refine hstep.trans (add_le_add le_rfl ?_)
      refine (bad_ccaRejectWithBad_le_sum_ciCombined E n k bit hq []).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eval_ciGame_ccaToCIAtIndexAdversary_key E ctBound j bit adversary n k hk hctBound]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hk, zero_mul, zero_mul]
  have hpSum_ne_top : pSum ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ => PMF.apply_ne_top _ _
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hpSum_ne_top⟩) hle1
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hpSum_ne_top⟩) hle2
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) hpSum_ne_top] at h1 h2
  have habs : |pCCA.toReal - pRej.toReal| ≤ pSum.toReal :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  rw [Game.coe_advantage]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, pCCA, pRej, pSum,
    ENNReal.toReal_sum (fun j _ => PMF.apply_ne_top _ _)] using habs

/-- Running `ccaToCIAdversary` in `ciGame` averages `ccaToCIAtIndexAdversary` uniformly over
`Fin (dyadicSize (Q n))`. -/
theorem eval_ciGame_ccaToCIAdversary (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (bit : Bool) (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q bit adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind
        (fun i =>
          ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound i.val bit adversary) n)) := by
  simp only [ciGame, ccaToCIAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret]
  have hsample (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
        (do
          let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))
          ccaToCIAtIndexAdversary ctBound j bit adversary n [])).run []).bind
        (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind (fun i =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
          (ccaToCIAtIndexAdversary ctBound i.val bit adversary n [])).run []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) := by
    rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
      ProbComp.eval_sampleDyadicIndex]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind]
  simp only [hsample]
  exact PMF.bind_comm _ _ _

/-- The sum of CI winning probabilities over `j ∈ Finset.range (Q n + 1)` is at most
`dyadicSize (Q n)` times the CI winning probability of `ccaToCIAdversary`. -/
private theorem sum_succProbability_ccaToCIAtIndexAdversary_le (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary) (n : ℕ) :
    (∑ j ∈ Finset.range (Q n + 1),
      (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) : ℝ)) ≤
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q bit adversary) n)) : ℝ) := by
  have hcap : (dyadicSize (Q n) : ℝ) ≠ 0 := by exact_mod_cast (dyadicSize_pos (Q n)).ne'
  rw [eval_ciGame_ccaToCIAdversary, Game.succProbability_uniform, NNReal.coe_div,
    NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_fin, mul_div_cancel₀ _ hcap,
    Fin.sum_univ_eq_sum_range
      (fun j => (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) : ℝ))]
  have hsub : Finset.range (Q n + 1) ⊆ Finset.range (dyadicSize (Q n)) := by
    intro x hx
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le (lt_dyadicSize (Q n)))
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => NNReal.coe_nonneg _

/-- **Quantitative AE $\Rightarrow$ CCA bound** ([BonehShoup2023], Section 9.2.3, Theorem 9.1,
printed pp. 363–365): for any `CCAAdversary` making at most `Q n` total oracle queries at security
parameter `n`, the adaptive CCA distinguishing advantage is bounded by the CPA advantage of
`ccaToCPAAdversary` plus `dyadicSize (Q n)` times the ciphertext-integrity winning probabilities of
`ccaToCIAdversary` for `bit = false` and `bit = true`.

Relative to equation (9.3) in [BonehShoup2023]
(`CCAadv[A, E] ≤ CPAadv[Bcpa, E] + 2 Qd · CIadv[Bci, E]`), `ccaToCIAdversary` samples a query index
uniformly from `{0, ..., dyadicSize (Q n) - 1}` over the total query budget `Q n ≥ Qe + Qd`, giving
coefficient `dyadicSize (Q n) ≤ 2 * Q n + 2` per bit. -/
theorem advantage_ccaGame_le (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q false adversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) +
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q true adversary) n)) : ℝ) := by
  have h1 : (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
      (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
        (ProbComp.eval (E.ccaRejectGame adversary false n)) : ℝ) +
      (Game.advantage (ProbComp.eval (E.ccaRejectGame adversary false n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) := by
    exact_mod_cast Game.advantage_triangle
      (ProbComp.eval (E.ccaGame adversary false n))
      (ProbComp.eval (E.ccaRejectGame adversary false n))
      (ProbComp.eval (E.ccaGame adversary true n))
  have h2 : (Game.advantage (ProbComp.eval (E.ccaRejectGame adversary false n))
      (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      (Game.advantage (ProbComp.eval (E.ccaRejectGame adversary false n))
        (ProbComp.eval (E.ccaRejectGame adversary true n)) : ℝ) +
      (Game.advantage (ProbComp.eval (E.ccaRejectGame adversary true n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) := by
    exact_mod_cast Game.advantage_triangle
      (ProbComp.eval (E.ccaRejectGame adversary false n))
      (ProbComp.eval (E.ccaRejectGame adversary true n))
      (ProbComp.eval (E.ccaGame adversary true n))
  have hcomm : Game.advantage (ProbComp.eval (E.ccaRejectGame adversary true n))
      (ProbComp.eval (E.ccaGame adversary true n)) =
      Game.advantage (ProbComp.eval (E.ccaGame adversary true n))
      (ProbComp.eval (E.ccaRejectGame adversary true n)) := Game.advantage_comm _ _
  have hcpaEq : Game.advantage (ProbComp.eval (E.ccaRejectGame adversary false n))
      (ProbComp.eval (E.ccaRejectGame adversary true n)) =
      Game.advantage (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) false n))
      (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) true n)) := by
    rw [eval_cpaGame_ccaToCPAAdversary E ctBound adversary false n hctBound,
      eval_cpaGame_ccaToCPAAdversary E ctBound adversary true n hctBound]
  rw [hcomm, hcpaEq] at h2
  have hfalse := (advantage_ccaGame_ccaRejectGame_le_sum E ctBound Q adversary false n hq
    hctBound).trans (sum_succProbability_ccaToCIAtIndexAdversary_le E ctBound Q false adversary n)
  have htrue := (advantage_ccaGame_ccaRejectGame_le_sum E ctBound Q adversary true n hq
    hctBound).trans (sum_succProbability_ccaToCIAtIndexAdversary_le E ctBound Q true adversary n)
  linarith

/-- Running `ccaToCIHiddenBitAdversary` in `ciGame` averages `ccaToCIAdversary` uniformly over
`bit : Bool`. -/
theorem eval_ciGame_ccaToCIHiddenBitAdversary (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n) =
      (PMF.uniformOfFintype Bool).bind
        (fun bit => ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q bit adversary) n)) := by
  simp only [ciGame, ccaToCIHiddenBitAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret]
  have hsample (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
        (do
          let bits ← ProbOracleComp.sample (BitString.sampleList 1)
          if bits == [true] then
            ccaToCIAdversary ctBound Q true adversary n []
          else
            ccaToCIAdversary ctBound Q false adversary n [])).run []).bind
        (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      (PMF.uniformOfFintype Bool).bind (fun bit =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
          (ccaToCIAdversary ctBound Q bit adversary n [])).run []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) := by
    rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
      BitString.eval_sampleList, BitString.uniformList_succ 0, BitString.uniformList_zero]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map,
      PMF.bind_bind, PMF.pure_bind]
    congr 1
    funext bit
    cases bit <;> rfl
  simp only [hsample]
  exact PMF.bind_comm _ _ _

/-- **Single-adversary quantitative AE $\Rightarrow$ CCA bound** ([BonehShoup2023], Section 9.2.3,
Theorem 9.1, equation (9.3) and proof on printed pp. 363–364): using `ccaToCIHiddenBitAdversary` to
sample the hidden challenge bit uniformly yields factor `2 * dyadicSize (Q n) ≤ 4 * Q n + 4` (over
the total query budget `Q n`, vs. `2 * Qd` over decryption queries in (9.3)) on the single CI
adversary. -/
theorem advantage_ccaGame_le_two_mul (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      2 * (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) := by
  have hmain := advantage_ccaGame_le E ctBound Q adversary n hq hctBound
  have havg : 2 * (Game.succProbability
      (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ) =
      (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q false adversary) n)) : ℝ) +
      (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q true adversary) n)) : ℝ) := by
    rw [eval_ciGame_ccaToCIHiddenBitAdversary, Game.succProbability_uniform,
      NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_bool,
      Fintype.sum_bool]
    ring
  have hd : 2 * (dyadicSize (Q n) : ℝ) *
      (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ) =
      (dyadicSize (Q n) : ℝ) *
        (2 * (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ)) := by
    ring
  rw [hd, havg]
  linarith

/-- **Authenticated encryption implies adaptive CCA security** ([BonehShoup2023], Section 9.2.3,
Theorem 9.1, printed pp. 363–365): every symmetric cipher satisfying `AuthenticatedEncryption`
(`INDCPA ∧ CiphertextIntegrity`) also satisfies `INDCCA`. -/
theorem AuthenticatedEncryption.indcca {E : SymmetricCipher} (hAE : E.AuthenticatedEncryption) :
    E.INDCCA := by
  rcases hAE with ⟨hcpa, hci⟩
  intro adversary hadversary
  obtain ⟨ck, dk, hlenKey⟩ := E.keyGen_ppt.length_le
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
  let ctBound : ℕ → ℕ := fun n => ce * (3 * n + 2 * (ck * (n + 1) ^ dk) + 4) ^ de
  let Q : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
  have hctBoundPoly : ComputableInPolyTime ctBound encUnary encUnary := by
    dsimp only [ctBound]; polytime
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; polytime
  have hctBound (n : ℕ) (k : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
      (msg : List Bool) (hmsg : msg.length = n) (ct : List Bool)
      (hct : ct ∈ (ProbComp.eval (E.encrypt n k msg)).support) : ct.length ≤ ctBound n := by
    have hkLen := hlenKey n k hk
    have hctLen := hlenEnc (n, k, msg) ct hct
    simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkLen
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmsg] at hctLen
    exact hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
  have hq (n : ℕ) : (adversary n []).IsQueryBounded (Q n) := by
    simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1
  have hcpaNeg := hcpa (ccaToCPAAdversary ctBound adversary)
    (isOraclePPT_ccaToCPAAdversary hctBoundPoly hadversary)
  have hciNeg := hci.negligible (ccaToCIHiddenBitAdversary ctBound Q adversary)
    (isOraclePPT_ccaToCIHiddenBitAdversary hctBoundPoly hQPoly hadversary)
  have hpolyDyadic : PolynomiallyBounded (fun n => 2 * dyadicSize (Q n)) := by
    dsimp only [Q]; fun_prop
  have hsumNeg := (hciNeg.polynomiallyBounded_mul hpolyDyadic).add hcpaNeg
  refine negligible_of_le hsumNeg fun n => ?_
  rw [← NNReal.coe_le_coe]
  simpa only [Pi.add_apply, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat,
    Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
    advantage_ccaGame_le_two_mul E ctBound Q adversary n (hq n) (hctBound n)

/-! #### Encryption-Query Preservation for Theorem 9.1 Reductions -/

/-- Structural encryption-query bound for a two-channel CCA computation (`Operation = Bool`,
where `false` is the encryption channel and `true` is the decryption channel): every execution path
makes at most `Qe` encryption-oracle queries (`(false, _)`), while allowing arbitrary random-coin
queries and decryption-oracle queries ([BonehShoup2023], Section 9.2.3, Theorem 9.1,
printed p. 363). -/
abbrev IsEncryptionQueryBounded {α : Type} (program : WordOracleComp Bool α) (Qe : ℕ) : Prop :=
  OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) (fun req : Bool × List Bool => if req.1 then 0 else 1))
    program Qe

/-- Every total-query bound `program.IsQueryBounded Q` implies the encryption-query bound
`IsEncryptionQueryBounded program Q`. -/
theorem isEncryptionQueryBounded_of_isQueryBounded {α : Type}
    {program : WordOracleComp Bool α} {Q : ℕ}
    (hq : program.IsQueryBounded Q) :
    IsEncryptionQueryBounded program Q :=
  OracleComp.IsCostBounded.of_le hq fun
    | Sum.inl _ => le_rfl
    | Sum.inr ⟨op, _⟩ => by cases op <;> simp

private theorem isQueryBounded_ccaToCPAHandler (n ctBound : ℕ) (request : Bool × List Bool)
    (s : Unit) :
    (ccaToCPAHandler n ctBound request s).IsQueryBounded (if request.1 then 0 else 1) := by
  unfold ccaToCPAHandler
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · simp only [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.IsQueryBounded.query ((), request.2)
    · exact OracleComp.IsCostBounded.pure ([], ()) 1
  · simp only [↓reduceIte]
    exact OracleComp.IsCostBounded.pure ([], ()) 0

/-- **Encryption-query preservation for `ccaToCPAAdversary`** ([BonehShoup2023], Section 9.2.3,
Theorem 9.1, printed p. 363): if `adversary n []` makes at most `Qe` encryption queries, then
`ccaToCPAAdversary ctBound adversary n aux` makes at most `Qe` CPA encryption queries. -/
theorem isQueryBounded_ccaToCPAAdversary_of_isEncryptionQueryBounded
    (ctBound : ℕ → ℕ) (adversary : CCAAdversary) (n : ℕ) (aux : List Bool) {Qe : ℕ}
    (hq : IsEncryptionQueryBounded (adversary n []) Qe) :
    (ccaToCPAAdversary ctBound adversary n aux).IsQueryBounded Qe := by
  unfold ccaToCPAAdversary
  have hrun :
      ((OracleComp.interpret
        (ProbOracleComp.handler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (ccaToCPAHandler n (ctBound n)))
        (adversary n [])).run ()).IsQueryBounded Qe := by
    refine OracleComp.IsCostBounded.run_interpret (fun q s => ?_) hq ()
    cases q with
    | inl m =>
      simp only [ProbOracleComp.handler, Sum.elim_inl]
      change ((·, s) <$> ProbOracleComp.sample (ProbComp.unifFin m)).IsQueryBounded 0
      simp only [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin m)
    | inr request =>
      simp only [ProbOracleComp.handler, Sum.elim_inr]
      exact isQueryBounded_ccaToCPAHandler n (ctBound n) request s
  simpa only [bind_pure_comp, OracleComp.isCostBounded_map_iff] using hrun

/-- If `adversary n []` makes at most `Q` total oracle queries, then
`ccaToCPAAdversary ctBound adversary n aux` makes at most `Q` CPA encryption queries. -/
theorem isQueryBounded_ccaToCPAAdversary
    (ctBound : ℕ → ℕ) (adversary : CCAAdversary) (n : ℕ) (aux : List Bool) {Q : ℕ}
    (hq : (adversary n []).IsQueryBounded Q) :
    (ccaToCPAAdversary ctBound adversary n aux).IsQueryBounded Q :=
  isQueryBounded_ccaToCPAAdversary_of_isEncryptionQueryBounded ctBound adversary n aux
    (isEncryptionQueryBounded_of_isQueryBounded hq)

private theorem isQueryBounded_ccaToCIHandler (n ctBound : ℕ) (bit : Bool)
    (request : Bool × List Bool) (state : ℕ × (Bool × List Bool)) :
    (ccaToCIHandler n ctBound bit request state).IsQueryBounded (if request.1 then 0 else 1) := by
  unfold ccaToCIHandler
  by_cases hcap : state.2.1 = true
  · simp only [hcap, ↓reduceIte]
    exact OracleComp.IsCostBounded.pure _ _
  · simp only [hcap, Bool.false_eq_true, ↓reduceIte]
    by_cases hzero : (state.1 == 0) = true
    · simp only [hzero, ↓reduceIte]
      cases hreq : request.1 <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;>
        exact OracleComp.IsCostBounded.pure _ _
    · simp only [hzero, Bool.false_eq_true, ↓reduceIte]
      cases hreq : request.1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hlen : (((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true
        · simp only [hlen, ↓reduceIte, OracleComp.isCostBounded_map_iff]
          exact ProbOracleComp.IsQueryBounded.query _
        · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
          exact OracleComp.IsCostBounded.pure _ 1
      · simp only [↓reduceIte]
        exact OracleComp.IsCostBounded.pure _ 0

/-- **Encryption-query preservation for `ccaToCIAtIndexAdversary`** ([BonehShoup2023],
Section 9.2.3, Theorem 9.1, printed p. 363): if `adversary n []` makes at most `Qe` encryption
queries, then `ccaToCIAtIndexAdversary ctBound j bit adversary n aux` makes at most `Qe` CI
encryption queries. -/
theorem isQueryBounded_ccaToCIAtIndexAdversary_of_isEncryptionQueryBounded
    (ctBound : ℕ → ℕ) (j : ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Qe : ℕ}
    (hq : IsEncryptionQueryBounded (adversary n []) Qe) :
    (ccaToCIAtIndexAdversary ctBound j bit adversary n aux).IsQueryBounded Qe := by
  unfold ccaToCIAtIndexAdversary
  have hrun :
      ((OracleComp.interpret
        (ProbOracleComp.handler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (ccaToCIHandler n (ctBound n) bit))
        (adversary n [])).run (j, (false, []))).IsQueryBounded Qe := by
    refine OracleComp.IsCostBounded.run_interpret (fun q state => ?_) hq (j, (false, []))
    cases q with
    | inl m =>
      simp only [ProbOracleComp.handler, Sum.elim_inl]
      change ((·, state) <$> ProbOracleComp.sample (ProbComp.unifFin m)).IsQueryBounded 0
      simp only [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin m)
    | inr request =>
      simp only [ProbOracleComp.handler, Sum.elim_inr]
      exact isQueryBounded_ccaToCIHandler n (ctBound n) bit request state
  simpa only [bind_pure_comp, OracleComp.isCostBounded_map_iff] using hrun

/-- If `adversary n []` makes at most `Q` total oracle queries, then
`ccaToCIAtIndexAdversary ctBound j bit adversary n aux` makes at most `Q` CI encryption queries. -/
theorem isQueryBounded_ccaToCIAtIndexAdversary
    (ctBound : ℕ → ℕ) (j : ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Q : ℕ}
    (hq : (adversary n []).IsQueryBounded Q) :
    (ccaToCIAtIndexAdversary ctBound j bit adversary n aux).IsQueryBounded Q :=
  isQueryBounded_ccaToCIAtIndexAdversary_of_isEncryptionQueryBounded ctBound j bit adversary n aux
    (isEncryptionQueryBounded_of_isQueryBounded hq)

/-- **Encryption-query preservation for `ccaToCIAdversary`** ([BonehShoup2023], Section 9.2.3,
Theorem 9.1, printed p. 363): if `adversary n []` makes at most `Qe` encryption queries, then
`ccaToCIAdversary ctBound Q bit adversary n aux` makes at most `Qe` CI encryption queries. -/
theorem isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded
    (ctBound Q : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Qe : ℕ}
    (hq : IsEncryptionQueryBounded (adversary n []) Qe) :
    (ccaToCIAdversary ctBound Q bit adversary n aux).IsQueryBounded Qe := by
  unfold ccaToCIAdversary
  simpa only [Nat.zero_add] using
    (ProbOracleComp.IsQueryBounded.sample (ProbComp.sampleDyadicIndex (Q n))).bind fun j =>
      isQueryBounded_ccaToCIAtIndexAdversary_of_isEncryptionQueryBounded
        ctBound j bit adversary n aux hq

/-- If `adversary n []` makes at most `Q'` total oracle queries, then
`ccaToCIAdversary ctBound Q bit adversary n aux` makes at most `Q'` CI encryption queries. -/
theorem isQueryBounded_ccaToCIAdversary
    (ctBound Q : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Q' : ℕ}
    (hq : (adversary n []).IsQueryBounded Q') :
    (ccaToCIAdversary ctBound Q bit adversary n aux).IsQueryBounded Q' :=
  isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded ctBound Q bit adversary n aux
    (isEncryptionQueryBounded_of_isQueryBounded hq)

/-- **Encryption-query preservation for `ccaToCIHiddenBitAdversary`** ([BonehShoup2023],
Section 9.2.3, Theorem 9.1, printed p. 363): if `adversary n []` makes at most `Qe` encryption
queries, then `ccaToCIHiddenBitAdversary ctBound Q adversary n aux` makes at most `Qe` CI
encryption queries. -/
theorem isQueryBounded_ccaToCIHiddenBitAdversary_of_isEncryptionQueryBounded
    (ctBound Q : ℕ → ℕ) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Qe : ℕ}
    (hq : IsEncryptionQueryBounded (adversary n []) Qe) :
    (ccaToCIHiddenBitAdversary ctBound Q adversary n aux).IsQueryBounded Qe := by
  unfold ccaToCIHiddenBitAdversary
  simpa only [Nat.zero_add] using
    (ProbOracleComp.IsQueryBounded.sample (BitString.sampleList 1)).bind fun bits => by
      split_ifs
      · exact isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded
          ctBound Q true adversary n aux hq
      · exact isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded
          ctBound Q false adversary n aux hq

/-- If `adversary n []` makes at most `Q'` total oracle queries, then
`ccaToCIHiddenBitAdversary ctBound Q adversary n aux` makes at most `Q'` CI encryption queries. -/
theorem isQueryBounded_ccaToCIHiddenBitAdversary
    (ctBound Q : ℕ → ℕ) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Q' : ℕ}
    (hq : (adversary n []).IsQueryBounded Q') :
    (ccaToCIHiddenBitAdversary ctBound Q adversary n aux).IsQueryBounded Q' :=
  isQueryBounded_ccaToCIHiddenBitAdversary_of_isEncryptionQueryBounded ctBound Q adversary n aux
    (isEncryptionQueryBounded_of_isQueryBounded hq)

/-! ### One-Time Authenticated Encryption Implies One-Time CCA Security (Boneh–Shoup Theorem 9.1) -/

/-- Hybrid two-channel oracle for the one-time Game 1 in the proof of [BonehShoup2023],
Theorem 9.1 (Section 9.2.3, printed pp. 363–364): encryption queries `(false, req)` behave
identically to `oneTimeCCAOracle`, whereas every decryption query `(true, _)` immediately returns
`[]` (rejection) without invoking `decrypt`. -/
noncomputable def oneTimeCCARejectOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      return ([], queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if queriedCiphertexts.isEmpty && (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, [ct])
      else
        return ([], queriedCiphertexts)

/-- The one-time all-reject hybrid CCA experiment (one-time Game 1 in [BonehShoup2023],
Section 9.2.3, Theorem 9.1): sample `k ← E.keyGen n` and run `adversary n []` against
`E.oneTimeCCARejectOracle n k bit`. -/
noncomputable def ccaOneTimeRejectGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.oneTimeCCARejectOracle n k bit)) (adversary n [])).run []
  return out.1

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ccaToCPAAdversary ctBound adversary` in `cpaOneTimeGame` has the exact same output
distribution as `ccaOneTimeRejectGame adversary` ([BonehShoup2023], Section 9.2.3, Theorem 9.1). -/
theorem eval_cpaOneTimeGame_ccaToCPAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.ccaOneTimeRejectGame adversary bit n) := by
  simp only [cpaOneTimeGame, ccaOneTimeRejectGame, ccaToCPAAdversary, ProbComp.eval_bind,
    ProbComp.eval_pure]
  apply PMF.bind_congr_on_support
  intro k hk
  simp only [ProbOracleComp.eval_run_interpret]
  rw [OracleComp.interpret_bind, StateT.run_bind]
  simp only [StateT.run_pure, OracleComp.interpret_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.run_interpret_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (fun request queried => ProbComp.eval (E.oneTimeCCARejectOracle n k bit request queried))
    (fun request state =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCPAEncryptionOracle n k bit q s)))
        ((ccaToCPAHandler n (ctBound n) request).run state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun queried : List (List Bool) => ((), !queried.isEmpty))
    (fun request queried => by
      change (ProbComp.eval (E.oneTimeCCARejectOracle n k bit request queried)).map
          (fun x => (x.1, (), !x.2.isEmpty)) =
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.oneTimeCPAEncryptionOracle n k bit q s)))
          (ccaToCPAHandler n (ctBound n) request ())).run (!queried.isEmpty)).map
          (fun result => (result.1.1, result.1.2, result.2))
      cases hreq : request.1
      · simp only [oneTimeCCARejectOracle, ccaToCPAHandler, hreq, Bool.false_eq_true, ↓reduceIte]
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte, Functor.map_map, OracleComp.interpret_map,
            StateT.run_map, ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map,
            oneTimeCPAEncryptionOracle]
          dsimp only [StateT.run]
          simp only [Bool.not_not]
          by_cases hemp : queried.isEmpty = true
          · have hcond : (queried.isEmpty && ((unframe request.2).length == n) &&
                ((dropFrame request.2).length == n)) = true := by
              rw [hemp, Bool.true_and, hlenEq]
            simp only [hcond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
              PMF.map_bind, PMF.pure_map, List.isEmpty_cons, Bool.not_false]
            simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
            have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
              cases bit <;> simp [hlenEq]
            apply PMF.bind_congr_on_support
            intro ct hct
            rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
          · have hcond : (queried.isEmpty && ((unframe request.2).length == n) &&
                ((dropFrame request.2).length == n)) = false := by
              rw [Bool.eq_false_iff.mpr hemp, Bool.false_and, Bool.false_and]
            simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
              PMF.pure_map, List.take_nil]
        · have hcond : (queried.isEmpty && ((unframe request.2).length == n) &&
              ((dropFrame request.2).length == n)) = false := by
            rw [Bool.and_assoc, Bool.eq_false_iff.mpr hlenEq, Bool.and_false]
          simp only [hcond, hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
            PMF.pure_map]
      · simp only [oneTimeCCARejectOracle, ccaToCPAHandler, hreq, ↓reduceIte, ProbComp.eval_pure,
          OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
          PMF.pure_map])
    (adversary n []) []
  dsimp only [List.isEmpty, not] at hsim
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

private noncomputable def oneTimeCCAWithBadOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) :
    StateT (List (List Bool) × Bool) ProbComp (List Bool) :=
  fun state =>
    if request.1 then
      if state.1.contains request.2 then
        return ([], state)
      else
        let dec := E.decrypt n k request.2
        return (encOption encBits dec, (state.1, state.2 || dec.isSome))
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if state.1.isEmpty && (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ([ct], state.2))
      else
        return ([], state)

private noncomputable def oneTimeCCARejectWithBadOracle (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) (request : Bool × List Bool) :
    StateT (List (List Bool) × Bool) ProbComp (List Bool) :=
  fun state =>
    if request.1 then
      if state.1.contains request.2 then
        return ([], state)
      else
        let dec := E.decrypt n k request.2
        return ([], (state.1, state.2 || dec.isSome))
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if state.1.isEmpty && (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ([ct], state.2))
      else
        return ([], state)

private theorem run_oneTimeCCAWithBadOracle_map_fst (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (program : WordOracleComp Bool Bool) (queried : List (List Bool)) (bad : Bool) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.oneTimeCCAWithBadOracle n k bit q s)))
      program).run (queried, bad)).map (fun (a, s) => (a, s.1)) =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCCAOracle n k bit q s)))
        program).run queried := by
  refine ProbOracleComp.run_interpret_map_state
    (fun q s => ProbComp.eval (E.oneTimeCCAWithBadOracle n k bit q s))
    (fun q s => ProbComp.eval (E.oneTimeCCAOracle n k bit q s))
    Prod.fst ?_ program (queried, bad)
  intro request state
  cases hreq : request.1
  · simp only [oneTimeCCAWithBadOracle, oneTimeCCAOracle, hreq, Bool.false_eq_true, ↓reduceIte]
    by_cases hlenEq : (state.1.isEmpty && ((unframe request.2).length == n) &&
        ((dropFrame request.2).length == n)) = true
    · simp [hlenEq, PMF.map_comp, Function.comp_def]
    · simp [hlenEq, PMF.pure_map]
  · simp only [oneTimeCCAWithBadOracle, oneTimeCCAOracle, hreq, ↓reduceIte]
    split_ifs <;> simp [PMF.pure_map]

private theorem run_oneTimeCCARejectWithBadOracle_map_fst (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) (program : WordOracleComp Bool Bool)
    (queried : List (List Bool)) (bad : Bool) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit q s)))
      program).run (queried, bad)).map (fun (a, s) => (a, s.1)) =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCCARejectOracle n k bit q s)))
        program).run queried := by
  refine ProbOracleComp.run_interpret_map_state
    (fun q s => ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit q s))
    (fun q s => ProbComp.eval (E.oneTimeCCARejectOracle n k bit q s))
    Prod.fst ?_ program (queried, bad)
  intro request state
  cases hreq : request.1
  · simp only [oneTimeCCARejectWithBadOracle, oneTimeCCARejectOracle, hreq, Bool.false_eq_true,
      ↓reduceIte]
    by_cases hlenEq : (state.1.isEmpty && ((unframe request.2).length == n) &&
        ((dropFrame request.2).length == n)) = true
    · simp [hlenEq, PMF.map_comp, Function.comp_def]
    · simp [hlenEq, PMF.pure_map]
  · simp only [oneTimeCCARejectWithBadOracle, oneTimeCCARejectOracle, hreq, ↓reduceIte]
    split_ifs <;> simp [PMF.pure_map]

private theorem identicalUntilBad_oneTimeCCARejectWithBad_oneTimeCCAWithBad
    (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool) :
    OracleComp.IdenticalUntilBad
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit q s)))
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.oneTimeCCAWithBadOracle n k bit q s)))
      (fun s => s.2 = true) where
  agree q s hs a s' hs' := by
    cases q with
    | inl m => rfl
    | inr request =>
      simp only [ProbOracleComp.handler]
      cases hreq : request.1
      · simp only [oneTimeCCARejectWithBadOracle, oneTimeCCAWithBadOracle, hreq,
          Bool.false_eq_true, ↓reduceIte]
      · simp only [oneTimeCCARejectWithBadOracle, oneTimeCCAWithBadOracle, hreq, ↓reduceIte]
        split_ifs with hmem
        · rfl
        · cases hdec : E.decrypt n k request.2 with
          | none =>
            simp [Option.isSome, encOption]
          | some msg =>
            have hne : s' ≠ (s.1, true) := fun h => hs' (congrArg Prod.snd h)
            simp [Option.isSome, ProbComp.eval_pure, PMF.pure_apply, hne]
  absorb_first q s hs x hx := by
    cases q with
    | inl m =>
      change x ∈ ((ProbComp.unifOracle m).map (·, s)).support at hx
      obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr request =>
      simp only [ProbOracleComp.handler, oneTimeCCARejectWithBadOracle] at hx
      cases hreq : request.1
      · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hx
        by_cases hlenEq : (s.1.isEmpty && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true
        · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hx
          obtain ⟨_, _, rfl⟩ := hx
          exact hs
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            PMF.mem_support_pure_iff] at hx
          subst x
          exact hs
      · simp only [hreq, ↓reduceIte] at hx
        split_ifs at hx <;>
          simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx <;>
          subst x <;>
          simp [hs]
  absorb_second q s hs x hx := by
    cases q with
    | inl m =>
      change x ∈ ((ProbComp.unifOracle m).map (·, s)).support at hx
      obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr request =>
      simp only [ProbOracleComp.handler, oneTimeCCAWithBadOracle] at hx
      cases hreq : request.1
      · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hx
        by_cases hlenEq : (s.1.isEmpty && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true
        · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hx
          obtain ⟨_, _, rfl⟩ := hx
          exact hs
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            PMF.mem_support_pure_iff] at hx
          subst x
          exact hs
      · simp only [hreq, ↓reduceIte] at hx
        split_ifs at hx <;>
          simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx <;>
          subst x <;>
          simp [hs]

private noncomputable def oneTimeCCAToCICombinedOracle (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) (request : Bool × List Bool) :
    StateT ((ℕ × (Bool × List Bool)) × List (List Bool)) ProbComp (List Bool) :=
  fun state =>
    if state.1.2.1 then
      return ([], ((state.1.1, (true, state.1.2.2)), state.2))
    else
      if state.1.1 == 0 then
        if request.1 then
          return ([], ((0, (true, request.2)), state.2))
        else
          return ([], ((0, (true, [])), state.2))
      else
        if request.1 then
          return ([], ((state.1.1 - 1, (false, [])), state.2))
        else
          let m0 := unframe request.2
          let m1 := dropFrame request.2
          if state.2.isEmpty && (m0.length == n) && (m1.length == n) then do
            let ct ← E.encrypt n k (if bit then m1 else m0)
            return (ct, ((state.1.1 - 1, (false, [])), [ct]))
          else
            return ([], ((state.1.1 - 1, (false, [])), state.2))

private theorem oneTimeCICombined_captured_bind_eq_one {α : Type} (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) (program : WordOracleComp Bool α) (rem : ℕ)
    (ct : List Bool) (queried : List (List Bool))
    (hwin : (!queried.contains ct && (E.decrypt n k ct).isSome) = true) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit q s)))
      program).run ((rem, (true, ct)), queried)).bind
      (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome)) true =
      1 := by
  refine le_antisymm (PMF.coe_le_one _ _) (PMF.le_bind_apply_on_support _ fun x hx => ?_)
  have hinv := ProbOracleComp.run_interpret_invariant
    (fun q s => ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit q s))
    (fun s => s.1.2 = (true, ct) ∧ s.2 = queried)
    (fun q s ⟨hcap, hq⟩ a s' hs' => by
      have hcap1 : s.1.2.1 = true := by rw [hcap]
      have hcap2 : s.1.2.2 = ct := by rw [hcap]
      simp only [oneTimeCCAToCICombinedOracle, hcap1, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hs'
      cases hs'
      exact ⟨by simp [hcap2], hq⟩)
    program ((rem, (true, ct)), queried) ⟨rfl, rfl⟩ x.1 x.2 hx
  have hct : x.2.1.2.2 = ct := by rw [hinv.1]
  rw [hct, hinv.2, hwin, PMF.pure_apply_self]

private theorem eval_oneTimeCCARejectWithBadOracle_false (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) (request : Bool × List Bool) (queried : List (List Bool)) :
    ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit request (queried, false)) =
      if request.1 then
        if queried.contains request.2 then
          PMF.pure ([], (queried, false))
        else
          PMF.pure ([], (queried, (E.decrypt n k request.2).isSome))
      else
        if (queried.isEmpty && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true then
          (ProbComp.eval (E.encrypt n k
            (if bit then dropFrame request.2 else unframe request.2))).bind
            (fun ct => PMF.pure (ct, ([ct], false)))
        else
          PMF.pure ([], (queried, false)) := by
  unfold oneTimeCCARejectWithBadOracle
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  · simp only [↓reduceIte, Bool.false_or]
    split_ifs <;> simp only [ProbComp.eval_pure]

private theorem eval_oneTimeCCAToCICombinedOracle_succ_false (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) (request : Bool × List Bool) (j : ℕ)
    (queried : List (List Bool)) :
    ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit request ((j + 1, (false, [])), queried)) =
      if request.1 then
        PMF.pure ([], ((j, (false, [])), queried))
      else
        if (queried.isEmpty && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true then
          (ProbComp.eval (E.encrypt n k
            (if bit then dropFrame request.2 else unframe request.2))).bind
            (fun ct => PMF.pure (ct, ((j, (false, [])), [ct])))
        else
          PMF.pure ([], ((j, (false, [])), queried)) := by
  have hne : ((j + 1 == 0) = true) ↔ False := by simp
  unfold oneTimeCCAToCICombinedOracle
  simp only [Bool.false_eq_true, ↓reduceIte, hne, Nat.add_sub_cancel]
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  · simp only [↓reduceIte, ProbComp.eval_pure]

private theorem eval_oneTimeCCAToCICombinedOracle_zero_false (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) (request : Bool × List Bool) (queried : List (List Bool)) :
    ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit request ((0, (false, [])), queried)) =
      if request.1 then
        PMF.pure ([], ((0, (true, request.2)), queried))
      else
        PMF.pure ([], ((0, (true, [])), queried)) := by
  unfold oneTimeCCAToCICombinedOracle
  cases hreq : request.1 <;>
    simp [ProbComp.eval_pure]

private theorem bad_oneTimeCCARejectWithBad_le_sum_oneTimeCICombined {α : Type}
    (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    {program : WordOracleComp Bool α} {Q : ℕ}
    (hq : program.IsQueryBounded Q) (queried : List (List Bool)) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit q s)))
      program).run (queried, false)).toOuterMeasure {x | x.2.2 = true} ≤
      ∑ j ∈ Finset.range (Q + 1),
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit q s)))
          program).run ((j, (false, [])), queried)).bind
          (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome))
          true := by
  induction hq generalizing queried with
  | pure a Q =>
    simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte, zero_le]
  | liftBind q cont Q hcont ih =>
    cases q with
    | inl m =>
      simp only [Sum.elim_inl, Nat.add_zero, OracleComp.run_interpret_bind,
        OracleComp.run_interpret_query, ProbOracleComp.handler, StateT.lift,
        Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.toOuterMeasure_bind_apply, PMF.bind_apply]
      calc ∑' a : Fin (m + 1), ProbComp.unifOracle m a *
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                (fun q s => ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit q s)))
              (cont a)).run (queried, false)).toOuterMeasure {x | x.2.2 = true}
          ≤ ∑' a : Fin (m + 1), ProbComp.unifOracle m a *
              ∑ j ∈ Finset.range (Q + 1),
                ((OracleComp.interpret
                  (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                    (fun q s => ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit q s)))
                  (cont a)).run ((j, (false, [])), queried)).bind
                  (fun x =>
                    PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome))
                  true :=
            tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (ih a queried) zero_le
        _ = _ := by
          simp only [Finset.mul_sum]
          rw [ennreal_tsum_finsetSum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [← PMF.bind_apply]
    | inr request =>
      simp only [Sum.elim_inr, OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        ProbOracleComp.handler]
      rw [Finset.sum_range_succ']
      simp only [eval_oneTimeCCARejectWithBadOracle_false,
        eval_oneTimeCCAToCICombinedOracle_succ_false,
        eval_oneTimeCCAToCICombinedOracle_zero_false]
      cases hreq : request.1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hlenEq : (queried.isEmpty && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true
        · simp only [hlenEq, ↓reduceIte,
            Probability.PMF.monad_bind_eq_bind,
            PMF.bind_bind, PMF.pure_bind, PMF.toOuterMeasure_bind_apply]
          have hle : ∑' ct : List Bool,
              ProbComp.eval
                (E.encrypt n k (if bit then dropFrame request.2 else unframe request.2)) ct *
                ((OracleComp.interpret
                  (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                    (fun q s => ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit q s)))
                  (cont ct)).run ([ct], false)).toOuterMeasure {x | x.2.2 = true} ≤
              ∑ j ∈ Finset.range (Q + 1),
                (ProbComp.eval (E.encrypt n k
                  (if bit then dropFrame request.2 else unframe request.2))).bind (fun ct =>
                    ((OracleComp.interpret
                      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                        (fun q s => ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit q s)))
                      (cont ct)).run ((j, (false, [])), [ct])).bind
                      (fun x =>
                        PMF.pure (!x.2.2.contains x.2.1.2.2 &&
                          (E.decrypt n k x.2.1.2.2).isSome)))
                  true := by
            calc ∑' ct : List Bool,
                  ProbComp.eval
                    (E.encrypt n k (if bit then dropFrame request.2 else unframe request.2)) ct *
                    ((OracleComp.interpret
                      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                        (fun q s => ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit q s)))
                      (cont ct)).run ([ct], false)).toOuterMeasure {x | x.2.2 = true}
                ≤ ∑' ct : List Bool,
                    ProbComp.eval
                      (E.encrypt n k (if bit then dropFrame request.2 else unframe request.2)) ct *
                      ∑ j ∈ Finset.range (Q + 1),
                        ((OracleComp.interpret
                          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                            (fun q s => ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit q s)))
                          (cont ct)).run ((j, (false, [])), [ct])).bind
                          (fun x =>
                            PMF.pure (!x.2.2.contains x.2.1.2.2 &&
                              (E.decrypt n k x.2.1.2.2).isSome))
                          true :=
                  tsum_le_tsum fun ct =>
                    mul_le_mul_of_nonneg_left (ih ct [ct]) zero_le
              _ = _ := by
                simp only [Finset.mul_sum]
                rw [ennreal_tsum_finsetSum]
                refine Finset.sum_congr rfl fun j _ => ?_
                simp only [PMF.bind_apply]
          exact hle.trans le_self_add
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte,
            Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
          exact (ih [] queried).trans le_self_add
      · simp only [↓reduceIte,
          Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
        by_cases hmem : queried.contains request.2 = true
        · simp only [hmem, ↓reduceIte, PMF.pure_bind]
          exact (ih [] queried).trans le_self_add
        · simp only [hmem, Bool.false_eq_true, ↓reduceIte, PMF.pure_bind]
          by_cases hsome : (E.decrypt n k request.2).isSome = true
          · simp only [hsome]
            have hwin :
                (!queried.contains request.2 && (E.decrypt n k request.2).isSome) = true := by
              rw [Bool.eq_false_iff.mpr hmem, hsome]
              rfl
            rw [oneTimeCICombined_captured_bind_eq_one E n k bit (cont []) 0 request.2 queried hwin]
            exact (Cslib.Probability.PMF.toOuterMeasure_le_one _ _).trans le_add_self
          · have hnotSome : (E.decrypt n k request.2).isSome = false :=
              Bool.eq_false_iff.mpr hsome
            simp only [hnotSome]
            exact (ih [] queried).trans le_self_add

private theorem eval_ciOneTimeGame_ccaToCIAtIndexAdversary_key (E : SymmetricCipher)
    (ctBound : ℕ → ℕ) (j : ℕ) (bit : Bool) (adversary : CCAAdversary) (n : ℕ) (k : List Bool)
    (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.oneTimeCIEncryptionOracle n k q s)))
      (ccaToCIAtIndexAdversary ctBound j bit adversary n [])).run []).bind
      (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit q s)))
        (adversary n [])).run ((j, (false, [])), [])).bind
        (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome)) := by
  unfold ccaToCIAtIndexAdversary
  rw [OracleComp.interpret_bind, StateT.run_bind]
  simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.run_interpret_run_interpret]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  congr 2
  funext q state
  cases q with
  | inl m => rfl
  | inr request =>
    simp only [ProbOracleComp.handler]
    change ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.oneTimeCIEncryptionOracle n k q s)))
      (ccaToCIHandler n (ctBound n) bit request state.1)).run state.2).map
      (fun result => (result.1.1, result.1.2, result.2)) =
      ProbComp.eval (E.oneTimeCCAToCICombinedOracle n k bit request state)
    unfold ccaToCIHandler oneTimeCCAToCICombinedOracle
    by_cases hcap : state.1.2.1 = true
    · simp only [hcap, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]
    · simp only [hcap, Bool.false_eq_true, ↓reduceIte]
      by_cases hzero : (state.1.1 == 0) = true
      · simp only [hzero, ↓reduceIte]
        cases hreq : request.1 <;>
          simp only [Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure,
            StateT.run_pure, Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]
      · simp only [hzero, Bool.false_eq_true, ↓reduceIte]
        cases hreq : request.1
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hlenEq : ((unframe request.2).length == n &&
              (dropFrame request.2).length == n) = true
          · simp only [hlenEq, ↓reduceIte, Functor.map_map, OracleComp.interpret_map,
              StateT.run_map, ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map,
              oneTimeCIEncryptionOracle]
            simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
            have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
              cases bit <;> simp [hlenEq]
            have hmbEq : ((if bit then dropFrame request.2 else unframe request.2).length == n) =
                true := beq_iff_eq.mpr hmbLen
            dsimp only [StateT.run]
            by_cases hemp : state.2.isEmpty = true
            · have hcond : (state.2.isEmpty && ((unframe request.2).length == n) &&
                  ((dropFrame request.2).length == n)) = true := by
                simp [hemp, hlenEq]
              have hciCond : (state.2.isEmpty &&
                  ((if bit then dropFrame request.2 else unframe request.2).length == n)) =
                  true := by
                rw [hemp, hmbEq]; rfl
              simp only [hcond, hciCond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
                PMF.map_bind, PMF.pure_map]
              apply PMF.bind_congr_on_support
              intro ct hct
              rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
            · have hcond : (state.2.isEmpty && ((unframe request.2).length == n) &&
                  ((dropFrame request.2).length == n)) = false := by
                rw [Bool.eq_false_iff.mpr hemp, Bool.false_and, Bool.false_and]
              have hciCond : (state.2.isEmpty &&
                  ((if bit then dropFrame request.2 else unframe request.2).length == n)) =
                  false := by
                rw [Bool.eq_false_iff.mpr hemp, Bool.false_and]
              simp only [hcond, hciCond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
                PMF.pure_map, List.take_nil]
          · have hcond : (state.2.isEmpty && ((unframe request.2).length == n) &&
                ((dropFrame request.2).length == n)) = false := by
              rw [Bool.and_assoc, Bool.eq_false_iff.mpr hlenEq, Bool.and_false]
            simp only [hcond, hlenEq, Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure,
              StateT.run_pure, Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]
        · simp only [↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
            Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]

private theorem advantage_ccaOneTimeGame_ccaOneTimeRejectGame_le_sum (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaOneTimeGame adversary bit n))
        (ProbComp.eval (E.ccaOneTimeRejectGame adversary bit n)) : ℝ) ≤
      ∑ j ∈ Finset.range (Q n + 1),
        (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) :
          ℝ) := by
  have hccaEq (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCCAOracle n k bit q s)))
        (adversary n [])).run []).bind (fun out => PMF.pure out.1) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCCAWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) := by
    rw [← run_oneTimeCCAWithBadOracle_map_fst E n k bit (adversary n []) [] false,
      PMF.bind_map, Function.comp_def]
  have hrejEq (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCCARejectOracle n k bit q s)))
        (adversary n [])).run []).bind (fun out => PMF.pure out.1) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) := by
    rw [← run_oneTimeCCARejectWithBadOracle_map_fst E n k bit (adversary n []) [] false,
      PMF.bind_map, Function.comp_def]
  set pCCA := ProbComp.eval (E.ccaOneTimeGame adversary bit n) true
  set pRej := ProbComp.eval (E.ccaOneTimeRejectGame adversary bit n) true
  set pSum : ℝ≥0∞ := ∑ j ∈ Finset.range (Q n + 1),
    ProbComp.eval (E.ciOneTimeGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n) true
  have hsum_eq : pSum = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ∑ j ∈ Finset.range (Q n + 1),
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.oneTimeCIEncryptionOracle n k q s)))
          (ccaToCIAtIndexAdversary ctBound j bit adversary n [])).run []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) true := by
    simp only [pSum, ciOneTimeGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret]
    conv_lhs =>
      arg 2; ext j
      rw [PMF.bind_apply]
    rw [← ennreal_tsum_finsetSum]
    refine tsum_congr fun k => ?_
    rw [Finset.mul_sum]
  have hCCA_eq : pCCA = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCCAWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) true := by
    simp only [pCCA, ccaOneTimeGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret, hccaEq]
    exact PMF.bind_apply _ _ _
  have hRej_eq : pRej = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCCARejectWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) true := by
    simp only [pRej, ccaOneTimeRejectGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret, hrejEq]
    exact PMF.bind_apply _ _ _
  have hle1 : pCCA ≤ pRej + pSum := by
    rw [hCCA_eq, hRej_eq, hsum_eq, ← tsum_add]
    refine tsum_le_tsum fun k => ?_
    rw [← mul_add]
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hiub := (identicalUntilBad_oneTimeCCARejectWithBad_oneTimeCCAWithBad E n k bit).symm
      have hstep := hiub.bind_apply_le (adversary n []) ([], false) (fun out => PMF.pure out.1) true
      rw [← (identicalUntilBad_oneTimeCCARejectWithBad_oneTimeCCAWithBad E n k bit).bad_eq] at hstep
      refine hstep.trans (add_le_add le_rfl ?_)
      refine (bad_oneTimeCCARejectWithBad_le_sum_oneTimeCICombined E n k bit hq []).trans
        (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eval_ciOneTimeGame_ccaToCIAtIndexAdversary_key E ctBound j bit adversary n k hk hctBound]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hk, zero_mul, zero_mul]
  have hle2 : pRej ≤ pCCA + pSum := by
    rw [hCCA_eq, hRej_eq, hsum_eq, ← tsum_add]
    refine tsum_le_tsum fun k => ?_
    rw [← mul_add]
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hiub := identicalUntilBad_oneTimeCCARejectWithBad_oneTimeCCAWithBad E n k bit
      have hstep := hiub.bind_apply_le (adversary n []) ([], false) (fun out => PMF.pure out.1) true
      refine hstep.trans (add_le_add le_rfl ?_)
      refine (bad_oneTimeCCARejectWithBad_le_sum_oneTimeCICombined E n k bit hq []).trans
        (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eval_ciOneTimeGame_ccaToCIAtIndexAdversary_key E ctBound j bit adversary n k hk hctBound]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hk, zero_mul, zero_mul]
  have hpSum_ne_top : pSum ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ => PMF.apply_ne_top _ _
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hpSum_ne_top⟩) hle1
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hpSum_ne_top⟩) hle2
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) hpSum_ne_top] at h1 h2
  have habs : |pCCA.toReal - pRej.toReal| ≤ pSum.toReal :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  rw [Game.coe_advantage]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, pCCA, pRej, pSum,
    ENNReal.toReal_sum (fun j _ => PMF.apply_ne_top _ _)] using habs

/-- Running `ccaToCIAdversary` in `ciOneTimeGame` averages `ccaToCIAtIndexAdversary` uniformly over
`Fin (dyadicSize (Q n))`. -/
theorem eval_ciOneTimeGame_ccaToCIAdversary (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (bit : Bool) (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Q bit adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind
        (fun i =>
          ProbComp.eval
            (E.ciOneTimeGame (ccaToCIAtIndexAdversary ctBound i.val bit adversary) n)) := by
  simp only [ciOneTimeGame, ccaToCIAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret]
  have hsample (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCIEncryptionOracle n k q s)))
        (do
          let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))
          ccaToCIAtIndexAdversary ctBound j bit adversary n [])).run []).bind
        (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind (fun i =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.oneTimeCIEncryptionOracle n k q s)))
          (ccaToCIAtIndexAdversary ctBound i.val bit adversary n [])).run []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) := by
    rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
      ProbComp.eval_sampleDyadicIndex]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind]
  simp only [hsample]
  exact PMF.bind_comm _ _ _

private theorem sum_succProbability_ciOneTimeGame_ccaToCIAtIndexAdversary_le (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary) (n : ℕ) :
    (∑ j ∈ Finset.range (Q n + 1),
      (Game.succProbability
        (ProbComp.eval (E.ciOneTimeGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) :
        ℝ)) ≤
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Q bit adversary) n)) : ℝ) := by
  have hcap : (dyadicSize (Q n) : ℝ) ≠ 0 := by exact_mod_cast (dyadicSize_pos (Q n)).ne'
  rw [eval_ciOneTimeGame_ccaToCIAdversary, Game.succProbability_uniform, NNReal.coe_div,
    NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_fin, mul_div_cancel₀ _ hcap,
    Fin.sum_univ_eq_sum_range
      (fun j => (Game.succProbability
        (ProbComp.eval (E.ciOneTimeGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) :
        ℝ))]
  have hsub : Finset.range (Q n + 1) ⊆ Finset.range (dyadicSize (Q n)) := by
    intro x hx
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le (lt_dyadicSize (Q n)))
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => NNReal.coe_nonneg _

/-- **Quantitative 1AE $\Rightarrow$ 1CCA bound** ([BonehShoup2023], Section 9.2.3, Theorem 9.1,
printed pp. 363–365): for any `CCAAdversary` making at most `Q n` total oracle queries at security
parameter `n`, the one-time CCA distinguishing advantage in `ccaOneTimeGame` is bounded by the
one-time CPA advantage of `ccaToCPAAdversary` in `cpaOneTimeGame` plus `dyadicSize (Q n)` times the
one-time ciphertext-integrity winning probabilities of `ccaToCIAdversary` in `ciOneTimeGame` for
`bit = false` and `bit = true`. -/
theorem advantage_ccaOneTimeGame_le (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaOneTimeGame adversary false n))
        (ProbComp.eval (E.ccaOneTimeGame adversary true n)) : ℝ) ≤
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Q false adversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) +
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Q true adversary) n)) : ℝ) := by
  have h1 : (Game.advantage (ProbComp.eval (E.ccaOneTimeGame adversary false n))
      (ProbComp.eval (E.ccaOneTimeGame adversary true n)) : ℝ) ≤
      (Game.advantage (ProbComp.eval (E.ccaOneTimeGame adversary false n))
        (ProbComp.eval (E.ccaOneTimeRejectGame adversary false n)) : ℝ) +
      (Game.advantage (ProbComp.eval (E.ccaOneTimeRejectGame adversary false n))
        (ProbComp.eval (E.ccaOneTimeGame adversary true n)) : ℝ) := by
    exact_mod_cast Game.advantage_triangle
      (ProbComp.eval (E.ccaOneTimeGame adversary false n))
      (ProbComp.eval (E.ccaOneTimeRejectGame adversary false n))
      (ProbComp.eval (E.ccaOneTimeGame adversary true n))
  have h2 : (Game.advantage (ProbComp.eval (E.ccaOneTimeRejectGame adversary false n))
      (ProbComp.eval (E.ccaOneTimeGame adversary true n)) : ℝ) ≤
      (Game.advantage (ProbComp.eval (E.ccaOneTimeRejectGame adversary false n))
        (ProbComp.eval (E.ccaOneTimeRejectGame adversary true n)) : ℝ) +
      (Game.advantage (ProbComp.eval (E.ccaOneTimeRejectGame adversary true n))
        (ProbComp.eval (E.ccaOneTimeGame adversary true n)) : ℝ) := by
    exact_mod_cast Game.advantage_triangle
      (ProbComp.eval (E.ccaOneTimeRejectGame adversary false n))
      (ProbComp.eval (E.ccaOneTimeRejectGame adversary true n))
      (ProbComp.eval (E.ccaOneTimeGame adversary true n))
  have hcomm : Game.advantage (ProbComp.eval (E.ccaOneTimeRejectGame adversary true n))
      (ProbComp.eval (E.ccaOneTimeGame adversary true n)) =
      Game.advantage (ProbComp.eval (E.ccaOneTimeGame adversary true n))
      (ProbComp.eval (E.ccaOneTimeRejectGame adversary true n)) := Game.advantage_comm _ _
  have hcpaEq : Game.advantage (ProbComp.eval (E.ccaOneTimeRejectGame adversary false n))
      (ProbComp.eval (E.ccaOneTimeRejectGame adversary true n)) =
      Game.advantage
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) true n)) := by
    rw [eval_cpaOneTimeGame_ccaToCPAAdversary E ctBound adversary false n hctBound,
      eval_cpaOneTimeGame_ccaToCPAAdversary E ctBound adversary true n hctBound]
  rw [hcomm, hcpaEq] at h2
  have hfalse := (advantage_ccaOneTimeGame_ccaOneTimeRejectGame_le_sum E ctBound Q adversary false n
    hq hctBound).trans
    (sum_succProbability_ciOneTimeGame_ccaToCIAtIndexAdversary_le E ctBound Q false adversary n)
  have htrue := (advantage_ccaOneTimeGame_ccaOneTimeRejectGame_le_sum E ctBound Q adversary true n
    hq hctBound).trans
    (sum_succProbability_ciOneTimeGame_ccaToCIAtIndexAdversary_le E ctBound Q true adversary n)
  linarith

/-- Running `ccaToCIHiddenBitAdversary` in `ciOneTimeGame` averages `ccaToCIAdversary` uniformly
over `bit : Bool`. -/
theorem eval_ciOneTimeGame_ccaToCIHiddenBitAdversary (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciOneTimeGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n) =
      (PMF.uniformOfFintype Bool).bind
        (fun bit =>
          ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Q bit adversary) n)) := by
  simp only [ciOneTimeGame, ccaToCIHiddenBitAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret]
  have hsample (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.oneTimeCIEncryptionOracle n k q s)))
        (do
          let bits ← ProbOracleComp.sample (BitString.sampleList 1)
          if bits == [true] then
            ccaToCIAdversary ctBound Q true adversary n []
          else
            ccaToCIAdversary ctBound Q false adversary n [])).run []).bind
        (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      (PMF.uniformOfFintype Bool).bind (fun bit =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.oneTimeCIEncryptionOracle n k q s)))
          (ccaToCIAdversary ctBound Q bit adversary n [])).run []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) := by
    rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
      BitString.eval_sampleList, BitString.uniformList_succ 0, BitString.uniformList_zero]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map,
      PMF.bind_bind, PMF.pure_bind]
    congr 1
    funext bit
    cases bit <;> rfl
  simp only [hsample]
  exact PMF.bind_comm _ _ _

/-- **Single-adversary quantitative 1AE $\Rightarrow$ 1CCA bound** ([BonehShoup2023],
Section 9.2.3, Theorem 9.1, printed pp. 363–364): using `ccaToCIHiddenBitAdversary` to sample the
hidden challenge bit uniformly yields factor `2 * dyadicSize (Q n) ≤ 4 * Q n + 4` on the single
one-time CI adversary in `ciOneTimeGame`. -/
theorem advantage_ccaOneTimeGame_le_two_mul (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaOneTimeGame adversary false n))
        (ProbComp.eval (E.ccaOneTimeGame adversary true n)) : ℝ) ≤
      2 * (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) := by
  have hmain := advantage_ccaOneTimeGame_le E ctBound Q adversary n hq hctBound
  have havg : 2 * (Game.succProbability
      (ProbComp.eval (E.ciOneTimeGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ) =
      (Game.succProbability
        (ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Q false adversary) n)) : ℝ) +
      (Game.succProbability
        (ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Q true adversary) n)) : ℝ) := by
    rw [eval_ciOneTimeGame_ccaToCIHiddenBitAdversary, Game.succProbability_uniform,
      NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_bool,
      Fintype.sum_bool]
    ring
  have hd : 2 * (dyadicSize (Q n) : ℝ) *
      (Game.succProbability
        (ProbComp.eval (E.ciOneTimeGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ) =
      (dyadicSize (Q n) : ℝ) *
        (2 * (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) :
          ℝ)) := by
    ring
  rw [hd, havg]
  linarith

/-- **One-time authenticated encryption implies one-time adaptive CCA security**
([BonehShoup2023], Section 9.2.3, Theorem 9.1, printed pp. 363–365): every symmetric cipher
satisfying `OneTimeAuthenticatedEncryption` (`OneTimeINDCPA ∧ OneTimeCiphertextIntegrity`,
Definition 9.4) also satisfies `OneTimeINDCCA` (`1CCA`, Definition 9.6). -/
theorem OneTimeAuthenticatedEncryption.oneTimeINDCCA {E : SymmetricCipher}
    (h1AE : E.OneTimeAuthenticatedEncryption) :
    E.OneTimeINDCCA := by
  rcases h1AE with ⟨hcpa, hci⟩
  intro adversary hadversary
  obtain ⟨ck, dk, hlenKey⟩ := E.keyGen_ppt.length_le
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
  let ctBound : ℕ → ℕ := fun n => ce * (3 * n + 2 * (ck * (n + 1) ^ dk) + 4) ^ de
  let Q : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
  have hctBoundPoly : ComputableInPolyTime ctBound encUnary encUnary := by
    dsimp only [ctBound]; polytime
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; polytime
  have hctBound (n : ℕ) (k : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
      (msg : List Bool) (hmsg : msg.length = n) (ct : List Bool)
      (hct : ct ∈ (ProbComp.eval (E.encrypt n k msg)).support) : ct.length ≤ ctBound n := by
    have hkLen := hlenKey n k hk
    have hctLen := hlenEnc (n, k, msg) ct hct
    simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkLen
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmsg] at hctLen
    exact hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
  have hq (n : ℕ) : (adversary n []).IsQueryBounded (Q n) := by
    simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1
  have hcpaNeg := hcpa (ccaToCPAAdversary ctBound adversary)
    (isOraclePPT_ccaToCPAAdversary hctBoundPoly hadversary)
  have hciNeg := hci.negligible (ccaToCIHiddenBitAdversary ctBound Q adversary)
    (isOraclePPT_ccaToCIHiddenBitAdversary hctBoundPoly hQPoly hadversary)
  have hpolyDyadic : PolynomiallyBounded (fun n => 2 * dyadicSize (Q n)) := by
    dsimp only [Q]; fun_prop
  have hsumNeg := (hciNeg.polynomiallyBounded_mul hpolyDyadic).add hcpaNeg
  refine negligible_of_le hsumNeg fun n => ?_
  rw [← NNReal.coe_le_coe]
  simpa only [Pi.add_apply, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat,
    Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
    advantage_ccaOneTimeGame_le_two_mul E ctBound Q adversary n (hq n) (hctBound n)

end SymmetricCipher

end Cslib.Crypto
