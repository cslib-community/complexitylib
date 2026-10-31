/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Signature
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Tidy
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Probability.PMF.Bind
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Indexed signature schemes

An indexed signature scheme ([BonehShoup2023], Definition 14.6) signs pairs `(u, msg)` of an index
`u < q` and a message. Its security game lets the adversary choose the indices of its signing
queries, but never the same index twice; it wins with a valid signature on any pair `(u, msg)` it
never had signed. An indexed scheme is what a stateful signer that never reuses an index needs:
Merkle's tree signature uses the index of the next unused leaf ([Merkle1989], Sections 6–7;
[BonehShoup2023], Section 14.6.4, where the index is a nonce). The index is an explicit input, so
the syntax is stateless; the state is the signer's obligation never to repeat an index, which the
game enforces.

The definition here differs from [BonehShoup2023], Definition 14.6, in four labelled ways.

* Signing may be randomized; the source requires deterministic signing.
* Messages are arbitrary bit strings, with no length restriction.
* Instead of forbidding the adversary to repeat an index, the signing oracle refuses a repeated
  index, and an index `u ≥ q`, by returning the empty word and recording nothing. Every oracle
  adversary is therefore admissible.
* A forgery may name any index, whereas the source's message space is `{1, …, q} × M`. The
  structure does not require verification to reject an index `u ≥ q`; the game does. The oracle
  never signs at such an index, so a forger that finds a valid signature there wins. This
  strengthens the source notion.

A request to the signing oracle is the word `encPair encUnary encBits (u, msg)`. The oracle reads
every word with the total decoder `requestDecoder`.

## Main definitions

* `Cslib.Crypto.IndexedForger`: adaptive oracle adversary outputting `(u, msg, sig)`.
* `Cslib.Crypto.IndexedSignatureScheme`: indexed signature scheme with capacity `q(n)`.
* `Cslib.Crypto.IndexedSignatureScheme.requestDecoder`: the index and message of a request word.
* `Cslib.Crypto.IndexedSignatureScheme.indexedSigningOracle`,
  `Cslib.Crypto.IndexedSignatureScheme.indexedEufCmaGame`,
  `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA`: the security game and predicate.

## Main results

* `Cslib.Crypto.IndexedSignatureScheme.isPPTOn_run_indexedSigningOracle`,
  `Cslib.Crypto.IndexedSignatureScheme.isPPTOn_indexedEufCmaGame`: strict PPT certificates for
  running an oracle-PPT forger against the signing oracle, and for the whole game.
* `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.negligible`,
  `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.of_negligible`: security as negligible
  forging probability.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.1 (Definition 14.6) and Section 14.6.4.
* [R. C. Merkle, *A Certified Digital Signature*][Merkle1989], Sections 6–7.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- An adaptive indexed forger receives a unary security parameter and a public key, queries a
signing oracle on request words `encPair encUnary encBits (u, msg)`, and outputs a candidate
`(u, msg, sig)`. -/
abbrev IndexedForger := ℕ → List Bool → WordOracleComp Unit (ℕ × List Bool × List Bool)

/-- An indexed signature scheme ([BonehShoup2023], Definition 14.6, with randomized signing and
arbitrary-length messages): at security parameter `n` it signs pairs `(u, msg)` with
`u < capacity n`, each index at most once. Key generation and signing are strict PPT, verification
is deterministic polynomial time, and every honest signature verifies. -/
structure IndexedSignatureScheme where
  /-- The number `q(n)` of indices available at security parameter `n`. -/
  capacity : ℕ → ℕ
  /-- Sample a public key and secret key `(pk, sk)` at unary parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Sign the message `msg` at index `u` with the secret key `sk`. -/
  sign : List Bool → ℕ → List Bool → ProbComp (List Bool)
  /-- Verify a candidate signature `sig` on the message `msg` at index `u` under `pk`. -/
  verify : List Bool → ℕ → List Bool → List Bool → Bool
  /-- The capacity is computable in polynomial time, so it is polynomially bounded. -/
  capacity_polyTime : ComputableInPolyTime capacity encUnary encUnary
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) keyGen
  /-- Signing is uniformly strict PPT in the secret key, the unary index and the message. -/
  sign_ppt : IsPPTOn (encPair encBits (encPair encUnary encBits)) encBits
    (fun p => sign p.1 p.2.1 p.2.2)
  /-- Verification is computable in plain polynomial time on `(pk, u, msg, sig)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun p : List Bool × ℕ × List Bool × List Bool => verify p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encBits (encPair encUnary (encPair encBits encBits))) encBool
  /-- Every signature produced at an index below the capacity, under a supported key pair, is
  accepted. -/
  verify_sign : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support → ∀ u < capacity n,
    ∀ msg sig, sig ∈ (ProbComp.eval (sign keys.2 u msg)).support →
      verify keys.1 u msg sig = true

namespace IndexedSignatureScheme

attribute [program_certificate] capacity_polyTime keyGen_ppt sign_ppt verify_polyTime

/-- The index and message of a request word: `encPair encUnary encBits (u, msg)` decodes to
`(u, msg)`, and every other word decodes to some pair. -/
def requestDecoder : Decoder (encPair encUnary encBits) := Decoder.unary.pair Decoder.bits

/-- The indexed signing oracle at security parameter `n`. Its state lists the signed pairs, most
recent first. A request `(u, msg)` is signed when `u < capacity n` and `u` was never used, and then
recorded; any other request receives the empty word and changes nothing. -/
def indexedSigningOracle (S : IndexedSignatureScheme) (n : ℕ) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (ℕ × List Bool)) ProbComp (List Bool) :=
  fun signed =>
    let r := requestDecoder.decode request.2
    if r.1 < S.capacity n ∧ r.1 ∉ signed.map Prod.fst then do
      let sig ← S.sign sk r.1 r.2
      return (sig, r :: signed)
    else
      return ([], signed)

/-- The indexed EUF-CMA experiment: sample `(pk, sk) ← keyGen n`, run the forger on `(n, pk)`
with the indexed signing oracle, and accept a valid signature on a pair `(u, msg)` that was never
signed. -/
def indexedEufCmaGame (S : IndexedSignatureScheme) (adversary : IndexedForger) (n : ℕ) :
    ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.indexedSigningOracle n keys.2)) (adversary n keys.1)).run []
  return !out.2.contains (out.1.1, out.1.2.1) &&
    S.verify keys.1 out.1.1 out.1.2.1 out.1.2.2

/-- Running an oracle-PPT indexed forger against `indexedSigningOracle` is uniformly strict PPT in
the unary security parameter, the public key and the secret key. -/
@[program_certificate]
theorem isPPTOn_run_indexedSigningOracle (S : IndexedSignatureScheme) {adversary : IndexedForger}
    (hadversary : IsOraclePPT (encPair encUnary (encPair encBits encBits)) adversary) :
    IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair (encPair encUnary (encPair encBits encBits)) (encList (encPair encUnary encBits)))
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.indexedSigningOracle caller.1 caller.2.2)) (adversary caller.1 caller.2.1)).run
          []) := by
  obtain ⟨c, d, hlen⟩ := S.sign_ppt.length_le
  have hcap := S.capacity_polyTime
  have hdecode := requestDecoder.computableInPolyTime
  have hhandler : IsPPTOn
      (encPair (encPair encUnary (encPair encBits encBits))
        (encPair (encPair (encFinEnum Unit) encBits) (encList (encPair encUnary encBits))))
      (encPair encBits (encList (encPair encUnary encBits)))
      (fun pair : (ℕ × (List Bool × List Bool)) ×
          ((Unit × List Bool) × List (ℕ × List Bool)) =>
        S.indexedSigningOracle pair.1.1 pair.1.2.2 pair.2.1 pair.2.2) := by
    unfold indexedSigningOracle
    apply IsPPTOn.ite
    · polytime
    · refine (S.sign_ppt.preprocess (prepare := fun pair :
          (ℕ × (List Bool × List Bool)) × ((Unit × List Bool) × List (ℕ × List Bool)) =>
          (pair.1.2.2, (requestDecoder.decode pair.2.1.2).1,
            (requestDecoder.decode pair.2.1.2).2)) ?_).bind_with ?_
      · polytime
      · apply ComputableInPolyTime.isPPTOn
        polytime
    · ppt
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × (List Bool × List Bool) => (caller.1, caller.2.1))
    (initial := fun _ => ([] : List (ℕ × List Bool)))
    (resources := fun caller query =>
      c * (2 * caller.2.2.length + 3 * query.length + 4) ^ d + 6 * query.length + 6)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request signed _ result hresult
  have hu := length_unframe_le request.2
  have hmsg := length_dropFrame_le request.2
  have hdecode :
      requestDecoder.decode request.2 = ((unframe request.2).length, dropFrame request.2) := rfl
  unfold indexedSigningOracle at hresult
  dsimp only at hresult
  rw [hdecode] at hresult
  split_ifs at hresult with hguard
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hresult
    obtain ⟨sig, hsig, rfl⟩ := hresult
    have hsigLen := hlen (caller.2.2, (unframe request.2).length, dropFrame request.2) sig hsig
    simp only [encBits_apply, encUnary_apply, length_encPair, List.length_replicate] at hsigLen
    refine ⟨trivial, ?_, ?_⟩
    · have hpow : c * (2 * caller.2.2.length + 1 + (2 * (unframe request.2).length + 1 +
          (dropFrame request.2).length) + 1) ^ d ≤
          c * (2 * caller.2.2.length + 3 * request.2.length + 4) ^ d :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
      dsimp only
      omega
    · simp only [encList_cons, List.length_append, length_frame, encPair_apply, encUnary_apply,
        encBits_apply, List.length_replicate]
      omega
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst hresult
    exact ⟨trivial, by simp, by lia⟩

/-- The whole indexed EUF-CMA experiment is uniformly strict PPT in its unary security parameter
for every oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_indexedEufCmaGame (S : IndexedSignatureScheme) {adversary : IndexedForger}
    (hadversary : IsOraclePPT (encPair encUnary (encPair encBits encBits)) adversary) :
    IsPPTOn encUnary encBool (S.indexedEufCmaGame adversary) := by
  have hrun := S.isPPTOn_run_indexedSigningOracle hadversary
  have hverify := S.verify_polyTime.tidy
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) ×
          ((ℕ × List Bool × List Bool) × List (ℕ × List Bool)) =>
        !pair.2.2.contains (pair.2.1.1, pair.2.1.2.1) &&
          S.verify pair.1.2.1 pair.2.1.1 pair.2.1.2.1 pair.2.1.2.2)
      (encPair (encPair encUnary (encPair encBits encBits))
        (encPair (encPair encUnary (encPair encBits encBits))
          (encList (encPair encUnary encBits)))) encBool := by
    polytime
  exact S.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- Existential unforgeability of an indexed scheme under adaptive chosen-message attack
([BonehShoup2023], Definition 14.6, with the differences listed in the module docstring) against
uniform strict oracle-PPT forgers. -/
def IndexedEUFCMA (S : IndexedSignatureScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.indexedEufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encUnary (encPair encBits encBits)))

/-- Indexed EUF-CMA security gives negligible forging probability for every oracle-PPT forger. -/
theorem IndexedEUFCMA.negligible {S : IndexedSignatureScheme} (h : S.IndexedEUFCMA)
    (adversary : IndexedForger)
    (hadversary : IsOraclePPT (encPair encUnary (encPair encBits encBits)) adversary) :
    Negligible (fun n =>
      Game.succProbability (ProbComp.eval (S.indexedEufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish indexed EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem IndexedEUFCMA.of_negligible {S : IndexedSignatureScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encUnary (encPair encBits encBits)) adversary →
      Negligible (fun n =>
        Game.succProbability (ProbComp.eval (S.indexedEufCmaGame adversary n)))) :
    S.IndexedEUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

end IndexedSignatureScheme

end Cslib.Crypto
