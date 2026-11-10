/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.MerkleDamgard
public import CslibFrontier.Crypto.Computational.Signature
public import CslibFrontier.Crypto.Computational.WordSignature
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# The Hash-and-Sign Paradigm from Collision-Resistant Hashing

This module formalizes the single-public-key **hash-and-sign** paradigm ([KatzLindell2020],
Section 13.3, Construction 13.3 and Theorem 13.4, pp. 467–468), which upgrades a fixed-length
`SignatureScheme` signing `n`-bit digests at security parameter `n` to an unrestricted
`WordSignatureScheme` signing arbitrary bit strings `msg : List Bool` using a collision-resistant
hash family `H`.

At security parameter `n`:
* `HashAndSign.keyGen S n` runs `(pk₀, sk₀) ← S.keyGen n`, samples a single hash key
  `s ← {0, 1}^n`, and outputs the public key `encPair encBits encBits (pk₀, s)` together with
  the secret key `encPair encBits encBits (sk₀, s)`.
* `HashAndSign.sign S H sk msg` decodes `(sk₀, s)` from `sk` and outputs `σ ← S.sign sk₀ (H s msg)`.
* `HashAndSign.verify S H pk msg sig` decodes `(pk₀, s)` from `pk` and checks
  `S.verify pk₀ (H s msg) sig`.

Unlike the target collision-resistant construction `TCRSignature.wordScheme`
([BonehShoup2023], Section 13.2.1), which must sample a fresh hash key per signature and attach it
to every signature because a universal one-way hash family cannot expose its key before the target
message is chosen, full collision resistance allows a single hash key `s` to be fixed once in the
public key so that signatures carry no hash-key overhead (`sign` returns a raw `S`-signature).
Following `CollisionResistant` and `HashFamily`, hash keys and digests both have length `n` with
uniform key sampling, specializing Construction 13.3 to digest length `ℓ(n) = n` and uniform `Gen`.

For the security reduction ([KatzLindell2020], Theorem 13.4, p. 468), any execution of an
`EUFCMA` forger producing a fresh valid forgery `(m*, σ*)` against `HashAndSign.scheme` splits
pointwise into two cases:
1. If some queried message `m ∈ queried` satisfies `H s m = H s m*`, then `m ≠ m*` (since
   `m* ∉ queried`), so `HashAndSign.collisionFinder` extracts a hash collision `(m*, m)` under the
   challenge key `s`.
2. Otherwise `H s m* ∉ queried.map (H s)` and `(H s m*).length = n`, so `HashAndSign.baseForger`
   forwards `(H s m*, σ*)` as a fresh valid `n`-bit forgery in `S.eufCmaGame`.

This yields the tight pointwise bound `succProbability_eufCmaGame_le` with loss factor `1` on both
terms, and hence `SignatureScheme.EUFCMA.wordEUFCMA_hashAndSign`,
`SignatureScheme.EUFCMA.wordEUFCMA_of_hashFamily`, and
`SignatureScheme.EUFCMA.wordEUFCMA_merkleDamgard`.

In the negative direction, `HashAndSign.not_eufCMA_scheme_of_collision` shows that key-independent
collisions break the scheme: if two distinct messages `m₀ ≠ m₁` collide under every hash key `s`,
a one-query forger queries `m₀` and outputs its signature on `m₁`, winning `eufCmaGame` with
probability `1` at every security parameter `n` regardless of the underlying `SignatureScheme` `S`.

## Main definitions

* `Cslib.Crypto.HashAndSign.keyGen`, `Cslib.Crypto.HashAndSign.sign`,
  `Cslib.Crypto.HashAndSign.verify`, `Cslib.Crypto.HashAndSign.scheme`: Construction 13.3 of
  [KatzLindell2020] packaged as a `WordSignatureScheme`.
* `Cslib.Crypto.HashAndSign.collisionFinder`: collision-finding reduction from an `EUFCMA` forger.
* `Cslib.Crypto.HashAndSign.baseForger`: underlying fixed-length signature reduction from an
  `EUFCMA` forger.
* `Cslib.Crypto.HashAndSign.fixedCollisionForger`: one-query attacker exploiting a known hash
  collision `H s m₀ = H s m₁`.

## Main results

* `Cslib.Crypto.HashAndSign.succProbability_eufCmaGame_le`: forging against `HashAndSign.scheme`
  succeeds at most as often as forging against `S` plus finding a collision in `H`.
* `Cslib.Crypto.SignatureScheme.EUFCMA.wordEUFCMA_hashAndSign`: Theorem 13.4 of [KatzLindell2020].
* `Cslib.Crypto.SignatureScheme.EUFCMA.wordEUFCMA_of_hashFamily`: specialization to a bundled
  `HashFamily`.
* `Cslib.Crypto.SignatureScheme.EUFCMA.wordEUFCMA_merkleDamgard`: specialization to a
  `CompressionFamily` via Merkle–Damgård domain extension.
* `Cslib.Crypto.HashAndSign.not_eufCMA_scheme_of_collision`: key-independent collisions break the
  scheme.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 13.3 (Construction 13.3 and Theorem 13.4, pp. 467–468).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

namespace HashAndSign

variable (S : SignatureScheme) (H : List Bool → List Bool → List Bool)

/-! ### Construction 13.3: Single-Key Hash-and-Sign Scheme -/

/-- Total polynomial-time decoder for a paired key `encPair encBits encBits (key₀, s)`. -/
def keyDecoder : Decoder (encPair encBits encBits) :=
  Decoder.bits.pair Decoder.bits

/-- Key generation for Construction 13.3 ([KatzLindell2020], p. 468): sample
`(pk₀, sk₀) ← S.keyGen n` and a single `n`-bit hash key `s ← {0, 1}^n`, returning `⟨pk₀, s⟩` and
`⟨sk₀, s⟩`. -/
noncomputable def keyGen (n : ℕ) : ProbComp (List Bool × List Bool) := do
  let keys ← S.keyGen n
  let s ← BitString.sampleList n
  return (encPair encBits encBits (keys.1, s), encPair encBits encBits (keys.2, s))

/-- Signing for Construction 13.3 ([KatzLindell2020], p. 468): decode `(sk₀, s)` from `sk` and sign
the digest `H s msg` under `sk₀`. -/
def sign (sk msg : List Bool) : ProbComp (List Bool) :=
  let (sk₀, s) := keyDecoder.decode sk
  S.sign sk₀ (H s msg)

/-- Verification for Construction 13.3 ([KatzLindell2020], p. 468): decode `(pk₀, s)` from `pk` and
verify `sig` on the digest `H s msg` under `pk₀`. -/
def verify (pk msg sig : List Bool) : Bool :=
  let (pk₀, s) := keyDecoder.decode pk
  S.verify pk₀ (H s msg) sig

theorem sign_encPair (sk₀ s msg : List Bool) :
    sign S H (encPair encBits encBits (sk₀, s)) msg = S.sign sk₀ (H s msg) := by
  unfold sign
  rw [keyDecoder.decode_enc (sk₀, s)]

theorem verify_encPair (pk₀ s msg sig : List Bool) :
    verify S H (encPair encBits encBits (pk₀, s)) msg sig = S.verify pk₀ (H s msg) sig := by
  unfold verify
  rw [keyDecoder.decode_enc (pk₀, s)]

/-- Support characterization for `HashAndSign.keyGen`: every generated key pair packs a valid
base key pair `keys₀ ∈ (ProbComp.eval (S.keyGen n)).support` with an `n`-bit hash key `s`. -/
theorem mem_support_keyGen {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGen S n)).support) :
    ∃ keys₀ ∈ (ProbComp.eval (S.keyGen n)).support,
      ∃ s : List Bool, s.length = n ∧
        keys = (encPair encBits encBits (keys₀.1, s), encPair encBits encBits (keys₀.2, s)) := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkeys
  rcases hkeys with ⟨keys₀, hkeys₀, s, hs, rfl⟩
  exact ⟨keys₀, hkeys₀, s, BitString.length_of_mem_support_uniformList hs, rfl⟩

/-- Correctness of Construction 13.3: for any length-preserving hash family (`|H s msg| = |s|`),
every signature produced by `HashAndSign.sign` under a honestly generated key pair verifies for any
arbitrary-length message `msg : List Bool`. -/
theorem verify_sign (hlen : ∀ s msg, (H s msg).length = s.length) (n : ℕ)
    (pk sk : List Bool) (hkeys : (pk, sk) ∈ (ProbComp.eval (keyGen S n)).support)
    (msg sig : List Bool) (hsig : sig ∈ (ProbComp.eval (sign S H sk msg)).support) :
    verify S H pk msg sig = true := by
  rcases mem_support_keyGen S hkeys with ⟨⟨pk₀, sk₀⟩, hkeys₀, s, hs, hpair⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
  rw [sign_encPair] at hsig
  rw [verify_encPair]
  exact S.verify_sign n (pk₀, sk₀) hkeys₀ (H s msg) (by rw [hlen, hs]) sig hsig

@[program_certificate]
theorem isPPTOn_keyGen : IsPPTOn encUnary (encPair encBits encBits) (keyGen S) := by
  have hkg := S.keyGen_ppt
  unfold keyGen
  ppt

@[program_certificate]
theorem isPPTOn_sign
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits) :
    IsPPTOn (encPair encBits encBits) encBits (fun ⟨sk, msg⟩ => sign S H sk msg) := by
  have hsign := S.sign_ppt
  have hHt := hH.tidy
  have hdec := keyDecoder.computableInPolyTime.tidy
  unfold sign
  ppt

@[fun_prop]
theorem computableInPolyTime_verify
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun ⟨pk, msg, sig⟩ => verify S H pk msg sig)
      (encPair encBits (encPair encBits encBits)) encBool := by
  have hverify := S.verify_polyTime
  have hdec := keyDecoder.computableInPolyTime
  unfold verify
  polytime

/-- **Construction 13.3** ([KatzLindell2020], Section 13.3, p. 468): the single-public-key
hash-and-sign `WordSignatureScheme` built from a fixed-length `SignatureScheme` `S` and a
length-preserving hash family `H`. -/
noncomputable def scheme
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ s msg, (H s msg).length = s.length) : WordSignatureScheme where
  keyGen := keyGen S
  sign := sign S H
  verify := verify S H
  verify_sign := verify_sign S H hlen
  keyGen_ppt := isPPTOn_keyGen S
  sign_ppt := isPPTOn_sign S H hH
  verify_polyTime := computableInPolyTime_verify S H hH

/-! ### Theorem 13.4: Reductions to Collision Finding and Fixed-Length Forgery -/

/-- Extract a colliding message pair `(m*, m)` from the output `((m*, σ*), queried)` of a
signing-oracle execution by selecting the first queried message `m ∈ queried` with
`H s m = H s m*`. -/
def collisionOf (s : List Bool) (out : (List Bool × List Bool) × List (List Bool)) :
    List Bool × List Bool :=
  (out.1.1, (out.2.find? fun m => H s m == H s out.1.1).getD [])

@[fun_prop]
theorem computableInPolyTime_collisionOf
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun p : List Bool × ((List Bool × List Bool) × List (List Bool)) =>
        collisionOf H p.1 p.2)
      (encPair encBits (encPair (encPair encBits encBits) (encList encBits)))
      (encPair encBits encBits) := by
  unfold collisionOf
  polytime

/-- Whenever `m* ∉ queried` and `queried.find? (fun m => H s m == H s m*)` succeeds, `collisionOf`
produces a genuine collision for `H` under key `s`. -/
theorem isCollision_collisionOf_of_isSome {n : ℕ} {s : List Bool}
    {out : (List Bool × List Bool) × List (List Bool)} (hfresh : !out.2.contains out.1.1 = true)
    (hfind : (out.2.find? fun m => H s m == H s out.1.1).isSome = true) :
    isCollision H (fun _ _ => true) n s (collisionOf H s out).1 (collisionOf H s out).2 = true := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hfind
  have hmem : m ∈ out.2 := List.mem_of_find?_eq_some hm
  have hcoll : H s m = H s out.1.1 :=
    beq_iff_eq.mp (List.find?_some (p := fun m => H s m == H s out.1.1) hm)
  have hnotmem : out.1.1 ∉ out.2 := by
    simpa [List.contains_iff_mem] using hfresh
  have hne : out.1.1 ≠ m := fun h => hnotmem (h ▸ hmem)
  simp only [collisionOf, hm, Option.getD_some]
  exact isCollision_eq_true_iff.mpr ⟨rfl, rfl, hne, hcoll.symm⟩

/-- **Collision-finding reduction** ([KatzLindell2020], Theorem 13.4, Case 1): given challenge
parameter `n` and hash key `s`, generate `(pk₀, sk₀) ← S.keyGen n`, simulate the `HashAndSign`
signing oracle directly using `sk₀` and `s`, and extract a colliding message pair via
`collisionOf`. -/
noncomputable def collisionFinder
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ s msg, (H s msg).length = s.length)
    (adversary : Forger) : CollisionFinder := fun n s => do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifFin j))
      ((scheme S H hH hlen).signingOracle (encPair encBits encBits (keys.2, s))))
    (adversary n (encPair encBits encBits (keys.1, s)))).run []
  return collisionOf H s out

@[program_certificate]
theorem isPPT_collisionFinder
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ s msg, (H s msg).length = s.length)
    {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT (encPair encBits encBits) (collisionFinder S H hH hlen adversary) := by
  change IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
    (fun p => collisionFinder S H hH hlen adversary p.1 p.2)
  have hkeys : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p : ℕ × List Bool => S.keyGen p.1) :=
    S.isPPTOn_keyGen_comp (ComputableInPolyTime.fst encUnary encBits)
  let E1 := encPair (encPair encUnary encBits) (encPair encBits encBits)
  have hfst := ComputableTidilyInPolyTime.fst (encPair encUnary encBits) (encPair encBits encBits)
  have hsnd := ComputableTidilyInPolyTime.snd (encPair encUnary encBits) (encPair encBits encBits)
  have henc := ComputableTidilyInPolyTime.encode (encPair encBits encBits)
  have hprep : ComputableTidilyInPolyTime
      (fun q : (ℕ × List Bool) × (List Bool × List Bool) =>
        (q.1.1, encPair encBits encBits (q.2.1, q.1.2), encPair encBits encBits (q.2.2, q.1.2)))
      E1 encKeyPairInput :=
    hfst.fst'.prod ((henc.comp (hsnd.fst'.prod hfst.snd')).prod
      (henc.comp (hsnd.snd'.prod hfst.snd')))
  have hrun₀ := (scheme S H hH hlen).isPPTOn_run_signingOracle hadversary
  have hrun := hrun₀.preprocess (.of_tidy hprep)
  let EOut := encPair (encPair encBits encBits) (encList encBits)
  have hrfst := ComputableTidilyInPolyTime.fst E1 EOut
  have hrsnd := ComputableTidilyInPolyTime.snd E1 EOut
  have hpost : ComputableTidilyInPolyTime
      (fun r : ((ℕ × List Bool) × (List Bool × List Bool)) ×
          ((List Bool × List Bool) × List (List Bool)) =>
        collisionOf H r.1.1.2 r.2)
      (encPair E1 EOut) (encPair encBits encBits) :=
    (computableInPolyTime_collisionOf H hH).tidy.comp (hrfst.fst'.snd'.prod hrsnd)
  unfold collisionFinder
  exact hkeys.bind_with (hrun.bind_with hpost.isPPTOn)

/-- Stateless oracle handler that answers a `WordSignatureScheme` signing query `((), msg)` by
querying the external fixed-length signing oracle on `((), H s msg)` and truncating the response to
`bound` bits. -/
def hashSigningHandler (s : List Bool) (bound : ℕ)
    (request : Unit × List Bool) : StateT Unit (WordOracleComp Unit) (List Bool) := fun _ => do
  let sig ← List.take bound <$> ProbOracleComp.query ((), H s request.2)
  return (sig, ())

/-- **Underlying signature reduction** ([KatzLindell2020], Theorem 13.4, Case 2): given `n` and
base public key `pk₀`, sample a uniform `n`-bit hash key `s`, run `adversary n ⟨pk₀, s⟩` by
forwarding hashed signing queries `H s msg` through `hashSigningHandler`, and output the hashed
forgery `(H s m*, σ*)`. -/
noncomputable def baseForger (bound : ℕ → ℕ) (adversary : Forger) : Forger := fun n pk₀ => do
  let s ← ProbOracleComp.sample (BitString.sampleList n)
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun j => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin j)))
      (hashSigningHandler H s (bound n)))
    (adversary n (encPair encBits encBits (pk₀, s)))).run ()
  return (H s out.1.1, out.1.2)

private theorem isOraclePPTOn_hashSigningHandler
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {bound : ℕ → ℕ} (hboundPoly : ComputableInPolyTime bound encUnary encUnary) :
    IsOraclePPTOn (Operation := Unit)
      (encPair (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        hashSigningHandler H p.1.2 (bound p.1.1.1) p.2.1 p.2.2) := by
  let ECaller := encPair (encPair encUnary encBits) encBits
  let EReq := encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)
  let EIn := encPair ECaller EReq
  have hc := ComputableInPolyTime.fst ECaller EReq
  have hr := ComputableInPolyTime.snd ECaller EReq
  have hn := hc.fst'.fst'
  have hs := hc.snd'
  have hmsg := hr.fst'.snd'
  have hdigest := hH.comp' (hs.prod hmsg)
  have hbn := hboundPoly.comp' hn
  have hq := IsOraclePPTOn.query_take' (input := EIn) () hdigest hbn
  have hpost : ComputableInPolyTime
      (fun r : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        (r.2, ()))
      (encPair EIn encBits) (encPair encBits (encFinEnum Unit)) :=
    (ComputableInPolyTime.snd EIn encBits).prod (ComputableInPolyTime.const ())
  unfold hashSigningHandler
  simpa [bind_pure_comp] using hq.map_with'
    (f := fun (_ : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) sig => (sig, ()))
    hpost

theorem isOraclePPT_baseForger
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {bound : ℕ → ℕ} (hboundPoly : ComputableInPolyTime bound encUnary encUnary)
    {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (baseForger H bound adversary) := by
  change IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) (encPair encBits encBits)
    (fun p : ℕ × List Bool => baseForger H bound adversary p.1 p.2)
  have hs : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool => ProbOracleComp.sample (BitString.sampleList p.1)) :=
    (ComputableInPolyTime.sampleList (ComputableInPolyTime.fst encUnary encBits)).isOraclePPTOn
  let ECaller := encPair (encPair encUnary encBits) encBits
  have hcfst := ComputableTidilyInPolyTime.fst (encPair encUnary encBits) encBits
  have hcsnd := ComputableTidilyInPolyTime.snd (encPair encUnary encBits) encBits
  have hprep : ComputableTidilyInPolyTime
      (fun c : (ℕ × List Bool) × List Bool => (c.1.1, encPair encBits encBits (c.1.2, c.2)))
      ECaller (encPair encUnary encBits) :=
    hcfst.fst'.prod ((ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp
      (hcfst.snd'.prod hcsnd))
  have hres : ComputableTidilyInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool => bound pair.1.1.1)
      (encPair ECaller encBits) encUnary :=
    ((ComputableTidilyInPolyTime.fst ECaller encBits).trans hcfst.fst').trans hboundPoly.tidy
  have hrun := hadversary.run_interpret_preprocess_open
    (prepare := fun c : (ℕ × List Bool) × List Bool =>
      (c.1.1, encPair encBits encBits (c.1.2, c.2)))
    (handler := fun (c : (ℕ × List Bool) × List Bool) request state =>
      hashSigningHandler H c.2 (bound c.1.1) request state)
    (initial := fun _ => ())
    (resources := fun c _ => bound c.1.1)
    hprep (isOraclePPTOn_hashSigningHandler H hH hboundPoly) (.const ())
    (fun _ _ => True) (fun _ => trivial) hres
    (fun c request state _ result hresult => by
      cases state
      dsimp only [hashSigningHandler] at hresult
      rw [bind_pure_comp] at hresult
      obtain ⟨sig, hsig, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hsig
      exact ⟨trivial, List.length_take_le _ _, Nat.le_add_right _ _⟩)
  let EOut := encPair (encPair encBits encBits) (encFinEnum Unit)
  have hrfst := ComputableTidilyInPolyTime.fst ECaller EOut
  have hrsnd := ComputableTidilyInPolyTime.snd ECaller EOut
  have hfinal : ComputableTidilyInPolyTime
      (fun r : ((ℕ × List Bool) × List Bool) × ((List Bool × List Bool) × Unit) =>
        (H r.1.2 r.2.1.1, r.2.1.2))
      (encPair ECaller EOut) (encPair encBits encBits) :=
    (hH.tidy.comp (hrfst.snd'.prod hrsnd.fst'.fst')).prod hrsnd.fst'.snd'
  unfold baseForger
  exact hs.bind_with (hrun.bind_with (hfinal.isOraclePPTOn (Operation := Unit)))

/-- When `bound` upper-bounds the bit-length of every signature in the support of
`S.sign sk₀ (H s msg)` and `|H s msg| = n`, interpreting `hashSigningHandler` against
`S.signingOracle sk₀` matches running `(scheme S H hH hlen).signingOracle ⟨sk₀, s⟩` while mapping
the recorded query log `queried` to `queried.map (H s)`. -/
theorem eval_run_hashSigningHandler
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ s msg, (H s msg).length = s.length)
    {n : ℕ} {sk₀ s : List Bool} (hs : s.length = n) {bound : ℕ}
    (hbound : ∀ msg : List Bool, msg.length = n →
      ∀ sig ∈ (ProbComp.eval (S.sign sk₀ msg)).support, sig.length ≤ bound)
    {α : Type} (program : WordOracleComp Unit α) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
        (fun q state => ProbComp.eval (S.signingOracle sk₀ q state)))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun j => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin j)))
          (hashSigningHandler H s bound))
        program).run ())).run [] =
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifFin j))
          ((scheme S H hH hlen).signingOracle (encPair encBits encBits (sk₀, s))))
        program).run [])).map (fun r => ((r.1, ()), r.2.map (H s))) := by
  rw [ProbOracleComp.eval_run_interpret, ProbOracleComp.run_interpret_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun (q : Unit × List Bool) (queried : List (List Bool)) => ProbComp.eval
      ((scheme S H hH hlen).signingOracle (encPair encBits encBits (sk₀, s)) q queried))
    (oracle' := fun (q : Unit × List Bool) (state : Unit × List (List Bool)) =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q state => ProbComp.eval (S.signingOracle sk₀ q state)))
        ((hashSigningHandler H s bound q).run state.1)).run state.2).map
          (fun result => (result.1.1, result.1.2, result.2)))
    (represent := fun queried => ((), queried.map (H s)))
    (step := by
      rintro ⟨⟨⟩, msg⟩ queried
      have hmsg : (H s msg).length = n := by rw [hlen, hs]
      change PMF.map (fun x => (x.1, (), List.map (H s) x.2))
          (ProbComp.eval ((scheme S H hH hlen).signingOracle
            (encPair encBits encBits (sk₀, s)) ((), msg) queried)) =
        PMF.map (fun result => (result.1.1, result.1.2, result.2))
          ((OracleComp.interpret
            (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
              (fun q state => ProbComp.eval (S.signingOracle sk₀ q state)))
            (do
              let sig ← List.take bound <$> ProbOracleComp.query ((), H s msg)
              return (sig, ()))).run (List.map (H s) queried))
      simp only [OracleComp.interpret_bind, OracleComp.interpret_map,
        ProbOracleComp.interpret_query, OracleComp.interpret_pure,
        StateT.run_bind, StateT.run_map, StateT.run_pure]
      simp only [StateT.run, WordSignatureScheme.signingOracle, SignatureScheme.signingOracle,
        scheme, sign_encPair, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
        PMF.map_bind, PMF.bind_bind, PMF.pure_bind, PMF.pure_map, List.map_cons]
      refine PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_
      rw [List.take_of_length_le (hbound (H s msg) hmsg sig hsig)])
    program []
  rw [show ((), ([] : List (List Bool)).map (H s)) = ((), []) from rfl] at hsim
  rw [← hsim, PMF.map_comp]
  rfl

/-- **Pointwise reduction inequality for Theorem 13.4** ([KatzLindell2020], p. 468): whenever
`bound n` upper-bounds the bit-length of valid `S`-signatures at parameter `n`, the `EUFCMA`
forging probability of `adversary` against `HashAndSign.scheme S H hH hlen` is at most the sum of
the `EUFCMA` forging probability of `baseForger H bound adversary` against `S` and the collision-
finding probability of `collisionFinder S H hH hlen adversary` against `H`. -/
theorem succProbability_eufCmaGame_le
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ s msg, (H s msg).length = s.length)
    {bound : ℕ → ℕ}
    (hbound : ∀ n : ℕ, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support,
      ∀ msg : List Bool, msg.length = n →
        ∀ sig ∈ (ProbComp.eval (S.sign keys.2 msg)).support, sig.length ≤ bound n)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval ((scheme S H hH hlen).eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (S.eufCmaGame (baseForger H bound adversary) n)) +
        Game.succProbability
          (ProbComp.eval (collisionGame H (fun _ _ => true)
            (collisionFinder S H hH hlen adversary) n)) := by
  let runDist (keys : List Bool × List Bool) (s : List Bool) :=
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifFin j))
        ((scheme S H hH hlen).signingOracle (encPair encBits encBits (keys.2, s))))
      (adversary n (encPair encBits encBits (keys.1, s)))).run [])
  have hbase : ProbComp.eval (S.eufCmaGame (baseForger H bound adversary) n) =
      (ProbComp.eval (S.keyGen n)).bind fun keys =>
        (BitString.uniformList n).bind fun s =>
          (runDist keys s).bind fun out =>
            PMF.pure (((H s out.1.1).length == n) &&
              !(out.2.map (H s)).contains (H s out.1.1) &&
              S.verify keys.1 (H s out.1.1) out.1.2) := by
    simp only [SignatureScheme.eufCmaGame, baseForger, ProbComp.eval_bind,
      ProbComp.eval_pure, ProbOracleComp.eval_run_interpret, OracleComp.interpret_bind,
      StateT.run_bind, ProbOracleComp.run_interpret_sample, OracleComp.interpret_pure,
      StateT.run_pure, BitString.eval_sampleList, PMF.bind_map,
      Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
    refine PMF.bind_congr_on_support _ _ _ fun s hs => ?_
    have hlen_s : s.length = n := BitString.length_of_mem_support_uniformList hs
    rw [eval_run_hashSigningHandler S H hH hlen hlen_s (hbound n keys hkeys), PMF.bind_map]
    rfl
  have hcol : ProbComp.eval (collisionGame H (fun _ _ => true)
        (collisionFinder S H hH hlen adversary) n) =
      (ProbComp.eval (S.keyGen n)).bind fun keys =>
        (BitString.uniformList n).bind fun s =>
          (runDist keys s).bind fun out =>
            PMF.pure (isCollision H (fun _ _ => true) n s
              (collisionOf H s out).1 (collisionOf H s out).2) := by
    simp only [collisionGame, collisionFinder, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
    rw [PMF.bind_comm]
  have hgame : ProbComp.eval ((scheme S H hH hlen).eufCmaGame adversary n) =
      (ProbComp.eval (S.keyGen n)).bind fun keys =>
        (BitString.uniformList n).bind fun s =>
          (runDist keys s).bind fun out =>
            PMF.pure (!out.2.contains out.1.1 && S.verify keys.1 (H s out.1.1) out.1.2) := by
    simp only [WordSignatureScheme.eufCmaGame, scheme, keyGen, verify_encPair,
      ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
      PMF.bind_bind, PMF.pure_bind]
    rfl
  have key : ProbComp.eval ((scheme S H hH hlen).eufCmaGame adversary n) true ≤
      ProbComp.eval (S.eufCmaGame (baseForger H bound adversary) n) true +
        ProbComp.eval (collisionGame H (fun _ _ => true)
          (collisionFinder S H hH hlen adversary) n) true := by
    rw [hgame, hbase, hcol]
    refine PMF.bind_apply_le_add_on_support _ true fun keys _ => ?_
    refine PMF.bind_apply_le_add_on_support _ true fun s hs => ?_
    have hlen_s : s.length = n := BitString.length_of_mem_support_uniformList hs
    refine PMF.bind_apply_le_add_on_support _ true fun out _ => ?_
    cases hwin : (!out.2.contains out.1.1 && S.verify keys.1 (H s out.1.1) out.1.2)
    · simp
    · obtain ⟨hfresh, hver⟩ := Bool.and_eq_true_iff.mp hwin
      cases hfind : (out.2.find? fun m => H s m == H s out.1.1).isSome
      · have hnotmem : (out.2.map (H s)).contains (H s out.1.1) = false := by
          rw [Bool.eq_false_iff]
          intro hmem
          obtain ⟨m, hm, hcoll⟩ := List.mem_map.mp (List.contains_iff_mem.mp hmem)
          have hex : ∃ m ∈ out.2, (H s m == H s out.1.1) = true :=
            ⟨m, hm, beq_iff_eq.mpr hcoll⟩
          have hisSome : (out.2.find? fun m => H s m == H s out.1.1).isSome = true :=
            List.find?_isSome.mpr hex
          exact Bool.false_ne_true (hfind.symm.trans hisSome)
        have hlen_d : ((H s out.1.1).length == n) = true := by
          rw [hlen, hlen_s, beq_self_eq_true]
        rw [hlen_d, hnotmem, hver]
        exact le_add_right le_rfl
      · rw [isCollision_collisionOf_of_isSome H hfresh hfind]
        exact le_add_left le_rfl
  unfold Game.succProbability
  refine (ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩) key).trans_eq ?_
  rw [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]

private theorem exists_sigLengthBound :
    ∃ bound : ℕ → ℕ,
      ComputableInPolyTime bound encUnary encUnary ∧
      ∀ n : ℕ, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support,
        ∀ msg : List Bool, msg.length = n →
          ∀ sig ∈ (ProbComp.eval (S.sign keys.2 msg)).support, sig.length ≤ bound n := by
  obtain ⟨ck, dk, hlenk⟩ := S.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := S.sign_ppt.length_le
  let bound (n : ℕ) : ℕ := cs * (2 * (ck * (n + 1) ^ dk) + n + 2) ^ ds
  have hboundPoly : ComputableInPolyTime bound encUnary encUnary := by
    let hn := ComputableInPolyTime.id' (encIn := encUnary)
    let cst (k : ℕ) := ComputableInPolyTime.const (encIn := encUnary) (encOut := encUnary) k
    exact ComputableInPolyTime.unary_mul' (cst cs)
      ((ComputableInPolyTime.unary_pow ds).comp
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_add'
            (ComputableInPolyTime.unary_mul' (cst 2)
              (ComputableInPolyTime.unary_mul' (cst ck)
                ((ComputableInPolyTime.unary_pow dk).comp
                  (ComputableInPolyTime.unary_add' hn (cst 1)))))
            hn)
          (cst 2)))
  refine ⟨bound, hboundPoly, fun n keys hkeys msg hmsg sig hsig => ?_⟩
  have hkeyLen := hlenk n keys hkeys
  simp only [encUnary_apply, List.length_replicate, length_encPair, encBits_apply] at hkeyLen
  have hsigLen := hlens (keys.2, msg) sig hsig
  simp only [length_encPair, encBits_apply] at hsigLen
  refine hsigLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left ?_ ds))
  omega

/-! ### Key-Independent Collisions Break the Scheme -/

/-- One-query forger that queries `m₀`, truncates the reply to `bound n` bits, and outputs it as a
forgery on `m₁`. Whenever `m₀ ≠ m₁` and `H s m₀ = H s m₁`, this attacker breaks
`HashAndSign.scheme` with probability `1`. -/
def fixedCollisionForger (bound : ℕ → ℕ) (m₀ m₁ : List Bool) : Forger := fun n _ => do
  let sig ← List.take (bound n) <$> ProbOracleComp.query ((), m₀)
  return (m₁, sig)

theorem isOraclePPT_fixedCollisionForger {bound : ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime bound encUnary encUnary) (m₀ m₁ : List Bool) :
    IsOraclePPT (encPair encBits encBits) (fixedCollisionForger bound m₀ m₁) := by
  change IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) (encPair encBits encBits)
    (fun p : ℕ × List Bool => fixedCollisionForger bound m₀ m₁ p.1 p.2)
  let EIn := encPair encUnary encBits
  have hbn := hboundPoly.comp' (ComputableInPolyTime.fst encUnary encBits)
  have hmsg : ComputableInPolyTime (fun _ : ℕ × List Bool => m₀) EIn encBits :=
    ComputableInPolyTime.const m₀
  have hq := IsOraclePPTOn.query_take' (input := EIn) () hmsg hbn
  have hpost : ComputableInPolyTime
      (fun r : (ℕ × List Bool) × List Bool => (m₁, r.2))
      (encPair EIn encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.const m₁).prod (ComputableInPolyTime.snd EIn encBits)
  unfold fixedCollisionForger
  simpa [bind_pure_comp] using hq.map_with' (f := fun (_ : ℕ × List Bool) sig => (m₁, sig)) hpost

/-- If `m₀ ≠ m₁` collide under every hash key (`∀ s, H s m₀ = H s m₁`) and `bound n` upper-bounds
the length of valid `S`-signatures, `fixedCollisionForger bound m₀ m₁` wins
`(scheme S H hH hlen).eufCmaGame` with probability `1` at every security parameter `n`. -/
theorem succProbability_eufCmaGame_fixedCollisionForger
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ s msg, (H s msg).length = s.length)
    {bound : ℕ → ℕ}
    (hbound : ∀ n : ℕ, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support,
      ∀ msg : List Bool, msg.length = n →
        ∀ sig ∈ (ProbComp.eval (S.sign keys.2 msg)).support, sig.length ≤ bound n)
    {m₀ m₁ : List Bool} (hne : m₁ ≠ m₀) (hcoll : ∀ s, H s m₀ = H s m₁) (n : ℕ) :
    Game.succProbability
      (ProbComp.eval ((scheme S H hH hlen).eufCmaGame (fixedCollisionForger bound m₀ m₁) n)) =
        1 := by
  have heval :
      ProbComp.eval ((scheme S H hH hlen).eufCmaGame (fixedCollisionForger bound m₀ m₁) n) =
        PMF.pure true := by
    simp only [WordSignatureScheme.eufCmaGame, fixedCollisionForger,
      OracleComp.interpret_bind, OracleComp.interpret_map, ProbOracleComp.interpret_query,
      OracleComp.interpret_pure, StateT.run_bind, StateT.run_map, StateT.run_pure]
    simp only [StateT.run, WordSignatureScheme.signingOracle, scheme, keyGen, sign_encPair,
      verify_encPair, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.bind_bind, PMF.map_bind, PMF.pure_bind,
      PMF.pure_map]
    refine (PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_).trans (PMF.bind_const _ _)
    refine (PMF.bind_congr_on_support _ _ _ fun s hs => ?_).trans (PMF.bind_const _ _)
    have hlen_s : s.length = n := BitString.length_of_mem_support_uniformList hs
    have hlen_d : (H s m₀).length = n := by rw [hlen, hlen_s]
    refine (PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_).trans (PMF.bind_const _ _)
    rw [List.take_of_length_le (hbound n keys hkeys (H s m₀) hlen_d sig hsig)]
    have hver : S.verify keys.1 (H s m₁) sig = true := by
      rw [← hcoll s]
      exact S.verify_sign n keys hkeys (H s m₀) hlen_d sig hsig
    have hnotmem : ([m₀] : List (List Bool)).contains m₁ = false := by
      simp [hne]
    rw [hnotmem, hver]
    rfl
  simp [Game.succProbability, heval]

/-- **Key-independent collisions break Construction 13.3**: if two distinct messages `m₀ ≠ m₁`
collide under every hash key `s`, then `(scheme S H hH hlen)` is not `EUFCMA` secure for any
underlying `SignatureScheme` `S`. -/
theorem not_eufCMA_scheme_of_collision
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ s msg, (H s msg).length = s.length)
    {m₀ m₁ : List Bool} (hne : m₁ ≠ m₀) (hcoll : ∀ s, H s m₀ = H s m₁) :
    ¬ (scheme S H hH hlen).EUFCMA := by
  intro heuf
  obtain ⟨bound, hboundPoly, hbound_le⟩ := exists_sigLengthBound S
  have hneg := heuf.negligible (fixedCollisionForger bound m₀ m₁)
    (isOraclePPT_fixedCollisionForger hboundPoly m₀ m₁)
  have hzero : Negligible (fun _ : ℕ => (1 : ℝ≥0)) :=
    hneg.congr fun n =>
      succProbability_eufCmaGame_fixedCollisionForger S H hH hlen hbound_le hne hcoll n
  exact not_negligible_const one_ne_zero hzero

end HashAndSign

open HashAndSign

/-! ### Main EUF-CMA Theorems ([KatzLindell2020], Theorem 13.4) -/

/-- **Theorem 13.4** ([KatzLindell2020], Section 13.3, p. 468): if `S` is an `EUFCMA`-secure
fixed-length `SignatureScheme` and `H` is a polynomial-time length-preserving collision-resistant
hash family, then the single-public-key hash-and-sign scheme `HashAndSign.scheme S H hH hlen` is an
`EUFCMA`-secure `WordSignatureScheme` on arbitrary-length bit strings. -/
theorem SignatureScheme.EUFCMA.wordEUFCMA_hashAndSign
    {S : SignatureScheme} (hS : S.EUFCMA) {H : List Bool → List Bool → List Bool}
    (hcr : CollisionResistant H)
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ s msg, (H s msg).length = s.length) :
    (scheme S H hH hlen).EUFCMA := by
  obtain ⟨bound, hboundPoly, hbound_le⟩ := exists_sigLengthBound S
  apply WordSignatureScheme.EUFCMA.of_negligible
  intro adversary hadversary
  have hbase := hS.negligible (baseForger H bound adversary)
    (isOraclePPT_baseForger H hH hboundPoly hadversary)
  have hcol := hcr.negligible (collisionFinder S H hH hlen adversary)
    (isPPT_collisionFinder S H hH hlen hadversary)
  exact negligible_of_le (hbase.add hcol)
    (succProbability_eufCmaGame_le S H hH hlen hbound_le adversary)

/-- **Theorem 13.4** specialized to a bundled `HashFamily` ([KatzLindell2020], Section 13.3,
p. 468). -/
theorem SignatureScheme.EUFCMA.wordEUFCMA_of_hashFamily
    {S : SignatureScheme} (hS : S.EUFCMA) {H : List Bool → List Bool → List Bool}
    (hH : HashFamily H) :
    (scheme S H hH.polyTime hH.length_eq).EUFCMA :=
  hS.wordEUFCMA_hashAndSign hH.collisionResistant hH.polyTime hH.length_eq

/-- **Merkle–Damgård + Hash-and-Sign** ([KatzLindell2020], Sections 6.2 and 13.3): an
`EUFCMA`-secure fixed-length `SignatureScheme` together with a collision-resistant `2 n → n`
`CompressionFamily` yields an `EUFCMA`-secure `WordSignatureScheme` on arbitrary-length messages via
`merkleDamgard` and `HashAndSign.scheme`. -/
theorem SignatureScheme.EUFCMA.wordEUFCMA_merkleDamgard
    {S : SignatureScheme} (hS : S.EUFCMA) {h : List Bool → List Bool → List Bool}
    (hh : CompressionFamily h) :
    (scheme S (merkleDamgard h)
      hh.hashFamily_merkleDamgard.polyTime
      hh.hashFamily_merkleDamgard.length_eq).EUFCMA :=
  hS.wordEUFCMA_of_hashFamily hh.hashFamily_merkleDamgard

end Cslib.Crypto
