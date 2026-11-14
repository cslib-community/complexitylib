/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Word-level Fujisaki–Okamoto family with native honest algorithms

The Fujisaki–Okamoto transforms `FO^⊥` and `FO-notbot` of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto` act on one fixed explicit-coin scheme. This
module states them for a security-parameter family of schemes over words, and proves that the
honest algorithms are uniform strict (oracle) PPT whenever the underlying public-key encryption
family is.

`WordPKE` is a public-key encryption family with explicit coins
([HofheinzHoevelmannsKiltz2017], IACR ePrint 2017/604, full version dated 2 November 2021, §2.1):
at parameter `n`, messages are words of length `msgLen n`, coins are uniform words of length
`coinLen n`, and the ciphertext space is the words of length at most `ctLen n`. Key generation is
randomized; deterministic encryption and decryption are functions of the parameter and their
word arguments. `WordPKE.IsEfficient` asks for strict PPT key generation and polynomial-time
encryption, decryption and lengths.

At each parameter, `WordPKE.scheme P keyLen n` is the FO parameter bundle `Scheme` over words,
with uniform messages, coins and `keyLen n`-bit keys. Its decryption reports only results of
message length. The native algorithms query two word oracles `G` and `H` (`RO`), reading at most
`coinLen n` bits of each `G` reply and `keyLen n` bits of each `H` reply:

* `WordPKE.keyGenNotBot` is `Scheme.keyGenNotBot` of the bundle;
* `WordPKE.encaps` draws `m`, queries `G(m)`, encrypts, and queries `H(false, m, c)`;
* `WordPKE.decapsNotBot` and `WordPKE.decapsBot` reject words longer than `ctLen n` with `none`,
  and otherwise run the oracle-generic decapsulations `Scheme.decapsNotBotM` and
  `Scheme.decapsBotM` of the bundle with the word oracles.

The `H` request is the word `encHQuery (b, m, c)`, keeping the library's domain-separated
`H : Bool × M × CT → K` (see `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto`).

## Deviations from [HofheinzHoevelmannsKiltz2017]

* Words longer than `ctLen n` are outside the ciphertext space, and decapsulation rejects them
  with `none` before any oracle call, for both transforms. In the source, decapsulation is only
  defined on the ciphertext space. ML-KEM performs the same check, the ciphertext type check of
  the decapsulation input check ([NISTFIPS203], §7.3).
* The source's decryption outputs a message of the finite message space or `⊥` (§2.1). Here a
  decryption result that is not a word of length `msgLen n` is treated as `⊥`.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient`: the word-level family and its
  efficiency.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.encrypt`: randomized encryption, the
  algorithm of the family's IND-CPA security.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.toExplicitCoin`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.scheme`: the explicit-coin scheme and the FO
  bundle at one parameter.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.encEncDetInput`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.encImplicitSK`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.encDecapsNotBotInput`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.encDecapsBotInput`: the encoded inputs of the
  certificates.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.RO`, `Cslib.Crypto.Protocols.FujisakiOkamoto.encHQuery`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.queryG`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.queryH`: the word random oracles.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.keyGenNotBot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.encaps`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.decapsNotBot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.decapsBot`: the native honest algorithms.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPTOn_encrypt`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPTOn_keyGenNotBot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isOraclePPTOn_encaps`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isOraclePPTOn_decapsNotBot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isOraclePPTOn_decapsBot`: native
  certificates for every honest algorithm, from the certificates of the PKE family.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021), §2.1, §3.2.1 Fig. 9 and §3.2.2 Fig. 12.
* [NIST, *FIPS 203: Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203],
  §7.3.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability Turing.MultiTapeTM

/-- A word-level public-key encryption family with explicit coins
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §2.1). At parameter `n`, messages
are words of length `msgLen n`, encryption coins are uniform words of length `coinLen n`, and the
ciphertext space is the words of length at most `ctLen n`. -/
structure WordPKE where
  /-- The message length at each parameter. -/
  msgLen : ℕ → ℕ
  /-- The coin length at each parameter. -/
  coinLen : ℕ → ℕ
  /-- The bound on ciphertext lengths at each parameter. -/
  ctLen : ℕ → ℕ
  /-- Key generation `(pk, sk) ← keyGen n`. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Deterministic encryption `encDet n pk m r` with explicit coins `r`. -/
  encDet : ℕ → List Bool → List Bool → List Bool → List Bool
  /-- Deterministic decryption `dec n sk c`, `none` on failure. -/
  dec : ℕ → List Bool → List Bool → Option (List Bool)

/-- The input `(1ⁿ, pk, m, r)` of deterministic encryption: the parameter in unary, then the
public key, the message and the coins as framed words. -/
abbrev encEncDetInput : ℕ × List Bool × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encBits encBits))

/-- Efficiency of a word-level PKE family: polynomial-time lengths, uniform strict PPT key
generation, and polynomial-time deterministic encryption and decryption. -/
structure WordPKE.IsEfficient (P : WordPKE) : Prop where
  /-- The message length is polynomial-time computable in unary. -/
  msgLen : ComputableInPolyTime P.msgLen encUnary encUnary
  /-- The coin length is polynomial-time computable in unary. -/
  coinLen : ComputableInPolyTime P.coinLen encUnary encUnary
  /-- The ciphertext length bound is polynomial-time computable in unary. -/
  ctLen : ComputableInPolyTime P.ctLen encUnary encUnary
  /-- Key generation is uniform strict PPT. -/
  keyGen : IsPPTOn encUnary (encPair encBits encBits) P.keyGen
  /-- Deterministic encryption is polynomial-time on `(1ⁿ, pk, m, r)`. -/
  encDet : ComputableInPolyTime (fun (n, pk, m, r) => P.encDet n pk m r) encEncDetInput encBits
  /-- Decryption is polynomial-time on `(1ⁿ, sk, c)`. -/
  dec : ComputableInPolyTime (fun (n, sk, c) => P.dec n sk c) (encKeyedInput encBits)
    (encOption encBits)

namespace WordPKE

variable (P : WordPKE) (keyLen : ℕ → ℕ)

/-- Randomized encryption: draw uniform coins `r` of length `coinLen n` and output
`encDet n pk m r`. The IND-CPA security of the family is stated for this algorithm. -/
noncomputable def encrypt (n : ℕ) (pk m : List Bool) : ProbComp (List Bool) := do
  let r ← BitString.sampleList (P.coinLen n)
  return P.encDet n pk m r

/-- The explicit-coin scheme of `P` at parameter `n`, over words: coins are uniform words of
length `coinLen n`, and decryption reports only results of length `msgLen n`. -/
noncomputable def toExplicitCoin (n : ℕ) :
    ExplicitCoinPKE (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) where
  keyGen := P.keyGen n
  sampleCoins := BitString.sampleList (P.coinLen n)
  encDet := P.encDet n
  dec sk c := (P.dec n sk c).filter fun m => m.length == P.msgLen n

/-- The FO parameter bundle of `P` at parameter `n`, over words: the explicit-coin scheme
`toExplicitCoin n`, uniform messages of length `msgLen n` and uniform keys of length `keyLen n`. -/
noncomputable def scheme (n : ℕ) :
    Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) where
  pke := P.toExplicitCoin n
  sampleMsg := BitString.sampleList (P.msgLen n)
  sampleKey := BitString.sampleList (keyLen n)

end WordPKE

/-- The two random oracles of the word-level FO transforms: `G` derives encryption coins from a
message and `H` derives keys. -/
inductive RO where
  /-- The coin-derivation oracle `G`. -/
  | G
  /-- The key-derivation oracle `H`. -/
  | H
  deriving DecidableEq

instance : Fintype RO := ⟨{.G, .H}, fun x => by cases x <;> simp⟩

/-- The word of an `H` query `(b, m, c)`: the domain-separation tag, then the message and the
ciphertext as framed words. -/
abbrev encHQuery : Bool × List Bool × List Bool ↪ List Bool :=
  encPair encBool (encPair encBits encBits)

/-- Query `H` on `(b, m, c)` and read at most `keyLen n` bits of the reply. -/
def queryH (keyLen : ℕ → ℕ) (n : ℕ) (x : Bool × List Bool × List Bool) :
    WordOracleComp RO (List Bool) :=
  List.take (keyLen n) <$>
    ProbOracleComp.query (spec := fun _ : RO × List Bool => List Bool) (RO.H, encHQuery x)

/-- The encoding of an `FO-notbot` secret key `(sk, pk, s)` as three framed words. -/
enc_structure encImplicitSK : ImplicitSK (List Bool) (List Bool) (List Bool) where
  sk : encBits, pk : encBits, fallback : encBits

/-- The input `(1ⁿ, dk, c)` of `FO-notbot` decapsulation: the parameter in unary, then the
secret key and the ciphertext. -/
abbrev encDecapsNotBotInput :
    ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool ↪ List Bool :=
  encPair encUnary (encPair encImplicitSK encBits)

/-- The input `(1ⁿ, pk, sk, c)` of `FO^⊥` decapsulation: the parameter in unary, then the public
key, the secret key and the ciphertext as framed words. -/
abbrev encDecapsBotInput : ℕ × List Bool × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encBits encBits))

namespace WordPKE

variable (P : WordPKE) (keyLen : ℕ → ℕ)

/-- Query `G` on `m` and read at most `coinLen n` bits of the reply. -/
def queryG (n : ℕ) (m : List Bool) : WordOracleComp RO (List Bool) :=
  List.take (P.coinLen n) <$>
    ProbOracleComp.query (spec := fun _ : RO × List Bool => List Bool) (RO.G, m)

/-- Native key generation of `FO-notbot` ([HofheinzHoevelmannsKiltz2017], ePrint 2017/604
(2 Nov 2021), §3.2.2, Fig. 12): `Scheme.keyGenNotBot` of the bundle `scheme P keyLen n`. -/
noncomputable def keyGenNotBot (n : ℕ) :
    ProbComp (List Bool × ImplicitSK (List Bool) (List Bool) (List Bool)) :=
  (P.scheme keyLen n).keyGenNotBot

/-- Native encapsulation of `FO^⊥` and `FO-notbot` ([HofheinzHoevelmannsKiltz2017], ePrint
2017/604 (2 Nov 2021), §3.2.1, Fig. 9 and §3.2.2, Fig. 12): draw a uniform message `m` of length
`msgLen n`, query `r = G(m)`, encrypt `c = encDet n pk m r`, query `k = H(false, m, c)`, and output
`(c, k)`. -/
noncomputable def encaps (n : ℕ) (pk : List Bool) : WordOracleComp RO (List Bool × List Bool) := do
  let m ← ProbOracleComp.sample (BitString.sampleList (P.msgLen n))
  let r ← P.queryG n m
  let c := P.encDet n pk m r
  let k ← queryH keyLen n (false, m, c)
  return (c, k)

/-- Native implicit-rejection decapsulation of `FO-notbot` ([HofheinzHoevelmannsKiltz2017],
ePrint 2017/604 (2 Nov 2021), §3.2.2, Fig. 12): reject a word longer than `ctLen n` with `none`,
and otherwise run `Scheme.decapsNotBotM` of the bundle with the word oracles. -/
noncomputable def decapsNotBot (n : ℕ) (dk : ImplicitSK (List Bool) (List Bool) (List Bool))
    (c : List Bool) : WordOracleComp RO (Option (List Bool)) :=
  if c.length ≤ P.ctLen n then
    some <$> (P.scheme keyLen n).decapsNotBotM (P.queryG n) (queryH keyLen n) dk c
  else
    pure none

/-- Native explicit-rejection decapsulation of `FO^⊥` ([HofheinzHoevelmannsKiltz2017], ePrint
2017/604 (2 Nov 2021), §3.2.1, Fig. 9): reject a word longer than `ctLen n` with `none`, and
otherwise run `Scheme.decapsBotM` of the bundle with the word oracles. -/
noncomputable def decapsBot (n : ℕ) (pk sk c : List Bool) :
    WordOracleComp RO (Option (List Bool)) :=
  if c.length ≤ P.ctLen n then
    (P.scheme keyLen n).decapsBotM (P.queryG n) (queryH keyLen n) pk sk c
  else
    pure none

/-! ### Native certificates -/

namespace IsEfficient

variable {P : WordPKE} {keyLen : ℕ → ℕ}

/-- Randomized encryption is uniform strict PPT on `(1ⁿ, pk, m)`. -/
theorem isPPTOn_encrypt (hP : P.IsEfficient) :
    IsPPTOn (encKeyedInput encBits) encBits (fun (n, pk, m) => P.encrypt n pk m) := by
  let E := encKeyedInput encBits
  change IsPPTOn E encBits (fun x => P.encrypt x.1 x.2.1 x.2.2)
  have hn : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => x.1) E encUnary := by
    fun_prop
  have hdet : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool => P.encDet p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair E encBits) encBits :=
    hP.encDet.comp (by fun_prop : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool => (p.1.1, p.1.2.1, p.1.2.2, p.2))
      (encPair E encBits) encEncDetInput)
  simpa only [encrypt, bind_pure_comp, Function.comp_def] using
    (hP.coinLen.comp hn).sampleList.map_with hdet

/-- Native `FO-notbot` key generation is uniform strict PPT. -/
theorem isPPTOn_keyGenNotBot (hP : P.IsEfficient) :
    IsPPTOn encUnary (encPair encBits encImplicitSK) (P.keyGenNotBot keyLen) := by
  have hmsg : ComputableInPolyTime
      (fun p : ℕ × (List Bool × List Bool) => P.msgLen p.1)
      (encPair encUnary (encPair encBits encBits)) encUnary :=
    hP.msgLen.comp (ComputableInPolyTime.fst _ _)
  have hout : ComputableInPolyTime
      (fun q : (ℕ × (List Bool × List Bool)) × List Bool =>
        (q.1.2.1, ImplicitSK.mk q.1.2.2 q.1.2.1 q.2))
      (encPair (encPair encUnary (encPair encBits encBits)) encBits)
      (encPair encBits encImplicitSK) := by
    fun_prop
  have hfallback : IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair encBits encImplicitSK) (fun p : ℕ × (List Bool × List Bool) =>
        (fun s => (p.2.1, ImplicitSK.mk p.2.2 p.2.1 s)) <$>
          BitString.sampleList (P.msgLen p.1)) :=
    hmsg.sampleList.map_with hout
  refine (hP.keyGen.bind_with (second := fun n keys =>
    (fun s => (keys.1, ImplicitSK.mk keys.2 keys.1 s)) <$> BitString.sampleList (P.msgLen n))
    hfallback).congr fun n => ?_
  simp [keyGenNotBot, Scheme.keyGenNotBot, scheme, toExplicitCoin, bind_pure_comp]

/-- The input `((1ⁿ, pk), m)` of encapsulation after the message draw. -/
private abbrev encEncapsDraw : (ℕ × List Bool) × List Bool ↪ List Bool :=
  encPair (encPair encUnary encBits) encBits

/-- The input `(((1ⁿ, pk), m), r)` of encapsulation after the `G` query. -/
private abbrev encEncapsCoin : ((ℕ × List Bool) × List Bool) × List Bool ↪ List Bool :=
  encPair encEncapsDraw encBits

/-- Native encapsulation is uniform strict oracle PPT on `(1ⁿ, pk)`, for every pair of external
oracles `G` and `H`. -/
theorem isOraclePPTOn_encaps (hP : P.IsEfficient)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsOraclePPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun (n, pk) => P.encaps keyLen n pk) := by
  change IsOraclePPTOn (encPair encUnary encBits) _ (fun x => P.encaps keyLen x.1 x.2)
  have hm : IsOraclePPTOn (Operation := RO) (encPair encUnary encBits) encBits
      (fun x : ℕ × List Bool => ProbOracleComp.sample (BitString.sampleList (P.msgLen x.1))) :=
    (hP.msgLen.comp (ComputableInPolyTime.fst _ _)).sampleList.isOraclePPTOn
  have hr : IsOraclePPTOn encEncapsDraw encBits
      (fun p : (ℕ × List Bool) × List Bool => P.queryG p.1.1 p.2) :=
    IsOraclePPTOn.query_take' RO.G (by fun_prop) (hP.coinLen.comp (by fun_prop))
  have hc : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × List Bool) × List Bool =>
        P.encDet q.1.1.1 q.1.1.2 q.1.2 q.2) encEncapsCoin encBits :=
    hP.encDet.comp (by fun_prop : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × List Bool) × List Bool => (q.1.1.1, q.1.1.2, q.1.2, q.2))
      encEncapsCoin encEncDetInput)
  have hk : IsOraclePPTOn encEncapsCoin encBits
      (fun q : ((ℕ × List Bool) × List Bool) × List Bool =>
        queryH keyLen q.1.1.1 (false, q.1.2, P.encDet q.1.1.1 q.1.1.2 q.1.2 q.2)) :=
    IsOraclePPTOn.query_take' RO.H
      (((ComputableInPolyTime.const false).prod
        ((by fun_prop : ComputableInPolyTime
          (fun q : ((ℕ × List Bool) × List Bool) × List Bool => q.1.2) encEncapsCoin encBits).prod
            hc)).encoding_comp)
      (hkeyLen.comp (by fun_prop))
  have hpost : ComputableInPolyTime
      (fun pair : (((ℕ × List Bool) × List Bool) × List Bool) × List Bool =>
        (P.encDet pair.1.1.1.1 pair.1.1.1.2 pair.1.1.2 pair.1.2, pair.2))
      (encPair encEncapsCoin encBits) (encPair encBits encBits) :=
    (hc.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)
  have hck : IsOraclePPTOn encEncapsCoin (encPair encBits encBits)
      (fun q : ((ℕ × List Bool) × List Bool) × List Bool =>
        (fun k => (P.encDet q.1.1.1 q.1.1.2 q.1.2 q.2, k)) <$>
          queryH keyLen q.1.1.1 (false, q.1.2, P.encDet q.1.1.1 q.1.1.2 q.1.2 q.2)) :=
    hk.map_with' (f := fun q k => (P.encDet q.1.1.1 q.1.1.2 q.1.2 q.2, k)) hpost
  have hrest := IsOraclePPTOn.bind_with (first := fun p : (ℕ × List Bool) × List Bool =>
      P.queryG p.1.1 p.2) (second := fun p r =>
      (fun k => (P.encDet p.1.1 p.1.2 p.2 r, k)) <$>
        queryH keyLen p.1.1 (false, p.2, P.encDet p.1.1 p.1.2 p.2 r)) hr hck
  have hall := IsOraclePPTOn.bind_with (first := fun x : ℕ × List Bool =>
      ProbOracleComp.sample (BitString.sampleList (P.msgLen x.1)))
    (second := fun x m => do
      let r ← P.queryG x.1 m
      (fun k => (P.encDet x.1 x.2 m r, k)) <$>
        queryH keyLen x.1 (false, m, P.encDet x.1 x.2 m r)) hm hrest
  refine hall.congr fun x _ _ _ => ?_
  simp only [encaps, bind_pure_comp]

/-- Decryption of the bundle, `dec` filtered to messages of length `msgLen n`, as an optional
elimination. -/
private theorem toExplicitCoin_dec (n : ℕ) (sk c : List Bool) :
    (P.toExplicitCoin n).dec sk c =
      (P.dec n sk c).elim none fun m => if m.length = P.msgLen n then some m else none := by
  simp only [toExplicitCoin]
  cases P.dec n sk c with
  | none => rfl
  | some m => simp [Option.filter]

/-- Decryption of the bundle is polynomial-time on `(1ⁿ, sk, c)`. -/
private theorem computableInPolyTime_toExplicitCoin_dec (hP : P.IsEfficient) :
    ComputableInPolyTime (fun (n, sk, c) => (P.toExplicitCoin n).dec sk c)
      (encKeyedInput encBits) (encOption encBits) := by
  simp only [toExplicitCoin_dec]
  have hmsg : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool =>
        decide (p.2.length = P.msgLen p.1.1))
      (encPair (encKeyedInput encBits) encBits) encBool :=
    ComputableInPolyTime.decide_eq' (by fun_prop) (hP.msgLen.comp (by fun_prop))
  exact ComputableInPolyTime.optionElimWithInput hP.dec (ComputableInPolyTime.const none)
    (ComputableInPolyTime.ite_decide hmsg (by fun_prop) (ComputableInPolyTime.const none))

/-- Native `FO-notbot` decapsulation is uniform strict oracle PPT on `(1ⁿ, dk, c)`, for every pair
of external oracles `G` and `H`. -/
theorem isOraclePPTOn_decapsNotBot (hP : P.IsEfficient)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsOraclePPTOn encDecapsNotBotInput (encOption encBits)
      (fun (n, dk, c) => P.decapsNotBot keyLen n dk c) := by
  change IsOraclePPTOn encDecapsNotBotInput _ (fun x => P.decapsNotBot keyLen x.1 x.2.1 x.2.2)
  have hD : ComputableInPolyTime
      (fun x : ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool =>
        (P.toExplicitCoin x.1).dec x.2.1.sk x.2.2) encDecapsNotBotInput (encOption encBits) :=
    (computableInPolyTime_toExplicitCoin_dec hP).comp (by fun_prop :
      ComputableInPolyTime
        (fun x : ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool =>
          (x.1, x.2.1.sk, x.2.2)) encDecapsNotBotInput (encKeyedInput encBits))
  have hm : ComputableInPolyTime
      (fun x : ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool =>
        ((P.toExplicitCoin x.1).dec x.2.1.sk x.2.2).getD []) encDecapsNotBotInput encBits := by
    fun_prop
  have hfallback : IsOraclePPTOn encDecapsNotBotInput encBits
      (fun x : ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool =>
        queryH keyLen x.1 (true, x.2.1.fallback, x.2.2)) :=
    IsOraclePPTOn.query_take' RO.H (by fun_prop) (hkeyLen.comp (by fun_prop))
  have hn : ComputableInPolyTime
      (fun x : ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool => x.1)
      encDecapsNotBotInput encUnary := by fun_prop
  have hn' : ComputableInPolyTime
      (fun p : (ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool) × List Bool =>
        p.1.1) (encPair encDecapsNotBotInput encBits) encUnary := by fun_prop
  have hG := IsOraclePPTOn.query_take' RO.G hm (hP.coinLen.comp hn)
  have hmQ : ComputableInPolyTime
      (fun p : (ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool) × List Bool =>
        ((P.toExplicitCoin p.1.1).dec p.1.2.1.sk p.1.2.2).getD [])
      (encPair encDecapsNotBotInput encBits) encBits :=
    hm.comp (ComputableInPolyTime.fst _ _)
  have hcQ : ComputableInPolyTime
      (fun p : (ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool) × List Bool =>
        p.1.2.2) (encPair encDecapsNotBotInput encBits) encBits := by fun_prop
  have hcheck : ComputableInPolyTime
      (fun p : (ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool) × List Bool =>
        decide (P.encDet p.1.1 p.1.2.1.pk
          (((P.toExplicitCoin p.1.1).dec p.1.2.1.sk p.1.2.2).getD []) p.2 = p.1.2.2))
      (encPair encDecapsNotBotInput encBits) encBool :=
    ComputableInPolyTime.decide_eq' (hP.encDet.comp (hn'.prod ((by fun_prop :
      ComputableInPolyTime
        (fun p : (ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool) × List Bool =>
          p.1.2.1.pk) (encPair encDecapsNotBotInput encBits) encBits).prod
      (hmQ.prod (ComputableInPolyTime.snd _ _))))) hcQ
  have hvalid : IsOraclePPTOn (encPair encDecapsNotBotInput encBits) encBits
      (fun p : (ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool) × List Bool =>
        queryH keyLen p.1.1
          (false, ((P.toExplicitCoin p.1.1).dec p.1.2.1.sk p.1.2.2).getD [], p.1.2.2)) :=
    IsOraclePPTOn.query_take' RO.H
      (((ComputableInPolyTime.const false).prod (hmQ.prod hcQ)).encoding_comp) (hkeyLen.comp hn')
  have hreject := hfallback.preprocess' (ComputableInPolyTime.fst encDecapsNotBotInput encBits)
  have hafter := IsOraclePPTOn.ite' hcheck hvalid hreject
  have hsome := IsOraclePPTOn.bind_with
    (first := fun x : ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool =>
      P.queryG x.1 (((P.toExplicitCoin x.1).dec x.2.1.sk x.2.2).getD []))
    (second := fun x r =>
      if P.encDet x.1 x.2.1.pk (((P.toExplicitCoin x.1).dec x.2.1.sk x.2.2).getD []) r =
          x.2.2 then
        queryH keyLen x.1 (false, ((P.toExplicitCoin x.1).dec x.2.1.sk x.2.2).getD [], x.2.2)
      else queryH keyLen x.1 (true, x.2.1.fallback, x.2.2)) hG hafter
  have hbody := IsOraclePPTOn.cond'
    (ComputableTidilyInPolyTime.optionIsSome hD.tidy).computableInPolyTime hsome hfallback
  have hall := IsOraclePPTOn.ite'
    (condition := fun x : ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool =>
      x.2.2.length ≤ P.ctLen x.1)
    (ComputableInPolyTime.unary_le' (by fun_prop) (hP.ctLen.comp hn))
    (hbody.map' (by fun_prop : ComputableInPolyTime (some (α := List Bool)) encBits
      (encOption encBits)))
    ((ComputableInPolyTime.const (none : Option (List Bool))).isOraclePPTOn)
  refine hall.congr fun x _ _ _ => ?_
  obtain ⟨n, dk, c⟩ := x
  congr 1
  simp only [decapsNotBot]
  refine if_congr Iff.rfl ?_ rfl
  congr 1
  rw [Scheme.decapsNotBotM_eq]
  simp only [scheme]
  cases (P.toExplicitCoin n).dec dk.sk c with
  | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  | some m =>
    simp only [Option.isSome_some, ↓reduceIte, Option.getD_some]
    congr 1 with r

/-- Native `FO^⊥` decapsulation is uniform strict oracle PPT on `(1ⁿ, pk, sk, c)`, for every pair
of external oracles `G` and `H`. -/
theorem isOraclePPTOn_decapsBot (hP : P.IsEfficient)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsOraclePPTOn encDecapsBotInput (encOption encBits)
      (fun (n, pk, sk, c) => P.decapsBot keyLen n pk sk c) := by
  change IsOraclePPTOn encDecapsBotInput _ (fun x => P.decapsBot keyLen x.1 x.2.1 x.2.2.1 x.2.2.2)
  have hn : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool × List Bool => x.1)
      encDecapsBotInput encUnary := by fun_prop
  have hn' : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool × List Bool) × List Bool => p.1.1)
      (encPair encDecapsBotInput encBits) encUnary := by fun_prop
  have hD : ComputableInPolyTime
      (fun x : ℕ × List Bool × List Bool × List Bool => (P.toExplicitCoin x.1).dec x.2.2.1 x.2.2.2)
      encDecapsBotInput (encOption encBits) :=
    (computableInPolyTime_toExplicitCoin_dec hP).comp (by fun_prop :
      ComputableInPolyTime (fun x : ℕ × List Bool × List Bool × List Bool =>
        (x.1, x.2.2.1, x.2.2.2)) encDecapsBotInput (encKeyedInput encBits))
  have hm : ComputableInPolyTime
      (fun x : ℕ × List Bool × List Bool × List Bool =>
        ((P.toExplicitCoin x.1).dec x.2.2.1 x.2.2.2).getD []) encDecapsBotInput encBits := by
    fun_prop
  have hmQ : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool × List Bool) × List Bool =>
        ((P.toExplicitCoin p.1.1).dec p.1.2.2.1 p.1.2.2.2).getD [])
      (encPair encDecapsBotInput encBits) encBits :=
    hm.comp (ComputableInPolyTime.fst _ _)
  have hcQ : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool × List Bool) × List Bool => p.1.2.2.2)
      (encPair encDecapsBotInput encBits) encBits := by fun_prop
  have hG := IsOraclePPTOn.query_take' RO.G hm (hP.coinLen.comp hn)
  have hcheck : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool × List Bool) × List Bool =>
        decide (P.encDet p.1.1 p.1.2.1
          (((P.toExplicitCoin p.1.1).dec p.1.2.2.1 p.1.2.2.2).getD []) p.2 = p.1.2.2.2))
      (encPair encDecapsBotInput encBits) encBool :=
    ComputableInPolyTime.decide_eq' (hP.encDet.comp (hn'.prod ((by fun_prop :
      ComputableInPolyTime (fun p : (ℕ × List Bool × List Bool × List Bool) × List Bool =>
        p.1.2.1) (encPair encDecapsBotInput encBits) encBits).prod
      (hmQ.prod (ComputableInPolyTime.snd _ _))))) hcQ
  have hH : IsOraclePPTOn (encPair encDecapsBotInput encBits) encBits
      (fun p : (ℕ × List Bool × List Bool × List Bool) × List Bool =>
        queryH keyLen p.1.1
          (false, ((P.toExplicitCoin p.1.1).dec p.1.2.2.1 p.1.2.2.2).getD [], p.1.2.2.2)) :=
    IsOraclePPTOn.query_take' RO.H
      (((ComputableInPolyTime.const false).prod (hmQ.prod hcQ)).encoding_comp) (hkeyLen.comp hn')
  have hvalid := hH.map' (f := some) (by fun_prop : ComputableInPolyTime (some (α := List Bool))
    encBits (encOption encBits))
  have hnone {α : Type} {input : α ↪ List Bool} :
      IsOraclePPTOn (Operation := RO) input (encOption encBits)
        (fun _ => pure (none : Option (List Bool))) :=
    (ComputableInPolyTime.const (none : Option (List Bool))).isOraclePPTOn
  have hafter := IsOraclePPTOn.ite' hcheck hvalid hnone
  have hsome := IsOraclePPTOn.bind_with
    (first := fun x : ℕ × List Bool × List Bool × List Bool =>
      P.queryG x.1 (((P.toExplicitCoin x.1).dec x.2.2.1 x.2.2.2).getD []))
    (second := fun x r =>
      if P.encDet x.1 x.2.1 (((P.toExplicitCoin x.1).dec x.2.2.1 x.2.2.2).getD []) r =
          x.2.2.2 then
        some <$> queryH keyLen x.1
          (false, ((P.toExplicitCoin x.1).dec x.2.2.1 x.2.2.2).getD [], x.2.2.2)
      else pure none) hG hafter
  have hbody := IsOraclePPTOn.cond'
    (ComputableTidilyInPolyTime.optionIsSome hD.tidy).computableInPolyTime hsome hnone
  have hall := IsOraclePPTOn.ite'
    (condition := fun x : ℕ × List Bool × List Bool × List Bool =>
      x.2.2.2.length ≤ P.ctLen x.1)
    (ComputableInPolyTime.unary_le' (by fun_prop) (hP.ctLen.comp hn)) hbody hnone
  refine hall.congr fun x _ _ _ => ?_
  obtain ⟨n, pk, sk, c⟩ := x
  congr 1
  simp only [decapsBot]
  refine if_congr Iff.rfl ?_ rfl
  rw [Scheme.decapsBotM_eq]
  simp only [scheme]
  cases (P.toExplicitCoin n).dec sk c <;> simp [toExplicitCoin]

end IsEfficient

end WordPKE

end Cslib.Crypto.Protocols.FujisakiOkamoto
