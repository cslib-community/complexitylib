/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Crypto.Computational.SchnorrProtocol
public import Complexity.Crypto.Protocols.SigmaProtocol.SchnorrSignature
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Data.BitString.Counter
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# Computational Schnorr signatures under the discrete-logarithm assumption

Schnorr's signature scheme ([Schnorr1991]; [BonehShoup2023], Sections 19.2–19.3) applies the
Fiat–Shamir transform ([FiatShamir1986]; [PointchevalStern2000]) to Schnorr's identification
protocol over a `PrimeOrderGroupFamily` `F`:

1. **Bit-encoded Schnorr signature operations and strict-PPT certificates**:
   * **Key generation** (`schnorrSigKeyGen`): at security parameter `n` and group description `d`,
     samples `sk ← F.sampleExp n d` (`ProbComp.sampleModNat`) and outputs the encoded public key
     `F.smul (d, sk, F.encode d (F.generator d))` (`encode (sk • g)`) and encoded secret key
     `(sk % F.order d).bits`. It is uniform strict PPT (`isPPTOn_schnorrSigKeyGen`) and within
     statistical distance `1 / 2 ^ n` of the ideal encoded Schnorr key generator
     (`closeTo_schnorrSigKeyGen`).
   * **Commitment, response, and signing** (`schnorrCommitBits`, `schnorrRespondBits`,
     `schnorrSignCoins`): given the description `d`, encoded secret key `sk`, message `msg`,
     commitment randomness `r`, and `k n`-bit random-oracle challenge `roOut`, computes the encoded
     commitment `t = r • g` and response `z = (r + roOut * sk) mod q`, both certified in
     `ComputableInPolyTime` and `IsPPTOn`.
   * **Verification and commitment recovery** (`schnorrSigVerifyBits`, `schnorrRecoverCommitBits`):
     compares the commitment word with the canonical recovery of `z • g - roOut • pk`.
     Under a canonical public key, acceptance forces a canonical commitment without a decoder.
     Both operations run in polynomial time (`computableInPolyTime_schnorrSigVerifyBits`,
     `computableInPolyTime_schnorrRecoverCommitBits`), with exact completeness on honest signatures
     (`schnorrSigVerifyBits_schnorrSignCoins`).

2. **Typed ROM scheme instantiation and Pointcheval–Stern / Bellare–Neven security bound**:
   * `schnorrFamilyROMScheme` instantiates the Fiat–Shamir ROM signature scheme over `F.Carrier d`
     with `m`-bit challenges `BitString m` embedded into `ZMod (F.order d)` whenever
     `2 ^ m ≤ F.order d` (`challengeEmbedding`, `schnorrBitSigma`), alongside the full-scalar
     scheme `schnorrScalarROMScheme`.
   * `succProbability_eufCmaGame_schnorrFamilyROMScheme_le` and
     `succProbability_eufCmaGame_schnorrScalarROMScheme_le` specialize
     `schnorr_succProbability_eufCmaGame_le` ([BonehShoup2023], Theorem 19.7 with Equation 19.21;
     [PointchevalStern2000]; [BellareNeven2006]) to `F.Carrier d`, bounding any `(Qs, Qro)`-bounded
     forger's EUF-CMA success probability by
     `Qs · (Qs + Qro) / q + (Qro + 1) / 2 ^ m + √((Qro + 1) · ε')`, where `ε'` is the
     discrete-logarithm success probability of the forking reduction
     (`oneWayGame_schnorrKeyGen_eq`), with asymptotic negligibility in
     `negligible_eufCmaGame_schnorrFamilyROMScheme`.

The typed security theorem is conditional on the success probability of its explicit forking
reduction. Applying `F.DiscreteLog` requires a separate strict-PPT realization of that reduction,
including its shared signing/hash oracle and private-coin replay. The bit-encoded arithmetic
certificates in this module do not establish that realization. Strict-PPT identification and
eavesdropping security are provided by `SchnorrIdentification` and `SchnorrEavesdrop`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigKeyGen`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrCommitBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrRespondBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSignCoins`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigVerifyBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrRecoverCommitBits`: bit-encoded Schnorr signature
  key generation, commitment, response, signing, verification, and commitment recovery.
* `Cslib.Crypto.PrimeOrderGroupFamily.challengeEmbedding`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrBitSigma`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrFamilyROMScheme`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrScalarROMScheme`: Fiat–Shamir ROM Schnorr signature
  schemes over `F` with `m`-bit and scalar challenges.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrSigKeyGen`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrCommitBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrRespondBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrSignCoins`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrSigVerifyBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrRecoverCommitBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigVerifyBits_schnorrSignCoins`: polynomial-time and
  strict-PPT certificates and completeness of the bit-encoded operations.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigVerifyBits_eq_true_iff`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigVerifyBits_commitment_mem_range`: acceptance under
  a canonical public key forces the exact recovered encoding, for arbitrary response and challenge
  words.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrFamilyROMScheme_correct`,
  `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_eufCmaGame_schnorrFamilyROMScheme_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_eufCmaGame_schnorrScalarROMScheme_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.negligible_eufCmaGame_schnorrFamilyROMScheme`: ROM correctness
  and Pointcheval–Stern / Bellare–Neven EUF-CMA bounds.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 19.2–19.3 (Theorems 19.7 and 19.16).
* [D. Pointcheval, J. Stern, *Security Arguments for Digital Signatures and Blind
  Signatures*][PointchevalStern2000].
* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General Forking
  Lemma*][BellareNeven2006], Lemma 1.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991].
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Protocols.ROMSignature
  Interactive
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### 1. Bit-encoded Schnorr signature algorithms and strict-PPT certificates -/

/-- Ideal encoded Schnorr key generation for group description `d`: sample a uniform secret scalar
`α : ZMod (F.order d)` and output the encoded public key `F.encode d (α • F.generator d)` paired
with the binary-encoded secret key `F.encScalar d α`. -/
noncomputable def schnorrIdealKeyGen (d : F.Desc) : PMF (List Bool × List Bool) :=
  (PMF.uniformOfFintype (ZMod (F.order d))).map
    fun α => (F.encode d (α • F.generator d), F.encScalar d α)

/-- Bit-encoded Schnorr signature key generation at security parameter `n` and group description `d`
([BonehShoup2023], Section 19.2): sample an approximate uniform exponent `sk ← F.sampleExp n d` and
output the encoded public key `F.smul (d, sk, F.encode d (F.generator d))` together with the binary
secret key `(sk % F.order d).bits`. -/
noncomputable def schnorrSigKeyGen (n : ℕ) (d : F.Desc) : ProbComp (List Bool × List Bool) := do
  let sk ← F.sampleExp n d
  return (F.smul (d, sk, F.encode d (F.generator d)), (sk % F.order d).bits)

/-- Output distribution of `schnorrSigKeyGen`: the sampled exponent modulo `F.order d` determines
the encoded public key `α • g` and secret scalar `α`. -/
theorem eval_schnorrSigKeyGen (n : ℕ) (d : F.Desc) :
    ProbComp.eval (F.schnorrSigKeyGen n d) =
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).map
        fun α => (F.encode d (α • F.generator d), F.encScalar d α) := by
  rw [schnorrSigKeyGen, ProbComp.eval_bind, PMF.map_comp]
  simp only [ProbComp.eval_pure, F.smul_encode, encScalar, Function.Embedding.coeFn_mk,
    encNat_apply]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext s
  simp only [Function.comp_apply, ZMod.val_natCast]

/-- `schnorrSigKeyGen n d` is within statistical distance `1 / 2 ^ n` of the ideal encoded Schnorr
key generator `schnorrIdealKeyGen d`. -/
theorem closeTo_schnorrSigKeyGen (n : ℕ) (d : F.Desc) :
    CloseTo (F.schnorrIdealKeyGen d) (ProbComp.eval (F.schnorrSigKeyGen n d))
      (1 / 2 ^ n : ℝ≥0) := by
  rw [schnorrIdealKeyGen, eval_schnorrSigKeyGen]
  exact (F.closeTo_uniform_sampleExp n d).map _

/-- **Schnorr signature key generation is uniform strict PPT** in the unary security parameter and
the group description. -/
theorem isPPTOn_schnorrSigKeyGen :
    IsPPTOn (encPair encUnary F.encDesc) (encPair encBits encBits)
      (fun input => F.schnorrSigKeyGen input.1 input.2) := by
  let encIn := encPair encUnary F.encDesc
  have hn : ComputableInPolyTime (fun p : ℕ × F.Desc => p.1) encIn encUnary := by fun_prop
  have hd : ComputableInPolyTime (fun p : ℕ × F.Desc => p.2) encIn F.encDesc := by fun_prop
  change IsPPTOn encIn (encPair encBits encBits) fun p =>
    F.sampleExp p.1 p.2 >>= fun sk =>
      pure (F.smul (p.2, sk, F.encode p.2 (F.generator p.2)), (sk % F.order p.2).bits)
  refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
  let encMid := encPair encIn encNat
  have hd' : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => p.1.2) encMid F.encDesc := by
    fun_prop
  have hsk : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => p.2) encMid encNat := by
    fun_prop
  have hq := F.computableInPolyTime_order.comp hd'
  have hg := F.computableInPolyTime_generator.comp hd'
  have hpk := F.computableInPolyTime_smul.comp (hd'.prod (hsk.prod hg))
  have hsk_bits : ComputableInPolyTime
      (fun p : (ℕ × F.Desc) × ℕ => (p.2 % F.order p.1.2).bits) encMid encBits :=
    .of_tidy (ComputableTidilyInPolyTime.natBits.comp (.binary_mod' hsk.tidy hq.tidy))
  exact (hpk.prod hsk_bits).isPPTOn

/-- Bit-level Schnorr commitment: given `(d, r)` where `r` is the binary-encoded commitment
exponent, compute the encoded group element `r • g`. -/
def schnorrCommitBits (input : F.Desc × List Bool) : List Bool :=
  let (d, r) := input
  F.smul (d, ofBits r, F.encode d (F.generator d))

/-- On an encoded scalar `r : ZMod (F.order d)`, `schnorrCommitBits` produces
`F.encode d (r • g)`. -/
@[simp] theorem schnorrCommitBits_encScalar (d : F.Desc) (r : ZMod (F.order d)) :
    F.schnorrCommitBits (d, F.encScalar d r) = F.encode d (r • F.generator d) := by
  simp only [schnorrCommitBits, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits,
    Nat.foldr_bit_bits, F.smul_encode, ZMod.natCast_zmod_val]

/-- **Bit-level Schnorr commitment is computable in polynomial time**. -/
theorem computableInPolyTime_schnorrCommitBits :
    ComputableInPolyTime F.schnorrCommitBits (encPair F.encDesc encBits) encBits := by
  let encIn := encPair F.encDesc encBits
  have hd : ComputableInPolyTime (fun p : F.Desc × List Bool => p.1) encIn F.encDesc := by fun_prop
  have hr : ComputableInPolyTime (fun p : F.Desc × List Bool => p.2) encIn encBits := by fun_prop
  have hr_nat : ComputableInPolyTime (fun p : F.Desc × List Bool => ofBits p.2) encIn encNat :=
    .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp hr.tidy)
  have hg := F.computableInPolyTime_generator.comp hd
  exact F.computableInPolyTime_smul.comp (hd.prod (hr_nat.prod hg))

/-- `schnorrCommitBits` lifted to `ProbComp` is uniform strict PPT. -/
theorem isPPTOn_schnorrCommitBits :
    IsPPTOn (encPair F.encDesc encBits) encBits (fun input => pure (F.schnorrCommitBits input)) :=
  F.computableInPolyTime_schnorrCommitBits.isPPTOn

/-- Bit-level Schnorr response: given `(d, sk, r, roOut)` where `sk` is the encoded secret key, `r`
is the encoded commitment randomness, and `roOut` is the random-oracle challenge bit string, compute
`((ofBits r + ofBits roOut * ofBits sk) % F.order d).bits`. -/
def schnorrRespondBits (input : F.Desc × List Bool × List Bool × List Bool) : List Bool :=
  let (d, sk, r, roOut) := input
  ((ofBits r + ofBits roOut * ofBits sk) % F.order d).bits

/-- On encoded scalars `α, r : ZMod (F.order d)`, `schnorrRespondBits` computes the encoded scalar
`r + (ofBits roOut : ZMod (F.order d)) * α`. -/
@[simp] theorem schnorrRespondBits_encScalar (d : F.Desc) (α r : ZMod (F.order d))
    (roOut : List Bool) :
    F.schnorrRespondBits (d, F.encScalar d α, F.encScalar d r, roOut) =
      F.encScalar d (r + (ofBits roOut : ZMod (F.order d)) * α) := by
  simp only [schnorrRespondBits, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits,
    Nat.foldr_bit_bits]
  congr 1
  rw [← ZMod.val_natCast (F.order d), Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]

/-- **Bit-level Schnorr response is computable in polynomial time**. -/
theorem computableInPolyTime_schnorrRespondBits :
    ComputableInPolyTime F.schnorrRespondBits
      (encPair F.encDesc (encPair encBits (encPair encBits encBits))) encBits := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits encBits))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.1) encIn F.encDesc := by fun_prop
  have hsk : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.1) encIn encBits := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.2.1) encIn encBits := by fun_prop
  have hro : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.2.2) encIn encBits := by fun_prop
  have hq := (F.computableInPolyTime_order.comp hd).tidy
  have hsk_nat := ComputableTidilyInPolyTime.bitsToNat.comp hsk.tidy
  have hr_nat := ComputableTidilyInPolyTime.bitsToNat.comp hr.tidy
  have hro_nat := ComputableTidilyInPolyTime.bitsToNat.comp hro.tidy
  exact .of_tidy (ComputableTidilyInPolyTime.natBits.comp
    (.binary_mod' (.binary_add' hr_nat (.binary_mul' hro_nat hsk_nat)) hq))

/-- `schnorrRespondBits` lifted to `ProbComp` is uniform strict PPT. -/
theorem isPPTOn_schnorrRespondBits :
    IsPPTOn (encPair F.encDesc (encPair encBits (encPair encBits encBits))) encBits
      (fun input => pure (F.schnorrRespondBits input)) :=
  F.computableInPolyTime_schnorrRespondBits.isPPTOn

/-- Deterministic bit-encoded Schnorr signing from explicit coins and a random-oracle challenge
([BonehShoup2023], Section 19.2): given `(d, sk, msg, r, roOut)` where `r` is the commitment
randomness and `roOut` is the random-oracle digest on `(msg, encode (r • g))`, output the encoded
signature `(t, z) = (schnorrCommitBits (d, r), schnorrRespondBits (d, sk, r, roOut))`.
This arithmetic kernel takes `roOut` as an input; its caller must obtain it from the shared hash
oracle. The message is not used again once that challenge has been supplied. -/
def schnorrSignCoins
    (input : F.Desc × List Bool × List Bool × List Bool × List Bool) : List Bool × List Bool :=
  let (d, sk, _msg, r, roOut) := input
  (F.schnorrCommitBits (d, r), F.schnorrRespondBits (d, sk, r, roOut))

/-- On encoded scalars `α, r : ZMod (F.order d)`, `schnorrSignCoins` outputs the encoded commitment
`r • g` and response `r + c * α`. -/
@[simp] theorem schnorrSignCoins_encScalar (d : F.Desc) (α r : ZMod (F.order d))
    (msg roOut : List Bool) :
    F.schnorrSignCoins (d, F.encScalar d α, msg, F.encScalar d r, roOut) =
      (F.encode d (r • F.generator d),
        F.encScalar d (r + (ofBits roOut : ZMod (F.order d)) * α)) := by
  simp only [schnorrSignCoins, schnorrCommitBits_encScalar, schnorrRespondBits_encScalar]

/-- **Deterministic bit-level Schnorr signing `schnorrSignCoins` is computable in polynomial
time**. -/
theorem computableInPolyTime_schnorrSignCoins :
    ComputableInPolyTime F.schnorrSignCoins
      (encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits encBits))))
      (encPair encBits encBits) := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits encBits)))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.1)
      encIn F.encDesc := by fun_prop
  have hsk : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.1)
      encIn encBits := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.2.2.1)
      encIn encBits := by fun_prop
  have hro : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.2.2.2)
      encIn encBits := by fun_prop
  have hcommit := F.computableInPolyTime_schnorrCommitBits.comp (hd.prod hr)
  have hresp := F.computableInPolyTime_schnorrRespondBits.comp (hd.prod (hsk.prod (hr.prod hro)))
  exact hcommit.prod hresp

/-- `schnorrSignCoins` lifted to `ProbComp` is uniform strict PPT. -/
theorem isPPTOn_schnorrSignCoins :
    IsPPTOn (encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits encBits))))
      (encPair encBits encBits) (fun input => pure (F.schnorrSignCoins input)) :=
  F.computableInPolyTime_schnorrSignCoins.isPPTOn

/-- Bit-level Schnorr commitment recovery ([BonehShoup2023], Section 19.2.1): given
`(d, pk, roOut, z)`, compute the encoded group element `z • g - roOut • pk`. -/
def schnorrRecoverCommitBits (input : F.Desc × List Bool × List Bool × List Bool) : List Bool :=
  let (d, pk, roOut, z) := input
  F.add (d, F.smul (d, ofBits z, F.encode d (F.generator d)),
    F.smul (d, F.order d - ofBits roOut % F.order d, pk))

/-- **Bit-level Schnorr commitment recovery is computable in polynomial time**. -/
theorem computableInPolyTime_schnorrRecoverCommitBits :
    ComputableInPolyTime F.schnorrRecoverCommitBits
      (encPair F.encDesc (encPair encBits (encPair encBits encBits))) encBits := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits encBits))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.1) encIn F.encDesc := by fun_prop
  have hpk : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.1) encIn encBits := by fun_prop
  have hro : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.2.1) encIn encBits := by fun_prop
  have hz : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.2.2) encIn encBits := by fun_prop
  have hq := F.computableInPolyTime_order.comp hd
  have hg := F.computableInPolyTime_generator.comp hd
  have hz_nat : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => ofBits p.2.2.2) encIn encNat :=
    .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp hz.tidy)
  have hzg := F.computableInPolyTime_smul.comp (hd.prod (hz_nat.prod hg))
  have hneg : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool =>
        F.order p.1 - ofBits p.2.2.1 % F.order p.1) encIn encNat :=
    .of_tidy (.binary_sub' hq.tidy
      (.binary_mod' (ComputableTidilyInPolyTime.bitsToNat.comp hro.tidy) hq.tidy))
  have hcpk := F.computableInPolyTime_smul.comp (hd.prod (hneg.prod hpk))
  exact F.computableInPolyTime_add.comp (hd.prod (hzg.prod hcpk))

/-- On an encoded public key `pk = F.encode d u`, `schnorrRecoverCommitBits` computes the encoding
of `z • g - roOut • u`. -/
@[simp] theorem schnorrRecoverCommitBits_encode (d : F.Desc) (u : F.Carrier d)
    (roOut z : List Bool) :
    F.schnorrRecoverCommitBits (d, F.encode d u, roOut, z) =
      F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
        (ofBits roOut : ZMod (F.order d)) • u) := by
  have hneg : ((F.order d - ofBits roOut % F.order d : ℕ) : ZMod (F.order d)) =
      -(ofBits roOut : ZMod (F.order d)) := by
    rw [Nat.cast_sub (Nat.mod_lt _ (F.prime_order d).pos).le, ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  simp only [schnorrRecoverCommitBits, F.smul_encode, F.add_encode, hneg, neg_smul,
    ← sub_eq_add_neg]

/-- Bit-encoded Schnorr signature verification ([BonehShoup2023], Section 19.2): given
`(d, pk, msg, (t, z), roOut)` where `roOut` is the random-oracle challenge for `(msg, t)`, compare
`t` with the canonical encoding of `z • g - roOut • pk`. For a canonical public key this rejects
noncanonical commitments without requiring a group-membership decoder. This checks the algebraic
equation for a supplied challenge; the caller must enforce `roOut = H(msg, t)` in the same
oracle world used by the signer and adversary. -/
def schnorrSigVerifyBits
    (input : F.Desc × List Bool × List Bool × (List Bool × List Bool) × List Bool) : Bool :=
  let (d, pk, _msg, (t, z), roOut) := input
  t == F.schnorrRecoverCommitBits (d, pk, roOut, z)

/-- **Bit-level Schnorr signature verification `schnorrSigVerifyBits` is computable in polynomial
time**. -/
theorem computableInPolyTime_schnorrSigVerifyBits :
    ComputableInPolyTime F.schnorrSigVerifyBits
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair (encPair encBits encBits) encBits))))
      encBool := by
  let encIn := encPair F.encDesc
    (encPair encBits (encPair encBits (encPair (encPair encBits encBits) encBits)))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × (List Bool × List Bool) × List Bool => p.1)
      encIn F.encDesc := by fun_prop
  have hpk : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × (List Bool × List Bool) × List Bool => p.2.1)
      encIn encBits := by fun_prop
  have ht : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × (List Bool × List Bool) × List Bool => p.2.2.2.1.1)
      encIn encBits := by fun_prop
  have hz : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × (List Bool × List Bool) × List Bool => p.2.2.2.1.2)
      encIn encBits := by fun_prop
  have hro : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × (List Bool × List Bool) × List Bool => p.2.2.2.2)
      encIn encBits := by fun_prop
  have hrecover := F.computableInPolyTime_schnorrRecoverCommitBits.comp
    (hd.prod (hpk.prod (hro.prod hz)))
  have hbeq : ComputableInPolyTime (fun q : List Bool × List Bool => q.1 == q.2)
      (encPair encBits encBits) encBool := by fun_prop
  exact hbeq.comp (ht.prod hrecover)

/-- `schnorrSigVerifyBits` lifted to `ProbComp` is uniform strict PPT. -/
theorem isPPTOn_schnorrSigVerifyBits :
    IsPPTOn
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair (encPair encBits encBits) encBits))))
      encBool (fun input => pure (F.schnorrSigVerifyBits input)) :=
  F.computableInPolyTime_schnorrSigVerifyBits.isPPTOn

/-- On encoded group elements `pk = F.encode d u` and `t = F.encode d T`, `schnorrSigVerifyBits`
decides Schnorr's verification equation `z • g = T + c • u`. -/
theorem schnorrSigVerifyBits_encode (d : F.Desc) (u T : F.Carrier d)
    (msg z roOut : List Bool) :
    F.schnorrSigVerifyBits (d, F.encode d u, msg, (F.encode d T, z), roOut) =
      decide ((ofBits z : ZMod (F.order d)) • F.generator d =
        T + (ofBits roOut : ZMod (F.order d)) • u) := by
  simp only [schnorrSigVerifyBits, schnorrRecoverCommitBits_encode, beq_eq_decide,
    (F.encode_injective d).eq_iff, eq_sub_iff_add_eq, eq_comm]

/-- **Completeness of bit-encoded Schnorr signing and verification**: every signature produced by
`schnorrSignCoins` on a key pair `(encode (α • g), encScalar α)` verifies under
`schnorrSigVerifyBits` with the same random-oracle challenge `roOut`. -/
theorem schnorrSigVerifyBits_schnorrSignCoins (d : F.Desc) (α r : ZMod (F.order d))
    (msg roOut : List Bool) :
    F.schnorrSigVerifyBits
      (d, F.encode d (α • F.generator d), msg,
        F.schnorrSignCoins (d, F.encScalar d α, msg, F.encScalar d r, roOut), roOut) =
      true := by
  rw [schnorrSignCoins_encScalar, schnorrSigVerifyBits_encode]
  simp only [encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits, Nat.foldr_bit_bits,
    ZMod.natCast_zmod_val, add_smul, mul_smul, decide_true]

/-- Verification compares the supplied commitment with public commitment recovery on all words,
including malformed inputs. -/
theorem schnorrSigVerifyBits_eq_decide_recover (d : F.Desc)
    (pk msg t z roOut : List Bool) :
    F.schnorrSigVerifyBits (d, pk, msg, (t, z), roOut) =
      decide (t = F.schnorrRecoverCommitBits (d, pk, roOut, z)) := by
  simp only [schnorrSigVerifyBits, beq_eq_decide]

/-- Under a canonical public key, acceptance forces the exact canonical recovered commitment.
The response and supplied challenge are arbitrary words, interpreted as scalars modulo the order.
No encoding-range conclusion is asserted for malformed public keys. -/
theorem schnorrSigVerifyBits_eq_true_iff (d : F.Desc) (u : F.Carrier d)
    (msg t z roOut : List Bool) :
    F.schnorrSigVerifyBits (d, F.encode d u, msg, (t, z), roOut) = true ↔
      t = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
        (ofBits roOut : ZMod (F.order d)) • u) := by
  simp only [schnorrSigVerifyBits, schnorrRecoverCommitBits_encode, beq_iff_eq]

/-- Every accepted commitment is in the encoding range when the public key is canonical. -/
theorem schnorrSigVerifyBits_commitment_mem_range (d : F.Desc) (u : F.Carrier d)
    (msg t z roOut : List Bool)
    (h : F.schnorrSigVerifyBits (d, F.encode d u, msg, (t, z), roOut) = true) :
    t ∈ Set.range (F.encode d) := by
  exact ⟨_, ((F.schnorrSigVerifyBits_eq_true_iff d u msg t z roOut).mp h).symm⟩

/-! ### 2. Typed ROM scheme instantiation and Pointcheval–Stern / Bellare–Neven security bound -/

/-- When `2 ^ m ≤ F.order d`, `m`-bit challenges `BitString m` embed injectively into
`ZMod (F.order d)` via their binary values. -/
def challengeEmbedding (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d) :
    BitString m ↪ ZMod (F.order d) where
  toFun c := (ofBits (List.ofFn c) : ZMod (F.order d))
  inj' c c' h := by
    rw [ZMod.natCast_eq_natCast_iff', ofBits, ofBits, ← BitString.lsbValue_eq_foldr_bit,
      ← BitString.lsbValue_eq_foldr_bit,
      Nat.mod_eq_of_lt ((BitString.lsbValue_lt _).trans_le (by simpa using hm)),
      Nat.mod_eq_of_lt ((BitString.lsbValue_lt _).trans_le (by simpa using hm))] at h
    exact List.ofFn_injective (BitString.lsbValue_injective (by simp) h)

/-- Schnorr's Sigma protocol in `F.Carrier d` with `m`-bit challenges `BitString m` when
`2 ^ m ≤ F.order d`. -/
noncomputable def schnorrBitSigma (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d) :
    SigmaProtocol (ZMod (F.order d)) (F.Carrier d) (F.Carrier d) (BitString m)
      (ZMod (F.order d)) :=
  schnorr (F.challengeEmbedding d hm) (F.generator d)

/-- **Schnorr's Fiat–Shamir ROM signature scheme with `m`-bit challenges** over `F.Carrier d`
([BonehShoup2023], Sections 19.2–19.3; [Schnorr1991]; [PointchevalStern2000]). -/
noncomputable def schnorrFamilyROMScheme {M : Type} (d : F.Desc) {m : ℕ}
    (hm : 2 ^ m ≤ F.order d) :
    ROMSignature.Scheme (F.Carrier d) (ZMod (F.order d) × F.Carrier d) M
      (F.Carrier d × ZMod (F.order d)) (M × F.Carrier d) (BitString m) :=
  fiatShamir (Function.Embedding.refl _) (F.schnorrBitSigma d hm) (schnorrKeyGen (F.generator d))

/-- **Schnorr's Fiat–Shamir ROM signature scheme with full scalar challenges** `ZMod (F.order d)`
over `F.Carrier d`. -/
noncomputable def schnorrScalarROMScheme {M : Type} (d : F.Desc) :
    ROMSignature.Scheme (F.Carrier d) (ZMod (F.order d) × F.Carrier d) M
      (F.Carrier d × ZMod (F.order d)) (M × F.Carrier d) (ZMod (F.order d)) :=
  fiatShamir (Function.Embedding.refl _) (schnorr (Function.Embedding.refl _) (F.generator d))
    (schnorrKeyGen (F.generator d))

/-- **Correctness of `schnorrFamilyROMScheme`**: every honest signature verifies. -/
theorem schnorrFamilyROMScheme_correct {M : Type} [DecidableEq M] (d : F.Desc) {m : ℕ}
    (hm : 2 ^ m ≤ F.order d) :
    (F.schnorrFamilyROMScheme (M := M) d hm).Correct :=
  fiatShamir_correct (Function.Embedding.refl _) schnorr_complete fun _ h =>
    mem_support_schnorrKeyGen h

/-- **Correctness of `schnorrScalarROMScheme`**: every honest signature verifies. -/
theorem schnorrScalarROMScheme_correct {M : Type} [DecidableEq M] (d : F.Desc) :
    (F.schnorrScalarROMScheme (M := M) d).Correct :=
  fiatShamir_correct (Function.Embedding.refl _) schnorr_complete fun _ h =>
    mem_support_schnorrKeyGen h

/-- The Fiat–Shamir / Bellare–Neven forking discrete-logarithm reduction for
`schnorrFamilyROMScheme`, returning zero on a failed fork. -/
noncomputable def schnorrFamilyROMSchemeReduction {M : Type} [DecidableEq M] (d : F.Desc) {m : ℕ}
    (hm : 2 ^ m ≤ F.order d)
    (A : Forger (F.Carrier d) M (F.Carrier d × ZMod (F.order d)) (M × F.Carrier d) (BitString m))
    (Qs Qro : ℕ) : F.Carrier d → PMF (ZMod (F.order d)) :=
  FiatShamir.reduction (Function.Embedding.refl _) (F.schnorrBitSigma d hm)
    (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order d))
      (F.Carrier d) (F.generator d)) id (F.challengeEmbedding d hm))
    (linearExtract (F.challengeEmbedding d hm)) 0 A Qs Qro

/-- The Fiat–Shamir / Bellare–Neven forking discrete-logarithm reduction for
`schnorrScalarROMScheme`, returning zero on a failed fork. -/
noncomputable def schnorrScalarROMSchemeReduction {M : Type} [DecidableEq M] (d : F.Desc)
    (A : Forger (F.Carrier d) M (F.Carrier d × ZMod (F.order d)) (M × F.Carrier d)
      (ZMod (F.order d)))
    (Qs Qro : ℕ) : F.Carrier d → PMF (ZMod (F.order d)) :=
  FiatShamir.reduction (Function.Embedding.refl _) (schnorr (Function.Embedding.refl _)
    (F.generator d))
    (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order d))
      (F.Carrier d) (F.generator d)) id (Function.Embedding.refl _))
    (linearExtract (Function.Embedding.refl _)) 0 A Qs Qro

/-- In `F.Carrier d`, the one-way game for `schnorrKeyGen (F.generator d)` is the exact
discrete-logarithm experiment: draw `α ← PMF.uniformOfFintype (ZMod (F.order d))`, run `B (α • g)`,
and accept when the output equals `α`. -/
theorem oneWayGame_schnorrKeyGen_eq (d : F.Desc) (B : F.Carrier d → PMF (ZMod (F.order d))) :
    oneWayGame (schnorrKeyGen (F.generator d)) (fun α u => α • F.generator d = u) B =
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (B (α • F.generator d)).map fun α' => decide (α' = α) := by
  simp only [oneWayGame, schnorrKeyGen, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_map, Function.comp_def, (F.smul_generator_injective d).eq_iff]
  rfl

/-- **Pointcheval–Stern / Bellare–Neven EUF-CMA security bound for `schnorrFamilyROMScheme`**
([BonehShoup2023], Theorem 19.7 with Equation 19.21; [PointchevalStern2000]; [BellareNeven2006]):
at any group description `d` with `2 ^ m ≤ F.order d`, a forger making at most `Qs` signing queries
and `Qro` random-oracle queries succeeds in `eufCmaGame` with probability at most
`Qs · (Qs + Qro) / F.order d + (Qro + 1) / 2 ^ m + √((Qro + 1) · ε')`, where `ε'` is the
discrete-logarithm success probability of `schnorrFamilyROMSchemeReduction`. -/
theorem succProbability_eufCmaGame_schnorrFamilyROMScheme_le {M : Type} [DecidableEq M]
    (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d)
    (A : Forger (F.Carrier d) M (F.Carrier d × ZMod (F.order d)) (M × F.Carrier d) (BitString m))
    {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro) :
    (Game.succProbability (eufCmaGame (F.schnorrFamilyROMScheme d hm) A) : ℝ) ≤
      Qs * (Qs + Qro) / F.order d + (Qro + 1) / 2 ^ m +
        √((Qro + 1) * Game.succProbability (oneWayGame (schnorrKeyGen (F.generator d))
          (fun α u => α • F.generator d = u)
          (F.schnorrFamilyROMSchemeReduction d hm A Qs Qro))) := by
  have h := schnorr_succProbability_eufCmaGame_le (ι := F.challengeEmbedding d hm)
    (F.generator_ne_zero d) A hA
  simpa only [schnorrFamilyROMScheme, schnorrBitSigma, schnorrFamilyROMSchemeReduction,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

/-- **Pointcheval–Stern / Bellare–Neven EUF-CMA security bound for `schnorrScalarROMScheme`**
([BonehShoup2023], Theorem 19.7 with Equation 19.21): with challenges in `ZMod (F.order d)`, a
forger making at most `Qs` signing queries and `Qro` random-oracle queries succeeds with probability
at most `Qs · (Qs + Qro) / F.order d + (Qro + 1) / F.order d + √((Qro + 1) · ε')`. -/
theorem succProbability_eufCmaGame_schnorrScalarROMScheme_le {M : Type} [DecidableEq M]
    (d : F.Desc)
    (A : Forger (F.Carrier d) M (F.Carrier d × ZMod (F.order d)) (M × F.Carrier d)
      (ZMod (F.order d)))
    {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro) :
    (Game.succProbability (eufCmaGame (F.schnorrScalarROMScheme d) A) : ℝ) ≤
      Qs * (Qs + Qro) / F.order d + (Qro + 1) / F.order d +
        √((Qro + 1) * Game.succProbability (oneWayGame (schnorrKeyGen (F.generator d))
          (fun α u => α • F.generator d = u)
          (F.schnorrScalarROMSchemeReduction d A Qs Qro))) := by
  have h := schnorr_succProbability_eufCmaGame_le (ι := Function.Embedding.refl (ZMod (F.order d)))
    (F.generator_ne_zero d) A hA
  simpa only [schnorrScalarROMScheme, schnorrScalarROMSchemeReduction, ZMod.card] using h

/-- **Asymptotic EUF-CMA negligibility for `schnorrFamilyROMScheme`** across a family of group
descriptions `d : ℕ → F.Desc`: when `Qs` and `Qro` are polynomially bounded, `1 / F.order (d n)`
and `1 / 2 ^ k n` are negligible, and the forking reduction's discrete-logarithm success
probability is negligible, the EUF-CMA forgery probability is negligible. -/
theorem negligible_eufCmaGame_schnorrFamilyROMScheme {M : Type} [DecidableEq M]
    {d : ℕ → F.Desc} {k Qs Qro : ℕ → ℕ}
    (hm : ∀ n, 2 ^ k n ≤ F.order (d n))
    (hQs : PolynomiallyBounded Qs) (hQro : PolynomiallyBounded Qro)
    (horder : Negligible fun n => (1 / F.order (d n) : ℝ≥0))
    (hchallenge : Negligible fun n => (1 / 2 ^ k n : ℝ≥0))
    {A : (n : ℕ) → Forger (F.Carrier (d n)) M (F.Carrier (d n) × ZMod (F.order (d n)))
      (M × F.Carrier (d n)) (BitString (k n))}
    (hA : ∀ n, (A n).CallBounded (Qs n) (Qro n))
    (hDL : Negligible fun n => Game.succProbability
      (oneWayGame (schnorrKeyGen (F.generator (d n)))
        (fun α u => α • F.generator (d n) = u)
        (F.schnorrFamilyROMSchemeReduction (d n) (hm n) (A n) (Qs n) (Qro n)))) :
    Negligible fun n =>
      Game.succProbability (eufCmaGame (F.schnorrFamilyROMScheme (d n) (hm n)) (A n)) := by
  have hpoly₁ : PolynomiallyBounded (fun n => Qs n * (Qs n + Qro n)) := hQs.mul (hQs.add hQro)
  have hpoly₂ : PolynomiallyBounded (fun n => Qro n + 1) := hQro.add (PolynomiallyBounded.const 1)
  have hterm₁ : Negligible fun n => (Qs n * (Qs n + Qro n) : ℕ) * (1 / F.order (d n) : ℝ≥0) :=
    horder.polynomiallyBounded_mul hpoly₁
  have hterm₂ : Negligible fun n => (Qro n + 1 : ℕ) * (1 / 2 ^ k n : ℝ≥0) :=
    hchallenge.polynomiallyBounded_mul hpoly₂
  have hterm₃ : Negligible fun n =>
      NNReal.sqrt ((Qro n + 1 : ℕ) * Game.succProbability
        (oneWayGame (schnorrKeyGen (F.generator (d n)))
          (fun α u => α • F.generator (d n) = u)
          (F.schnorrFamilyROMSchemeReduction (d n) (hm n) (A n) (Qs n) (Qro n)))) :=
    Negligible.sqrt (hDL.polynomiallyBounded_mul hpoly₂)
  refine negligible_of_le ((hterm₁.add hterm₂).add hterm₃) fun n => ?_
  rw [← NNReal.coe_le_coe, Pi.add_apply, Pi.add_apply, NNReal.coe_add, NNReal.coe_add,
    NNReal.coe_mul, NNReal.coe_mul, Real.coe_sqrt, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_natCast,
    NNReal.coe_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_one,
    mul_one_div, mul_one_div]
  exact F.succProbability_eufCmaGame_schnorrFamilyROMScheme_le (d n) (hm n) (A n) (hA n)

end Cslib.Crypto.PrimeOrderGroupFamily
