/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.Int.DotProduct
public import CslibFrontier.Foundations.Data.ZMod.DotProduct
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.NativeExtract
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient
public import CslibFrontier.Crypto.Game.CloseTo.IntBox
public import CslibFrontier.Computability.Probabilistic.IntBox
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.ZMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import Mathlib.Data.List.GetD

/-!
# Efficiency certificates for Lyubashevsky identification

`SigmaProtocol.lyubashevsky` (`CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky.lean`)
defines
Lyubashevsky's lattice identification protocol ([Lyubashevsky2009], [Lyubashevsky2012]) with
Dilithium-style uniform-box rejection sampling ([DucasEtAl2018]) over `PMF`. In the strict
polynomial-time Turing machine model with fair coins, sampling the integer box `[-B, B]^m` of
odd cardinality `(2 B + 1)^m` is approximate rather than exact.

This module connects the strict-PPT integer-box samplers of
`CslibFrontier/Languages/Probabilistic/IntBox.lean` (`sampleIntBoxList`, `sampleIntBoxVec`, with
their certificates in `CslibFrontier/Computability/Probabilistic/IntBox.lean` and statistical
distance bounds in `CslibFrontier/Crypto/Game/CloseTo/IntBox.lean`), together with the serialized
extractor of `CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/NativeExtract.lean`, to
uniform machine-backed efficiency certificates for `SigmaProtocol.lyubashevsky`. Statements,
commitments and challenges use the residue and bit-string encodings `encZModMatrix`, `encZModVec`
and `encBitString`.

1. **Efficient special soundness** (`efficientSpecialSoundness_lyubashevsky`): connects
   `lyubashevskyExtractWord` to `SigmaProtocol.EfficientSpecialSoundness` over the indexed protocol
   family `lyubashevskyFamily`.
2. **Efficient verification** (`VerifierRealizedBy`, `EfficientVerifier`,
   `efficientVerifier_lyubashevsky`): a uniform polynomial-time word verifier
   `lyubashevskyVerifyWord` checks inner-box membership `z ∈ [-(γ - β), γ - β]^m` and the linear
   relation `A z = w + T ĉ` modulo `q`.
3. **Strict-PPT non-abort special HVZK simulator** (`NonAbortSimulator`,
   `EfficientNonAbortSpecialHVZK`, `lyubashevskySimulator`,
   `efficientNonAbortSpecialHVZK_lyubashevsky`): the typed simulator `lyubashevskySimulator`
   samples the integer box with fair bits and is within statistical distance
   `m * ((2 * γ + 1) / 2 ^ width)` of `lyubashevskySimulate`. Its strict-PPT certificate is the
   word program `lyubashevskySimulateWord` (with coin form `lyubashevskySimulateCoins`), which
   computes it on encodings (`eval_lyubashevskySimulateWord`).

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.VerifierRealizedBy`,
  `Cslib.Crypto.Protocols.SigmaProtocol.EfficientVerifier`: polynomial-time verifier certificates
  for indexed Sigma protocol families.
* `Cslib.Crypto.Protocols.SigmaProtocol.NonAbortSimulator`,
  `Cslib.Crypto.Protocols.SigmaProtocol.NonAbortSimulator.IsPPT`,
  `Cslib.Crypto.Protocols.SigmaProtocol.EfficientNonAbortSpecialHVZK`: typed simulators that may
  abort, their uniform strict PPT admissibility, and strict-PPT simulator certificates for Sigma
  protocols with aborts.
* `Cslib.Crypto.Protocols.SigmaProtocol.encCommitResponseOrAbort`: the encoding of the optional
  commitment-response pair output by a program that may abort.
* `Cslib.Crypto.Protocols.SigmaProtocol.LyubashevskyParams`,
  `Cslib.Crypto.Protocols.SigmaProtocol.encLyubashevskyParams`: parameter record and encoding.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyFamily`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyEncoding`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyVerifyWord`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySimulator`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySimulateCoins`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySimulateWord`.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.efficientSpecialSoundness_lyubashevsky`.
* `Cslib.Crypto.Protocols.SigmaProtocol.efficientVerifier_lyubashevsky`.
* `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.closeTo_acceptedTranscript`: a
  simulator realizing a non-abort simulator is close to the honest accepted transcript.
* `Cslib.Crypto.Protocols.SigmaProtocol.computableInPolyTime_lyubashevskySimulateCoins`,
  `Cslib.Crypto.Protocols.SigmaProtocol.isPPTOn_lyubashevskySimulateWord`,
  `Cslib.Crypto.Protocols.SigmaProtocol.eval_lyubashevskySimulateWord`,
  `Cslib.Crypto.Protocols.SigmaProtocol.isPPT_lyubashevskySimulator`,
  `Cslib.Crypto.Protocols.SigmaProtocol.simulatorRealizedBy_lyubashevskySimulator`,
  `Cslib.Crypto.Protocols.SigmaProtocol.efficientNonAbortSpecialHVZK_lyubashevsky`.

## References

* [V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
  Signatures*][Lyubashevsky2009]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Mathlib.Tactic.Matrix

open Probability Probability.PMF Interactive Turing.MultiTapeTM
open scoped ENNReal _root_.Matrix

/-! ### Efficient verifier and non-abort simulator interfaces -/

variable {I : Type} {X Y T C Z : I → Type}

/-- The word function `f` computes the verifier of the protocol family `P` on encodings: from the
index and the encoded statement, commitment, challenge and response, it returns `(P i).verify`. -/
def VerifierRealizedBy (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (enc : Encoding I Y T C Z)
    (f : I × List Bool × List Bool × List Bool × List Bool → Bool) : Prop :=
  ∀ i y t c z,
    f (i, enc.statement i y, enc.commitment i t, enc.challenge i c, enc.response i z) =
      (P i).verify y t c z

/-- **Efficient verification** for an indexed family of Sigma protocols: one deterministic
polynomial-time function of the index and words computes `(P i).verify` on encodings. -/
def EfficientVerifier (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (enc : Encoding I Y T C Z) : Prop :=
  ∃ f, ComputableInPolyTime f
      (encPair enc.index (encPair encBits (encPair encBits (encPair encBits encBits)))) encBool ∧
    VerifierRealizedBy P enc f

/-- Output of a word program that may abort, such as a non-abort simulator or a signing attempt:
`some (t, z)`, a commitment and a response as bit words, or `none` on an abort. `encOption`
encodes `none` as the empty word and `some` by a `true` tag bit before the pair, whose commitment
is framed. -/
abbrev encCommitResponseOrAbort : Option (List Bool × List Bool) ↪ List Bool :=
  encOption (encPair encBits encBits)

variable (I Y T C Z) in
/-- A family of non-abort special HVZK simulators: at index `i`, a probabilistic program from a
statement and a challenge to a commitment and a response, or `none` on an abort.
`NonAbortSimulator.IsPPT` states its efficiency on encodings. -/
abbrev NonAbortSimulator : Type :=
  ∀ i, Y i → C i → ProbComp (Option (T i × Z i))

/-- A family of simulators that may abort is uniform strict PPT: one machine reads
`encSimulatorInput enc` and writes the encoded commitment and response, or the empty word on an
abort (`encCommitResponseOrAbort`). The response encoding is that of the protocol's optional
responses at `some`. -/
def NonAbortSimulator.IsPPT (enc : Encoding I Y T C (fun i => Option (Z i)))
    (sim : NonAbortSimulator I Y T C Z) : Prop :=
  IsPPTOn (encSimulatorInput enc) encCommitResponseOrAbort fun s =>
    Option.map (fun tz => (enc.commitment s.index tz.1, enc.response s.index (some tz.2))) <$>
      sim s.index s.statement s.challenge

/-- **Efficient special HVZK up to aborts**, with statistical error `δ`. At every index `simulate i`
is a perfect `NonAbortSpecialHVZK` simulator for `P i`, and one uniform strict PPT simulator family
realizes the family up to `δ`. -/
structure EfficientNonAbortSpecialHVZK
    (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Option (Z i)))
    (R : ∀ i, X i → Y i → Prop)
    (enc : Encoding I Y T C (fun i => Option (Z i)))
    (simulate : ∀ i, Y i → C i → PMF (Option (T i × Z i))) (δ : I → ℝ≥0∞) : Prop where
  /-- `simulate i` is a perfect non-abort special HVZK simulator at every index. -/
  nonAbortSpecialHVZK : ∀ i, (P i).NonAbortSpecialHVZK (R i) (simulate i)
  /-- One uniform strict PPT simulator family realizes `simulate` up to `δ`. -/
  realized : ∃ sim : NonAbortSimulator I Y T C Z, NonAbortSimulator.IsPPT enc sim ∧
    SimulatorRealizedBy simulate sim δ

/-- A simulator realizing a non-abort simulator is `δ i`-close to the honest prover's
`acceptedTranscript` (published transcripts and aborts) at every challenge. -/
theorem SimulatorRealizedBy.closeTo_acceptedTranscript
    {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Option (Z i))}
    {R : ∀ i, X i → Y i → Prop}
    {simulate : ∀ i, Y i → C i → PMF (Option (T i × Z i))}
    {sim : NonAbortSimulator I Y T C Z} {δ : I → ℝ≥0∞}
    (hS : ∀ i, (P i).NonAbortSpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy simulate sim δ)
    {i : I} {x : X i} {y : Y i} (hxy : R i x y) (c : C i) :
    CloseTo ((P i).acceptedTranscript x y c) (ProbComp.eval (sim i y c)) (δ i) := by
  rw [← (hS i).acceptedTranscript_eq x y hxy c]
  exact h i y c

/-! ### Word encodings for Lyubashevsky's identification family -/

/-- Runtime parameters for an indexed family of Lyubashevsky identification protocols:
unary dimensions `(n, m, k)` and per-coordinate sampling bit width `width`, paired with binary
modulus and box radii `(q, γ, β)`. -/
@[ext]
structure LyubashevskyParams where
  /-- Number of rows `n` in the public matrix `A`. -/
  n : ℕ
  /-- Number of columns `m` in the public matrix `A` (and response dimension). -/
  m : ℕ
  /-- Challenge bit length `k` (and number of columns in `T`). -/
  k : ℕ
  /-- Per-coordinate sampling bit width `width`. -/
  width : ℕ
  /-- Modulus `q`. -/
  q : ℕ
  /-- Outer commitment box radius `γ`. -/
  γ : ℕ
  /-- Rejection margin `β` (inner response box radius is `γ - β`). -/
  β : ℕ
  deriving DecidableEq, Repr

/-- Word encoding of `LyubashevskyParams`: `(n, m, k, width)` in unary and `(q, γ, β)` in
binary. -/
enc_structure encLyubashevskyParams : LyubashevskyParams where
  n : encUnary,
  m : encUnary,
  k : encUnary,
  width : encUnary,
  q : encNat,
  γ : encNat,
  β : encNat

attribute [fun_prop] encLyubashevskyParams_n_polyTime encLyubashevskyParams_m_polyTime
  encLyubashevskyParams_k_polyTime encLyubashevskyParams_width_polyTime
  encLyubashevskyParams_q_polyTime encLyubashevskyParams_γ_polyTime
  encLyubashevskyParams_β_polyTime encLyubashevskyParams_mk_polyTime

/-- Encode an optional integer response `Option (Fin m → ℤ)` via `encOption (encList encIntBin)`. -/
def encIntVecOption (m : ℕ) : Option (Fin m → ℤ) ↪ List Bool :=
  ⟨fun oz => encOption (encList encIntBin) (oz.map List.ofFn),
    (encOption (encList encIntBin)).injective.comp
      (Option.map_injective List.ofFn_injective)⟩

/-- Encode an extracted SIS witness `Fin m ⊕ Fin k → ℤ` as a framed list of `m + k` binary
integers, matching `lyubashevskyExtractWord_eq_extract`. -/
def encExtractedWitness (m k : ℕ) : (Fin m ⊕ Fin k → ℤ) ↪ List Bool :=
  ⟨fun u => encList encIntBin
      (List.ofFn fun j : Fin (m + k) => u (finSumFinEquiv.symm j)), by
    intro u v huv
    have hlist := (encList encIntBin).injective huv
    have hfn := List.ofFn_injective hlist
    funext s
    have hs := congrFun hfn (finSumFinEquiv s)
    simpa only [Equiv.symm_apply_apply] using hs⟩

/-- Lyubashevsky's identification protocol indexed by `p : LyubashevskyParams`. -/
noncomputable def lyubashevskyFamily (p : LyubashevskyParams) :
    SigmaProtocol (Matrix (Fin p.m) (Fin p.k) ℤ)
      (Matrix (Fin p.n) (Fin p.m) (ZMod p.q) ×
        Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
      (Fin p.n → ZMod p.q) (BitString p.k) (Option (Fin p.m → ℤ)) :=
  lyubashevsky p.n p.m p.k p.q p.γ p.β

/-- Word encodings for `lyubashevskyFamily`. -/
def lyubashevskyEncoding :
    Encoding LyubashevskyParams
      (fun p => Matrix (Fin p.n) (Fin p.m) (ZMod p.q) ×
        Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
      (fun p => Fin p.n → ZMod p.q)
      (fun p => BitString p.k)
      (fun p => Option (Fin p.m → ℤ)) where
  index := encLyubashevskyParams
  statement p := encPair (encZModMatrix p.n p.m p.q) (encZModMatrix p.n p.k p.q)
  commitment p := encZModVec p.n p.q
  challenge p := encBitString p.k
  response p := encIntVecOption p.m

/-- Extracted-witness encoding family for `lyubashevskyFamily`. -/
def encLyubashevskyExtracted (p : LyubashevskyParams) :
    (Fin p.m ⊕ Fin p.k → ℤ) ↪ List Bool :=
  encExtractedWitness p.m p.k

/-! ### Part 1a: Efficient special soundness via `NativeExtract` -/

/-- Adapter feeding the `(m, k)` dimensions and encoded challenge/response pairs from an
`ExtractorRealizedBy` input tuple into `lyubashevskyExtractWord`. -/
def lyubashevskyExtractorAdapter
    (inp : LyubashevskyParams × List Bool × List Bool × List Bool × List Bool ×
      List Bool × List Bool) : List Bool :=
  let (p, _, _, c, z, c', z') := inp
  lyubashevskyExtractWord
    (encPair (encPair encUnary encUnary)
      (encPair (encPair encBits encBits) (encPair encBits encBits))
      ((p.m, p.k), ((c, z), (c', z'))))

/-- `lyubashevskyExtractorAdapter` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskyExtractorAdapter :
    ComputableInPolyTime lyubashevskyExtractorAdapter
      (encPair encLyubashevskyParams (encPair encBits (encPair encBits
        (encPair encBits (encPair encBits (encPair encBits encBits)))))) encBits := by
  let encPack := encPair (encPair encUnary encUnary)
    (encPair (encPair encBits encBits) (encPair encBits encBits))
  have hpack : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool × List Bool × List Bool ×
          List Bool × List Bool =>
        let (p, _, _, c, z, c', z') := inp
        encPack ((p.m, p.k), ((c, z), (c', z'))))
      (encPair encLyubashevskyParams (encPair encBits (encPair encBits
        (encPair encBits (encPair encBits (encPair encBits encBits)))))) encBits :=
    (by fun_prop : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool × List Bool × List Bool ×
          List Bool × List Bool =>
        let (p, _, _, c, z, c', z') := inp
        ((p.m, p.k), ((c, z), (c', z'))))
      (encPair encLyubashevskyParams (encPair encBits (encPair encBits
        (encPair encBits (encPair encBits (encPair encBits encBits))))))
      encPack).encoding_comp
  exact computableInPolyTime_lyubashevskyExtractWord.comp hpack

/-- `lyubashevskyExtractorAdapter` realizes the typed extractor `lyubashevskyExtract` across all
parameter records `p : LyubashevskyParams`. -/
theorem extractorRealizedBy_lyubashevskyExtractorAdapter :
    ExtractorRealizedBy lyubashevskyEncoding encLyubashevskyExtracted
      (fun p => lyubashevskyExtract p.n p.m p.k p.q)
      lyubashevskyExtractorAdapter := by
  intro p y t c z c' z'
  have hinput :
      encPair (encPair encUnary encUnary)
        (encPair (encPair encBits encBits) (encPair encBits encBits))
        ((p.m, p.k),
          ((lyubashevskyEncoding.challenge p c, lyubashevskyEncoding.response p z),
            (lyubashevskyEncoding.challenge p c', lyubashevskyEncoding.response p z'))) =
      encLyubashevskyExtractInput
        ⟨⟨p.m, p.k⟩, ⟨List.ofFn c, z.map List.ofFn⟩, ⟨List.ofFn c', z'.map List.ofFn⟩⟩ := rfl
  dsimp only [lyubashevskyExtractorAdapter]
  rw [hinput, lyubashevskyExtractWord_eq_extract p.n p.m p.k p.q y t c z c' z']
  rfl

/-- **Lyubashevsky's identification protocol has efficient special soundness** for the relaxed SIS
relation with norm bound `max (2 * (γ - β)) 1`. -/
theorem efficientSpecialSoundness_lyubashevsky :
    EfficientSpecialSoundness lyubashevskyFamily
      (fun p u y => SIS.IsSolution (Matrix.fromCols y.1 y.2) (max (2 * (p.γ - p.β)) 1) u)
      lyubashevskyEncoding encLyubashevskyExtracted
      (fun p => lyubashevskyExtract p.n p.m p.k p.q) where
  specialSoundness _ := lyubashevsky_specialSoundness
  polyTime := ⟨lyubashevskyExtractorAdapter,
    computableInPolyTime_lyubashevskyExtractorAdapter,
    extractorRealizedBy_lyubashevskyExtractorAdapter⟩

/-! ### Part 1b: Uniform polynomial-time verifier (`EfficientVerifier`) -/

/-- Total polynomial-time decoder for framed lists of signed binary integers. -/
def intListDecoder : Decoder (encList encIntBin) :=
  Decoder.list Decoder.intBin

/-- Total polynomial-time decoder for framed matrices of signed binary integers. -/
def intMatrixDecoder : Decoder (encList (encList encIntBin)) :=
  Decoder.list intListDecoder

/-- Total polynomial-time decoder for optional framed integer lists. -/
def responseListDecoder : Decoder (encOption (encList encIntBin)) :=
  Decoder.option intListDecoder

@[local fun_prop]
private theorem computableInPolyTime_decodeIntList :
    ComputableInPolyTime intListDecoder.decode encBits (encList encIntBin) :=
  intListDecoder.computableInPolyTime

@[local fun_prop]
private theorem computableInPolyTime_decodeIntMatrix :
    ComputableInPolyTime intMatrixDecoder.decode encBits (encList (encList encIntBin)) :=
  intMatrixDecoder.computableInPolyTime

@[local fun_prop]
private theorem computableInPolyTime_decodeResponseList :
    ComputableInPolyTime responseListDecoder.decode encBits (encOption (encList encIntBin)) :=
  responseListDecoder.computableInPolyTime

/-- Reduce an integer `a` to its canonical `ZMod q` representative `ZMod.cast (a : ZMod q)`, for any
`q : ℕ` (including `q = 0`). -/
def zmodReduce (q : ℕ) (a : ℤ) : ℤ :=
  if q == 0 then a else ((a % (q : ℤ)).toNat : ℤ)

@[local fun_prop]
private theorem computableTidilyInPolyTime_zmodReduce :
    ComputableTidilyInPolyTime (fun p : ℕ × ℤ => zmodReduce p.1 p.2)
      (encPair encNat encIntBin) encIntBin := by
  have hmod : ComputableInPolyTime (fun p : ℕ × ℤ => ((p.2 % (p.1 : ℤ)).toNat : ℤ))
      (encPair encNat encIntBin) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.intBin_emodNat' (by fun_prop) (by fun_prop))
  have hmod_tidy := hmod.tidy
  unfold zmodReduce
  fun_prop

/-- `zmodReduce` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_zmodReduce :
    ComputableInPolyTime (fun p : ℕ × ℤ => zmodReduce p.1 p.2)
      (encPair encNat encIntBin) encIntBin :=
  .of_tidy computableTidilyInPolyTime_zmodReduce

/-- `zmodReduce q a` equals `ZMod.cast (a : ZMod q)` for every `q : ℕ` and `a : ℤ`. -/
theorem zmodReduce_eq_cast (q : ℕ) (a : ℤ) :
    zmodReduce q a = ZMod.cast (a : ZMod q) := by
  rw [zmodReduce, ZMod.coe_intCast]
  by_cases hq : q = 0
  · subst q
    simp
  · have hq' : (q == 0) = false := beq_false_of_ne hq
    simp only [hq', Bool.false_eq_true, ↓reduceIte]
    have hnonneg : 0 ≤ a % (q : ℤ) := Int.emod_nonneg a (by omega)
    omega

/-- Convert the first `k` bits of a raw challenge word `c` into a `0`-`1` integer list. -/
def challengeIntList (k : ℕ) (c : List Bool) : List ℤ :=
  (List.range k).map fun j => if c.getD j false then 1 else 0

/-- Check whether the first `m` coordinates of `z` lie in `[-B, B]`. -/
def inBoxList (m B : ℕ) (z : List ℤ) : Bool :=
  (List.range m).all fun j => decide ((z.getD j 0).natAbs ≤ B)

/-- Polynomial-time evaluation on the displayed binary/unary encodings. -/
@[fun_prop]
theorem computableInPolyTime_challengeIntList :
    ComputableInPolyTime (fun p : ℕ × List Bool => challengeIntList p.1 p.2)
      (encPair encUnary encBits) (encList encIntBin) := by
  unfold challengeIntList
  fun_prop

/-- Polynomial-time evaluation on the displayed binary/unary encodings. -/
@[fun_prop]
theorem computableInPolyTime_inBoxList :
    ComputableInPolyTime (fun p : ℕ × ℕ × List ℤ => inBoxList p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encNat (encList encIntBin))) encBool := by
  unfold inBoxList
  fun_prop

/-- Check whether `A z = w + T ĉ` modulo `q` across the first `n` rows. -/
def lyubashevskyVerifyEqList (n m k q : ℕ) (A T : List (List ℤ)) (w z : List ℤ)
    (c : List Bool) : Bool :=
  (List.range n).all fun i =>
    decide (zmodReduce q (ListMatrix.dotProduct m (A.getD i []) z) =
      zmodReduce q (w.getD i 0 + ListMatrix.dotProduct k (T.getD i []) (challengeIntList k c)))

/-- List-level verifier for Lyubashevsky's identification protocol. -/
def lyubashevskyVerifyList (n m k q γ β : ℕ) (A T : List (List ℤ)) (w : List ℤ)
    (c : List Bool) (oz : Option (List ℤ)) : Bool :=
  oz.isSome &&
    inBoxList m (γ - β) (oz.getD []) &&
    lyubashevskyVerifyEqList n m k q A T w (oz.getD []) c

/-- Complete serialized verifier program for `lyubashevskyFamily`. -/
def lyubashevskyVerifyWord
    (inp : LyubashevskyParams × List Bool × List Bool × List Bool × List Bool) : Bool :=
  let (p, yw, ww, cw, zw) := inp
  lyubashevskyVerifyList p.n p.m p.k p.q p.γ p.β
    (intMatrixDecoder.decode (unframe yw))
    (intMatrixDecoder.decode (dropFrame yw))
    (intListDecoder.decode ww)
    cw
    (responseListDecoder.decode zw)

/-- `lyubashevskyVerifyWord` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskyVerifyWord :
    ComputableInPolyTime lyubashevskyVerifyWord
      (encPair encLyubashevskyParams (encPair encBits (encPair encBits (encPair encBits encBits))))
      encBool := by
  unfold lyubashevskyVerifyWord lyubashevskyVerifyList inBoxList lyubashevskyVerifyEqList
  fun_prop

theorem challengeIntList_ofFn {k : ℕ} (c : BitString k) :
    challengeIntList k (List.ofFn c) = List.ofFn (lyubashevskyChallenge c) := by
  rw [challengeIntList, ← List.map_coe_finRange_eq_range, List.map_map]
  conv_rhs => rw [List.ofFn_eq_map]
  refine List.map_congr_left fun j _ => ?_
  simp [lyubashevskyChallenge]

theorem inBoxList_ofFn {m B : ℕ} (z : Fin m → ℤ) :
    inBoxList m B (List.ofFn z) = decide (z ∈ intBox (Fin m) B) := by
  rw [Bool.eq_iff_iff, inBoxList, List.all_eq_true, decide_eq_true_eq, mem_intBox]
  constructor
  · intro h i
    have hi := h i.val (List.mem_range.mpr i.isLt)
    simp only [List.getD_ofFn, decide_eq_true_eq] at hi
    zify at hi
    exact hi
  · intro h j hj
    have hj_lt : j < m := List.mem_range.mp hj
    have hi := h ⟨j, hj_lt⟩
    simp only [List.getD_ofFn_of_lt z hj_lt, decide_eq_true_eq]
    zify
    exact hi

theorem lyubashevskyVerifyEqList_ofFn (n m k q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (T : Matrix (Fin n) (Fin k) (ZMod q))
    (w : Fin n → ZMod q) (z : Fin m → ℤ) (c : BitString k) :
    lyubashevskyVerifyEqList n m k q
      (List.ofFn fun r : Fin n => List.ofFn fun col : Fin m => ZMod.cast (A r col))
      (List.ofFn fun r : Fin n => List.ofFn fun col : Fin k => ZMod.cast (T r col))
      (List.ofFn fun r : Fin n => ZMod.cast (w r))
      (List.ofFn z) (List.ofFn c) =
      decide (A *ᵥ (Int.cast ∘ z) = w + T *ᵥ (Int.cast ∘ lyubashevskyChallenge c)) := by
  rw [Bool.eq_iff_iff, lyubashevskyVerifyEqList, challengeIntList_ofFn,
    List.all_eq_true, decide_eq_true_eq, funext_iff]
  constructor
  · intro h i
    have hi := h i.val (List.mem_range.mpr i.isLt)
    rw [decide_eq_true_eq, zmodReduce_eq_cast, zmodReduce_eq_cast] at hi
    have hcast := Function.LeftInverse.injective ZMod.intCast_zmod_cast hi
    rw [ListMatrix.intCast_dotProduct_matrix_ofFn A z i] at hcast
    rw [Int.cast_add,
      ListMatrix.intCast_dotProduct_matrix_ofFn T (lyubashevskyChallenge c) i] at hcast
    simp only [List.getD_ofFn, ZMod.intCast_zmod_cast] at hcast
    exact hcast
  · intro h j hj
    have hj_lt : j < n := List.mem_range.mp hj
    let i : Fin n := ⟨j, hj_lt⟩
    rw [decide_eq_true_eq, zmodReduce_eq_cast, zmodReduce_eq_cast]
    congr 1
    rw [ListMatrix.intCast_dotProduct_matrix_ofFn A z i, Int.cast_add,
      ListMatrix.intCast_dotProduct_matrix_ofFn T (lyubashevskyChallenge c) i]
    rw [List.getD_ofFn_of_lt _ hj_lt, ZMod.intCast_zmod_cast]
    exact h i

@[simp]
theorem decode_encZModMatrix (n m q : ℕ) (M : Matrix (Fin n) (Fin m) (ZMod q)) :
    intMatrixDecoder.decode (encZModMatrix n m q M) =
      List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => ZMod.cast (M i j) :=
  intMatrixDecoder.decode_enc _

@[simp]
theorem decode_encZModVec (n q : ℕ) (v : Fin n → ZMod q) :
    intListDecoder.decode (encZModVec n q v) =
      List.ofFn fun i : Fin n => ZMod.cast (v i) :=
  intListDecoder.decode_enc _

@[simp]
theorem decode_encIntVecOption (m : ℕ) (oz : Option (Fin m → ℤ)) :
    responseListDecoder.decode (encIntVecOption m oz) = oz.map List.ofFn :=
  responseListDecoder.decode_enc _

/-- `lyubashevskyVerifyWord` agrees with `(lyubashevskyFamily p).verify` on all encoded inputs. -/
theorem verifierRealizedBy_lyubashevskyVerifyWord :
    VerifierRealizedBy lyubashevskyFamily lyubashevskyEncoding lyubashevskyVerifyWord := by
  intro p y w c oz
  dsimp only [lyubashevskyVerifyWord, lyubashevskyEncoding]
  rw [unframe_encPair, dropFrame_encPair, decode_encZModMatrix, decode_encZModMatrix,
    decode_encZModVec, decode_encIntVecOption, encBitString_apply]
  cases oz with
  | none =>
    rfl
  | some z =>
    simp only [Option.map_some, lyubashevskyVerifyList, Option.isSome_some, Option.getD_some,
      Bool.true_and, inBoxList_ofFn, lyubashevskyVerifyEqList_ofFn, lyubashevskyFamily,
      lyubashevsky, Bool.decide_and]

/-- **Lyubashevsky's identification protocol has an efficient polynomial-time verifier.** -/
theorem efficientVerifier_lyubashevsky :
    EfficientVerifier lyubashevskyFamily lyubashevskyEncoding :=
  ⟨lyubashevskyVerifyWord, computableInPolyTime_lyubashevskyVerifyWord,
    verifierRealizedBy_lyubashevskyVerifyWord⟩

/-! ### Part 2: Strict-PPT simulator (`lyubashevskySimulateCoins`, `lyubashevskySimulateWord`) -/

/-- Compute the simulated commitment vector `w = (A z - T ĉ) mod q` as a list of `n` canonical
integer representatives. -/
def lyubashevskySimCommitList (n m k q : ℕ) (A T : List (List ℤ)) (z : List ℤ) (c : List Bool) :
    List ℤ :=
  (List.range n).map fun i =>
    zmodReduce q
      (ListMatrix.dotProduct m (A.getD i []) z -
        ListMatrix.dotProduct k (T.getD i []) (challengeIntList k c))

theorem lyubashevskySimCommitList_ofFn (n m k q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (T : Matrix (Fin n) (Fin k) (ZMod q))
    (z : Fin m → ℤ) (c : BitString k) :
    lyubashevskySimCommitList n m k q
      (List.ofFn fun r : Fin n => List.ofFn fun col : Fin m => ZMod.cast (A r col))
      (List.ofFn fun r : Fin n => List.ofFn fun col : Fin k => ZMod.cast (T r col))
      (List.ofFn z) (List.ofFn c) =
      List.ofFn fun i : Fin n =>
        ZMod.cast ((A *ᵥ (Int.cast ∘ z) - T *ᵥ (Int.cast ∘ lyubashevskyChallenge c)) i) := by
  rw [lyubashevskySimCommitList, challengeIntList_ofFn, ← List.map_coe_finRange_eq_range,
    List.map_map]
  conv_rhs => rw [List.ofFn_eq_map]
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, zmodReduce_eq_cast, Int.cast_sub,
    ListMatrix.intCast_dotProduct_matrix_ofFn A z i,
    ListMatrix.intCast_dotProduct_matrix_ofFn T (lyubashevskyChallenge c) i]
  rfl

/-- Deterministic postprocessing of a candidate response list `z : List ℤ` in Lyubashevsky's
simulator: check `z ∈ [-(γ - β), γ - β]^m` and, if so, return the encoded commitment
`w = A z - T ĉ` and encoded response `some z`. -/
def lyubashevskySimulatePostprocess
    (inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ) :
    Option (List Bool × List Bool) :=
  let ((p, yw, cw), z) := inp
  if inBoxList p.m (p.γ - p.β) z then
    some (
      encList encIntBin
        (lyubashevskySimCommitList p.n p.m p.k p.q
          (intMatrixDecoder.decode (unframe yw))
          (intMatrixDecoder.decode (dropFrame yw))
          z cw),
      encOption (encList encIntBin) (some z))
  else
    none

/-- `lyubashevskySimulatePostprocess` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskySimulatePostprocess :
    ComputableInPolyTime lyubashevskySimulatePostprocess
      (encPair (encSimulatorWordInput encLyubashevskyParams) (encList encIntBin))
      encCommitResponseOrAbort := by
  let encIn := encPair (encPair encLyubashevskyParams (encPair encBits encBits)) (encList encIntBin)
  have hcond : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        let ((p, _, _), z) := inp
        inBoxList p.m (p.γ - p.β) z)
      encIn encBool := by
    unfold inBoxList encIn
    fun_prop
  have hw_list : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        let ((p, yw, cw), z) := inp
        lyubashevskySimCommitList p.n p.m p.k p.q
          (intMatrixDecoder.decode (unframe yw))
          (intMatrixDecoder.decode (dropFrame yw))
          z cw)
      encIn (encList encIntBin) := by
    unfold lyubashevskySimCommitList encIn
    fun_prop
  have hw : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        let ((p, yw, cw), z) := inp
        encList encIntBin
          (lyubashevskySimCommitList p.n p.m p.k p.q
            (intMatrixDecoder.decode (unframe yw))
            (intMatrixDecoder.decode (dropFrame yw))
            z cw))
      encIn encBits :=
    hw_list.encoding_comp
  have hz : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        encOption (encList encIntBin) (some inp.2))
      encIn encBits :=
    ((ComputableInPolyTime.optionSome (encList encIntBin)).comp
      (ComputableInPolyTime.snd _ _)).encoding_comp
  have hsome : ComputableInPolyTime
      (fun inp : (LyubashevskyParams × List Bool × List Bool) × List ℤ =>
        let ((p, yw, cw), z) := inp
        some (
          encList encIntBin
            (lyubashevskySimCommitList p.n p.m p.k p.q
              (intMatrixDecoder.decode (unframe yw))
              (intMatrixDecoder.decode (dropFrame yw))
              z cw),
          encOption (encList encIntBin) (some z)))
      encIn (encOption (encPair encBits encBits)) :=
    (ComputableInPolyTime.optionSome (encPair encBits encBits)).comp (hw.prod hz)
  exact hcond.ite' hsome (ComputableInPolyTime.const none)

/-- Coin-realized deterministic simulator for Lyubashevsky's identification protocol: map
`m * width` fair coin bits to `z ∈ [-γ, γ]^m` via `sampleIntBoxListCoins` and apply
`lyubashevskySimulatePostprocess`. -/
def lyubashevskySimulateCoins
    (inp : (LyubashevskyParams × List Bool × List Bool) × List Bool) :
    Option (List Bool × List Bool) :=
  let ((p, yw, cw), coins) := inp
  lyubashevskySimulatePostprocess
    ((p, yw, cw), sampleIntBoxListCoins p.γ p.m p.width coins)

/-- `lyubashevskySimulateCoins` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskySimulateCoins :
    ComputableInPolyTime lyubashevskySimulateCoins
      (encPair (encSimulatorWordInput encLyubashevskyParams) encBits)
      encCommitResponseOrAbort := by
  unfold lyubashevskySimulateCoins
  fun_prop

/-- Uniform strict-PPT simulator program for `lyubashevskyFamily` on words: the certificate of
`lyubashevskySimulator`, which it computes on encodings (`eval_lyubashevskySimulateWord`). -/
noncomputable def lyubashevskySimulateWord
    (inp : LyubashevskyParams × List Bool × List Bool) :
    ProbComp (Option (List Bool × List Bool)) :=
  let (p, _, _) := inp
  (fun z => lyubashevskySimulatePostprocess (inp, z)) <$>
    sampleIntBoxList p.γ p.m p.width

/-- `lyubashevskySimulateWord` is uniformly strict PPT. -/
theorem isPPTOn_lyubashevskySimulateWord :
    IsPPTOn (encSimulatorWordInput encLyubashevskyParams)
      encCommitResponseOrAbort lyubashevskySimulateWord := by
  let encIn := encPair encLyubashevskyParams (encPair encBits encBits)
  have hγ : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool => inp.1.γ) encIn encNat := by
    unfold encIn
    fun_prop
  have hm : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool => inp.1.m) encIn encUnary := by
    unfold encIn
    fun_prop
  have hwidth : ComputableInPolyTime
      (fun inp : LyubashevskyParams × List Bool × List Bool => inp.1.width) encIn encUnary := by
    unfold encIn
    fun_prop
  exact (isPPTOn_sampleIntBoxList hγ hm hwidth).map_with
    computableInPolyTime_lyubashevskySimulatePostprocess

/-- `lyubashevskySimulateWord` has the same evaluation law as running `lyubashevskySimulateCoins`
on `m * width` uniform fair coin bits. -/
theorem eval_lyubashevskySimulateWord_eq_coins
    (inp : LyubashevskyParams × List Bool × List Bool) :
    ProbComp.eval (lyubashevskySimulateWord inp) =
      (BitString.uniformList (inp.1.m * inp.1.width)).map
        (fun coins => lyubashevskySimulateCoins (inp, coins)) := by
  rw [lyubashevskySimulateWord, ProbComp.eval_map, eval_sampleIntBoxList_eq_coins, PMF.map_comp]
  rfl

/-- On canonical encoded statements and challenges, `lyubashevskySimulatePostprocess` computes the
exact simulator's postprocessing of a candidate vector `z ∈ [-γ, γ]^m`. -/
theorem lyubashevskySimulatePostprocess_ofFn (p : LyubashevskyParams)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) ×
      Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
    (c : BitString p.k) (z : Fin p.m → ℤ) :
    lyubashevskySimulatePostprocess
      ((p, lyubashevskyEncoding.statement p y, lyubashevskyEncoding.challenge p c),
        List.ofFn z) =
      if z ∈ intBox (Fin p.m) (p.γ - p.β) then
        some (lyubashevskyEncoding.commitment p
            (y.1 *ᵥ (Int.cast ∘ z) - y.2 *ᵥ (Int.cast ∘ lyubashevskyChallenge c)),
          lyubashevskyEncoding.response p (some z))
      else
        none := by
  dsimp only [lyubashevskySimulatePostprocess, lyubashevskyEncoding]
  rw [unframe_encPair, dropFrame_encPair, decode_encZModMatrix, decode_encZModMatrix,
    encBitString_apply, inBoxList_ofFn, lyubashevskySimCommitList_ofFn]
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

/-- Lyubashevsky's simulator with fair coins: sample `z` from the fair-bit integer box
`sampleIntBoxVec γ m width`, keep it only inside `[-(γ - β), γ - β]^m`, and solve the verification
equation for the commitment `w = A z - T ĉ`. It approximates `lyubashevskySimulate`, which samples
`[-γ, γ]^m` exactly (`simulatorRealizedBy_lyubashevskySimulator`). -/
noncomputable def lyubashevskySimulator :
    NonAbortSimulator LyubashevskyParams
      (fun p => Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
      (fun p => Fin p.n → ZMod p.q) (fun p => BitString p.k) (fun p => Fin p.m → ℤ) :=
  fun p y c => (fun z => if z ∈ intBox (Fin p.m) (p.γ - p.β) then
      some (y.1 *ᵥ (Int.cast ∘ z) - y.2 *ᵥ (Int.cast ∘ lyubashevskyChallenge c), z)
    else none) <$> sampleIntBoxVec p.γ p.m p.width

/-- On encoded statements and challenges, `lyubashevskySimulateWord` computes the encoded output of
`lyubashevskySimulator`. -/
theorem eval_lyubashevskySimulateWord (p : LyubashevskyParams)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
    (c : BitString p.k) :
    ProbComp.eval (lyubashevskySimulateWord
        (p, lyubashevskyEncoding.statement p y, lyubashevskyEncoding.challenge p c)) =
      (ProbComp.eval (lyubashevskySimulator p y c)).map (Option.map fun tz =>
        (lyubashevskyEncoding.commitment p tz.1, lyubashevskyEncoding.response p (some tz.2))) := by
  rw [lyubashevskySimulateWord, ProbComp.eval_map, eval_sampleIntBoxList_eq_map_ofFn, PMF.map_comp,
    lyubashevskySimulator, ProbComp.eval_map, PMF.map_comp]
  congr 1 with z : 1
  simp only [Function.comp_apply, lyubashevskySimulatePostprocess_ofFn]
  split_ifs <;> rfl

/-- `lyubashevskySimulator` is uniformly strict PPT, certified by `lyubashevskySimulateWord`. -/
theorem isPPT_lyubashevskySimulator :
    NonAbortSimulator.IsPPT lyubashevskyEncoding lyubashevskySimulator :=
  isPPTOn_encSimulatorInput_of_word lyubashevskyEncoding isPPTOn_lyubashevskySimulateWord
    fun s => by rw [eval_lyubashevskySimulateWord, ProbComp.eval_map]

/-- **Simulator realization.** `lyubashevskySimulator` is within statistical distance
`m * ((2 * γ + 1) / 2 ^ width)` of `lyubashevskySimulate`. -/
theorem simulatorRealizedBy_lyubashevskySimulator :
    SimulatorRealizedBy (fun p : LyubashevskyParams => lyubashevskySimulate p.n p.m p.k p.q p.γ p.β)
      lyubashevskySimulator
      (fun p => (p.m : ℝ≥0∞) * ((2 * p.γ + 1 : ℝ≥0∞) / 2 ^ p.width)) := by
  intro p y c
  simp only [lyubashevskySimulate, boxReject, shiftReject, PMF.map_comp, lyubashevskySimulator,
    ProbComp.eval_map]
  convert (closeTo_uniform_intBox_sampleIntBoxVec p.γ p.m p.width).map _ using 2
  congr 1 with z : 1
  simp only [Function.comp_apply, add_zero]
  split_ifs <;> rfl

/-- Witness-statement relation for `lyubashevskyFamily` at norm bound `η p`, bundling the
rejection-sampling parameter conditions `p.β ≤ p.γ` and `p.k * η p ≤ p.β` required for perfect
non-abort HVZK. -/
def lyubashevskyFamilyRelation (η : LyubashevskyParams → ℕ) (p : LyubashevskyParams)
    (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q)) : Prop :=
  p.β ≤ p.γ ∧ p.k * η p ≤ p.β ∧ lyubashevskyRelation (η p) S y

instance (η : LyubashevskyParams → ℕ) (p : LyubashevskyParams)
    (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q)) :
    Decidable (lyubashevskyFamilyRelation η p S y) := by
  unfold lyubashevskyFamilyRelation lyubashevskyRelation
  infer_instance

/-- At every parameter record `p : LyubashevskyParams`, `lyubashevskySimulate` is a perfect
`NonAbortSpecialHVZK` simulator for `lyubashevskyFamilyRelation η p`. -/
theorem lyubashevskyFamily_nonAbortSpecialHVZK (η : LyubashevskyParams → ℕ)
    (p : LyubashevskyParams) :
    (lyubashevskyFamily p).NonAbortSpecialHVZK (lyubashevskyFamilyRelation η p)
      (lyubashevskySimulate p.n p.m p.k p.q p.γ p.β) where
  accepts y c t z h := by
    obtain ⟨oz, hoz, hsome⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    cases oz with
    | none => cases hsome
    | some z' =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      rw [lyubashevskyFamily, lyubashevsky_accepts_some_iff]
      exact ⟨mem_intBox_of_some_mem_support_boxReject hoz, (sub_add_cancel _ _).symm⟩
  acceptedTranscript_eq S y hSy c :=
    (lyubashevsky_nonAbortSpecialHVZK hSy.1 hSy.2.1).acceptedTranscript_eq S y hSy.2.2 c

/-- **Efficient non-abort special HVZK for Lyubashevsky's identification protocol.** For any witness
norm schedule `η : LyubashevskyParams → ℕ`, `lyubashevskySimulator` realizes non-abort special
HVZK for `lyubashevskyFamilyRelation η` with statistical error `m * ((2 * γ + 1) / 2 ^ width)`. -/
theorem efficientNonAbortSpecialHVZK_lyubashevsky (η : LyubashevskyParams → ℕ) :
    EfficientNonAbortSpecialHVZK lyubashevskyFamily
      (lyubashevskyFamilyRelation η)
      lyubashevskyEncoding
      (fun p => lyubashevskySimulate p.n p.m p.k p.q p.γ p.β)
      (fun p => (p.m : ℝ≥0∞) * ((2 * p.γ + 1 : ℝ≥0∞) / 2 ^ p.width)) where
  nonAbortSpecialHVZK := lyubashevskyFamily_nonAbortSpecialHVZK η
  realized := ⟨lyubashevskySimulator, isPPT_lyubashevskySimulator,
    simulatorRealizedBy_lyubashevskySimulator⟩

end Cslib.Crypto.Protocols.SigmaProtocol
