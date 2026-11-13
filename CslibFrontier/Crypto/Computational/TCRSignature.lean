/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.IndexedSignature.Double
public import CslibFrontier.Crypto.Computational.NaorYung
public import CslibFrontier.Crypto.Computational.OneWayToSignature
public import CslibFrontier.Crypto.Computational.TreeSignature.Security
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.PairCapture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Target collision-resistant hash-and-sign and stateless signatures from one-way permutations

When hashing messages before signing under a target collision-resistant hash family (UOWHF), placing
a single hash key in the public verification key fails: an adversary seeing `k` in `pk` before
choosing its signing query and forgery could search for full collisions rather than target
collisions. Instead, construction `(13.2)` of [BonehShoup2023], Section 13.2.1 (p. 533) samples a
**fresh hash key `k` inside every signature** and signs the pair `(k, H(k, m))`:

* **Source mapping**: [BonehShoup2023], Section 13.2.1 states construction `(13.2)` and Theorem 13.2
  for extending the message space of an unrestricted many-time EUF-CMA base signature scheme. Here
  `TCRSignature.scheme S H` instantiates the same per-signature fresh-hash-key construction over a
  **one-time** signature scheme `S` (`OneTimeEUFCMA` on fixed-length bit strings) and an
  unrestricted `KeyedHashFamily` `H`, yielding an `IndexedSignatureScheme` of capacity `1` on
  arbitrary-length `List Bool` messages without storing a hash key in `pk`:
  1. Key generation samples `(otvk, otsk) ← S.keyGen (otsParam H n)` at an injective parameter
     `otsParam H n > H.keyLen n + H.digestLen n` (`TreeSignature.coinParam`) and bundles `n` with
     each key (`encPair encUnary encBits`).
  2. Signing `msg` at index `0` samples `k ← {0, 1}^{H.keyLen n}`, pads `(k, H.eval n k msg)` to an
     `otsParam H n`-bit word `otsMsg H n k (H.eval n k msg)`, signs that word under `S.sign otsk` to
     obtain `ots`, and returns `encPair encBits encBits (k, ots)`.
  3. Verification at index `0` checks `k.length == H.keyLen n` and verifies `ots` on
     `otsMsg H n k (H.eval n k msg)` under `otvk`, rejecting every index `u ≥ 1`.

* **Two-branch security reduction (`exists_reduction_indexedEufCmaGame_le`,
  `SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature`)**: following the case split in the
  proof of [BonehShoup2023], Theorem 13.2, every valid forgery `(0, m₁, (k', ots'))` against
  `TCRSignature.scheme S H` either:
  1. produces a valid one-time signature `ots'` on an `otsParam H n`-bit word
     `M* = otsMsg H n k' (H.eval n k' m₁)` never signed by `S` (either no valid index-`0` signing
     query occurred, or `M* ≠ otsMsg H n k (H.eval n k m₀)`), winning `S.eufOneTimeGame` via
     `oneTimeForger`; or
  2. satisfies `M* = otsMsg H n k (H.eval n k m₀)` for the unique valid index-`0` signing query
     `m₀ ≠ m₁`, which by injectivity of `otsMsg` on `(H.keyLen n, H.digestLen n)`-bit pairs forces
     `k' = k` and `H.eval n k m₀ = H.eval n k m₁`, winning `targetCollisionGame` via the two-stage
     adversary `tcrAdversary` (`simRun` dry-runs the clocked oracle machine on pre-sampled fair
     coins before `k` is chosen to commit `m₀`, then replays on the same coins once `k` arrives).

* **Upgrading to stateless many-time `EUFCMA` (`OneWay.exists_eufCMA_of_targetCollisionResistant`,
  `OneWayPermutation.exists_eufCMA`)**:
  1. Given `OneWay f` and a target collision-resistant `KeyedHashFamily` `H`, Lamport's scheme
     (`OneWay.exists_oneTimeSignature`) supplies a `OneTimeEUFCMA` base scheme `S`,
     `TCRSignature.scheme S H` gives a capacity-`1` `IndexedEUFCMA` scheme on all `List Bool`,
     `IndexedSignatureScheme.double` upgrades capacity from `1` to `2`, and
     `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay` (`TreeSignature.scheme` with
     PRFs from `OneWay f`) yields a stateless many-time `SignatureScheme` satisfying `EUFCMA`.
  2. Combining `OneWayPermutation.oneWay` with Naor–Yung's target collision-resistant
     `KeyedHashFamily` (`OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily`) proves
     that **every one-way permutation implies the existence of a stateless many-time EUF-CMA secure
     digital signature scheme (`OneWayPermutation.exists_eufCMA`)**, with no separate hash-family
     assumption. Many-time extension to unrestricted `List Bool` messages (`WordSignatureScheme`)
     and instantiation from general `OneWay` functions ([Rompel1990]) are proved in
     `CslibFrontier.Crypto.Computational.TCRSignature.ManyTime` and
     `CslibFrontier.Crypto.Computational.Rompel`.

## Main definitions

* `Cslib.Crypto.TCRSignature.otsBudget`, `Cslib.Crypto.TCRSignature.otsParam`,
  `Cslib.Crypto.TCRSignature.otsParamInv`, `Cslib.Crypto.TCRSignature.otsMsg`,
  `Cslib.Crypto.TCRSignature.otsForgeryOf`: injective one-time parameter schedule, fixed-length
  `(k, digest)` message encoding, and fixed-length forgery translator.
* `Cslib.Crypto.TCRSignature.keyDecoder`, `Cslib.Crypto.TCRSignature.sigDecoder`,
  `Cslib.Crypto.TCRSignature.keyGen`, `Cslib.Crypto.TCRSignature.sign`,
  `Cslib.Crypto.TCRSignature.verify`, `Cslib.Crypto.TCRSignature.scheme`: the fresh-key TCR
  hash-and-sign capacity-`1` indexed signature scheme.
* `Cslib.Crypto.TCRSignature.simStep`, `Cslib.Crypto.TCRSignature.simRun`,
  `Cslib.Crypto.TCRSignature.simPkOf`, `Cslib.Crypto.TCRSignature.simWordOf`,
  `Cslib.Crypto.TCRSignature.simFuelOf`: deterministic finite-configuration step, coin-driven run,
  and encoded input/fuel helpers used to commit the first valid signing query before sampling the
  hash key `k` and replay with a reply afterward.
* `Cslib.Crypto.TCRSignature.oneTimeForger`, `Cslib.Crypto.TCRSignature.tcrAdversary`: the one-time
  signature forger and two-stage target-collision adversary.

## Main results

* `Cslib.Crypto.TCRSignature.computableInPolyTime_simRun_comp`: `simRun` is computable in plain
  polynomial time for every finite-control `MultiTapePTM`.
* `Cslib.Crypto.TCRSignature.isOraclePPT_oneTimeForger`,
  `Cslib.Crypto.TCRSignature.isPPT_tcrAdversary`: uniform strict PPT certificates for both
  reductions.
* `Cslib.Crypto.TCRSignature.succProbability_indexedEufCmaGame_le_of_machine`,
  `Cslib.Crypto.TCRSignature.exists_reduction_indexedEufCmaGame_le`: concrete Theorem 13.2 security
  bound splitting indexed forgeries into one-time signature forgeries and target collisions.
* `Cslib.Crypto.SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature`: `TCRSignature.scheme S H`
  is `IndexedEUFCMA`-secure whenever `S` is `OneTimeEUFCMA` and `H` is target collision-resistant.
* `Cslib.Crypto.OneWay.exists_indexedEUFCMA_of_targetCollisionResistant`,
  `Cslib.Crypto.OneWay.exists_eufCMA_of_targetCollisionResistant`: capacity-`2` indexed and
  stateless many-time `EUFCMA` signatures from a one-way function and a target collision-resistant
  `KeyedHashFamily`.
* `Cslib.Crypto.OneWayPermutation.exists_eufCMA`: stateless many-time `EUFCMA` signatures from a
  one-way permutation alone.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 13.2.1 (construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534) and Section 14.6.
* [M. Naor, M. Yung, *Universal One-Way Hash Functions and their Cryptographic
  Applications*][NaorYung1989], Sections 2–4.
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990].
-/

public section

namespace Cslib.Crypto

open Probability _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace TCRSignature

/-! ### Injective one-time parameter schedule and `(k, digest)` message encoding -/

/-- Total bit budget `H.keyLen n + H.digestLen n` signed under the one-time signature scheme at
security parameter `n`. -/
@[expose]
def otsBudget (H : KeyedHashFamily) (n : ℕ) : ℕ :=
  H.keyLen n + H.digestLen n

/-- Injective one-time signature security parameter strictly above `otsBudget H n`. -/
@[expose]
def otsParam (H : KeyedHashFamily) : ℕ → ℕ :=
  TreeSignature.coinParam (otsBudget H)

/-- Polynomial-time bounded-search left inverse of `otsParam H`. -/
@[expose]
def otsParamInv (H : KeyedHashFamily) : ℕ → ℕ :=
  TreeSignature.coinParamInv (otsBudget H)

theorem le_otsParam (H : KeyedHashFamily) (n : ℕ) : n ≤ otsParam H n :=
  TreeSignature.le_coinParam (otsBudget H) n

theorem otsBudget_lt_otsParam (H : KeyedHashFamily) (n : ℕ) :
    otsBudget H n < otsParam H n :=
  TreeSignature.lt_coinParam (otsBudget H) n

@[simp]
theorem otsParamInv_otsParam (H : KeyedHashFamily) (n : ℕ) :
    otsParamInv H (otsParam H n) = n :=
  TreeSignature.coinParamInv_coinParam (otsBudget H) n

theorem computableInPolyTime_otsBudget (H : KeyedHashFamily) :
    ComputableInPolyTime (otsBudget H) encUnary encUnary :=
  H.keyLen_polyTime.unary_add' H.digestLen_polyTime

theorem computableInPolyTime_otsParam (H : KeyedHashFamily) :
    ComputableInPolyTime (otsParam H) encUnary encUnary :=
  TreeSignature.computableInPolyTime_coinParam (computableInPolyTime_otsBudget H)

theorem computableInPolyTime_otsParamInv (H : KeyedHashFamily) :
    ComputableInPolyTime (otsParamInv H) encUnary encUnary :=
  TreeSignature.computableInPolyTime_coinParamInv (computableInPolyTime_otsBudget H)

/-- Encode `(k, d)` as an exact `otsParam H n`-bit word by concatenating the `H.keyLen n`-bit fixed
view of `k`, the `H.digestLen n`-bit fixed view of `d`, and `otsParam H n - otsBudget H n` trailing
`false` bits. -/
@[expose]
def otsMsg (H : KeyedHashFamily) (n : ℕ) (k d : List Bool) : List Bool :=
  BitString.listRow (H.keyLen n) 0 k ++
    BitString.listRow (H.digestLen n) 0 d ++
    List.replicate (otsParam H n - otsBudget H n) false

@[simp]
theorem length_otsMsg (H : KeyedHashFamily) (n : ℕ) (k d : List Bool) :
    (otsMsg H n k d).length = otsParam H n := by
  have hlt := otsBudget_lt_otsParam H n
  simp only [otsBudget] at hlt
  simp only [otsMsg, otsBudget, List.length_append, BitString.length_listRow,
    List.length_replicate]
  omega

theorem otsMsg_inj (H : KeyedHashFamily) {n : ℕ} {k₁ d₁ k₂ d₂ : List Bool}
    (hk₁ : k₁.length = H.keyLen n) (hd₁ : d₁.length = H.digestLen n)
    (hk₂ : k₂.length = H.keyLen n) (hd₂ : d₂.length = H.digestLen n)
    (heq : otsMsg H n k₁ d₁ = otsMsg H n k₂ d₂) :
    k₁ = k₂ ∧ d₁ = d₂ := by
  have hrow {w : ℕ} {l : List Bool} (h : l.length = w) : BitString.listRow w 0 l = l := by
    simp only [BitString.listRow, Nat.zero_mul, List.drop_zero, List.take_left' h]
  simp only [otsMsg, hrow hk₁, hrow hd₁, hrow hk₂, hrow hd₂] at heq
  have hprefix : k₁ ++ d₁ = k₂ ++ d₂ :=
    (List.append_inj heq (by simp only [List.length_append, hk₁, hd₁, hk₂, hd₂])).1
  exact List.append_inj hprefix (hk₁.trans hk₂.symm)

theorem computableInPolyTime_otsMsg_comp (H : KeyedHashFamily) {α : Type}
    {input : α ↪ List Bool} {n : α → ℕ} {k d : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hk : ComputableInPolyTime k input encBits)
    (hd : ComputableInPolyTime d input encBits) :
    ComputableInPolyTime (fun a => otsMsg H (n a) (k a) (d a)) input encBits := by
  have hrowK := ComputableInPolyTime.bitsRowWithInput
    (H.keyLen_polyTime.comp hn) (.const 0) hk
  have hrowD := ComputableInPolyTime.bitsRowWithInput
    (H.digestLen_polyTime.comp hn) (.const 0) hd
  have hpadLen := ComputableInPolyTime.unary_sub.comp
    (((computableInPolyTime_otsParam H).comp hn).prod
      ((computableInPolyTime_otsBudget H).comp hn))
  have hpad := (ComputableInPolyTime.bitsReplicate false).comp hpadLen
  exact (ComputableInPolyTime.bitsAppend hrowK hrowD).bitsAppend hpad

/-- Compose `otsMsg H` with `H.eval` in polynomial time. -/
theorem computableInPolyTime_otsMsg_eval_comp (H : KeyedHashFamily) {α : Type}
    {input : α ↪ List Bool} {n : α → ℕ} {k msg : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hk : ComputableInPolyTime k input encBits)
    (hmsg : ComputableInPolyTime msg input encBits) :
    ComputableInPolyTime
      (fun a => otsMsg H (n a) (k a) (H.eval (n a) (k a) (msg a))) input encBits :=
  computableInPolyTime_otsMsg_comp H hn hk ((hn.prod (hk.prod hmsg)).trans H.polyTime)

/-! ### The capacity-`1` fresh-key TCR hash-and-sign scheme -/

/-- Total decoder for `(n, key)` words encoded with `encPair encUnary encBits`. -/
@[expose]
def keyDecoder : Decoder (encPair encUnary encBits) :=
  Decoder.unary.pair Decoder.bits

/-- Total decoder for `(k, ots)` signature words encoded with `encPair encBits encBits`. -/
@[expose]
def sigDecoder : Decoder (encPair encBits encBits) :=
  Decoder.bits.pair Decoder.bits

/-- Translate a `(msg, sig)` word pair at parameter `n` into the underlying fixed-length
`(otsMsg H n k (H.eval n k msg), ots)` forgery candidate for `S`. -/
@[expose]
def otsForgeryOf (H : KeyedHashFamily) (n : ℕ) (msg sig : List Bool) :
    List Bool × List Bool :=
  let parsedSig := sigDecoder.decode sig
  (otsMsg H n parsedSig.1 (H.eval n parsedSig.1 msg), parsedSig.2)

theorem computableInPolyTime_otsForgeryOf_comp (H : KeyedHashFamily) {α : Type}
    {input : α ↪ List Bool} {n : α → ℕ} {msg sig : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hmsg : ComputableInPolyTime msg input encBits)
    (hsig : ComputableInPolyTime sig input encBits) :
    ComputableInPolyTime
      (fun a => otsForgeryOf H (n a) (msg a) (sig a))
      input (encPair encBits encBits) := by
  have hparsed := hsig.trans sigDecoder.computableInPolyTime
  exact ((computableInPolyTime_otsMsg_eval_comp H hn hparsed.fst' hmsg).prod
    hparsed.snd').of_enc_eq fun _ => rfl

/-- Sample a one-time key pair `(otvk, otsk) ← S.keyGen (otsParam H n)` and bundle `n` with each
half via `encPair encUnary encBits`. -/
@[expose]
def keyGen (S : SignatureScheme) (H : KeyedHashFamily) (n : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let keys ← S.keyGen (otsParam H n)
  return (encPair encUnary encBits (n, keys.1), encPair encUnary encBits (n, keys.2))

/-- Sign `msg` at index `0` by sampling a fresh `H.keyLen n`-bit key `k`, signing
`otsMsg H n k (H.eval n k msg)` under `S.sign`, and returning `encPair encBits encBits (k, ots)`.
Returns `[]` for every index `u ≥ 1`. -/
@[expose]
noncomputable def sign (S : SignatureScheme) (H : KeyedHashFamily) (sk : List Bool) (u : ℕ)
    (msg : List Bool) : ProbComp (List Bool) :=
  let parsed := keyDecoder.decode sk
  if u = 0 then do
    let k ← BitString.sampleList (H.keyLen parsed.1)
    let ots ← S.sign parsed.2 (otsMsg H parsed.1 k (H.eval parsed.1 k msg))
    return encPair encBits encBits (k, ots)
  else
    pure []

/-- Verify `sig` on `msg` at index `u` under `pk`: require `u == 0`, `k.length == H.keyLen n`, and
`S.verify otvk (otsMsg H n k (H.eval n k msg)) ots`. -/
@[expose]
def verify (S : SignatureScheme) (H : KeyedHashFamily) (pk : List Bool) (u : ℕ)
    (msg sig : List Bool) : Bool :=
  let parsedPk := keyDecoder.decode pk
  let parsedSig := sigDecoder.decode sig
  (u == 0) && (parsedSig.1.length == H.keyLen parsedPk.1) &&
    S.verify parsedPk.2
      (otsMsg H parsedPk.1 parsedSig.1 (H.eval parsedPk.1 parsedSig.1 msg))
      parsedSig.2

theorem keyGen_ppt (S : SignatureScheme) (H : KeyedHashFamily) :
    IsPPTOn encUnary (encPair encBits encBits) (keyGen S H) := by
  have hkg : IsPPTOn encUnary (encPair encBits encBits)
      (fun n => S.keyGen (otsParam H n)) :=
    S.isPPTOn_keyGen_comp (computableInPolyTime_otsParam H)
  have hpost : ComputableInPolyTime
      (fun p : ℕ × (List Bool × List Bool) =>
        (encPair encUnary encBits (p.1, p.2.1), encPair encUnary encBits (p.1, p.2.2)))
      (encPair encUnary (encPair encBits encBits))
      (encPair encBits encBits) := by
    have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
    have hpk := (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).fst'
    have hsk := (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd'
    have henc : ComputableInPolyTime (encPair encUnary encBits)
        (encPair encUnary encBits) encBits := .of_eq fun _ => rfl
    exact (((hn.prod hpk).trans henc).prod ((hn.prod hsk).trans henc)).of_enc_eq fun _ => rfl
  exact hkg.map_pair hpost

theorem sign_ppt (S : SignatureScheme) (H : KeyedHashFamily) :
    IsPPTOn encIndexedSignInput encBits
      (fun p => sign S H p.1 p.2.1 p.2.2) := by
  let In := List Bool × ℕ × List Bool
  let encIn : In ↪ List Bool := encPair encBits (encPair encUnary encBits)
  have hsk : ComputableInPolyTime (fun p : In => p.1) encIn encBits :=
    ComputableInPolyTime.fst _ _
  have hu : ComputableInPolyTime (fun p : In => p.2.1) encIn encUnary :=
    (ComputableInPolyTime.snd _ _).fst'
  have hmsg : ComputableInPolyTime (fun p : In => p.2.2) encIn encBits :=
    (ComputableInPolyTime.snd _ _).snd'
  have hparsed : ComputableInPolyTime (fun p : In => keyDecoder.decode p.1)
      encIn (encPair encUnary encBits) :=
    (hsk.trans keyDecoder.computableInPolyTime).of_enc_eq fun _ => rfl
  have hn : ComputableInPolyTime (fun p : In => (keyDecoder.decode p.1).1) encIn encUnary :=
    hparsed.fst'
  have hotsk : ComputableInPolyTime (fun p : In => (keyDecoder.decode p.1).2) encIn encBits :=
    hparsed.snd'
  have huZero : ComputableInPolyTime (fun p : In => decide (p.2.1 = 0)) encIn encBool :=
    ComputableInPolyTime.unary_eq' hu (.const 0)
  have hsampleK : IsPPTOn encIn encBits
      (fun p : In => BitString.sampleList (H.keyLen (keyDecoder.decode p.1).1)) :=
    (hn.trans H.keyLen_polyTime).sampleList
  have hsignStep : IsPPTOn (encPair encIn encBits) encBits
      (fun q : In × List Bool => do
        let parsed := keyDecoder.decode q.1.1
        let ots ← S.sign parsed.2 (otsMsg H parsed.1 q.2 (H.eval parsed.1 q.2 q.1.2.2))
        return encPair encBits encBits (q.2, ots)) := by
    have hqIn := ComputableInPolyTime.fst encIn encBits
    have hqK := ComputableInPolyTime.snd encIn encBits
    have hqN := hqIn.trans hn
    have hqSk := hqIn.trans hotsk
    have hqMsg := hqIn.trans hmsg
    have hM := computableInPolyTime_otsMsg_eval_comp H hqN hqK hqMsg
    have hots := S.isPPTOn_sign_comp hqSk hM
    have henc : ComputableInPolyTime (encPair encBits encBits)
        (encPair encBits encBits) encBits := .of_eq fun _ => rfl
    have hencSig : ComputableInPolyTime
        (fun r : (In × List Bool) × List Bool => encPair encBits encBits (r.1.2, r.2))
        (encPair (encPair encIn encBits) encBits) encBits :=
      ((((ComputableInPolyTime.fst (encPair encIn encBits) encBits).trans hqK).prod
        (ComputableInPolyTime.snd (encPair encIn encBits) encBits)).trans henc).of_enc_eq
          fun _ => rfl
    exact hots.map_pair hencSig
  exact IsPPTOn.ite' huZero (hsampleK.bind_pair hsignStep)
    (ComputableInPolyTime.const (encIn := encIn) (encOut := encBits) []).isPPTOn

theorem verify_polyTime (S : SignatureScheme) (H : KeyedHashFamily) :
    ComputableInPolyTime
      (fun p : List Bool × ℕ × List Bool × List Bool => verify S H p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encBits encIndexedSignedMessage) encBool := by
  let In := List Bool × ℕ × List Bool × List Bool
  let encIn : In ↪ List Bool := encPair encBits (encPair encUnary (encPair encBits encBits))
  have hpk : ComputableInPolyTime (fun p : In => p.1) encIn encBits :=
    ComputableInPolyTime.fst _ _
  have hu : ComputableInPolyTime (fun p : In => p.2.1) encIn encUnary :=
    (ComputableInPolyTime.snd _ _).fst'
  have hmsg : ComputableInPolyTime (fun p : In => p.2.2.1) encIn encBits :=
    (ComputableInPolyTime.snd _ _).snd'.fst'
  have hsig : ComputableInPolyTime (fun p : In => p.2.2.2) encIn encBits :=
    (ComputableInPolyTime.snd _ _).snd'.snd'
  have hparsedPk := hpk.trans keyDecoder.computableInPolyTime
  have hparsedSig := hsig.trans sigDecoder.computableInPolyTime
  have hn := hparsedPk.fst'
  have hotvk := hparsedPk.snd'
  have hk := hparsedSig.fst'
  have hots := hparsedSig.snd'
  have huEq := ComputableInPolyTime.unary_beq' hu (.const 0)
  have hkLenEq := ComputableInPolyTime.unary_beq'
    (hk.trans ComputableInPolyTime.length_bits) (hn.trans H.keyLen_polyTime)
  have hM := computableInPolyTime_otsMsg_eval_comp H hn hk hmsg
  have hv := S.computableInPolyTime_verify_comp hotvk hM hots
  exact ((huEq.bool_and' hkLenEq).bool_and' hv).of_enc_eq fun _ => rfl

theorem verify_sign (S : SignatureScheme) (H : KeyedHashFamily)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (keyGen S H n)).support)
    (u : ℕ) (hu : u < 1) (msg sig : List Bool)
    (hsig : sig ∈ (ProbComp.eval (sign S H keys.2 u msg)).support) :
    verify S H keys.1 u msg sig = true := by
  obtain rfl : u = 0 := by omega
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hkeys
  obtain ⟨otKeys, hotKeys, rfl⟩ := hkeys
  simp only [sign, keyDecoder.decode_enc, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsig
  obtain ⟨k, hk, ots, hots, rfl⟩ := hsig
  have hkLen : k.length = H.keyLen n := BitString.length_of_mem_support_uniformList hk
  have hv := S.verify_sign (otsParam H n) otKeys hotKeys
    (otsMsg H n k (H.eval n k msg)) (length_otsMsg H n k _) ots hots
  simp only [verify, keyDecoder.decode_enc, sigDecoder.decode_enc, beq_self_eq_true, hkLen, hv,
    Bool.and_self]

/-- **Fresh-key TCR hash-and-sign capacity-`1` indexed signature scheme** ([BonehShoup2023],
Section 13.2.1, construction `(13.2)` instantiated over a one-time signature scheme `S` and an
unrestricted `KeyedHashFamily` `H`): signs arbitrary-length `List Bool` messages at index `0` by
sampling a fresh hash key `k` per signature and signing `(k, H.eval n k msg)` under `S` at
`otsParam H n`. -/
@[expose]
noncomputable def scheme (S : SignatureScheme) (H : KeyedHashFamily) : IndexedSignatureScheme where
  capacity _ := 1
  keyGen := keyGen S H
  sign := sign S H
  verify := verify S H
  capacity_polyTime := ComputableInPolyTime.const 1
  keyGen_ppt := keyGen_ppt S H
  sign_ppt := sign_ppt S H
  verify_polyTime := verify_polyTime S H
  verify_sign := verify_sign S H

/-- `scheme S H` has capacity `1` at every security parameter. -/
@[simp] theorem scheme_capacity (S : SignatureScheme) (H : KeyedHashFamily) :
    (scheme S H).capacity = fun _ => 1 := rfl

/-- Key generation of `scheme S H` is `keyGen S H`. -/
@[simp] theorem scheme_keyGen (S : SignatureScheme) (H : KeyedHashFamily) :
    (scheme S H).keyGen = keyGen S H := rfl

/-- Signing of `scheme S H` is `sign S H`. -/
@[simp] theorem scheme_sign (S : SignatureScheme) (H : KeyedHashFamily) :
    (scheme S H).sign = sign S H := rfl

/-- Verification of `scheme S H` is `verify S H`. -/
@[simp] theorem scheme_verify (S : SignatureScheme) (H : KeyedHashFamily) :
    (scheme S H).verify = verify S H := rfl

/-! ### Deterministic coin-driven simulator for capacity-`1` indexed runs -/

section Simulator

theorem computableInPolyTime_finiteConfig_reqWord {k : ℕ} {Control α : Type} [Finite Control]
    {encIn : α ↪ List Bool} {cfg : α → FiniteConfig k Bool Control Unit}
    (hcfg : ComputableInPolyTime cfg encIn encFiniteConfig) :
    ComputableInPolyTime (fun a => ((cfg a).channels ()).1) encIn encBits :=
  ((ComputableInPolyTime.pi_apply (encPair encBits (encBiTape encBool)) ()).comp
    (ComputableInPolyTime.finiteConfig_channels.comp hcfg)).fst'

/-- Finite-tag transition dispatch on `FiniteConfig`: given polynomial-time projections for a
`FiniteConfig` `cfg` and a coin `coin`, plus polynomial-time handlers for the halted branch, each
`(action, symbol, move)` step branch, and each `next` query branch, the full transition is
computable in polynomial time. -/
theorem computableInPolyTime_finiteConfig_cases {k : ℕ} {Control α β : Type} [Finite Control]
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Unit)
    {cfg : α → FiniteConfig k Bool Control Unit}
    {coin : α → Bool}
    (hcfg : ComputableInPolyTime cfg encIn encFiniteConfig)
    (hcoin : ComputableInPolyTime coin encIn encBool)
    {onHalt : α → β}
    (hHalt : ComputableInPolyTime onHalt encIn encOut)
    {onStep : Action k Bool Control → (Unit → Option Bool) → (Unit → SignType) → α → β}
    (hStep : ∀ action symbol move,
      ComputableInPolyTime (onStep action symbol move) encIn encOut)
    {onQuery : Control → α → β}
    (hQuery : ∀ next, ComputableInPolyTime (onQuery next) encIn encOut) :
    ComputableInPolyTime
      (fun a =>
        match (cfg a).tapes.state with
        | none => onHalt a
        | some state =>
          match machine.tr state (cfg a).tapes.inputSymbol (cfg a).tapes.workTapeSymbols
              (cfg a).answerSymbols (coin a) with
          | .step action symbol move => onStep action symbol move a
          | .query () next => onQuery next a)
      encIn encOut := by
  have htapes := ComputableInPolyTime.finiteConfig_tapes.comp hcfg
  let Tag := Option Control × Option Bool × (Fin k → Option Bool) × (Unit → Option Bool) × Bool
  let encTag : Tag ↪ List Bool :=
    encPair (encFinite (Option Control))
      (encPair (encFinEnum (Option Bool))
        (encPair (encFinEnum (Fin k → Option Bool))
          (encPair (encFinite (Unit → Option Bool)) encBool)))
  have htag : ComputableInPolyTime
      (fun a : α =>
        ((cfg a).tapes.state, (cfg a).tapes.inputSymbol, (cfg a).tapes.workTapeSymbols,
          (cfg a).answerSymbols, coin a))
      encIn encTag :=
    (ComputableInPolyTime.finiteCfg_state.comp htapes).prod
      ((ComputableInPolyTime.finiteCfg_inputSymbol.comp htapes).prod
        ((ComputableInPolyTime.finiteCfg_workTapeSymbols.comp htapes).prod
          ((ComputableInPolyTime.finiteConfig_answerSymbols.comp hcfg).prod hcoin)))
  let branch (choice : Tag) (a : α) : β :=
    match choice.1 with
    | none => onHalt a
    | some state =>
      match machine.tr state choice.2.1 choice.2.2.1 choice.2.2.2.1 choice.2.2.2.2 with
      | .step action symbol move => onStep action symbol move a
      | .query () next => onQuery next a
  have hbranch : ∀ choice : Tag, ComputableInPolyTime (branch choice) encIn encOut := by
    rintro ⟨stOpt, inSym, workSyms, ansSyms, coinVal⟩
    cases stOpt with
    | none => exact hHalt
    | some state =>
      dsimp only [branch]
      cases machine.tr state inSym workSyms ansSyms coinVal with
      | step action symbol move => exact hStep action symbol move
      | query ch next =>
        cases ch
        exact hQuery next
  exact (htag.finite_cases hbranch).of_enc_eq fun _ => rfl

/-- One deterministic transition of `machine` on finite storage `(cfg, qOpt)` using fair coin `coin`
and pre-supplied `reply` for the **first** query at index `0` (`r.1 == 0 && qOpt.isNone`). Every
other query (`r.1 ≠ 0` or after `qOpt = some m₀`) receives the empty reply `[]`, matching
`indexedSigningOracle` at capacity `1`. -/
def simStep {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (reply : List Bool) (acc : FiniteConfig k Bool Control Unit × Option (List Bool))
    (coin : Bool) : FiniteConfig k Bool Control Unit × Option (List Bool) :=
  match acc.1.tapes.state with
  | none => acc
  | some state =>
    match machine.tr state acc.1.tapes.inputSymbol acc.1.tapes.workTapeSymbols
        acc.1.answerSymbols coin with
    | .step action symbol move => (acc.1.step action symbol move, acc.2)
    | .query () next =>
      let r := IndexedSignatureScheme.requestDecoder.decode (acc.1.channels ()).1
      if r.1 == 0 && acc.2.isNone then
        (acc.1.receive () next reply, some r.2)
      else
        (acc.1.receive () next [], acc.2)

/-- Run `machine` deterministically on `word` over `coins` using `reply` for the first valid
index-`0` signing query, returning `(finalOutput, recordedQuery)`. -/
def simRun {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (word reply coins : List Bool) : List Bool × Option (List Bool) :=
  let final := coins.foldl (simStep machine reply) (FiniteConfig.init machine.initial word, none)
  (final.1.tapes.output, final.2)

private theorem computableInPolyTime_simStep {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Unit) :
    ComputableInPolyTime
      (fun q : (List Bool × (FiniteConfig k Bool Control Unit × Option (List Bool))) × Bool =>
        simStep machine q.1.1 q.1.2 q.2)
      (encPair
        (encPair encBits (encPair encFiniteConfig (encOption encBits)))
        encBool)
      (encPair encFiniteConfig (encOption encBits)) := by
  let Acc := FiniteConfig k Bool Control Unit × Option (List Bool)
  let encAcc : Acc ↪ List Bool := encPair encFiniteConfig (encOption encBits)
  let Q := (List Bool × Acc) × Bool
  let encQ : Q ↪ List Bool := encPair (encPair encBits encAcc) encBool
  have hreply : ComputableInPolyTime (fun q : Q => q.1.1) encQ encBits :=
    (ComputableInPolyTime.fst _ _).fst'
  have hacc : ComputableInPolyTime (fun q : Q => q.1.2) encQ encAcc :=
    (ComputableInPolyTime.fst _ _).snd'
  have hcfg : ComputableInPolyTime (fun q : Q => q.1.2.1) encQ encFiniteConfig :=
    hacc.fst'
  have hqOpt : ComputableInPolyTime (fun q : Q => q.1.2.2) encQ (encOption encBits) :=
    hacc.snd'
  have hcoin : ComputableInPolyTime (fun q : Q => q.2) encQ encBool :=
    ComputableInPolyTime.snd _ _
  have hr := IndexedSignatureScheme.requestDecoder.computableInPolyTime.comp
    (computableInPolyTime_finiteConfig_reqWord hcfg)
  have hrZero := ComputableInPolyTime.unary_beq' hr.fst' (.const 0)
  have hisNone : ComputableInPolyTime (fun q : Q => q.1.2.2.isNone) encQ encBool :=
    (hqOpt.optionIsSome.trans ComputableInPolyTime.bool_not).of_enc_eq fun q => by
      cases q.1.2.2 <;> rfl
  have hcond := hrZero.bool_and' hisNone
  exact (computableInPolyTime_finiteConfig_cases machine hcfg hcoin hacc
    (fun action symbol move =>
      ((ComputableInPolyTime.finiteConfig_step action symbol move).comp hcfg).prod hqOpt)
    (fun next =>
      hcond.ite
        ((ComputableInPolyTime.finiteConfig_receive hcfg hreply () next).prod
          ((ComputableInPolyTime.optionSome encBits).comp hr.snd'))
        ((ComputableInPolyTime.finiteConfig_receive hcfg (.const []) () next).prod
          hqOpt))).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_simRun_raw {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Unit) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool => simRun machine p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits))
      (encPair encBits (encOption encBits)) := by
  let P := List Bool × List Bool × List Bool
  let encP : P ↪ List Bool := encPair encBits (encPair encBits encBits)
  let Acc := FiniteConfig k Bool Control Unit × Option (List Bool)
  let encAcc : Acc ↪ List Bool := encPair encFiniteConfig (encOption encBits)
  have hword : ComputableInPolyTime (fun p : P => p.1) encP encBits :=
    ComputableInPolyTime.fst _ _
  have hreply : ComputableInPolyTime (fun p : P => p.2.1) encP encBits :=
    (ComputableInPolyTime.snd _ _).fst'
  have hcoins : ComputableInPolyTime (fun p : P => p.2.2) encP encBits :=
    (ComputableInPolyTime.snd _ _).snd'
  have hinit : ComputableInPolyTime
      (fun p : P => (FiniteConfig.init machine.initial p.1, (none : Option (List Bool))))
      encP encAcc :=
    (ComputableInPolyTime.finiteConfig_init hword machine.initial).prod (.const none)
  obtain ⟨cCfg, hcCfg⟩ :=
    length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  let inv (p : P) (consumed : List Bool) (acc : Acc) : Prop :=
    FiniteConfig.SpaceBound p.1.length consumed.length p.2.1.length acc.1 ∧
      ∀ m₀, acc.2 = some m₀ → m₀.length ≤ consumed.length
  let size (p : P) : ℕ :=
    (2 * cCfg + 2) * (p.1.length + p.2.2.length + p.2.1.length + 1) + 2
  have hsize : PolyBounded (fun p : P => (encP p).length) size := by
    apply PolyBounded.of_forall_le (2 * cCfg + 4) 1
    rintro ⟨w, r, cs⟩
    dsimp only [P, encP, size]
    rw [length_encPair, length_encPair]
    simp only [encBits_apply, pow_one]
    calc (2 * cCfg + 2) * (w.length + cs.length + r.length + 1) + 2
        ≤ (2 * cCfg + 2) * (w.length + cs.length + r.length + 1) +
            2 * (w.length + cs.length + r.length + 1) := by omega
      _ = (2 * cCfg + 4) * (w.length + cs.length + r.length + 1) := by ring
      _ ≤ (2 * cCfg + 4) * (2 * w.length + 1 + (2 * r.length + 1 + cs.length) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
  have hfold := (ComputableInPolyTime.foldlWith_spec
    (encA := encBool) (encL := encBits) (encB := encAcc)
    (par := fun p : P => p.2.1) (list := fun p : P => p.2.2)
    (init := fun p : P => (FiniteConfig.init machine.initial p.1, none))
    (step := simStep machine)
    hreply hcoins hinit (computableInPolyTime_simStep machine)
    inv
    (fun p => ⟨FiniteConfig.spaceBound_init machine.initial p.1 p.2.1.length,
      by rintro _ ⟨⟩⟩)
    (fun p consumed acc coin _ hinv => by
      rcases acc with ⟨cfg, qOpt⟩
      dsimp only [inv, simStep] at hinv ⊢
      simp only [List.length_append, List.length_singleton]
      cases cfg.tapes.state with
      | none =>
        dsimp only
        exact ⟨hinv.1.mono le_rfl (Nat.le_succ _) le_rfl,
          fun m₀ hm => (hinv.2 m₀ hm).trans (Nat.le_succ _)⟩
      | some state =>
        dsimp only
        cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols coin with
        | step action symbol move =>
          dsimp only
          exact ⟨hinv.1.step action symbol move,
            fun m₀ hm => (hinv.2 m₀ hm).trans (Nat.le_succ _)⟩
        | query ch next =>
          cases ch
          dsimp only
          split_ifs with hfirst
          · dsimp only
            refine ⟨hinv.1.receive () next p.2.1 le_rfl, ?_⟩
            intro m₀ hm
            injection hm with hmEq
            subst hmEq
            have hdrop :
                (IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1).2.length ≤
                  ((cfg.channels ()).1).length := by
              simpa only [IndexedSignatureScheme.requestDecoder, Decoder.pair, Decoder.bits,
                id_eq] using length_dropFrame_le (cfg.channels ()).1
            exact (hdrop.trans (hinv.1.query ())).trans (Nat.le_succ _)
          · dsimp only
            exact ⟨hinv.1.receive () next [] (Nat.zero_le _),
              fun m₀ hm => (hinv.2 m₀ hm).trans (Nat.le_succ _)⟩)
    hsize
    (fun p consumed acc hpre hinv => by
      rcases p with ⟨w, r, cs⟩
      rcases acc with ⟨cfg, qOpt⟩
      have hlenPre : consumed.length ≤ cs.length := hpre.length_le
      have hcfgLen : (encFiniteConfig cfg).length ≤
          cCfg * (w.length + cs.length + r.length + 1) :=
        (hcCfg w.length consumed.length r.length cfg hinv.1).trans
          (Nat.mul_le_mul_left cCfg (by omega))
      have hoptLen : (encOption encBits qOpt).length ≤ cs.length + 1 := by
        cases hq : qOpt with
        | none => simp
        | some m₀ =>
          have hm := (hinv.2 m₀ hq).trans hlenPre
          simp only [encOption_some, List.length_cons, encBits_apply]
          omega
      have hcfgLen2 := Nat.mul_le_mul_left 2 hcfgLen
      rw [← Nat.mul_assoc] at hcfgLen2
      dsimp only [Acc, encAcc, size]
      rw [length_encPair, Nat.add_mul]
      dsimp only
      omega)).1
  have hout : ComputableInPolyTime (fun acc : Acc => (acc.1.tapes.output, acc.2))
      encAcc (encPair encBits (encOption encBits)) := by
    have hbuilt :=
      (((ComputableInPolyTime.fst encFiniteConfig (encOption encBits)).trans
        (ComputableInPolyTime.finiteConfig_tapes (k := k) (State := Control)
          (Oracle := Unit))).trans
        ComputableInPolyTime.finiteCfg_output).prod
        (ComputableInPolyTime.snd encFiniteConfig (encOption encBits))
    exact hbuilt.of_enc_eq fun _ => rfl
  exact (hfold.trans hout).of_enc_eq fun _ => rfl

/-- `simRun` is computable in plain polynomial time for every finite-control `MultiTapePTM`. -/
theorem computableInPolyTime_simRun_comp {k : ℕ} {Control α : Type} [Finite Control]
    {input : α ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Unit)
    {word reply coins : α → List Bool}
    (hword : ComputableInPolyTime word input encBits)
    (hreply : ComputableInPolyTime reply input encBits)
    (hcoins : ComputableInPolyTime coins input encBits) :
    ComputableInPolyTime (fun a => simRun machine (word a) (reply a) (coins a))
      input (encPair encBits (encOption encBits)) :=
  ((hword.prod (hreply.prod hcoins)).trans
    (computableInPolyTime_simRun_raw machine)).of_enc_eq fun _ => rfl

/-! ### Exact coupling between `finiteStep` and `simStep` -/

private theorem simFold_some {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (reply : List Bool) (coins : List Bool) (cfg : FiniteConfig k Bool Control Unit)
    (m₀ : List Bool) :
    coins.foldl (simStep machine reply) (cfg, some m₀) =
      coins.foldl (simStep machine []) (cfg, some m₀) ∧
    (coins.foldl (simStep machine []) (cfg, some m₀)).2 = some m₀ := by
  induction coins generalizing cfg with
  | nil => exact ⟨rfl, rfl⟩
  | cons coin rest ih =>
    have hstep :
        ∃ cfg', simStep machine reply (cfg, some m₀) coin = (cfg', some m₀) ∧
          simStep machine [] (cfg, some m₀) coin = (cfg', some m₀) := by
      dsimp only [simStep]
      cases cfg.tapes.state with
      | none => exact ⟨cfg, rfl, rfl⟩
      | some state =>
        dsimp only
        cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols coin with
        | step action symbol move => exact ⟨cfg.step action symbol move, rfl, rfl⟩
        | query ch next =>
          cases ch
          dsimp only
          simp only [Option.isNone_some, Bool.and_false]
          exact ⟨cfg.receive () next [], rfl, rfl⟩
    obtain ⟨cfg', h1, h2⟩ := hstep
    simp only [List.foldl_cons, h1, h2]
    exact ih cfg'

private theorem simFold_none_eq {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit)
    (reply : List Bool) (coins : List Bool) (cfg : FiniteConfig k Bool Control Unit)
    (hnone : (coins.foldl (simStep machine []) (cfg, none)).2 = none) :
    coins.foldl (simStep machine reply) (cfg, none) =
      coins.foldl (simStep machine []) (cfg, none) := by
  induction coins generalizing cfg with
  | nil => rfl
  | cons coin rest ih =>
    simp only [List.foldl_cons] at hnone ⊢
    have hstepNone : (simStep machine [] (cfg, none) coin).2 = none := by
      cases hs : (simStep machine [] (cfg, none) coin).2 with
      | none => rfl
      | some m₀ =>
        have hkeep :
            (rest.foldl (simStep machine [])
              (simStep machine [] (cfg, none) coin)).2 = some m₀ := by
          rcases hpair : simStep machine [] (cfg, none) coin with ⟨cfg', q'⟩
          rw [hpair] at hs
          dsimp only at hs
          subst hs
          exact (simFold_some machine [] rest cfg' m₀).2
        rw [hkeep] at hnone
        cases hnone
    have hstepEq :
        simStep machine reply (cfg, none) coin = simStep machine [] (cfg, none) coin := by
      unfold simStep at hstepNone ⊢
      cases hst : cfg.tapes.state with
      | none => rfl
      | some state =>
        simp only [hst] at hstepNone ⊢
        cases htr : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols coin with
        | step action symbol move => rfl
        | query ch next =>
          cases ch
          simp only [htr] at hstepNone ⊢
          split_ifs with hfirst
          · simp only [hfirst, ↓reduceIte] at hstepNone
            cases hstepNone
          · rfl
    rw [hstepEq]
    rcases hpair : simStep machine [] (cfg, none) coin with ⟨cfg', q'⟩
    rw [hpair] at hnone hstepNone
    dsimp only at hstepNone
    subst hstepNone
    exact ih cfg' hnone

private theorem iterate_finiteStep_after_query {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    (n : ℕ) (sk : List Bool) (limit steps : ℕ)
    (cfg : FiniteConfig k Bool Control Unit) (m₀ : List Bool) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun req s => ProbComp.eval ((scheme S H).indexedSigningOracle n sk req s)))
      (OracleComp.iterate steps
        (machine.finiteStep
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => List.take limit <$> ProbOracleComp.query (op, word)))
        cfg)).run [(0, m₀)] =
    (BitString.uniformList steps).map fun coins =>
      ((coins.foldl (simStep machine []) (cfg, some m₀)).1, [(0, m₀)]) := by
  induction steps generalizing cfg with
  | zero =>
    simp only [OracleComp.iterate_zero, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, BitString.uniformList_zero, PMF.pure_map,
      List.foldl_nil]
  | succ steps ih =>
    rw [OracleComp.iterate_succ_bind, BitString.uniformList_succ, PMF.map_bind]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [finiteStep, hs, pure_bind, ih cfg, PMF.map_comp, Function.comp_def,
        List.foldl_cons, simStep, PMF.bind_const]
    | some state =>
      simp only [finiteStep, hs, bind_map_left, bind_assoc, OracleComp.interpret_bind,
        StateT.run_bind, ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform,
        Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
      congr 1
      funext bit
      cases htr : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | step action symbol move =>
        simp only [OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, PMF.pure_bind, ih (cfg.step action symbol move),
          PMF.map_comp, Function.comp_def, List.foldl_cons, simStep, hs, htr]
      | query ch next =>
        cases ch
        have hrefuse :
            ¬ ((IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1).1 < 1 ∧
              (IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1).1 ∉
                ([(0, m₀)].map Prod.fst)) := by
          rintro ⟨hlt, hnotmem⟩
          have hzero : (IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1).1 = 0 :=
            by omega
          exact hnotmem (by simp [hzero])
        have hq :
            StateT.run
              (fun s => ProbComp.eval
                ((scheme S H).indexedSigningOracle n sk ((), (cfg.channels ()).1) s))
              [(0, m₀)] = PMF.pure ([], [(0, m₀)]) := by
          simp only [StateT.run, IndexedSignatureScheme.indexedSigningOracle, scheme_capacity,
            hrefuse, ↓reduceIte, ProbComp.eval_pure]
        simp only [OracleComp.interpret_bind, OracleComp.interpret_pure,
          StateT.run_bind, StateT.run_pure, ProbOracleComp.interpret_query,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
        rw [hq]
        simp only [PMF.pure_bind, List.take_nil, ih (cfg.receive () next []), PMF.map_comp,
          Function.comp_def, List.foldl_cons, simStep, hs, htr, Option.isNone_some, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte]

private theorem iterate_finiteStep_from_empty {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    (n : ℕ) (otsk : List Bool) (limit steps : ℕ)
    (cfg : FiniteConfig k Bool Control Unit) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun req s => ProbComp.eval
          ((scheme S H).indexedSigningOracle n (encPair encUnary encBits (n, otsk)) req s)))
      (OracleComp.iterate steps
        (machine.finiteStep
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => List.take limit <$> ProbOracleComp.query (op, word)))
        cfg)).run [] =
    (BitString.uniformList steps).bind fun coins =>
      let r0 := coins.foldl (simStep machine []) (cfg, none)
      match r0.2 with
      | none => PMF.pure (r0.1, [])
      | some m₀ =>
        (BitString.uniformList (H.keyLen n)).bind fun hashKey =>
          (ProbComp.eval (S.sign otsk (otsMsg H n hashKey (H.eval n hashKey m₀)))).map fun ots =>
            ((coins.foldl (simStep machine ((encPair encBits encBits (hashKey, ots)).take limit))
              (cfg, none)).1, [(0, m₀)]) := by
  induction steps generalizing cfg with
  | zero =>
    simp only [OracleComp.iterate_zero, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, BitString.uniformList_zero, PMF.pure_bind,
      List.foldl_nil]
  | succ steps ih =>
    rw [OracleComp.iterate_succ_bind, BitString.uniformList_succ, PMF.bind_bind]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [finiteStep, hs, pure_bind, ih cfg]
      let rhs (coins : List Bool) :
          PMF (FiniteConfig k Bool Control Unit × List (ℕ × List Bool)) :=
        let r0 := coins.foldl (simStep machine []) (cfg, none)
        match r0.2 with
        | none => PMF.pure (r0.1, [])
        | some m₀ =>
          (BitString.uniformList (H.keyLen n)).bind fun hashKey =>
            (ProbComp.eval
              (S.sign otsk (otsMsg H n hashKey (H.eval n hashKey m₀)))).map fun ots =>
                ((coins.foldl
                  (simStep machine ((encPair encBits encBits (hashKey, ots)).take limit))
                  (cfg, none)).1, [(0, m₀)])
      have hconst (bit : Bool) :
          ((BitString.uniformList steps).map (List.cons bit)).bind rhs =
            (BitString.uniformList steps).bind rhs := by
        simp only [rhs, PMF.bind_map, Function.comp_def, List.foldl_cons, simStep, hs]
      change (BitString.uniformList steps).bind rhs =
        (PMF.uniformOfFintype Bool).bind
          (fun bit => ((BitString.uniformList steps).map (List.cons bit)).bind rhs)
      simp only [hconst, PMF.bind_const]
    | some state =>
      simp only [finiteStep, hs, bind_map_left, bind_assoc, OracleComp.interpret_bind,
        StateT.run_bind, ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform,
        Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
      congr 1
      funext bit
      cases htr : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | step action symbol move =>
        simp only [OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, PMF.pure_bind, ih (cfg.step action symbol move),
          List.foldl_cons, simStep, hs, htr]
      | query ch next =>
        cases ch
        let r := IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1
        by_cases hr0 : r.1 = 0
        · have haccept : r.1 < 1 ∧ r.1 ∉ ([] : List (ℕ × List Bool)).map Prod.fst := by
            simp [hr0]
          have hrPair : r = (0, r.2) := Prod.ext hr0 rfl
          have hq :
              StateT.run
                (fun s => ProbComp.eval
                  ((scheme S H).indexedSigningOracle n
                    (encPair encUnary encBits (n, otsk)) ((), (cfg.channels ()).1) s))
                [] =
              (BitString.uniformList (H.keyLen n)).bind fun hashKey =>
                (ProbComp.eval
                  (S.sign otsk (otsMsg H n hashKey (H.eval n hashKey r.2)))).bind fun ots =>
                    PMF.pure (encPair encBits encBits (hashKey, ots), [(0, r.2)]) := by
            dsimp only [StateT.run, IndexedSignatureScheme.indexedSigningOracle, scheme]
            split_ifs with hcond
            · change ProbComp.eval (do
                let sig ← sign S H (encPair encUnary encBits (n, otsk)) r.1 r.2
                return (sig, [r])) = _
              rw [← hrPair]
              simp only [sign, keyDecoder.decode_enc, hr0, ↓reduceIte, ProbComp.eval_bind,
                ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
            · exact (hcond haccept).elim
          simp only [OracleComp.interpret_bind, OracleComp.interpret_pure,
            StateT.run_bind, StateT.run_pure, ProbOracleComp.interpret_query,
            Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
          rw [hq]
          simp only [PMF.bind_bind, PMF.pure_bind]
          have hcont : ∀ hashKey ots,
              ((OracleComp.interpret
                (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
                  (fun req s => ProbComp.eval
                    ((scheme S H).indexedSigningOracle n (encPair encUnary encBits (n, otsk))
                      req s)))
                (OracleComp.iterate steps
                  (machine.finiteStep
                    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
                    (fun op word => List.take limit <$> ProbOracleComp.query (op, word)))
                  (cfg.receive () next ((encPair encBits encBits (hashKey, ots)).take limit)))).run
                    [(0, r.2)]) =
              (BitString.uniformList steps).map fun cs =>
                (((bit :: cs).foldl
                  (simStep machine ((encPair encBits encBits (hashKey, ots)).take limit))
                  (cfg, none)).1, [(0, r.2)]) := by
            intro hashKey ots
            rw [iterate_finiteStep_after_query]
            congr 1
            funext cs
            have heq := (simFold_some machine
              ((encPair encBits encBits (hashKey, ots)).take limit) cs
              (cfg.receive () next ((encPair encBits encBits (hashKey, ots)).take limit)) r.2).1
            simp only [List.foldl_cons, simStep, hs, htr,
              show IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1 = r from rfl,
              hr0, beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte, heq]
          simp only [hcont]
          have hrhs : ∀ cs : List Bool,
              ((bit :: cs).foldl (simStep machine []) (cfg, none)).2 = some r.2 := by
            intro cs
            simp only [List.foldl_cons, simStep, hs, htr,
              show IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1 = r from rfl,
              hr0, beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte]
            exact (simFold_some machine [] cs (cfg.receive () next []) r.2).2
          simp only [hrhs]
          pmf_swap
        · have hrefuse : ¬ (r.1 < 1 ∧ r.1 ∉ ([] : List (ℕ × List Bool)).map Prod.fst) := by
            rintro ⟨hlt, _⟩
            exact hr0 (by omega)
          have hbeq : (r.1 == 0) = false := beq_false_of_ne hr0
          have hq :
              StateT.run
                (fun s => ProbComp.eval
                  ((scheme S H).indexedSigningOracle n
                    (encPair encUnary encBits (n, otsk)) ((), (cfg.channels ()).1) s))
                [] = PMF.pure ([], []) := by
            dsimp only [StateT.run, IndexedSignatureScheme.indexedSigningOracle, scheme]
            split_ifs with hcond
            · exact (hrefuse hcond).elim
            · exact ProbComp.eval_pure _
          simp only [OracleComp.interpret_bind, OracleComp.interpret_pure,
            StateT.run_bind, StateT.run_pure, ProbOracleComp.interpret_query,
            Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
          rw [hq]
          simp only [PMF.pure_bind, List.take_nil, ih (cfg.receive () next [])]
          congr 1
          funext cs
          simp only [List.foldl_cons, simStep, hs, htr,
            show IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1 = r from rfl,
            hbeq, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

end Simulator

/-! ### The two reductions: `oneTimeForger` and `tcrAdversary` -/

section Reductions

/-- Total decoder for raw `IndexedForger` outputs `(u, msg, sig)`. -/
@[expose]
def outDecoder : Decoder encIndexedSignedMessage :=
  Decoder.unary.pair (Decoder.bits.pair Decoder.bits)

/-- Total decoder for `tcrAdversary` saved state `(keys, coins)`. -/
@[expose]
def stateDecoder : Decoder (encPair (encPair encBits encBits) encBits) :=
  (Decoder.bits.pair Decoder.bits).pair Decoder.bits

/-- Bundled public key `(n, otvk)` passed to an adversary against `scheme` or `wordScheme`. -/
@[expose]
def simPkOf (n : ℕ) (otvk : List Bool) : List Bool :=
  encPair encUnary encBits (n, otvk)

/-- Encoded machine input `(n, simPkOf n otvk)` for a simulated adversary run. -/
@[expose]
def simWordOf (n : ℕ) (otvk : List Bool) : List Bool :=
  encPair encUnary encBits (n, simPkOf n otvk)

/-- Polynomial step/reply budget `c * ((simWordOf n otvk).length + 1) ^ d` on `(n, otvk)`. -/
@[expose]
def simFuelOf (c d n : ℕ) (otvk : List Bool) : ℕ :=
  c * ((simWordOf n otvk).length + 1) ^ d

/-- One-time signature forger at security parameter `M = otsParam H n`: recovers
`n := otsParamInv H M`, samples coins and a uniform hash key `k`, dry-runs `simRun` on `[]`,
queries its external one-time signing oracle at most once on `otsMsg H n k (H.eval n k m₀)` (with
reply truncated to `sigBound n`), replays `simRun`, and outputs `(otsMsg H n k' (H.eval n k' m₁),
ots')`. -/
noncomputable def oneTimeForger {k : ℕ} {Control : Type}
    (H : KeyedHashFamily) (sigBound : ℕ → ℕ)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ) : Forger :=
  fun M otvk =>
    let n := otsParamInv H M
    if otsParam H n = M then do
      let word := simWordOf n otvk
      let fuel := simFuelOf c d n otvk
      let coins ← ProbOracleComp.sample (BitString.sampleList fuel)
      let hashKey ← ProbOracleComp.sample (BitString.sampleList (H.keyLen n))
      let r0 := simRun machine word [] coins
      match r0.2 with
      | none =>
        let (_, msg, sig) := outDecoder.decode r0.1
        return otsForgeryOf H n msg sig
      | some m₀ =>
        let ots ← List.take (sigBound n) <$>
          ProbOracleComp.query ((), otsMsg H n hashKey (H.eval n hashKey m₀))
        let reply := (encPair encBits encBits (hashKey, ots)).take fuel
        let r1 := simRun machine word reply coins
        let (_, msg, sig) := outDecoder.decode r1.1
        return otsForgeryOf H n msg sig
    else
      pure ([], [])

/-- Two-stage target-collision adversary against `H`: `choose n` samples `keys ← S.keyGen
(otsParam H n)` and `coins`, dry-runs `simRun` on `[]` to commit the first valid signing query `m₀`
before `k` is chosen, and saves `(keys, coins)`; `find n state k` signs `(k, H.eval n k m₀)`
locally using `keys.2`, replays `simRun` on the same `coins`, and outputs the forged message `m₁`.
-/
noncomputable def tcrAdversary {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ) : TargetCollisionFinder where
  choose n := do
    let keys ← S.keyGen (otsParam H n)
    let word := simWordOf n keys.1
    let fuel := simFuelOf c d n keys.1
    let coins ← BitString.sampleList fuel
    let r0 := simRun machine word [] coins
    return (r0.2.getD [], encPair (encPair encBits encBits) encBits (keys, coins))
  find n stateWord hashKey := do
    let saved := stateDecoder.decode stateWord
    let keys := saved.1
    let coins := saved.2
    let word := simWordOf n keys.1
    let fuel := simFuelOf c d n keys.1
    let r0 := simRun machine word [] coins
    match r0.2 with
    | none =>
      let (_, m₁, _) := outDecoder.decode r0.1
      return m₁
    | some m₀ =>
      let ots ← S.sign keys.2 (otsMsg H n hashKey (H.eval n hashKey m₀))
      let reply := (encPair encBits encBits (hashKey, ots)).take fuel
      let r1 := simRun machine word reply coins
      let (_, m₁, _) := outDecoder.decode r1.1
      return m₁

theorem computableInPolyTime_wordOf {α : Type} {input : α ↪ List Bool}
    {n : α → ℕ} {pk : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits) :
    ComputableInPolyTime (fun a => simWordOf (n a) (pk a)) input encBits := by
  have henc : ComputableInPolyTime (encPair encUnary encBits)
      (encPair encUnary encBits) encBits := .of_eq fun _ => rfl
  exact henc.comp (hn.prod (henc.comp (hn.prod hpk)))

theorem computableInPolyTime_fuelOf {α : Type} {input : α ↪ List Bool}
    (c d : ℕ) {n : α → ℕ} {pk : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits) :
    ComputableInPolyTime (fun a => simFuelOf c d (n a) (pk a)) input encUnary := by
  have hword := computableInPolyTime_wordOf hn hpk
  unfold simFuelOf
  fun_prop

private theorem computableInPolyTime_simReplay_comp {k : ℕ} {Control α : Type}
    [Finite Control] {input : α ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Unit)
    {word hk ots : α → List Bool} {fuel : α → ℕ} {coins : α → List Bool}
    (hword : ComputableInPolyTime word input encBits)
    (hhk : ComputableInPolyTime hk input encBits)
    (hots : ComputableInPolyTime ots input encBits)
    (hfuel : ComputableInPolyTime fuel input encUnary)
    (hcoins : ComputableInPolyTime coins input encBits) :
    ComputableInPolyTime
      (fun a => simRun machine (word a)
        ((encPair encBits encBits (hk a, ots a)).take (fuel a)) (coins a))
      input (encPair encBits (encOption encBits)) := by
  have henc : ComputableInPolyTime (encPair encBits encBits)
      (encPair encBits encBits) encBits := .of_eq fun _ => rfl
  have hreply := ComputableInPolyTime.bitsTakeWithInput ((hhk.prod hots).trans henc) hfuel
  exact computableInPolyTime_simRun_comp machine hword hreply hcoins

/-- `oneTimeForger` is uniformly strict oracle PPT whenever `sigBound` is computable in plain
polynomial time on unary `n`. -/
theorem isOraclePPT_oneTimeForger {k : ℕ} {Control : Type} [Finite Control]
    (H : KeyedHashFamily) {sigBound : ℕ → ℕ}
    (hsigBound : ComputableInPolyTime sigBound encUnary encUnary)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ) :
    IsOraclePPT (encPair encBits encBits) (oneTimeForger H sigBound machine c d) := by
  apply IsOraclePPTOn.isOraclePPT
  let In := ℕ × List Bool
  let encIn : In ↪ List Bool := encPair encUnary encBits
  have hM : ComputableInPolyTime (fun p : In => p.1) encIn encUnary :=
    ComputableInPolyTime.fst _ _
  have hotvk : ComputableInPolyTime (fun p : In => p.2) encIn encBits :=
    ComputableInPolyTime.snd _ _
  have hn : ComputableInPolyTime (fun p : In => otsParamInv H p.1) encIn encUnary :=
    (computableInPolyTime_otsParamInv H).comp hM
  have hcond : ComputableInPolyTime
      (fun p : In => decide (otsParam H (otsParamInv H p.1) = p.1)) encIn encBool :=
    ComputableInPolyTime.unary_eq' ((computableInPolyTime_otsParam H).comp hn) hM
  have hword := computableInPolyTime_wordOf hn hotvk
  have hfuel := computableInPolyTime_fuelOf c d hn hotvk
  have hcoins : IsOraclePPTOn (Operation := Unit) encIn encBits
      (fun p : In => ProbOracleComp.sample
        (BitString.sampleList (simFuelOf c d (otsParamInv H p.1) p.2))) :=
    hfuel.sampleList.isOraclePPTOn
  have hhashKey : IsOraclePPTOn (Operation := Unit) (encPair encIn encBits) encBits
      (fun q : In × List Bool => ProbOracleComp.sample
        (BitString.sampleList (H.keyLen (otsParamInv H q.1.1)))) :=
    ((H.keyLen_polyTime.comp (hn.comp (ComputableInPolyTime.fst _ _))).sampleList).isOraclePPTOn
  let Mid := (In × List Bool) × List Bool
  let encMid : Mid ↪ List Bool := encPair (encPair encIn encBits) encBits
  have hmIn : ComputableInPolyTime (fun q : Mid => q.1.1) encMid encIn :=
    (ComputableInPolyTime.fst _ _).fst'
  have hmCoins : ComputableInPolyTime (fun q : Mid => q.1.2) encMid encBits :=
    (ComputableInPolyTime.fst _ _).snd'
  have hmK : ComputableInPolyTime (fun q : Mid => q.2) encMid encBits :=
    ComputableInPolyTime.snd _ _
  have hmN : ComputableInPolyTime (fun q : Mid => otsParamInv H q.1.1.1) encMid encUnary :=
    hn.comp hmIn
  have hmWord : ComputableInPolyTime
      (fun q : Mid => simWordOf (otsParamInv H q.1.1.1) q.1.1.2) encMid encBits :=
    hword.comp hmIn
  have hmFuel : ComputableInPolyTime
      (fun q : Mid => simFuelOf c d (otsParamInv H q.1.1.1) q.1.1.2) encMid encUnary :=
    hfuel.comp hmIn
  have hmR0 := computableInPolyTime_simRun_comp machine hmWord (.const []) hmCoins
  have hmOut0 := hmR0.fst'.trans outDecoder.computableInPolyTime
  have hbranchNone : IsOraclePPTOn (Operation := Unit) encMid (encPair encBits encBits)
      (fun q : Mid =>
        let r0 := simRun machine (simWordOf (otsParamInv H q.1.1.1) q.1.1.2) [] q.1.2
        let out := outDecoder.decode r0.1
        pure (otsForgeryOf H (otsParamInv H q.1.1.1) out.2.1 out.2.2)) :=
    ((computableInPolyTime_otsForgeryOf_comp H hmN hmOut0.snd'.fst' hmOut0.snd'.snd').of_enc_eq
      fun _ => rfl).isOraclePPTOn
  have hmM0 := hmR0.snd'.optionGetDWithInput (.const [])
  have hmOtsReq := computableInPolyTime_otsMsg_eval_comp H hmN hmK hmM0
  have hqueryOts : IsOraclePPTOn (Operation := Unit) encMid encBits
      (fun q : Mid => List.take (sigBound (otsParamInv H q.1.1.1)) <$>
        ProbOracleComp.query ((),
          otsMsg H (otsParamInv H q.1.1.1) q.2
            (H.eval (otsParamInv H q.1.1.1) q.2
              ((simRun machine (simWordOf (otsParamInv H q.1.1.1) q.1.1.2)
                [] q.1.2).2.getD [])))) :=
    IsOraclePPTOn.query_take' () (hmOtsReq.of_enc_eq fun _ => rfl)
      ((hmN.trans hsigBound).of_enc_eq fun _ => rfl)
  have hpostSome : ComputableInPolyTime
      (fun r : Mid × List Bool =>
        let n := otsParamInv H r.1.1.1.1
        let word := simWordOf n r.1.1.1.2
        let fuel := simFuelOf c d n r.1.1.1.2
        let reply := (encPair encBits encBits (r.1.2, r.2)).take fuel
        let r1 := simRun machine word reply r.1.1.2
        let out := outDecoder.decode r1.1
        otsForgeryOf H n out.2.1 out.2.2)
      (encPair encMid encBits) (encPair encBits encBits) := by
    have hrMid := ComputableInPolyTime.fst encMid encBits
    have hrOts := ComputableInPolyTime.snd encMid encBits
    have hr1 := computableInPolyTime_simReplay_comp machine
      (hrMid.trans hmWord) (hrMid.trans hmK) hrOts (hrMid.trans hmFuel) (hrMid.trans hmCoins)
    have hrOut1 := hr1.fst'.trans outDecoder.computableInPolyTime
    exact (computableInPolyTime_otsForgeryOf_comp H
      (hrMid.trans hmN) hrOut1.snd'.fst' hrOut1.snd'.snd').of_enc_eq fun _ => rfl
  have hbranchSome := hqueryOts.map_pair' hpostSome
  have hmatch : IsOraclePPTOn (Operation := Unit) encMid (encPair encBits encBits)
      (fun q : Mid =>
        let n := otsParamInv H q.1.1.1
        let word := simWordOf n q.1.1.2
        let fuel := simFuelOf c d n q.1.1.2
        let r0 := simRun machine word [] q.1.2
        match r0.2 with
        | none =>
          let out := outDecoder.decode r0.1
          pure (otsForgeryOf H n out.2.1 out.2.2)
        | some m₀ => do
          let ots ← List.take (sigBound n) <$>
            ProbOracleComp.query ((), otsMsg H n q.2 (H.eval n q.2 m₀))
          let reply := (encPair encBits encBits (q.2, ots)).take fuel
          let r1 := simRun machine word reply q.1.2
          let out := outDecoder.decode r1.1
          return otsForgeryOf H n out.2.1 out.2.2) := by
    have hite := IsOraclePPTOn.cond' hmR0.snd'.optionIsSome hbranchSome hbranchNone
    refine hite.congr fun q State oracle s => ?_
    dsimp only
    cases hopt : (simRun machine (simWordOf (otsParamInv H q.1.1.1) q.1.1.2) [] q.1.2).2 with
    | none => rfl
    | some m₀ =>
      simp only [Option.isSome_some, ↓reduceIte, Option.getD_some]
  have hactive := hcoins.bind_pair (hhashKey.bind_pair hmatch)
  have hempty : IsOraclePPTOn (Operation := Unit) encIn (encPair encBits encBits)
      (fun _ : In => pure ([], [])) :=
    (ComputableInPolyTime.const (encIn := encIn) (encOut := encPair encBits encBits)
      ([], [])).isOraclePPTOn
  exact (IsOraclePPTOn.ite' hcond hactive hempty).congr fun _ _ _ _ => rfl

/-- Both stages of `tcrAdversary` are uniformly strict PPT. -/
theorem isPPT_tcrAdversary {k : ℕ} {Control : Type} [Finite Control]
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ) :
    (tcrAdversary S H machine c d).IsPPT where
  choose := by
    have hkg : IsPPTOn encUnary (encPair encBits encBits)
        (fun n => S.keyGen (otsParam H n)) :=
      S.isPPTOn_keyGen_comp (computableInPolyTime_otsParam H)
    let KIn := ℕ × (List Bool × List Bool)
    let encKIn : KIn ↪ List Bool := encPair encUnary (encPair encBits encBits)
    have hn : ComputableInPolyTime (fun p : KIn => p.1) encKIn encUnary :=
      ComputableInPolyTime.fst _ _
    have hkeys : ComputableInPolyTime (fun p : KIn => p.2) encKIn (encPair encBits encBits) :=
      ComputableInPolyTime.snd _ _
    have hword := computableInPolyTime_wordOf hn hkeys.fst'
    have hfuel := computableInPolyTime_fuelOf c d hn hkeys.fst'
    have hcoins : IsPPTOn encKIn encBits
        (fun p : KIn => BitString.sampleList (simFuelOf c d p.1 p.2.1)) :=
      (hfuel.of_enc_eq fun _ => rfl).sampleList
    have hpost : ComputableInPolyTime
        (fun q : KIn × List Bool =>
          let r0 := simRun machine (simWordOf q.1.1 q.1.2.1) [] q.2
          (r0.2.getD [], encPair (encPair encBits encBits) encBits (q.1.2, q.2)))
        (encPair encKIn encBits) (encPair encBits encBits) := by
      have hqIn := ComputableInPolyTime.fst encKIn encBits
      have hqCoins := ComputableInPolyTime.snd encKIn encBits
      have hr0 := computableInPolyTime_simRun_comp machine
        (hqIn.trans hword) (.const []) hqCoins
      have hm0 := hr0.snd'.optionGetDWithInput (.const [])
      have hencState : ComputableInPolyTime (encPair (encPair encBits encBits) encBits)
          (encPair (encPair encBits encBits) encBits) encBits := .of_eq fun _ => rfl
      have hst := ((hqIn.trans hkeys).prod hqCoins).trans hencState
      exact (hm0.prod hst).of_enc_eq fun _ => rfl
    exact (hkg.bind_pair (hcoins.map_pair hpost)).congr fun _ => rfl
  find := by
    let FIn := ℕ × List Bool × List Bool
    let encFIn : FIn ↪ List Bool := encPair encUnary (encPair encBits encBits)
    have hn : ComputableInPolyTime (fun p : FIn => p.1) encFIn encUnary :=
      ComputableInPolyTime.fst _ _
    have hstateWord : ComputableInPolyTime (fun p : FIn => p.2.1) encFIn encBits :=
      (ComputableInPolyTime.snd _ _).fst'
    have hhashKey : ComputableInPolyTime (fun p : FIn => p.2.2) encFIn encBits :=
      (ComputableInPolyTime.snd _ _).snd'
    have hsaved := hstateWord.trans stateDecoder.computableInPolyTime
    have hkeys := hsaved.fst'
    have hcoins := hsaved.snd'
    have hword := computableInPolyTime_wordOf hn hkeys.fst'
    have hfuel := computableInPolyTime_fuelOf c d hn hkeys.fst'
    have hr0 := computableInPolyTime_simRun_comp machine hword (.const []) hcoins
    have hisSome := hr0.snd'.optionIsSome
    have hbranchNone : IsPPTOn encFIn encBits
        (fun p : FIn =>
          let saved := stateDecoder.decode p.2.1
          let r0 := simRun machine (simWordOf p.1 saved.1.1) [] saved.2
          pure (outDecoder.decode r0.1).2.1) :=
      (((hr0.fst'.trans outDecoder.computableInPolyTime).snd'.fst').of_enc_eq fun _ => rfl).isPPTOn
    have hm0 := hr0.snd'.optionGetDWithInput (.const [])
    have hM0 := computableInPolyTime_otsMsg_eval_comp H hn hhashKey hm0
    have hsignOts := S.isPPTOn_sign_comp (hkeys.snd'.of_enc_eq fun _ => rfl)
      (hM0.of_enc_eq fun _ => rfl)
    have hpostSome : ComputableInPolyTime
        (fun q : FIn × List Bool =>
          let saved := stateDecoder.decode q.1.2.1
          let word := simWordOf q.1.1 saved.1.1
          let fuel := simFuelOf c d q.1.1 saved.1.1
          let reply := (encPair encBits encBits (q.1.2.2, q.2)).take fuel
          let r1 := simRun machine word reply saved.2
          (outDecoder.decode r1.1).2.1)
        (encPair encFIn encBits) encBits := by
      have hqIn := ComputableInPolyTime.fst encFIn encBits
      have hqOts := ComputableInPolyTime.snd encFIn encBits
      have hr1 := computableInPolyTime_simReplay_comp machine
        (hqIn.trans hword) (hqIn.trans hhashKey) hqOts (hqIn.trans hfuel) (hqIn.trans hcoins)
      exact ((hr1.fst'.trans outDecoder.computableInPolyTime).snd'.fst').of_enc_eq fun _ => rfl
    have hbranchSome := hsignOts.map_pair hpostSome
    have hcondFIn : ComputableInPolyTime
        (fun p : FIn => decide ((simRun machine
          (simWordOf p.1 (stateDecoder.decode p.2.1).1.1)
          [] (stateDecoder.decode p.2.1).2).2.isSome = true))
        encFIn encBool :=
      hisSome.of_enc_eq fun _ => rfl
    have hite := IsPPTOn.ite' hcondFIn hbranchSome hbranchNone
    refine hite.congr fun p => ?_
    dsimp only [tcrAdversary]
    cases hopt : (simRun machine
        (simWordOf p.1 (stateDecoder.decode p.2.1).1.1)
        [] (stateDecoder.decode p.2.1).2).2 with
    | none => rfl
    | some m₀ =>
      simp only [Option.isSome_some, ↓reduceIte, Option.getD_some]

/-! ### Security bound and existential upgrades -/

/-- **Concrete security bound for `TCRSignature.scheme` with an explicit realizing machine**
([BonehShoup2023], Section 13.2.1, Theorem 13.2): at every security parameter `n`, the indexed
forging probability against `scheme S H` is at most the one-time forging probability of
`oneTimeForger` against `S` at `otsParam H n` plus the target-collision probability of
`tcrAdversary` against `H` at `n`. -/
theorem succProbability_indexedEufCmaGame_le_of_machine {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (sigBound : ℕ → ℕ)
    (hsigBound : ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen (otsParam H n))).support,
      ∀ msg, msg.length = otsParam H n →
      ∀ ots ∈ (ProbComp.eval (S.sign keys.2 msg)).support, ots.length ≤ sigBound n)
    (adversary : IndexedForger)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ)
    (hmachine : ∀ (input : ℕ × List Bool) (State : Type)
      (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
          (encIndexedSignedMessage <$> adversary input.1 input.2)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
          (machine.runOracle
            (c * ((encPair encUnary encBits input).length + 1) ^ d)
            (encPair encUnary encBits input))).run s)
    (n : ℕ) :
    Game.succProbability (ProbComp.eval ((scheme S H).indexedEufCmaGame adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (S.eufOneTimeGame (oneTimeForger H sigBound machine c d) (otsParam H n))) +
      Game.succProbability
        (ProbComp.eval
          (targetCollisionGame H.keyLen H.eval (fun _ _ => true)
            (tcrAdversary S H machine c d) n)) := by
  let pkOf := simPkOf n
  let wordOf := simWordOf n
  let fuelOf := simFuelOf c d n
  let otsDist (keys : List Bool × List Bool) (coins hashKey : List Bool) : PMF (List Bool) :=
    match (simRun machine (wordOf keys.1) [] coins).2 with
    | none => PMF.pure []
    | some m₀ => ProbComp.eval (S.sign keys.2 (otsMsg H n hashKey (H.eval n hashKey m₀)))
  let μ : PMF ((List Bool × List Bool) × List Bool × List Bool × List Bool) := do
    let keys ← ProbComp.eval (S.keyGen (otsParam H n))
    let coins ← BitString.uniformList (fuelOf keys.1)
    let hashKey ← BitString.uniformList (H.keyLen n)
    (otsDist keys coins hashKey).map fun ots => (keys, coins, hashKey, ots)
  let finalOut (keys : List Bool × List Bool) (coins hashKey ots : List Bool) :
      ℕ × List Bool × List Bool :=
    match (simRun machine (wordOf keys.1) [] coins).2 with
    | none => outDecoder.decode (simRun machine (wordOf keys.1) [] coins).1
    | some _ =>
      outDecoder.decode
        (simRun machine (wordOf keys.1)
          ((encPair encBits encBits (hashKey, ots)).take (fuelOf keys.1)) coins).1
  let winIdx (sample : (List Bool × List Bool) × List Bool × List Bool × List Bool) : Bool :=
    let keys := sample.1
    let coins := sample.2.1
    let hashKey := sample.2.2.1
    let ots := sample.2.2.2
    let out := finalOut keys coins hashKey ots
    let signed : List (ℕ × List Bool) :=
      match (simRun machine (wordOf keys.1) [] coins).2 with
      | none => []
      | some m₀ => [(0, m₀)]
    !signed.contains (out.1, out.2.1) && verify S H (pkOf keys.1) out.1 out.2.1 out.2.2
  let winOts (sample : (List Bool × List Bool) × List Bool × List Bool × List Bool) : Bool :=
    let keys := sample.1
    let coins := sample.2.1
    let hashKey := sample.2.2.1
    let ots := sample.2.2.2
    let out := finalOut keys coins hashKey ots
    let parsedSig := sigDecoder.decode out.2.2
    let MStar := otsMsg H n parsedSig.1 (H.eval n parsedSig.1 out.2.1)
    let queried : List (List Bool) :=
      match (simRun machine (wordOf keys.1) [] coins).2 with
      | none => []
      | some m₀ => [otsMsg H n hashKey (H.eval n hashKey m₀)]
    (MStar.length == otsParam H n) && !queried.contains MStar && S.verify keys.1 MStar parsedSig.2
  let winTcr (sample : (List Bool × List Bool) × List Bool × List Bool × List Bool) : Bool :=
    let keys := sample.1
    let coins := sample.2.1
    let hashKey := sample.2.2.1
    let ots := sample.2.2.2
    let m₀ := (simRun machine (wordOf keys.1) [] coins).2.getD []
    let out := finalOut keys coins hashKey ots
    isCollision (H.eval n) (fun _ _ => true) n hashKey m₀ out.2.1
  have hidxEq :
      ProbComp.eval ((scheme S H).indexedEufCmaGame adversary n) = μ.map winIdx := by
    have hdecodeAdv : ∀ pk,
        adversary n pk =
          outDecoder.decode <$>
            ((encPair encUnary (encPair encBits encBits)) <$> adversary n pk) := by
      intro pk
      simp only [Functor.map_map, outDecoder.decode_enc]
      exact (id_map _).symm
    simp only [IndexedSignatureScheme.indexedEufCmaGame, scheme_keyGen, scheme_verify, keyGen,
      ProbOracleComp.eval_run_interpret, μ, pmf_norm]
    peel_binds keys
    rw [hdecodeAdv (encPair encUnary encBits (n, keys.1)), OracleComp.interpret_map,
      StateT.run_map, _root_.PMF.monad_map_eq_map,
      hmachine (n, encPair encUnary encBits (n, keys.1)) _ _ []]
    erw [← machine.finiteRunFrom_take_runOracle (fuelOf keys.1) (wordOf keys.1)]
    simp only [finiteRunFrom, OracleComp.interpret_map, StateT.run_map, pmf_norm]
    rw [iterate_finiteStep_from_empty S H machine n keys.2 (fuelOf keys.1) (fuelOf keys.1)
      (FiniteConfig.init machine.initial (wordOf keys.1))]
    simp only [pmf_norm]
    peel_binds coins
    dsimp only [otsDist, winIdx, finalOut, simRun, wordOf, pkOf, fuelOf,
      simWordOf, simPkOf, simFuelOf]
    cases hopt : ((coins.foldl (simStep machine [])
        (FiniteConfig.init machine.initial
          (encPair encUnary encBits (n, encPair encUnary encBits (n, keys.1))), none)).2) with
    | none =>
      simp only [PMF.bind_const, pmf_norm]
    | some m₀ =>
      simp only [_root_.PMF.map, pmf_norm]
  have hotsEq :
      ProbComp.eval (S.eufOneTimeGame (oneTimeForger H sigBound machine c d) (otsParam H n)) =
        μ.map winOts := by
    simp only [SignatureScheme.eufOneTimeGame, oneTimeForger, otsParamInv_otsParam, ↓reduceIte,
      BitString.eval_sampleList, μ, fuelOf, runWith_norm, pmf_norm]
    peel_binds keys coins hashKey
    dsimp only [otsDist, winOts, finalOut, wordOf, pkOf, fuelOf, simWordOf, simPkOf, simFuelOf,
      otsForgeryOf]
    cases hopt : (simRun machine
        (encPair encUnary encBits (n, encPair encUnary encBits (n, keys.1))) [] coins).2 with
    | none =>
      simp only [runWith_norm, pmf_norm]
    | some m₀ =>
      simp only [SignatureScheme.oneTimeSigningOracle, SignatureScheme.oneTimeSigningOracleOf,
        List.isEmpty_nil, ↓reduceIte, _root_.PMF.map, runWith_norm, pmf_norm]
      peel_binds ots
      have htake : ots.take (sigBound n) = ots :=
        List.take_of_length_le
          (hsigBound n keys keys_mem (otsMsg H n hashKey (H.eval n hashKey m₀))
            (length_otsMsg H n hashKey _) ots ots_mem)
      simp only [htake]
  have htcrEq :
      ProbComp.eval
        (targetCollisionGame H.keyLen H.eval (fun _ _ => true)
          (tcrAdversary S H machine c d) n) = μ.map winTcr := by
    simp only [targetCollisionGame, tcrAdversary, BitString.eval_sampleList,
      stateDecoder.decode_enc, μ, fuelOf, pmf_norm]
    peel_binds keys coins hashKey
    dsimp only [otsDist, winTcr, finalOut, wordOf, pkOf, fuelOf, simWordOf, simPkOf, simFuelOf]
    cases hopt : (simRun machine
        (encPair encUnary encBits (n, encPair encUnary encBits (n, keys.1))) [] coins).2 <;>
      simp only [_root_.PMF.map, pmf_norm]
  have hpointwise : ∀ sample ∈ μ.support,
      winIdx sample = true → winOts sample = true ∨ winTcr sample = true := by
    rintro ⟨keys, coins, hashKey, ots⟩ hsupp hwin
    simp only [μ, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hsupp
    obtain ⟨keys', _, coins', _, hashKey', hhk, ⟨ots', _, heqSample⟩⟩ := hsupp
    rcases Prod.mk.inj heqSample.symm with ⟨rfl, heq1⟩
    rcases Prod.mk.inj heq1 with ⟨rfl, heq2⟩
    rcases Prod.mk.inj heq2 with ⟨rfl, rfl⟩
    have hhkLen : hashKey.length = H.keyLen n :=
      BitString.length_of_mem_support_uniformList hhk
    dsimp only [winIdx, pkOf, simPkOf] at hwin
    simp only [Bool.and_eq_true, Bool.not_eq_true', verify, keyDecoder.decode_enc, Bool.and_assoc,
      beq_iff_eq] at hwin
    obtain ⟨hnotSigned, hu0, hk'Len, hverifyS⟩ := hwin
    let out := finalOut keys coins hashKey ots
    let parsedSig := sigDecoder.decode out.2.2
    let MStar := otsMsg H n parsedSig.1 (H.eval n parsedSig.1 out.2.1)
    dsimp only [winOts, winTcr]
    cases hopt : (simRun machine (wordOf keys.1) [] coins).2 with
    | none =>
      left
      simp only [length_otsMsg, beq_self_eq_true, List.contains_nil, Bool.not_false,
        hverifyS, Bool.and_self]
    | some m₀ =>
      rw [hopt] at hnotSigned
      have hmNe : m₀ ≠ out.2.1 := by
        intro hEq
        rw [← hu0, ← hEq] at hnotSigned
        simp at hnotSigned
      by_cases hMEq : MStar = otsMsg H n hashKey (H.eval n hashKey m₀)
      · right
        have hd'Len : (H.eval n parsedSig.1 out.2.1).length = H.digestLen n :=
          H.length_eq n parsedSig.1 out.2.1 hk'Len
        have hd0Len : (H.eval n hashKey m₀).length = H.digestLen n :=
          H.length_eq n hashKey m₀ hhkLen
        obtain ⟨hkEq, hdEq⟩ := otsMsg_inj H hk'Len hd'Len hhkLen hd0Len hMEq
        rw [hkEq] at hdEq
        dsimp only [out] at hmNe hdEq
        simp only [Option.getD_some, isCollision, hdEq.symm, beq_self_eq_true, Bool.true_and,
          Bool.and_true, bne_iff_ne]
        exact hmNe
      · left
        have hnotMem : ¬ [otsMsg H n hashKey (H.eval n hashKey m₀)].contains MStar = true := by
          simp only [List.contains_iff_mem, List.mem_singleton]
          exact hMEq
        have hcontainsFalse :
            [otsMsg H n hashKey (H.eval n hashKey m₀)].contains
              (otsMsg H n (sigDecoder.decode (finalOut keys coins hashKey ots).2.2).1
                (H.eval n (sigDecoder.decode (finalOut keys coins hashKey ots).2.2).1
                  (finalOut keys coins hashKey ots).2.1)) = false :=
          Bool.eq_false_iff.mpr hnotMem
        simp only [length_otsMsg, beq_self_eq_true, hcontainsFalse, Bool.not_false,
          hverifyS, Bool.and_self]
  unfold Game.succProbability
  rw [hidxEq, hotsEq, htcrEq]
  have hne_top : (μ.map winOts) true + (μ.map winTcr) true ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩
  simpa only [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] using
    ENNReal.toNNReal_mono hne_top (μ.map_true_le_add hpointwise)

/-- Polynomial-time upper bounds on one-time verification keys and signatures sampled at
`otsParam H n`. -/
theorem exists_ots_bounds (S : SignatureScheme) (H : KeyedHashFamily) :
    ∃ (ckg dkg : ℕ) (sigBound : ℕ → ℕ),
      ComputableInPolyTime sigBound encUnary encUnary ∧
      (∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen (otsParam H n))).support,
        keys.1.length ≤ ckg * (otsParam H n + 1) ^ dkg) ∧
      (∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen (otsParam H n))).support,
        ∀ msg, msg.length = otsParam H n →
        ∀ ots ∈ (ProbComp.eval (S.sign keys.2 msg)).support, ots.length ≤ sigBound n) := by
  obtain ⟨ckg, dkg, hkgLen⟩ := S.keyGen_ppt.length_le
  obtain ⟨bound, hboundPoly, hbound⟩ := S.exists_sign_length_bound_of_length_eq
  refine ⟨ckg, dkg, fun n => bound (otsParam H n),
    hboundPoly.comp (computableInPolyTime_otsParam H), fun n keys hkeys => ?_,
    fun n => hbound (otsParam H n)⟩
  have hkPair := hkgLen (otsParam H n) keys hkeys
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at hkPair
  omega

/-- **Existential reduction for `TCRSignature.scheme`** ([BonehShoup2023], Section 13.2.1,
Theorem 13.2): every strict oracle-PPT indexed forger `adversary` induces a strict oracle-PPT
one-time forger `otForger` and a strict PPT two-stage `TargetCollisionFinder` `tcrAdv` bounding
`adversary`'s indexed forging probability at every security parameter `n`. -/
theorem exists_reduction_indexedEufCmaGame_le (S : SignatureScheme) (H : KeyedHashFamily)
    {adversary : IndexedForger}
    (hadversary : IsOraclePPT encIndexedSignedMessage adversary) :
    ∃ (otForger : Forger) (tcrAdv : TargetCollisionFinder),
      IsOraclePPT (encPair encBits encBits) otForger ∧
      tcrAdv.IsPPT ∧
      ∀ n, Game.succProbability (ProbComp.eval ((scheme S H).indexedEufCmaGame adversary n)) ≤
        Game.succProbability (ProbComp.eval (S.eufOneTimeGame otForger (otsParam H n))) +
          Game.succProbability
            (ProbComp.eval (targetCollisionGame H.keyLen H.eval (fun _ _ => true) tcrAdv n)) := by
  obtain ⟨_, k, Control, hfinite, machine, c, d, hmachine⟩ := hadversary.on
  obtain ⟨_, _, sigBound, hsigBoundPoly, _, hsigBoundLe⟩ := exists_ots_bounds S H
  exact ⟨oneTimeForger H sigBound machine c d,
    tcrAdversary S H machine c d,
    isOraclePPT_oneTimeForger H hsigBoundPoly machine c d,
    isPPT_tcrAdversary S H machine c d,
    succProbability_indexedEufCmaGame_le_of_machine S H sigBound hsigBoundLe adversary
      machine c d hmachine⟩

end Reductions

/-- Any `Negligible` function remains `Negligible` after precomposing with `otsParam H`. -/
theorem negligible_comp_otsParam {f : ℕ → ℝ≥0} (hf : Negligible f) (H : KeyedHashFamily) :
    Negligible (fun n => f (otsParam H n)) :=
  hf.comp_polynomiallyLowerBounded (.mono_of_le .id (le_otsParam H))

end TCRSignature

/-- **Fresh-key TCR hash-and-sign security** ([BonehShoup2023], Section 13.2.1, Theorem 13.2,
adapted to capacity-`1` indexed signatures over a one-time signature scheme): if `S` is one-time
EUF-CMA secure (`OneTimeEUFCMA`) and `H` is target collision-resistant on `List Bool`, then
`TCRSignature.scheme S H` is an `IndexedEUFCMA`-secure capacity-`1` indexed signature scheme on
arbitrary-length bit strings. -/
theorem SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature
    {S : SignatureScheme} (hS : S.OneTimeEUFCMA)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    (TCRSignature.scheme S H).IndexedEUFCMA := by
  refine IndexedSignatureScheme.IndexedEUFCMA.of_negligible fun adversary hadversary => ?_
  obtain ⟨otForger, tcrAdv, hotPPT, htcrPPT, hbound⟩ :=
    TCRSignature.exists_reduction_indexedEufCmaGame_le S H hadversary
  have := TCRSignature.negligible_comp_otsParam (hS.negligible otForger hotPPT) H
  have := hH.negligible tcrAdv htcrPPT
  negligible using hbound

/-- **Capacity-`2` indexed signatures from one-way functions and target collision-resistant hash
families**: combining Lamport's one-time signature scheme (`OneWay.exists_oneTimeSignature`),
`TCRSignature.scheme`, and `IndexedSignatureScheme.double` yields a capacity-`2` `IndexedEUFCMA`
scheme without collision-resistant hashing. -/
theorem OneWay.exists_indexedEUFCMA_of_targetCollisionResistant
    {f : List Bool → List Bool} (hf : OneWay f)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2) ∧ S.IndexedEUFCMA := by
  obtain ⟨S₀, hS₀⟩ := hf.exists_oneTimeSignature
  have hcap₁ : ∀ n, 1 ≤ (TCRSignature.scheme S₀ H).capacity n := fun _ => le_rfl
  exact ⟨(TCRSignature.scheme S₀ H).double hcap₁,
    fun _ => rfl,
    (hS₀.indexedEUFCMA_tcrSignature hH).double hcap₁⟩

/-- **Stateless many-time EUF-CMA signatures from one-way functions and target collision-resistant
hash families** ([NaorYung1989], Section 4; [BonehShoup2023], Sections 13.2.1 and 14.6): any
one-way function and any unrestricted target collision-resistant `KeyedHashFamily` yield a
stateless many-time `SignatureScheme` satisfying `EUFCMA`. -/
theorem OneWay.exists_eufCMA_of_targetCollisionResistant
    {f : List Bool → List Bool} (hf : OneWay f)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    ∃ M : SignatureScheme, M.EUFCMA := by
  obtain ⟨S, hcapS, hS⟩ := hf.exists_indexedEUFCMA_of_targetCollisionResistant hH
  exact hS.exists_eufCMA_of_oneWay (fun n => by rw [hcapS n]) hf

/-- **Naor–Yung signature theorem** ([NaorYung1989], Theorem 2 / Section 4): every one-way
permutation implies the existence of a stateless many-time `EUFCMA`-secure digital signature
scheme, with no separate hash-family assumption. -/
theorem OneWayPermutation.exists_eufCMA
    {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    ∃ M : SignatureScheme, M.EUFCMA := by
  obtain ⟨H, hH⟩ := hf.exists_targetCollisionResistant_keyedHashFamily
  exact hf.oneWay.exists_eufCMA_of_targetCollisionResistant hH

end Cslib.Crypto
