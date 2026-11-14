/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Security
public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
public import CslibFrontier.Computability.Probabilistic.Memoize
public import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Mathlib.Data.FinEnum
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The certified IND-CPA reduction of the word-level Fujisaki–Okamoto family

The IND-CCA bounds of `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot` and `…Bot`
reduce to the two-stage IND-CPA advantage of one explicit adversary,
`Scheme.romFilterCpaReduction`. This module gives that reduction for the word-level family
`WordPKE` of `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word` as a chosen-message
adversary of `Encryption.gameOn`, and proves that it is uniform strict PPT whenever the adversary
it wraps is uniform strict oracle PPT.

**Adversaries.** A word-level ROM IND-CCA adversary is a program
`A : ℕ → List Bool → WordOracleComp CCAOp Bool`. At parameter `n` it receives the challenge word
`Encryption.encKEMChallenge (pk, k*, c*)`, the layout of the word-level KEM distinguishers of
`Encryption.KEMINDCPA`, and calls the oracles `G`, `H` and decapsulation (`CCAOp`). Its efficiency
is `IsOraclePPT encBool A`.

**The simulator.** `WordPKE.simFilterWordHandler d` answers the adversary without the secret key.
A request in the domain is answered by the typed keyless simulator `Scheme.simFilterHandler` of
the bundle `WordPKE.scheme P keyLen n`, on the same state `SimState`; a decapsulation answer is
encoded with `encOption encBits`. The domain is: messages of length `msgLen n` for `G`; for `H`,
the canonical encodings `encHQuery (b, m, c)` of a message `m` of length `msgLen n` and a
ciphertext `c` of length at most `ctLen n` (`WordPKE.isHQuery`); and ciphertexts of length at most
`ctLen n` for decapsulation. Any other request gets the empty reply and leaves the state
unchanged. The filter `d pk gCache c` decides which decapsulation queries are answered; every
query is answered for `FO-notbot` (`WordPKE.romCpaReductionWord`).

**The reduction.** `WordPKE.romFilterCpaReductionWord d A` mirrors
`Scheme.romFilterCpaReduction`. Its first stage draws `m₀, m₁` uniformly of length `msgLen n` and
saves the public key with `m₁`. Its second stage draws the challenge key `k*` of length `keyLen n`,
runs `A` against the simulator from empty caches (`WordPKE.simFilterWordHit`) and reports whether
`m₁` was queried to `G`.

**The certificate.** `WordPKE.IsEfficient.isPPT_romFilterCpaReductionWord` derives
`Encryption.AdversaryOf.IsPPT` of the reduction from `IsOraclePPT encBool A`, the efficiency of
the PKE family (`WordPKE.IsEfficient`), a polynomial-time key length and a polynomial-time filter.
The simulator is substituted into `A` with `IsOraclePPT.run_interpret_preprocess'`. Each call is
strict PPT in the full state (`WordPKE.IsEfficient.isPPTOn_simFilterWordHandler`), keeps every
cached value at most `coinLen n + keyLen n` bits long, and adds at most a polynomial in the
request length and `n` to the encoded state.

Relating the advantage of this reduction to the typed `cpaAdvantage` of `Scheme.romCpaReduction`
on a typed view of `A`, and the asymptotic IND-CCA theorem, are later steps of #5293.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.CCAOp`: the oracle operations of an adversary.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.encSimState`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.encSimCall`: the encodings of the simulator state and of
  one simulator call.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.hQueryDecoder`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.isHQuery`: decoding and the domain of `H`
  requests.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.simFilterWordHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.simFilterWordHit`: the native keyless simulator
  and its run on a challenge.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.romFilterCpaReductionWord`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.romCpaReductionWord`: the native IND-CPA
  reduction, and its `FO-notbot` instance.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.computableInPolyTime_isHQuery`: the
  `H` domain test is polynomial-time.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPTOn_simFilterWordHandler`: one
  simulator call is uniform strict PPT.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPT_romFilterCpaReductionWord`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPT_romCpaReductionWord`: the
  reduction is uniform strict PPT whenever the adversary is uniform strict oracle PPT.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021); the simulator and reduction are those of
  `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Security`, which documents their relation
  to the source.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability Turing.MultiTapeTM

/-- Oracle operations of a word-level ROM IND-CCA adversary against an FO key encapsulation
mechanism: the random oracles `G` and `H`, and decapsulation. -/
inductive CCAOp where
  /-- Query the coin-derivation oracle `G`. -/
  | G
  /-- Query the key-derivation oracle `H`. -/
  | H
  /-- Query the decapsulation oracle. -/
  | decaps
  deriving DecidableEq

instance : FinEnum CCAOp := FinEnum.ofList [.G, .H, .decaps] (by intro x; cases x <;> simp)

/-- The state of the native keyless simulator: the caches of `SimState` over words, each an
association list. -/
enc_structure encSimState : SimState (List Bool) (List Bool) (List Bool) (List Bool) where
  gCache : (encMemoCache encBits encBits), hCache : (encMemoCache encHQuery encBits),
  hqCache : (encMemoCache encBits encBits)

/-- The input `((1ⁿ, pk, cStar), (op, w), st)` of one call of the native simulator: the
parameter, the public key and the challenge ciphertext, then the request and the simulator
state. -/
abbrev encSimCall : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) ×
    SimState (List Bool) (List Bool) (List Bool) (List Bool) ↪ List Bool :=
  encHandlerCall (encPair encUnary (encPair encBits encBits)) (encFinEnum CCAOp) encSimState

/-- The total decoder of `H` requests. -/
def hQueryDecoder : Decoder encHQuery := Decoder.bool.pair (Decoder.bits.pair Decoder.bits)

namespace WordPKE

variable (P : WordPKE) (keyLen : ℕ → ℕ)

/-- Whether the `H` request `w` is in the domain at parameter `n`: it is the canonical encoding
of a triple `(b, m, c)` with `m` of length `msgLen n` and `c` of length at most `ctLen n`. -/
def isHQuery (n : ℕ) (w : List Bool) : Bool :=
  match hQueryDecoder.decode w with
  | (b, m, c) =>
    encHQuery (b, m, c) == w && m.length == P.msgLen n && decide (c.length ≤ P.ctLen n)

/-- The native keyless simulator with decapsulation filter `d` at parameter `n`, for public key
`pk` and challenge ciphertext `cStar`. A request in the domain is answered by the typed simulator
`Scheme.simFilterHandler` of the bundle `scheme P keyLen n`, on the same state; a decapsulation
answer is encoded with `encOption encBits`. A request outside the domain gets the empty reply and
leaves the state unchanged: a `G` request that is not a message of length `msgLen n`, an `H`
request that fails `isHQuery`, and a decapsulation request longer than `ctLen n`. -/
noncomputable def simFilterWordHandler
    (d : List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (n : ℕ) (pk cStar : List Bool) (request : CCAOp × List Bool) :
    StateT (SimState (List Bool) (List Bool) (List Bool) (List Bool)) ProbComp (List Bool) :=
  fun st => match request with
  | (.G, m) =>
    if m.length = P.msgLen n then (P.scheme keyLen n).simFilterHandler (d pk) pk cStar (.G m) st
    else pure ([], st)
  | (.H, w) =>
    if P.isHQuery n w then
      (P.scheme keyLen n).simFilterHandler (d pk) pk cStar (.H (hQueryDecoder.decode w)) st
    else pure ([], st)
  | (.decaps, c) =>
    if c.length ≤ P.ctLen n then
      (fun (k, st') => (encOption encBits k, st')) <$>
        (P.scheme keyLen n).simFilterHandler (d pk) pk cStar (.decaps c) st
    else pure ([], st)

/-- The native keyless simulator run inside the reduction: draw nothing, run the word adversary
`A` at parameter `n` on the challenge `(pk, kStar, cStar)` against `simFilterWordHandler d` from
empty caches, and report whether the target `m` was queried to `G`. -/
noncomputable def simFilterWordHit
    (d : List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (A : ℕ → List Bool → WordOracleComp CCAOp Bool) (n : ℕ) (pk m cStar kStar : List Bool) :
    ProbComp Bool := do
  let (_, st) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (P.simFilterWordHandler keyLen d n pk cStar))
    (A n (Encryption.encKEMChallenge (pk, kStar, cStar)))).run {}
  return (st.gCache.lookup m).isSome

/-- **The native IND-CPA reduction** of the FO proofs with decapsulation filter `d`, for a word
adversary `A`, as a chosen-message adversary of `Encryption.gameOn`. The first stage draws both
challenge messages of length `msgLen n` and saves the public key with `m₁`. The second stage
draws the challenge key `kStar` of length `keyLen n` and runs `simFilterWordHit`, which reports
whether `m₁` was queried to `G`. It is the word-level counterpart of
`Scheme.romFilterCpaReduction`. -/
noncomputable def romFilterCpaReductionWord
    (d : List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (A : ℕ → List Bool → WordOracleComp CCAOp Bool) : Encryption.AdversaryOf (List Bool) where
  choose n pk := do
    let m₀ ← BitString.sampleList (P.msgLen n)
    let m₁ ← BitString.sampleList (P.msgLen n)
    return ((m₀, m₁), encPair encBits encBits (pk, m₁))
  guess n state cStar := do
    let kStar ← BitString.sampleList (keyLen n)
    let (pk, m₁) := (Decoder.bits.pair Decoder.bits).decode state
    P.simFilterWordHit keyLen d A n pk m₁ cStar kStar

/-- **The native IND-CPA reduction for `FO-notbot`**: `romFilterCpaReductionWord` with every
decapsulation query answered, the word-level counterpart of `Scheme.romCpaReduction`. -/
noncomputable def romCpaReductionWord (A : ℕ → List Bool → WordOracleComp CCAOp Bool) :
    Encryption.AdversaryOf (List Bool) :=
  P.romFilterCpaReductionWord keyLen (fun _ _ _ => true) A

/-- The domain test of `H` requests is polynomial-time on `(1ⁿ, w)`. -/
theorem IsEfficient.computableInPolyTime_isHQuery {P : WordPKE} (hP : P.IsEfficient) :
    ComputableInPolyTime (fun (n, w) => P.isHQuery n w) (encPair encUnary encBits) encBool := by
  have hdec : ComputableInPolyTime (fun x : ℕ × List Bool => hQueryDecoder.decode x.2)
      (encPair encUnary encBits) encHQuery :=
    hQueryDecoder.computableInPolyTime.comp (ComputableInPolyTime.snd _ _)
  have hcanon : ComputableInPolyTime
      (fun x : ℕ × List Bool => encHQuery (hQueryDecoder.decode x.2) == x.2)
      (encPair encUnary encBits) encBool :=
    ComputableInPolyTime.beq hdec.encoding_comp (ComputableInPolyTime.snd _ _)
  have hmsg : ComputableInPolyTime
      (fun x : ℕ × List Bool => (hQueryDecoder.decode x.2).2.1.length == P.msgLen x.1)
      (encPair encUnary encBits) encBool :=
    ComputableInPolyTime.beq (ComputableInPolyTime.length_bits.comp hdec.snd'.fst')
      (hP.msgLen.comp (ComputableInPolyTime.fst _ _))
  have hct : ComputableInPolyTime
      (fun x : ℕ × List Bool => decide ((hQueryDecoder.decode x.2).2.2.length ≤ P.ctLen x.1))
      (encPair encUnary encBits) encBool :=
    ComputableInPolyTime.unary_le' (ComputableInPolyTime.length_bits.comp hdec.snd'.snd')
      (hP.ctLen.comp (ComputableInPolyTime.fst _ _))
  exact (ComputableTidilyInPolyTime.bool_and' (ComputableTidilyInPolyTime.bool_and' hcanon.tidy
    hmsg.tidy) hct.tidy).computableInPolyTime

/-! ### Certificates -/

section Certificates

/-- A lazily sampled cache inside the simulator state is uniform strict PPT: one `memoize` call
on the cache selected by `get`, drawing a word of length `len`, written back by `set`. -/
private theorem isPPTOn_zoomMemoize {Key : Type} [DecidableEq Key]
    {keyEncoding : Key ↪ List Bool}
    (get : SimState (List Bool) (List Bool) (List Bool) (List Bool) → List (Key × List Bool))
    (set : SimState (List Bool) (List Bool) (List Bool) (List Bool) → List (Key × List Bool) →
      SimState (List Bool) (List Bool) (List Bool) (List Bool))
    (hget : ComputableInPolyTime get encSimState (encMemoCache keyEncoding encBits))
    (hset : ComputableInPolyTime (fun p : SimState (List Bool) (List Bool) (List Bool) (List Bool) ×
        List (Key × List Bool) => set p.1 p.2)
      (encPair encSimState (encMemoCache keyEncoding encBits)) encSimState)
    {α : Type} {input : α ↪ List Bool} {len : α → ℕ} {key : α → Key}
    {st : α → SimState (List Bool) (List Bool) (List Bool) (List Bool)}
    (hlen : ComputableInPolyTime len input encUnary)
    (hkey : ComputableInPolyTime key input keyEncoding)
    (hst : ComputableInPolyTime st input encSimState) :
    IsPPTOn input (encPair encBits encSimState) (fun a =>
      RandomOracle.zoomStateT get set (memoize (fun _ => BitString.sampleList (len a)) (key a))
        (st a)) := by
  have hmemo := IsPPTOn.memoize (compute := fun a _ => BitString.sampleList (len a))
    (query := key) (cache := fun a => get (st a)) hlen.sampleList hkey (hget.comp hst)
  have hpost : ComputableInPolyTime
      (fun p : α × (List Bool × List (Key × List Bool)) => (p.2.1, set (st p.1) p.2.2))
      (encPair input (encPair encBits (encMemoCache keyEncoding encBits)))
      (encPair encBits encSimState) :=
    (ComputableInPolyTime.snd _ _).fst'.prod
      (hset.comp ((hst.comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _).snd'))
  refine (hmemo.map_with (f := fun a p => (p.1, set (st a) p.2)) hpost).congr fun a => ?_
  simp [RandomOracle.zoomStateT, bind_pure_comp]

/-- The simulator state `SimState` over words. -/
local notation "WState" => SimState (List Bool) (List Bool) (List Bool) (List Bool)

private theorem isPPTOn_simHashG {α : Type} {input : α ↪ List Bool} {len : α → ℕ}
    {m : α → List Bool} {st : α → WState}
    (hlen : ComputableInPolyTime len input encUnary) (hm : ComputableInPolyTime m input encBits)
    (hst : ComputableInPolyTime st input encSimState) :
    IsPPTOn input (encPair encBits encSimState)
      (fun a => simHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (len a)) (m a)
        (st a)) := by
  unfold simHashG
  exact isPPTOn_zoomMemoize (fun st => st.gCache) (fun st c => { st with gCache := c })
    (by fun_prop) (by fun_prop) hlen hm hst

private theorem isPPTOn_simHashHq {α : Type} {input : α ↪ List Bool} {len : α → ℕ}
    {c : α → List Bool} {st : α → WState}
    (hlen : ComputableInPolyTime len input encUnary) (hc : ComputableInPolyTime c input encBits)
    (hst : ComputableInPolyTime st input encSimState) :
    IsPPTOn input (encPair encBits encSimState)
      (fun a => simHashHq (M := List Bool) (R := List Bool) (BitString.sampleList (len a)) (c a)
        (st a)) := by
  unfold simHashHq
  exact isPPTOn_zoomMemoize SimState.hqCache (fun st c' => { st with hqCache := c' })
    (by fun_prop) (by fun_prop) hlen hc hst

private theorem isPPTOn_simHashHRaw {α : Type} {input : α ↪ List Bool} {len : α → ℕ}
    {x : α → Bool × List Bool × List Bool} {st : α → WState}
    (hlen : ComputableInPolyTime len input encUnary) (hx : ComputableInPolyTime x input encHQuery)
    (hst : ComputableInPolyTime st input encSimState) :
    IsPPTOn input (encPair encBits encSimState)
      (fun a => simHashHRaw (R := List Bool) (BitString.sampleList (len a)) (x a) (st a)) := by
  unfold simHashHRaw
  exact isPPTOn_zoomMemoize (fun st => st.hCache) (fun st c => { st with hCache := c })
    (by fun_prop) (by fun_prop) hlen hx hst

/-- The simulator call on `x = ((n, pk, cStar), (op, w), st)` with every branch made explicit, for
the runtime certificate. -/
private noncomputable def simCallExplicit (P : WordPKE) (keyLen : ℕ → ℕ)
    (d : List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState) :
    ProbComp (List Bool × WState) :=
  if x.2.1.1 = .G then
    if x.2.1.2.length = P.msgLen x.1.1 then
      simHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (P.coinLen x.1.1))
        x.2.1.2 x.2.2
    else pure ([], x.2.2)
  else if x.2.1.1 = .H then
    if P.isHQuery x.1.1 x.2.1.2 then
      if (hQueryDecoder.decode x.2.1.2).1 then
        simHashHRaw (R := List Bool) (BitString.sampleList (keyLen x.1.1))
          (true, (hQueryDecoder.decode x.2.1.2).2.1, (hQueryDecoder.decode x.2.1.2).2.2) x.2.2
      else do
        let (r, st₁) ← simHashG (CT := List Bool) (K := List Bool)
          (BitString.sampleList (P.coinLen x.1.1)) (hQueryDecoder.decode x.2.1.2).2.1 x.2.2
        if P.encDet x.1.1 x.1.2.1 (hQueryDecoder.decode x.2.1.2).2.1 r =
            (hQueryDecoder.decode x.2.1.2).2.2 then
          simHashHq (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen x.1.1))
            (hQueryDecoder.decode x.2.1.2).2.2 st₁
        else
          simHashHRaw (R := List Bool) (BitString.sampleList (keyLen x.1.1))
            (false, (hQueryDecoder.decode x.2.1.2).2.1, (hQueryDecoder.decode x.2.1.2).2.2) st₁
    else pure ([], x.2.2)
  else
    if x.2.1.2.length ≤ P.ctLen x.1.1 then
      if x.2.1.2 = x.1.2.2 then pure (encOption encBits none, x.2.2)
      else if d x.1.2.1 x.2.2.gCache x.2.1.2 then
        (fun p => (encOption encBits (some p.1), p.2)) <$>
          simHashHq (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen x.1.1))
            x.2.1.2 x.2.2
      else pure (encOption encBits none, x.2.2)
    else pure ([], x.2.2)

private theorem stateT_bind_apply {σ α β : Type} (x : StateT σ ProbComp α)
    (f : α → StateT σ ProbComp β) (s : σ) : (x >>= f) s = x s >>= fun p => f p.1 p.2 :=
  StateT.run_bind x f s

private theorem stateT_pure_apply {σ α : Type} (a : α) (s : σ) :
    (pure a : StateT σ ProbComp α) s = pure (a, s) :=
  rfl

private theorem simFilterWordHandler_eq_explicit (P : WordPKE) (keyLen : ℕ → ℕ)
    (d : List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState) :
    P.simFilterWordHandler keyLen d x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2 =
      simCallExplicit P keyLen d x := by
  obtain ⟨⟨n, pk, cStar⟩, ⟨op, w⟩, st⟩ := x
  cases op
  · rfl
  · simp only [simFilterWordHandler, simCallExplicit, reduceCtorEq, ↓reduceIte]
    by_cases hq : P.isHQuery n w = true
    · simp only [hq, ↓reduceIte, Scheme.simFilterHandler, Scheme.simFilterDispatch,
        ROQuery.dispatch]
      generalize hQueryDecoder.decode w = y
      obtain ⟨b, m, c⟩ := y
      cases b
      · simp only [Scheme.simHashH, stateT_bind_apply, Bool.false_eq_true, ↓reduceIte, scheme,
          toExplicitCoin]
        congr 1 with p
        by_cases h : P.encDet n pk m p.1 = c <;> simp only [h, ↓reduceIte]
      · rfl
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
  · simp only [simFilterWordHandler, simCallExplicit, reduceCtorEq, ↓reduceIte]
    by_cases hl : w.length ≤ P.ctLen n
    · simp only [hl, ↓reduceIte, Scheme.simFilterHandler, Scheme.simFilterDispatch,
        ROQuery.dispatch]
      by_cases hc : w = cStar
      · simp only [hc, ↓reduceIte]
        rfl
      · simp only [hc, ↓reduceIte, filterDecaps]
        cases d pk st.gCache w
        · rfl
        · simp only [Bool.cond_true, ↓reduceIte, stateT_bind_apply, stateT_pure_apply,
            bind_pure_comp, Functor.map_map]
          rfl
    · simp only [hl, ↓reduceIte]

/-- The native simulator is uniform strict PPT on one call `((1ⁿ, pk, cStar), (op, w), st)`,
charging the complete state, whenever the PKE family and the decapsulation filter are
efficient. -/
theorem IsEfficient.isPPTOn_simFilterWordHandler {P : WordPKE} (hP : P.IsEfficient)
    {keyLen : ℕ → ℕ} (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {d : List Bool → List (List Bool × List Bool) → List Bool → Bool}
    (hd : ComputableInPolyTime (fun (pk, cache, c) => d pk cache c)
      (encPair encBits (encPair (encMemoCache encBits encBits) encBits)) encBool) :
    IsPPTOn encSimCall (encPair encBits encSimState)
      (fun ((n, pk, cStar), request, st) =>
        P.simFilterWordHandler keyLen d n pk cStar request st) := by
  change IsPPTOn encSimCall (encPair encBits encSimState)
    (fun x => P.simFilterWordHandler keyLen d x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2)
  have hn : ComputableInPolyTime
      (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState => x.1.1)
      encSimCall encUnary := by fun_prop
  have hpk : ComputableInPolyTime
      (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState => x.1.2.1)
      encSimCall encBits := by fun_prop
  have hcs : ComputableInPolyTime
      (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState => x.1.2.2)
      encSimCall encBits := by fun_prop
  have hop : ComputableInPolyTime
      (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState => x.2.1.1)
      encSimCall (encFinEnum CCAOp) := by fun_prop
  have hw : ComputableInPolyTime
      (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState => x.2.1.2)
      encSimCall encBits := by fun_prop
  have hst : ComputableInPolyTime
      (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState => x.2.2)
      encSimCall encSimState := by fun_prop
  have hdec : ComputableInPolyTime
      (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState =>
        hQueryDecoder.decode x.2.1.2) encSimCall encHQuery :=
    hQueryDecoder.computableInPolyTime.comp hw
  have hreject : IsPPTOn encSimCall (encPair encBits encSimState)
      (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState =>
        pure (([] : List Bool), x.2.2)) :=
    ((ComputableInPolyTime.const ([] : List Bool)).prod hst).isPPTOn
  -- `G` requests
  have hG := IsPPTOn.ite'
    (condition := fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState =>
      x.2.1.2.length = P.msgLen x.1.1)
    (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.length_bits.comp hw)
      (hP.msgLen.comp hn))
    (isPPTOn_simHashG (hP.coinLen.comp hn) hw hst) hreject
  -- `H` requests
  have hraw := isPPTOn_simHashHRaw (x := fun x => (true, (hQueryDecoder.decode x.2.1.2).2.1,
      (hQueryDecoder.decode x.2.1.2).2.2)) (hkeyLen.comp hn)
    ((ComputableInPolyTime.const true).prod hdec.snd') hst
  let Q := encPair encSimCall (encPair encBits encSimState)
  have hfst : ComputableInPolyTime
      (fun q : ((ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState) ×
        (List Bool × WState) => q.1) Q encSimCall := ComputableInPolyTime.fst _ _
  have hcheck : ComputableInPolyTime
      (fun q : ((ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState) ×
        (List Bool × WState) =>
        decide (P.encDet q.1.1.1 q.1.1.2.1 (hQueryDecoder.decode q.1.2.1.2).2.1 q.2.1 =
          (hQueryDecoder.decode q.1.2.1.2).2.2)) Q encBool :=
    ComputableInPolyTime.decide_eq' (hP.encDet.comp ((hn.comp hfst).prod ((hpk.comp hfst).prod
      ((hdec.snd'.fst'.comp hfst).prod (ComputableInPolyTime.snd _ _).fst'))))
      (hdec.snd'.snd'.comp hfst)
  have hafter := IsPPTOn.ite' hcheck
    (isPPTOn_simHashHq (hkeyLen.comp (hn.comp hfst)) (hdec.snd'.snd'.comp hfst)
      (ComputableInPolyTime.snd _ _).snd')
    (isPPTOn_simHashHRaw (hkeyLen.comp (hn.comp hfst))
      ((ComputableInPolyTime.const false).prod (hdec.snd'.comp hfst))
      (ComputableInPolyTime.snd _ _).snd')
  have hfalse := IsPPTOn.bind_with
    (first := fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState =>
      simHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (P.coinLen x.1.1))
        (hQueryDecoder.decode x.2.1.2).2.1 x.2.2)
    (second := fun x p =>
      if P.encDet x.1.1 x.1.2.1 (hQueryDecoder.decode x.2.1.2).2.1 p.1 =
          (hQueryDecoder.decode x.2.1.2).2.2 then
        simHashHq (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen x.1.1))
          (hQueryDecoder.decode x.2.1.2).2.2 p.2
      else
        simHashHRaw (R := List Bool) (BitString.sampleList (keyLen x.1.1))
          (false, (hQueryDecoder.decode x.2.1.2).2.1, (hQueryDecoder.decode x.2.1.2).2.2) p.2)
    (isPPTOn_simHashG (hP.coinLen.comp hn) hdec.snd'.fst' hst) hafter
  have hH := IsPPTOn.cond' (hP.computableInPolyTime_isHQuery.comp (hn.prod hw))
    (IsPPTOn.cond' hdec.fst' hraw hfalse) hreject
  -- decapsulation requests
  have hnone : IsPPTOn encSimCall (encPair encBits encSimState)
      (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState =>
        pure (encOption encBits none, x.2.2)) :=
    ((ComputableInPolyTime.const (encOption encBits none)).prod hst).isPPTOn
  have hsome : ComputableInPolyTime (fun p : List Bool × WState => some p.1)
      (encPair encBits encSimState) (encOption encBits) := by fun_prop
  have hkey := (isPPTOn_simHashHq (hkeyLen.comp hn) hw hst).map
    (f := fun p => (encOption encBits (some p.1), p.2))
    (hsome.encoding_comp.prod (ComputableInPolyTime.snd _ _))
  have hD := IsPPTOn.ite'
    (condition := fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState =>
      x.2.1.2.length ≤ P.ctLen x.1.1)
    (ComputableInPolyTime.unary_le' (ComputableInPolyTime.length_bits.comp hw)
      (hP.ctLen.comp hn))
    (IsPPTOn.ite' (ComputableInPolyTime.decide_eq' hw hcs) hnone
      (IsPPTOn.cond' (hd.comp (hpk.prod ((by fun_prop : ComputableInPolyTime
        (fun x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState => x.2.2.gCache)
        encSimCall (encMemoCache encBits encBits)).prod hw))) hkey hnone)) hreject
  have hall := IsPPTOn.ite' (ComputableInPolyTime.decide_eq' hop
      (ComputableInPolyTime.const CCAOp.G)) hG
    (IsPPTOn.ite' (ComputableInPolyTime.decide_eq' hop (ComputableInPolyTime.const CCAOp.H))
      hH hD)
  refine hall.congr fun x => ?_
  rw [simFilterWordHandler_eq_explicit]
  rfl

/-! ### Resource bounds of one simulator call -/

/-- Every value cached by the simulator has length at most `V`. -/
private def CachesBounded (V : ℕ) (st : WState) : Prop :=
  (∀ e ∈ st.gCache, e.2.length ≤ V) ∧ (∀ e ∈ st.hCache, e.2.length ≤ V) ∧
    ∀ e ∈ st.hqCache, e.2.length ≤ V

/-- One cached draw of a word of length `len ≤ V`: the reply has length at most `V`, and the new
cache keeps the bound and grows by at most one entry. -/
private theorem zoomMemoize_support {Key : Type} [DecidableEq Key] (keyEncoding : Key ↪ List Bool)
    (get : WState → List (Key × List Bool)) (set : WState → List (Key × List Bool) → WState)
    {len V : ℕ} (hlen : len ≤ V) (key : Key) (st : WState)
    (hcache : ∀ e ∈ get st, e.2.length ≤ V) (result : List Bool × WState)
    (hresult : result ∈ (ProbComp.eval (RandomOracle.zoomStateT get set
      (memoize (fun _ => BitString.sampleList len) key) st)).support) :
    result.1.length ≤ V ∧ ∃ c', result.2 = set st c' ∧ (∀ e ∈ c', e.2.length ≤ V) ∧
      (encMemoCache keyEncoding encBits c').length ≤
        (encMemoCache keyEncoding encBits (get st)).length + 4 * (keyEncoding key).length +
          2 * V + 3 := by
  rw [RandomOracle.eval_zoomStateT_memoize] at hresult
  obtain ⟨⟨v, c'⟩, hmem, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
  obtain ⟨hreply, hcache', hgrowth⟩ := memoize_call_size_le keyEncoding encBits
    (fun _ => ProbComp.eval (BitString.sampleList len)) key (get st) V
    (by simpa only [encBits_apply] using hcache) (fun value hvalue => by
      rw [BitString.eval_sampleList] at hvalue
      simpa only [encBits_apply, BitString.length_of_mem_support_uniformList hvalue] using hlen)
    (v, c') hmem
  exact ⟨by simpa only [encBits_apply] using hreply, c', rfl,
    by simpa only [encBits_apply] using hcache', hgrowth⟩

private theorem length_encSimState (st : WState) :
    (encSimState st).length = 2 * (encMemoCache encBits encBits st.gCache).length +
      2 * (encMemoCache encHQuery encBits st.hCache).length +
        (encMemoCache encBits encBits st.hqCache).length + 2 := by
  simp only [encSimState_apply, encSimStateFields, length_encPair]
  ring

private theorem length_encHQuery (b : Bool) (m c : List Bool) :
    (encHQuery (b, m, c)).length = 2 * m.length + c.length + 4 := by
  simp only [length_encPair, encBool_apply, List.length_singleton, encBits_apply]
  ring

/-- A request in the `H` domain bounds the lengths of its message and ciphertext. -/
private theorem length_le_of_isHQuery {P : WordPKE} {n : ℕ} {w : List Bool}
    (h : P.isHQuery n w = true) :
    2 * (hQueryDecoder.decode w).2.1.length + (hQueryDecoder.decode w).2.2.length + 4 =
      w.length := by
  unfold isHQuery at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hlen := congrArg List.length h.1.1
  rw [length_encHQuery] at hlen
  exact hlen

/-- One call of the simulator keeps every cached value of length at most `V`, replies with at most
`V + 1` bits, and adds at most `16 |w| + 8 V + 12` bits of encoded state for a request word `w`,
when coins and keys have length at most `V`. -/
private theorem simCallExplicit_support (P : WordPKE) (keyLen : ℕ → ℕ)
    (d : List Bool → List (List Bool × List Bool) → List Bool → Bool) {V : ℕ}
    (x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState)
    (hcoin : P.coinLen x.1.1 ≤ V) (hkey : keyLen x.1.1 ≤ V) (hinv : CachesBounded V x.2.2)
    (result : List Bool × WState)
    (hresult : result ∈ (ProbComp.eval (simCallExplicit P keyLen d x)).support) :
    CachesBounded V result.2 ∧ result.1.length ≤ V + 1 ∧
      (encSimState result.2).length ≤
        (encSimState x.2.2).length + 16 * x.2.1.2.length + 8 * V + 12 := by
  obtain ⟨⟨n, pk, cStar⟩, ⟨op, w⟩, st⟩ := x
  obtain ⟨hg, hh, hq⟩ := hinv
  -- the three cached draws
  have stepG (m : List Bool) (st₀ : WState) (h₀ : CachesBounded V st₀) (r : List Bool × WState)
      (hr : r ∈ (ProbComp.eval (simHashG (CT := List Bool) (K := List Bool)
        (BitString.sampleList (P.coinLen n)) m st₀)).support) :
      CachesBounded V r.2 ∧ r.1.length ≤ V ∧
        (encSimState r.2).length ≤ (encSimState st₀).length + 8 * m.length + 4 * V + 6 := by
    unfold simHashG at hr
    obtain ⟨hreply, c', hnext, hc', hlen⟩ := zoomMemoize_support encBits (fun st => st.gCache)
      (fun st c => { st with gCache := c }) hcoin m st₀ h₀.1 r hr
    refine ⟨?_, hreply, ?_⟩
    · rw [hnext]; exact ⟨hc', h₀.2⟩
    · rw [hnext, length_encSimState, length_encSimState]
      simp only [encBits_apply] at hlen
      lia
  have stepHq (c : List Bool) (st₀ : WState) (h₀ : CachesBounded V st₀) (r : List Bool × WState)
      (hr : r ∈ (ProbComp.eval (simHashHq (M := List Bool) (R := List Bool)
        (BitString.sampleList (keyLen n)) c st₀)).support) :
      CachesBounded V r.2 ∧ r.1.length ≤ V ∧
        (encSimState r.2).length ≤ (encSimState st₀).length + 4 * c.length + 2 * V + 3 := by
    unfold simHashHq at hr
    obtain ⟨hreply, c', hnext, hc', hlen⟩ := zoomMemoize_support encBits SimState.hqCache
      (fun st c' => { st with hqCache := c' }) hkey c st₀ h₀.2.2 r hr
    refine ⟨?_, hreply, ?_⟩
    · rw [hnext]; exact ⟨h₀.1, h₀.2.1, hc'⟩
    · rw [hnext, length_encSimState, length_encSimState]
      simp only [encBits_apply] at hlen
      lia
  have stepHRaw (y : Bool × List Bool × List Bool) (st₀ : WState) (h₀ : CachesBounded V st₀)
      (r : List Bool × WState)
      (hr : r ∈ (ProbComp.eval (simHashHRaw (R := List Bool)
        (BitString.sampleList (keyLen n)) y st₀)).support) :
      CachesBounded V r.2 ∧ r.1.length ≤ V ∧
        (encSimState r.2).length ≤
          (encSimState st₀).length + 8 * (encHQuery y).length + 4 * V + 6 := by
    unfold simHashHRaw at hr
    obtain ⟨hreply, c', hnext, hc', hlen⟩ := zoomMemoize_support encHQuery (fun st => st.hCache)
      (fun st c => { st with hCache := c }) hkey y st₀ h₀.2.1 r hr
    refine ⟨?_, hreply, ?_⟩
    · rw [hnext]; exact ⟨h₀.1, hc', h₀.2.2⟩
    · rw [hnext, length_encSimState, length_encSimState]
      lia
  have hinv : CachesBounded V st := ⟨hg, hh, hq⟩
  have hpure (v : List Bool) (hv : v.length ≤ V + 1)
      (hr : result ∈ (ProbComp.eval (pure (v, st) : ProbComp (List Bool × WState))).support) :
      CachesBounded V result.2 ∧ result.1.length ≤ V + 1 ∧
        (encSimState result.2).length ≤ (encSimState st).length + 16 * w.length + 8 * V + 12 := by
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hr
    subst hr
    exact ⟨hinv, hv, by lia⟩
  cases op
  · simp only [simCallExplicit, ↓reduceIte] at hresult ⊢
    split_ifs at hresult
    · obtain ⟨h₁, h₂, h₃⟩ := stepG w st hinv result hresult
      exact ⟨h₁, by lia, by lia⟩
    · exact hpure [] (by simp) hresult
  · simp only [simCallExplicit, reduceCtorEq, ↓reduceIte] at hresult ⊢
    split_ifs at hresult with hvalid htag
    · have hw := length_le_of_isHQuery hvalid
      obtain ⟨h₁, h₂, h₃⟩ := stepHRaw _ st hinv result hresult
      refine ⟨h₁, by lia, ?_⟩
      rw [length_encHQuery] at h₃
      lia
    · have hw := length_le_of_isHQuery hvalid
      rw [ProbComp.eval_bind] at hresult
      obtain ⟨r, hr, hresult⟩ := (PMF.mem_support_bind_iff _ _ _).mp hresult
      obtain ⟨h₁, -, h₃⟩ := stepG _ st hinv r hr
      split_ifs at hresult
      · obtain ⟨h₄, h₅, h₆⟩ := stepHq _ r.2 h₁ result hresult
        exact ⟨h₄, by lia, by lia⟩
      · obtain ⟨h₄, h₅, h₆⟩ := stepHRaw _ r.2 h₁ result hresult
        rw [length_encHQuery] at h₆
        exact ⟨h₄, by lia, by lia⟩
    · exact hpure [] (by simp) hresult
  · simp only [simCallExplicit, reduceCtorEq, ↓reduceIte] at hresult ⊢
    split_ifs at hresult
    · exact hpure _ (by simp) hresult
    · rw [ProbComp.eval_map] at hresult
      obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      obtain ⟨h₁, h₂, h₃⟩ := stepHq w st hinv r hr
      refine ⟨h₁, ?_, by lia⟩
      simp only [encOption_some, List.length_cons, encBits_apply]
      lia
    · exact hpure _ (by simp) hresult
    · exact hpure [] (by simp) hresult

private theorem lookup_isSome_eq_any (m : List Bool) (cache : List (List Bool × List Bool)) :
    (cache.lookup m).isSome = cache.any fun e => e.1 == m := by
  induction cache with
  | nil => rfl
  | cons e cache ih =>
    obtain ⟨k, v⟩ := e
    by_cases h : m = k
    · subst h; simp [List.lookup]
    · simp [List.lookup, beq_eq_false_iff_ne.mpr h, ih, Ne.symm h]

/-- The guessing stage of the reduction after its key draw, on `((n, state, cStar), kStar)`. -/
private abbrev encGuessKey : (ℕ × List Bool × List Bool) × List Bool ↪ List Bool :=
  encPair Encryption.encGuessInput encBits

/-- **The reduction is uniform strict PPT.** For an efficient PKE family, a polynomial-time key
length and an efficient decapsulation filter, the word-level IND-CPA reduction of every
uniform strict oracle PPT ROM IND-CCA adversary is a uniform strict PPT chosen-message adversary.
The certificate covers the lazy `G`/`H` simulation and the simulated decapsulation oracle. -/
theorem IsEfficient.isPPT_romFilterCpaReductionWord {P : WordPKE} (hP : P.IsEfficient)
    {keyLen : ℕ → ℕ} (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {d : List Bool → List (List Bool × List Bool) → List Bool → Bool}
    (hd : ComputableInPolyTime (fun (pk, cache, c) => d pk cache c)
      (encPair encBits (encPair (encMemoCache encBits encBits) encBits)) encBool)
    {A : ℕ → List Bool → WordOracleComp CCAOp Bool} (hA : IsOraclePPT encBool A) :
    (P.romFilterCpaReductionWord keyLen d A).IsPPT encBits where
  choose := by
    change IsPPTOn (encPair encUnary encBits) (Encryption.encChoiceOut encBits) (fun x =>
      (P.romFilterCpaReductionWord keyLen d A).choose x.1 x.2)
    have hm₀ := (hP.msgLen.comp (ComputableInPolyTime.fst encUnary encBits)).sampleList
    have hm₁ := (hP.msgLen.comp ((ComputableInPolyTime.fst encUnary encBits).comp
      (ComputableInPolyTime.fst (encPair encUnary encBits) encBits))).sampleList
    have hout : ComputableInPolyTime
        (fun q : ((ℕ × List Bool) × List Bool) × List Bool =>
          ((q.1.2, q.2), encPair encBits encBits (q.1.1.2, q.2)))
        (encPair (encPair (encPair encUnary encBits) encBits) encBits)
        (Encryption.encChoiceOut encBits) := by
      refine ((ComputableInPolyTime.fst _ _).snd'.prod (ComputableInPolyTime.snd _ _)).prod ?_
      exact ((ComputableInPolyTime.fst _ _).fst'.snd'.prod
        (ComputableInPolyTime.snd _ _)).encoding_comp
    have hall := IsPPTOn.bind_with
      (first := fun x : ℕ × List Bool => BitString.sampleList (P.msgLen x.1))
      (second := fun x m₀ => BitString.sampleList (P.msgLen x.1) >>= fun m₁ =>
        pure ((m₀, m₁), encPair encBits encBits (x.2, m₁))) hm₀
      (IsPPTOn.bind_with (first := fun p : (ℕ × List Bool) × List Bool =>
          BitString.sampleList (P.msgLen p.1.1))
        (second := fun p m₁ => pure ((p.2, m₁), encPair encBits encBits (p.1.2, m₁))) hm₁
        hout.isPPTOn)
    exact hall.congr fun x => rfl
  guess := by
    change IsPPTOn Encryption.encGuessInput encBool (fun x =>
      (P.romFilterCpaReductionWord keyLen d A).guess x.1 x.2.1 x.2.2)
    let D := Decoder.bits.pair Decoder.bits
    have hn : ComputableInPolyTime (fun c : (ℕ × List Bool × List Bool) × List Bool => c.1.1)
        encGuessKey encUnary := by fun_prop
    have hstate : ComputableInPolyTime
        (fun c : (ℕ × List Bool × List Bool) × List Bool => D.decode c.1.2.1)
        encGuessKey (encPair encBits encBits) :=
      D.computableInPolyTime.comp (by fun_prop)
    have hcs : ComputableInPolyTime
        (fun c : (ℕ × List Bool × List Bool) × List Bool => c.1.2.2) encGuessKey encBits := by
      fun_prop
    have hk : ComputableInPolyTime
        (fun c : (ℕ × List Bool × List Bool) × List Bool => c.2) encGuessKey encBits := by
      fun_prop
    -- the simulator as a closed handler of the adversary
    have hhandler : IsPPTOn (encHandlerCall encGuessKey (encFinEnum CCAOp) encSimState)
        (encPair encBits encSimState)
        (fun z : ((ℕ × List Bool × List Bool) × List Bool) × (CCAOp × List Bool) × WState =>
          P.simFilterWordHandler keyLen d z.1.1.1 (D.decode z.1.1.2.1).1 z.1.1.2.2 z.2.1 z.2.2) :=
      (hP.isPPTOn_simFilterWordHandler hkeyLen hd).preprocess
        (((hn.comp (ComputableInPolyTime.fst _ _)).prod
          ((hstate.fst'.comp (ComputableInPolyTime.fst _ _)).prod
            (hcs.comp (ComputableInPolyTime.fst _ _)))).prod
          (ComputableInPolyTime.snd _ _))
    have hrun := hA.run_interpret_preprocess' (operationEncoding := encFinEnum CCAOp)
      (stateEncoding := encSimState)
      (handler := fun (c : (ℕ × List Bool × List Bool) × List Bool) request st =>
        P.simFilterWordHandler keyLen d c.1.1 (D.decode c.1.2.1).1 c.1.2.2 request st)
      (prepare := fun c : (ℕ × List Bool × List Bool) × List Bool =>
        (c.1.1, Encryption.encKEMChallenge ((D.decode c.1.2.1).1, c.2, c.1.2.2)))
      (initial := fun _ => {})
      (resources := fun (c : (ℕ × List Bool × List Bool) × List Bool) w =>
        16 * w.length + 8 * (P.coinLen c.1.1 + keyLen c.1.1) + 13)
      (hn.prod (hstate.fst'.prod (hk.prod hcs)).encoding_comp)
      hhandler (ComputableInPolyTime.const _)
      (fun (c : (ℕ × List Bool × List Bool) × List Bool) st =>
        CachesBounded (P.coinLen c.1.1 + keyLen c.1.1) st)
      (fun _ => ⟨by simp, by simp, by simp⟩)
      (by
        have h₁ := hP.coinLen.comp (hn.comp (ComputableInPolyTime.fst encGuessKey encBits))
        have h₂ := hkeyLen.comp (hn.comp (ComputableInPolyTime.fst encGuessKey encBits))
        have h₃ := ComputableInPolyTime.length_bits.comp
          (ComputableInPolyTime.snd encGuessKey encBits)
        fun_prop)
      (fun c request st hst result hresult => by
        have hx := simFilterWordHandler_eq_explicit P keyLen d
          ((c.1.1, (D.decode c.1.2.1).1, c.1.2.2), request, st)
        change P.simFilterWordHandler keyLen d c.1.1 (D.decode c.1.2.1).1 c.1.2.2 request st =
          _ at hx
        rw [hx] at hresult
        obtain ⟨h₁, h₂, h₃⟩ := simCallExplicit_support P keyLen d _ (Nat.le_add_right _ _)
          (Nat.le_add_left _ _) hst result hresult
        exact ⟨h₁, by lia, by lia⟩)
    have hlookup : ComputableInPolyTime
        (fun q : ((ℕ × List Bool × List Bool) × List Bool) × (Bool × WState) =>
          (q.2.2.gCache.lookup (D.decode q.1.1.2.1).2).isSome)
        (encPair encGuessKey (encPair encBool encSimState)) encBool := by
      simp only [lookup_isSome_eq_any]
      exact ComputableInPolyTime.anyWithInput (by fun_prop)
        (ComputableInPolyTime.beq (by fun_prop)
          (hstate.snd'.comp ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))))
    have hhit := hrun.map_with (f := fun c q => (q.2.gCache.lookup (D.decode c.1.2.1).2).isSome)
      hlookup
    have hall := IsPPTOn.bind_with
      (first := fun x : ℕ × List Bool × List Bool => BitString.sampleList (keyLen x.1))
      (second := fun x kStar =>
        (fun q : Bool × WState => (q.2.gCache.lookup (D.decode x.2.1).2).isSome) <$>
          (OracleComp.interpret
            (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) fun request st =>
              P.simFilterWordHandler keyLen d x.1 (D.decode x.2.1).1 x.2.2 request st)
            (A x.1 (Encryption.encKEMChallenge ((D.decode x.2.1).1, kStar, x.2.2)))).run {})
      (hkeyLen.comp (ComputableInPolyTime.fst _ _)).sampleList hhit
    refine hall.congr fun x => ?_
    simp only [romFilterCpaReductionWord, simFilterWordHit, bind_pure_comp]
    rfl

/-- **The `FO-notbot` reduction is uniform strict PPT.** For an efficient PKE family and a
polynomial-time key length, the word-level IND-CPA reduction `romCpaReductionWord A` of every
uniform strict oracle PPT ROM IND-CCA adversary `A` is a uniform strict PPT chosen-message
adversary. -/
theorem IsEfficient.isPPT_romCpaReductionWord {P : WordPKE} (hP : P.IsEfficient)
    {keyLen : ℕ → ℕ} (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {A : ℕ → List Bool → WordOracleComp CCAOp Bool} (hA : IsOraclePPT encBool A) :
    (P.romCpaReductionWord keyLen A).IsPPT encBits :=
  hP.isPPT_romFilterCpaReductionWord hkeyLen (d := fun _ _ _ => true)
    (ComputableInPolyTime.const true) hA

end Certificates

end WordPKE

end Cslib.Crypto.Protocols.FujisakiOkamoto
