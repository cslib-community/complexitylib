/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordGame
import CslibFrontier.Computability.Probabilistic.Oracle.ReplayParameter
import Mathlib.Data.Set.Finite.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.QueryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PMFSwap

/-!
# The word-level FO game at one parameter, as the typed FO game

The ROM IND-CCA bound for `FO-notbot`, `Scheme.indCcaRomAdvantage_le` in
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot`, holds for one scheme over finite
message, coin, ciphertext and key types, against randomized adversaries that draw their coins
first. The word-level family `WordPKE` has a native game `WordPKE.romIndCcaGameWord` against
programs with private coins, and a native IND-CPA reduction `WordPKE.romCpaReductionWord`. This
module identifies the two at each parameter.

**The scheme at one parameter.** `WordPKE.finiteScheme P keyLen n` is the FO bundle of `P` at
`n` over finite types: uniform bit strings of lengths `msgLen n`, `coinLen n` and `keyLen n`, and
the ciphertext space `WordPKE.Ciphertext P n` of words of length at most `ctLen n`. Its
explicit-coin scheme `WordPKE.finitePKE P n` reads `encDet` as a ciphertext with
`WordPKE.toCiphertext`, which keeps a word that fits and replaces a longer one by the empty word.

**Properties of the PKE family.** `WordPKE.DeltaCorrect` is the `δ`-correctness of
[HofheinzHoevelmannsKiltz2017] at every parameter, stated for `finitePKE`. For a family whose
ciphertexts fit (`WordPKE.CiphertextFits`, in
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word`), `finitePKE` encrypts exactly as `P` on
generated keys.

**The typed view of a native adversary.** A uniform strict oracle PPT adversary has a coin-tape
machine whose replay on a uniform tape of polynomial length has the joint law of the adversary
against every stateful oracle (`IsOraclePPT.exists_savedCoins_of_keyGen`), with the tape length
bounded on the challenge words of the games. `WordPKE.savedCoinAdversary` is that replay as a
`RandomizedROAdversary` of `finiteScheme n`: it sends each request through `WordPKE.typedQuery`,
which answers out-of-domain requests with the empty word, as the word game and the native simulator
do.

**The bridge.** `WordPKE.IsEfficient.exists_typedAdversary` gives, for an efficient family and a
polynomial-time key length, a typed adversary at each parameter with polynomially many `G` and `H`
queries. When the ciphertexts of `P` fit, the word game has the law of the typed game
`Scheme.roIndCcaGame` played by it, and the advantage of `romCpaReductionWord` in the IND-CPA
game of `P` is the two-stage IND-CPA advantage `ExplicitCoinPKE.cpaAdvantage` of the typed
reduction `Scheme.romCpaReduction`. The proofs represent typed caches as word caches: one lazy call
of the typed game or simulator gives the word call on the represented cache (`memoize_map`), and
replaying the machine against the typed oracles gives its replay against the word oracles.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.Ciphertext`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.toCiphertext`: the ciphertext space at one
  parameter.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.finitePKE`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.finiteScheme`: the scheme and the FO bundle at
  one parameter over finite types.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.DeltaCorrect`: correctness of the PKE family.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.typedHQuery`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.typedQuery`: native requests as typed queries.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.savedCoinAdversary`: the typed view of a
  coin-tape replay.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.savedCoinAdversary_queryBounds`: the typed view
  makes polynomially many `G` and `H` queries.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.exists_typedAdversary`: the word game
  is the typed game, and the native reduction's IND-CPA advantage is the typed reduction's.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021), §2.1.
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability Turing.MultiTapeTM
open scoped NNReal

namespace WordPKE

variable (P : WordPKE) (keyLen : ℕ → ℕ)

/-! ### The scheme at one parameter over finite spaces -/

/-- The ciphertext space of `P` at parameter `n`: the words of length at most `ctLen n`. -/
abbrev Ciphertext (n : ℕ) : Type := {c : List Bool // c.length ≤ P.ctLen n}

instance (n : ℕ) : Finite (P.Ciphertext n) :=
  (List.finite_length_le Bool (P.ctLen n)).to_subtype

/-- A word as a ciphertext at parameter `n`: the word itself when it has length at most `ctLen n`,
and the empty word otherwise. -/
@[expose] def toCiphertext (n : ℕ) (c : List Bool) : P.Ciphertext n :=
  if h : c.length ≤ P.ctLen n then ⟨c, h⟩ else ⟨[], Nat.zero_le _⟩

/-- The explicit-coin scheme of `P` at parameter `n` over finite spaces: messages and coins are
bit strings of lengths `msgLen n` and `coinLen n`, coins are uniform, and ciphertexts lie in
`Ciphertext n`. Encryption is `encDet` read with `toCiphertext`; decryption reports only results
of length `msgLen n`. When the ciphertexts of `P` fit its ciphertext space (`CiphertextFits`),
encryption under a generated key is `encDet` itself. -/
@[expose] noncomputable def finitePKE (n : ℕ) :
    ExplicitCoinPKE (List Bool) (List Bool) (BitString (P.msgLen n)) (BitString (P.coinLen n))
      (P.Ciphertext n) where
  keyGen := P.keyGen n
  sampleCoins := ProbComp.uniform _
  encDet pk m r := P.toCiphertext n (P.encDet n pk (List.ofFn m) (List.ofFn r))
  dec sk c := (P.dec n sk c.val).bind fun m =>
    if m.length = P.msgLen n then some (BitString.ofList _ m) else none

/-- The FO parameter bundle of `P` at parameter `n` over finite spaces: the explicit-coin scheme
`finitePKE n`, uniform messages and uniform keys of length `keyLen n`. -/
@[expose] noncomputable def finiteScheme (n : ℕ) :
    Scheme (List Bool) (List Bool) (BitString (P.msgLen n)) (BitString (P.coinLen n))
      (P.Ciphertext n) (BitString (keyLen n)) where
  pke := P.finitePKE n
  sampleMsg := ProbComp.uniform _
  sampleKey := ProbComp.uniform _

/-- The explicit-coin scheme of `finiteScheme n` is `finitePKE n`. -/
@[simp] theorem finiteScheme_pke (n : ℕ) : (P.finiteScheme keyLen n).pke = P.finitePKE n :=
  rfl

/-- Messages of `finiteScheme n` are uniform. -/
@[simp] theorem finiteScheme_sampleMsg (n : ℕ) :
    (P.finiteScheme keyLen n).sampleMsg = ProbComp.uniform _ :=
  rfl

/-- Keys of `finiteScheme n` are uniform. -/
@[simp] theorem finiteScheme_sampleKey (n : ℕ) :
    (P.finiteScheme keyLen n).sampleKey = ProbComp.uniform _ :=
  rfl

/-- Key generation of `finitePKE n` is that of `P` at `n`. -/
@[simp] theorem finitePKE_keyGen (n : ℕ) : (P.finitePKE n).keyGen = P.keyGen n :=
  rfl

/-- Coins of `finitePKE n` are uniform. -/
@[simp] theorem finitePKE_sampleCoins (n : ℕ) :
    (P.finitePKE n).sampleCoins = ProbComp.uniform _ :=
  rfl

/-! ### Properties of the PKE family -/

/-- **`δ`-correctness of `P`** ([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021),
§2.1): at every parameter `n`, the expectation over generated key pairs of the worst-message
probability that decryption of an encryption under uniform coins fails is at most `δ n`. It is
`ExplicitCoinPKE.DeltaCorrect` of the scheme at parameter `n`. -/
@[expose] def DeltaCorrect (δ : ℕ → ℝ≥0) : Prop :=
  ∀ n, (P.finitePKE n).DeltaCorrect (δ n)

/-! ### The typed view of a native adversary -/

/-- The `H` request of the typed interface at parameter `n` named by a word: the triple
`(b, m, c)` that the word encodes, when it is in the `H` domain (`isHQuery`). -/
def typedHQuery (n : ℕ) (w : List Bool) :
    Option (Bool × BitString (P.msgLen n) × P.Ciphertext n) :=
  match hQueryDecoder.decode w with
  | (b, m, c) =>
    if P.isHQuery n w then some (b, BitString.ofList _ m, P.toCiphertext n c) else none

/-- A request of a native adversary at parameter `n` as a query of the typed ROM IND-CCA
interface of `finiteScheme n`, with the typed answer returned as a word: `G` on messages of length
`msgLen n`, `H` on requests in the `H` domain, and decapsulation on words of length at most
`ctLen n`, whose answer is encoded with `encOption encBits`. Every other request is answered with
the empty word and makes no query. These are the answers of the word game `romIndCcaGameWord` and
of the native simulator `simFilterWordHandler`. -/
noncomputable def typedQuery (n : ℕ) : CCAOp → List Bool →
    OracleComp (ROResp (M := BitString (P.msgLen n)) (CT := P.Ciphertext n)
      (BitString (P.coinLen n)) (BitString (keyLen n))) (List Bool)
  | .G, w =>
    if w.length = P.msgLen n then
      List.ofFn <$> OracleComp.query (spec := ROResp (M := BitString (P.msgLen n))
        (CT := P.Ciphertext n) (BitString (P.coinLen n)) (BitString (keyLen n)))
        (ROQuery.G (BitString.ofList _ w))
    else pure []
  | .H, w =>
    match P.typedHQuery n w with
    | some x =>
      List.ofFn <$> OracleComp.query (spec := ROResp (M := BitString (P.msgLen n))
        (CT := P.Ciphertext n) (BitString (P.coinLen n)) (BitString (keyLen n))) (ROQuery.H x)
    | none => pure []
  | .decaps, w =>
    if w.length ≤ P.ctLen n then
      (fun k => encOption encBits (Option.map List.ofFn k)) <$>
        OracleComp.query (spec := ROResp (M := BitString (P.msgLen n))
          (CT := P.Ciphertext n) (BitString (P.coinLen n)) (BitString (keyLen n)))
          (ROQuery.decaps (P.toCiphertext n w))
    else pure []

/-- **The saved-coin view of a native adversary** at parameter `n`, as a randomized adversary of
the typed ROM IND-CCA game of `finiteScheme n`. Its coins are a uniform tape of
`c * (2 n + 2 + keyC (n + 1) ^ keyD) ^ d` bits. On the challenge `(pk, c*, k*)` it replays the
coin-tape machine `machine` on `(1ⁿ, encKEMChallenge (pk, k*, c*))` with the tape cut at the
machine's clock, sends each request through `typedQuery`, and decodes the output bit. A challenge
word longer than `keyC (n + 1) ^ keyD` gets `false` without any query. -/
noncomputable def savedCoinAdversary {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control CCAOp) (c d keyC keyD n : ℕ) :
    RandomizedROAdversary (List Bool) (BitString (P.msgLen n)) (BitString (P.coinLen n))
      (P.Ciphertext n) (BitString (keyLen n)) where
  Coins := List Bool
  coins := BitString.sampleList (c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d)
  run tape := fun ⟨pk, ct, key⟩ =>
    if (Encryption.encKEMChallenge (pk, List.ofFn key, ct.val)).length ≤ keyC * (n + 1) ^ keyD then
      Decoder.bool.decode <$> machine.runCoins (P.typedQuery keyLen n)
        (tape.take (c * ((encPair encUnary encBits
          (n, Encryption.encKEMChallenge (pk, List.ofFn key, ct.val))).length + 1) ^ d))
        (encPair encUnary encBits (n, Encryption.encKEMChallenge (pk, List.ofFn key, ct.val)))
    else pure false

/-! ### Represented executions -/

section Represents

variable {σ σ' α α' β β' : Type}

/-- The typed stateful computation `x'` represents the word computation `x` under the state map
`rep` and the reply map `f`: from every typed state, mapping the result and the final state of
`x'` gives the run of `x` from the represented state. -/
private def Represents (rep : σ' → σ) (f : α' → α) (x' : StateT σ' ProbComp α')
    (x : StateT σ ProbComp α) : Prop :=
  ∀ s, (ProbComp.eval (x'.run s)).map (fun p => (f p.1, rep p.2)) = ProbComp.eval (x.run (rep s))

private theorem Represents.pure {rep : σ' → σ} {f : α' → α} (a : α') :
    Represents rep f (pure a) (pure (f a)) := by
  intro s
  simp [ProbComp.eval_pure]

private theorem Represents.bind {rep : σ' → σ} {f : α' → α} {g : β' → β}
    {x' : StateT σ' ProbComp α'} {x : StateT σ ProbComp α}
    {k' : α' → StateT σ' ProbComp β'} {k : α → StateT σ ProbComp β}
    (hx : Represents rep f x' x) (hk : ∀ a, Represents rep g (k' a) (k (f a))) :
    Represents rep g (x' >>= k') (x >>= k) := by
  intro s
  rw [StateT.run_bind, StateT.run_bind, ProbComp.eval_bind, ProbComp.eval_bind, PMF.map_bind,
    ← hx s, PMF.bind_map]
  exact congrArg (PMF.bind _) (funext fun p => hk p.1 p.2)

private theorem Represents.map_left {rep : σ' → σ} {f : α' → α} {g : β' → α'}
    {x' : StateT σ' ProbComp β'} {x : StateT σ ProbComp α}
    (h : Represents rep (fun b => f (g b)) x' x) : Represents rep f (g <$> x') x := by
  intro s
  rw [StateT.run_map, ProbComp.eval_map, PMF.map_comp, ← h s]
  rfl

private theorem Represents.map_right {rep : σ' → σ} {f : α' → α} {g : α → β}
    {x' : StateT σ' ProbComp α'} {x : StateT σ ProbComp α}
    (h : Represents rep f x' x) : Represents rep (fun a => g (f a)) x' (g <$> x) := by
  intro s
  rw [StateT.run_map, ProbComp.eval_map, ← h s, PMF.map_comp]
  rfl

private theorem Represents.congr_fun {rep : σ' → σ} {f g : α' → α}
    {x' : StateT σ' ProbComp α'} {x : StateT σ ProbComp α}
    (h : Represents rep f x' x) (hfg : ∀ a, f a = g a) : Represents rep g x' x := by
  have : f = g := funext hfg
  exact this ▸ h

/-- One lazy random-oracle call on related caches: a typed `memoize` call on a component cache
represents the word call at the key's image, when the word sampler is the image of the typed
one. -/
private theorem represents_zoomMemoize {Key Key' V V' : Type} [DecidableEq Key]
    [DecidableEq Key'] (rep : σ' → σ) (get' : σ' → List (Key × V))
    (set' : σ' → List (Key × V) → σ') (get : σ → List (Key' × V'))
    (set : σ → List (Key' × V') → σ) (keyMap : Key ↪ Key') (valueMap : V → V')
    (hget : ∀ s, get (rep s) = (get' s).map fun e => (keyMap e.1, valueMap e.2))
    (hset : ∀ s c, rep (set' s c) = set (rep s) (c.map fun e => (keyMap e.1, valueMap e.2)))
    (d' : ProbComp V) (d : ProbComp V') (hd : (ProbComp.eval d').map valueMap = ProbComp.eval d)
    (key : Key) :
    Represents rep valueMap (RandomOracle.zoomStateT get' set' (memoize (fun _ => d') key))
      (RandomOracle.zoomStateT get set (memoize (fun _ => d) (keyMap key))) := by
  intro s
  change (ProbComp.eval (RandomOracle.zoomStateT get' set' (memoize (fun _ => d') key) s)).map _ =
    ProbComp.eval (RandomOracle.zoomStateT get set (memoize (fun _ => d) (keyMap key)) (rep s))
  rw [RandomOracle.eval_zoomStateT_memoize, RandomOracle.eval_zoomStateT_memoize, PMF.map_comp,
    hget, ← memoize_map (m := PMF) keyMap valueMap (fun _ => ProbComp.eval d')
      (fun _ => ProbComp.eval d) (fun _ => by rw [PMF.monad_map_eq_map, hd]) key (get' s),
    PMF.monad_map_eq_map, PMF.map_comp]
  congr 1
  funext ⟨v, c⟩
  exact Prod.ext rfl (hset s c)

end Represents

/-! ### Typed calls as word calls -/

variable {P keyLen}

/-- A word that fits the ciphertext space is its own ciphertext. -/
theorem toCiphertext_val {n : ℕ} {c : List Bool} (h : c.length ≤ P.ctLen n) :
    (P.toCiphertext n c).val = c := by
  simp [toCiphertext, h]

/-- Two words that fit the ciphertext space are equal as ciphertexts exactly when they are equal. -/
theorem toCiphertext_inj {n : ℕ} {c c' : List Bool} (h : c.length ≤ P.ctLen n)
    (h' : c'.length ≤ P.ctLen n) : P.toCiphertext n c = P.toCiphertext n c' ↔ c = c' := by
  refine ⟨fun heq => ?_, fun heq => heq ▸ rfl⟩
  rw [← toCiphertext_val h, ← toCiphertext_val h', heq]

/-- Bit strings as words. -/
private def ofFnEmb (k : ℕ) : BitString k ↪ List Bool := ⟨List.ofFn, List.ofFn_injective⟩

/-- Typed `H` requests as word triples. -/
private def hKeyEmb (P : WordPKE) (n : ℕ) :
    Bool × BitString (P.msgLen n) × P.Ciphertext n ↪ Bool × List Bool × List Bool :=
  (Function.Embedding.refl Bool).prodMap ((ofFnEmb _).prodMap (Function.Embedding.subtype _))

/-- The typed random-oracle caches of the game at parameter `n` as word caches. -/
private def cacheRep (P : WordPKE) (keyLen : ℕ → ℕ) (n : ℕ)
    (st : ROCache (BitString (P.msgLen n)) (BitString (P.coinLen n)) (P.Ciphertext n)
      (BitString (keyLen n))) : ROCache (List Bool) (List Bool) (List Bool) (List Bool) where
  gCache := st.gCache.map fun e => (ofFnEmb _ e.1, List.ofFn e.2)
  hCache := st.hCache.map fun e => (hKeyEmb P n e.1, List.ofFn e.2)

/-- The typed secret key of `FO-notbot` as a word secret key. -/
private def skRep (P : WordPKE) (n : ℕ) (dk : ImplicitSK (List Bool) (List Bool)
    (BitString (P.msgLen n))) : ImplicitSK (List Bool) (List Bool) (List Bool) :=
  ⟨dk.sk, dk.pk, List.ofFn dk.fallback⟩

/-- Uniform words are uniform bit strings read as words. -/
private theorem uniformList_eq_map_ofFn (k : ℕ) :
    BitString.uniformList k = (ProbComp.eval (ProbComp.uniform (BitString k))).map List.ofFn := by
  rw [ProbComp.eval_uniform]
  rfl

private theorem represents_roHashG (n : ℕ) (m : BitString (P.msgLen n)) :
    Represents (cacheRep P keyLen n) List.ofFn
      (roHashG (CT := P.Ciphertext n) (K := BitString (keyLen n))
        (ProbComp.uniform (BitString (P.coinLen n))) m)
      (roHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (P.coinLen n))
        (List.ofFn m)) :=
  represents_zoomMemoize (cacheRep P keyLen n) ROCache.gCache (fun st c => { st with gCache := c })
    ROCache.gCache (fun st c => { st with gCache := c }) (ofFnEmb _) List.ofFn (fun _ => rfl)
    (fun _ _ => rfl) _ _ (by rw [BitString.eval_sampleList, uniformList_eq_map_ofFn]) m

private theorem represents_roHashH (n : ℕ) (x : Bool × BitString (P.msgLen n) × P.Ciphertext n) :
    Represents (cacheRep P keyLen n) List.ofFn
      (roHashH (M := BitString (P.msgLen n)) (R := BitString (P.coinLen n))
        (ProbComp.uniform (BitString (keyLen n))) x)
      (roHashH (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen n))
        (hKeyEmb P n x)) :=
  represents_zoomMemoize (cacheRep P keyLen n) ROCache.hCache (fun st c => { st with hCache := c })
    ROCache.hCache (fun st c => { st with hCache := c }) (hKeyEmb P n) List.ofFn (fun _ => rfl)
    (fun _ _ => rfl) _ _ (by rw [BitString.eval_sampleList, uniformList_eq_map_ofFn]) x

private theorem roWordOracle_G (n : ℕ) (w : List Bool) :
    P.roWordOracle keyLen n (.G, w) =
      if w.length = P.msgLen n then
        roHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (P.coinLen n)) w
      else pure [] := by
  funext st
  by_cases h : w.length = P.msgLen n
  · simp only [roWordOracle, h, ↓reduceIte]
  · simp only [roWordOracle, h, ↓reduceIte]
    rfl

private theorem roWordOracle_H (n : ℕ) (w : List Bool) :
    P.roWordOracle keyLen n (.H, w) =
      if P.isHQuery n w then
        roHashH (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen n))
          (hQueryDecoder.decode w)
      else pure [] := by
  funext st
  by_cases h : P.isHQuery n w = true
  · simp only [roWordOracle, h, ↓reduceIte]
  · simp only [roWordOracle, h, Bool.false_eq_true, ↓reduceIte]
    rfl

private theorem hKeyEmb_apply (n : ℕ) (b : Bool) (m : BitString (P.msgLen n))
    (c : P.Ciphertext n) : hKeyEmb P n (b, m, c) = (b, List.ofFn m, c.val) :=
  rfl

/-- A word in the `H` domain names a typed `H` request, whose word triple it encodes. -/
private theorem typedHQuery_of_isHQuery {n : ℕ} {w : List Bool} (h : P.isHQuery n w = true) :
    ∃ x, P.typedHQuery n w = some x ∧ hKeyEmb P n x = hQueryDecoder.decode w := by
  have hy := h
  unfold isHQuery at hy
  unfold typedHQuery
  rcases hd : hQueryDecoder.decode w with ⟨b, m, c⟩
  rw [hd] at hy
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  simp only [h, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  rw [hKeyEmb_apply, BitString.ofFn_ofList hy.1.2, toCiphertext_val hy.2]

private theorem typedHQuery_of_not_isHQuery {n : ℕ} {w : List Bool}
    (h : ¬P.isHQuery n w = true) : P.typedHQuery n w = none := by
  unfold typedHQuery
  rcases hQueryDecoder.decode w with ⟨b, m, c⟩
  simp [h]

/-- The word triple of a typed `H` request is in the `H` domain. -/
private theorem isHQuery_encHQuery (n : ℕ) (x : Bool × BitString (P.msgLen n) × P.Ciphertext n) :
    P.isHQuery n (encHQuery (hKeyEmb P n x)) = true := by
  obtain ⟨b, m, c⟩ := x
  unfold isHQuery
  rw [hQueryDecoder.decode_enc, hKeyEmb_apply]
  simp [c.2]

private theorem withRO_queryG (n : ℕ) (m : List Bool) :
    P.withRO keyLen n (P.queryG n m) =
      List.take (P.coinLen n) <$> P.roWordOracle keyLen n (.G, m) := by
  simp only [withRO, queryG, OracleComp.interpret_map, ProbOracleComp.interpret_query]

private theorem withRO_queryH (n : ℕ) (x : Bool × List Bool × List Bool) :
    P.withRO keyLen n (queryH keyLen n x) =
      List.take (keyLen n) <$> P.roWordOracle keyLen n (.H, encHQuery x) := by
  simp only [withRO, queryH, OracleComp.interpret_map, ProbOracleComp.interpret_query]

private theorem represents_withRO_queryG (n : ℕ) (m : BitString (P.msgLen n)) :
    Represents (cacheRep P keyLen n) List.ofFn
      (roHashG (CT := P.Ciphertext n) (K := BitString (keyLen n))
        (ProbComp.uniform (BitString (P.coinLen n))) m)
      (P.withRO keyLen n (P.queryG n (List.ofFn m))) := by
  simp only [withRO_queryG, roWordOracle_G, List.length_ofFn, ↓reduceIte]
  exact (represents_roHashG n m).map_right.congr_fun fun r =>
    List.take_of_length_le (by simp)

private theorem represents_withRO_queryH (n : ℕ)
    (x : Bool × BitString (P.msgLen n) × P.Ciphertext n) :
    Represents (cacheRep P keyLen n) List.ofFn
      (roHashH (M := BitString (P.msgLen n)) (R := BitString (P.coinLen n))
        (ProbComp.uniform (BitString (keyLen n))) x)
      (P.withRO keyLen n (queryH keyLen n (hKeyEmb P n x))) := by
  simp only [withRO_queryH, roWordOracle_H, isHQuery_encHQuery n x, hQueryDecoder.decode_enc,
    ↓reduceIte]
  exact (represents_roHashH n x).map_right.congr_fun fun k =>
    List.take_of_length_le (by simp)

/-- Typed `FO-notbot` decapsulation against the typed random oracles represents native
decapsulation against the word random oracles, for a ciphertext in the ciphertext space and a key
whose ciphertexts fit. -/
private theorem represents_decapsNotBotM {n : ℕ}
    (dk : ImplicitSK (List Bool) (List Bool) (BitString (P.msgLen n)))
    (hfit : ∀ m r, m.length = P.msgLen n → r.length = P.coinLen n →
      (P.encDet n dk.pk m r).length ≤ P.ctLen n)
    {w : List Bool} (hw : w.length ≤ P.ctLen n) :
    Represents (cacheRep P keyLen n) List.ofFn
      ((P.finiteScheme keyLen n).decapsNotBotM
        (roHashG (CT := P.Ciphertext n) (K := BitString (keyLen n))
          (ProbComp.uniform (BitString (P.coinLen n))))
        (roHashH (M := BitString (P.msgLen n)) (R := BitString (P.coinLen n))
          (ProbComp.uniform (BitString (keyLen n))))
        dk (P.toCiphertext n w))
      ((P.scheme keyLen n).decapsNotBotM (fun m => P.withRO keyLen n (P.queryG n m))
        (fun x => P.withRO keyLen n (queryH keyLen n x)) (skRep P n dk) w) := by
  have hH (b : Bool) (m : BitString (P.msgLen n)) := represents_withRO_queryH (keyLen := keyLen) n
    (b, m, P.toCiphertext n w)
  simp only [hKeyEmb_apply, toCiphertext_val hw] at hH
  rw [Scheme.decapsNotBotM_eq, Scheme.decapsNotBotM_eq]
  have hdec : (P.finiteScheme keyLen n).pke.dec dk.sk (P.toCiphertext n w) =
      (P.dec n dk.sk w).bind fun m =>
        if m.length = P.msgLen n then some (BitString.ofList _ m) else none := by
    simp only [finiteScheme, finitePKE, toCiphertext_val hw]
  have hdec' : (P.scheme keyLen n).pke.dec (skRep P n dk).sk w =
      (P.dec n dk.sk w).filter fun m => m.length == P.msgLen n :=
    rfl
  rw [hdec, hdec']
  cases hD : P.dec n dk.sk w with
  | none => exact hH true dk.fallback
  | some m =>
    by_cases hm : m.length = P.msgLen n
    · obtain ⟨m, rfl⟩ : ∃ m', m = List.ofFn m' := ⟨_, (BitString.ofFn_ofList hm).symm⟩
      simp only [Option.bind_some, Option.filter_some, List.length_ofFn, ↓reduceIte,
        BitString.ofList_ofFn, beq_self_eq_true]
      refine (represents_withRO_queryG n m).bind fun r => ?_
      have hiff := toCiphertext_inj (P := P) (hfit _ _ (List.length_ofFn (f := m))
        (List.length_ofFn (f := r))) hw
      split_ifs with h₁ h₂ h₂
      · exact hH false m
      · exact absurd (hiff.mp h₁) h₂
      · exact absurd (hiff.mpr h₂) h₁
      · exact hH true dk.fallback
    · have hm' : (m.length == P.msgLen n) = false := by simpa using hm
      simp only [Option.bind_some, Option.filter_some, hm, hm', ↓reduceIte, Bool.false_eq_true]
      exact hH true dk.fallback

/-- **The oracles of the word game, typed.** At a key whose ciphertexts fit, the typed query of
every request, answered by the oracles of the typed game `roHandler`, represents the oracle
`ccaWordOracle` of the word game on represented caches. -/
private theorem represents_ccaWordOracle {n : ℕ}
    (dk : ImplicitSK (List Bool) (List Bool) (BitString (P.msgLen n))) (cStar : P.Ciphertext n)
    (hfit : ∀ m r, m.length = P.msgLen n → r.length = P.coinLen n →
      (P.encDet n dk.pk m r).length ≤ P.ctLen n)
    (op : CCAOp) (w : List Bool) :
    Represents (cacheRep P keyLen n) id
      (OracleComp.interpret ((P.finiteScheme keyLen n).roHandler dk cStar)
        (P.typedQuery keyLen n op w))
      (P.ccaWordOracle keyLen n (skRep P n dk) cStar.val (op, w)) := by
  cases op with
  | G =>
    simp only [typedQuery, ccaWordOracle, roWordOracle_G]
    by_cases hw : w.length = P.msgLen n
    · obtain ⟨m, rfl⟩ : ∃ m', w = List.ofFn m' := ⟨_, (BitString.ofFn_ofList hw).symm⟩
      simp only [List.length_ofFn, ↓reduceIte, OracleComp.interpret_map,
        OracleComp.interpret_query, Scheme.roHandler, ROQuery.dispatch, BitString.ofList_ofFn]
      exact Represents.map_left (represents_roHashG n m)
    · simp only [hw, ↓reduceIte, OracleComp.interpret_pure]
      exact Represents.pure []
  | H =>
    simp only [typedQuery, ccaWordOracle, roWordOracle_H]
    by_cases hq : P.isHQuery n w = true
    · obtain ⟨x, hx, hxw⟩ := typedHQuery_of_isHQuery hq
      simp only [hx, hq, ↓reduceIte, OracleComp.interpret_map, OracleComp.interpret_query,
        Scheme.roHandler, ROQuery.dispatch, ← hxw]
      exact Represents.map_left (represents_roHashH n x)
    · simp only [typedHQuery_of_not_isHQuery hq, hq, Bool.false_eq_true, ↓reduceIte,
        OracleComp.interpret_pure]
      exact Represents.pure []
  | decaps =>
    simp only [typedQuery, ccaWordOracle]
    by_cases hw : w.length ≤ P.ctLen n
    · simp only [hw, ↓reduceIte, OracleComp.interpret_map, OracleComp.interpret_query,
        Scheme.roHandler, ROQuery.dispatch]
      by_cases hc : w = cStar.val
      · have hc' : P.toCiphertext n w = cStar := Subtype.ext (by rw [toCiphertext_val hw, hc])
        simp only [hc', ↓reduceIte]
        simp only [hc, ↓reduceIte, map_pure, Option.map_none, encOption_none]
        exact Represents.pure []
      · have hc' : P.toCiphertext n w ≠ cStar := fun h => hc (by rw [← h, toCiphertext_val hw])
        simp only [hc', hc, ↓reduceIte, decapsNotBot, hw, withRO, OracleComp.interpret_map,
          Scheme.interpret_decapsNotBotM]
        have h := ((represents_decapsNotBotM (keyLen := keyLen) dk hfit hw).map_right
          (g := some)).map_right (g := ⇑(encOption encBits))
        exact Represents.map_left (Represents.map_left (h.congr_fun fun _ => rfl))
    · have hc : w ≠ cStar.val := fun h => hw (h ▸ cStar.2)
      simp only [hw, hc, ↓reduceIte, decapsNotBot, withRO, OracleComp.interpret_pure, map_pure,
        encOption_none]
      exact Represents.pure []

/-! ### The native simulator, typed -/

/-- The typed state of the keyless simulator at parameter `n` as a word state. -/
private def simRep (P : WordPKE) (keyLen : ℕ → ℕ) (n : ℕ)
    (st : SimState (BitString (P.msgLen n)) (BitString (P.coinLen n)) (P.Ciphertext n)
      (BitString (keyLen n))) : SimState (List Bool) (List Bool) (List Bool) (List Bool) where
  gCache := st.gCache.map fun e => (ofFnEmb _ e.1, List.ofFn e.2)
  hCache := st.hCache.map fun e => (hKeyEmb P n e.1, List.ofFn e.2)
  hqCache := st.hqCache.map fun e => (Function.Embedding.subtype _ e.1, List.ofFn e.2)

private theorem represents_simHashG (n : ℕ) (m : BitString (P.msgLen n)) :
    Represents (simRep P keyLen n) List.ofFn
      (simHashG (CT := P.Ciphertext n) (K := BitString (keyLen n))
        (ProbComp.uniform (BitString (P.coinLen n))) m)
      (simHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (P.coinLen n))
        (List.ofFn m)) :=
  represents_zoomMemoize (simRep P keyLen n) (fun st => st.gCache)
    (fun st c => { st with gCache := c }) (fun st => st.gCache)
    (fun st c => { st with gCache := c }) (ofFnEmb _) List.ofFn (fun _ => rfl)
    (fun _ _ => rfl) _ _ (by rw [BitString.eval_sampleList, uniformList_eq_map_ofFn]) m

private theorem represents_simHashHRaw (n : ℕ)
    (x : Bool × BitString (P.msgLen n) × P.Ciphertext n) :
    Represents (simRep P keyLen n) List.ofFn
      (simHashHRaw (R := BitString (P.coinLen n)) (ProbComp.uniform (BitString (keyLen n))) x)
      (simHashHRaw (R := List Bool) (BitString.sampleList (keyLen n)) (hKeyEmb P n x)) :=
  represents_zoomMemoize (simRep P keyLen n) (fun st => st.hCache)
    (fun st c => { st with hCache := c }) (fun st => st.hCache)
    (fun st c => { st with hCache := c }) (hKeyEmb P n) List.ofFn (fun _ => rfl)
    (fun _ _ => rfl) _ _ (by rw [BitString.eval_sampleList, uniformList_eq_map_ofFn]) x

private theorem represents_simHashHq (n : ℕ) (c : P.Ciphertext n) :
    Represents (simRep P keyLen n) List.ofFn
      (simHashHq (M := BitString (P.msgLen n)) (R := BitString (P.coinLen n))
        (ProbComp.uniform (BitString (keyLen n))) c)
      (simHashHq (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen n)) c.val) :=
  represents_zoomMemoize (simRep P keyLen n) SimState.hqCache
    (fun st c' => { st with hqCache := c' }) SimState.hqCache
    (fun st c' => { st with hqCache := c' }) (Function.Embedding.subtype _) List.ofFn
    (fun _ => rfl) (fun _ _ => rfl) _ _
    (by rw [BitString.eval_sampleList, uniformList_eq_map_ofFn]) c

private theorem filterDecaps_true {M R CT K : Type}
    (Hq : CT → StateT (SimState M R CT K) ProbComp K) (c : CT) :
    filterDecaps Hq (fun _ _ => true) c = some <$> Hq c := by
  funext st
  simp only [filterDecaps, Bool.cond_true, bind_pure_comp]

private theorem simFilterWordHandler_G (n : ℕ) (pk cStar w : List Bool) :
    P.simFilterWordHandler keyLen (fun _ _ _ => true) n pk cStar (.G, w) =
      if w.length = P.msgLen n then
        simHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (P.coinLen n)) w
      else pure [] := by
  funext st
  by_cases h : w.length = P.msgLen n
  · simp only [simFilterWordHandler, h, ↓reduceIte]
    rfl
  · simp only [simFilterWordHandler, h, ↓reduceIte]
    rfl

private theorem simFilterWordHandler_H (n : ℕ) (pk cStar w : List Bool) :
    P.simFilterWordHandler keyLen (fun _ _ _ => true) n pk cStar (.H, w) =
      if P.isHQuery n w then
        (P.scheme keyLen n).simHashH pk (hQueryDecoder.decode w)
      else pure [] := by
  funext st
  by_cases h : P.isHQuery n w = true
  · simp only [simFilterWordHandler, h, ↓reduceIte]
    rfl
  · simp only [simFilterWordHandler, h, Bool.false_eq_true, ↓reduceIte]
    rfl

private theorem simFilterWordHandler_decaps (n : ℕ) (pk cStar w : List Bool) :
    P.simFilterWordHandler keyLen (fun _ _ _ => true) n pk cStar (.decaps, w) =
      if w.length ≤ P.ctLen n then
        encOption encBits <$> (if w = cStar then pure none else
          some <$> simHashHq (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen n)) w)
      else pure [] := by
  funext st
  by_cases h : w.length ≤ P.ctLen n
  · simp only [simFilterWordHandler, h, ↓reduceIte, Scheme.simFilterHandler,
      Scheme.simFilterDispatch, ROQuery.dispatch, filterDecaps_true]
    exact (StateT.run_map (m := ProbComp) (encOption encBits) _ st).symm
  · simp only [simFilterWordHandler, h, ↓reduceIte]
    rfl

/-- **The native simulator, typed.** At a key whose ciphertexts fit, the typed query of every
request, answered by the typed keyless simulator of `FO-notbot`, represents the native simulator
`simFilterWordHandler` on represented states. -/
private theorem represents_simFilterWordHandler {n : ℕ} (pk : List Bool) (cStar : P.Ciphertext n)
    (hfit : ∀ m r, m.length = P.msgLen n → r.length = P.coinLen n →
      (P.encDet n pk m r).length ≤ P.ctLen n)
    (op : CCAOp) (w : List Bool) :
    Represents (simRep P keyLen n) id
      (OracleComp.interpret ((P.finiteScheme keyLen n).simFilterHandler (fun _ _ => true) pk cStar)
        (P.typedQuery keyLen n op w))
      (P.simFilterWordHandler keyLen (fun _ _ _ => true) n pk cStar.val (op, w)) := by
  cases op with
  | G =>
    simp only [typedQuery, simFilterWordHandler_G]
    by_cases hw : w.length = P.msgLen n
    · obtain ⟨m, rfl⟩ : ∃ m', w = List.ofFn m' := ⟨_, (BitString.ofFn_ofList hw).symm⟩
      simp only [List.length_ofFn, ↓reduceIte, OracleComp.interpret_map,
        OracleComp.interpret_query, Scheme.simFilterHandler, Scheme.simFilterDispatch,
        ROQuery.dispatch, BitString.ofList_ofFn]
      exact Represents.map_left (represents_simHashG n m)
    · simp only [hw, ↓reduceIte, OracleComp.interpret_pure]
      exact Represents.pure []
  | H =>
    simp only [typedQuery, simFilterWordHandler_H]
    by_cases hq : P.isHQuery n w = true
    · obtain ⟨x, hx, hxw⟩ := typedHQuery_of_isHQuery hq
      simp only [hx, hq, ↓reduceIte, OracleComp.interpret_map, OracleComp.interpret_query,
        Scheme.simFilterHandler, Scheme.simFilterDispatch, ROQuery.dispatch, ← hxw]
      refine Represents.map_left ?_
      obtain ⟨b, m, c⟩ := x
      cases b with
      | true =>
        exact represents_simHashHRaw n (true, m, c)
      | false =>
        simp only [Scheme.simHashH, hKeyEmb_apply]
        refine (represents_simHashG n m).bind fun r => ?_
        have hiff := toCiphertext_inj (P := P) (hfit _ _ (List.length_ofFn (f := m))
          (List.length_ofFn (f := r))) c.2
        rw [show P.toCiphertext n c.val = c from Subtype.ext (toCiphertext_val c.2)] at hiff
        split_ifs with h₁ h₂ h₂
        · exact represents_simHashHq n c
        · exact absurd (hiff.mp h₁) h₂
        · exact absurd (hiff.mpr h₂) h₁
        · exact represents_simHashHRaw n (false, m, c)
    · simp only [typedHQuery_of_not_isHQuery hq, hq, Bool.false_eq_true, ↓reduceIte,
        OracleComp.interpret_pure]
      exact Represents.pure []
  | decaps =>
    simp only [typedQuery, simFilterWordHandler_decaps]
    by_cases hw : w.length ≤ P.ctLen n
    · simp only [hw, ↓reduceIte, OracleComp.interpret_map, OracleComp.interpret_query,
        Scheme.simFilterHandler, Scheme.simFilterDispatch, ROQuery.dispatch, filterDecaps_true]
      by_cases hc : w = cStar.val
      · have hc' : P.toCiphertext n w = cStar := Subtype.ext (by rw [toCiphertext_val hw, hc])
        simp only [hc', ↓reduceIte]
        simp only [hc, ↓reduceIte, map_pure, Option.map_none]
        exact Represents.pure []
      · have hc' : P.toCiphertext n w ≠ cStar := fun h => hc (by rw [← h, toCiphertext_val hw])
        simp only [hc', hc, ↓reduceIte]
        have h := represents_simHashHq (keyLen := keyLen) n (P.toCiphertext n w)
        rw [toCiphertext_val hw] at h
        exact Represents.map_left (Represents.map_left
          ((h.map_right (g := some)).map_right (g := ⇑(encOption encBits)) |>.congr_fun
            fun _ => rfl))
    · simp only [hw, ↓reduceIte, OracleComp.interpret_pure]
      exact Represents.pure []

/-! ### Replaying the saved coins -/

/-- Replaying a coin-tape machine with typed queries against a typed handler represents its replay
with word queries against a word handler, when every typed query represents the word call. -/
private theorem run_runCoins_typedQuery {σ σ' : Type} (n : ℕ) (rep : σ' → σ)
    (handler' : (q : ROQuery (BitString (P.msgLen n)) (P.Ciphertext n)) →
      StateT σ' ProbComp (ROResp (BitString (P.coinLen n)) (BitString (keyLen n)) q))
    (handler : CCAOp × List Bool → StateT σ ProbComp (List Bool))
    (hstep : ∀ op w, Represents rep id (OracleComp.interpret handler' (P.typedQuery keyLen n op w))
      (handler (op, w)))
    {k : ℕ} {Control : Type} (machine : _root_.Turing.MultiTapePTM k Bool Control CCAOp)
    (tape input : List Bool) (s : σ') :
    (ProbComp.eval ((OracleComp.interpret handler'
        (machine.runCoins (P.typedQuery keyLen n) tape input)).run s)).map
        (fun p => (p.1, rep p.2)) =
      ProbOracleComp.runWith (fun q st => ProbComp.eval (handler q st))
        (machine.runCoins (fun op w => ProbOracleComp.query (op, w)) tape input) (rep s) := by
  let W := machine.runCoins
    (fun op w => OracleComp.query (spec := fun _ : CCAOp × List Bool => List Bool) (op, w))
    tape input
  have h₁ : machine.runCoins (P.typedQuery keyLen n) tape input =
      OracleComp.interpret (fun q => P.typedQuery keyLen n q.1 q.2) W := by
    simp only [W, _root_.Turing.MultiTapePTM.interpret_runCoins, OracleComp.interpret_query]
  have h₂ : machine.runCoins (fun op w => ProbOracleComp.query (op, w)) tape input =
      OracleComp.interpret (fun q => ProbOracleComp.query q) W := by
    simp only [W, _root_.Turing.MultiTapePTM.interpret_runCoins, OracleComp.interpret_query]
  rw [h₁, h₂, OracleComp.interpret_interpret,
    OracleComp.map_run_interpret ProbComp.isMonadHom_eval, ProbOracleComp.runWith,
    OracleComp.runWith, OracleComp.interpret_interpret]
  simp only [ProbOracleComp.interpret_query]
  exact OracleComp.run_interpret_map_state _ _ rep (fun q st => hstep q.1 q.2 st) W s

/-- The challenge words of the saved-coin budget at parameter `n`: a generated public key, a
uniform key of length `keyLen n` and an encryption of a uniform message, as the word
`encKEMChallenge (pk, k, c)`. Every challenge of the word game and of the reduction's simulator
lies in its support. -/
private noncomputable def challengeWords (P : WordPKE) (keyLen : ℕ → ℕ) (n : ℕ) :
    ProbComp (List Bool × Unit) := do
  let pk ← Prod.fst <$> P.keyGen n
  let m ← BitString.sampleList (P.msgLen n)
  let c ← P.encrypt n pk m
  let k ← BitString.sampleList (keyLen n)
  return (Encryption.encKEMChallenge (pk, k, c), ())

private theorem isPPTOn_challengeWords (hP : P.IsEfficient)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsPPTOn encUnary (encPair encBits encUnit) (challengeWords P keyLen) := by
  -- On `(1ⁿ, pk)`: encrypt a uniform message of length `msgLen n`.
  have hc : IsPPTOn (encPair encUnary encBits) encBits (fun x : ℕ × List Bool => do
      let m ← BitString.sampleList (P.msgLen x.1)
      P.encrypt x.1 x.2 m) :=
    (hP.msgLen.comp (ComputableInPolyTime.fst _ _)).sampleList.bind_with
      (hP.isPPTOn_encrypt.preprocess
        (prepare := fun y : (ℕ × List Bool) × List Bool => (y.1.1, y.1.2, y.2)) (by fun_prop))
  -- On `((1ⁿ, pk), c)`: draw a uniform key and write the challenge word.
  have hk : IsPPTOn (encPair (encPair encUnary encBits) encBits) (encPair encBits encUnit)
      (fun y : (ℕ × List Bool) × List Bool =>
        (fun k => (Encryption.encKEMChallenge (y.1.2, k, y.2), ())) <$>
          BitString.sampleList (keyLen y.1.1)) :=
    (hkeyLen.comp (by fun_prop)).sampleList.map_with
      ((ComputableInPolyTime.encoding_comp (by fun_prop)).prod (by fun_prop))
  refine ((hP.keyGen.map (ComputableInPolyTime.fst _ _)).bind_with (second := fun n pk =>
      (do let m ← BitString.sampleList (P.msgLen n); P.encrypt n pk m) >>= fun c =>
        (fun k => (Encryption.encKEMChallenge (pk, k, c), ())) <$> BitString.sampleList (keyLen n))
    (hc.bind_with hk)).congr fun n => ?_
  simp only [challengeWords, bind_assoc, bind_pure_comp]

/-- Every challenge word of the games is a challenge word of `challengeWords`. -/
private theorem mem_support_challengeWords {n : ℕ} {pk sk : List Bool}
    (hkeys : (pk, sk) ∈ (ProbComp.eval (P.keyGen n)).support) (m : BitString (P.msgLen n))
    (r : BitString (P.coinLen n)) (k : BitString (keyLen n)) :
    (Encryption.encKEMChallenge (pk, List.ofFn k, P.encDet n pk (List.ofFn m) (List.ofFn r)),
      ()) ∈ (ProbComp.eval (challengeWords P keyLen n)).support := by
  simp only [challengeWords, encrypt, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.support_bind, PMF.support_map, PMF.support_pure, Set.mem_iUnion, Set.mem_image,
    Set.mem_singleton_iff, BitString.eval_sampleList, BitString.mem_support_uniformList_iff,
    exists_prop, exists_exists_and_eq_and]
  exact ⟨(pk, sk), hkeys, List.ofFn m, by simp, P.encDet n pk (List.ofFn m) (List.ofFn r),
    ⟨List.ofFn r, by simp, rfl⟩, List.ofFn k, by simp, rfl⟩

/-- **Saved coins of a native adversary.** For an efficient PKE family and a polynomial-time key
length, every uniform strict oracle PPT adversary has a coin-tape machine and polynomial clocks
such that, on every challenge of the word games, running the adversary against any word handler
is drawing the coins of `savedCoinAdversary` and running it against any typed handler that
represents the word handler query by query. -/
private theorem exists_savedCoins (hP : P.IsEfficient)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {A : ℕ → List Bool → WordOracleComp CCAOp Bool} (hA : IsOraclePPT encBool A) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : _root_.Turing.MultiTapePTM k Bool Control CCAOp) (c d keyC keyD : ℕ),
      ∀ n (pk : List Bool) (ct : P.Ciphertext n) (key : BitString (keyLen n)),
        (Encryption.encKEMChallenge (pk, List.ofFn key, ct.val), ()) ∈
          (ProbComp.eval (challengeWords P keyLen n)).support →
        ∀ {σ σ' : Type} (rep : σ' → σ)
          (handler' : (q : ROQuery (BitString (P.msgLen n)) (P.Ciphertext n)) →
            StateT σ' ProbComp (ROResp (BitString (P.coinLen n)) (BitString (keyLen n)) q))
          (handler : CCAOp × List Bool → StateT σ ProbComp (List Bool)),
          (∀ op w, Represents rep id
            (OracleComp.interpret handler' (P.typedQuery keyLen n op w)) (handler (op, w))) →
          ∀ s : σ',
            ProbOracleComp.runWith (fun q st => ProbComp.eval (handler q st))
                (A n (Encryption.encKEMChallenge (pk, List.ofFn key, ct.val))) (rep s) =
              (ProbComp.eval (P.savedCoinAdversary keyLen machine c d keyC keyD n).coins).bind
                fun ω => (ProbComp.eval ((OracleComp.interpret handler'
                  ((P.savedCoinAdversary keyLen machine c d keyC keyD n).run ω ⟨pk, ct, key⟩)).run
                    s)).map fun p => (p.1, rep p.2) := by
  obtain ⟨k, Control, hfinite, machine, c, d, keyC, keyD, hkeys, -, -, hrun⟩ :=
    hA.exists_savedCoins_of_keyGen (isPPTOn_challengeWords hP hkeyLen)
  refine ⟨k, Control, hfinite, machine, c, d, keyC, keyD, ?_⟩
  intro n pk ct key hmem σ σ' rep handler' handler hstep s
  have hlen : (Encryption.encKEMChallenge (pk, List.ofFn key, ct.val)).length ≤
      keyC * (n + 1) ^ keyD := hkeys n _ hmem
  have hdecode (x : PMF (Bool × σ)) :
      (x.map (Prod.map encBool id)).map (Prod.map Decoder.bool.decode id) = x := by
    rw [PMF.map_comp]
    convert PMF.map_id x
    funext p
    exact Prod.ext (Decoder.bool.decode_enc _) rfl
  rw [← hdecode (ProbOracleComp.runWith _ _ _), ← ProbOracleComp.runWith_map, hrun n _ hlen,
    PMF.map_bind]
  simp only [savedCoinAdversary, BitString.eval_sampleList]
  congr 1
  funext ω
  simp only [hlen, ↓reduceIte]
  rw [OracleComp.interpret_map, StateT.run_map, ProbComp.eval_map, PMF.map_comp,
    ← run_runCoins_typedQuery n rep handler' handler hstep, PMF.map_comp]
  rfl

/-- Each typed query makes at most one call. -/
private theorem isQueryBounded_typedQuery (n : ℕ) (op : CCAOp) (w : List Bool) :
    OracleComp.IsQueryBounded (P.typedQuery keyLen n op w) 1 := by
  cases op with
  | G =>
    simp only [typedQuery]
    split
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    · exact .pure _ _
  | H =>
    simp only [typedQuery]
    split
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    · exact .pure _ _
  | decaps =>
    simp only [typedQuery]
    split
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    · exact .pure _ _

/-- **Query bounds of the saved-coin view.** Every coin value and challenge makes at most
`c * (2 n + 2 + keyC (n + 1) ^ keyD) ^ d` queries to `G` and as many to `H`. -/
theorem savedCoinAdversary_queryBounds {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control CCAOp) (c d keyC keyD n : ℕ) :
    (P.savedCoinAdversary keyLen machine c d keyC keyD n).QueryBounds
      (c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d)
      (c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d) := by
  intro ω ch
  change List Bool at ω
  obtain ⟨pk, ct, key⟩ := ch
  have htotal : OracleComp.IsQueryBounded
      ((P.savedCoinAdversary keyLen machine c d keyC keyD n).run ω ⟨pk, ct, key⟩)
      (c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d) := by
    simp only [savedCoinAdversary]
    split
    · rename_i hlen
      apply (OracleComp.isCostBounded_map_iff _ _ _).mpr
      apply (machine.isCostBounded_runCoins (P.typedQuery keyLen n) 1
        (isQueryBounded_typedQuery n) _ _).mono
      simp only [List.length_take, Nat.mul_one]
      apply (Nat.min_le_left _ _).trans
      apply Nat.mul_le_mul_left c
      apply Nat.pow_le_pow_left
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at *
      omega
    · exact .pure _ _
  exact ⟨htotal.of_le fun q => by cases q <;> simp, htotal.of_le fun q => by cases q <;> simp⟩

/-! ### The word game as the typed game -/

/-- Native key generation is typed key generation with the fallback seed read as a word. -/
private theorem eval_keyGenNotBot (n : ℕ) :
    ProbComp.eval (P.keyGenNotBot keyLen n) =
      (ProbComp.eval (P.finiteScheme keyLen n).keyGenNotBot).map
        fun x => (x.1, skRep P n x.2) := by
  simp only [keyGenNotBot, Scheme.keyGenNotBot, scheme, toExplicitCoin, finiteScheme, finitePKE,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, BitString.eval_sampleList,
    uniformList_eq_map_ofFn, PMF.bind_map]
  congr 1
  funext ⟨pk, sk⟩
  simp [PMF.pure_map, skRep, Function.comp_def]

private theorem eval_roHashG_nil {M R CT K : Type} [DecidableEq M] (d : ProbComp R) (m : M)
    (h : List ((Bool × M × CT) × K)) :
    ProbComp.eval (roHashG (CT := CT) (K := K) d m { gCache := [], hCache := h }) =
      (ProbComp.eval d).map fun r => (r, { gCache := [(m, r)], hCache := h }) := by
  simp [roHashG, RandomOracle.zoomStateT, memoize, PMF.map]

private theorem eval_roHashH_nil {M R CT K : Type} [DecidableEq M] [DecidableEq CT]
    (d : ProbComp K) (x : Bool × M × CT) (g : List (M × R)) :
    ProbComp.eval (roHashH (M := M) (R := R) d x { gCache := g, hCache := [] }) =
      (ProbComp.eval d).map fun k => (k, { gCache := g, hCache := [(x, k)] }) := by
  simp [roHashH, RandomOracle.zoomStateT, memoize, PMF.map]

/-- **Native encapsulation against fresh random oracles** draws a uniform message, coins and
key, and leaves the caches of the typed challenge, at a key whose ciphertexts fit. -/
private theorem eval_run_withRO_encaps {n : ℕ} {pk : List Bool}
    (hfit : ∀ m r, m.length = P.msgLen n → r.length = P.coinLen n →
      (P.encDet n pk m r).length ≤ P.ctLen n) :
    ProbComp.eval ((P.withRO keyLen n (P.encaps keyLen n pk)).run {}) =
      (ProbComp.eval (ProbComp.uniform (BitString (P.msgLen n)))).bind fun m =>
      (ProbComp.eval (ProbComp.uniform (BitString (P.coinLen n)))).bind fun r =>
      (ProbComp.eval (ProbComp.uniform (BitString (keyLen n)))).bind fun k =>
        PMF.pure ((((P.finitePKE n).encDet pk m r).val, List.ofFn k),
          cacheRep P keyLen n
            ⟨[(m, r)], [((false, m, (P.finitePKE n).encDet pk m r), k)]⟩) := by
  rw [withRO, ProbOracleComp.eval_run_interpret_eq_runWith]
  simp only [encaps, ProbOracleComp.runWith_sample_bind, BitString.eval_sampleList,
    uniformList_eq_map_ofFn, PMF.bind_map]
  congr 1
  funext m
  have hG : ProbOracleComp.runWith
      (fun q st => ProbComp.eval (P.roWordOracle keyLen n q st)) (P.queryG n (List.ofFn m)) {} =
      (ProbComp.eval (ProbComp.uniform (BitString (P.coinLen n)))).map fun r =>
        (List.ofFn r, { gCache := [(List.ofFn m, List.ofFn r)] }) := by
    simp only [queryG, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, roWordOracle_G,
      List.length_ofFn, ↓reduceIte]
    rw [eval_roHashG_nil, BitString.eval_sampleList, uniformList_eq_map_ofFn, PMF.map_comp,
      PMF.map_comp]
    congr 1
    funext r
    simp
  simp only [Function.comp_def, ProbOracleComp.runWith_bind, hG, PMF.bind_map]
  congr 1
  funext r
  have hc := hfit _ _ (List.length_ofFn (f := m)) (List.length_ofFn (f := r))
  have hx := isHQuery_encHQuery (P := P) n (false, m, P.toCiphertext n
    (P.encDet n pk (List.ofFn m) (List.ofFn r)))
  rw [hKeyEmb_apply, toCiphertext_val hc] at hx
  simp only [queryH, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, roWordOracle_H,
    hx, ↓reduceIte, hQueryDecoder.decode_enc, ProbOracleComp.runWith_pure]
  change PMF.bind (PMF.map _ (ProbComp.eval (roHashH _ _ { gCache := _, hCache := [] }))) _ = _
  rw [eval_roHashH_nil, BitString.eval_sampleList, uniformList_eq_map_ofFn, PMF.map_comp,
    PMF.map_comp, PMF.bind_map]
  congr 1
  funext k
  have hk : List.take (keyLen n) (List.ofFn k) = List.ofFn k := List.take_of_length_le (by simp)
  simp [cacheRep, finitePKE, toCiphertext_val hc, hKeyEmb_apply, ofFnEmb, hk]

private theorem mem_support_finiteKeyGenNotBot {n : ℕ} {pk : List Bool}
    {dk : ImplicitSK (List Bool) (List Bool) (BitString (P.msgLen n))}
    (h : (pk, dk) ∈ (ProbComp.eval (P.finiteScheme keyLen n).keyGenNotBot).support) :
    dk.pk = pk ∧ (pk, dk.sk) ∈ (ProbComp.eval (P.keyGen n)).support := by
  simp only [Scheme.keyGenNotBot, finiteScheme, finitePKE, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.support_bind, PMF.support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff, exists_prop] at h
  obtain ⟨⟨pk', sk'⟩, hkeys, s, -, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨rfl, hkeys⟩

/-- **The word game is the typed game** of the saved-coin view, at a parameter where the
adversary's saved coins replay it. -/
private theorem eval_romIndCcaGameWord_eq {n : ℕ} (hfit : P.CiphertextFits)
    {A : ℕ → List Bool → WordOracleComp CCAOp Bool} {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control CCAOp) (c d keyC keyD : ℕ)
    (hreplay : ∀ (pk : List Bool) (ct : P.Ciphertext n) (key : BitString (keyLen n)),
        (Encryption.encKEMChallenge (pk, List.ofFn key, ct.val), ()) ∈
          (ProbComp.eval (challengeWords P keyLen n)).support →
        ∀ {σ σ' : Type} (rep : σ' → σ)
          (handler' : (q : ROQuery (BitString (P.msgLen n)) (P.Ciphertext n)) →
            StateT σ' ProbComp (ROResp (BitString (P.coinLen n)) (BitString (keyLen n)) q))
          (handler : CCAOp × List Bool → StateT σ ProbComp (List Bool)),
          (∀ op w, Represents rep id
            (OracleComp.interpret handler' (P.typedQuery keyLen n op w)) (handler (op, w))) →
          ∀ s : σ',
            ProbOracleComp.runWith (fun q st => ProbComp.eval (handler q st))
                (A n (Encryption.encKEMChallenge (pk, List.ofFn key, ct.val))) (rep s) =
              (ProbComp.eval (P.savedCoinAdversary keyLen machine c d keyC keyD n).coins).bind
                fun ω => (ProbComp.eval ((OracleComp.interpret handler'
                  ((P.savedCoinAdversary keyLen machine c d keyC keyD n).run ω ⟨pk, ct, key⟩)).run
                    s)).map fun p => (p.1, rep p.2))
    (b : Bool) :
    ProbComp.eval (P.romIndCcaGameWord keyLen A b n) =
      ProbComp.eval ((P.savedCoinAdversary keyLen machine c d keyC keyD n).play
        (P.finiteScheme keyLen n).roIndCcaGame b) := by
  simp only [romIndCcaGameWord, RandomizedROAdversary.play, Scheme.roIndCcaGame,
    ProbComp.eval_bind, eval_keyGenNotBot, PMF.bind_map]
  rw [PMF.bind_comm (ProbComp.eval (P.savedCoinAdversary keyLen machine c d keyC keyD n).coins)]
  apply PMF.bind_congr_on_support
  rintro ⟨pk, dk⟩ hx
  obtain ⟨hpk, hkeys⟩ := mem_support_finiteKeyGenNotBot hx
  have hfit' := hfit n pk dk.sk hkeys
  simp only [Function.comp_def]
  rw [eval_run_withRO_encaps hfit']
  simp only [PMF.bind_bind, PMF.pure_bind, BitString.eval_sampleList, uniformList_eq_map_ofFn,
    PMF.bind_map, Function.comp_def, ProbOracleComp.eval_run_interpret_eq_runWith,
    finiteScheme_pke, finiteScheme_sampleMsg, finiteScheme_sampleKey, finitePKE_sampleCoins,
    ProbComp.eval_pure]
  have hite (x y : BitString (keyLen n)) :
      (if b = true then List.ofFn x else List.ofFn y) = List.ofFn (if b = true then x else y) := by
    split <;> rfl
  have hct (m : BitString (P.msgLen n)) (r : BitString (P.coinLen n)) :
      ((P.finitePKE n).encDet pk m r).val = P.encDet n pk (List.ofFn m) (List.ofFn r) :=
    toCiphertext_val (hfit' _ _ (by simp) (by simp))
  have hfitdk : ∀ m r, m.length = P.msgLen n → r.length = P.coinLen n →
      (P.encDet n dk.pk m r).length ≤ P.ctLen n := by
    rw [hpk]
    exact hfit'
  have hrun (m : BitString (P.msgLen n)) (r : BitString (P.coinLen n))
      (kR kStar : BitString (keyLen n)) :=
    hreplay pk ((P.finitePKE n).encDet pk m r) kStar
      (by rw [hct]; exact mem_support_challengeWords hkeys m r kStar)
      (cacheRep P keyLen n) ((P.finiteScheme keyLen n).roHandler dk ((P.finitePKE n).encDet pk m r))
      (P.ccaWordOracle keyLen n (skRep P n dk) ((P.finitePKE n).encDet pk m r).val)
      (represents_ccaWordOracle dk _ hfitdk)
      ⟨[(m, r)], [((false, m, (P.finitePKE n).encDet pk m r), kR)]⟩
  simp only [hite, hrun, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  pmf_swap

/-! ### The reduction's IND-CPA game as the typed IND-CPA game -/

private theorem lookup_simRep_isSome (n : ℕ)
    (st : SimState (BitString (P.msgLen n)) (BitString (P.coinLen n)) (P.Ciphertext n)
      (BitString (keyLen n))) (m : BitString (P.msgLen n)) :
    ((simRep P keyLen n st).gCache.lookup (List.ofFn m)).isSome = (st.gCache.lookup m).isSome := by
  apply Bool.eq_iff_iff.mpr
  simp [simRep, ofFnEmb, List.lookup_isSome_iff, List.ofFn_inj]

/-- **The reduction's game is the typed IND-CPA game** of the typed reduction of the saved-coin
view, at a parameter where the adversary's saved coins replay it. -/
private theorem eval_gameOn_romCpaReductionWord_eq {n : ℕ} (hfit : P.CiphertextFits)
    {A : ℕ → List Bool → WordOracleComp CCAOp Bool} {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control CCAOp) (c d keyC keyD : ℕ)
    (hreplay : ∀ (pk : List Bool) (ct : P.Ciphertext n) (key : BitString (keyLen n)),
        (Encryption.encKEMChallenge (pk, List.ofFn key, ct.val), ()) ∈
          (ProbComp.eval (challengeWords P keyLen n)).support →
        ∀ {σ σ' : Type} (rep : σ' → σ)
          (handler' : (q : ROQuery (BitString (P.msgLen n)) (P.Ciphertext n)) →
            StateT σ' ProbComp (ROResp (BitString (P.coinLen n)) (BitString (keyLen n)) q))
          (handler : CCAOp × List Bool → StateT σ ProbComp (List Bool)),
          (∀ op w, Represents rep id
            (OracleComp.interpret handler' (P.typedQuery keyLen n op w)) (handler (op, w))) →
          ∀ s : σ',
            ProbOracleComp.runWith (fun q st => ProbComp.eval (handler q st))
                (A n (Encryption.encKEMChallenge (pk, List.ofFn key, ct.val))) (rep s) =
              (ProbComp.eval (P.savedCoinAdversary keyLen machine c d keyC keyD n).coins).bind
                fun ω => (ProbComp.eval ((OracleComp.interpret handler'
                  ((P.savedCoinAdversary keyLen machine c d keyC keyD n).run ω ⟨pk, ct, key⟩)).run
                    s)).map fun p => (p.1, rep p.2))
    (bit : Bool) :
    ProbComp.eval (Encryption.gameOn P.IsMessagePair P.keyGen P.encrypt
        (P.romCpaReductionWord keyLen A) bit n) =
      ProbComp.eval ((P.finitePKE n).toPKE.cpaExperiment (fun _ _ _ => true)
        ((P.finiteScheme keyLen n).romCpaReduction
          (P.savedCoinAdversary keyLen machine c d keyC keyD n)) bit) := by
  simp only [Encryption.gameOn, PKE.cpaExperiment, ProbComp.eval_bind, eval_lrExperiment,
    ExplicitCoinPKE.toPKE, Scheme.romCpaReduction, Scheme.romFilterCpaReduction,
    romCpaReductionWord, romFilterCpaReductionWord, finitePKE_keyGen]
  apply PMF.bind_congr_on_support
  rintro ⟨pk, sk⟩ hkeys
  have hfit' := hfit n pk sk hkeys
  have hvalid (m₀ m₁ : BitString (P.msgLen n)) :
      P.IsMessagePair n pk (List.ofFn m₀) (List.ofFn m₁) = true := by
    simp [IsMessagePair]
  simp only [Encryption.ChoiceOut.msg₀_mk, Encryption.ChoiceOut.msg₁_mk, hvalid, Decoder.decode_enc,
    ↓reduceIte, encrypt, ExplicitCoinPKE.encrypt, simFilterWordHit, Scheme.simFilterHit,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, uniformList_eq_map_ofFn,
    PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, finiteScheme_sampleKey,
    finiteScheme_sampleMsg, finitePKE_sampleCoins, ProbOracleComp.eval_run_interpret_eq_runWith]
  have hsel (m₀ m₁ : BitString (P.msgLen n)) :
      (if bit = true then List.ofFn m₁ else List.ofFn m₀) =
        List.ofFn (({ msg₀ := m₀, msg₁ := m₁ } : MessagePair _).select bit) := by
    cases bit <;> rfl
  have hct (m : BitString (P.msgLen n)) (r : BitString (P.coinLen n)) :
      P.encDet n pk (List.ofFn m) (List.ofFn r) = ((P.finitePKE n).encDet pk m r).val :=
    (toCiphertext_val (hfit' _ _ (by simp) (by simp))).symm
  have hrun (m : BitString (P.msgLen n)) (r : BitString (P.coinLen n))
      (kStar : BitString (keyLen n)) :
      ProbOracleComp.runWith (fun q st => ProbComp.eval (P.simFilterWordHandler keyLen
          (fun _ _ _ => true) n pk ((P.finitePKE n).encDet pk m r).val q st))
        (A n (Encryption.encKEMChallenge
          (pk, List.ofFn kStar, ((P.finitePKE n).encDet pk m r).val)))
        {} = _ :=
    hreplay pk ((P.finitePKE n).encDet pk m r) kStar
      (by rw [← hct]; exact mem_support_challengeWords hkeys m r kStar)
      (simRep P keyLen n)
      ((P.finiteScheme keyLen n).simFilterHandler (fun _ _ => true) pk
        ((P.finitePKE n).encDet pk m r))
      (P.simFilterWordHandler keyLen (fun _ _ _ => true) n pk ((P.finitePKE n).encDet pk m r).val)
      (represents_simFilterWordHandler pk _ hfit') {}
  simp only [hsel, hct, hrun, PMF.bind_bind, PMF.bind_map, Function.comp_def, lookup_simRep_isSome]
  pmf_swap

/-! ### The bridge -/

/-- **The typed bridge of the word-level FO family.** For an efficient PKE family and a
polynomial-time key length, every uniform strict oracle PPT ROM IND-CCA adversary `A` has a typed
view: at each parameter `n`, a randomized adversary `B n` of the typed ROM IND-CCA game of
`finiteScheme n`, with a polynomial bound `q` on its `G` and `H` queries. When the ciphertexts of
`P` fit its ciphertext space,

* the word game `romIndCcaGameWord A b n` has the law of `B n` playing the typed game
  `roIndCcaGame` of `finiteScheme n`, for both challenge bits;
* the advantage of the native reduction `romCpaReductionWord A` in the IND-CPA game of `P` at `n`
  is the two-stage IND-CPA advantage of the typed reduction `romCpaReduction (B n)` against
  `finitePKE n`.

`B n` replays `A` on a saved coin tape of polynomial length (`savedCoinAdversary`). -/
theorem IsEfficient.exists_typedAdversary (hP : P.IsEfficient)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {A : ℕ → List Bool → WordOracleComp CCAOp Bool} (hA : IsOraclePPT encBool A) :
    ∃ (B : (n : ℕ) → RandomizedROAdversary (List Bool) (BitString (P.msgLen n))
        (BitString (P.coinLen n)) (P.Ciphertext n) (BitString (keyLen n))) (q : ℕ → ℕ),
      PolynomiallyBounded q ∧ (∀ n, (B n).QueryBounds (q n) (q n)) ∧
      (P.CiphertextFits → ∀ n,
        (∀ b, ProbComp.eval (P.romIndCcaGameWord keyLen A b n) =
          ProbComp.eval ((B n).play (P.finiteScheme keyLen n).roIndCcaGame b)) ∧
        Encryption.advantage (Encryption.gameOn P.IsMessagePair P.keyGen P.encrypt
            (P.romCpaReductionWord keyLen A)) n =
          (P.finitePKE n).cpaAdvantage ((P.finiteScheme keyLen n).romCpaReduction (B n))) := by
  obtain ⟨k, Control, -, machine, c, d, keyC, keyD, hrun⟩ := exists_savedCoins hP hkeyLen hA
  refine ⟨fun n => P.savedCoinAdversary keyLen machine c d keyC keyD n,
    fun n => c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d, by fun_prop,
    fun n => savedCoinAdversary_queryBounds machine c d keyC keyD n, fun hfit n =>
      ⟨fun b => eval_romIndCcaGameWord_eq hfit machine c d keyC keyD (hrun n) b, ?_⟩⟩
  simp only [Encryption.advantage, ExplicitCoinPKE.cpaAdvantage, Experiment.advantage,
    eval_gameOn_romCpaReductionWord_eq hfit machine c d keyC keyD (hrun n)]

end WordPKE

end Cslib.Crypto.Protocols.FujisakiOkamoto
