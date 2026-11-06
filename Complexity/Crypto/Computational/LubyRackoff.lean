/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomFunction.MultiKey
public import Complexity.Crypto.Computational.PseudorandomPermutation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Crypto.Negligible.Basic
import Complexity.Crypto.Protocols.Cipher.LubyRackoff
import Complexity.Foundations.Data.BitString.List.Operations
import Complexity.Languages.Probabilistic.Oracle.CoinFixing
import Complexity.Probability.PMF.Bind
import Complexity.Probability.Product

/-!
# The Luby–Rackoff block ciphers from a pseudorandom function

From a keyed family `family` with `n`-bit keys, inputs and outputs, the Luby–Rackoff cipher
`lubyRackoffCipher` ([BonehShoup2023], Section 4.5) has `3 * n`-bit keys `k₁ ++ k₂ ++ k₃` and
`2 * n`-bit blocks `u ++ v`. Encryption computes three Feistel rounds
`w = u ⊕ F(k₁, v)`, `x = v ⊕ F(k₂, w)`, `y = w ⊕ F(k₃, x)` and outputs `x ++ y`; decryption runs
the rounds backwards.

**Luby–Rackoff theorem** ([BonehShoup2023], Theorem 4.9): if `family` is a pseudorandom function,
the Luby–Rackoff cipher is a pseudorandom permutation
(`PseudorandomFunction.prp_lubyRackoffCipher`).
The proof follows the textbook. The 3-wise parallel composition of the PRF
(`PseudorandomFunction.multiKey`) replaces the three keyed rounds with independent random functions.
The adapter `lubyRackoffAdversary` turns a block-cipher adversary into a three-channel one, which
costs one oracle-PPT reduction (`isOraclePPT_lubyRackoffAdversary`). With random rounds, the
information-theoretic bound `LubyRackoff.advantage_feistel3RandomRoundsGame_idealPermGame_le`
compares the network with a uniform permutation of `2 * n`-bit blocks for deterministic adversaries;
fixing the private coins of the adversary (`ProbOracleComp.coinLaw`) transfers it to randomized
ones (`advantage_lubyRackoffRandomRounds_prpIdealGame_le`).

**Four rounds** ([LubyRackoff1988]; [KatzLindell2020], Proposition 6.29): the four-round cipher
`lubyRackoff4Cipher` (keys `k₁ ++ k₂ ++ k₃ ++ k₄`) is a strong pseudorandom permutation, secure
against adversaries that may also decrypt (`PseudorandomFunction.strongPRP_lubyRackoff4Cipher`);
strongly secure block ciphers are [BonehShoup2023], Section 4.1.3 and Exercise 4.9. The proof has
the same structure, with the bidirectional adapter `strongLubyRackoffAdversary`, four PRF channels
and the finite-group bound
`LubyRackoff.advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le`.

## Main definitions

* `Cslib.Crypto.feistelRoundWord`, `Cslib.Crypto.feistelNetworkWord`,
  `Cslib.Crypto.feistelNetworkWordInv`: Feistel rounds on words with round oracles.
* `Cslib.Crypto.lubyRackoffEncrypt`, `Cslib.Crypto.lubyRackoffDecrypt`,
  `Cslib.Crypto.lubyRackoffCipher`: the three-round Luby–Rackoff block cipher.
* `Cslib.Crypto.feistelRoundQuery`, `Cslib.Crypto.feistelNetworkQuery`,
  `Cslib.Crypto.feistelNetworkInvQuery`: Feistel rounds whose round functions are read from PRF
  channels.
* `Cslib.Crypto.lubyRackoffQuery`, `Cslib.Crypto.lubyRackoffAdversary`: the reduction to the
  three-key PRF games.
* `Cslib.Crypto.lubyRackoff4Encrypt`, `Cslib.Crypto.lubyRackoff4Decrypt`,
  `Cslib.Crypto.lubyRackoff4Cipher`: the four-round cipher.
* `Cslib.Crypto.strongLubyRackoffQuery`, `Cslib.Crypto.strongLubyRackoffAdversary`: the
  bidirectional reduction to the four-key PRF games.

## Main results

* `Cslib.Crypto.isOraclePPT_lubyRackoffAdversary`: the reduction is oracle PPT.
* `Cslib.Crypto.eval_prpRealGame_lubyRackoffCipher`: the real chosen-plaintext experiment is the
  real three-key experiment of the reduction.
* `Cslib.Crypto.advantage_lubyRackoffRandomRounds_prpIdealGame_le`: with random rounds, a
  `Q`-query adversary has advantage at most `2 * Q.choose 2 / 2 ^ n + Q.choose 2 / 4 ^ n` against a
  uniform permutation.
* `Cslib.Crypto.PseudorandomFunction.prp_lubyRackoffCipher`: the Luby–Rackoff theorem.
* `Cslib.Crypto.isOraclePPT_strongLubyRackoffAdversary`,
  `Cslib.Crypto.eval_strongPRPRealGame_lubyRackoff4Cipher`,
  `Cslib.Crypto.advantage_lubyRackoff4RandomRounds_strongPRPIdealGame_le`: the four-round
  reduction and the random-round bound `2 * Q.choose 2 / 2 ^ n + 2 * Q.choose 2 / 4 ^ n`.
* `Cslib.Crypto.PseudorandomFunction.strongPRP_lubyRackoff4Cipher`,
  `Cslib.Crypto.PseudorandomFunction.prp_lubyRackoff4Cipher`: the four-round cipher is a strong
  pseudorandom permutation, hence a pseudorandom permutation.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023]:
  Section 4.1.3 (p. 101), Exercise 4.9 (p. 169), Section 4.5 (printed pp. 141–147), Theorem 4.9
  (p. 143) and Exercise 4.26 (pp. 174–175).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020]:
  Proposition 6.29.
* [M. Luby, C. Rackoff, *How to Construct Pseudorandom Permutations from Pseudorandom
  Functions*][LubyRackoff1988].
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Feistel networks on words -/

/-- One Feistel round `a ++ b ↦ b ++ (a ⊕ g b)` on a word with `n`-bit halves. -/
@[expose] def feistelRoundWord (g : List Bool → List Bool) (n : ℕ) (block : List Bool) :
    List Bool :=
  block.drop n ++ List.zipWith Bool.xor (block.take n) (g (block.drop n))

/-- The inverse Feistel round `c ++ d ↦ (d ⊕ g c) ++ c` on a word with `n`-bit halves. -/
@[expose] def feistelInvRoundWord (g : List Bool → List Bool) (n : ℕ) (block : List Bool) :
    List Bool :=
  List.zipWith Bool.xor (block.drop n) (g (block.take n)) ++ block.take n

/-- Feistel rounds with the round oracles `gs`, applied in order. -/
@[expose] def feistelNetworkWord (gs : List (List Bool → List Bool)) (n : ℕ) (block : List Bool) :
    List Bool :=
  gs.foldl (fun word g => feistelRoundWord g n word) block

/-- Inverse Feistel rounds with the round oracles `gs`, applied in reverse order. -/
@[expose] def feistelNetworkWordInv (gs : List (List Bool → List Bool)) (n : ℕ)
    (block : List Bool) : List Bool :=
  gs.foldr (fun g word => feistelInvRoundWord g n word) block

/-- The halves of a `2 * n`-bit block. -/
private def splitBlock (n : ℕ) (block : List Bool) : BitString n × BitString n :=
  (BitString.ofList n (block.take n), BitString.ofList n (block.drop n))

/-- The block with the given halves. -/
private def joinBlock {n : ℕ} (halves : BitString n × BitString n) : List Bool :=
  List.ofFn halves.1 ++ List.ofFn halves.2

private theorem length_joinBlock {n : ℕ} (halves : BitString n × BitString n) :
    (joinBlock halves).length = 2 * n := by
  simp only [joinBlock, List.length_append, List.length_ofFn]; omega

private theorem joinBlock_splitBlock {n : ℕ} {block : List Bool} (hblock : block.length = 2 * n) :
    joinBlock (splitBlock n block) = block := by
  simp only [joinBlock, splitBlock]
  rw [BitString.ofFn_ofList (by simp only [List.length_take]; omega),
    BitString.ofFn_ofList (by simp only [List.length_drop]; omega), List.take_append_drop]

private theorem splitBlock_joinBlock {n : ℕ} (halves : BitString n × BitString n) :
    splitBlock n (joinBlock halves) = halves := by
  simp [splitBlock, joinBlock]

private theorem bitString_sub_eq_add {n : ℕ} (a b : BitString n) : a - b = a + b :=
  funext fun i => BooleanRing.sub_eq_add (a i) (b i)

/-- A word oracle `g` represents `f` on `n`-bit strings. -/
private abbrev Represents {n : ℕ} (g : List Bool → List Bool) (f : BitString n → BitString n) :
    Prop :=
  ∀ x, g (List.ofFn x) = List.ofFn (f x)

private theorem feistelRoundWord_joinBlock {n : ℕ} {g : List Bool → List Bool}
    {f : BitString n → BitString n} (h : Represents g f) :
    ∀ halves : BitString n × BitString n,
      feistelRoundWord g n (joinBlock halves) = joinBlock (LubyRackoff.feistelRound f halves)
  | ⟨_, _⟩ => by
    simp only [feistelRoundWord, joinBlock, LubyRackoff.feistelRound,
      List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn, h, ← BitString.ofFn_add]

private theorem feistelInvRoundWord_joinBlock {n : ℕ} {g : List Bool → List Bool}
    {f : BitString n → BitString n} (h : Represents g f) :
    ∀ halves : BitString n × BitString n,
      feistelInvRoundWord g n (joinBlock halves) =
        joinBlock (LubyRackoff.feistelInvRound f halves)
  | ⟨_, _⟩ => by
    simp only [feistelInvRoundWord, joinBlock, LubyRackoff.feistelInvRound,
      List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn, h, bitString_sub_eq_add,
      ← BitString.ofFn_add]

/-- Word-level Feistel rounds compute the Feistel network of the round functions they represent.
-/
private theorem feistelNetworkWord_joinBlock {n : ℕ} {gs : List (List Bool → List Bool)}
    {fs : List (BitString n → BitString n)} (h : List.Forall₂ Represents gs fs)
    (halves : BitString n × BitString n) :
    feistelNetworkWord gs n (joinBlock halves) =
      joinBlock (LubyRackoff.feistelNetwork fs halves) := by
  induction h generalizing halves with
  | nil => rfl
  | cons hg _ ih =>
    rw [feistelNetworkWord, List.foldl_cons, ← feistelNetworkWord, feistelRoundWord_joinBlock hg,
      ih, LubyRackoff.feistelNetwork_cons]; rfl

/-- Word-level inverse rounds compute the inverse Feistel network. -/
private theorem feistelNetworkWordInv_joinBlock {n : ℕ} {gs : List (List Bool → List Bool)}
    {fs : List (BitString n → BitString n)} (h : List.Forall₂ Represents gs fs)
    (halves : BitString n × BitString n) :
    feistelNetworkWordInv gs n (joinBlock halves) =
      joinBlock ((LubyRackoff.feistelNetwork fs).symm halves) := by
  induction h generalizing halves with
  | nil => rfl
  | cons hg _ ih =>
    rw [feistelNetworkWordInv, List.foldr_cons, ← feistelNetworkWordInv, ih,
      feistelInvRoundWord_joinBlock hg, LubyRackoff.feistelNetwork_cons]; rfl

/-! ### The cipher -/

section Cipher

variable (family : List Bool → List Bool → List Bool)

/-- Luby–Rackoff encryption of a block `u ++ v` under a key `k₁ ++ k₂ ++ k₃`
([BonehShoup2023], Section 4.5): three Feistel rounds keyed by the blocks of the key. -/
@[expose] def lubyRackoffEncrypt (n : ℕ) (key : List Bool) : List Bool → List Bool :=
  feistelNetworkWord
    [family (keyBlock n 0 key), family (keyBlock n 1 key), family (keyBlock n 2 key)] n

/-- Luby–Rackoff decryption of a block `x ++ y` under a key `k₁ ++ k₂ ++ k₃`
([BonehShoup2023], Section 4.5). -/
@[expose] def lubyRackoffDecrypt (n : ℕ) (key : List Bool) : List Bool → List Bool :=
  feistelNetworkWordInv
    [family (keyBlock n 0 key), family (keyBlock n 1 key), family (keyBlock n 2 key)] n

variable {family}

/-- The round function on `n`-bit strings induced by the `i`-th key block. -/
private def roundFunction (family : List Bool → List Bool → List Bool) (n i : ℕ)
    (key : List Bool) (x : BitString n) : BitString n :=
  BitString.ofList n (family (keyBlock n i key) (List.ofFn x))

private theorem represents_roundFunction
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n t i : ℕ} {key : List Bool} (hkey : key.length = t * n) (hi : i < t) :
    Represents (family (keyBlock n i key)) (roundFunction family n i key) := by
  intro x
  have hblock := length_keyBlock hkey hi
  rw [roundFunction, BitString.ofFn_ofList
    ((hlength _ _ (by rw [List.length_ofFn, hblock])).trans hblock)]

private theorem lubyRackoffEncrypt_eq
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {key block : List Bool} (hkey : key.length = 3 * n) (hblock : block.length = 2 * n) :
    lubyRackoffEncrypt family n key block =
      joinBlock (LubyRackoff.feistel3 (roundFunction family n 0 key) (roundFunction family n 1 key)
        (roundFunction family n 2 key) (splitBlock n block)) := by
  have hrep {i} (hi : i < 3) := represents_roundFunction hlength hkey hi
  conv_lhs => rw [← joinBlock_splitBlock hblock]
  exact feistelNetworkWord_joinBlock
    (.cons (hrep (by decide)) (.cons (hrep (by decide)) (.cons (hrep (by decide)) .nil))) _

private theorem lubyRackoffDecrypt_eq
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {key block : List Bool} (hkey : key.length = 3 * n) (hblock : block.length = 2 * n) :
    lubyRackoffDecrypt family n key block =
      joinBlock ((LubyRackoff.feistel3 (roundFunction family n 0 key)
        (roundFunction family n 1 key) (roundFunction family n 2 key)).symm
          (splitBlock n block)) := by
  have hrep {i} (hi : i < 3) := represents_roundFunction hlength hkey hi
  conv_lhs => rw [← joinBlock_splitBlock hblock]
  exact feistelNetworkWordInv_joinBlock
    (.cons (hrep (by decide)) (.cons (hrep (by decide)) (.cons (hrep (by decide)) .nil))) _

private theorem computableInPolyTime_feistelRoundWord {α : Type} {enc : α ↪ List Bool}
    {g : α → List Bool → List Bool} {n : α → ℕ} {block : α → List Bool}
    (hg : ∀ {q : α → List Bool}, ComputableInPolyTime q enc encBits →
      ComputableInPolyTime (fun a => g a (q a)) enc encBits)
    (hn : ComputableInPolyTime n enc encUnary)
    (hblock : ComputableInPolyTime block enc encBits) :
    ComputableInPolyTime (fun a => feistelRoundWord (g a) (n a) (block a)) enc encBits :=
  let hdrop := hblock.bitsDropWithInput hn
  hdrop.bitsAppend ((ComputableInPolyTime.bitsZipWith Bool.xor).comp
    ((hblock.bitsTakeWithInput hn).prod (hg hdrop)))

private theorem computableInPolyTime_feistelInvRoundWord {α : Type} {enc : α ↪ List Bool}
    {g : α → List Bool → List Bool} {n : α → ℕ} {block : α → List Bool}
    (hg : ∀ {q : α → List Bool}, ComputableInPolyTime q enc encBits →
      ComputableInPolyTime (fun a => g a (q a)) enc encBits)
    (hn : ComputableInPolyTime n enc encUnary)
    (hblock : ComputableInPolyTime block enc encBits) :
    ComputableInPolyTime (fun a => feistelInvRoundWord (g a) (n a) (block a)) enc encBits :=
  let htake := hblock.bitsTakeWithInput hn
  ((ComputableInPolyTime.bitsZipWith Bool.xor).comp
    ((hblock.bitsDropWithInput hn).prod (hg htake))).bitsAppend htake

private theorem computableInPolyTime_keyRound
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (i : ℕ) {q : ℕ × List Bool × List Bool → List Bool}
    (hq : ComputableInPolyTime q (encPair encUnary (encPair encBits encBits)) encBits) :
    ComputableInPolyTime (fun x => family (keyBlock x.1 i x.2.1) (q x))
      (encPair encUnary (encPair encBits encBits)) encBits :=
  let hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  let hk := (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).fst'
  hpoly.comp (((hk.bitsDropWithInput
    (ComputableInPolyTime.unary_mul' (.const i) hn)).bitsTakeWithInput hn).prod hq)

variable (family) in
/-- The three-round Luby–Rackoff block cipher with `3 * n`-bit keys and `2 * n`-bit blocks, built
from a length-preserving keyed family computable in polynomial time ([BonehShoup2023],
Section 4.5). -/
@[expose] def lubyRackoffCipher
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    BlockCipher where
  keyLen n := 3 * n
  blockLen n := 2 * n
  keyLen_polyTime := by exact ComputableInPolyTime.unary_mul' (.const 3) .id'
  blockLen_polyTime := by exact ComputableInPolyTime.unary_mul' (.const 2) .id'
  encrypt := lubyRackoffEncrypt family
  decrypt := lubyRackoffDecrypt family
  encrypt_polyTime := by
    have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
    have hb := (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd'
    exact computableInPolyTime_feistelRoundWord (computableInPolyTime_keyRound hpoly 2) hn
      (computableInPolyTime_feistelRoundWord (computableInPolyTime_keyRound hpoly 1) hn
        (computableInPolyTime_feistelRoundWord (computableInPolyTime_keyRound hpoly 0) hn hb))
  decrypt_polyTime := by
    have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
    have hb := (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd'
    exact computableInPolyTime_feistelInvRoundWord (computableInPolyTime_keyRound hpoly 0) hn
      (computableInPolyTime_feistelInvRoundWord (computableInPolyTime_keyRound hpoly 1) hn
        (computableInPolyTime_feistelInvRoundWord (computableInPolyTime_keyRound hpoly 2) hn hb))
  length_encrypt n key block hkey hblock := by
    rw [lubyRackoffEncrypt_eq hlength hkey hblock, length_joinBlock]
  length_decrypt n key block hkey hblock := by
    rw [lubyRackoffDecrypt_eq hlength hkey hblock, length_joinBlock]
  decrypt_encrypt n key block hkey hblock := by
    rw [lubyRackoffDecrypt_eq hlength hkey (by rw [lubyRackoffEncrypt_eq hlength hkey hblock,
      length_joinBlock]), lubyRackoffEncrypt_eq hlength hkey hblock, splitBlock_joinBlock,
      Equiv.symm_apply_apply, joinBlock_splitBlock hblock]
  encrypt_decrypt n key block hkey hblock := by
    rw [lubyRackoffEncrypt_eq hlength hkey (by rw [lubyRackoffDecrypt_eq hlength hkey hblock,
      length_joinBlock]), lubyRackoffDecrypt_eq hlength hkey hblock, splitBlock_joinBlock,
      Equiv.apply_symm_apply, joinBlock_splitBlock hblock]

end Cipher

/-! ### Feistel rounds through PRF channels -/

section Queries

variable {t : ℕ}

/-- One Feistel round on a word with `n`-bit halves, reading the round function from channel `i`.
The reply is cut at `n` bits, which changes nothing for replies of the declared length. -/
@[expose] def feistelRoundQuery (i : Fin t) (n : ℕ) (block : List Bool) :
    WordOracleComp (Fin t) (List Bool) :=
  (fun reply => block.drop n ++ List.zipWith Bool.xor (block.take n) reply) <$>
    (List.take n <$> ProbOracleComp.query (i, block.drop n))

/-- One inverse Feistel round on a word with `n`-bit halves, reading the round function from
channel `i`. -/
@[expose] def feistelInvRoundQuery (i : Fin t) (n : ℕ) (block : List Bool) :
    WordOracleComp (Fin t) (List Bool) :=
  (fun reply => List.zipWith Bool.xor (block.drop n) reply ++ block.take n) <$>
    (List.take n <$> ProbOracleComp.query (i, block.take n))

/-- Feistel rounds reading the round functions from the channels `rounds`, in order. -/
@[expose] def feistelNetworkQuery (rounds : List (Fin t)) (n : ℕ) (block : List Bool) :
    WordOracleComp (Fin t) (List Bool) :=
  rounds.foldlM (fun word i => feistelRoundQuery i n word) block

/-- Inverse Feistel rounds reading the round functions from the channels `rounds`, in reverse
order. -/
@[expose] def feistelNetworkInvQuery (rounds : List (Fin t)) (n : ℕ) (block : List Bool) :
    WordOracleComp (Fin t) (List Bool) :=
  rounds.foldrM (fun i word => feistelInvRoundQuery i n word) block

private theorem interpret_feistelRoundQuery (oracle : Fin t × List Bool → List Bool) (n : ℕ)
    (i : Fin t) (block : List Bool) :
    OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun request => PMF.pure (oracle request)))
        (feistelRoundQuery i n block) =
      PMF.pure (feistelRoundWord (fun query => (oracle (i, query)).take n) n block) := by
  simp [feistelRoundQuery, feistelRoundWord, PMF.monad_map_eq_map]

private theorem interpret_feistelInvRoundQuery (oracle : Fin t × List Bool → List Bool) (n : ℕ)
    (i : Fin t) (block : List Bool) :
    OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun request => PMF.pure (oracle request)))
        (feistelInvRoundQuery i n block) =
      PMF.pure (feistelInvRoundWord (fun query => (oracle (i, query)).take n) n block) := by
  simp [feistelInvRoundQuery, feistelInvRoundWord, PMF.monad_map_eq_map]

/-- Against deterministic channels, Feistel query rounds are word-level Feistel rounds whose
round oracles read the channels. -/
private theorem interpret_feistelNetworkQuery (oracle : Fin t × List Bool → List Bool) (n : ℕ)
    (rounds : List (Fin t)) (block : List Bool) :
    OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun request => PMF.pure (oracle request)))
        (feistelNetworkQuery rounds n block) =
      PMF.pure (feistelNetworkWord (rounds.map fun i query => (oracle (i, query)).take n) n
        block) := by
  induction rounds generalizing block with
  | nil => rfl
  | cons i rounds ih =>
    rw [feistelNetworkQuery, List.foldlM_cons, OracleComp.interpret_bind,
      interpret_feistelRoundQuery, Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
    exact ih _

private theorem interpret_feistelNetworkInvQuery (oracle : Fin t × List Bool → List Bool)
    (n : ℕ) (rounds : List (Fin t)) (block : List Bool) :
    OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun request => PMF.pure (oracle request)))
        (feistelNetworkInvQuery rounds n block) =
      PMF.pure (feistelNetworkWordInv (rounds.map fun i query => (oracle (i, query)).take n) n
        block) := by
  induction rounds generalizing block with
  | nil => rfl
  | cons i rounds ih =>
    have hrest := ih block
    unfold feistelNetworkInvQuery at hrest
    rw [feistelNetworkInvQuery, List.foldrM_cons, OracleComp.interpret_bind, hrest,
      Probability.PMF.monad_bind_eq_bind, PMF.pure_bind, interpret_feistelInvRoundQuery]
    rfl

private theorem isOraclePPTOn_feistelRoundQuery {α : Type} {input : α ↪ List Bool}
    (i : Fin t) {n : α → ℕ} {block : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hblock : ComputableInPolyTime block input encBits) :
    IsOraclePPTOn input encBits (fun a => feistelRoundQuery i (n a) (block a)) :=
  let hfst := ComputableInPolyTime.fst input encBits
  (IsOraclePPTOn.query_take' i (hblock.bitsDropWithInput hn) hn).map_with'
    (f := fun a reply => (block a).drop (n a) ++
      List.zipWith Bool.xor ((block a).take (n a)) reply)
    (computableInPolyTime_feistelRoundWord (g := fun p : α × List Bool => fun _ => p.2)
      (fun _ => ComputableInPolyTime.snd input encBits) (hfst.trans hn) (hfst.trans hblock))

private theorem isOraclePPTOn_feistelInvRoundQuery {α : Type} {input : α ↪ List Bool}
    (i : Fin t) {n : α → ℕ} {block : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hblock : ComputableInPolyTime block input encBits) :
    IsOraclePPTOn input encBits (fun a => feistelInvRoundQuery i (n a) (block a)) :=
  let hfst := ComputableInPolyTime.fst input encBits
  (IsOraclePPTOn.query_take' i (hblock.bitsTakeWithInput hn) hn).map_with'
    (f := fun a reply => List.zipWith Bool.xor ((block a).drop (n a)) reply ++
      (block a).take (n a))
    (computableInPolyTime_feistelInvRoundWord (g := fun p : α × List Bool => fun _ => p.2)
      (fun _ => ComputableInPolyTime.snd input encBits) (hfst.trans hn) (hfst.trans hblock))

private theorem isOraclePPTOn_feistelNetworkQuery (rounds : List (Fin t)) :
    ∀ {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {block : α → List Bool},
      ComputableInPolyTime n input encUnary → ComputableInPolyTime block input encBits →
      IsOraclePPTOn input encBits (fun a => feistelNetworkQuery rounds (n a) (block a)) := by
  induction rounds with
  | nil => exact fun _ hblock => hblock.isPPTOn.isOraclePPTOn (Operation := Fin t)
  | cons i rounds ih =>
    intro α input n block hn hblock
    exact (isOraclePPTOn_feistelRoundQuery i hn hblock).bind_with
      (second := fun a word => feistelNetworkQuery rounds (n a) word)
      (ih ((ComputableInPolyTime.fst input encBits).trans hn)
        (ComputableInPolyTime.snd input encBits))

private theorem isOraclePPTOn_feistelNetworkInvQuery (rounds : List (Fin t)) :
    ∀ {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {block : α → List Bool},
      ComputableInPolyTime n input encUnary → ComputableInPolyTime block input encBits →
      IsOraclePPTOn input encBits (fun a => feistelNetworkInvQuery rounds (n a) (block a)) := by
  induction rounds with
  | nil => exact fun _ hblock => hblock.isPPTOn.isOraclePPTOn (Operation := Fin t)
  | cons i rounds ih =>
    intro α input n block hn hblock
    simp only [feistelNetworkInvQuery, List.foldrM_cons]
    exact (ih hn hblock).bind_with (second := fun a word => feistelInvRoundQuery i (n a) word)
      (isOraclePPTOn_feistelInvRoundQuery i
        ((ComputableInPolyTime.fst input encBits).trans hn)
        (ComputableInPolyTime.snd input encBits))

/-- Feistel query rounds never lengthen a word. -/
private theorem length_le_of_mem_support_feistelNetworkQuery (rounds : List (Fin t)) (n : ℕ) :
    ∀ (block reply : List Bool), reply ∈ OracleComp.support (feistelNetworkQuery rounds n block) →
      reply.length ≤ block.length := by
  induction rounds with
  | nil =>
    intro block reply hreply
    simpa [feistelNetworkQuery, OracleComp.support] using congrArg List.length hreply |>.le
  | cons i rounds ih =>
    intro block reply hreply
    simp only [feistelNetworkQuery, List.foldlM_cons, OracleComp.mem_supportWith_bind_iff,
      feistelRoundQuery, OracleComp.mem_supportWith_map_iff] at hreply
    obtain ⟨_, ⟨_, ⟨raw, _, rfl⟩, rfl⟩, hrest⟩ := hreply
    refine (ih _ _ hrest).trans ?_
    simp only [List.length_append, List.length_drop, List.length_zipWith, List.length_take]; omega

/-- Inverse Feistel query rounds never lengthen a word. -/
private theorem length_le_of_mem_support_feistelNetworkInvQuery (rounds : List (Fin t))
    (n : ℕ) : ∀ (block reply : List Bool),
      reply ∈ OracleComp.support (feistelNetworkInvQuery rounds n block) →
      reply.length ≤ block.length := by
  induction rounds with
  | nil =>
    intro block reply hreply
    simpa [feistelNetworkInvQuery, OracleComp.support] using congrArg List.length hreply |>.le
  | cons i rounds ih =>
    intro block reply hreply
    simp only [feistelNetworkInvQuery, List.foldrM_cons, OracleComp.mem_supportWith_bind_iff,
      feistelInvRoundQuery, OracleComp.mem_supportWith_map_iff] at hreply
    obtain ⟨word, hword, _, ⟨raw, _, rfl⟩, rfl⟩ := hreply
    refine le_trans ?_ (ih _ _ hword)
    simp only [List.length_append, List.length_drop, List.length_zipWith, List.length_take]; omega

end Queries

/-- Substituting a stateless handler with its own oracle calls into an oracle-PPT adversary is
oracle PPT, when the handler is oracle PPT and its replies are bounded by an efficient allowance.
-/
private theorem isOraclePPT_interpret_handler {Operation External : Type} [DecidableEq Operation]
    [FinEnum Operation] [DecidableEq External] [Finite External]
    {adversary : ℕ → List Bool → WordOracleComp Operation Bool}
    (hadversary : IsOraclePPT encBool adversary)
    {handler : ℕ → Operation × List Bool → WordOracleComp External (List Bool)}
    (hhandler : IsOraclePPTOn
      (encPair (encPair encUnary encBits) (encPair (encFinEnum Operation) encBits)) encBits
      (fun x : (ℕ × List Bool) × (Operation × List Bool) => handler x.1.1 x.2))
    {resources : ℕ → List Bool → ℕ}
    (hresources : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => resources pair.1.1 pair.2)
      (encPair (encPair encUnary encBits) encBits) encUnary)
    (hreply : ∀ n request, ∀ reply ∈ OracleComp.support (handler n request),
      reply.length ≤ resources n request.2) :
    IsOraclePPT encBool (fun n aux => OracleComp.interpret
      (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) (handler n))
      (adversary n aux)) := by
  have hfst := ComputableInPolyTime.fst (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Operation) encBits) (encFinEnum Unit))
  have hsnd := ComputableInPolyTime.snd (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Operation) encBits) (encFinEnum Unit))
  have hstate := (hhandler.preprocess' (hfst.prod hsnd.fst')).map'
    (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const (encOut := encFinEnum Unit) ()))
  have hrun := hadversary.run_interpret_preprocess_open' (External := External) (State := Unit)
    (input := encPair encUnary encBits) (operationEncoding := encFinEnum Operation)
    (stateEncoding := encFinEnum Unit)
    (handler := fun caller request (_ : Unit) =>
      (fun reply => (reply, ())) <$> handler caller.1 request)
    (prepare := id) (initial := fun _ => ())
    (resources := fun caller query => resources caller.1 query)
    ComputableInPolyTime.id' hstate (ComputableInPolyTime.const ()) (fun _ _ => True)
    (fun _ => trivial) hresources
    (fun caller request _ _ result hresult => by
      simp only [OracleComp.mem_supportWith_map_iff] at hresult
      obtain ⟨reply, hreply', rfl⟩ := hresult
      exact ⟨trivial, hreply caller.1 request reply hreply', by simp [encFinEnum]⟩)
  have h := hrun.map' (ComputableInPolyTime.fst encBool (encFinEnum Unit))
  refine IsOraclePPTOn.isOraclePPT ?_
  convert h using 1; funext ⟨n, aux⟩
  rw [show (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (fun request (_ : Unit) => (fun reply => (reply, ())) <$> handler n request)) =
      fun q => StateT.lift (OracleComp.sumHandler
        (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) (handler n) q) by
    funext q; rcases q with k | request
    · rfl
    · funext u; simp only [OracleComp.sumHandler, StateT.lift, bind_pure_comp],
    OracleComp.run_interpret_lift, Functor.map_map]
  exact (id_map _).symm

/-! ### The reduction to three PRF keys -/

/-- Answer one block query through three PRF channels, which provide the three Feistel rounds.
Malformed blocks are answered with `[]` without querying. -/
@[expose] def lubyRackoffQuery (n : ℕ) (block : List Bool) : WordOracleComp (Fin 3) (List Bool) :=
  if block.length = 2 * n then feistelNetworkQuery [0, 1, 2] n block else pure []

/-- Run a block-cipher adversary against three PRF channels, answering each block query with
`lubyRackoffQuery`. -/
@[expose] def lubyRackoffAdversary (adversary : OracleDistinguisher) : MultiKeyDistinguisher 3 :=
  fun n aux => OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun request => lubyRackoffQuery n request.2)) (adversary n aux)

/-- The adapter is oracle PPT for every oracle-PPT block-cipher adversary. -/
theorem isOraclePPT_lubyRackoffAdversary {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (lubyRackoffAdversary adversary) := by
  have hn := (ComputableInPolyTime.fst (encPair encUnary encBits)
    (encPair (encFinEnum Unit) encBits)).fst'
  have hblock := (ComputableInPolyTime.snd (encPair encUnary encBits)
    (encPair (encFinEnum Unit) encBits)).snd'
  refine isOraclePPT_interpret_handler hadversary
    (IsOraclePPTOn.ite'
      (ComputableInPolyTime.unary_eq' (hblock.trans ComputableInPolyTime.length_bits)
        (ComputableInPolyTime.unary_mul' (.const 2) hn))
      (isOraclePPTOn_feistelNetworkQuery [0, 1, 2] hn hblock)
      ((ComputableInPolyTime.const ([] : List Bool)).isPPTOn.isOraclePPTOn (Operation := Fin 3)))
    (resources := fun n _ => 2 * n)
    (ComputableInPolyTime.unary_mul' (.const 2)
      (ComputableInPolyTime.fst (encPair encUnary encBits) encBits).fst')
    fun n request reply hreply => ?_
  simp only [lubyRackoffQuery] at hreply
  split_ifs at hreply with hblock
  · exact (length_le_of_mem_support_feistelNetworkQuery _ _ _ _ hreply).trans hblock.le
  · simp only [OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hreply
    subst hreply; simp

/-- Interpreting the adapter against deterministic channels runs the block-cipher adversary
against the word-level Feistel rounds that read the channels. -/
private theorem interpret_lubyRackoffAdversary (adversary : OracleDistinguisher) (n : ℕ)
    (oracle : Fin 3 × List Bool → List Bool) :
    OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun request => PMF.pure (oracle request)))
        (lubyRackoffAdversary adversary n []) =
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun request =>
        PMF.pure (if request.2.length = 2 * n then
          feistelNetworkWord ([0, 1, 2].map fun i query => (oracle (i, query)).take n) n request.2
        else []))) (adversary n []) := by
  simp only [lubyRackoffAdversary, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
    ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
  congr 2; funext request; unfold lubyRackoffQuery; split_ifs
  · exact interpret_feistelNetworkQuery oracle n _ _
  · rfl

/-- Keyed channel replies, cut at `n` bits, represent the round functions of the key blocks. -/
private theorem represents_prfOracle_take {family : List Bool → List Bool → List Bool}
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n t i : ℕ} {key : List Bool} (hkey : key.length = t * n) (hi : i < t) :
    Represents (fun query => (prfOracle family n (keyBlock n i key) query).take n)
      (roundFunction family n i key) := fun x => by
  simp only [prfOracle, List.length_ofFn, ↓reduceIte]
  rw [represents_roundFunction hlength hkey hi x, List.take_of_length_le List.length_ofFn.le]

/-- The real chosen-plaintext experiment of the Luby–Rackoff cipher is the real three-key
experiment of the adapter. -/
theorem eval_prpRealGame_lubyRackoffCipher {family : List Bool → List Bool → List Bool}
    (hfamily : PseudorandomFunction family) (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval ((lubyRackoffCipher family hfamily.polyTime hfamily.length_eq).prpRealGame
        adversary n) =
      ProbComp.eval (prfMultiRealGame family 3 (lubyRackoffAdversary adversary) n) := by
  simp only [BlockCipher.prpRealGame, prfMultiRealGame, ProbComp.eval_bind,
    BitString.eval_sampleList, ProbOracleComp.eval_interpret, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
  have hkeyLength : key.length = 3 * n := BitString.length_of_mem_support_uniformList hkey
  rw [interpret_lubyRackoffAdversary]; congr 2; funext request; congr 1
  change (if request.2.length = 2 * n then lubyRackoffEncrypt family n key request.2 else []) = _
  split_ifs with hblock
  · rw [lubyRackoffEncrypt_eq hfamily.length_eq hkeyLength hblock]
    conv_rhs => rw [← joinBlock_splitBlock hblock]
    have hrep {i} (hi : i < 3) := represents_prfOracle_take hfamily.length_eq hkeyLength hi
    exact (feistelNetworkWord_joinBlock
      (.cons (hrep (by decide)) (.cons (hrep (by decide)) (.cons (hrep (by decide)) .nil))) _).symm
  · rfl

/-! ### Random rounds against a random permutation -/

/-- Read a function of pairs of `n`-bit strings on `2 * n`-bit words, answering other words with
`[]`. -/
private def blockOracle (n : ℕ) (σ : BitString n × BitString n → BitString n × BitString n)
    (block : List Bool) : List Bool :=
  if block.length = 2 * n then joinBlock (σ (splitBlock n block)) else []

/-- `2 * n`-bit strings as pairs of `n`-bit halves. -/
private def blockEquiv (n : ℕ) : BitString (2 * n) ≃ BitString n × BitString n where
  toFun z := splitBlock n (List.ofFn z)
  invFun halves := BitString.ofList (2 * n) (joinBlock halves)
  left_inv z := by dsimp only; rw [joinBlock_splitBlock List.length_ofFn, BitString.ofList_ofFn]
  right_inv h := by
    dsimp only; rw [BitString.ofFn_ofList (length_joinBlock h), splitBlock_joinBlock]

/-- A permutation of `2 * n`-bit strings reads as the corresponding permutation of halves. -/
private theorem randomPermOracle_eq_blockOracle (n : ℕ) (π : Equiv.Perm (BitString (2 * n)))
    (block : List Bool) :
    randomPermOracle (2 * n) π block = blockOracle n ((blockEquiv n).permCongr π) block := by
  unfold randomPermOracle randomFunctionOracle blockOracle
  split_ifs with hblock
  · simp only [Equiv.permCongr_apply, blockEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
      joinBlock_splitBlock hblock, joinBlock_splitBlock List.length_ofFn]
  · rfl

/-- The block-cipher adversary as a program querying pairs of `n`-bit halves; malformed queries
are answered with `[]` without querying. -/
private noncomputable def pairAdversary (adversary : OracleDistinguisher) (n : ℕ) :
    ProbOracleComp (fun _ : BitString n × BitString n => BitString n × BitString n) Bool :=
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun request : Unit × List Bool =>
        if request.2.length = 2 * n then joinBlock <$> ProbOracleComp.query (splitBlock n request.2)
        else pure []))
    (adversary n [])

private theorem isQueryBounded_pairAdversary {adversary : OracleDistinguisher} {n Q : ℕ}
    (hQ : (adversary n []).IsQueryBounded Q) : (pairAdversary adversary n).IsQueryBounded Q := by
  refine hQ.interpret fun q => ?_
  rcases q with k | request
  · exact ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin k)
  · dsimp only [OracleComp.sumHandler]; split_ifs
    · simpa only [map_eq_bind_pure_comp, Function.comp_def, Nat.add_zero, Sum.elim_inr] using
        (ProbOracleComp.IsQueryBounded.query (splitBlock n request.2)).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0
    · exact OracleComp.IsCostBounded.pure [] _

private theorem interpret_pairAdversary (adversary : OracleDistinguisher) (n : ℕ)
    (σ : BitString n × BitString n → BitString n × BitString n) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun p => PMF.pure (σ p)))
        (pairAdversary adversary n) =
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request : Unit × List Bool => PMF.pure (blockOracle n σ request.2)))
        (adversary n []) := by
  simp only [pairAdversary, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
    ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
  congr 2; funext request; unfold blockOracle; split_ifs <;> simp [PMF.monad_map_eq_map]

/-- With random round functions, the adapter runs the block-cipher adversary against the Feistel
network of three independent uniform random functions. -/
private theorem eval_prfMultiIdealGame_lubyRackoffAdversary (adversary : OracleDistinguisher)
    (n : ℕ) :
    ProbComp.eval (prfMultiIdealGame 3 (lubyRackoffAdversary adversary) n) =
      (PMF.uniformOfFintype (Fin 3 → BitString n → BitString n)).bind fun tables =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun p =>
          PMF.pure (LubyRackoff.feistel3 (tables 0) (tables 1) (tables 2) p)))
          (pairAdversary adversary n) := by
  simp only [prfMultiIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, interpret_pairAdversary]
  congr 1; funext tables; rw [interpret_lubyRackoffAdversary]; congr 2; funext request; congr 1
  unfold blockOracle; split_ifs with hblock
  · conv_lhs => rw [← joinBlock_splitBlock hblock]
    have hT (i : Fin 3) : Represents (fun q => (randomFunctionOracle n (tables i) q).take n)
        (tables i) := fun x => by
      simp only [randomFunctionOracle, List.length_ofFn, ↓reduceIte, BitString.ofList_ofFn]
      exact List.take_of_length_le List.length_ofFn.le
    exact feistelNetworkWord_joinBlock (.cons (hT 0) (.cons (hT 1) (.cons (hT 2) .nil))) _
  · rfl

/-- Three independent uniform draws are the coordinates of a uniform triple. -/
private theorem bind_uniformOfFintype_fin_three {X β : Type} [Fintype X] [Nonempty X]
    (F : X → X → X → PMF β) :
    (PMF.uniformOfFintype (Fin 3 → X)).bind (fun f => F (f 0) (f 1) (f 2)) =
      (PMF.uniformOfFintype X).bind fun a => (PMF.uniformOfFintype X).bind fun b =>
        (PMF.uniformOfFintype X).bind fun c => F a b c := by
  let e : X × X × X ≃ (Fin 3 → X) :=
    { toFun := fun t => ![t.1, t.2.1, t.2.2], invFun := fun f => (f 0, f 1, f 2)
      left_inv := fun _ => rfl, right_inv := fun f => by funext i; fin_cases i <;> rfl }
  rw [← PMF.uniformOfFintype_map_equiv e, PMF.bind_map, ← PMF.uniformOfFintype_prod,
    ← PMF.uniformOfFintype_prod]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]; rfl

/-- **Three random Feistel rounds against a random permutation**, for randomized word-oracle
adversaries ([BonehShoup2023], proof of Theorem 4.9): with independent uniform random round
functions, a `Q`-query adversary distinguishes the adapter's three-key ideal game from a uniform
permutation of `2 * n`-bit blocks with advantage at most `2 * Q.choose 2 / 2 ^ n + Q.choose 2 /
4 ^ n`. -/
theorem advantage_lubyRackoffRandomRounds_prpIdealGame_le (adversary : OracleDistinguisher)
    (n Q : ℕ) (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage (ProbComp.eval (prfMultiIdealGame 3 (lubyRackoffAdversary adversary) n))
      (ProbComp.eval (prpIdealGame (fun n => 2 * n) adversary n)) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ + (Q.choose 2 : ℝ) * (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
  have hadaptedQ := isQueryBounded_pairAdversary hQ
  have hperm : ProbComp.eval (prpIdealGame (fun n => 2 * n) adversary n) =
      (PMF.uniformOfFintype (Equiv.Perm (BitString n × BitString n))).bind fun σ =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun p => PMF.pure (σ p))) (pairAdversary adversary n) := by
    simp only [prpIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.eval_interpret, ProbComp.eval_pure, interpret_pairAdversary]
    rw [← PMF.uniformOfFintype_map_equiv (blockEquiv n).permCongr, PMF.bind_map]
    congr 1; funext π; simp only [Function.comp_apply, randomPermOracle_eq_blockOracle]
  rw [eval_prfMultiIdealGame_lubyRackoffAdversary, hperm,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
      (PMF.uniformOfFintype (Fin 3 → BitString n → BitString n))
      (fun tables p => LubyRackoff.feistel3 (tables 0) (tables 1) (tables 2) p)
      (pairAdversary adversary n),
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
      (PMF.uniformOfFintype (Equiv.Perm (BitString n × BitString n))) (fun σ p => σ p)
      (pairAdversary adversary n)]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  have h := LubyRackoff.advantage_feistel3RandomRoundsGame_idealPermGame_le
    (ProbOracleComp.isQueryBounded_fixCoins hadaptedQ ω)
  rw [bind_uniformOfFintype_fin_three (fun f₁ f₂ f₃ => OracleComp.interpret
    (fun p => PMF.pure (LubyRackoff.feistel3 f₁ f₂ f₃ p))
    (ProbOracleComp.fixCoins (pairAdversary adversary n) ω))]
  simpa only [LubyRackoff.feistel3RandomRoundsGame, LubyRackoff.feistel3FixedGame,
    LubyRackoff.idealPermGame, Probability.PMF.monad_bind_eq_bind, Fintype.card_pi,
    Fintype.card_fin, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Nat.cast_pow,
    Nat.cast_ofNat] using h

/-- **The Luby–Rackoff theorem** ([BonehShoup2023], Theorem 4.9; [LubyRackoff1988]): the
three-round Luby–Rackoff cipher built from a pseudorandom function is a pseudorandom permutation
against oracle-PPT distinguishers. -/
theorem PseudorandomFunction.prp_lubyRackoffCipher {family : List Bool → List Bool → List Bool}
    (hfamily : PseudorandomFunction family) :
    (lubyRackoffCipher family hfamily.polyTime hfamily.length_eq).PRP := by
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hQ : PolynomiallyBounded fun n => 3 * (Q n).choose 2 := by
    refine PolynomiallyBounded.mono_of_le (g := fun n => 3 * Q n ^ 2)
      ((PolynomiallyBounded.const 3).mul
        (((PolynomiallyBounded.const c).mul ((PolynomiallyBounded.id.add (.const 2)).pow d)).pow 2))
      fun n => ?_
    change 3 * (Q n).choose 2 ≤ 3 * Q n ^ 2
    rw [Nat.choose_two_right, sq]
    exact Nat.mul_le_mul_left _
      ((Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
  have hgeometric : Negligible fun n => ((2 : ℝ≥0) ^ n)⁻¹ := by
    simpa only [inv_pow] using negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)
  refine negligible_of_le ((hfamily.multiKey 3 (lubyRackoffAdversary adversary)
    (isOraclePPT_lubyRackoffAdversary hadversary)).add
      (hgeometric.polynomiallyBounded_mul hQ)) fun n => ?_
  dsimp only [Pi.add_apply]
  rw [eval_prpRealGame_lubyRackoffCipher hfamily]
  refine (Game.advantage_triangle _
    (ProbComp.eval (prfMultiIdealGame 3 (lubyRackoffAdversary adversary) n)) _).trans
      (add_le_add le_rfl ?_)
  rw [← NNReal.coe_le_coe]
  have hrandom := advantage_lubyRackoffRandomRounds_prpIdealGame_le adversary n (Q n)
    (by simpa only [List.length_nil, Nat.add_zero, Q] using (hbounds n []).1)
  have hsmall : (((2 : ℝ) ^ n)⁻¹) ^ 2 ≤ ((2 : ℝ) ^ n)⁻¹ := by
    have h₀ : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
    have h₁ : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    nlinarith
  have hchoose : (0 : ℝ) ≤ (Q n).choose 2 := Nat.cast_nonneg _
  refine hrandom.trans ?_
  push_cast
  nlinarith


/-! ### Four rounds: a strong pseudorandom permutation -/

section Cipher4

variable (family : List Bool → List Bool → List Bool)

/-- Four-round Luby–Rackoff encryption of a block under a key `k₁ ++ k₂ ++ k₃ ++ k₄`. -/
@[expose] def lubyRackoff4Encrypt (n : ℕ) (key : List Bool) : List Bool → List Bool :=
  feistelNetworkWord [family (keyBlock n 0 key), family (keyBlock n 1 key),
    family (keyBlock n 2 key), family (keyBlock n 3 key)] n

/-- Four-round Luby–Rackoff decryption of a block under a key `k₁ ++ k₂ ++ k₃ ++ k₄`. -/
@[expose] def lubyRackoff4Decrypt (n : ℕ) (key : List Bool) : List Bool → List Bool :=
  feistelNetworkWordInv [family (keyBlock n 0 key), family (keyBlock n 1 key),
    family (keyBlock n 2 key), family (keyBlock n 3 key)] n

variable {family}

private theorem forall₂_represents_four
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {key : List Bool} (hkey : key.length = 4 * n) :
    List.Forall₂ Represents
      [family (keyBlock n 0 key), family (keyBlock n 1 key), family (keyBlock n 2 key),
        family (keyBlock n 3 key)]
      [roundFunction family n 0 key, roundFunction family n 1 key, roundFunction family n 2 key,
        roundFunction family n 3 key] :=
  have hrep {i} (hi : i < 4) := represents_roundFunction hlength hkey hi
  .cons (hrep (by decide))
    (.cons (hrep (by decide)) (.cons (hrep (by decide)) (.cons (hrep (by decide)) .nil)))

private theorem lubyRackoff4Encrypt_eq
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {key block : List Bool} (hkey : key.length = 4 * n) (hblock : block.length = 2 * n) :
    lubyRackoff4Encrypt family n key block =
      joinBlock (LubyRackoff.feistel4 (roundFunction family n 0 key)
        (roundFunction family n 1 key) (roundFunction family n 2 key)
        (roundFunction family n 3 key) (splitBlock n block)) := by
  conv_lhs => rw [← joinBlock_splitBlock hblock]
  exact feistelNetworkWord_joinBlock (forall₂_represents_four hlength hkey) _

private theorem lubyRackoff4Decrypt_eq
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {key block : List Bool} (hkey : key.length = 4 * n) (hblock : block.length = 2 * n) :
    lubyRackoff4Decrypt family n key block =
      joinBlock ((LubyRackoff.feistel4 (roundFunction family n 0 key)
        (roundFunction family n 1 key) (roundFunction family n 2 key)
        (roundFunction family n 3 key)).symm (splitBlock n block)) := by
  conv_lhs => rw [← joinBlock_splitBlock hblock]
  exact feistelNetworkWordInv_joinBlock (forall₂_represents_four hlength hkey) _

variable (family) in
/-- The four-round Luby–Rackoff block cipher with `4 * n`-bit keys and `2 * n`-bit blocks, built
from a length-preserving keyed family computable in polynomial time ([LubyRackoff1988]). -/
@[expose] def lubyRackoff4Cipher
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    BlockCipher where
  keyLen n := 4 * n
  blockLen n := 2 * n
  keyLen_polyTime := by exact ComputableInPolyTime.unary_mul' (.const 4) .id'
  blockLen_polyTime := by exact ComputableInPolyTime.unary_mul' (.const 2) .id'
  encrypt := lubyRackoff4Encrypt family
  decrypt := lubyRackoff4Decrypt family
  encrypt_polyTime := by
    have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
    have hb := (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd'
    exact computableInPolyTime_feistelRoundWord (computableInPolyTime_keyRound hpoly 3) hn
      (computableInPolyTime_feistelRoundWord (computableInPolyTime_keyRound hpoly 2) hn
        (computableInPolyTime_feistelRoundWord (computableInPolyTime_keyRound hpoly 1) hn
          (computableInPolyTime_feistelRoundWord (computableInPolyTime_keyRound hpoly 0) hn hb)))
  decrypt_polyTime := by
    have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
    have hb := (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd'
    exact computableInPolyTime_feistelInvRoundWord (computableInPolyTime_keyRound hpoly 0) hn
      (computableInPolyTime_feistelInvRoundWord (computableInPolyTime_keyRound hpoly 1) hn
        (computableInPolyTime_feistelInvRoundWord (computableInPolyTime_keyRound hpoly 2) hn
          (computableInPolyTime_feistelInvRoundWord (computableInPolyTime_keyRound hpoly 3) hn hb)))
  length_encrypt n key block hkey hblock := by
    rw [lubyRackoff4Encrypt_eq hlength hkey hblock, length_joinBlock]
  length_decrypt n key block hkey hblock := by
    rw [lubyRackoff4Decrypt_eq hlength hkey hblock, length_joinBlock]
  decrypt_encrypt n key block hkey hblock := by
    rw [lubyRackoff4Decrypt_eq hlength hkey (by rw [lubyRackoff4Encrypt_eq hlength hkey hblock,
      length_joinBlock]), lubyRackoff4Encrypt_eq hlength hkey hblock, splitBlock_joinBlock,
      Equiv.symm_apply_apply, joinBlock_splitBlock hblock]
  encrypt_decrypt n key block hkey hblock := by
    rw [lubyRackoff4Encrypt_eq hlength hkey (by rw [lubyRackoff4Decrypt_eq hlength hkey hblock,
      length_joinBlock]), lubyRackoff4Decrypt_eq hlength hkey hblock, splitBlock_joinBlock,
      Equiv.apply_symm_apply, joinBlock_splitBlock hblock]

end Cipher4

/-! ### The reduction to four PRF keys -/

/-- Answer one forward (`false`) or inverse (`true`) block query through four PRF channels, which
provide the four Feistel rounds. Malformed blocks are answered with `[]` without querying. -/
@[expose] def strongLubyRackoffQuery (n : ℕ) (request : Bool × List Bool) :
    WordOracleComp (Fin 4) (List Bool) :=
  match request with
  | (inverse, block) =>
    if block.length = 2 * n then
      if inverse then feistelNetworkInvQuery [0, 1, 2, 3] n block
      else feistelNetworkQuery [0, 1, 2, 3] n block
    else pure []

/-- Run a bidirectional block-cipher adversary against four PRF channels, answering each query
with `strongLubyRackoffQuery`. -/
@[expose] def strongLubyRackoffAdversary (adversary : StrongPRPDistinguisher) :
    MultiKeyDistinguisher 4 :=
  fun n aux => OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (strongLubyRackoffQuery n)) (adversary n aux)

/-- The bidirectional adapter is oracle PPT for every oracle-PPT adversary. -/
theorem isOraclePPT_strongLubyRackoffAdversary {adversary : StrongPRPDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (strongLubyRackoffAdversary adversary) := by
  have hn := (ComputableInPolyTime.fst (encPair encUnary encBits)
    (encPair (encFinEnum Bool) encBits)).fst'
  have hreq := ComputableInPolyTime.snd (encPair encUnary encBits)
    (encPair (encFinEnum Bool) encBits)
  have hblock := hreq.snd'
  refine isOraclePPT_interpret_handler hadversary
    (IsOraclePPTOn.ite'
      (ComputableInPolyTime.unary_eq' (hblock.trans ComputableInPolyTime.length_bits)
        (ComputableInPolyTime.unary_mul' (.const 2) hn))
      (IsOraclePPTOn.cond' (hreq.fst'.trans (.of_finite id))
        (isOraclePPTOn_feistelNetworkInvQuery [0, 1, 2, 3] hn hblock)
        (isOraclePPTOn_feistelNetworkQuery [0, 1, 2, 3] hn hblock))
      ((ComputableInPolyTime.const ([] : List Bool)).isPPTOn.isOraclePPTOn (Operation := Fin 4)))
    (resources := fun n _ => 2 * n)
    (ComputableInPolyTime.unary_mul' (.const 2)
      (ComputableInPolyTime.fst (encPair encUnary encBits) encBits).fst')
    fun n ⟨inverse, block⟩ reply hreply => ?_
  simp only [strongLubyRackoffQuery] at hreply
  split_ifs at hreply with hblock hinverse
  · exact (length_le_of_mem_support_feistelNetworkInvQuery _ _ _ _ hreply).trans hblock.le
  · exact (length_le_of_mem_support_feistelNetworkQuery _ _ _ _ hreply).trans hblock.le
  · simp only [OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hreply
    subst hreply; simp

/-- Interpreting the bidirectional adapter against deterministic channels runs the adversary
against the word-level Feistel rounds that read the channels. -/
private theorem interpret_strongLubyRackoffAdversary (adversary : StrongPRPDistinguisher)
    (n : ℕ) (oracle : Fin 4 × List Bool → List Bool) :
    OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun request => PMF.pure (oracle request)))
        (strongLubyRackoffAdversary adversary n []) =
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun request =>
        PMF.pure (if request.2.length = 2 * n then
          (if request.1 then
            feistelNetworkWordInv ([0, 1, 2, 3].map fun i query => (oracle (i, query)).take n) n
              request.2
          else
            feistelNetworkWord ([0, 1, 2, 3].map fun i query => (oracle (i, query)).take n) n
              request.2)
        else []))) (adversary n []) := by
  simp only [strongLubyRackoffAdversary, OracleComp.interpret_interpret,
    OracleComp.interpret_sumHandler, ProbOracleComp.interpret_sample, ProbComp.unifFin,
    OracleComp.interpret_query]
  congr 2; funext ⟨inverse, block⟩; dsimp only [strongLubyRackoffQuery]; split_ifs
  · exact interpret_feistelNetworkInvQuery oracle n _ _
  · exact interpret_feistelNetworkQuery oracle n _ _
  · rfl

/-- The real chosen-ciphertext experiment of the four-round cipher is the real four-key
experiment of the bidirectional adapter. -/
theorem eval_strongPRPRealGame_lubyRackoff4Cipher {family : List Bool → List Bool → List Bool}
    (hfamily : PseudorandomFunction family) (adversary : StrongPRPDistinguisher) (n : ℕ) :
    ProbComp.eval ((lubyRackoff4Cipher family hfamily.polyTime hfamily.length_eq).strongPRPRealGame
        adversary n) =
      ProbComp.eval (prfMultiRealGame family 4 (strongLubyRackoffAdversary adversary) n) := by
  simp only [BlockCipher.strongPRPRealGame, prfMultiRealGame, ProbComp.eval_bind,
    BitString.eval_sampleList, ProbOracleComp.eval_interpret, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
  have hkeyLength : key.length = 4 * n := BitString.length_of_mem_support_uniformList hkey
  have hrep {i} (hi : i < 4) := represents_prfOracle_take hfamily.length_eq hkeyLength hi
  have hrounds : List.Forall₂ Represents
      ([0, 1, 2, 3].map fun (i : Fin 4) query =>
        (prfOracle family n (keyBlock n i key) query).take n)
      [roundFunction family n 0 key, roundFunction family n 1 key,
        roundFunction family n 2 key, roundFunction family n 3 key] :=
    .cons (hrep (by decide))
      (.cons (hrep (by decide)) (.cons (hrep (by decide)) (.cons (hrep (by decide)) .nil)))
  rw [interpret_strongLubyRackoffAdversary]; congr 2; funext ⟨inverse, block⟩; congr 1
  change (if block.length = 2 * n then
    (if inverse then lubyRackoff4Decrypt family n key block
    else lubyRackoff4Encrypt family n key block) else []) = _
  by_cases hblock : block.length = 2 * n
  · simp only [hblock, ↓reduceIte]
    conv_rhs => rw [← joinBlock_splitBlock hblock]
    cases inverse
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [lubyRackoff4Encrypt_eq hfamily.length_eq hkeyLength hblock]
      exact (feistelNetworkWord_joinBlock hrounds _).symm
    · simp only [↓reduceIte]
      rw [lubyRackoff4Decrypt_eq hfamily.length_eq hkeyLength hblock]
      exact (feistelNetworkWordInv_joinBlock hrounds _).symm
  · simp only [hblock, ↓reduceIte]

/-! ### Four random rounds against a random permutation, in both directions -/

/-- Read a permutation of pairs of `n`-bit strings in both directions on `2 * n`-bit words,
answering other words with `[]`. -/
private def strongBlockOracle (n : ℕ) (σ : Equiv.Perm (BitString n × BitString n))
    (request : Bool × List Bool) : List Bool :=
  if request.2.length = 2 * n then
    joinBlock ((if request.1 then σ.symm else σ) (splitBlock n request.2))
  else []

/-- A bidirectional permutation as a deterministic table. -/
private def strongTable {X : Type} (σ : Equiv.Perm X) (request : Bool × X) : X :=
  if request.1 then σ.symm request.2 else σ request.2

private theorem feistelStrongOracle_eq {n : ℕ} (σ : Equiv.Perm (BitString n × BitString n)) :
    LubyRackoff.feistelStrongOracle σ = fun request => PMF.pure (strongTable σ request) := by
  funext ⟨inverse, p⟩; cases inverse <;> rfl

private theorem strongRandomPermOracle_eq_strongBlockOracle (n : ℕ)
    (π : Equiv.Perm (BitString (2 * n))) (request : Bool × List Bool) :
    strongRandomPermOracle (2 * n) π request =
      strongBlockOracle n ((blockEquiv n).permCongr π) request := by
  obtain ⟨inverse, block⟩ := request
  unfold strongRandomPermOracle strongBlockOracle; dsimp only
  by_cases hblock : block.length = 2 * n
  · simp only [hblock, ↓reduceIte]
    cases inverse
    · simp only [Bool.false_eq_true, ↓reduceIte, Equiv.permCongr_apply, blockEquiv,
        Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, joinBlock_splitBlock hblock,
        joinBlock_splitBlock List.length_ofFn]
    · simp only [↓reduceIte]
      change _ = joinBlock ((blockEquiv n).permCongr π.symm (splitBlock n block))
      simp only [Equiv.permCongr_apply, blockEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
        joinBlock_splitBlock hblock, joinBlock_splitBlock List.length_ofFn]
  · simp only [hblock, ↓reduceIte]

/-- The bidirectional adversary as a program querying pairs of `n`-bit halves. -/
private noncomputable def strongPairAdversary (adversary : StrongPRPDistinguisher) (n : ℕ) :
    ProbOracleComp (fun _ : Bool × (BitString n × BitString n) => BitString n × BitString n)
      Bool :=
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun request : Bool × List Bool =>
        if request.2.length = 2 * n then
          joinBlock <$> ProbOracleComp.query (request.1, splitBlock n request.2)
        else pure []))
    (adversary n [])

private theorem isQueryBounded_strongPairAdversary {adversary : StrongPRPDistinguisher}
    {n Q : ℕ} (hQ : (adversary n []).IsQueryBounded Q) :
    (strongPairAdversary adversary n).IsQueryBounded Q := by
  refine hQ.interpret fun q => ?_
  rcases q with k | request
  · exact ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin k)
  · dsimp only [OracleComp.sumHandler]; split_ifs
    · simpa only [map_eq_bind_pure_comp, Function.comp_def, Nat.add_zero, Sum.elim_inr] using
        (ProbOracleComp.IsQueryBounded.query (request.1, splitBlock n request.2)).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0
    · exact OracleComp.IsCostBounded.pure [] _

private theorem interpret_strongPairAdversary (adversary : StrongPRPDistinguisher) (n : ℕ)
    (σ : Equiv.Perm (BitString n × BitString n)) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request => PMF.pure (strongTable σ request))) (strongPairAdversary adversary n) =
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request : Bool × List Bool => PMF.pure (strongBlockOracle n σ request)))
        (adversary n []) := by
  simp only [strongPairAdversary, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
    ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
  congr 2; funext request; unfold strongBlockOracle strongTable
  split_ifs <;> simp [*, PMF.monad_map_eq_map]

/-- With random round functions, the bidirectional adapter runs the adversary against the
four-round Feistel network of independent uniform random functions, in both directions. -/
private theorem eval_prfMultiIdealGame_strongLubyRackoffAdversary
    (adversary : StrongPRPDistinguisher) (n : ℕ) :
    ProbComp.eval (prfMultiIdealGame 4 (strongLubyRackoffAdversary adversary) n) =
      (PMF.uniformOfFintype (Fin 4 → BitString n → BitString n)).bind fun tables =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun request =>
          PMF.pure (strongTable (LubyRackoff.feistel4 (tables 0) (tables 1) (tables 2) (tables 3))
            request))) (strongPairAdversary adversary n) := by
  simp only [prfMultiIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, interpret_strongPairAdversary]
  congr 1; funext tables; rw [interpret_strongLubyRackoffAdversary]; congr 2
  funext ⟨inverse, block⟩; congr 1
  have hT (i : Fin 4) : Represents (fun q => (randomFunctionOracle n (tables i) q).take n)
      (tables i) := fun x => by
    simp only [randomFunctionOracle, List.length_ofFn, ↓reduceIte, BitString.ofList_ofFn]
    exact List.take_of_length_le List.length_ofFn.le
  have hrounds := List.Forall₂.cons (hT 0) (.cons (hT 1) (.cons (hT 2) (.cons (hT 3) .nil)))
  unfold strongBlockOracle; dsimp only
  by_cases hblock : block.length = 2 * n
  · simp only [hblock, ↓reduceIte]
    conv_lhs => rw [← joinBlock_splitBlock hblock]
    cases inverse
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact feistelNetworkWord_joinBlock hrounds _
    · simp only [↓reduceIte]
      exact feistelNetworkWordInv_joinBlock hrounds _
  · simp only [hblock, ↓reduceIte]

/-- Four independent uniform draws are the coordinates of a uniform quadruple. -/
private theorem bind_uniformOfFintype_fin_four {X β : Type} [Fintype X] [Nonempty X]
    (F : X → X → X → X → PMF β) :
    (PMF.uniformOfFintype (Fin 4 → X)).bind (fun f => F (f 0) (f 1) (f 2) (f 3)) =
      (PMF.uniformOfFintype X).bind fun a => (PMF.uniformOfFintype X).bind fun b =>
        (PMF.uniformOfFintype X).bind fun c => (PMF.uniformOfFintype X).bind fun d =>
          F a b c d := by
  let e : X × X × X × X ≃ (Fin 4 → X) :=
    { toFun := fun t => ![t.1, t.2.1, t.2.2.1, t.2.2.2]
      invFun := fun f => (f 0, f 1, f 2, f 3)
      left_inv := fun _ => rfl
      right_inv := fun f => by funext i; fin_cases i <;> rfl }
  rw [← PMF.uniformOfFintype_map_equiv e, PMF.bind_map, ← PMF.uniformOfFintype_prod,
    ← PMF.uniformOfFintype_prod, ← PMF.uniformOfFintype_prod]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]; rfl

/-- **Four random Feistel rounds against a random permutation, in both directions**
([LubyRackoff1988]), for randomized bidirectional word-oracle adversaries: with independent
uniform random round functions, a `Q`-query adversary distinguishes the adapter's four-key ideal
game from a uniform permutation of `2 * n`-bit blocks with advantage at most
`2 * Q.choose 2 / 2 ^ n + 2 * Q.choose 2 / 4 ^ n`. -/
theorem advantage_lubyRackoff4RandomRounds_strongPRPIdealGame_le
    (adversary : StrongPRPDistinguisher) (n Q : ℕ) (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage (ProbComp.eval (prfMultiIdealGame 4 (strongLubyRackoffAdversary adversary) n))
      (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n) adversary n)) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ +
        2 * (Q.choose 2 : ℝ) * (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
  have hadaptedQ := isQueryBounded_strongPairAdversary hQ
  have hperm : ProbComp.eval (strongPRPIdealGame (fun n => 2 * n) adversary n) =
      (PMF.uniformOfFintype (Equiv.Perm (BitString n × BitString n))).bind fun σ =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun request => PMF.pure (strongTable σ request))) (strongPairAdversary adversary n) := by
    simp only [strongPRPIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.eval_interpret, ProbComp.eval_pure, interpret_strongPairAdversary]
    rw [← PMF.uniformOfFintype_map_equiv (blockEquiv n).permCongr, PMF.bind_map]
    congr 1; funext π; simp only [Function.comp_apply, strongRandomPermOracle_eq_strongBlockOracle]
  rw [eval_prfMultiIdealGame_strongLubyRackoffAdversary, hperm,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
      (PMF.uniformOfFintype (Fin 4 → BitString n → BitString n))
      (fun tables request =>
        strongTable (LubyRackoff.feistel4 (tables 0) (tables 1) (tables 2) (tables 3)) request)
      (strongPairAdversary adversary n),
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
      (PMF.uniformOfFintype (Equiv.Perm (BitString n × BitString n)))
      (fun σ request => strongTable σ request) (strongPairAdversary adversary n)]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  have h := LubyRackoff.advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le
    (ProbOracleComp.isQueryBounded_fixCoins hadaptedQ ω)
  rw [bind_uniformOfFintype_fin_four (fun f₁ f₂ f₃ f₄ => OracleComp.interpret
    (fun request => PMF.pure (strongTable (LubyRackoff.feistel4 f₁ f₂ f₃ f₄) request))
    (ProbOracleComp.fixCoins (strongPairAdversary adversary n) ω))]
  simpa only [LubyRackoff.feistel4StrongRandomRoundsGame, LubyRackoff.idealStrongGame,
    feistelStrongOracle_eq, Probability.PMF.monad_bind_eq_bind, Fintype.card_pi,
    Fintype.card_fin, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Nat.cast_pow,
    Nat.cast_ofNat] using h

/-- **Four-round Luby–Rackoff theorem** ([LubyRackoff1988]; [KatzLindell2020], Proposition 6.29;
strongly secure block ciphers as in [BonehShoup2023], Section 4.1.3 and Exercise 4.9): the
four-round Luby–Rackoff cipher built from a pseudorandom function is a strong pseudorandom
permutation against oracle-PPT distinguishers. -/
theorem PseudorandomFunction.strongPRP_lubyRackoff4Cipher
    {family : List Bool → List Bool → List Bool} (hfamily : PseudorandomFunction family) :
    (lubyRackoff4Cipher family hfamily.polyTime hfamily.length_eq).StrongPRP := by
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hQ : PolynomiallyBounded fun n => 4 * (Q n).choose 2 := by
    refine PolynomiallyBounded.mono_of_le (g := fun n => 4 * Q n ^ 2)
      ((PolynomiallyBounded.const 4).mul
        (((PolynomiallyBounded.const c).mul ((PolynomiallyBounded.id.add (.const 2)).pow d)).pow 2))
      fun n => ?_
    change 4 * (Q n).choose 2 ≤ 4 * Q n ^ 2
    rw [Nat.choose_two_right, sq]
    exact Nat.mul_le_mul_left _
      ((Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
  have hgeometric : Negligible fun n => ((2 : ℝ≥0) ^ n)⁻¹ := by
    simpa only [inv_pow] using negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)
  refine negligible_of_le ((hfamily.multiKey 4 (strongLubyRackoffAdversary adversary)
    (isOraclePPT_strongLubyRackoffAdversary hadversary)).add
      (hgeometric.polynomiallyBounded_mul hQ)) fun n => ?_
  dsimp only [Pi.add_apply]
  rw [eval_strongPRPRealGame_lubyRackoff4Cipher hfamily]
  refine (Game.advantage_triangle _
    (ProbComp.eval (prfMultiIdealGame 4 (strongLubyRackoffAdversary adversary) n)) _).trans
      (add_le_add le_rfl ?_)
  rw [← NNReal.coe_le_coe]
  have hrandom := advantage_lubyRackoff4RandomRounds_strongPRPIdealGame_le adversary n (Q n)
    (by simpa only [List.length_nil, Nat.add_zero, Q] using (hbounds n []).1)
  have hsmall : (((2 : ℝ) ^ n)⁻¹) ^ 2 ≤ ((2 : ℝ) ^ n)⁻¹ := by
    have h₀ : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
    have h₁ : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    nlinarith
  have hchoose : (0 : ℝ) ≤ (Q n).choose 2 := Nat.cast_nonneg _
  refine hrandom.trans ?_
  push_cast
  nlinarith

/-- The four-round Luby–Rackoff cipher is in particular a pseudorandom permutation. -/
theorem PseudorandomFunction.prp_lubyRackoff4Cipher
    {family : List Bool → List Bool → List Bool} (hfamily : PseudorandomFunction family) :
    (lubyRackoff4Cipher family hfamily.polyTime hfamily.length_eq).PRP :=
  hfamily.strongPRP_lubyRackoff4Cipher.prp

end Cslib.Crypto
