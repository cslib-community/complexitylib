/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomFunction.MultiKey
public import Complexity.Crypto.Computational.PseudorandomPermutation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Crypto.Negligible.Basic
import Complexity.Crypto.Protocols.Cipher.LubyRackoff
import Complexity.Foundations.Data.BitString.List.Operations
import Complexity.Languages.Probabilistic.Oracle.CoinFixing
import Complexity.Probability.PMF.Bind
import Complexity.Probability.Product
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# The Luby–Rackoff block cipher from a pseudorandom function

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

## Main definitions

* `Cslib.Crypto.lubyRackoffEncrypt`, `Cslib.Crypto.lubyRackoffDecrypt`,
  `Cslib.Crypto.lubyRackoffCipher`: the three-round Luby–Rackoff block cipher.
* `Cslib.Crypto.lubyRackoffQuery`, `Cslib.Crypto.lubyRackoffAdversary`: the reduction to the
  three-key PRF games.

## Main results

* `Cslib.Crypto.isOraclePPT_lubyRackoffAdversary`: the reduction is oracle PPT.
* `Cslib.Crypto.eval_prpRealGame_lubyRackoffCipher`: the real chosen-plaintext experiment is the
  real three-key experiment of the reduction.
* `Cslib.Crypto.advantage_lubyRackoffRandomRounds_prpIdealGame_le`: with random rounds, a
  `Q`-query adversary has advantage at most `2 * Q.choose 2 / 2 ^ n + Q.choose 2 / 4 ^ n` against a
  uniform permutation.
* `Cslib.Crypto.PseudorandomFunction.prp_lubyRackoffCipher`: the Luby–Rackoff theorem.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023]:
  Section 4.5 (printed pp. 141–147), Theorem 4.9 (p. 143) and Exercise 4.26 (p. 174).
* [M. Luby, C. Rackoff, *How to Construct Pseudorandom Permutations from Pseudorandom
  Functions*][LubyRackoff1988].
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Feistel rounds on words -/

/-- Three Feistel rounds on a `2 * n`-bit block `u ++ v` with round oracles `g₁, g₂, g₃` on words:
`w = u ⊕ g₁ v`, `x = v ⊕ g₂ w`, output `x ++ (w ⊕ g₃ x)`. -/
@[expose] def feistelWords (g₁ g₂ g₃ : List Bool → List Bool) (n : ℕ) (block : List Bool) :
    List Bool :=
  let w := List.zipWith Bool.xor (block.take n) (g₁ (block.drop n))
  let x := List.zipWith Bool.xor (block.drop n) (g₂ w)
  x ++ List.zipWith Bool.xor w (g₃ x)

/-- The inverse of `feistelWords` on a block `x ++ y`: `w = y ⊕ g₃ x`, `v = x ⊕ g₂ w`, output
`(w ⊕ g₁ v) ++ v`. -/
@[expose] def feistelWordsInv (g₁ g₂ g₃ : List Bool → List Bool) (n : ℕ) (block : List Bool) :
    List Bool :=
  let w := List.zipWith Bool.xor (block.drop n) (g₃ (block.take n))
  let v := List.zipWith Bool.xor (block.take n) (g₂ w)
  List.zipWith Bool.xor w (g₁ v) ++ v

/-- The halves of a `2 * n`-bit block. -/
private def splitBlock (n : ℕ) (block : List Bool) : BitString n × BitString n :=
  (BitString.ofList n (block.take n), BitString.ofList n (block.drop n))

/-- The block with the given halves. -/
private def joinBlock {n : ℕ} (halves : BitString n × BitString n) : List Bool :=
  List.ofFn halves.1 ++ List.ofFn halves.2

private theorem length_joinBlock {n : ℕ} (halves : BitString n × BitString n) :
    (joinBlock halves).length = 2 * n := by
  simp only [joinBlock, List.length_append, List.length_ofFn]
  omega

private theorem joinBlock_splitBlock {n : ℕ} {block : List Bool} (hblock : block.length = 2 * n) :
    joinBlock (splitBlock n block) = block := by
  simp only [joinBlock, splitBlock]
  rw [BitString.ofFn_ofList (by simp only [List.length_take]; omega),
    BitString.ofFn_ofList (by simp only [List.length_drop]; omega), List.take_append_drop]

private theorem splitBlock_joinBlock {n : ℕ} (halves : BitString n × BitString n) :
    splitBlock n (joinBlock halves) = halves := by
  simp [splitBlock, joinBlock]

/-- Word-level Feistel rounds compute the Feistel network of round functions they represent. -/
private theorem feistelWords_eq {n : ℕ} {g₁ g₂ g₃ : List Bool → List Bool}
    {f₁ f₂ f₃ : BitString n → BitString n} (h₁ : ∀ x, g₁ (List.ofFn x) = List.ofFn (f₁ x))
    (h₂ : ∀ x, g₂ (List.ofFn x) = List.ofFn (f₂ x)) (h₃ : ∀ x, g₃ (List.ofFn x) = List.ofFn (f₃ x))
    {block : List Bool} (hblock : block.length = 2 * n) :
    feistelWords g₁ g₂ g₃ n block =
      joinBlock (LubyRackoff.feistel3 f₁ f₂ f₃ (splitBlock n block)) := by
  obtain ⟨⟨a, b⟩, rfl⟩ : ∃ halves, joinBlock halves = block :=
    ⟨splitBlock n block, joinBlock_splitBlock hblock⟩
  rw [splitBlock_joinBlock]
  simp only [feistelWords, LubyRackoff.feistel3_apply, joinBlock,
    List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn, h₁, h₂, h₃,
    ← BitString.ofFn_add]

private theorem bitString_sub_eq_add {n : ℕ} (a b : BitString n) : a - b = a + b :=
  funext fun i => BooleanRing.sub_eq_add (a i) (b i)

/-- Word-level inverse rounds compute the inverse Feistel network. -/
private theorem feistelWordsInv_eq {n : ℕ} {g₁ g₂ g₃ : List Bool → List Bool}
    {f₁ f₂ f₃ : BitString n → BitString n} (h₁ : ∀ x, g₁ (List.ofFn x) = List.ofFn (f₁ x))
    (h₂ : ∀ x, g₂ (List.ofFn x) = List.ofFn (f₂ x)) (h₃ : ∀ x, g₃ (List.ofFn x) = List.ofFn (f₃ x))
    {block : List Bool} (hblock : block.length = 2 * n) :
    feistelWordsInv g₁ g₂ g₃ n block =
      joinBlock ((LubyRackoff.feistel3 f₁ f₂ f₃).symm (splitBlock n block)) := by
  obtain ⟨⟨a, b⟩, rfl⟩ : ∃ halves, joinBlock halves = block :=
    ⟨splitBlock n block, joinBlock_splitBlock hblock⟩
  rw [splitBlock_joinBlock]
  simp only [feistelWordsInv, LubyRackoff.feistel3_symm_apply, joinBlock,
    List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn, bitString_sub_eq_add,
    h₁, h₂, h₃,
    ← BitString.ofFn_add]

/-! ### The cipher -/

section Cipher

variable (family : List Bool → List Bool → List Bool)

/-- Luby–Rackoff encryption of a block `u ++ v` under a key `k₁ ++ k₂ ++ k₃`
([BonehShoup2023], Section 4.5): three Feistel rounds keyed by the blocks of the key. -/
@[expose] def lubyRackoffEncrypt (n : ℕ) (key : List Bool) : List Bool → List Bool :=
  feistelWords (family (keyBlock n 0 key)) (family (keyBlock n 1 key)) (family (keyBlock n 2 key)) n

/-- Luby–Rackoff decryption of a block `x ++ y` under a key `k₁ ++ k₂ ++ k₃`
([BonehShoup2023], Section 4.5). -/
@[expose] def lubyRackoffDecrypt (n : ℕ) (key : List Bool) : List Bool → List Bool :=
  feistelWordsInv (family (keyBlock n 0 key)) (family (keyBlock n 1 key))
    (family (keyBlock n 2 key)) n

variable {family}

/-- The round function on `n`-bit strings induced by the `i`-th key block. -/
private def roundFunction (family : List Bool → List Bool → List Bool) (n i : ℕ)
    (key : List Bool) (x : BitString n) : BitString n :=
  BitString.ofList n (family (keyBlock n i key) (List.ofFn x))

private theorem family_keyBlock_ofFn
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n i : ℕ} {key : List Bool} (hkey : key.length = 3 * n) (hi : i < 3) (x : BitString n) :
    family (keyBlock n i key) (List.ofFn x) = List.ofFn (roundFunction family n i key x) := by
  have hblock := length_keyBlock hkey hi
  rw [roundFunction, BitString.ofFn_ofList
    ((hlength _ _ (by rw [List.length_ofFn, hblock])).trans hblock)]

private theorem lubyRackoffEncrypt_eq
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {key block : List Bool} (hkey : key.length = 3 * n) (hblock : block.length = 2 * n) :
    lubyRackoffEncrypt family n key block =
      joinBlock (LubyRackoff.feistel3 (roundFunction family n 0 key) (roundFunction family n 1 key)
        (roundFunction family n 2 key) (splitBlock n block)) :=
  feistelWords_eq (family_keyBlock_ofFn hlength hkey (by decide))
    (family_keyBlock_ofFn hlength hkey (by decide)) (family_keyBlock_ofFn hlength hkey (by decide))
    hblock

private theorem lubyRackoffDecrypt_eq
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {key block : List Bool} (hkey : key.length = 3 * n) (hblock : block.length = 2 * n) :
    lubyRackoffDecrypt family n key block =
      joinBlock ((LubyRackoff.feistel3 (roundFunction family n 0 key)
        (roundFunction family n 1 key) (roundFunction family n 2 key)).symm
          (splitBlock n block)) :=
  feistelWordsInv_eq (family_keyBlock_ofFn hlength hkey (by decide))
    (family_keyBlock_ofFn hlength hkey (by decide)) (family_keyBlock_ofFn hlength hkey (by decide))
    hblock

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
  keyLen_polyTime := by polytime
  blockLen_polyTime := by polytime
  encrypt := lubyRackoffEncrypt family
  decrypt := lubyRackoffDecrypt family
  encrypt_polyTime := by
    unfold lubyRackoffEncrypt feistelWords keyBlock
    polytime
  decrypt_polyTime := by
    unfold lubyRackoffDecrypt feistelWordsInv keyBlock
    polytime
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

end Cslib.Crypto

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### The reduction to three PRF keys -/

/-- Answer one block query through three PRF channels: the rounds of `feistelWords`, with channel
`i` providing round `i + 1`. Malformed blocks are answered with `[]` without querying. Replies are
cut at `n` bits, which changes nothing for replies of the declared length. -/
@[expose] def lubyRackoffQuery (n : ℕ) (block : List Bool) : WordOracleComp (Fin 3) (List Bool) :=
  if block.length = 2 * n then do
    let y₁ ← List.take n <$> ProbOracleComp.query (0, block.drop n)
    let w := List.zipWith Bool.xor (block.take n) y₁
    let y₂ ← List.take n <$> ProbOracleComp.query (1, w)
    let x := List.zipWith Bool.xor (block.drop n) y₂
    let y₃ ← List.take n <$> ProbOracleComp.query (2, x)
    return x ++ List.zipWith Bool.xor w y₃
  else pure []

/-- Run a block-cipher adversary against three PRF channels, answering each block query with
`lubyRackoffQuery`. -/
@[expose] def lubyRackoffAdversary (adversary : OracleDistinguisher) : MultiKeyDistinguisher 3 :=
  fun n aux => OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun request => lubyRackoffQuery n request.2)) (adversary n aux)

/-- The input of one adapter call: the security parameter with the auxiliary word, and the
request. -/
private abbrev QueryInput := (ℕ × List Bool) × (Unit × List Bool)

/-- The encoding of `QueryInput`. -/
private abbrev queryInputEncoding : QueryInput ↪ List Bool :=
  encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)

private theorem isOraclePPTOn_lubyRackoffQuery :
    IsOraclePPTOn queryInputEncoding encBits
      (fun x : QueryInput => lubyRackoffQuery x.1.1 x.2.2) := by
  have q₁ : IsOraclePPTOn queryInputEncoding encBits (fun x : QueryInput =>
      List.take x.1.1 <$> ProbOracleComp.query (spec := fun _ : Fin 3 × List Bool => List Bool)
        (0, x.2.2.drop x.1.1)) :=
    IsOraclePPTOn.query_take' 0 (by polytime) (by polytime)
  have q₂ : IsOraclePPTOn (encPair queryInputEncoding encBits) encBits
      (fun p : QueryInput × List Bool =>
        List.take p.1.1.1 <$> ProbOracleComp.query (spec := fun _ : Fin 3 × List Bool => List Bool)
          (1, List.zipWith Bool.xor (p.1.2.2.take p.1.1.1) p.2)) :=
    IsOraclePPTOn.query_take' 1 (by polytime) (by polytime)
  have q₃ : IsOraclePPTOn (encPair (encPair queryInputEncoding encBits) encBits) encBits
      (fun p : (QueryInput × List Bool) × List Bool =>
        List.take p.1.1.1.1 <$> ProbOracleComp.query
          (spec := fun _ : Fin 3 × List Bool => List Bool)
          (2, List.zipWith Bool.xor (p.1.1.2.2.drop p.1.1.1.1) p.2)) :=
    IsOraclePPTOn.query_take' 2 (by polytime) (by polytime)
  have hreturn : IsOraclePPTOn
      (encPair (encPair (encPair queryInputEncoding encBits) encBits) encBits) encBits
      (fun p : ((QueryInput × List Bool) × List Bool) × List Bool =>
        pure (List.zipWith Bool.xor (p.1.1.1.2.2.drop p.1.1.1.1.1) p.1.2 ++
          List.zipWith Bool.xor
            (List.zipWith Bool.xor (p.1.1.1.2.2.take p.1.1.1.1.1) p.1.1.2) p.2)) :=
    (ComputableInPolyTime.isPPTOn (by polytime)).isOraclePPTOn (Operation := Fin 3)
  have h₃ := q₃.bind_with (second := fun (p : (QueryInput × List Bool) × List Bool) y₃ =>
    (pure (List.zipWith Bool.xor (p.1.1.2.2.drop p.1.1.1.1) p.2 ++
      List.zipWith Bool.xor (List.zipWith Bool.xor (p.1.1.2.2.take p.1.1.1.1) p.1.2) y₃) :
        WordOracleComp (Fin 3) (List Bool))) hreturn
  have h₂ := q₂.bind_with (second := fun (p : QueryInput × List Bool) y₂ => do
    let y₃ ← List.take p.1.1.1 <$> ProbOracleComp.query
      (spec := fun _ : Fin 3 × List Bool => List Bool)
      (2, List.zipWith Bool.xor (p.1.2.2.drop p.1.1.1) y₂)
    pure (List.zipWith Bool.xor (p.1.2.2.drop p.1.1.1) y₂ ++
      List.zipWith Bool.xor (List.zipWith Bool.xor (p.1.2.2.take p.1.1.1) p.2) y₃)) h₃
  have hyes := q₁.bind_with (second := fun (x : QueryInput) y₁ => do
    let y₂ ← List.take x.1.1 <$> ProbOracleComp.query
      (spec := fun _ : Fin 3 × List Bool => List Bool)
      (1, List.zipWith Bool.xor (x.2.2.take x.1.1) y₁)
    let y₃ ← List.take x.1.1 <$> ProbOracleComp.query
      (spec := fun _ : Fin 3 × List Bool => List Bool)
      (2, List.zipWith Bool.xor (x.2.2.drop x.1.1) y₂)
    pure (List.zipWith Bool.xor (x.2.2.drop x.1.1) y₂ ++
      List.zipWith Bool.xor (List.zipWith Bool.xor (x.2.2.take x.1.1) y₁) y₃)) h₂
  have hcondition : ComputableInPolyTime
      (fun x : QueryInput => decide (x.2.2.length = 2 * x.1.1)) queryInputEncoding encBool := by
    polytime
  exact IsOraclePPTOn.ite' hcondition hyes
    ((ComputableInPolyTime.isPPTOn (ComputableInPolyTime.const ([] : List Bool))).isOraclePPTOn
      (Operation := Fin 3))


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
  have hstate : IsOraclePPTOn (encPair (encPair encUnary encBits)
      (encPair (encPair (encFinEnum Operation) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun x : (ℕ × List Bool) × (Operation × List Bool) × Unit =>
        (fun reply => (reply, ())) <$> handler x.1.1 x.2.1) :=
    (hhandler.preprocess'
      (prepare := fun x : (ℕ × List Bool) × (Operation × List Bool) × Unit => (x.1, x.2.1))
      (by polytime)).map' (by polytime)
  have hrun := hadversary.run_interpret_preprocess_open' (External := External) (State := Unit)
    (input := encPair encUnary encBits) (operationEncoding := encFinEnum Operation)
    (stateEncoding := encFinEnum Unit)
    (handler := fun caller request (_ : Unit) =>
      (fun reply => (reply, ())) <$> handler caller.1 request)
    (prepare := id) (initial := fun _ => ())
    (resources := fun caller query => resources caller.1 query)
    (by polytime) hstate (by polytime) (fun _ _ => True) (fun _ => trivial) hresources
    (fun caller request _ _ result hresult => by
      simp only [OracleComp.mem_supportWith_map_iff] at hresult
      obtain ⟨reply, hreply', rfl⟩ := hresult
      exact ⟨trivial, hreply caller.1 request reply hreply', by simp [encFinEnum]⟩)
  have heq (n : ℕ) (aux : List Bool) :
      Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (fun request (_ : Unit) => (fun reply => (reply, ())) <$> handler n request))
        (adversary n aux)).run () =
      OracleComp.interpret
        (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) (handler n))
        (adversary n aux) := by
    rw [show (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (fun request (_ : Unit) => (fun reply => (reply, ())) <$> handler n request)) =
        fun q => StateT.lift (OracleComp.sumHandler
          (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) (handler n) q) by
      funext q
      rcases q with k | request
      · rfl
      · funext u
        simp only [OracleComp.sumHandler, StateT.lift, bind_pure_comp],
      OracleComp.run_interpret_lift, Functor.map_map]
    exact id_map _
  have h := hrun.map' (ComputableInPolyTime.fst encBool (encFinEnum Unit))
  refine IsOraclePPTOn.isOraclePPT ?_
  convert h using 1
  funext input
  exact (heq input.1 input.2).symm

/-- The adapter is oracle PPT for every oracle-PPT block-cipher adversary. -/
theorem isOraclePPT_lubyRackoffAdversary {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (lubyRackoffAdversary adversary) :=
  isOraclePPT_interpret_handler hadversary isOraclePPTOn_lubyRackoffQuery
    (resources := fun n _ => 2 * n) (by polytime) fun n request reply hreply => by
      simp only [lubyRackoffQuery] at hreply
      split_ifs at hreply
      · simp only [OracleComp.mem_supportWith_bind_iff, OracleComp.mem_supportWith_map_iff,
          OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hreply
        obtain ⟨_, ⟨_, _, rfl⟩, _, ⟨_, _, rfl⟩, _, ⟨_, _, rfl⟩, rfl⟩ := hreply
        simp only [List.length_append, List.length_zipWith, List.length_take, List.length_drop]
        omega
      · simp only [OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff]
          at hreply
        subst hreply
        simp

/-- Against deterministic channels, one adapter call is three word-level Feistel rounds whose
round oracles read the channels. -/
private theorem interpret_lubyRackoffQuery (n : ℕ) (oracle : Fin 3 × List Bool → List Bool)
    (block : List Bool) :
    OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun request => PMF.pure (oracle request)))
        (lubyRackoffQuery n block) =
      PMF.pure (if block.length = 2 * n then
        feistelWords (fun q => (oracle (0, q)).take n) (fun q => (oracle (1, q)).take n)
          (fun q => (oracle (2, q)).take n) n block
      else []) := by
  unfold lubyRackoffQuery
  split_ifs <;> simp [feistelWords, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.monad_map_eq_map]

/-- Interpreting the adapter against deterministic channels runs the block-cipher adversary
against the word-level Feistel rounds that read the channels. -/
private theorem interpret_lubyRackoffAdversary (adversary : OracleDistinguisher) (n : ℕ)
    (oracle : Fin 3 × List Bool → List Bool) :
    OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun request => PMF.pure (oracle request)))
        (lubyRackoffAdversary adversary n []) =
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun request =>
        PMF.pure (if request.2.length = 2 * n then
          feistelWords (fun q => (oracle (0, q)).take n) (fun q => (oracle (1, q)).take n)
            (fun q => (oracle (2, q)).take n) n request.2
        else []))) (adversary n []) := by
  simp only [lubyRackoffAdversary, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
    ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query,
    interpret_lubyRackoffQuery]

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
  rw [interpret_lubyRackoffAdversary]
  congr 2
  funext request
  congr 1
  change (if request.2.length = 2 * n then lubyRackoffEncrypt family n key request.2 else []) = _
  by_cases hblock : request.2.length = 2 * n
  · simp only [hblock, ↓reduceIte]
    rw [lubyRackoffEncrypt_eq hfamily.length_eq hkeyLength hblock]
    have hround (i : ℕ) (hi : i < 3) (x : BitString n) :
        (prfOracle family n (keyBlock n i key) (List.ofFn x)).take n =
          List.ofFn (roundFunction family n i key x) := by
      simp only [prfOracle, List.length_ofFn, ↓reduceIte]
      rw [family_keyBlock_ofFn hfamily.length_eq hkeyLength hi x,
        List.take_of_length_le List.length_ofFn.le]
    exact (feistelWords_eq (hround 0 (by decide)) (hround 1 (by decide))
      (hround 2 (by decide)) hblock).symm
  · simp only [hblock, ↓reduceIte]

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
  left_inv z := by
    dsimp only
    rw [joinBlock_splitBlock List.length_ofFn, BitString.ofList_ofFn]
  right_inv halves := by
    dsimp only
    rw [BitString.ofFn_ofList (length_joinBlock halves), splitBlock_joinBlock]

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
  · dsimp only [OracleComp.sumHandler]
    split_ifs
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
  congr 2
  funext request
  unfold blockOracle
  split_ifs <;> simp [PMF.monad_map_eq_map]

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
  congr 1
  funext tables
  rw [interpret_lubyRackoffAdversary]
  congr 2
  funext request
  congr 1
  unfold blockOracle
  split_ifs with hblock
  · refine feistelWords_eq ?_ ?_ ?_ hblock <;>
    · intro x
      simp only [randomFunctionOracle, List.length_ofFn, ↓reduceIte, BitString.ofList_ofFn]
      exact List.take_of_length_le List.length_ofFn.le
  · rfl

/-- Three independent uniform draws are the coordinates of a uniform triple. -/
private theorem bind_uniformOfFintype_fin_three {X β : Type} [Fintype X] [Nonempty X]
    (F : X → X → X → PMF β) :
    (PMF.uniformOfFintype (Fin 3 → X)).bind (fun f => F (f 0) (f 1) (f 2)) =
      (PMF.uniformOfFintype X).bind fun a => (PMF.uniformOfFintype X).bind fun b =>
        (PMF.uniformOfFintype X).bind fun c => F a b c := by
  let e : X × X × X ≃ (Fin 3 → X) :=
    { toFun := fun t => ![t.1, t.2.1, t.2.2]
      invFun := fun f => (f 0, f 1, f 2)
      left_inv := fun _ => rfl
      right_inv := fun f => by
        funext i
        fin_cases i <;> rfl }
  rw [← PMF.uniformOfFintype_map_equiv e, PMF.bind_map, ← PMF.uniformOfFintype_prod,
    ← PMF.uniformOfFintype_prod]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl

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
    congr 1
    funext π
    simp only [Function.comp_apply, randomPermOracle_eq_blockOracle]
  have hroundsCoins := ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
    (PMF.uniformOfFintype (Fin 3 → BitString n → BitString n))
    (fun tables p => LubyRackoff.feistel3 (tables 0) (tables 1) (tables 2) p)
    (pairAdversary adversary n)
  have hpermCoins := ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
    (PMF.uniformOfFintype (Equiv.Perm (BitString n × BitString n))) (fun σ p => σ p)
    (pairAdversary adversary n)
  rw [eval_prfMultiIdealGame_lubyRackoffAdversary, hperm, hroundsCoins, hpermCoins]
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
    refine PolynomiallyBounded.mono_of_le (g := fun n => 3 * Q n ^ 2) (by dsimp only [Q]; fun_prop)
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

end Cslib.Crypto
