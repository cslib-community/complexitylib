/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomFunction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Crypto.Negligible.Basic
import Complexity.Languages.Probabilistic.Oracle.CoinFixing
import Complexity.Languages.Probabilistic.RandomPermutation
import Complexity.Probability.PMF.Bind

/-!
# Uniform computational block ciphers and pseudorandom permutations

A `BlockCipher` ([BonehShoup2023], Section 4.1, interpreted asymptotically as in Sections 2.3 and
4.1.5) has
polynomial-time key- and block-length schedules `keyLen, blockLen : ℕ → ℕ` and deterministic
polynomial-time algorithms `encrypt n key block` and `decrypt n key block` that receive the unary
security parameter `n`. On every `keyLen n`-bit key they preserve `blockLen n`-bit blocks and invert
one another, so each valid key induces a permutation `BlockCipher.permEquiv` of
`BitString (blockLen n)`.

There are two adaptive security notions against uniform `IsOraclePPT encBool` distinguishers:

1. **Pseudorandom permutation (`BlockCipher.PRP`, chosen-plaintext):** an `OracleDistinguisher`
   queries encryption on `blockLen n`-bit words (other words are answered with `[]`) and cannot tell
   a uniformly keyed cipher (`BlockCipher.prpRealGame`) from a uniformly random permutation of
   `BitString (blockLen n)` (`prpIdealGame`); this is [BonehShoup2023], Attack Game 4.1 and
   Definition 4.1.
2. **Strong pseudorandom permutation (`BlockCipher.StrongPRP`, chosen-ciphertext):** a
   `StrongPRPDistinguisher` asks `(false, x)` for encryption and `(true, y)` for decryption and
   cannot tell `BlockCipher.strongPRPRealGame` from `strongPRPIdealGame`; this is the strongly
   secure block cipher sketched in [BonehShoup2023], Section 4.1.3, and left as Exercise 4.9(a).

Fixing the private coins of a randomized adversary (`ProbOracleComp.coinLaw`) transfers the
deterministic PRP/PRF switching bound `RandomPermutation.abs_sub_uniformPerm_uniformFunc_le` to
word-oracle adversaries (`advantage_prpIdealGame_randomFunctionIdealGame_le`). Consequently a
`PRP` with `keyLen = blockLen = id` is a `PseudorandomFunction`
(`BlockCipher.PRP.pseudorandomFunction`), and every `StrongPRP` is a `PRP`
(`BlockCipher.StrongPRP.prp`).

## Main definitions

* `Cslib.Crypto.StrongPRPDistinguisher`: a bidirectional adaptive word-oracle distinguisher.
* `Cslib.Crypto.BlockCipher`, `Cslib.Crypto.BlockCipher.permEquiv`: a uniform deterministic block
  cipher and the permutation induced by a valid key.
* `Cslib.Crypto.randomPermOracle`, `Cslib.Crypto.prpIdealGame`,
  `Cslib.Crypto.BlockCipher.prpOracle`, `Cslib.Crypto.BlockCipher.prpRealGame`,
  `Cslib.Crypto.BlockCipher.PRP`: the chosen-plaintext oracles, games and security notion.
* `Cslib.Crypto.strongRandomPermOracle`, `Cslib.Crypto.strongPRPIdealGame`,
  `Cslib.Crypto.BlockCipher.strongPRPOracle`, `Cslib.Crypto.BlockCipher.strongPRPRealGame`,
  `Cslib.Crypto.BlockCipher.StrongPRP`: the chosen-ciphertext oracles, games and security notion.
* `Cslib.Crypto.randomFunctionIdealGame`: a uniform random function on `blockLen n`-bit words.
* `Cslib.Crypto.liftForwardDistinguisher`: run a forward distinguisher on the encryption channel.

## Main results

* `Cslib.Crypto.BlockCipher.prpOracle_eq_randomPermOracle`,
  `Cslib.Crypto.BlockCipher.strongPRPOracle_eq_strongRandomPermOracle`: a valid key answers as its
  induced permutation.
* `Cslib.Crypto.BlockCipher.isPPTOn_prpRealGame`,
  `Cslib.Crypto.BlockCipher.isPPTOn_strongPRPRealGame`: the real experiments are uniformly strict
  PPT.
* `Cslib.Crypto.isOraclePPT_liftForwardDistinguisher`, `Cslib.Crypto.BlockCipher.StrongPRP.prp`:
  strong PRP security implies PRP security.
* `Cslib.Crypto.advantage_prpIdealGame_randomFunctionIdealGame_le`,
  `Cslib.Crypto.indistinguishable_prpIdealGame_randomFunctionIdealGame`: the PRP/PRF switching
  lemma for randomized word-oracle adversaries ([BonehShoup2023], Theorem 4.4).
* `Cslib.Crypto.BlockCipher.PRP.pseudorandomFunction`: a length-preserving PRP is a PRF
  ([BonehShoup2023], Corollary 4.5).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023]:
  Section 4.1 (printed p. 96), Attack Game 4.1 (p. 97), Definition 4.1 (p. 98), Section 4.1.3
  (p. 101), Section 4.1.5 (p. 106) with Section 2.3, Theorem 4.4 (p. 134), Corollary 4.5 (p. 135)
  and Exercise 4.9 (p. 169).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- An adaptive test with a unary parameter, an auxiliary word and a bidirectional word channel:
`(false, x)` asks for encryption of `x` and `(true, y)` asks for decryption of `y`. -/
abbrev StrongPRPDistinguisher := ℕ → List Bool → WordOracleComp Bool Bool

/-- A uniform deterministic block cipher ([BonehShoup2023], Section 4.1, interpreted
asymptotically as in Section 4.1.5). Both algorithms receive the unary security parameter `n`.
Lengths and inversion are required only for keys of length `keyLen n` and blocks of length
`blockLen n`. -/
structure BlockCipher where
  /-- Key length at security parameter `n`. -/
  keyLen : ℕ → ℕ
  /-- Block length at security parameter `n`. -/
  blockLen : ℕ → ℕ
  /-- The key length is computable in polynomial time in unary. -/
  keyLen_polyTime : ComputableInPolyTime keyLen encUnary encUnary
  /-- The block length is computable in polynomial time in unary. -/
  blockLen_polyTime : ComputableInPolyTime blockLen encUnary encUnary
  /-- Encryption `(n, key, block) ↦ ciphertext`. -/
  encrypt : ℕ → List Bool → List Bool → List Bool
  /-- Decryption `(n, key, ciphertext) ↦ block`. -/
  decrypt : ℕ → List Bool → List Bool → List Bool
  /-- One deterministic machine computes encryption. -/
  encrypt_polyTime : ComputableInPolyTime (fun (n, key, block) => encrypt n key block)
    (encPair encUnary (encPair encBits encBits)) encBits
  /-- One deterministic machine computes decryption. -/
  decrypt_polyTime : ComputableInPolyTime (fun (n, key, block) => decrypt n key block)
    (encPair encUnary (encPair encBits encBits)) encBits
  /-- Encryption preserves the block length on valid inputs. -/
  length_encrypt : ∀ n key block, key.length = keyLen n → block.length = blockLen n →
    (encrypt n key block).length = blockLen n
  /-- Decryption preserves the block length on valid inputs. -/
  length_decrypt : ∀ n key block, key.length = keyLen n → block.length = blockLen n →
    (decrypt n key block).length = blockLen n
  /-- Decryption inverts encryption on valid inputs. -/
  decrypt_encrypt : ∀ n key block, key.length = keyLen n → block.length = blockLen n →
    decrypt n key (encrypt n key block) = block
  /-- Encryption inverts decryption on valid inputs. -/
  encrypt_decrypt : ∀ n key block, key.length = keyLen n → block.length = blockLen n →
    encrypt n key (decrypt n key block) = block

/-- Read a permutation of `m`-bit blocks as a table, answering other words with `[]`. -/
@[expose] def randomPermOracle (m : ℕ) (π : Equiv.Perm (BitString m)) (query : List Bool) :
    List Bool :=
  randomFunctionOracle m π query

/-- Read a permutation of `m`-bit blocks in both directions (`false` for `π`, `true` for
`π.symm`), answering other words with `[]`. -/
@[expose] def strongRandomPermOracle (m : ℕ) (π : Equiv.Perm (BitString m))
    (request : Bool × List Bool) : List Bool :=
  match request with
  | (inverse, query) =>
    if query.length = m then
      List.ofFn ((if inverse then π.symm else π) (BitString.ofList m query))
    else []

/-- The ideal chosen-plaintext experiment: a uniform permutation of `blockLen n`-bit blocks,
sampled independently of the adversary's private coins ([BonehShoup2023], Attack Game 4.1,
Experiment 1). -/
@[expose] noncomputable def prpIdealGame (blockLen : ℕ → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) : ProbComp Bool := do
  let π ← ProbComp.uniform (Equiv.Perm (BitString (blockLen n)))
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin
      (fun request => pure (randomPermOracle (blockLen n) π request.2)))
    (adversary n [])

/-- The ideal chosen-ciphertext experiment: one uniform permutation answers both forward and
inverse queries ([BonehShoup2023], Section 4.1.3). -/
@[expose] noncomputable def strongPRPIdealGame (blockLen : ℕ → ℕ)
    (adversary : StrongPRPDistinguisher) (n : ℕ) : ProbComp Bool := do
  let π ← ProbComp.uniform (Equiv.Perm (BitString (blockLen n)))
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin
      (fun request => pure (strongRandomPermOracle (blockLen n) π request)))
    (adversary n [])

/-- A uniform random function on `blockLen n`-bit words; at `blockLen = id` this is `prfIdealGame`
(`randomFunctionIdealGame_id`). -/
@[expose] noncomputable def randomFunctionIdealGame (blockLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString (blockLen n) → BitString (blockLen n))
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin
      (fun request => pure (randomFunctionOracle (blockLen n) table request.2)))
    (adversary n [])

@[simp] theorem randomFunctionIdealGame_id (adversary : OracleDistinguisher) (n : ℕ) :
    randomFunctionIdealGame id adversary n = prfIdealGame adversary n := rfl

namespace BlockCipher

variable (E : BlockCipher)

attribute [program_certificate] keyLen_polyTime blockLen_polyTime

/-- The key length of an efficiently computed parameter is efficiently computable. -/
@[program_certificate]
theorem computableInPolyTime_keyLen_comp {γ : Type} {input : γ ↪ List Bool} {n : γ → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a => E.keyLen (n a)) input encUnary :=
  E.keyLen_polyTime.comp hn

/-- The block length of an efficiently computed parameter is efficiently computable. -/
@[program_certificate]
theorem computableInPolyTime_blockLen_comp {γ : Type} {input : γ ↪ List Bool} {n : γ → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a => E.blockLen (n a)) input encUnary :=
  E.blockLen_polyTime.comp hn

/-- Encryption of efficiently computed arguments is efficiently computable. -/
@[program_certificate]
theorem computableInPolyTime_encrypt_comp {γ : Type} {input : γ ↪ List Bool} {n : γ → ℕ}
    {key block : γ → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (hkey : ComputableInPolyTime key input encBits)
    (hblock : ComputableInPolyTime block input encBits) :
    ComputableInPolyTime (fun a => E.encrypt (n a) (key a) (block a)) input encBits :=
  E.encrypt_polyTime.comp (hn.prod (hkey.prod hblock))

/-- Decryption of efficiently computed arguments is efficiently computable. -/
@[program_certificate]
theorem computableInPolyTime_decrypt_comp {γ : Type} {input : γ ↪ List Bool} {n : γ → ℕ}
    {key block : γ → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (hkey : ComputableInPolyTime key input encBits)
    (hblock : ComputableInPolyTime block input encBits) :
    ComputableInPolyTime (fun a => E.decrypt (n a) (key a) (block a)) input encBits :=
  E.decrypt_polyTime.comp (hn.prod (hkey.prod hblock))

/-- The permutation of `blockLen n`-bit blocks induced by a valid key. -/
@[expose] def permEquiv (n : ℕ) (key : List Bool) (hkey : key.length = E.keyLen n) :
    Equiv.Perm (BitString (E.blockLen n)) where
  toFun x := BitString.ofList (E.blockLen n) (E.encrypt n key (List.ofFn x))
  invFun y := BitString.ofList (E.blockLen n) (E.decrypt n key (List.ofFn y))
  left_inv x := by
    have hx : (List.ofFn x).length = E.blockLen n := List.length_ofFn
    dsimp only; rw [BitString.ofFn_ofList (E.length_encrypt n key _ hkey hx),
      E.decrypt_encrypt n key _ hkey hx, BitString.ofList_ofFn]
  right_inv y := by
    have hy : (List.ofFn y).length = E.blockLen n := List.length_ofFn
    dsimp only; rw [BitString.ofFn_ofList (E.length_decrypt n key _ hkey hy),
      E.encrypt_decrypt n key _ hkey hy, BitString.ofList_ofFn]

/-- The encryption oracle, answering words of the wrong length with `[]`. -/
@[expose] def prpOracle (n : ℕ) (key query : List Bool) : List Bool :=
  if query.length = E.blockLen n then E.encrypt n key query else []

/-- The encryption/decryption oracle (`false` for encryption, `true` for decryption), answering
words of the wrong length with `[]`. -/
@[expose] def strongPRPOracle (n : ℕ) (key : List Bool) (request : Bool × List Bool) :
    List Bool :=
  match request with
  | (inverse, query) =>
    if query.length = E.blockLen n then
      if inverse then E.decrypt n key query else E.encrypt n key query
    else []

/-- A valid key answers encryption queries as its induced permutation. -/
theorem prpOracle_eq_randomPermOracle {n : ℕ} {key : List Bool} (hkey : key.length = E.keyLen n)
    (query : List Bool) :
    E.prpOracle n key query = randomPermOracle (E.blockLen n) (E.permEquiv n key hkey) query := by
  by_cases hq : query.length = E.blockLen n
  · simp only [prpOracle, randomPermOracle, randomFunctionOracle, hq, ↓reduceIte]
    change E.encrypt n key query = List.ofFn (BitString.ofList (E.blockLen n)
      (E.encrypt n key (List.ofFn (BitString.ofList (E.blockLen n) query))))
    rw [BitString.ofFn_ofList hq, BitString.ofFn_ofList (E.length_encrypt n key query hkey hq)]
  · simp [prpOracle, randomPermOracle, randomFunctionOracle, hq]

/-- A valid key answers encryption and decryption queries as its induced permutation. -/
theorem strongPRPOracle_eq_strongRandomPermOracle {n : ℕ} {key : List Bool}
    (hkey : key.length = E.keyLen n) (request : Bool × List Bool) :
    E.strongPRPOracle n key request =
      strongRandomPermOracle (E.blockLen n) (E.permEquiv n key hkey) request := by
  obtain ⟨inverse, query⟩ := request
  cases inverse
  · exact E.prpOracle_eq_randomPermOracle hkey query
  · by_cases hq : query.length = E.blockLen n
    · simp only [strongPRPOracle, strongRandomPermOracle, hq, ↓reduceIte]
      change E.decrypt n key query = List.ofFn (BitString.ofList (E.blockLen n)
        (E.decrypt n key (List.ofFn (BitString.ofList (E.blockLen n) query))))
      rw [BitString.ofFn_ofList hq, BitString.ofFn_ofList (E.length_decrypt n key query hkey hq)]
    · simp [strongPRPOracle, strongRandomPermOracle, hq]

/-- The real chosen-plaintext experiment: one uniform `keyLen n`-bit key answers every encryption
query ([BonehShoup2023], Attack Game 4.1, Experiment 0). -/
@[expose] noncomputable def prpRealGame (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp Bool := do
  let key ← BitString.sampleList (E.keyLen n)
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin (fun request => pure (E.prpOracle n key request.2)))
    (adversary n [])

/-- The real chosen-ciphertext experiment: one uniform `keyLen n`-bit key answers forward queries
with encryption and inverse queries with decryption ([BonehShoup2023], Section 4.1.3). -/
@[expose] noncomputable def strongPRPRealGame (adversary : StrongPRPDistinguisher) (n : ℕ) :
    ProbComp Bool := do
  let key ← BitString.sampleList (E.keyLen n)
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin (fun request => pure (E.strongPRPOracle n key request)))
    (adversary n [])

/-- Pseudorandom-permutation security against uniform oracle-PPT distinguishers
([BonehShoup2023], Definition 4.1, interpreted asymptotically as in Section 4.1.5). -/
@[expose] def PRP : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.prpRealGame adversary n))
    (fun adversary n => ProbComp.eval (prpIdealGame E.blockLen adversary n))
    (IsOraclePPT encBool)

/-- Strong pseudorandom-permutation security against uniform oracle-PPT distinguishers
([BonehShoup2023], Section 4.1.3 and Exercise 4.9(a)). -/
@[expose] def StrongPRP : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.strongPRPRealGame adversary n))
    (fun adversary n => ProbComp.eval (strongPRPIdealGame E.blockLen adversary n))
    (IsOraclePPT encBool)

end BlockCipher

/-! ### Efficiency of the real experiments -/

/-- A stateless keyed oracle whose replies to valid keys have bounded length gives a strict PPT
experiment for every oracle-PPT adversary. Replies are cut at the bound inside the certificate,
which changes nothing on the support of the key sampler. -/
private theorem isPPTOn_keyedOracleGame {Operation : Type} [DecidableEq Operation]
    [FinEnum Operation]
    {adversary : ℕ → List Bool → WordOracleComp Operation Bool}
    (hadversary : IsOraclePPT encBool adversary) {keyLen bound : ℕ → ℕ}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hbound : ComputableInPolyTime bound encUnary encUnary)
    (oracle : ℕ → List Bool → Operation × List Bool → List Bool)
    (horacle : ComputableInPolyTime (fun (n, key, request) => oracle n key request)
      (encPair encUnary (encPair encBits (encPair (encFinEnum Operation) encBits))) encBits)
    (hlength : ∀ n key request, key.length = keyLen n → (oracle n key request).length ≤ bound n) :
    IsPPTOn encUnary encBool (fun n => do
      let key ← BitString.sampleList (keyLen n)
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin (fun request => pure (oracle n key request)))
        (adversary n [])) := by
  let caller : (ℕ × List Bool) ↪ List Bool := encPair encUnary encBits
  have hfst := ComputableInPolyTime.fst caller
    (encPair (encPair (encFinEnum Operation) encBits) (encFinEnum Unit))
  have hsnd := ComputableInPolyTime.snd caller
    (encPair (encPair (encFinEnum Operation) encBits) (encFinEnum Unit))
  have hcall := hfst.fst'.prod (hfst.snd'.prod hsnd.fst')
  have hreply := ((horacle.comp hcall).bitsTakeWithInput (hbound.comp hfst.fst')).prod
    (ComputableInPolyTime.const (encOut := encFinEnum Unit) ())
  have hrun := hadversary.run_interpret_preprocess' (State := Unit) (input := caller)
    (operationEncoding := encFinEnum Operation) (stateEncoding := encFinEnum Unit)
    (handler := fun caller request (_ : Unit) =>
      pure ((oracle caller.1 caller.2 request).take (bound caller.1), ()))
    (prepare := fun caller => (caller.1, [])) (initial := fun _ => ())
    (resources := fun caller _ => bound caller.1)
    ((ComputableInPolyTime.fst encUnary encBits).prod (ComputableInPolyTime.const []))
    hreply.isPPTOn (ComputableInPolyTime.const ()) (fun _ _ => True) (fun _ => trivial)
    (hbound.comp (ComputableInPolyTime.fst caller encBits).fst')
    (fun caller request _ _ result hresult => by
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨trivial, List.length_take_le _ _, by simp [encFinEnum]⟩)
  refine (hkeyLen.sampleList.bind_with (second := fun n key =>
      Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          fun request (_ : Unit) =>
            pure ((oracle n key request).take (bound n), ())) (adversary n [])).run ())
      (hrun.map (ComputableInPolyTime.fst encBool (encFinEnum Unit)))).congr fun n => ?_
  simp only [ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
  have hkeyLen : key.length = keyLen n := BitString.length_of_mem_support_uniformList hkey
  have htake (request : Operation × List Bool) :
      (oracle n key request).take (bound n) = oracle n key request :=
    List.take_of_length_le (hlength n key request hkeyLen)
  simp only [htake, ProbComp.eval_map, ProbOracleComp.eval_run_interpret,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure]
  rw [show (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifOracle r))
      fun request (_ : Unit) => PMF.pure (oracle n key request, ())) =
      fun q => StateT.lift (OracleComp.sumHandler ProbComp.unifOracle
        (fun request => PMF.pure (oracle n key request)) q) by
    funext q; rcases q with r | request
    · rfl
    · funext u; simp [StateT.lift, Probability.PMF.monad_pure_eq_pure]]
  rw [OracleComp.run_interpret_lift, ← PMF.monad_map_eq_map, Functor.map_map]
  exact id_map _

namespace BlockCipher

variable (E : BlockCipher)

/-- The real chosen-plaintext experiment is uniformly strict PPT for every oracle-PPT
adversary. -/
theorem isPPTOn_prpRealGame {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn encUnary encBool (E.prpRealGame adversary) := by
  have hn := ComputableInPolyTime.fst encUnary
    (encPair encBits (encPair (encFinEnum Unit) encBits))
  have hrest := ComputableInPolyTime.snd encUnary
    (encPair encBits (encPair (encFinEnum Unit) encBits))
  have hq := hrest.snd'.snd'
  exact isPPTOn_keyedOracleGame hadversary E.keyLen_polyTime E.blockLen_polyTime
    (fun n key request => E.prpOracle n key request.2)
    (ComputableInPolyTime.ite_decide
      (ComputableInPolyTime.unary_eq' (hq.trans ComputableInPolyTime.length_bits)
        (hn.trans E.blockLen_polyTime))
      (E.computableInPolyTime_encrypt_comp hn hrest.fst' hq)
      (ComputableInPolyTime.const []))
    fun n key request hkey => by
      unfold prpOracle; split_ifs with hq
      · exact (E.length_encrypt n key _ hkey hq).le
      · exact Nat.zero_le _

/-- The real chosen-ciphertext experiment is uniformly strict PPT for every oracle-PPT
adversary. -/
theorem isPPTOn_strongPRPRealGame {adversary : StrongPRPDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn encUnary encBool (E.strongPRPRealGame adversary) := by
  have hn := ComputableInPolyTime.fst encUnary
    (encPair encBits (encPair (encFinEnum Bool) encBits))
  have hrest := ComputableInPolyTime.snd encUnary
    (encPair encBits (encPair (encFinEnum Bool) encBits))
  have hq := hrest.snd'.snd'
  exact isPPTOn_keyedOracleGame hadversary E.keyLen_polyTime E.blockLen_polyTime
    (fun n key request => E.strongPRPOracle n key request)
    (ComputableInPolyTime.ite_decide
      (ComputableInPolyTime.unary_eq' (hq.trans ComputableInPolyTime.length_bits)
        (hn.trans E.blockLen_polyTime))
      (ComputableInPolyTime.ite hrest.snd'.fst'
        (E.computableInPolyTime_decrypt_comp hn hrest.fst' hq)
        (E.computableInPolyTime_encrypt_comp hn hrest.fst' hq))
      (ComputableInPolyTime.const []))
    fun n key ⟨inverse, query⟩ hkey => by
      simp only [strongPRPOracle]; split_ifs with hq
      · exact (E.length_decrypt n key _ hkey hq).le
      · exact (E.length_encrypt n key _ hkey hq).le
      · exact Nat.zero_le _

end BlockCipher

/-! ### Strong pseudorandom permutations are pseudorandom permutations -/

/-- Run a forward distinguisher against a bidirectional oracle, sending every query to the
encryption channel `false`. Replies are cut at `blockLen n` bits, which changes nothing against the
real or ideal permutation oracles and keeps the substitution polynomial on arbitrary replies. -/
@[expose] def liftForwardDistinguisher (blockLen : ℕ → ℕ) (adversary : OracleDistinguisher) :
    StrongPRPDistinguisher := fun n aux =>
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (fun (request : Unit × List Bool) (_ : Unit) =>
        (fun reply => (reply, ())) <$> (List.take (blockLen n) <$>
          ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool) (false, request.2))))
    (adversary n aux)).run ()

/-- Lifting an oracle-PPT forward distinguisher with a polynomial-time block length gives an
oracle-PPT bidirectional distinguisher. -/
theorem isOraclePPT_liftForwardDistinguisher {blockLen : ℕ → ℕ}
    (hblockLen : ComputableInPolyTime blockLen encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (liftForwardDistinguisher blockLen adversary) := by
  let caller : (ℕ × List Bool) ↪ List Bool := encPair encUnary encBits
  have hfst := ComputableInPolyTime.fst caller
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hsnd := ComputableInPolyTime.snd caller
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hhandler :=
    (IsOraclePPTOn.query_take' false hsnd.fst'.snd' (hfst.fst'.trans hblockLen)).map'
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const (encOut := encFinEnum Unit) ()))
  have hrun := hadversary.run_interpret_preprocess_open' (External := Bool) (State := Unit)
    (input := caller) (operationEncoding := encFinEnum Unit) (stateEncoding := encFinEnum Unit)
    (handler := fun caller (request : Unit × List Bool) (_ : Unit) =>
      (fun reply => (reply, ())) <$> (List.take (blockLen caller.1) <$>
        ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool) (false, request.2)))
    (prepare := id) (initial := fun _ => ()) (resources := fun caller _ => blockLen caller.1)
    ComputableInPolyTime.id' hhandler (ComputableInPolyTime.const ()) (fun _ _ => True)
    (fun _ => trivial) (hblockLen.comp (ComputableInPolyTime.fst caller encBits).fst')
    (fun _ _ _ _ result hresult => by
      simp only [OracleComp.mem_supportWith_map_iff] at hresult
      obtain ⟨reply, ⟨raw, _, rfl⟩, rfl⟩ := hresult
      exact ⟨trivial, List.length_take_le _ _, by simp [encFinEnum]⟩)
  exact (hrun.map' (ComputableInPolyTime.fst encBool (encFinEnum Unit))).isOraclePPT

/-- A stateless word handler that forwards to channel `false` and cuts replies agrees with the
`StateT Unit` handler of `liftForwardDistinguisher`. -/
private theorem liftForward_handler_eq (m : ℕ) :
    OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (fun (request : Unit × List Bool) (_ : Unit) =>
        (fun reply => (reply, ())) <$> (List.take m <$>
          ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool)
            (false, request.2))) =
      fun q => StateT.lift (OracleComp.sumHandler
        (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
        (fun request : Unit × List Bool => List.take m <$>
          ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool) (false, request.2))
        q) := by
  funext q; rcases q with k | request
  · rfl
  · funext ⟨⟩; simp only [OracleComp.sumHandler, StateT.lift, bind_pure_comp]

/-- Running `liftForwardDistinguisher` against a bidirectional table `oracle` is running the
forward adversary against the cut encryption channel of `oracle`. -/
private theorem eval_interpret_liftForwardDistinguisher (blockLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) (oracle : Bool × List Bool → List Bool) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request => PMF.pure (oracle request)))
      (liftForwardDistinguisher blockLen adversary n []) =
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request : Unit × List Bool =>
          PMF.pure ((oracle (false, request.2)).take (blockLen n))))
      (adversary n []) := by
  rw [liftForwardDistinguisher, liftForward_handler_eq, OracleComp.run_interpret_lift,
    OracleComp.interpret_map, OracleComp.interpret_map, Functor.map_map]
  simp only [id_map', OracleComp.interpret_interpret]
  congr 1; funext q; rcases q with k | request
  · simp [OracleComp.sumHandler, ProbOracleComp.sample, ProbComp.unifFin]
  · simp [OracleComp.sumHandler, PMF.monad_map_eq_map]

/-- Against the real bidirectional experiment, the lifted distinguisher has the law of the
forward distinguisher in the real chosen-plaintext experiment. -/
theorem BlockCipher.eval_strongPRPRealGame_liftForwardDistinguisher (E : BlockCipher)
    (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (E.strongPRPRealGame (liftForwardDistinguisher E.blockLen adversary) n) =
      ProbComp.eval (E.prpRealGame adversary n) := by
  simp only [BlockCipher.strongPRPRealGame, BlockCipher.prpRealGame, ProbComp.eval_bind,
    BitString.eval_sampleList, ProbOracleComp.eval_interpret, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
  have hkeyLen : key.length = E.keyLen n := BitString.length_of_mem_support_uniformList hkey
  rw [eval_interpret_liftForwardDistinguisher]
  congr 2
  funext request
  simp only [BlockCipher.strongPRPOracle, BlockCipher.prpOracle, Bool.false_eq_true, ↓reduceIte]
  split_ifs with hq
  · rw [List.take_of_length_le (E.length_encrypt n key _ hkeyLen hq).le]
  · simp

/-- Against the ideal bidirectional experiment, the lifted distinguisher has the law of the
forward distinguisher in the ideal chosen-plaintext experiment. -/
theorem eval_strongPRPIdealGame_liftForwardDistinguisher (blockLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (strongPRPIdealGame blockLen (liftForwardDistinguisher blockLen adversary) n) =
      ProbComp.eval (prpIdealGame blockLen adversary n) := by
  simp only [strongPRPIdealGame, prpIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure]
  congr 1
  funext π
  rw [eval_interpret_liftForwardDistinguisher]
  congr 2
  funext request
  simp only [strongRandomPermOracle, randomPermOracle, randomFunctionOracle, Bool.false_eq_true,
    ↓reduceIte]
  split_ifs
  · rw [List.take_of_length_le List.length_ofFn.le]
  · simp

/-- **Strong PRP security implies PRP security** ([BonehShoup2023], Section 4.1.3). -/
theorem BlockCipher.StrongPRP.prp {E : BlockCipher} (h : E.StrongPRP) : E.PRP := by
  intro adversary hadversary
  refine negligible_of_le (h (liftForwardDistinguisher E.blockLen adversary)
    (isOraclePPT_liftForwardDistinguisher E.blockLen_polyTime hadversary)) fun n => ?_
  dsimp only
  rw [E.eval_strongPRPRealGame_liftForwardDistinguisher,
    eval_strongPRPIdealGame_liftForwardDistinguisher]

/-! ### The PRP/PRF switching lemma -/

/-- **PRP/PRF switching lemma** ([BonehShoup2023], Theorem 4.4): a randomized word-oracle
adversary making at most `Q` queries distinguishes a uniform permutation of `blockLen n`-bit blocks
from a uniform random function on them with advantage at most `Q.choose 2 / 2 ^ blockLen n`. -/
theorem advantage_prpIdealGame_randomFunctionIdealGame_le (blockLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n Q : ℕ) (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage
      (ProbComp.eval (prpIdealGame blockLen adversary n))
      (ProbComp.eval (randomFunctionIdealGame blockLen adversary n)) : ℝ) ≤
      (Q.choose 2 : ℝ) * ((2 : ℝ) ^ blockLen n)⁻¹ := by
  let m := blockLen n
  let adapted : ProbOracleComp (fun _ : BitString m => BitString m) Bool :=
    OracleComp.interpret
      (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
        (fun request : Unit × List Bool => randomFunctionQuery m request.2))
      (adversary n [])
  have hadaptedQ : adapted.IsQueryBounded Q := hQ.interpret fun
    | .inl k => ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin k)
    | .inr request => isQueryBounded_randomFunctionQuery m request.2
  have heval (table : BitString m → BitString m) :
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun request : Unit × List Bool => PMF.pure (randomFunctionOracle m table request.2)))
        (adversary n []) =
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun x => PMF.pure (table x))) adapted := by
    have heager (query : List Bool) :
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle (fun bits => PMF.pure (table bits)))
          (randomFunctionQuery m query) = PMF.pure (randomFunctionOracle m table query) :=
      interpret_randomFunctionQuery ProbComp.unifOracle m table query
    simp only [adapted, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
      ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query, heager]
  have hperm : ProbComp.eval (prpIdealGame blockLen adversary n) =
      (PMF.uniformOfFintype (Equiv.Perm (BitString m))).bind fun π =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle (fun x => PMF.pure (π x))) adapted := by
    simp only [prpIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.eval_interpret, ProbComp.eval_pure]; exact congrArg _ (funext fun π => heval π)
  have hfunc : ProbComp.eval (randomFunctionIdealGame blockLen adversary n) =
      (PMF.uniformOfFintype (BitString m → BitString m)).bind fun f =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle (fun x => PMF.pure (f x))) adapted := by
    simp only [randomFunctionIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.eval_interpret, ProbComp.eval_pure]; exact congrArg _ (funext heval)
  rw [hperm, hfunc, ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
      (PMF.uniformOfFintype (Equiv.Perm (BitString m))) (fun π x => π x) adapted,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
      (PMF.uniformOfFintype (BitString m → BitString m)) (fun f x => f x) adapted]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  rw [Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  have hdet := RandomPermutation.abs_sub_uniformPerm_uniformFunc_le
    (ProbOracleComp.isQueryBounded_fixCoins hadaptedQ ω) PMF.pure true
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_pure] at hdet
  simpa only [Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] using hdet

/-- Asymptotic PRP/PRF switching: when `(2 ^ blockLen n)⁻¹` is negligible, no oracle-PPT
distinguisher tells a uniform permutation from a uniform random function on `blockLen n`-bit
blocks. -/
theorem indistinguishable_prpIdealGame_randomFunctionIdealGame {blockLen : ℕ → ℕ}
    (hneg : Negligible fun n => ((2 : ℝ≥0) ^ blockLen n)⁻¹) :
    Game.Indistinguishable
      (fun adversary n => ProbComp.eval (prpIdealGame blockLen adversary n))
      (fun adversary n => ProbComp.eval (randomFunctionIdealGame blockLen adversary n))
      (IsOraclePPT encBool) := by
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hQ : PolynomiallyBounded fun n => (Q n).choose 2 := by
    refine PolynomiallyBounded.mono_of_le (g := fun n => Q n ^ 2)
      (((PolynomiallyBounded.const c).mul ((PolynomiallyBounded.id.add (.const 2)).pow d)).pow 2)
      fun n => ?_
    change (Q n).choose 2 ≤ Q n ^ 2
    rw [Nat.choose_two_right, sq]
    exact (Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  refine negligible_of_le (hneg.polynomiallyBounded_mul hQ) fun n => ?_
  rw [← NNReal.coe_le_coe]
  have h := advantage_prpIdealGame_randomFunctionIdealGame_le blockLen adversary n (Q n)
    (by simpa [Q] using (hbounds n []).1)
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_ofNat, mul_comm] using h

/-- **A length-preserving pseudorandom permutation is a pseudorandom function**
([BonehShoup2023], Corollary 4.5). -/
theorem BlockCipher.PRP.pseudorandomFunction {E : BlockCipher} (hkey : E.keyLen = id)
    (hblock : E.blockLen = id) (h : E.PRP) :
    PseudorandomFunction (fun key query => E.encrypt key.length key query) where
  polyTime := E.computableInPolyTime_encrypt_comp
    ((ComputableInPolyTime.fst encBits encBits).trans ComputableInPolyTime.length_bits)
    (ComputableInPolyTime.fst encBits encBits)
    (ComputableInPolyTime.snd encBits encBits)
  length_eq key query hq := by
    simpa only [hblock, id_eq] using E.length_encrypt key.length key query
      (by simp [hkey]) (by simp [hblock, hq])
  secure := by
    intro adversary hadversary
    have hswitch := indistinguishable_prpIdealGame_randomFunctionIdealGame (blockLen := id)
      (by simpa only [id_eq, inv_pow] using
        negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)) adversary hadversary
    have hreal (n : ℕ) : ProbComp.eval (E.prpRealGame adversary n) =
        ProbComp.eval
          (prfRealGame (fun key query => E.encrypt key.length key query) adversary n) := by
      simp only [BlockCipher.prpRealGame, prfRealGame, ProbComp.eval_bind,
        BitString.eval_sampleList, hkey, id_eq]
      refine PMF.bind_congr_on_support _ _ _ fun key hk => ?_
      have hlen : key.length = n := BitString.length_of_mem_support_uniformList hk
      simp only [BlockCipher.prpOracle, prfOracle, hblock, id_eq, hlen]
    refine negligible_of_le ((h adversary hadversary).add hswitch) fun n => ?_
    dsimp only [Pi.add_apply]
    rw [← hreal n, ← randomFunctionIdealGame_id, hblock]
    exact Game.advantage_triangle _ _ _

end Cslib.Crypto
