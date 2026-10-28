/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomFunction
public import Complexity.Languages.Probabilistic.RandomPermutation
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Crypto.Negligible.Basic
import Complexity.Languages.Probabilistic.Oracle.CoinFixing
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Uniform
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT
import Mathlib.Tactic.Linarith

/-!
# Uniform computational block ciphers and pseudorandom permutations

A `BlockCipher` ([BonehShoup2023], Section 4.1, Definitions 4.1–4.3) specifies polynomial-time key-
and block-length schedules `keyLen, blockLen : ℕ → ℕ` together with
uniform deterministic polynomial-time `encrypt` and `decrypt` algorithms that preserve block length
and invert one another on every `(keyLen n)`-bit key and `(blockLen n)`-bit block. Each valid key
therefore induces a permutation `BlockCipher.permEquiv` of `BitString (blockLen n)`.

We define two adaptive security notions against uniform `IsOraclePPT encBool` distinguishers:

1. **Forward (chosen-plaintext) pseudorandom permutation (`BlockCipher.PRP`):** an
   `OracleDistinguisher` (`WordOracleComp Unit Bool`) queries encryption on `blockLen n`-bit blocks
   (malformed queries return `[]`) and cannot distinguish a uniformly keyed cipher
   (`BlockCipher.prpRealGame`) from a uniformly random permutation on `BitString (blockLen n)`
   (`prpIdealGame`).
2. **Bidirectional (chosen-ciphertext / strong) pseudorandom permutation
   (`BlockCipher.StrongPRP`):** a `StrongPRPDistinguisher` (`WordOracleComp Bool Bool`) queries
   forward encryption via `(false, x)` and inverse decryption via `(true, y)` (matching
   `RandomPermutation.PermQuery.ofBoolProd`) and cannot distinguish `BlockCipher.strongPRPRealGame`
   from `strongPRPIdealGame`.

Using `ProbOracleComp.table_bind_interpret_eq_coinLaw_bind` and
`RandomPermutation.abs_sub_uniformPerm_uniformFunc_le`, we lift the **PRP/PRF switching lemma**
([BonehShoup2023], Section 4.4, Theorem 4.4) to randomized word-oracle adversaries
(`advantage_prpIdealGame_generalPRFIdealGame_le`, `advantage_prpIdealGame_prfIdealGame_le`), proving
both `BlockCipher.StrongPRP.prp` (`StrongPRP` implies `PRP`) and
`BlockCipher.PRP.pseudorandomFunction` (any `PRP` with `keyLen = id` and `blockLen = id` is a
`PseudorandomFunction`).

## Main definitions

* `Cslib.Crypto.StrongPRPDistinguisher`: adaptive bidirectional (`Bool`-tagged) word-oracle
  distinguisher (`false` = forward encryption, `true` = inverse decryption).
* `Cslib.Crypto.BlockCipher`, `Cslib.Crypto.BlockCipher.permEquiv`: uniform deterministic block
  cipher and its induced permutation on `BitString (blockLen n)`.
* `Cslib.Crypto.BlockCipher.prpOracle`, `Cslib.Crypto.randomPermOracle`,
  `Cslib.Crypto.BlockCipher.prpRealGame`, `Cslib.Crypto.prpIdealGame`,
  `Cslib.Crypto.BlockCipher.PRP`: forward CPA pseudorandom-permutation oracles, games, and security
  predicate.
* `Cslib.Crypto.BlockCipher.strongPRPOracle`, `Cslib.Crypto.strongRandomPermOracle`,
  `Cslib.Crypto.BlockCipher.strongPRPRealGame`, `Cslib.Crypto.strongPRPIdealGame`,
  `Cslib.Crypto.BlockCipher.StrongPRP`: bidirectional strong-PRP oracles, games, and security
  predicate.
* `Cslib.Crypto.generalPRFIdealGame`: uniform random-function word game at block length
  `blockLen n` (specializing to `prfIdealGame` when `blockLen = id`).
* `Cslib.Crypto.liftForwardDistinguisher`: embeds a forward `OracleDistinguisher` into a
  `StrongPRPDistinguisher` on channel `false`.

## Main results

* `Cslib.Crypto.BlockCipher.isPPTOn_prpRealGame`,
  `Cslib.Crypto.BlockCipher.isPPTOn_strongPRPRealGame`: strict PPT certificates for the real PRP
  and strong-PRP experiments against any `IsOraclePPT encBool` distinguisher.
* `Cslib.Crypto.isOraclePPT_liftForwardDistinguisher`,
  `Cslib.Crypto.BlockCipher.StrongPRP.prp`: strong PRP security implies forward PRP security.
* `Cslib.Crypto.advantage_prpIdealGame_generalPRFIdealGame_le`,
  `Cslib.Crypto.advantage_prpIdealGame_prfIdealGame_le`: computational PRP/PRF switching bounds
  `Q.choose 2 / 2 ^ (blockLen n)` for `Q`-query randomized word-oracle adversaries
  ([BonehShoup2023], Section 4.4, Theorem 4.4).
* `Cslib.Crypto.BlockCipher.PRP.pseudorandomFunction`: every `PRP` with `keyLen = id` and
  `blockLen = id` satisfies `PseudorandomFunction`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 4.1 and 4.4 (Definitions 4.1–4.3 and Theorem 4.4).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-- An adaptive test with a unary parameter, an auxiliary word, and a bidirectional (`Bool`-tagged)
word channel: `(false, x)` queries forward encryption and `(true, y)` queries inverse decryption
(matching `RandomPermutation.PermQuery.ofBoolProd`). -/
abbrev StrongPRPDistinguisher := ℕ → List Bool → WordOracleComp Bool Bool

/-- A uniform deterministic block cipher with polynomial-time key- and block-length schedules
`keyLen, blockLen : ℕ → ℕ`, plain polynomial-time `encrypt` and `decrypt` algorithms, length
preservation, and exact two-sided inversion on valid keys and blocks (paraphrase of
[BonehShoup2023], Section 4.1, Definition 4.1). -/
structure BlockCipher where
  /-- Secret-key bit-length at unary security parameter `n`. -/
  keyLen : ℕ → ℕ
  /-- Block bit-length at unary security parameter `n`. -/
  blockLen : ℕ → ℕ
  /-- Plain polynomial-time computability of `keyLen` in unary. -/
  keyLen_polyTime : ComputableInPolyTime keyLen encUnary encUnary
  /-- Plain polynomial-time computability of `blockLen` in unary. -/
  blockLen_polyTime : ComputableInPolyTime blockLen encUnary encUnary
  /-- Deterministic encryption `(key, block) ↦ ciphertext`. -/
  encrypt : List Bool → List Bool → List Bool
  /-- Deterministic decryption `(key, ciphertext) ↦ block`. -/
  decrypt : List Bool → List Bool → List Bool
  /-- Uniform plain polynomial-time certificate for `encrypt`. -/
  encrypt_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => encrypt p.1 p.2)
      (encPair encBits encBits) encBits
  /-- Uniform plain polynomial-time certificate for `decrypt`. -/
  decrypt_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => decrypt p.1 p.2)
      (encPair encBits encBits) encBits
  /-- Encryption preserves `blockLen n` on valid `(keyLen n, blockLen n)` inputs. -/
  encrypt_length_eq : ∀ n key block,
    key.length = keyLen n → block.length = blockLen n →
    (encrypt key block).length = blockLen n
  /-- Decryption preserves `blockLen n` on valid `(keyLen n, blockLen n)` inputs. -/
  decrypt_length_eq : ∀ n key block,
    key.length = keyLen n → block.length = blockLen n →
    (decrypt key block).length = blockLen n
  /-- Left inverse law `decrypt key (encrypt key block) = block` on valid inputs. -/
  decrypt_encrypt : ∀ n key block,
    key.length = keyLen n → block.length = blockLen n →
    decrypt key (encrypt key block) = block
  /-- Right inverse law `encrypt key (decrypt key block) = block` on valid inputs. -/
  encrypt_decrypt : ∀ n key block,
    key.length = keyLen n → block.length = blockLen n →
    encrypt key (decrypt key block) = block

/-- Read a fixed random permutation on `m`-bit blocks, rejecting malformed words with `[]`. -/
@[expose] def randomPermOracle (m : ℕ) (π : Equiv.Perm (BitString m)) (query : List Bool) :
    List Bool :=
  if query.length = m then List.ofFn (π (BitString.ofList m query)) else []

/-- Read a fixed bidirectional permutation on `m`-bit blocks (`false` = `π`, `true` = `π.symm`),
rejecting malformed words with `[]`. -/
@[expose] def strongRandomPermOracle (m : ℕ) (π : Equiv.Perm (BitString m))
    (request : Bool × List Bool) : List Bool :=
  if request.2.length = m then
    List.ofFn ((if request.1 then π.symm else π) (BitString.ofList m request.2))
  else []

/-- Ideal forward random-permutation experiment at block length `blockLen n` (paraphrase of
[BonehShoup2023], Section 4.1.1, Attack Game 4.1). -/
@[expose] noncomputable def prpIdealGame (blockLen : ℕ → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) : ProbComp Bool := do
  let π ← ProbComp.uniform (Equiv.Perm (BitString (blockLen n)))
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin
      (fun request => pure (randomPermOracle (blockLen n) π request.2)))
    (adversary n [])

/-- Ideal bidirectional strong random-permutation experiment at block length `blockLen n`
(paraphrase of [BonehShoup2023], Section 4.1.3, Attack Game 4.3). -/
@[expose] noncomputable def strongPRPIdealGame (blockLen : ℕ → ℕ)
    (adversary : StrongPRPDistinguisher) (n : ℕ) : ProbComp Bool := do
  let π ← ProbComp.uniform (Equiv.Perm (BitString (blockLen n)))
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin
      (fun request => pure (strongRandomPermOracle (blockLen n) π request)))
    (adversary n [])

/-- Ideal random-function experiment at block length `blockLen n` (coinciding with `prfIdealGame`
when `blockLen = id`). -/
@[expose] noncomputable def generalPRFIdealGame (blockLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString (blockLen n) → BitString (blockLen n))
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin
      (fun request => pure (randomFunctionOracle (blockLen n) table request.2)))
    (adversary n [])

/-- At `blockLen = id`, `generalPRFIdealGame` is definitionally `prfIdealGame`. -/
@[simp] theorem generalPRFIdealGame_id (adversary : OracleDistinguisher) (n : ℕ) :
    generalPRFIdealGame id adversary n = prfIdealGame adversary n := rfl

namespace BlockCipher

variable (E : BlockCipher)

/-- Every valid `keyLen n`-bit key induces a bijection on `BitString (E.blockLen n)`. -/
@[expose] def permEquiv (n : ℕ) (key : List Bool) (hkey : key.length = E.keyLen n) :
    Equiv.Perm (BitString (E.blockLen n)) where
  toFun x := BitString.ofList (E.blockLen n) (E.encrypt key (List.ofFn x))
  invFun y := BitString.ofList (E.blockLen n) (E.decrypt key (List.ofFn y))
  left_inv x := by
    dsimp only
    have hx : (List.ofFn x).length = E.blockLen n := List.length_ofFn
    have henc : (E.encrypt key (List.ofFn x)).length = E.blockLen n :=
      E.encrypt_length_eq n key (List.ofFn x) hkey hx
    rw [BitString.ofFn_ofList henc, E.decrypt_encrypt n key (List.ofFn x) hkey hx,
      BitString.ofList_ofFn]
  right_inv y := by
    dsimp only
    have hy : (List.ofFn y).length = E.blockLen n := List.length_ofFn
    have hdec : (E.decrypt key (List.ofFn y)).length = E.blockLen n :=
      E.decrypt_length_eq n key (List.ofFn y) hkey hy
    rw [BitString.ofFn_ofList hdec, E.encrypt_decrypt n key (List.ofFn y) hkey hy,
      BitString.ofList_ofFn]

/-- Forward encryption oracle for `E`, rejecting queries outside `E.blockLen n` with `[]`. -/
@[expose] def prpOracle (n : ℕ) (key query : List Bool) : List Bool :=
  if query.length = E.blockLen n then E.encrypt key query else []

/-- Bidirectional encryption/decryption oracle for `E` (`false` = `encrypt`, `true` = `decrypt`),
rejecting queries outside `E.blockLen n` with `[]`. -/
@[expose] def strongPRPOracle (n : ℕ) (key : List Bool) (request : Bool × List Bool) : List Bool :=
  if request.2.length = E.blockLen n then
    if request.1 then E.decrypt key request.2 else E.encrypt key request.2
  else []

/-- On a valid key, `E.prpOracle` agrees with `randomPermOracle` of `E.permEquiv`. -/
theorem prpOracle_eq_randomPermOracle {n : ℕ} {key : List Bool} (hkey : key.length = E.keyLen n)
    (query : List Bool) :
    E.prpOracle n key query = randomPermOracle (E.blockLen n) (E.permEquiv n key hkey) query := by
  by_cases hq : query.length = E.blockLen n
  · simp only [prpOracle, randomPermOracle, hq, ↓reduceIte]
    change E.encrypt key query =
      List.ofFn (BitString.ofList (E.blockLen n)
        (E.encrypt key (List.ofFn (BitString.ofList (E.blockLen n) query))))
    rw [BitString.ofFn_ofList hq, BitString.ofFn_ofList (E.encrypt_length_eq n key query hkey hq)]
  · simp [prpOracle, randomPermOracle, hq]

/-- On a valid key, `E.strongPRPOracle` agrees with `strongRandomPermOracle` of `E.permEquiv`. -/
theorem strongPRPOracle_eq_strongRandomPermOracle {n : ℕ} {key : List Bool}
    (hkey : key.length = E.keyLen n) (request : Bool × List Bool) :
    E.strongPRPOracle n key request =
      strongRandomPermOracle (E.blockLen n) (E.permEquiv n key hkey) request := by
  by_cases hq : request.2.length = E.blockLen n
  · cases hdir : request.1
    · simp only [strongPRPOracle, strongRandomPermOracle, hq, hdir, ↓reduceIte, Bool.false_eq_true]
      change E.encrypt key request.2 =
        List.ofFn (BitString.ofList (E.blockLen n)
          (E.encrypt key (List.ofFn (BitString.ofList (E.blockLen n) request.2))))
      rw [BitString.ofFn_ofList hq,
        BitString.ofFn_ofList (E.encrypt_length_eq n key request.2 hkey hq)]
    · simp only [strongPRPOracle, strongRandomPermOracle, hq, hdir, ↓reduceIte]
      change E.decrypt key request.2 =
        List.ofFn (BitString.ofList (E.blockLen n)
          (E.decrypt key (List.ofFn (BitString.ofList (E.blockLen n) request.2))))
      rw [BitString.ofFn_ofList hq,
        BitString.ofFn_ofList (E.decrypt_length_eq n key request.2 hkey hq)]
  · simp [strongPRPOracle, strongRandomPermOracle, hq]

/-- Real forward PRP experiment: sample `key ← BitString.sampleList (E.keyLen n)` and answer
forward encryption queries with `E.prpOracle n key` (paraphrase of [BonehShoup2023], Section 4.1.1,
Attack Game 4.1). -/
@[expose] noncomputable def prpRealGame (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp Bool := do
  let key ← BitString.sampleList (E.keyLen n)
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin
      (fun request => pure (E.prpOracle n key request.2)))
    (adversary n [])

/-- Real bidirectional strong-PRP experiment: sample `key ← BitString.sampleList (E.keyLen n)` and
answer forward and inverse queries with `E.strongPRPOracle n key` (paraphrase of [BonehShoup2023],
Section 4.1.3, Attack Game 4.3). -/
@[expose] noncomputable def strongPRPRealGame (adversary : StrongPRPDistinguisher) (n : ℕ) :
    ProbComp Bool := do
  let key ← BitString.sampleList (E.keyLen n)
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin
      (fun request => pure (E.strongPRPOracle n key request)))
    (adversary n [])

/-- Forward (chosen-plaintext) pseudorandom-permutation security against uniform `IsOraclePPT`
distinguishers (paraphrase of [BonehShoup2023], Section 4.1.1, Definition 4.2). -/
@[expose] def PRP : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.prpRealGame adversary n))
    (fun adversary n => ProbComp.eval (prpIdealGame E.blockLen adversary n))
    (IsOraclePPT encBool)

/-- Bidirectional (chosen-ciphertext / strong) pseudorandom-permutation security against uniform
`IsOraclePPT` distinguishers (paraphrase of [BonehShoup2023], Section 4.1.3, Definition 4.3). -/
@[expose] def StrongPRP : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.strongPRPRealGame adversary n))
    (fun adversary n => ProbComp.eval (strongPRPIdealGame E.blockLen adversary n))
    (IsOraclePPT encBool)

/-- The real forward PRP experiment `E.prpRealGame adversary` is uniform strict PPT whenever
`adversary` satisfies `IsOraclePPT encBool`. -/
theorem isPPTOn_prpRealGame {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn encUnary encBool (E.prpRealGame adversary) := by
  let ECaller := encPair encUnary encBits
  let EReq := encPair (encFinEnum Unit) encBits
  let ERest := encPair EReq (encFinEnum Unit)
  let EHandler := encPair ECaller ERest
  have hkey : IsPPTOn encUnary encBits (fun n => BitString.sampleList (E.keyLen n)) :=
    E.keyLen_polyTime.sampleList
  have hprep : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => (p.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) :=
    (ComputableTidilyInPolyTime.fst encUnary encBits).prod (ComputableTidilyInPolyTime.const [])
  have hfstH := ComputableTidilyInPolyTime.fst ECaller ERest
  have hsndH := ComputableTidilyInPolyTime.snd ECaller ERest
  have hnH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => pair.1.1)
      EHandler encUnary :=
    (ComputableTidilyInPolyTime.fst encUnary encBits).comp hfstH
  have hkH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => pair.1.2)
      EHandler encBits :=
    (ComputableTidilyInPolyTime.snd encUnary encBits).comp hfstH
  have hqH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => pair.2.1.2)
      EHandler encBits :=
    (ComputableTidilyInPolyTime.snd (encFinEnum Unit) encBits).comp
      ((ComputableTidilyInPolyTime.fst EReq (encFinEnum Unit)).comp hsndH)
  have hblH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => E.blockLen pair.1.1)
      EHandler encUnary :=
    E.blockLen_polyTime.tidy.comp hnH
  have hguard : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit =>
        pair.2.1.2.length == E.blockLen pair.1.1)
      EHandler encBool :=
    ComputableTidilyInPolyTime.unary_beq
      (ComputableTidilyInPolyTime.length_bits.comp hqH) hblH
  have henc : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit =>
        (List.take (E.blockLen pair.1.1) (E.encrypt pair.1.2 pair.2.1.2), ()))
      EHandler (encPair encBits (encFinEnum Unit)) := by
    have hencRaw : ComputableInPolyTime
        (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => E.encrypt pair.1.2 pair.2.1.2)
        EHandler encBits :=
      E.encrypt_polyTime.comp' ((ComputableInPolyTime.of_tidy hkH).prod
        (ComputableInPolyTime.of_tidy hqH))
    exact (ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bitsTakeWithInput hencRaw.tidy hblH)).prod
      (ComputableInPolyTime.const ())
  have hhandler : IsPPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit =>
        pure (if pair.2.1.2.length = E.blockLen pair.1.1 then
          List.take (E.blockLen pair.1.1) (E.encrypt pair.1.2 pair.2.1.2)
        else [], ())) := by
    refine (IsPPTOn.ite hguard henc.isPPTOn
      (ComputableInPolyTime.const ([], ())).isPPTOn).congr fun pair => ?_
    by_cases h : pair.2.1.2.length = E.blockLen pair.1.1 <;> simp [h]
  have hres : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => E.blockLen pair.1.1)
      (encPair ECaller encBits) encUnary :=
    E.blockLen_polyTime.tidy.comp
      ((ComputableTidilyInPolyTime.fst encUnary encBits).comp
        (ComputableTidilyInPolyTime.fst ECaller encBits))
  have hrun := hadversary.run_interpret_preprocess (State := Unit)
    (operationEncoding := encFinEnum Unit)
    (stateEncoding := encFinEnum Unit)
    (handler := fun (p : ℕ × List Bool) (request : Unit × List Bool) (_ : Unit) =>
      pure (if request.2.length = E.blockLen p.1 then
        List.take (E.blockLen p.1) (E.encrypt p.2 request.2)
      else [], ()))
    (prepare := fun p : ℕ × List Bool => (p.1, []))
    (initial := fun _ => ())
    (resources := fun p _ => E.blockLen p.1)
    hprep hhandler (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) hres
    (fun a request _ _ result hresult => by
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      by_cases hq : request.2.length = E.blockLen a.1 <;> simp [hq])
  have hbody : IsPPTOn (encPair encUnary encBits) encBool (fun p : ℕ × List Bool =>
      Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
          fun (request : Unit × List Bool) (_ : Unit) =>
            pure (if request.2.length = E.blockLen p.1 then
              List.take (E.blockLen p.1) (E.encrypt p.2 request.2)
            else [], ()))
        (adversary p.1 [])).run ()) :=
    hrun.map (ComputableInPolyTime.fst encBool (encFinEnum Unit))
  refine (hkey.bind_with (second := fun n key =>
      Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
          fun (request : Unit × List Bool) (_ : Unit) =>
            pure (if request.2.length = E.blockLen n then
              List.take (E.blockLen n) (E.encrypt key request.2)
            else [], ()))
        (adversary n [])).run ()) hbody).congr fun n => ?_
  simp only [prpRealGame, ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey_supp => ?_
  have hklen : key.length = E.keyLen n := BitString.length_of_mem_support_uniformList hkey_supp
  simp only [ProbComp.eval_map, ProbOracleComp.eval_run_interpret, ProbComp.eval_pure,
    ProbOracleComp.eval_interpret]
  have hH :
      ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
        (fun (request : Unit × List Bool) (_ : Unit) =>
          PMF.pure (if request.2.length = E.blockLen n then
            List.take (E.blockLen n) (E.encrypt key request.2)
          else [], ())) =
      fun q => StateT.lift (ProbOracleComp.handler ProbComp.unifOracle
        (fun request => PMF.pure (E.prpOracle n key request.2)) q) := by
    funext q
    cases q with
    | inl r => rfl
    | inr request =>
      funext u
      dsimp only [ProbOracleComp.handler, prpOracle, StateT.lift]
      by_cases hq : request.2.length = E.blockLen n
      · simp only [hq, ↓reduceIte, PMF.monad_pure_eq_pure,
          List.take_of_length_le (E.encrypt_length_eq n key request.2 hklen hq).le]
        simp
      · simp [hq, PMF.monad_pure_eq_pure]
  rw [hH, OracleComp.run_interpret_lift, ← PMF.monad_map_eq_map, Functor.map_map]
  exact id_map _

/-- The real bidirectional strong-PRP experiment `E.strongPRPRealGame adversary` is uniform strict
PPT whenever `adversary` satisfies `IsOraclePPT encBool`. -/
theorem isPPTOn_strongPRPRealGame {adversary : StrongPRPDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn encUnary encBool (E.strongPRPRealGame adversary) := by
  let ECaller := encPair encUnary encBits
  let EReq := encPair encBool encBits
  let ERest := encPair EReq (encFinEnum Unit)
  let EHandler := encPair ECaller ERest
  have hkey : IsPPTOn encUnary encBits (fun n => BitString.sampleList (E.keyLen n)) :=
    E.keyLen_polyTime.sampleList
  have hprep : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => (p.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) :=
    (ComputableTidilyInPolyTime.fst encUnary encBits).prod (ComputableTidilyInPolyTime.const [])
  have hfstH := ComputableTidilyInPolyTime.fst ECaller ERest
  have hsndH := ComputableTidilyInPolyTime.snd ECaller ERest
  have hnH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit => pair.1.1)
      EHandler encUnary :=
    (ComputableTidilyInPolyTime.fst encUnary encBits).comp hfstH
  have hkH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit => pair.1.2)
      EHandler encBits :=
    (ComputableTidilyInPolyTime.snd encUnary encBits).comp hfstH
  have hreqPair := (ComputableTidilyInPolyTime.fst EReq (encFinEnum Unit)).comp hsndH
  have hdirH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit => pair.2.1.1)
      EHandler encBool :=
    (ComputableTidilyInPolyTime.fst encBool encBits).comp hreqPair
  have hqH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit => pair.2.1.2)
      EHandler encBits :=
    (ComputableTidilyInPolyTime.snd encBool encBits).comp hreqPair
  have hblH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit => E.blockLen pair.1.1)
      EHandler encUnary :=
    E.blockLen_polyTime.tidy.comp hnH
  have hguard : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit =>
        pair.2.1.2.length == E.blockLen pair.1.1)
      EHandler encBool :=
    ComputableTidilyInPolyTime.unary_beq
      (ComputableTidilyInPolyTime.length_bits.comp hqH) hblH
  have hencBranch : IsPPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit =>
        pure (List.take (E.blockLen pair.1.1) (E.encrypt pair.1.2 pair.2.1.2), ())) := by
    have hencRaw : ComputableInPolyTime
        (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit => E.encrypt pair.1.2 pair.2.1.2)
        EHandler encBits :=
      E.encrypt_polyTime.comp' ((ComputableInPolyTime.of_tidy hkH).prod
        (ComputableInPolyTime.of_tidy hqH))
    exact ((ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bitsTakeWithInput hencRaw.tidy hblH)).prod
      (ComputableInPolyTime.const ())).isPPTOn
  have hdecBranch : IsPPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit =>
        pure (List.take (E.blockLen pair.1.1) (E.decrypt pair.1.2 pair.2.1.2), ())) := by
    have hdecRaw : ComputableInPolyTime
        (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit => E.decrypt pair.1.2 pair.2.1.2)
        EHandler encBits :=
      E.decrypt_polyTime.comp' ((ComputableInPolyTime.of_tidy hkH).prod
        (ComputableInPolyTime.of_tidy hqH))
    exact ((ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bitsTakeWithInput hdecRaw.tidy hblH)).prod
      (ComputableInPolyTime.const ())).isPPTOn
  have hboth : IsPPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit =>
        if pair.2.1.1 then
          pure (List.take (E.blockLen pair.1.1) (E.decrypt pair.1.2 pair.2.1.2), ())
        else
          pure (List.take (E.blockLen pair.1.1) (E.encrypt pair.1.2 pair.2.1.2), ())) :=
    IsPPTOn.cond hdirH hdecBranch hencBranch
  have hhandler : IsPPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × (Bool × List Bool) × Unit =>
        pure (if pair.2.1.2.length = E.blockLen pair.1.1 then
          List.take (E.blockLen pair.1.1)
            (if pair.2.1.1 then E.decrypt pair.1.2 pair.2.1.2 else E.encrypt pair.1.2 pair.2.1.2)
        else [], ())) := by
    refine (IsPPTOn.ite hguard hboth
      (ComputableInPolyTime.const ([], ())).isPPTOn).congr fun pair => ?_
    by_cases h : pair.2.1.2.length = E.blockLen pair.1.1 <;> cases pair.2.1.1 <;> simp [h]
  have hres : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => E.blockLen pair.1.1)
      (encPair ECaller encBits) encUnary :=
    E.blockLen_polyTime.tidy.comp
      ((ComputableTidilyInPolyTime.fst encUnary encBits).comp
        (ComputableTidilyInPolyTime.fst ECaller encBits))
  have hrun := hadversary.run_interpret_preprocess (State := Unit)
    (operationEncoding := encBool)
    (stateEncoding := encFinEnum Unit)
    (handler := fun (p : ℕ × List Bool) (request : Bool × List Bool) (_ : Unit) =>
      pure (if request.2.length = E.blockLen p.1 then
        List.take (E.blockLen p.1)
          (if request.1 then E.decrypt p.2 request.2 else E.encrypt p.2 request.2)
      else [], ()))
    (prepare := fun p : ℕ × List Bool => (p.1, []))
    (initial := fun _ => ())
    (resources := fun p _ => E.blockLen p.1)
    hprep hhandler (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) hres
    (fun a request _ _ result hresult => by
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      by_cases hq : request.2.length = E.blockLen a.1 <;> simp [hq])
  have hbody : IsPPTOn (encPair encUnary encBits) encBool (fun p : ℕ × List Bool =>
      Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
          fun (request : Bool × List Bool) (_ : Unit) =>
            pure (if request.2.length = E.blockLen p.1 then
              List.take (E.blockLen p.1)
                (if request.1 then E.decrypt p.2 request.2 else E.encrypt p.2 request.2)
            else [], ()))
        (adversary p.1 [])).run ()) :=
    hrun.map (ComputableInPolyTime.fst encBool (encFinEnum Unit))
  refine (hkey.bind_with (second := fun n key =>
      Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
          fun (request : Bool × List Bool) (_ : Unit) =>
            pure (if request.2.length = E.blockLen n then
              List.take (E.blockLen n)
                (if request.1 then E.decrypt key request.2 else E.encrypt key request.2)
            else [], ()))
        (adversary n [])).run ()) hbody).congr fun n => ?_
  simp only [strongPRPRealGame, ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey_supp => ?_
  have hklen : key.length = E.keyLen n := BitString.length_of_mem_support_uniformList hkey_supp
  simp only [ProbComp.eval_map, ProbOracleComp.eval_run_interpret, ProbComp.eval_pure,
    ProbOracleComp.eval_interpret]
  have hH :
      ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
        (fun (request : Bool × List Bool) (_ : Unit) =>
          PMF.pure (if request.2.length = E.blockLen n then
            List.take (E.blockLen n)
              (if request.1 then E.decrypt key request.2 else E.encrypt key request.2)
          else [], ())) =
      fun q => StateT.lift (ProbOracleComp.handler ProbComp.unifOracle
        (fun request => PMF.pure (E.strongPRPOracle n key request)) q) := by
    funext q
    cases q with
    | inl r => rfl
    | inr request =>
      funext u
      dsimp only [ProbOracleComp.handler, strongPRPOracle, StateT.lift]
      by_cases hq : request.2.length = E.blockLen n
      · cases request.1
        · simp only [hq, ↓reduceIte, Bool.false_eq_true, PMF.monad_pure_eq_pure,
            List.take_of_length_le (E.encrypt_length_eq n key request.2 hklen hq).le]
          simp
        · simp only [hq, ↓reduceIte, PMF.monad_pure_eq_pure,
            List.take_of_length_le (E.decrypt_length_eq n key request.2 hklen hq).le]
          simp
      · simp [hq, PMF.monad_pure_eq_pure]
  rw [hH, OracleComp.run_interpret_lift, ← PMF.monad_map_eq_map, Functor.map_map]
  exact id_map _

end BlockCipher

/-! ### Embedding forward CPA distinguishers into bidirectional Strong-PRP distinguishers -/

/-- Embed a forward-only `OracleDistinguisher` into a `StrongPRPDistinguisher` by forwarding every
query on channel `false` and bounding reply length by `blockLen n` so open substitution stays
uniformly polynomial-time on arbitrary external replies. -/
@[expose] def liftForwardDistinguisher (blockLen : ℕ → ℕ) (adversary : OracleDistinguisher) :
    StrongPRPDistinguisher :=
  fun n aux =>
    Prod.fst <$> (OracleComp.interpret
      (ProbOracleComp.handler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (fun (request : Unit × List Bool) (_ : Unit) =>
          (fun reply => (reply, ())) <$>
            (List.take (blockLen n) <$>
              ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool)
                (false, request.2))))
      (adversary n aux)).run ()

/-- `liftForwardDistinguisher blockLen adversary` satisfies `IsOraclePPT encBool` whenever
`blockLen` is polynomial-time computable in unary and `adversary` satisfies
`IsOraclePPT encBool`. -/
theorem isOraclePPT_liftForwardDistinguisher {blockLen : ℕ → ℕ}
    (hblockLen : ComputableInPolyTime blockLen encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (liftForwardDistinguisher blockLen adversary) := by
  let ECaller := encPair encUnary encBits
  let EReq := encPair (encFinEnum Unit) encBits
  let ERest := encPair EReq (encFinEnum Unit)
  let EHandler := encPair ECaller ERest
  have hfstH := ComputableTidilyInPolyTime.fst ECaller ERest
  have hsndH := ComputableTidilyInPolyTime.snd ECaller ERest
  have hnH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => pair.1.1)
      EHandler encUnary :=
    (ComputableTidilyInPolyTime.fst encUnary encBits).comp hfstH
  have hqH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => pair.2.1.2)
      EHandler encBits :=
    (ComputableTidilyInPolyTime.snd (encFinEnum Unit) encBits).comp
      ((ComputableTidilyInPolyTime.fst EReq (encFinEnum Unit)).comp hsndH)
  have hblH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => blockLen pair.1.1)
      EHandler encUnary :=
    hblockLen.tidy.comp hnH
  have hqTake := IsOraclePPTOn.query_take (Operation := Bool) false hqH hblH
  have hhandler : IsOraclePPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit =>
        (fun reply => (reply, ())) <$>
          (List.take (blockLen pair.1.1) <$>
            ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool)
              (false, pair.2.1.2))) :=
    hqTake.map ((ComputableTidilyInPolyTime.id').prod (ComputableTidilyInPolyTime.const ()))
  have hres : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => blockLen pair.1.1)
      (encPair ECaller encBits) encUnary :=
    hblockLen.tidy.comp
      ((ComputableTidilyInPolyTime.fst encUnary encBits).comp
        (ComputableTidilyInPolyTime.fst ECaller encBits))
  have hrun := hadversary.run_interpret_preprocess_open (External := Bool) (State := Unit)
    (input := ECaller)
    (operationEncoding := encFinEnum Unit)
    (stateEncoding := encFinEnum Unit)
    (handler := fun (p : ℕ × List Bool) (request : Unit × List Bool) (_ : Unit) =>
      (fun reply => (reply, ())) <$>
        (List.take (blockLen p.1) <$>
          ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool)
            (false, request.2)))
    (prepare := id)
    (initial := fun _ => ())
    (resources := fun p _ => blockLen p.1)
    ComputableTidilyInPolyTime.id' hhandler (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) hres
    (fun a request _ _ result hresult => by
      obtain ⟨reply, hreply, rfl⟩ := ProbOracleComp.mem_support_map hresult
      obtain ⟨raw, _, rfl⟩ := ProbOracleComp.mem_support_map hreply
      exact ⟨trivial, by rw [List.length_take]; exact Nat.min_le_left _ _, by simp [encFinEnum]⟩)
  exact (hrun.map (ComputableTidilyInPolyTime.fst encBool (encFinEnum Unit))).isOraclePPT

/-- Against `E.strongPRPRealGame`, `liftForwardDistinguisher E.blockLen adversary` has the exact
distribution of `E.prpRealGame adversary`. -/
theorem BlockCipher.eval_strongPRPRealGame_liftForwardDistinguisher (E : BlockCipher)
    (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (E.strongPRPRealGame (liftForwardDistinguisher E.blockLen adversary) n) =
      ProbComp.eval (E.prpRealGame adversary n) := by
  simp only [BlockCipher.strongPRPRealGame, BlockCipher.prpRealGame, ProbComp.eval_bind,
    BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey_supp => ?_
  have hklen : key.length = E.keyLen n := BitString.length_of_mem_support_uniformList hkey_supp
  simp only [liftForwardDistinguisher, ProbOracleComp.eval_interpret, ProbComp.eval_pure,
    OracleComp.interpret_map]
  have hH :
      ProbOracleComp.handler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (fun (request : Unit × List Bool) (_ : Unit) =>
          (fun reply => (reply, ())) <$>
            (List.take (E.blockLen n) <$>
              ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool)
                (false, request.2))) =
      fun q => StateT.lift
        (ProbOracleComp.handler
          (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
          (fun request : Unit × List Bool =>
            List.take (E.blockLen n) <$>
              ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool)
                (false, request.2)) q) := by
    funext q
    cases q with
    | inl k => rfl
    | inr request =>
      funext u
      cases u
      simp only [ProbOracleComp.handler, StateT.lift, bind_pure_comp]
  rw [hH, OracleComp.run_interpret_lift, OracleComp.interpret_map,
    ProbComp.eval_map, ProbComp.eval_map, PMF.map_comp,
    show Prod.fst ∘ (fun a : Bool => (a, ())) = id from rfl, PMF.map_id,
    ProbOracleComp.eval_interpret, OracleComp.interpret_interpret]
  simp only [ProbComp.eval_pure]
  congr 1; funext q
  cases q with
  | inl k => simp [ProbOracleComp.handler, ProbOracleComp.sample, ProbComp.unifFin]
  | inr request =>
    dsimp only [ProbOracleComp.handler, BlockCipher.strongPRPOracle, BlockCipher.prpOracle]
    by_cases hq : request.2.length = E.blockLen n
    · simp [hq, PMF.monad_map_eq_map,
        List.take_of_length_le (E.encrypt_length_eq n key request.2 hklen hq).le]
    · simp [hq, PMF.monad_map_eq_map]

/-- Against `strongPRPIdealGame blockLen`, `liftForwardDistinguisher blockLen adversary` has the
exact distribution of `prpIdealGame blockLen adversary`. -/
theorem eval_strongPRPIdealGame_liftForwardDistinguisher (blockLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (strongPRPIdealGame blockLen (liftForwardDistinguisher blockLen adversary) n) =
      ProbComp.eval (prpIdealGame blockLen adversary n) := by
  simp only [strongPRPIdealGame, prpIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform]
  congr 1; funext π
  simp only [liftForwardDistinguisher, ProbOracleComp.eval_interpret, ProbComp.eval_pure,
    OracleComp.interpret_map]
  have hH :
      ProbOracleComp.handler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (fun (request : Unit × List Bool) (_ : Unit) =>
          (fun reply => (reply, ())) <$>
            (List.take (blockLen n) <$>
              ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool)
                (false, request.2))) =
      fun q => StateT.lift
        (ProbOracleComp.handler
          (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
          (fun request : Unit × List Bool =>
            List.take (blockLen n) <$>
              ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool)
                (false, request.2)) q) := by
    funext q
    cases q with
    | inl k => rfl
    | inr request =>
      funext u
      cases u
      simp only [ProbOracleComp.handler, StateT.lift, bind_pure_comp]
  rw [hH, OracleComp.run_interpret_lift, OracleComp.interpret_map,
    ProbComp.eval_map, ProbComp.eval_map, PMF.map_comp,
    show Prod.fst ∘ (fun a : Bool => (a, ())) = id from rfl, PMF.map_id,
    ProbOracleComp.eval_interpret, OracleComp.interpret_interpret]
  simp only [ProbComp.eval_pure]
  congr 1; funext q
  cases q with
  | inl k => simp [ProbOracleComp.handler, ProbOracleComp.sample, ProbComp.unifFin]
  | inr request =>
    dsimp only [ProbOracleComp.handler, strongRandomPermOracle, randomPermOracle]
    by_cases hq : request.2.length = blockLen n
    · simp [hq, PMF.monad_map_eq_map, List.take_of_length_le List.length_ofFn.le]
    · simp [hq, PMF.monad_map_eq_map]

/-- **Strong PRP security implies forward PRP security** ([BonehShoup2023], Section 4.1.3). -/
theorem BlockCipher.StrongPRP.prp {E : BlockCipher} (h : E.StrongPRP) : E.PRP := by
  intro adversary hadversary
  have hstrong := h (liftForwardDistinguisher E.blockLen adversary)
    (isOraclePPT_liftForwardDistinguisher E.blockLen_polyTime hadversary)
  refine negligible_of_le hstrong fun n => ?_
  dsimp only
  rw [E.eval_strongPRPRealGame_liftForwardDistinguisher,
    eval_strongPRPIdealGame_liftForwardDistinguisher]

/-! ### Computational PRP/PRF switching lemma -/

/-- `randomFunctionQuery m query` makes at most `1` external query. -/
theorem isQueryBounded_randomFunctionQuery (m : ℕ) (query : List Bool) :
    (randomFunctionQuery m query).IsQueryBounded 1 := by
  unfold randomFunctionQuery
  by_cases h : query.length = m
  · simp only [h, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_def]
    simpa only [Nat.add_zero] using
      (ProbOracleComp.IsQueryBounded.query (BitString.ofList m query)).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0
  · simp only [h, ↓reduceIte]
    exact OracleComp.IsCostBounded.pure [] 1

private theorem isQueryBounded_adaptWordToBitString {m Q : ℕ}
    {prog : WordOracleComp Unit Bool} (hQ : prog.IsQueryBounded Q) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
        (fun request : Unit × List Bool => randomFunctionQuery m request.2))
      prog).IsQueryBounded Q := by
  refine hQ.interpret fun q => ?_
  cases q with
  | inl k => exact ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin k)
  | inr request => exact isQueryBounded_randomFunctionQuery m request.2

/-- **Computational PRP/PRF switching lemma** ([BonehShoup2023], Section 4.4, Theorem 4.4): any
adaptive randomized word-oracle adversary making at most `Q` queries distinguishes a uniform random
permutation on `BitString (blockLen n)` (`prpIdealGame`) from a uniform random function on
`BitString (blockLen n)` (`generalPRFIdealGame`) with advantage at most
`Q.choose 2 / 2 ^ (blockLen n)`. -/
theorem advantage_prpIdealGame_generalPRFIdealGame_le (blockLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n Q : ℕ)
    (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage
      (ProbComp.eval (prpIdealGame blockLen adversary n))
      (ProbComp.eval (generalPRFIdealGame blockLen adversary n)) : ℝ) ≤
      (Q.choose 2 : ℝ) * ((2 : ℝ) ^ (blockLen n))⁻¹ := by
  let m := blockLen n
  let adapted : ProbOracleComp (fun _ : BitString m => BitString m) Bool :=
    OracleComp.interpret
      (ProbOracleComp.handler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
        (fun request : Unit × List Bool => randomFunctionQuery m request.2))
      (adversary n [])
  have hadaptedQ : adapted.IsQueryBounded Q := isQueryBounded_adaptWordToBitString hQ
  have hperm_eq :
      ProbComp.eval (prpIdealGame blockLen adversary n) =
      (PMF.uniformOfFintype (Equiv.Perm (BitString m))).bind fun π =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle (fun x => PMF.pure (π x)))
          adapted := by
    have heager (π : Equiv.Perm (BitString m)) (query : List Bool) :
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle (fun bits => PMF.pure (π bits)))
          (randomFunctionQuery m query) = PMF.pure (randomPermOracle m π query) :=
      interpret_randomFunctionQuery ProbComp.unifOracle m (fun x => π x) query
    simp only [prpIdealGame, adapted, m, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.eval_interpret, ProbComp.eval_pure, OracleComp.interpret_interpret,
      ProbOracleComp.interpret_handler, ProbOracleComp.interpret_sample, ProbComp.unifFin,
      OracleComp.interpret_query, heager]
  have hfunc_eq :
      ProbComp.eval (generalPRFIdealGame blockLen adversary n) =
      (PMF.uniformOfFintype (BitString m → BitString m)).bind fun f =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle (fun x => PMF.pure (f x)))
          adapted := by
    have heager (f : BitString m → BitString m) (query : List Bool) :
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle (fun bits => PMF.pure (f bits)))
          (randomFunctionQuery m query) = PMF.pure (randomFunctionOracle m f query) :=
      interpret_randomFunctionQuery ProbComp.unifOracle m f query
    simp only [generalPRFIdealGame, adapted, m, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.eval_interpret, ProbComp.eval_pure, OracleComp.interpret_interpret,
      ProbOracleComp.interpret_handler, ProbOracleComp.interpret_sample, ProbComp.unifFin,
      OracleComp.interpret_query, heager]
  rw [hperm_eq, hfunc_eq,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
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

/-- Specialization of `advantage_prpIdealGame_generalPRFIdealGame_le` to `blockLen = id`
(`prfIdealGame`). -/
theorem advantage_prpIdealGame_prfIdealGame_le (adversary : OracleDistinguisher) (n Q : ℕ)
    (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage
      (ProbComp.eval (prpIdealGame id adversary n))
      (ProbComp.eval (prfIdealGame adversary n)) : ℝ) ≤
      (Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
  simpa only [generalPRFIdealGame_id, id_eq] using
    advantage_prpIdealGame_generalPRFIdealGame_le id adversary n Q hQ

/-- Asymptotic PRP/PRF switching: whenever `n ↦ (2 ^ (blockLen n))⁻¹` is negligible, no uniform
`IsOraclePPT encBool` distinguisher can tell `prpIdealGame blockLen` apart from
`generalPRFIdealGame blockLen`. -/
theorem indistinguishable_prpIdealGame_generalPRFIdealGame {blockLen : ℕ → ℕ}
    (hneg : Negligible fun n => ((2 : ℝ≥0) ^ (blockLen n))⁻¹) :
    Game.Indistinguishable
      (fun adversary n => ProbComp.eval (prpIdealGame blockLen adversary n))
      (fun adversary n => ProbComp.eval (generalPRFIdealGame blockLen adversary n))
      (IsOraclePPT encBool) := by
  intro adversary hadversary
  obtain ⟨cA, dA, hQb⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => cA * (n + 2) ^ dA
  have hQ_poly : PolynomiallyBounded (fun n => (Q n).choose 2) := by
    refine PolynomiallyBounded.mono_of_le (g := fun n => Q n ^ 2) (by dsimp only [Q]; fun_prop)
      fun n => ?_
    rw [Nat.choose_two_right]
    have : Q n * (Q n - 1) ≤ Q n * Q n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    simpa only [sq] using (Nat.div_le_self _ 2).trans this
  refine negligible_of_le (hneg.polynomiallyBounded_mul hQ_poly) fun n => ?_
  rw [← NNReal.coe_le_coe]
  have hsw := advantage_prpIdealGame_generalPRFIdealGame_le blockLen adversary n (Q n)
    (by simpa [Q] using (hQb n []).1)
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_ofNat, mul_comm] using hsw

/-- **Every forward `PRP` with `keyLen = id` and `blockLen = id` is a `PseudorandomFunction`**
([BonehShoup2023], Section 4.4, Proposition 4.5 / Theorem 4.4). -/
theorem BlockCipher.PRP.pseudorandomFunction {E : BlockCipher}
    (hkey : E.keyLen = id) (hblock : E.blockLen = id) (hPRP : E.PRP) :
    PseudorandomFunction E.encrypt where
  polyTime := E.encrypt_polyTime
  length_eq key query hq := by
    have hk : key.length = E.keyLen key.length := by simp [hkey]
    have hqb : query.length = E.blockLen key.length := by simp [hblock, hq]
    simpa [hblock] using E.encrypt_length_eq key.length key query hk hqb
  secure := by
    intro adversary hadversary
    have hsw := indistinguishable_prpIdealGame_generalPRFIdealGame (blockLen := id)
      (by
        simpa only [id_eq, inv_pow] using
          negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num))
      adversary hadversary
    have hreal_eq (n : ℕ) : E.prpRealGame adversary n = prfRealGame E.encrypt adversary n := by
      simp [BlockCipher.prpRealGame, prfRealGame, BlockCipher.prpOracle, prfOracle, hkey, hblock]
    refine negligible_of_le ((hPRP adversary hadversary).add hsw) fun n => ?_
    dsimp only [Pi.add_apply]
    rw [← hreal_eq n, ← generalPRFIdealGame_id]
    have hb : prpIdealGame E.blockLen adversary n = prpIdealGame id adversary n := by rw [hblock]
    rw [← hb]
    exact Game.advantage_triangle _ (ProbComp.eval (prpIdealGame E.blockLen adversary n)) _

end Cslib.Crypto
