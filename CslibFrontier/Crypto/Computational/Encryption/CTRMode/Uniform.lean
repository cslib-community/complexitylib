/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.IVStream.Reduction
public import CslibFrontier.Foundations.Data.BitString.Counter
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Computational.Encryption.BlockModeWord
import CslibFrontier.Crypto.Computational.Encryption.CTRMode
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Randomized counter mode from a uniform pseudorandom function

Randomized counter mode ([BonehShoup2023], Section 5.4.2, printed p. 189) encrypts a message of
`v` blocks `m[0], …, m[v - 1]` under a key `k` by drawing a uniform initial value `x` and sending
`(x, c)` with `c[j] = F(k, x + j mod N) ⊕ m[j]`. Here the security parameter `n` is the block
length and `N = 2 ^ n`: the PRF `family` takes `n`-bit keys and `n`-bit inputs to `n`-bit outputs,
and the `j`-th counter block is `ctrWordCounter n x j`, the `n`-bit little-endian representation
of `x + j mod 2 ^ n`. A message is any word made of whole blocks. `ctrWordEncrypt` outputs the
word `x ++ c`, and `ctrWordDecrypt` inverts it; both are the shared envelope `ivStreamEncrypt`,
`ivStreamDecrypt` with the counter keystream `ctrWordKeystream`.

Security is many-query left-or-right CPA security (`SymmetricINDCPAOn`, Attack Game 5.2) on
equal-length pairs of whole blocks (`blockPairValid`), in the standard model, against uniform
strict oracle-PPT adversaries. The PRF distinguisher `ctrToPrfDistinguisher adversary bit` is the
shared stream reduction `ivStreamToPrfDistinguisher` with the counter keystream queries
`ctrKeystreamQueries`: it runs the adversary and answers each admissible request itself, drawing
the initial value and obtaining each keystream block with one query to its own function oracle,
keeping at most `n` bits of the reply.

1. It is uniform strict oracle PPT whenever the adversary is
   (`isOraclePPT_ctrToPrfDistinguisher`).
2. Against the keyed oracle, its output law is that of the adversary in the CPA game with
   challenge bit `bit` (`eval_prfRealGame_ctrToPrfDistinguisher`).
3. Against a uniform random function, it is the typed reduction `ctrReduction ctrModCounter` of
   `CTRMode.lean` run on the adversary read as a block-mode adversary (`blockModeWordAdversary`),
   and the typed collision
   bound `advantage_idealExperiment_ctrReduction_le` applies. This gives the concrete bound
   `advantage_ctrWordCPAGame_le` and then `PseudorandomFunction.indcpa_ctrWordEncrypt`.

## Deviations from Theorem 5.3

* **No cap on the number of blocks.** The source fixes a poly-bounded `ℓ` and the message space
  `Y^{≤ℓ}`. Here every whole-block length is admitted, which implies the statement for every `ℓ`.
  A PPT adversary can only write polynomially long requests.
* **Two fixed-bit distinguishers and a cruder collision term.** As for `prfCipher`, the bound uses
  the PRF advantages of `ctrToPrfDistinguisher adversary false` and
  `ctrToPrfDistinguisher adversary true` instead of one distinguisher that flips the bit. Its
  collision term is `2 (Q L) ^ 2 / 2 ^ n` for `Q` requests of at most `L` bits, rather than
  `2 Q ^ 2 ℓ / N`, because it bounds the blocks of all requests by `Q L` and the typed bound is
  quadratic in that total.

## Main definitions

* `Cslib.Crypto.ctrWordCounter`, `Cslib.Crypto.ctrWordKeystream`: counter blocks and keystream.
* `Cslib.Crypto.ctrWordEncrypt`, `Cslib.Crypto.ctrWordDecrypt`: the cipher on whole-block words.
* `Cslib.Crypto.ctrKeystreamStep`, `Cslib.Crypto.ctrKeystreamQueries`: the keystream from the
  function oracle.
* `Cslib.Crypto.ctrToPrfDistinguisher`: the reduction to the PRF game.

## Main results

* `Cslib.Crypto.ctrWordDecrypt_ctrWordEncrypt`: decryption inverts encryption.
* `Cslib.Crypto.isPPTOn_ctrWordEncrypt`, `Cslib.Crypto.computableInPolyTime_ctrWordDecrypt`:
  efficiency of the honest algorithms.
* `Cslib.Crypto.isOraclePPT_ctrToPrfDistinguisher`: the reduction is uniform strict oracle PPT.
* `Cslib.Crypto.eval_prfRealGame_ctrToPrfDistinguisher`: the real PRF game of the reduction is
  the CPA game.
* `Cslib.Crypto.advantage_ctrWordCPAGame_le`: the concrete CPA bound.
* `Cslib.Crypto.PseudorandomFunction.indcpa_ctrWordEncrypt`: counter mode is CPA-secure for every
  `PseudorandomFunction`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.3 (Attack Game 5.2, printed pp. 181–182), Section 5.4.2 (printed p. 189) and
  Theorem 5.3 (printed p. 191).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-! ### The cipher -/

/-- The `j`-th counter block from initial value `iv`: the `n`-bit little-endian representation of
`iv + j mod 2 ^ n`, reading `iv` least significant bit first. -/
@[expose]
def ctrWordCounter (n : ℕ) (iv : List Bool) (j : ℕ) : List Bool :=
  BitString.lowBits n (BitString.lsbValue iv + j)

/-- The keystream of `blocks` blocks under `family k` from initial value `iv`: the outputs at the
counter blocks `0, …, blocks - 1`, concatenated. -/
@[expose]
def ctrWordKeystream (family : List Bool → List Bool → List Bool) (n : ℕ) (k iv : List Bool)
    (blocks : ℕ) : List Bool :=
  (List.range blocks).flatMap fun j => family k (ctrWordCounter n iv j)

/-- Randomized counter-mode encryption ([BonehShoup2023], Section 5.4.2): draw a uniform `n`-bit
initial value `iv` and output `iv` followed by the message XORed with the keystream of
`msg.length / n` blocks. -/
noncomputable def ctrWordEncrypt (family : List Bool → List Bool → List Bool) :
    ℕ → List Bool → List Bool → ProbComp (List Bool) :=
  ivStreamEncrypt (ctrWordKeystream family)

/-- Counter-mode decryption: accept an `n`-bit initial value followed by whole blocks, and XOR the
blocks with the keystream from that initial value. -/
def ctrWordDecrypt (family : List Bool → List Bool → List Bool) :
    ℕ → List Bool → List Bool → Option (List Bool) :=
  ivStreamDecrypt (ctrWordKeystream family)

@[simp]
theorem length_ctrWordCounter (n : ℕ) (iv : List Bool) (j : ℕ) :
    (ctrWordCounter n iv j).length = n := by
  simp [ctrWordCounter, BitString.lowBits]

/-- Under a key of length `n`, a family with `n`-bit outputs on `n`-bit inputs produces a
keystream of `blocks * n` bits. -/
theorem length_ctrWordKeystream {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) (iv : List Bool) (blocks : ℕ) :
    (ctrWordKeystream family n k iv blocks).length = blocks * n := by
  induction blocks with
  | zero => simp [ctrWordKeystream]
  | succ blocks ih =>
    have hblock : (family k (ctrWordCounter n iv blocks)).length = n := by
      rw [hlen k _ (by rw [length_ctrWordCounter, hk]), hk]
    rw [ctrWordKeystream, List.range_succ, List.flatMap_append, List.length_append,
      ← ctrWordKeystream, ih]
    simp [hblock, Nat.succ_mul]

/-- Decryption inverts encryption on whole-block messages under keys of length `n`. -/
theorem ctrWordDecrypt_ctrWordEncrypt {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) {msg : List Bool} (hmsg : msg.length % n = 0)
    {ct : List Bool} (hct : ct ∈ (ProbComp.eval (ctrWordEncrypt family n k msg)).support) :
    ctrWordDecrypt family n k ct = some msg :=
  ivStreamDecrypt_ivStreamEncrypt (fun iv _ => length_ctrWordKeystream hlen hk iv _) hmsg hct

/-! ### Efficiency of the honest algorithms -/

/-- Counter blocks are computable in polynomial time from a unary width, the initial value and a
unary offset. -/
theorem computableInPolyTime_ctrWordCounter {α : Type} {input : α ↪ List Bool}
    {n j : α → ℕ} {iv : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (hiv : ComputableInPolyTime iv input encBits)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => ctrWordCounter (n a) (iv a) (j a)) input encBits := by
  have hvalue : ComputableInPolyTime (fun a => BitString.lsbValue (iv a)) input encNat := by
    simp only [BitString.lsbValue_eq_binaryValue_reverse]
    exact ComputableInPolyTime.bitsBinaryValue.comp
      ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsReverse).comp hiv)
  unfold ctrWordCounter
  exact ComputableInPolyTime.bitsLow hn
    (ComputableInPolyTime.binary_add' hvalue
      ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp hj))

/-- The keystream is computable in polynomial time from the family's evaluator. -/
theorem computableInPolyTime_ctrWordKeystream {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    {α : Type} {input : α ↪ List Bool} {n blocks : α → ℕ} {k iv : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encBits)
    (hiv : ComputableInPolyTime iv input encBits)
    (hblocks : ComputableInPolyTime blocks input encUnary) :
    ComputableInPolyTime (fun a => ctrWordKeystream family (n a) (k a) (iv a) (blocks a))
      input encBits := by
  unfold ctrWordKeystream
  refine ComputableInPolyTime.flatMapToBitsWithInput (enc := encUnary)
    (ComputableInPolyTime.range.comp hblocks) ?_
  exact hpoly.comp ((hk.comp (ComputableInPolyTime.fst _ _)).prod
    (computableInPolyTime_ctrWordCounter (hn.comp (ComputableInPolyTime.fst _ _))
      (hiv.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _)))

/-- The keystream as a function of `(n, k, iv, blocks)` is computable in polynomial time. -/
private theorem computableInPolyTime_ctrWordKeystream_tuple
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime
      (fun ((n, k, iv, blocks) : ℕ × List Bool × List Bool × ℕ) =>
        ctrWordKeystream family n k iv blocks)
      (encPair encUnary (encPair encBits (encPair encBits encUnary))) encBits :=
  computableInPolyTime_ctrWordKeystream hpoly (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop)

/-- Counter-mode encryption is uniformly strict PPT in `(n, k, msg)`. -/
theorem isPPTOn_ctrWordEncrypt {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ((n, k, msg) : ℕ × List Bool × List Bool) => ctrWordEncrypt family n k msg) :=
  isPPTOn_ivStreamEncrypt (computableInPolyTime_ctrWordKeystream_tuple hpoly)

/-- Counter-mode decryption is computable in polynomial time on `(n, k, ct)`. -/
theorem computableInPolyTime_ctrWordDecrypt {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime
      (fun ((n, k, ct) : ℕ × List Bool × List Bool) => ctrWordDecrypt family n k ct)
      (encKeyedInput encBits) (encOption encBits) :=
  computableInPolyTime_ivStreamDecrypt (computableInPolyTime_ctrWordKeystream_tuple hpoly)

/-! ### The reduction to the PRF game -/

/-- One keystream block from the function oracle: query the `j`-th counter block, keep at most
`n` bits of the reply and append them to the keystream so far. -/
def ctrKeystreamStep (n : ℕ) (iv : List Bool) (state : ℕ × List Bool) :
    WordOracleComp Unit (ℕ × List Bool) :=
  (fun block => (state.1 + 1, state.2 ++ block)) <$>
    (List.take n <$> ProbOracleComp.query ((), ctrWordCounter n iv state.1))

/-- The keystream of `blocks` blocks from the function oracle, with one query per block. -/
def ctrKeystreamQueries (n : ℕ) (iv : List Bool) (blocks : ℕ) : WordOracleComp Unit (List Bool) :=
  Prod.snd <$> OracleComp.iterate blocks (ctrKeystreamStep n iv) (0, [])

/-- The PRF distinguisher built from a left-or-right CPA adversary against counter mode
([BonehShoup2023], proof of Theorem 5.3): the shared stream reduction
`ivStreamToPrfDistinguisher` with the counter keystream queries `ctrKeystreamQueries`. -/
noncomputable abbrev ctrToPrfDistinguisher (adversary : OracleDistinguisher) (bit : Bool) :
    OracleDistinguisher :=
  ivStreamToPrfDistinguisher ctrKeystreamQueries adversary bit

/-- Answered by a deterministic oracle `g` with `n`-bit answers on `n`-bit requests, the keystream
queries return the concatenated answers at the counter blocks. -/
theorem run_ctrKeystreamQueries_of_length {n : ℕ} {g : List Bool → List Bool}
    (hg : ∀ x, x.length = n → (g x).length = n) (iv : List Bool) (blocks : ℕ) :
    (ctrKeystreamQueries n iv blocks).run (fun request => pure (g request.2)) =
      pure ((List.range blocks).flatMap fun j => g (ctrWordCounter n iv j)) := by
  have hloop : ProbOracleComp.run (OracleComp.iterate blocks (ctrKeystreamStep n iv) (0, []))
      (fun request => pure (g request.2)) =
      pure (blocks, (List.range blocks).flatMap fun j => g (ctrWordCounter n iv j)) := by
    induction blocks with
    | zero => rfl
    | succ blocks ih =>
      have hblock : (g (ctrWordCounter n iv blocks)).length = n :=
        hg _ (length_ctrWordCounter n iv blocks)
      rw [OracleComp.iterate_succ, ProbOracleComp.run_bind, ih, pure_bind, ctrKeystreamStep]
      simp [List.take_of_length_le hblock.le, List.range_succ]
  rw [ctrKeystreamQueries, ProbOracleComp.run_map, hloop, map_pure]

/-- Answered by the keyed oracle under a key of length `n`, the keystream queries compute the
keystream. -/
theorem run_ctrKeystreamQueries {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) (iv : List Bool) (blocks : ℕ) :
    (ctrKeystreamQueries n iv blocks).run (fun request => pure (prfOracle family n k request.2)) =
      pure (ctrWordKeystream family n k iv blocks) := by
  rw [run_ctrKeystreamQueries_of_length (fun x hx => by
    rw [prfOracle, ite_eq_left hx, hlen k x (by rw [hx, hk]), hk])]
  simp [ctrWordKeystream, prfOracle]

/-- **Real game.** Against the keyed oracle, `ctrToPrfDistinguisher adversary bit` has the output
law of `adversary` in the counter-mode CPA game with challenge bit `bit`. -/
theorem eval_prfRealGame_ctrToPrfDistinguisher {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval (prfRealGame family (ctrToPrfDistinguisher adversary bit) n) =
      ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ctrWordEncrypt family) adversary bit n) :=
  eval_prfRealGame_ivStreamToPrfDistinguisher
    (fun _ hk iv _ blocks => run_ctrKeystreamQueries hlen hk iv blocks) adversary bit

/-- The keystream queries are strict oracle PPT: each step makes one charged query and grows the
encoded state by at most `n + 2` bits. -/
private theorem isOraclePPTOn_ctrKeystreamQueries {α : Type} {input : α ↪ List Bool}
    {n blocks : α → ℕ} {iv : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (hiv : ComputableInPolyTime iv input encBits)
    (hblocks : ComputableInPolyTime blocks input encUnary) :
    IsOraclePPTOn (Operation := Unit) input encBits
      (fun a => ctrKeystreamQueries (n a) (iv a) (blocks a)) := by
  let EStep := encPair input (encPair encUnary encBits)
  have hnStep : ComputableInPolyTime (fun pair : α × (ℕ × List Bool) => n pair.1) EStep encUnary :=
    hn.comp (ComputableInPolyTime.fst _ _)
  have hquery : IsOraclePPTOn (Operation := Unit) EStep encBits
      (fun pair : α × (ℕ × List Bool) => List.take (n pair.1) <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), ctrWordCounter (n pair.1) (iv pair.1) pair.2.1)) :=
    IsOraclePPTOn.query_take' ()
      (computableInPolyTime_ctrWordCounter hnStep (hiv.comp (ComputableInPolyTime.fst _ _))
        (by dsimp only [EStep]; fun_prop))
      hnStep
  have hstep : IsOraclePPTOn EStep (encPair encUnary encBits)
      (fun pair : α × (ℕ × List Bool) => ctrKeystreamStep (n pair.1) (iv pair.1) pair.2) :=
    hquery.map_with' (f := fun pair block => (pair.2.1 + 1, pair.2.2 ++ block))
      (by dsimp only [EStep]; fun_prop)
  have hnBound : PolyBounded (fun a => (input a).length) n := by
    simpa only [encUnary_apply, List.length_replicate] using hn.polyBounded_length
  have hgrowthPoly : PolyBounded (fun a => (input a).length) (fun a => n a + 2) :=
    hnBound.add (PolyBounded.const 2)
  have hloop := IsOraclePPTOn.iterateWith_of_bounded_growth'
    (stateEncoding := encPair encUnary encBits)
    (initial := fun _ => ((0 : ℕ), ([] : List Bool))) (count := blocks)
    (step := fun a state => ctrKeystreamStep (n a) (iv a) state)
    hblocks (ComputableInPolyTime.const _) hstep (growth := fun a => n a + 2) hgrowthPoly
    (fun a state next hnext => by
      obtain ⟨block, hblock, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hblock
      have htake := List.length_take_le (n a) reply
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
        List.length_append]
      omega)
  exact hloop.map' (ComputableInPolyTime.snd _ _)

/-- **Efficiency of the reduction.** For every uniform strict oracle-PPT adversary,
`ctrToPrfDistinguisher adversary bit` is uniform strict oracle PPT. -/
theorem isOraclePPT_ctrToPrfDistinguisher {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool (ctrToPrfDistinguisher adversary bit) :=
  isOraclePPT_ivStreamToPrfDistinguisher
    (isOraclePPTOn_ctrKeystreamQueries (by fun_prop) (by fun_prop) (by fun_prop)) hadversary bit

/-! ### The ideal game -/

/-- The word counter at the bits of `iv` is the bits of `ctrModCounter iv j`. -/
private theorem ctrWordCounter_ofFn {n : ℕ} (iv : BitString n) (j : ℕ) :
    ctrWordCounter n (List.ofFn iv) j = List.ofFn (ctrModCounter iv j) := by
  rw [ctrWordCounter, BitString.lsbValue_ofFn, ctrModCounter,
    ← BitString.lowBits_eq_ofFn_equivFin_symm, BitString.lowBits_mod_two_pow]

/-- Answered by the oracle of a fixed function `f`, the keystream queries from the bits of `iv`
compute the bits of the typed mask blocks `ctrMaskBlocks f ctrModCounter iv blocks`. -/
private theorem run_ctrKeystreamQueries_randomFunction {n : ℕ} (f : BitString n → BitString n)
    (iv : BitString n) (blocks : ℕ) :
    (ctrKeystreamQueries n (List.ofFn iv) blocks).run
        (fun request => pure (randomFunctionOracle n f request.2)) =
      pure ((ctrMaskBlocks f ctrModCounter iv blocks).flatMap List.ofFn) := by
  rw [run_ctrKeystreamQueries_of_length fun x hx => by simp [randomFunctionOracle, hx]]
  simp [ctrMaskBlocks, ctrWordCounter_ofFn, randomFunctionOracle, List.flatMap_map]

/-- Against a uniform random function, the reduction for an adversary whose requests have at most
`ℓ` bits is the typed CTR reduction for the block-mode adversary. -/
private theorem eval_prfIdealGame_ctrToPrfDistinguisher (adversary : OracleDistinguisher)
    (bit : Bool) {n ℓ : ℕ}
    (hℓ : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ ℓ) :
    ProbComp.eval (prfIdealGame (ctrToPrfDistinguisher adversary bit) n) =
      ProbComp.eval (PRF.idealExperiment
        (ctrReduction ctrModCounter ℓ bit (blockModeWordAdversary adversary n))) :=
  eval_prfIdealGame_ivStreamToPrfDistinguisher
    (keystreamBlocks := fun f iv blocks => ctrMaskBlocks f ctrModCounter iv blocks)
    (fun f iv blocks => length_ctrMaskBlocks f ctrModCounter iv blocks)
    (fun f iv blocks => run_ctrMaskQueriesFrom_zero f ctrModCounter iv blocks)
    run_ctrKeystreamQueries_randomFunction adversary bit hℓ

/-- **Concrete CPA bound for counter mode**, after [BonehShoup2023], Theorem 5.3, (5.14). At
parameter `n`, an adversary making at most `Q` requests of at most `L ≤ 2 ^ n` bits has CPA
advantage against `ctrWordEncrypt family` at most the PRF advantages of
`ctrToPrfDistinguisher adversary false` and `ctrToPrfDistinguisher adversary true` plus
`2 (Q L) ^ 2 / 2 ^ n`. Requests of `L` bits ask for at most `L` blocks, so `Q L` bounds the blocks
encrypted in total. This is not the bound (5.14), which has one distinguisher with a factor `2`
and the collision term `2 Q ^ 2 ℓ / N` for `ℓ` blocks per request; see the module's deviations. -/
theorem advantage_ctrWordCPAGame_le {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) {n Q L : ℕ} (hQ : (adversary n []).IsQueryBounded Q)
    (hL : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ L)
    (hLn : L ≤ 2 ^ n) :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ctrWordEncrypt family) adversary false n))
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ctrWordEncrypt family) adversary true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ctrToPrfDistinguisher adversary false) n))
        (ProbComp.eval (prfIdealGame (ctrToPrfDistinguisher adversary false) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ctrToPrfDistinguisher adversary true) n))
        (ProbComp.eval (prfIdealGame (ctrToPrfDistinguisher adversary true) n)) : ℝ) +
      2 * ((Q : ℝ) * L) ^ 2 / 2 ^ n := by
  rw [← eval_prfRealGame_ctrToPrfDistinguisher hlen adversary false n,
    ← eval_prfRealGame_ctrToPrfDistinguisher hlen adversary true n]
  have hcost := isCostBounded_blockModeWordAdversary hQ L
  have hintra : ∀ iv i j, i < L → j < L → i ≠ j → ctrModCounter iv i ≠ ctrModCounter iv j :=
    fun iv _ _ hi hj hij => ctrModCounter_injOn hLn iv hi hj hij
  have hiv : ∀ i < L, Function.Injective (fun iv : BitString n => ctrModCounter iv i) :=
    fun i _ => ctrModCounter_injective_left i
  have h₀ := advantage_idealExperiment_ctrReduction_le ctrModCounter L false hcost hintra hiv
  have h₁ := advantage_idealExperiment_ctrReduction_le ctrModCounter L true hcost hintra hiv
  rw [← eval_prfIdealGame_ctrToPrfDistinguisher adversary false hL] at h₀
  rw [← eval_prfIdealGame_ctrToPrfDistinguisher adversary true hL] at h₁
  refine (advantage_le_four _
    (ProbComp.eval (prfIdealGame (ctrToPrfDistinguisher adversary false) n))
    (ProbComp.eval (blockModeIdealExperiment L (blockModeWordAdversary adversary n)))
    (ProbComp.eval (prfIdealGame (ctrToPrfDistinguisher adversary true) n)) _).trans ?_
  rw [Nat.cast_mul] at h₀ h₁
  have hsplit : 2 * ((Q : ℝ) * L) ^ 2 / 2 ^ n =
      ((Q : ℝ) * L) ^ 2 / 2 ^ n + ((Q : ℝ) * L) ^ 2 / 2 ^ n := by ring
  rw [hsplit]
  linarith

/-- **Counter mode is CPA-secure for a pseudorandom function** ([BonehShoup2023], Section 5.4.2,
Theorem 5.3): if `family` is a `PseudorandomFunction`, randomized counter mode with `n`-bit
blocks at security parameter `n` has negligible many-query left-or-right CPA advantage on
equal-length pairs of whole blocks, against every uniform strict oracle-PPT adversary. The
source fixes a poly-bounded cap `ℓ` on the number of blocks; here there is no cap, which implies
the statement for every `ℓ`. -/
theorem PseudorandomFunction.indcpa_ctrWordEncrypt {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    SymmetricINDCPAOn blockPairValid BitString.sampleList (ctrWordEncrypt family) := by
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let P : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hq (n : ℕ) : (adversary n []).IsQueryBounded (P n) := by
    simpa only [P, List.length_nil, Nat.add_zero] using (hbounds n []).1
  have hl (n : ℕ) : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ P n := by
    simpa only [P, List.length_nil, Nat.add_zero] using (hbounds n []).2
  have hP : PolynomiallyBounded P :=
    (PolynomiallyBounded.const c).mul ((PolynomiallyBounded.id.add (.const 2)).pow d)
  have hprf₀ := hprf.secure (ctrToPrfDistinguisher adversary false)
    (isOraclePPT_ctrToPrfDistinguisher hadversary false)
  have hprf₁ := hprf.secure (ctrToPrfDistinguisher adversary true)
    (isOraclePPT_ctrToPrfDistinguisher hadversary true)
  negligible eventually (hP.eventually_lt_two_pow.mono fun n hn =>
    advantage_ctrWordCPAGame_le hprf.length_eq adversary (hq n) (hl n) hn.le)

end Cslib.Crypto
