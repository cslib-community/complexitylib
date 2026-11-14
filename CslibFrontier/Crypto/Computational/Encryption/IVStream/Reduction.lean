/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.BlockModeWord
public import CslibFrontier.Crypto.Computational.Encryption.IVStream
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# The PRF reduction for stream encryption under a random initial value

Randomized counter mode and output feedback mode are both the envelope `ivStreamEncrypt` of
`IVStream.lean`, with different keystreams. The reduction of the proof of [BonehShoup2023],
Theorem 5.3, written there for counter mode, proves both CPA-secure for a pseudorandom function:
the PRF distinguisher runs the CPA adversary and answers each admissible left-or-right request
itself, drawing the initial value and obtaining each keystream block with one query to its own
function oracle. The modes differ only in the program `keystreamQueries n iv blocks` that obtains
the keystream of `blocks` blocks from initial value `iv`. `ivStreamPrfHandler keystreamQueries` and
`ivStreamToPrfDistinguisher keystreamQueries` are the reduction for any such program.

1. The distinguisher is uniform strict oracle PPT whenever the adversary is and
   `keystreamQueries` is strict oracle PPT on `(1ⁿ, iv, 1^blocks)`
   (`isOraclePPT_ivStreamToPrfDistinguisher`).
2. Against the keyed oracle, if the keystream queries compute the keystream
   `keystream n k iv blocks` from every `n`-bit initial value, its output law is that of the
   adversary in the CPA game of `ivStreamEncrypt keystream`
   (`eval_prfRealGame_ivStreamToPrfDistinguisher`).
3. Against a uniform random function, if the keystream queries compute the bits of the blocks that
   a typed keystream program computes, it is the typed reduction `blockModeReduction` run on the
   adversary read as a block-mode adversary (`blockModeWordAdversary`)
   (`eval_prfIdealGame_ivStreamToPrfDistinguisher`). The typed collision bounds of each mode then
   apply.

## Main definitions

* `Cslib.Crypto.ivStreamPrfHandler`: the reduction's answer to one request.
* `Cslib.Crypto.ivStreamToPrfDistinguisher`: the PRF distinguisher built from a CPA adversary.

## Main results

* `Cslib.Crypto.isOraclePPT_ivStreamToPrfDistinguisher`: the reduction is uniform strict oracle
  PPT.
* `Cslib.Crypto.eval_prfRealGame_ivStreamToPrfDistinguisher`: the real PRF game of the reduction
  is the CPA game.
* `Cslib.Crypto.eval_prfIdealGame_ivStreamToPrfDistinguisher`: the ideal PRF game of the reduction
  is the typed block-mode reduction against a random function.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Theorem 5.3 (printed p. 191).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- The reduction's answer to one left-or-right request, for a program
`keystreamQueries n iv blocks` that obtains the keystream of `blocks` blocks from initial value
`iv` with queries to the function oracle ([BonehShoup2023], proof of Theorem 5.3): on an
admissible pair, draw a uniform `n`-bit initial value, obtain the keystream and XOR it with the
message selected by `bit`; answer inadmissible requests with `[]` and no query. -/
noncomputable def ivStreamPrfHandler
    (keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)) (n : ℕ)
    (bit : Bool) (request : Unit × List Bool) : WordOracleComp Unit (List Bool) :=
  let m0 := unframe request.2
  let m1 := dropFrame request.2
  if blockPairValid n m0 m1 then do
    let iv ← ProbOracleComp.sample (BitString.sampleList n)
    (fun ks => iv ++ List.zipWith xor ks (if bit then m1 else m0)) <$>
      keystreamQueries n iv (m0.length / n)
  else
    pure []

/-- The PRF distinguisher built from a left-or-right CPA adversary against stream encryption with
keystream queries `keystreamQueries` ([BonehShoup2023], proof of Theorem 5.3): run the adversary
and answer every request with `ivStreamPrfHandler keystreamQueries n bit`. -/
noncomputable def ivStreamToPrfDistinguisher
    (keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool))
    (adversary : OracleDistinguisher) (bit : Bool) : OracleDistinguisher :=
  fun n _ => ProbOracleComp.simulate (ivStreamPrfHandler keystreamQueries n bit) (adversary n [])

/-! ### Efficiency -/

/-- The handler is uniformly strict oracle PPT in the parameter, the auxiliary word and the
request. -/
private theorem isOraclePPTOn_ivStreamPrfHandler
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)}
    (hks : IsOraclePPTOn (encPair encUnary (encPair encBits encUnary)) encBits
      (fun ((n, iv, blocks) : ℕ × List Bool × ℕ) => keystreamQueries n iv blocks))
    (bit : Bool) :
    IsOraclePPTOn (encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)) encBits
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) =>
        ivStreamPrfHandler keystreamQueries pair.1.1 bit pair.2) := by
  let E := encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)
  let EIv := encPair E encBits
  have hn : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Unit × List Bool) => p.1.1)
      E encUnary := by dsimp only [E]; fun_prop
  have hm0 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) => unframe p.2.2) E encBits :=
    ComputableInPolyTime.unframe.comp (by dsimp only [E]; fun_prop)
  have hm1 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) => dropFrame p.2.2) E encBits :=
    ComputableInPolyTime.dropFrame.comp (by dsimp only [E]; fun_prop)
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) =>
        blockPairValid p.1.1 (unframe p.2.2) (dropFrame p.2.2)) E encBool := by
    unfold blockPairValid; fun_prop
  have hmsg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) =>
        if bit then dropFrame p.2.2 else unframe p.2.2) E encBits := by
    cases bit
    · exact hm0
    · exact hm1
  have hblocks : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × (Unit × List Bool)) × List Bool =>
        (unframe q.1.2.2).length / q.1.1.1) EIv encUnary :=
    ComputableInPolyTime.unary_div'
      (ComputableInPolyTime.length_bits_comp (hm0.comp (ComputableInPolyTime.fst _ _)))
      (hn.comp (ComputableInPolyTime.fst _ _))
  have hksIv : IsOraclePPTOn (Operation := Unit) EIv encBits
      (fun q : ((ℕ × List Bool) × (Unit × List Bool)) × List Bool =>
        keystreamQueries q.1.1.1 q.2 ((unframe q.1.2.2).length / q.1.1.1)) :=
    hks.preprocess' ((hn.comp (ComputableInPolyTime.fst _ _)).prod
      ((ComputableInPolyTime.snd _ _).prod hblocks))
  have hyes : IsOraclePPTOn (Operation := Unit) EIv encBits
      (fun q : ((ℕ × List Bool) × (Unit × List Bool)) × List Bool =>
        (fun ks => q.2 ++ List.zipWith xor ks (if bit then dropFrame q.1.2.2 else unframe q.1.2.2))
          <$> keystreamQueries q.1.1.1 q.2 ((unframe q.1.2.2).length / q.1.1.1)) :=
    hksIv.map_with' (ComputableInPolyTime.bitsAppend (by dsimp only [EIv]; fun_prop)
      (ComputableInPolyTime.bitsZipWithInput xor (ComputableInPolyTime.snd _ _)
        (hmsg.comp ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))))
  unfold ivStreamPrfHandler
  exact IsOraclePPTOn.cond' hcond
    (IsOraclePPTOn.bind_with
      ((isPPTOn_sampleList.preprocess hn).isOraclePPTOn) hyes)
    (ComputableInPolyTime.isOraclePPTOn (ComputableInPolyTime.const []))

/-- Every answer of the handler has at most `n` bits more than the request. -/
private theorem length_le_of_mem_support_ivStreamPrfHandler
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)} {n : ℕ}
    {bit : Bool} {request : Unit × List Bool} {reply : List Bool}
    (hreply : reply ∈ OracleComp.support (ivStreamPrfHandler keystreamQueries n bit request)) :
    reply.length ≤ n + request.2.length := by
  unfold ivStreamPrfHandler at hreply
  dsimp only at hreply
  split at hreply
  · obtain ⟨iv, hiv, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hreply
    change iv ∈ OracleComp.support (ProbOracleComp.sample (BitString.sampleList n)) at hiv
    rw [ProbOracleComp.support_sample, BitString.eval_sampleList] at hiv
    have hivLen : iv.length = n := BitString.length_of_mem_support_uniformList hiv
    obtain ⟨ks, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
    have hmsg : (if bit then dropFrame request.2 else unframe request.2).length ≤
        request.2.length := by
      cases bit
      · exact length_unframe_le _
      · exact length_dropFrame_le _
    simp only [List.length_append, List.length_zipWith, hivLen]
    omega
  · have hreplyEq := OracleComp.eq_of_mem_supportWith_pure hreply
    subst hreplyEq
    simp

/-- **Efficiency of the reduction.** If the keystream queries are strict oracle PPT on
`(1ⁿ, iv, 1^blocks)`, then for every uniform strict oracle-PPT adversary,
`ivStreamToPrfDistinguisher keystreamQueries adversary bit` is uniform strict oracle PPT. -/
theorem isOraclePPT_ivStreamToPrfDistinguisher
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)}
    (hks : IsOraclePPTOn (encPair encUnary (encPair encBits encUnary)) encBits
      (fun ((n, iv, blocks) : ℕ × List Bool × ℕ) => keystreamQueries n iv blocks))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool (ivStreamToPrfDistinguisher keystreamQueries adversary bit) :=
  (IsOraclePPTOn.interpret_preprocess_open' (operationEncoding := encFinEnum Unit)
    (handler := fun caller : ℕ × List Bool => ivStreamPrfHandler keystreamQueries caller.1 bit)
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (resources := fun caller request => caller.1 + request.length)
    hadversary (by fun_prop) (isOraclePPTOn_ivStreamPrfHandler hks bit) (by fun_prop)
    fun _ _ _ hreply => length_le_of_mem_support_ivStreamPrfHandler hreply).isOraclePPT

/-! ### The real game -/

/-- Under a key `k`, if the keystream queries answered by the keyed oracle compute
`keystream n k iv blocks` from every `n`-bit initial value `iv`, the handler answers each request
with the law of the CPA oracle of `ivStreamEncrypt keystream`. -/
theorem eval_run_ivStreamPrfHandler
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)}
    {keystream : ℕ → List Bool → List Bool → ℕ → List Bool}
    {family : List Bool → List Bool → List Bool} {n : ℕ} {k : List Bool}
    (hks : ∀ iv : List Bool, iv.length = n → ∀ blocks,
      (keystreamQueries n iv blocks).run (fun request => pure (prfOracle family n k request.2)) =
        pure (keystream n k iv blocks))
    (bit : Bool) (request : Unit × List Bool) :
    ProbComp.eval ((ivStreamPrfHandler keystreamQueries n bit request).run
        fun request => pure (prfOracle family n k request.2)) =
      ProbComp.eval
        (symmetricCPAReplyOn blockPairValid (ivStreamEncrypt keystream) n k bit request) := by
  unfold ivStreamPrfHandler symmetricCPAReplyOn
  dsimp only
  by_cases hvalid : blockPairValid n (unframe request.2) (dropFrame request.2) = true
  · have hlenEq : (unframe request.2).length = (dropFrame request.2).length := by
      simpa [blockPairValid] using (Bool.and_eq_true _ _).mp hvalid |>.1
    have hmb : (if bit then dropFrame request.2 else unframe request.2).length =
        (unframe request.2).length := by
      cases bit <;> simp [hlenEq]
    simp only [hvalid, ↓reduceIte, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
      ProbOracleComp.run_map, ivStreamEncrypt, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, BitString.eval_sampleList, hmb]
    refine PMF.bind_congr_on_support _ _ _ fun iv hiv => ?_
    rw [hks iv (BitString.length_of_mem_support_uniformList hiv), ProbComp.eval_pure, PMF.pure_map]
  · simp [hvalid]

/-- **Real game.** If, under every key of length `n`, the keystream queries answered by the keyed
oracle compute `keystream n k iv blocks` from every `n`-bit initial value `iv`, then against the
keyed oracle `ivStreamToPrfDistinguisher keystreamQueries adversary bit` has the output law of
`adversary` in the CPA game of `ivStreamEncrypt keystream` with challenge bit `bit`. -/
theorem eval_prfRealGame_ivStreamToPrfDistinguisher
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)}
    {keystream : ℕ → List Bool → List Bool → ℕ → List Bool}
    {family : List Bool → List Bool → List Bool} {n : ℕ}
    (hks : ∀ k : List Bool, k.length = n → ∀ iv : List Bool, iv.length = n → ∀ blocks,
      (keystreamQueries n iv blocks).run (fun request => pure (prfOracle family n k request.2)) =
        pure (keystream n k iv blocks))
    (adversary : OracleDistinguisher) (bit : Bool) :
    ProbComp.eval (prfRealGame family (ivStreamToPrfDistinguisher keystreamQueries adversary bit)
        n) =
      ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ivStreamEncrypt keystream) adversary bit n) := by
  simp only [prfRealGame, symmetricCPAGameOn, ivStreamToPrfDistinguisher,
    ProbOracleComp.run_simulate, ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
  exact (ProbOracleComp.QueriesSatisfy.of_forall (p := fun _ => True) (fun _ => trivial)
    (adversary n [])).eval_run_congr fun request _ =>
      eval_run_ivStreamPrfHandler (hks k hkLen) bit request

/-! ### The ideal game -/

/-- Against a fixed function `f`, suppose the typed keystream program `typedQueries iv blocks`
computes the `blocks` blocks `keystreamBlocks iv blocks` with `f`, and the keystream queries from
the bits of `iv` compute the bits of those blocks. Then the handler answers a request of at most
`ℓ` bits as the typed block-mode query program answers its block query. -/
private theorem eval_run_ivStreamPrfHandler_randomFunction
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)} {n : ℕ}
    {typedQueries : BitString n → ℕ →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n))}
    {f : BitString n → BitString n} {keystreamBlocks : BitString n → ℕ → List (BitString n)}
    (hlen : ∀ iv blocks, (keystreamBlocks iv blocks).length = blocks)
    (htyped : ∀ iv blocks,
      (typedQueries iv blocks).run (fun x => pure (f x)) = pure (keystreamBlocks iv blocks))
    (hword : ∀ iv blocks, (keystreamQueries n (List.ofFn iv) blocks).run
        (fun request => pure (randomFunctionOracle n f request.2)) =
          pure ((keystreamBlocks iv blocks).flatMap List.ofFn))
    (ℓ : ℕ) (bit : Bool) (request : Unit × List Bool) (hℓ : request.2.length ≤ ℓ) :
    ProbComp.eval ((ivStreamPrfHandler keystreamQueries n bit request).run
        fun r => pure (randomFunctionOracle n f r.2)) =
      ProbComp.eval ((blockModeWordQuery n request).run
        fun q => (blockModeQueryProgram typedQueries ℓ bit q).run fun x => pure (f x)) := by
  unfold ivStreamPrfHandler blockModeWordQuery
  dsimp only
  by_cases hvalid : blockPairValid n (unframe request.2) (dropFrame request.2) = true
  · have hpair := hvalid
    simp only [blockPairValid, Bool.and_eq_true, beq_iff_eq] at hpair
    obtain ⟨hlenEq, hmod⟩ := hpair
    have hm0 : (unframe request.2).length / n ≤ ℓ :=
      (Nat.div_le_self _ _).trans ((length_unframe_le _).trans hℓ)
    have hsel := blockModeSelect_padBlocks bit hvalid hm0
    have hmb : (if bit then dropFrame request.2 else unframe request.2).length =
        (unframe request.2).length := by
      cases bit <;> simp [hlenEq]
    have hmbMod : (if bit then dropFrame request.2 else unframe request.2).length % n = 0 := by
      rw [hmb, hmod]
    simp only [hvalid, ↓reduceIte, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
      ProbOracleComp.run_map, ProbOracleComp.run_query, blockModeQueryProgram, hsel, htyped,
      ProbOracleComp.run_pure, pure_bind, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, ProbComp.eval_uniform, BitString.eval_sampleList, BitString.uniformList,
      PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.pure_map, hword]
    refine congrArg _ (funext fun iv => congrArg PMF.pure ?_)
    rw [BitString.flatMap_ofFn_zipWith_add _ _ (by
        rw [hlen, BitString.length_padBlocks, hmb]),
      BitString.flatMap_ofFn_padBlocks (Nat.dvd_of_mod_eq_zero hmbMod), BitString.length_padBlocks,
      hmb]
  · simp [hvalid]

/-- **Ideal game.** Suppose that against every function `f`, the typed keystream program
`typedQueries iv blocks` computes the `blocks` blocks `keystreamBlocks f iv blocks`, and the
keystream queries from the bits of `iv`, answered by the random-function oracle of `f`, compute
the bits of those blocks. Then against a uniform random function, the reduction for an adversary
whose requests have at most `ℓ` bits is the typed reduction `blockModeReduction typedQueries ℓ bit`
for the block-mode adversary. -/
theorem eval_prfIdealGame_ivStreamToPrfDistinguisher
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)} {n : ℕ}
    {typedQueries : BitString n → ℕ →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n))}
    {keystreamBlocks : (BitString n → BitString n) → BitString n → ℕ → List (BitString n)}
    (hlen : ∀ f iv blocks, (keystreamBlocks f iv blocks).length = blocks)
    (htyped : ∀ f iv blocks,
      (typedQueries iv blocks).run (fun x => pure (f x)) = pure (keystreamBlocks f iv blocks))
    (hword : ∀ f iv blocks, (keystreamQueries n (List.ofFn iv) blocks).run
        (fun request => pure (randomFunctionOracle n f request.2)) =
          pure ((keystreamBlocks f iv blocks).flatMap List.ofFn))
    (adversary : OracleDistinguisher) (bit : Bool) {ℓ : ℕ}
    (hℓ : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ ℓ) :
    ProbComp.eval (prfIdealGame (ivStreamToPrfDistinguisher keystreamQueries adversary bit) n) =
      ProbComp.eval (PRF.idealExperiment
        (blockModeReduction typedQueries ℓ bit (blockModeWordAdversary adversary n))) := by
  simp only [prfIdealGame, PRF.idealExperiment, ivStreamToPrfDistinguisher, blockModeReduction,
    blockModeWordAdversary, ProbOracleComp.run_simulate, ProbComp.eval_bind]
  exact congrArg _ (funext fun f =>
    hℓ.eval_run_congr fun request hrequest =>
      eval_run_ivStreamPrfHandler_randomFunction (hlen f) (htyped f) (hword f) ℓ bit request
        hrequest)

end Cslib.Crypto
