/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.IVStream
public import CslibFrontier.Crypto.Computational.Encryption.SymmetricCPA
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Crypto.Computational.Encryption.BlockModeWord
import CslibFrontier.Crypto.Computational.Encryption.OFBMode
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Output feedback mode from a uniform pseudorandom function

Output feedback (OFB) mode ([BonehShoup2023], Exercise 5.15(b), printed p. 212) encrypts a message
of `v` blocks `m[1], …, m[v]` under a key `k` by drawing a uniform initial value `x₀` and sending
`(x₀, c[1], …, c[v])` with `xᵢ = F(k, xᵢ₋₁)` and `c[i] = m[i] ⊕ xᵢ`. Here the security parameter
`n` is the block length: the PRF `family` takes `n`-bit keys and `n`-bit inputs to `n`-bit
outputs. A message is any word made of whole blocks. `ofbWordEncrypt` outputs the word
`x₀ ++ c`, and `ofbWordDecrypt` inverts it; both are the shared envelope `ivStreamEncrypt`,
`ivStreamDecrypt` with the chain keystream `ofbWordKeystream`. Each chain value is truncated to
`n` bits (`ofbWordStep`). For keys of length `n` this changes nothing; for other keys it keeps
the chain, and so encryption, polynomial-time.

Security is many-query left-or-right CPA security (`SymmetricINDCPAOn`, Attack Game 5.2) on
equal-length pairs of whole blocks (`blockPairValid`), in the standard model, against uniform
strict oracle-PPT adversaries. The PRF distinguisher `ofbToPrfDistinguisher adversary bit` runs the
adversary and answers each admissible request itself: it draws the initial value and obtains each
chain value with one query to its own function oracle on the previous one, keeping at most `n`
bits of the reply.

1. It is uniform strict oracle PPT whenever the adversary is
   (`isOraclePPT_ofbToPrfDistinguisher`).
2. Against the keyed oracle, its output law is that of the adversary in the CPA game with
   challenge bit `bit` (`eval_prfRealGame_ofbToPrfDistinguisher`).
3. Against a uniform random function, it is the typed reduction `ofbReduction` of `OFBMode.lean`
   run on the adversary read as a block-mode adversary (`blockModeWordAdversary`), and the typed
   chain-collision bound `advantage_idealExperiment_ofbReduction_le` applies. This gives the
   concrete bound `advantage_ofbWordCPAGame_le` and then
   `PseudorandomFunction.indcpa_ofbWordEncrypt`.

## Deviations from Exercise 5.15(b)

* **Any number of blocks.** The exercise fixes a poly-bounded `ℓ` and the message space `X^ℓ`.
  Here every whole-block length is admitted, which implies the statement for every `ℓ`.
* **Two fixed-bit distinguishers.** As for `prfCipher`, the bound uses the PRF advantages of
  `ofbToPrfDistinguisher adversary false` and `ofbToPrfDistinguisher adversary true`. Its collision
  term is `2 (Q L) (Q L + L) / 2 ^ n` for `Q` requests of at most `L` bits, from the typed bound
  `K (K + ℓ) / 2 ^ n` with `K = Q L` blocks in total and at most `ℓ = L` per request.

## Main definitions

* `Cslib.Crypto.ofbWordStep`, `Cslib.Crypto.ofbWordKeystream`: chain steps and keystream.
* `Cslib.Crypto.ofbWordEncrypt`, `Cslib.Crypto.ofbWordDecrypt`: the cipher on whole-block words.
* `Cslib.Crypto.ofbKeystreamStep`, `Cslib.Crypto.ofbKeystreamQueries`,
  `Cslib.Crypto.ofbPrfHandler`, `Cslib.Crypto.ofbToPrfDistinguisher`: the reduction to the PRF
  game.

## Main results

* `Cslib.Crypto.ofbWordDecrypt_ofbWordEncrypt`: decryption inverts encryption.
* `Cslib.Crypto.isPPTOn_ofbWordEncrypt`, `Cslib.Crypto.computableInPolyTime_ofbWordDecrypt`:
  efficiency of the honest algorithms.
* `Cslib.Crypto.isOraclePPT_ofbToPrfDistinguisher`: the reduction is uniform strict oracle PPT.
* `Cslib.Crypto.eval_prfRealGame_ofbToPrfDistinguisher`: the real PRF game of the reduction is
  the CPA game.
* `Cslib.Crypto.advantage_ofbWordCPAGame_le`: the concrete CPA bound.
* `Cslib.Crypto.PseudorandomFunction.indcpa_ofbWordEncrypt`: OFB mode is CPA-secure for every
  `PseudorandomFunction`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.3 (Attack Game 5.2, printed pp. 181–182) and Exercise 5.15 (printed p. 212).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-! ### The cipher -/

/-- One OFB chain step under `family k`: the next chain value is the image of the current one,
truncated to `n` bits, and it is appended to the keystream so far. -/
@[expose]
def ofbWordStep (family : List Bool → List Bool → List Bool) (n : ℕ) (k : List Bool)
    (state : List Bool × List Bool) : List Bool × List Bool :=
  ((family k state.1).take n, state.2 ++ (family k state.1).take n)

/-- The keystream of `blocks` blocks under `family k` from initial value `iv`: the chain values
`x₁, …, x_blocks` after `x₀ = iv`, concatenated. -/
@[expose]
def ofbWordKeystream (family : List Bool → List Bool → List Bool) (n : ℕ) (k iv : List Bool)
    (blocks : ℕ) : List Bool :=
  ((ofbWordStep family n k)^[blocks] (iv, [])).2

/-- OFB encryption ([BonehShoup2023], Exercise 5.15(b)): draw a uniform `n`-bit initial value
`iv` and output `iv` followed by the message XORed with the keystream of `msg.length / n`
blocks. -/
noncomputable def ofbWordEncrypt (family : List Bool → List Bool → List Bool) :
    ℕ → List Bool → List Bool → ProbComp (List Bool) :=
  ivStreamEncrypt (ofbWordKeystream family)

/-- OFB decryption: accept an `n`-bit initial value followed by whole blocks, and XOR the blocks
with the keystream from that initial value. -/
def ofbWordDecrypt (family : List Bool → List Bool → List Bool) :
    ℕ → List Bool → List Bool → Option (List Bool) :=
  ivStreamDecrypt (ofbWordKeystream family)

/-- Under a key of length `n`, a family with `n`-bit outputs on `n`-bit inputs produces a
keystream of `blocks * n` bits from an `n`-bit initial value. -/
theorem length_ofbWordKeystream {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) {iv : List Bool} (hiv : iv.length = n)
    (blocks : ℕ) :
    (ofbWordKeystream family n k iv blocks).length = blocks * n := by
  have hstep (state : List Bool × List Bool) (hstate : state.1.length = n) :
      (ofbWordStep family n k state).1.length = n ∧
        (ofbWordStep family n k state).2.length = state.2.length + n := by
    have hy : (family k state.1).length = n := by rw [hlen k _ (by rw [hstate, hk]), hk]
    simp [ofbWordStep, hy]
  have hloop : ∀ (b : ℕ) (state : List Bool × List Bool), state.1.length = n →
      ((ofbWordStep family n k)^[b] state).2.length = state.2.length + b * n := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      intro state hstate
      rw [Function.iterate_succ_apply, ih _ (hstep state hstate).1, (hstep state hstate).2]
      ring
  simpa [ofbWordKeystream] using hloop blocks (iv, []) hiv

/-- Decryption inverts encryption on whole-block messages under keys of length `n`. -/
theorem ofbWordDecrypt_ofbWordEncrypt {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) {msg : List Bool} (hmsg : msg.length % n = 0)
    {ct : List Bool} (hct : ct ∈ (ProbComp.eval (ofbWordEncrypt family n k msg)).support) :
    ofbWordDecrypt family n k ct = some msg :=
  ivStreamDecrypt_ivStreamEncrypt (fun _ hiv => length_ofbWordKeystream hlen hk hiv _) hmsg hct

/-! ### Efficiency of the honest algorithms -/

/-- The keystream is computable in polynomial time from the family's evaluator: every chain value
has at most `n` bits, so each step grows the encoded state by at most `3 n` bits. -/
theorem computableInPolyTime_ofbWordKeystream {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    {α : Type} {input : α ↪ List Bool} {n blocks : α → ℕ} {k iv : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encBits)
    (hiv : ComputableInPolyTime iv input encBits)
    (hblocks : ComputableInPolyTime blocks input encUnary) :
    ComputableInPolyTime (fun a => ofbWordKeystream family (n a) (k a) (iv a) (blocks a))
      input encBits := by
  let EStep := encPair input (encPair encBits encBits)
  have hy : ComputableInPolyTime
      (fun p : α × (List Bool × List Bool) => (family (k p.1) p.2.1).take (n p.1)) EStep encBits :=
    ComputableInPolyTime.bitsTakeWithInput
      (hpoly.comp ((hk.comp (ComputableInPolyTime.fst _ _)).prod
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))))
      (hn.comp (ComputableInPolyTime.fst _ _))
  have hstep : ComputableInPolyTime
      (fun p : α × (List Bool × List Bool) => ofbWordStep family (n p.1) (k p.1) p.2)
      EStep (encPair encBits encBits) :=
    hy.prod (ComputableInPolyTime.bitsAppend
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)) hy)
  have hnBound : PolyBounded (fun a => (input a).length) n := by
    simpa only [encUnary_apply, List.length_replicate] using hn.polyBounded_length
  have hloop := ComputableInPolyTime.iterateWithInput_of_bounded_growth
    (encState := encPair encBits encBits) (count := blocks)
    (init := fun a => (iv a, ([] : List Bool)))
    (step := fun a state => ofbWordStep family (n a) (k a) state)
    hblocks (hiv.prod (ComputableInPolyTime.const [])) hstep
    (growth := fun a => n a * 3)
    ⟨hnBound.mul (PolyBounded.const 3), fun a state => by
      have htake := List.length_take_le (n a) (family (k a) state.1)
      simp only [ofbWordStep, length_encPair, encBits_apply, List.length_append]
      omega⟩
  exact (ComputableInPolyTime.snd _ _).comp hloop

/-- The keystream as a function of `(n, k, iv, blocks)` is computable in polynomial time. -/
private theorem computableInPolyTime_ofbWordKeystream_tuple
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime
      (fun ((n, k, iv, blocks) : ℕ × List Bool × List Bool × ℕ) =>
        ofbWordKeystream family n k iv blocks)
      (encPair encUnary (encPair encBits (encPair encBits encUnary))) encBits :=
  computableInPolyTime_ofbWordKeystream hpoly (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop)

/-- OFB encryption is uniformly strict PPT in `(n, k, msg)`. -/
theorem isPPTOn_ofbWordEncrypt {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun ((n, k, msg) : ℕ × List Bool × List Bool) => ofbWordEncrypt family n k msg) :=
  isPPTOn_ivStreamEncrypt (computableInPolyTime_ofbWordKeystream_tuple hpoly)

/-- OFB decryption is computable in polynomial time on `(n, k, ct)`. -/
theorem computableInPolyTime_ofbWordDecrypt {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime
      (fun ((n, k, ct) : ℕ × List Bool × List Bool) => ofbWordDecrypt family n k ct)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits) :=
  computableInPolyTime_ivStreamDecrypt (computableInPolyTime_ofbWordKeystream_tuple hpoly)

/-! ### The reduction to the PRF game -/

/-- One chain value from the function oracle: query the current chain value, keep at most `n`
bits of the reply as the next one and append it to the keystream so far. -/
def ofbKeystreamStep (n : ℕ) (state : List Bool × List Bool) :
    WordOracleComp Unit (List Bool × List Bool) :=
  (fun y => (y, state.2 ++ y)) <$> (List.take n <$> ProbOracleComp.query ((), state.1))

/-- The keystream of `blocks` blocks from the function oracle, with one query per block. -/
def ofbKeystreamQueries (n : ℕ) (iv : List Bool) (blocks : ℕ) :
    WordOracleComp Unit (List Bool) :=
  Prod.snd <$> OracleComp.iterate blocks (ofbKeystreamStep n) (iv, [])

/-- The reduction's answer to one left-or-right request: on an admissible pair, draw a uniform
`n`-bit initial value, obtain the keystream from the function oracle and XOR it with the message
selected by `bit`; answer inadmissible requests with `[]` and no query. -/
noncomputable def ofbPrfHandler (n : ℕ) (bit : Bool) (request : Unit × List Bool) :
    WordOracleComp Unit (List Bool) :=
  let m0 := unframe request.2
  let m1 := dropFrame request.2
  if blockPairValid n m0 m1 then do
    let iv ← ProbOracleComp.sample (BitString.sampleList n)
    (fun ks => iv ++ List.zipWith xor ks (if bit then m1 else m0)) <$>
      ofbKeystreamQueries n iv (m0.length / n)
  else
    pure []

/-- The PRF distinguisher built from a left-or-right CPA adversary against OFB mode: run the
adversary and answer every request with `ofbPrfHandler n bit`. -/
noncomputable def ofbToPrfDistinguisher (adversary : OracleDistinguisher) (bit : Bool) :
    OracleDistinguisher :=
  fun n _ => ProbOracleComp.simulate (ofbPrfHandler n bit) (adversary n [])

/-- Answered by a deterministic oracle `g`, the keystream queries iterate the chain step that
replaces the chain value by `g` of it, truncated to `n` bits. -/
theorem run_ofbKeystreamQueries {n : ℕ} (g : List Bool → List Bool) (iv : List Bool)
    (blocks : ℕ) :
    (ofbKeystreamQueries n iv blocks).run (fun request => pure (g request.2)) =
      pure (((fun state : List Bool × List Bool =>
        ((g state.1).take n, state.2 ++ (g state.1).take n))^[blocks] (iv, [])).2) := by
  have hloop (b : ℕ) (state : List Bool × List Bool) :
      ProbOracleComp.run (OracleComp.iterate b (ofbKeystreamStep n) state)
        (fun request => pure (g request.2)) =
      pure ((fun state : List Bool × List Bool =>
        ((g state.1).take n, state.2 ++ (g state.1).take n))^[b] state) := by
    induction b with
    | zero => rfl
    | succ b ih =>
      rw [OracleComp.iterate_succ, ProbOracleComp.run_bind, ih, pure_bind, ofbKeystreamStep,
        Function.iterate_succ_apply']
      simp
  rw [ofbKeystreamQueries, ProbOracleComp.run_map, hloop, map_pure]

/-- Under a key of length `n`, the reduction answers each request with the law of the CPA
oracle. -/
theorem eval_run_ofbPrfHandler {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) (bit : Bool) (request : Unit × List Bool) :
    ProbComp.eval ((ofbPrfHandler n bit request).run
        fun request => pure (prfOracle family n k request.2)) =
      ProbComp.eval
        (symmetricCPAReplyOn blockPairValid (ofbWordEncrypt family) n k bit request) := by
  have hchain : ∀ (b : ℕ) (state : List Bool × List Bool), state.1.length = n →
      (fun state : List Bool × List Bool =>
        ((prfOracle family n k state.1).take n,
          state.2 ++ (prfOracle family n k state.1).take n))^[b] state =
        (ofbWordStep family n k)^[b] state := by
    intro b
    induction b with
    | zero => intro _ _; rfl
    | succ b ih =>
      intro state hstate
      have hy : (family k state.1).length = n := by rw [hlen k _ (by rw [hstate, hk]), hk]
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [prfOracle, hstate, ↓reduceIte]
      exact ih _ (by simp [hy])
  unfold ofbPrfHandler symmetricCPAReplyOn
  dsimp only
  by_cases hvalid : blockPairValid n (unframe request.2) (dropFrame request.2) = true
  · have hlenEq : (unframe request.2).length = (dropFrame request.2).length := by
      simpa [blockPairValid] using (Bool.and_eq_true _ _).mp hvalid |>.1
    have hmb : (if bit then dropFrame request.2 else unframe request.2).length =
        (unframe request.2).length := by
      cases bit <;> simp [hlenEq]
    simp only [hvalid, ↓reduceIte, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
      ProbOracleComp.run_map, run_ofbKeystreamQueries, map_pure, ofbWordEncrypt, ivStreamEncrypt,
      ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, hmb]
    refine PMF.bind_congr_on_support _ _ _ fun iv hiv => ?_
    rw [hchain _ _ (BitString.length_of_mem_support_uniformList hiv), ofbWordKeystream]
  · simp [hvalid]

/-- **Real game.** Against the keyed oracle, `ofbToPrfDistinguisher adversary bit` has the output
law of `adversary` in the OFB CPA game with challenge bit `bit`. -/
theorem eval_prfRealGame_ofbToPrfDistinguisher {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval (prfRealGame family (ofbToPrfDistinguisher adversary bit) n) =
      ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ofbWordEncrypt family) adversary bit n) := by
  simp only [prfRealGame, symmetricCPAGameOn, ofbToPrfDistinguisher, ProbOracleComp.run_simulate,
    ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
  exact (ProbOracleComp.QueriesSatisfy.of_forall (p := fun _ => True) (fun _ => trivial)
    (adversary n [])).eval_run_congr fun request _ =>
      eval_run_ofbPrfHandler hlen hkLen bit request

/-- The keystream queries are strict oracle PPT: each step makes one charged query and grows the
encoded state by at most `3 n` bits. -/
private theorem isOraclePPTOn_ofbKeystreamQueries {α : Type} {input : α ↪ List Bool}
    {n blocks : α → ℕ} {iv : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (hiv : ComputableInPolyTime iv input encBits)
    (hblocks : ComputableInPolyTime blocks input encUnary) :
    IsOraclePPTOn (Operation := Unit) input encBits
      (fun a => ofbKeystreamQueries (n a) (iv a) (blocks a)) := by
  let EStep := encPair input (encPair encBits encBits)
  have hnStep : ComputableInPolyTime (fun pair : α × (List Bool × List Bool) => n pair.1)
      EStep encUnary :=
    hn.comp (ComputableInPolyTime.fst _ _)
  have hquery : IsOraclePPTOn (Operation := Unit) EStep encBits
      (fun pair : α × (List Bool × List Bool) => List.take (n pair.1) <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), pair.2.1)) :=
    IsOraclePPTOn.query_take' () (by dsimp only [EStep]; fun_prop) hnStep
  have hstep : IsOraclePPTOn EStep (encPair encBits encBits)
      (fun pair : α × (List Bool × List Bool) => ofbKeystreamStep (n pair.1) pair.2) :=
    hquery.map_with' (f := fun pair y => (y, pair.2.2 ++ y)) (by dsimp only [EStep]; fun_prop)
  have hnBound : PolyBounded (fun a => (input a).length) n := by
    simpa only [encUnary_apply, List.length_replicate] using hn.polyBounded_length
  have hloop := IsOraclePPTOn.iterateWith_of_bounded_growth'
    (stateEncoding := encPair encBits encBits)
    (initial := fun a => (iv a, ([] : List Bool))) (count := blocks)
    (step := fun a state => ofbKeystreamStep (n a) state)
    hblocks (hiv.prod (ComputableInPolyTime.const [])) hstep (growth := fun a => n a * 3)
    (hnBound.mul (PolyBounded.const 3))
    (fun a state next hnext => by
      obtain ⟨y, hy, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hy
      have htake := List.length_take_le (n a) reply
      simp only [length_encPair, encBits_apply, List.length_append]
      omega)
  exact hloop.map' (ComputableInPolyTime.snd _ _)

/-- The reduction's handler is uniformly strict oracle PPT in the parameter, the auxiliary word
and the request. -/
private theorem isOraclePPTOn_ofbPrfHandler (bit : Bool) :
    IsOraclePPTOn (encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)) encBits
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) => ofbPrfHandler pair.1.1 bit pair.2) := by
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
  have hks : IsOraclePPTOn (Operation := Unit) EIv encBits
      (fun q : ((ℕ × List Bool) × (Unit × List Bool)) × List Bool =>
        ofbKeystreamQueries q.1.1.1 q.2 ((unframe q.1.2.2).length / q.1.1.1)) :=
    isOraclePPTOn_ofbKeystreamQueries (hn.comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _) hblocks
  have hyes : IsOraclePPTOn (Operation := Unit) EIv encBits
      (fun q : ((ℕ × List Bool) × (Unit × List Bool)) × List Bool =>
        (fun ks => q.2 ++ List.zipWith xor ks (if bit then dropFrame q.1.2.2 else unframe q.1.2.2))
          <$> ofbKeystreamQueries q.1.1.1 q.2 ((unframe q.1.2.2).length / q.1.1.1)) :=
    hks.map_with' (ComputableInPolyTime.bitsAppend (by dsimp only [EIv]; fun_prop)
      (ComputableInPolyTime.bitsZipWithInput xor (ComputableInPolyTime.snd _ _)
        (hmsg.comp ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))))
  unfold ofbPrfHandler
  exact IsOraclePPTOn.cond' hcond
    (IsOraclePPTOn.bind_with
      ((isPPTOn_sampleList.preprocess hn).isOraclePPTOn) hyes)
    (ComputableInPolyTime.isOraclePPTOn (ComputableInPolyTime.const []))

/-- Every answer of the handler has at most `n` bits more than the request. -/
private theorem length_le_of_mem_support_ofbPrfHandler {n : ℕ} {bit : Bool}
    {request : Unit × List Bool} {reply : List Bool}
    (hreply : reply ∈ OracleComp.support (ofbPrfHandler n bit request)) :
    reply.length ≤ n + request.2.length := by
  unfold ofbPrfHandler at hreply
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

/-- **Efficiency of the reduction.** For every uniform strict oracle-PPT adversary,
`ofbToPrfDistinguisher adversary bit` is uniform strict oracle PPT. -/
theorem isOraclePPT_ofbToPrfDistinguisher {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool (ofbToPrfDistinguisher adversary bit) :=
  (IsOraclePPTOn.interpret_preprocess_open' (operationEncoding := encFinEnum Unit)
    (handler := fun caller : ℕ × List Bool => ofbPrfHandler caller.1 bit)
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (resources := fun caller request => caller.1 + request.length)
    hadversary (by fun_prop) (isOraclePPTOn_ofbPrfHandler bit) (by fun_prop)
    fun _ _ _ hreply => length_le_of_mem_support_ofbPrfHandler hreply).isOraclePPT

/-! ### The ideal game -/

/-- From the bits of `x`, the chain against a random table `f` produces the bits of the typed
chain `ofbChain f x`. -/
private theorem iterate_randomFunction_ofFn {n : ℕ} (f : BitString n → BitString n) (b : ℕ)
    (x : BitString n) (acc : List Bool) :
    ((fun state : List Bool × List Bool =>
        ((randomFunctionOracle n f state.1).take n,
          state.2 ++ (randomFunctionOracle n f state.1).take n))^[b] (List.ofFn x, acc)).2 =
      acc ++ (ofbChain f x b).flatMap List.ofFn := by
  induction b generalizing x acc with
  | zero => simp [ofbChain]
  | succ b ih =>
    rw [Function.iterate_succ_apply]
    have hstep : (randomFunctionOracle n f (List.ofFn x)).take n = List.ofFn (f x) := by
      simp [randomFunctionOracle]
    simp only [hstep]
    rw [ih, ofbChain, List.flatMap_cons, List.append_assoc]

/-- Against a fixed function `f`, the reduction answers a request of at most `ℓ` bits as the
block-mode reduction answers its block query. -/
private theorem eval_run_ofbPrfHandler_randomFunction {n : ℕ} (f : BitString n → BitString n)
    (ℓ : ℕ) (bit : Bool) (request : Unit × List Bool) (hℓ : request.2.length ≤ ℓ) :
    ProbComp.eval ((ofbPrfHandler n bit request).run
        fun r => pure (randomFunctionOracle n f r.2)) =
      ProbComp.eval ((blockModeWordQuery n request).run
        fun q => (ofbQueryProgram ℓ bit q).run fun x => pure (f x)) := by
  unfold ofbPrfHandler blockModeWordQuery
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
      ProbOracleComp.run_map, ProbOracleComp.run_query, ofbQueryProgram, blockModeQueryProgram,
      hsel, run_ofbChainQueries, ProbOracleComp.run_pure, pure_bind, run_ofbKeystreamQueries,
      map_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, ProbComp.eval_uniform,
      BitString.eval_sampleList, BitString.uniformList, PMF.bind_map, PMF.map_bind,
      Function.comp_def, PMF.pure_map]
    refine congrArg _ (funext fun iv => congrArg PMF.pure ?_)
    rw [iterate_randomFunction_ofFn, List.nil_append, BitString.flatMap_ofFn_zipWith_add _ _ (by
        rw [length_ofbChain, BitString.length_padBlocks, hmb]),
      BitString.flatMap_ofFn_padBlocks (Nat.dvd_of_mod_eq_zero hmbMod), BitString.length_padBlocks,
      hmb]
  · simp [hvalid]

/-- Against a uniform random function, the reduction for an adversary whose requests have at most
`ℓ` bits is the typed OFB reduction for the block-mode adversary. -/
private theorem eval_prfIdealGame_ofbToPrfDistinguisher (adversary : OracleDistinguisher)
    (bit : Bool) {n ℓ : ℕ}
    (hℓ : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ ℓ) :
    ProbComp.eval (prfIdealGame (ofbToPrfDistinguisher adversary bit) n) =
      ProbComp.eval (PRF.idealExperiment
        (ofbReduction ℓ bit (blockModeWordAdversary adversary n))) := by
  simp only [prfIdealGame, PRF.idealExperiment, ofbToPrfDistinguisher, ofbReduction,
    blockModeReduction, blockModeWordAdversary, ProbOracleComp.run_simulate, ProbComp.eval_bind]
  exact congrArg _ (funext fun f =>
    hℓ.eval_run_congr fun request hrequest =>
      eval_run_ofbPrfHandler_randomFunction f ℓ bit request hrequest)

/-- **Concrete CPA bound for OFB mode** ([BonehShoup2023], Exercise 5.15(b)). At parameter `n`, an
adversary making at most `Q` requests of at most `L` bits has CPA advantage against
`ofbWordEncrypt family` at most the PRF advantages of `ofbToPrfDistinguisher adversary false` and
`ofbToPrfDistinguisher adversary true` plus `2 (Q L) (Q L + L) / 2 ^ n`. -/
theorem advantage_ofbWordCPAGame_le {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) {n Q L : ℕ} (hQ : (adversary n []).IsQueryBounded Q)
    (hL : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ L) :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ofbWordEncrypt family) adversary false n))
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ofbWordEncrypt family) adversary true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ofbToPrfDistinguisher adversary false) n))
        (ProbComp.eval (prfIdealGame (ofbToPrfDistinguisher adversary false) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame family (ofbToPrfDistinguisher adversary true) n))
        (ProbComp.eval (prfIdealGame (ofbToPrfDistinguisher adversary true) n)) : ℝ) +
      2 * ((Q : ℝ) * L) * ((Q : ℝ) * L + L) / 2 ^ n := by
  rw [← eval_prfRealGame_ofbToPrfDistinguisher hlen adversary false n,
    ← eval_prfRealGame_ofbToPrfDistinguisher hlen adversary true n]
  have hcost := isCostBounded_blockModeWordAdversary hQ L
  have h₀ := advantage_idealExperiment_ofbReduction_le L false hcost
  have h₁ := advantage_idealExperiment_ofbReduction_le L true hcost
  rw [← eval_prfIdealGame_ofbToPrfDistinguisher adversary false hL] at h₀
  rw [← eval_prfIdealGame_ofbToPrfDistinguisher adversary true hL] at h₁
  refine (advantage_le_four _
    (ProbComp.eval (prfIdealGame (ofbToPrfDistinguisher adversary false) n))
    (ProbComp.eval (blockModeIdealExperiment L (blockModeWordAdversary adversary n)))
    (ProbComp.eval (prfIdealGame (ofbToPrfDistinguisher adversary true) n)) _).trans ?_
  rw [Nat.cast_mul] at h₀ h₁
  have hsplit : 2 * ((Q : ℝ) * L) * ((Q : ℝ) * L + L) / 2 ^ n =
      (Q : ℝ) * L * ((Q : ℝ) * L + L) / 2 ^ n + (Q : ℝ) * L * ((Q : ℝ) * L + L) / 2 ^ n := by
    ring
  rw [hsplit]
  linarith

/-- **OFB mode is CPA-secure for a pseudorandom function** ([BonehShoup2023], Exercise 5.15(b)):
if `family` is a `PseudorandomFunction`, OFB mode with `n`-bit blocks at security parameter `n`
has negligible many-query left-or-right CPA advantage on equal-length pairs of whole blocks,
against every uniform strict oracle-PPT adversary. The exercise fixes the number of blocks `ℓ`;
here every number of blocks is admitted. -/
theorem PseudorandomFunction.indcpa_ofbWordEncrypt {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    SymmetricINDCPAOn blockPairValid BitString.sampleList (ofbWordEncrypt family) := by
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let P : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hq (n : ℕ) : (adversary n []).IsQueryBounded (P n) := by
    simpa only [P, List.length_nil, Nat.add_zero] using (hbounds n []).1
  have hl (n : ℕ) : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ P n := by
    simpa only [P, List.length_nil, Nat.add_zero] using (hbounds n []).2
  have hprf₀ := hprf.secure (ofbToPrfDistinguisher adversary false)
    (isOraclePPT_ofbToPrfDistinguisher hadversary false)
  have hprf₁ := hprf.secure (ofbToPrfDistinguisher adversary true)
    (isOraclePPT_ofbToPrfDistinguisher hadversary true)
  negligible using fun n => advantage_ofbWordCPAGame_le hprf.length_eq adversary (hq n) (hl n)

end Cslib.Crypto
