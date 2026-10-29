/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.NaorReingold.Security
public import Complexity.Crypto.Computational.PseudorandomFunction
public import Complexity.Crypto.Computational.PseudorandomGenerator
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Probabilistic.Oracle.Parameter
import Complexity.Crypto.Computational.GGM.Security
import Complexity.Crypto.Computational.GeneratorReindex
import Complexity.Crypto.Computational.PseudorandomFunction.TruthTable
import Complexity.Crypto.Computational.Stretch
import Complexity.Crypto.Game.Statistical
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.BitString
import Complexity.Probability.IID
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Map
import Complexity.Probability.StatisticalDistance.Product
import Complexity.Probability.Uniform
import Complexity.Tactic.PPT
import Mathlib.Tactic.Linarith

/-!
# Uniform `PseudorandomFunction` Instantiation of Naor–Reingold from DDH

This module connects the setup-parameterized universal-hash Naor–Reingold security theorems of
`Complexity.Crypto.Computational.NaorReingold.Security` to the uniform bit-string primitives
`Cslib.Crypto.PseudorandomGenerator` and `Cslib.Crypto.PseudorandomFunction` over any deterministic
polynomial-time prime-order group family `desc : ℕ → F.Desc`:

1. **Key-expanded Naor–Reingold bit-string PRF (`naorReingoldSeededPRF`,
   `DDH.pseudorandomFunction_naorReingoldSeeded`)** (paraphrase of [NaorReingold2004], Section 4.1,
   Construction 4.2 and Theorem 4.3, combined with PRG key expansion so a uniform `n`-bit secret key
   supplies both the `n + 1` modular exponents and the two-universal hash seed required by
   `Cslib.Crypto.PseudorandomFunction`): given an expanding PRG `expand : List Bool → List Bool`
   producing at least `(n + 1) * expWidth n + n * (2 * bound (desc n) + 1)` bits from an `n`-bit key
   with `expWidth n ≥ (F.order (desc n)).size + n`, `naorReingoldSeededPRF` slices `expand key` into
   `n + 1` binary exponents `α₀, α₁, …, αₙ` and a universal-hash seed and evaluates
   `naorReingoldHashedWordEval`. When `F.DDH (fun n => PMF.pure (desc n))` holds and
   `2 ^ n / F.order (desc n)` is negligible, `naorReingoldSeededPRF` satisfies
   `Cslib.Crypto.PseudorandomFunction`.
2. **Direct algebraic PRG from DDH alone (`DDH.exists_pseudorandomGenerator`)**: evaluating 1-bit
   universal-hash Naor–Reingold (`outLen = 1`, whose Leftover Hash Lemma error decays via
   `DDH.negligible_expected_inv_order` without any external order-growth hypothesis) at
   `seedLen n + 1` distinct binary inputs `Cslib.BitString.lowBits (inBits n) i` stretches a uniform
   `seedLen n`-bit seed by one bit, and `Cslib.Crypto.GeneratorReindex.pseudorandomGenerator`
   reindexes it to a `Cslib.Crypto.PseudorandomGenerator` at every seed length `n`.
3. **End-to-end `PseudorandomFunction` from DDH (`DDH.exists_naorReingoldPseudorandomFunction`,
   `DDH.exists_pseudorandomFunction`)**: amplifying the DDH PRG via
   `Cslib.Crypto.PseudorandomGenerator.amplify` instantiates `naorReingoldSeededPRF` directly from
   `F.DDH (fun n => PMF.pure (desc n))` and `Negligible (fun n => 2 ^ n / F.order (desc n))`;
   combining `DDH.exists_pseudorandomGenerator` with the Goldreich–Goldwasser–Micali construction
   `PseudorandomGenerator.exists_pseudorandomFunction` ([GGM1986]) also yields
   `∃ family, PseudorandomFunction family` from `F.DDH (fun n => PMF.pure (desc n))` alone.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldSeededPRF`: keyed bit-string family evaluating
  `naorReingoldHashedWordEval` on exponents and hash seed expanded from an `n`-bit secret key.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_naorReingoldSeededPRF`: polynomial-time
  evaluation of `naorReingoldSeededPRF`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.pseudorandomFunction_naorReingoldSeeded`:
  `PseudorandomFunction` security of `naorReingoldSeededPRF` from DDH, a key-expanding PRG, and
  negligible `2 ^ n / F.order (desc n)`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.exists_pseudorandomGenerator`: existence of a uniform
  one-bit-stretch `PseudorandomGenerator` from `F.DDH (fun n => PMF.pure (desc n))` alone.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.exists_naorReingoldPseudorandomFunction`: existence of
  parameters instantiating `naorReingoldSeededPRF` as a `PseudorandomFunction` from DDH and
  negligible `2 ^ n / F.order (desc n)`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.exists_pseudorandomFunction`: existence of a uniform
  `PseudorandomFunction` from `F.DDH (fun n => PMF.pure (desc n))` alone via
  `DDH.exists_pseudorandomGenerator` and the Goldreich–Goldwasser–Micali construction ([GGM1986]).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.11 (Exercise 4.18, p. 172) and Section 10.11
  (Exercises 10.4, 10.8, and 10.11, pp. 424–426).
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].
* [M. Naor, O. Reingold, *Number-Theoretic Constructions of Efficient Pseudo-Random
  Functions*][NaorReingold2004], Section 4.1 (Construction 4.1, Theorem 4.1, Lemma 4.2,
  Construction 4.2, Theorem 4.3, and Remark 4.2).
-/

public section

open scoped ENNReal NNReal Cslib.Probability.PMF

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace PrimeOrderGroupFamily

variable (F : PrimeOrderGroupFamily)

/-! ### Tape Parsing and Uniform-Tape Indistinguishability -/

private def parseNaorReingoldTape (count expWidth hashLen : ℕ) (tape : List Bool) :
    ℕ × List ℕ × List Bool :=
  let rest := tape.drop expWidth
  let α₀ := Cslib.BitString.binaryValue (tape.take expWidth)
  let αs := (Cslib.BitString.listRows count expWidth (rest.take (count * expWidth))).map
    Cslib.BitString.binaryValue
  let hashSeed := (rest.drop (count * expWidth)).take hashLen
  (α₀, αs, hashSeed)

private theorem parseNaorReingoldTape_take {count expWidth hashLen limit : ℕ}
    (hlim : expWidth + (count * expWidth + hashLen) ≤ limit) (tape : List Bool) :
    parseNaorReingoldTape count expWidth hashLen (tape.take limit) =
      parseNaorReingoldTape count expWidth hashLen tape := by
  simp only [parseNaorReingoldTape, List.take_take, List.drop_take]
  have h1 : min expWidth limit = expWidth := Nat.min_eq_left (by omega)
  have h2 : min (count * expWidth) (limit - expWidth) = count * expWidth :=
    Nat.min_eq_left (by omega)
  have h3 : min hashLen (limit - expWidth - count * expWidth) = hashLen :=
    Nat.min_eq_left (by omega)
  rw [h1, h2, h3]

private def evalNaorReingoldTape (inLen outLen : ℕ → ℕ) (desc : ℕ → F.Desc) (bound : F.Desc → ℕ)
    (expWidth : ℕ → ℕ) (n : ℕ) (tape query : List Bool) : List Bool :=
  let parsed :=
    parseNaorReingoldTape (inLen n) (expWidth n) (outLen n * (2 * bound (desc n) + 1)) tape
  F.naorReingoldHashedWordEval (outLen n) bound (desc n) parsed.2.2 parsed.1 parsed.2.1 query

@[simp]
private theorem length_evalNaorReingoldTape (inLen outLen : ℕ → ℕ) (desc : ℕ → F.Desc)
    (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ) (n : ℕ) (tape query : List Bool) :
    (F.evalNaorReingoldTape inLen outLen desc bound expWidth n tape query).length = outLen n := by
  simp [evalNaorReingoldTape]

private theorem evalNaorReingoldTape_take (inLen outLen : ℕ → ℕ) (desc : ℕ → F.Desc)
    (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ) {n limit : ℕ}
    (hlim : expWidth n + (inLen n * expWidth n + outLen n * (2 * bound (desc n) + 1)) ≤ limit)
    (tape query : List Bool) :
    F.evalNaorReingoldTape inLen outLen desc bound expWidth n (tape.take limit) query =
      F.evalNaorReingoldTape inLen outLen desc bound expWidth n tape query := by
  simp only [evalNaorReingoldTape, parseNaorReingoldTape_take hlim]

private theorem computableTidilyInPolyTime_parseNaorReingoldTape {α : Type} {input : α ↪ List Bool}
    {count expWidth hashLen : α → ℕ} {tape : α → List Bool}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hexp : ComputableTidilyInPolyTime expWidth input encUnary)
    (hhash : ComputableTidilyInPolyTime hashLen input encUnary)
    (htape : ComputableTidilyInPolyTime tape input encBits) :
    ComputableTidilyInPolyTime
      (fun a => parseNaorReingoldTape (count a) (expWidth a) (hashLen a) (tape a))
      input (encPair encNat (encPair (encList encNat) encBits)) := by
  have hcw : ComputableTidilyInPolyTime (fun a => count a * expWidth a) input encUnary := by
    polytime
  have hrest := ComputableTidilyInPolyTime.bitsDropWithInput htape hexp
  have hα₀ := ComputableTidilyInPolyTime.bitsBinaryValue.comp
    (ComputableTidilyInPolyTime.bitsTakeWithInput htape hexp)
  have hrows := ComputableTidilyInPolyTime.bitsRowsWithInput hcount hexp
    (ComputableTidilyInPolyTime.bitsTakeWithInput hrest hcw)
  have hαs := (ComputableTidilyInPolyTime.map ComputableTidilyInPolyTime.bitsBinaryValue).comp hrows
  have hseed := ComputableTidilyInPolyTime.bitsTakeWithInput
    (ComputableTidilyInPolyTime.bitsDropWithInput hrest hcw) hhash
  exact hα₀.prod (hαs.prod hseed)

private theorem computableInPolyTime_evalNaorReingoldTape
    {inLen outLen : ℕ → ℕ} {desc : ℕ → F.Desc} {bound : F.Desc → ℕ} {expWidth : ℕ → ℕ}
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    (hexp : ComputableInPolyTime expWidth encUnary encUnary) :
    ComputableInPolyTime
      (fun x : ℕ × List Bool × List Bool =>
        F.evalNaorReingoldTape inLen outLen desc bound expWidth x.1 x.2.1 x.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  let EIn := encPair encUnary (encPair encBits encBits)
  have hparam : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => x.1) EIn encUnary :=
    ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  have hrest := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  have htape : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => x.2.1) EIn encBits :=
    (ComputableInPolyTime.fst encBits encBits).comp hrest
  have hquery : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => x.2.2) EIn encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp hrest
  have hp_t := hparam.tidy
  have hin_t := hinLen.tidy.comp hp_t
  have hd_c := hdesc.comp hparam
  have hexp_t := hexp.tidy.comp hp_t
  have hhash_t : ComputableTidilyInPolyTime
      (fun x : ℕ × List Bool × List Bool => outLen x.1 * (2 * bound (desc x.1) + 1))
      EIn encUnary :=
    ((houtLen.comp hparam).unary_mul'
      (((ComputableInPolyTime.const 2).unary_mul' (hbound.comp hd_c)).unary_add'
        (ComputableInPolyTime.const 1))).tidy
  have hparsed := computableTidilyInPolyTime_parseNaorReingoldTape hin_t hexp_t hhash_t htape.tidy
  let ERows := encPair (encList encNat) encBits
  have hp1 : ComputableInPolyTime
      (fun x : ℕ × List Bool × List Bool => (parseNaorReingoldTape (inLen x.1) (expWidth x.1)
        (outLen x.1 * (2 * bound (desc x.1) + 1)) x.2.1).1)
      EIn encNat :=
    .of_tidy ((ComputableTidilyInPolyTime.fst encNat ERows).comp hparsed)
  have hp2 := (ComputableTidilyInPolyTime.snd encNat ERows).comp hparsed
  have hp21 : ComputableInPolyTime
      (fun x : ℕ × List Bool × List Bool => (parseNaorReingoldTape (inLen x.1) (expWidth x.1)
        (outLen x.1 * (2 * bound (desc x.1) + 1)) x.2.1).2.1)
      EIn (encList encNat) :=
    .of_tidy ((ComputableTidilyInPolyTime.fst (encList encNat) encBits).comp hp2)
  have hp22 : ComputableInPolyTime
      (fun x : ℕ × List Bool × List Bool => (parseNaorReingoldTape (inLen x.1) (expWidth x.1)
        (outLen x.1 * (2 * bound (desc x.1) + 1)) x.2.1).2.2)
      EIn encBits :=
    .of_tidy ((ComputableTidilyInPolyTime.snd (encList encNat) encBits).comp hp2)
  have hpack : ComputableInPolyTime
      (fun x : ℕ × List Bool × List Bool =>
        let p := parseNaorReingoldTape (inLen x.1) (expWidth x.1)
          (outLen x.1 * (2 * bound (desc x.1) + 1)) x.2.1
        (outLen x.1, desc x.1, p.2.2, p.1, p.2.1, x.2.2))
      EIn (encPair encUnary (encPair F.encDesc
        (encPair encBits (encPair encNat (encPair (encList encNat) encBits))))) :=
    (houtLen.comp hparam).prod (hd_c.prod (hp22.prod (hp1.prod (hp21.prod hquery))))
  exact (F.computableInPolyTime_naorReingoldHashedWordEval hbound).comp hpack

private theorem computableInPolyTime_evalNaorReingoldTape_of
    {α : Type} {input : α ↪ List Bool}
    {inLen outLen : ℕ → ℕ} {desc : ℕ → F.Desc} {bound : F.Desc → ℕ} {expWidth : ℕ → ℕ}
    {param : α → ℕ} {tape query : α → List Bool}
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    (hexp : ComputableInPolyTime expWidth encUnary encUnary)
    (hparam : ComputableInPolyTime param input encUnary)
    (htape : ComputableInPolyTime tape input encBits)
    (hquery : ComputableInPolyTime query input encBits) :
    ComputableInPolyTime
      (fun a => F.evalNaorReingoldTape inLen outLen desc bound expWidth
        (param a) (tape a) (query a))
      input encBits :=
  ((computableInPolyTime_evalNaorReingoldTape F hinLen houtLen hdesc hbound hexp).comp
    (hparam.prod (htape.prod hquery))).of_enc_eq fun _ => rfl

private noncomputable def binaryZModLaw (width q : ℕ) : PMF (ZMod q) :=
  ((Cslib.BitString.uniformList width).map Cslib.BitString.binaryValue).map Nat.cast

private theorem binaryZModLaw_eq_sampleModNat (width q : ℕ) :
    binaryZModLaw width q = (ProbComp.eval (ProbComp.sampleModNat width q)).map Nat.cast := by
  simp only [binaryZModLaw, ProbComp.sampleModNat, ProbComp.sampleBinaryNat, ProbComp.eval_map,
    Cslib.BitString.eval_sampleList, PMF.map_comp, Function.comp_def, ZMod.natCast_mod]

private theorem dist_binaryZModLaw_le {s width q : ℕ} [NeZero q]
    (hw : q.size + s ≤ width) :
    dist (binaryZModLaw width q) (PMF.uniformOfFintype (ZMod q)) ≤ 1 / 2 ^ s := by
  rw [binaryZModLaw_eq_sampleModNat]
  have h1 := ProbComp.dist_map_natCast_eval_sampleModNat_le width q
  have hlt : (q : ℝ) < (2 : ℝ) ^ q.size := by exact_mod_cast Nat.lt_size_self q
  have hle : (2 : ℝ) ^ (q.size + s) ≤ (2 : ℝ) ^ width := pow_le_pow_right₀ (by norm_num) hw
  calc dist ((ProbComp.eval (ProbComp.sampleModNat width q)).map (Nat.cast : ℕ → ZMod q))
        (PMF.uniformOfFintype (ZMod q))
      ≤ (q : ℝ) / (2 : ℝ) ^ width := h1
    _ ≤ (2 : ℝ) ^ q.size / (2 : ℝ) ^ (q.size + s) := by
        exact div_le_div₀ (by positivity) hlt.le (by positivity) hle
    _ = 1 / 2 ^ s := by
        rw [pow_add, div_mul_eq_div_div, div_self (by positivity)]

private theorem uniformList_map_listRows_binaryValue : ∀ (count width : ℕ),
    (Cslib.BitString.uniformList (count * width)).map
      (fun w => (Cslib.BitString.listRows count width w).map Cslib.BitString.binaryValue) =
    (PMF.iid ((Cslib.BitString.uniformList width).map Cslib.BitString.binaryValue) count).map
      List.ofFn
  | 0, width => by
      simp [Cslib.BitString.listRows, PMF.iid, PMF.map, Function.comp_def, PMF.bind_const]
  | count + 1, width => by
      have hmul : (count + 1) * width = width + count * width := by ring
      rw [hmul, Cslib.BitString.uniformList_add, PMF.iid, PMF.monad_bind_eq_bind, PMF.map_bind,
        PMF.map_bind, PMF.bind_map]
      refine PMF.bind_congr_on_support _ _ _ fun u hu => ?_
      have hlen : u.length = width := Cslib.BitString.length_of_mem_support_uniformList hu
      have hstep :
          ((Cslib.BitString.uniformList (count * width)).map (u ++ ·)).map
            (fun w =>
              (Cslib.BitString.listRows (count + 1) width w).map Cslib.BitString.binaryValue) =
          ((Cslib.BitString.uniformList (count * width)).map
            (fun v =>
              (Cslib.BitString.listRows count width v).map Cslib.BitString.binaryValue)).map
            (Cslib.BitString.binaryValue u :: ·) := by
        simp only [PMF.map_comp, Function.comp_def,
          Cslib.BitString.listRows_succ_append count width hlen, List.map_cons]
      rw [hstep, uniformList_map_listRows_binaryValue count width]
      simp only [PMF.map_comp, Function.comp_def]
      congr 1; funext v
      simp [List.ofFn_succ]

private theorem uniformList_map_parseNaorReingoldTape (count expWidth hashLen : ℕ) :
    (Cslib.BitString.uniformList (expWidth + (count * expWidth + hashLen))).map
      (parseNaorReingoldTape count expWidth hashLen) =
    ((Cslib.BitString.uniformList expWidth).map Cslib.BitString.binaryValue).bind fun α₀ =>
      ((PMF.iid ((Cslib.BitString.uniformList expWidth).map Cslib.BitString.binaryValue) count).map
        List.ofFn).bind fun αs =>
        (Cslib.BitString.uniformList hashLen).map fun seed => (α₀, αs, seed) := by
  rw [PMF.map]
  simp only [Function.comp_def, parseNaorReingoldTape]
  rw [Cslib.BitString.uniformList_bind_split expWidth (count * expWidth + hashLen)
    (fun front rest => PMF.pure
      (Cslib.BitString.binaryValue front,
        (Cslib.BitString.listRows count expWidth (rest.take (count * expWidth))).map
          Cslib.BitString.binaryValue,
        (rest.drop (count * expWidth)).take hashLen))]
  conv_rhs => rw [PMF.bind_map]
  congr 1; funext front
  rw [Cslib.BitString.uniformList_bind_split (count * expWidth) hashLen
    (fun mid back => PMF.pure
      (Cslib.BitString.binaryValue front,
        (Cslib.BitString.listRows count expWidth mid).map Cslib.BitString.binaryValue,
        back.take hashLen))]
  have hmid :
      ((Cslib.BitString.uniformList (count * expWidth)).bind fun mid =>
        (Cslib.BitString.uniformList hashLen).bind fun back =>
          PMF.pure (Cslib.BitString.binaryValue front,
            (Cslib.BitString.listRows count expWidth mid).map Cslib.BitString.binaryValue,
            back.take hashLen)) =
      (((Cslib.BitString.uniformList (count * expWidth)).map fun mid =>
          (Cslib.BitString.listRows count expWidth mid).map Cslib.BitString.binaryValue).bind
        fun αs => (Cslib.BitString.uniformList hashLen).bind fun back =>
          PMF.pure (Cslib.BitString.binaryValue front, αs, back.take hashLen)) := by
    rw [PMF.bind_map]; rfl
  rw [hmid, uniformList_map_listRows_binaryValue count expWidth]
  dsimp only [Function.comp_def]
  congr 1; funext αs
  rw [PMF.map]
  refine PMF.bind_congr_on_support _ _ _ fun back hback => ?_
  have hlen := Cslib.BitString.length_of_mem_support_uniformList hback
  simp only [Function.comp_def, List.take_of_length_le hlen.le]

private theorem advantage_evalNaorReingoldTape_uniform_le (inLen outLen : ℕ → ℕ)
    (desc : ℕ → F.Desc) (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ)
    (hexp : (F.order (desc n)).size + n ≤ expWidth n) :
    Game.advantage
      ((Cslib.BitString.uniformList
        (expWidth n + (inLen n * expWidth n + outLen n * (2 * bound (desc n) + 1)))).bind
        fun tape =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = inLen n then
                F.evalNaorReingoldTape inLen outLen desc bound expWidth n tape request.2
              else []))
            (adversary n []))
      (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) inLen outLen bound
        (fun k _ => adversary k []) n) ≤
      ((inLen n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  let m := inLen n
  let ℓ := outLen n
  let d := desc n
  let E := expWidth n
  let H := ℓ * (2 * bound d + 1)
  have : NeZero (F.order d) := ⟨(F.prime_order d).ne_zero⟩
  let detRun : ZMod (F.order d) × (Fin m → ZMod (F.order d)) → PMF Bool :=
    fun p =>
      (Cslib.BitString.uniformList H).bind fun seed =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle fun request =>
            PMF.pure (if request.2.length = m then
              F.linearHashKDF (fun _ => ℓ) bound
                ((d, seed), F.encode d (F.naorReingoldEval d p.1 p.2
                  (BitString.ofList m request.2)))
            else []))
          (adversary n [])
  let μNat : PMF ℕ := (Cslib.BitString.uniformList E).map Cslib.BitString.binaryValue
  let μ : PMF (ZMod (F.order d)) := μNat.map Nat.cast
  let ν : PMF (ZMod (F.order d)) := PMF.uniformOfFintype (ZMod (F.order d))
  have hlhs :
      ((Cslib.BitString.uniformList (E + (m * E + H))).bind fun tape =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle fun request =>
            PMF.pure (if request.2.length = m then
              F.evalNaorReingoldTape inLen outLen desc bound expWidth n tape request.2
            else []))
          (adversary n [])) =
      (μ.bind fun α₀ => (PMF.iid μ m).map (α₀, ·)).bind detRun := by
    have hparse := congrArg
      (fun law : PMF (ℕ × List ℕ × List Bool) =>
        law.bind fun parsed =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = m then
                F.naorReingoldHashedWordEval ℓ bound d parsed.2.2 parsed.1 parsed.2.1 request.2
              else []))
            (adversary n []))
      (uniformList_map_parseNaorReingoldTape m E H)
    conv_lhs at hparse => rw [PMF.bind_map]
    refine Eq.trans hparse ?_
    change ((μNat.bind fun α₀ => ((PMF.iid μNat m).map List.ofFn).bind fun αs =>
      (Cslib.BitString.uniformList H).map fun seed => (α₀, αs, seed)).bind _) = _
    simp only [μ, PMF.iid_map, PMF.bind_map, PMF.bind_bind, PMF.map_comp, Function.comp_def]
    congr 1; funext a₀; congr 1; funext aVec; congr 1; funext seed
    congr 1; funext q
    cases q with
    | inl r => rfl
    | inr request =>
      dsimp only [ProbOracleComp.handler]
      by_cases hq : request.2.length = m
      · simp only [hq, ↓reduceIte, naorReingoldHashedWordEval]
        have hxs : List.ofFn (BitString.ofList m request.2) = request.2 :=
          BitString.ofFn_ofList hq
        have heval := F.naorReingoldWordEval_eq_encode d a₀ aVec
          (BitString.ofList m request.2)
        rw [hxs] at heval
        rw [heval]
      · simp [hq]
  have hrhs :
      F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) inLen outLen bound
        (fun k _ => adversary k []) n =
      (ν.bind fun α₀ => (PMF.iid ν m).map (α₀, ·)).bind detRun := by
    simp only [naorReingoldHashedRealGame, seededSetup, linearHashSeedLen,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.bind_bind, PMF.bind_map,
      Function.comp_def]
    change ((Cslib.BitString.uniformList H).bind fun seed =>
      ν.bind fun α₀ => (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle fun request =>
            PMF.pure (if request.2.length = m then
              F.linearHashKDF (fun _ => ℓ) bound
                ((d, seed), F.encode d (F.naorReingoldEval d α₀ α (BitString.ofList m request.2)))
            else []))
          (adversary n [])) =
      ν.bind fun α₀ => (PMF.iid ν m).bind fun α => detRun (α₀, α)
    rw [PMF.bind_comm (Cslib.BitString.uniformList H) ν]
    congr 1; funext α₀
    rw [PMF.bind_comm (Cslib.BitString.uniformList H)
      (PMF.uniformOfFintype (Fin m → ZMod (F.order d))), ← iid_uniformOfFintype m]
  change Game.advantage
    ((Cslib.BitString.uniformList (E + (m * E + H))).bind _)
    (F.naorReingoldHashedRealGame _ _ _ _ _ n) ≤ _
  rw [hlhs, hrhs, Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
  have hd_step : dist μ ν ≤ 1 / 2 ^ n :=
    dist_binaryZModLaw_le hexp
  have h1 :
      dist (μ.bind fun α₀ => (PMF.iid μ m).map (α₀, ·))
        (ν.bind fun α₀ => (PMF.iid μ m).map (α₀, ·)) ≤ dist μ ν :=
    PMF.dist_bind_le _ _ _
  have hswap (p : PMF (ZMod (F.order d))) (q : PMF (Fin m → ZMod (F.order d))) :
      (p.bind fun α₀ => q.map (α₀, ·)) = (q.bind fun α => p.map (·, α)) := by
    simp only [PMF.map]
    exact PMF.bind_comm p q _
  have h2 :
      dist (ν.bind fun α₀ => (PMF.iid μ m).map (α₀, ·))
        (ν.bind fun α₀ => (PMF.iid ν m).map (α₀, ·)) ≤ m * dist μ ν := by
    rw [hswap ν (PMF.iid μ m), hswap ν (PMF.iid ν m)]
    exact (PMF.dist_bind_le _ _ _).trans (PMF.dist_iid_le μ ν m)
  calc dist
        ((μ.bind fun α₀ => (PMF.iid μ m).map (α₀, ·)).bind detRun)
        ((ν.bind fun α₀ => (PMF.iid ν m).map (α₀, ·)).bind detRun)
      ≤ dist
          (μ.bind fun α₀ => (PMF.iid μ m).map (α₀, ·))
          (ν.bind fun α₀ => (PMF.iid ν m).map (α₀, ·)) :=
        PMF.dist_bind_le _ _ _
    _ ≤ dist μ ν + m * dist μ ν := (dist_triangle _ _ _).trans (add_le_add h1 h2)
    _ = (m + 1 : ℝ) * dist μ ν := by ring
    _ ≤ (m + 1 : ℝ) * (1 / 2 ^ n) := mul_le_mul_of_nonneg_left hd_step (by positivity)
    _ = ((((m + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by push_cast; ring

private theorem naorReingoldHashedIdealGame_pure_const (inLen outLen : ℕ → ℕ)
    (desc : ℕ → F.Desc) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) inLen outLen bound
      (fun k _ => adversary k []) n =
    (PMF.uniformOfFintype (BitString (inLen n) → BitString (outLen n))).bind fun f =>
      OracleComp.interpret
        (ProbOracleComp.handler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = inLen n then
            List.ofFn (f (BitString.ofList (inLen n) request.2))
          else []))
        (adversary n []) := by
  simp only [naorReingoldHashedIdealGame, PMF.monad_bind_eq_bind, PMF.bind_const]

/-! ### Key-Expanded Naor–Reingold `PseudorandomFunction` -/

/-- Keyed bit-string family evaluating the universal-hash Naor–Reingold construction
`naorReingoldHashedWordEval` after expanding `key` via `expand` into `key.length + 1`
`expWidth key.length`-bit binary exponents and a
`key.length * (2 * bound (desc key.length) + 1)`-bit two-universal hash seed (paraphrase of
[NaorReingold2004], Section 4.1, Construction 4.2, combined with PRG key expansion so a uniform
`n`-bit secret key suffices for `Cslib.Crypto.PseudorandomFunction`). -/
@[expose] def naorReingoldSeededPRF (desc : ℕ → F.Desc) (bound : F.Desc → ℕ)
    (expWidth : ℕ → ℕ) (expand : List Bool → List Bool)
    (key query : List Bool) : List Bool :=
  let n := key.length
  let E := expWidth n
  let H := n * (2 * bound (desc n) + 1)
  let tape := expand key
  let rest := tape.drop E
  let α₀ := Cslib.BitString.binaryValue (tape.take E)
  let αs := (Cslib.BitString.listRows n E (rest.take (n * E))).map Cslib.BitString.binaryValue
  let hashSeed := (rest.drop (n * E)).take H
  F.naorReingoldHashedWordEval n bound (desc n) hashSeed α₀ αs query

private theorem naorReingoldSeededPRF_eq_evalTape (desc : ℕ → F.Desc) (bound : F.Desc → ℕ)
    (expWidth : ℕ → ℕ) (expand : List Bool → List Bool) (key query : List Bool) :
    F.naorReingoldSeededPRF desc bound expWidth expand key query =
      F.evalNaorReingoldTape id id desc bound expWidth key.length (expand key) query := rfl

/-- `naorReingoldSeededPRF` always outputs a bit string of length `key.length`. -/
@[simp] theorem length_naorReingoldSeededPRF (desc : ℕ → F.Desc) (bound : F.Desc → ℕ)
    (expWidth : ℕ → ℕ) (expand : List Bool → List Bool) (key query : List Bool) :
    (F.naorReingoldSeededPRF desc bound expWidth expand key query).length = key.length := by
  simp [naorReingoldSeededPRF]

/-- `naorReingoldSeededPRF` is computable in deterministic polynomial time when `desc`, `bound`,
`expWidth`, and `expand` are polynomial-time computable. -/
theorem computableInPolyTime_naorReingoldSeededPRF {desc : ℕ → F.Desc} {bound : F.Desc → ℕ}
    {expWidth : ℕ → ℕ} {expand : List Bool → List Bool}
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    (hexpWidth : ComputableInPolyTime expWidth encUnary encUnary)
    (hexpand : ComputableInPolyTime expand encBits encBits) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        F.naorReingoldSeededPRF desc bound expWidth expand p.1 p.2)
      (encPair encBits encBits) encBits := by
  simp only [naorReingoldSeededPRF_eq_evalTape]
  have hklen : ComputableInPolyTime (fun p : List Bool × List Bool => p.1.length)
      (encPair encBits encBits) encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.length_bits.comp
      (ComputableTidilyInPolyTime.fst encBits encBits))
  have htape : ComputableInPolyTime (fun p : List Bool × List Bool => expand p.1)
      (encPair encBits encBits) encBits :=
    hexpand.comp' (ComputableInPolyTime.fst encBits encBits)
  have hquery : ComputableInPolyTime (fun p : List Bool × List Bool => p.2)
      (encPair encBits encBits) encBits :=
    ComputableInPolyTime.snd encBits encBits
  exact computableInPolyTime_evalNaorReingoldTape_of (inLen := id) (outLen := id) F
    ComputableInPolyTime.id' ComputableInPolyTime.id' hdesc hbound hexpWidth
    hklen htape hquery

private noncomputable def prfTapeDistinguisher (F : PrimeOrderGroupFamily)
    (desc : ℕ → F.Desc) (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ)
    (adversary : OracleDistinguisher) : Distinguisher :=
  fun n tape =>
    Prod.fst <$> (OracleComp.interpret
      (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifFin r))
        fun request _ =>
          pure (if request.2.length = n then
            F.evalNaorReingoldTape id id desc bound expWidth n tape request.2
          else [], ()))
      (adversary n [])).run ()

private theorem isPPT_prfTapeDistinguisher (F : PrimeOrderGroupFamily)
    {desc : ℕ → F.Desc} {bound : F.Desc → ℕ} {expWidth : ℕ → ℕ}
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    (hexpWidth : ComputableInPolyTime expWidth encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsPPT encBool (prfTapeDistinguisher F desc bound expWidth adversary) := by
  let ECaller := encPair encUnary encBits
  let EReq := encPair (encFinEnum Unit) encBits
  let ERest := encPair EReq (encFinEnum Unit)
  let EHandler := encPair ECaller ERest
  have hprep : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => (p.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) :=
    (ComputableTidilyInPolyTime.fst encUnary encBits).prod (ComputableTidilyInPolyTime.const [])
  have hfstH := ComputableTidilyInPolyTime.fst ECaller ERest
  have hsndH := ComputableTidilyInPolyTime.snd ECaller ERest
  have hreqQ : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => pair.2.1.2)
      EHandler encBits :=
    (ComputableTidilyInPolyTime.snd (encFinEnum Unit) encBits).comp
      ((ComputableTidilyInPolyTime.fst EReq (encFinEnum Unit)).comp hsndH)
  have hnH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => pair.1.1)
      EHandler encUnary :=
    (ComputableTidilyInPolyTime.fst encUnary encBits).comp hfstH
  have htH : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit => pair.1.2)
      EHandler encBits :=
    (ComputableTidilyInPolyTime.snd encUnary encBits).comp hfstH
  have hguard : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit =>
        pair.2.1.2.length == pair.1.1)
      EHandler encBool :=
    ComputableTidilyInPolyTime.unary_beq
      (ComputableTidilyInPolyTime.length_bits.comp hreqQ) hnH
  have heval : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit =>
        (F.evalNaorReingoldTape id id desc bound expWidth pair.1.1 pair.1.2 pair.2.1.2, ()))
      EHandler (encPair encBits (encFinEnum Unit)) :=
    (computableInPolyTime_evalNaorReingoldTape_of F
      ComputableInPolyTime.id' ComputableInPolyTime.id' hdesc hbound hexpWidth
      (ComputableInPolyTime.of_tidy hnH)
      (ComputableInPolyTime.of_tidy htH)
      (ComputableInPolyTime.of_tidy hreqQ)).prod
      (ComputableInPolyTime.const (encIn := EHandler) (encOut := encFinEnum Unit) ())
  have hhandler : IsPPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) × Unit =>
        pure (if pair.2.1.2.length = pair.1.1 then
          F.evalNaorReingoldTape id id desc bound expWidth pair.1.1 pair.1.2 pair.2.1.2
        else [], ())) := by
    refine (IsPPTOn.ite hguard heval.isPPTOn
      (ComputableInPolyTime.const ([], ())).isPPTOn).congr fun pair => ?_
    by_cases h : pair.2.1.2.length = pair.1.1 <;> simp [h]
  have hres : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => pair.1.1 + 1)
      (encPair ECaller encBits) encUnary := by
    have hn : ComputableTidilyInPolyTime
        (fun pair : (ℕ × List Bool) × List Bool => pair.1.1)
        (encPair ECaller encBits) encUnary := by dsimp only [ECaller]; fun_prop
    have hsucc : ComputableTidilyInPolyTime (fun n => n + 1) encUnary encUnary := by fun_prop
    exact hsucc.comp hn
  have hrun := hadversary.run_interpret_preprocess (State := Unit)
    (stateEncoding := encFinEnum Unit)
    (handler := fun (p : ℕ × List Bool) (request : Unit × List Bool) (_ : Unit) =>
      pure (if request.2.length = p.1 then
        F.evalNaorReingoldTape id id desc bound expWidth p.1 p.2 request.2
      else [], ()))
    (prepare := fun p : ℕ × List Bool => (p.1, []))
    (initial := fun _ => ())
    (resources := fun p _ => p.1 + 1)
    hprep hhandler (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) hres
    (fun a request _ _ result hresult => by
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      by_cases hq : request.2.length = a.1 <;> simp [hq])
  exact hrun.map (ComputableInPolyTime.fst encBool (encFinEnum Unit))

private theorem eval_prfTapeDistinguisher (F : PrimeOrderGroupFamily)
    (desc : ℕ → F.Desc) (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) (tape : List Bool) :
    ProbComp.eval (prfTapeDistinguisher F desc bound expWidth adversary n tape) =
      OracleComp.interpret
        (ProbOracleComp.handler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = n then
            F.evalNaorReingoldTape id id desc bound expWidth n tape request.2
          else []))
        (adversary n []) := by
  simp only [prfTapeDistinguisher, ProbComp.eval_map, ProbOracleComp.eval_run_interpret,
    ProbComp.eval_pure]
  have hH :
      ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
        (fun (request : Unit × List Bool) (_ : Unit) =>
          PMF.pure (if request.2.length = n then
            F.evalNaorReingoldTape id id desc bound expWidth n tape request.2
          else [], ())) =
      fun q => StateT.lift (ProbOracleComp.handler ProbComp.unifOracle
        (fun request => PMF.pure (if request.2.length = n then
          F.evalNaorReingoldTape id id desc bound expWidth n tape request.2
        else [])) q) := by
    funext q
    cases q with
    | inl r => rfl
    | inr request =>
      funext u
      simp [ProbOracleComp.handler, StateT.lift, PMF.monad_pure_eq_pure]
  rw [hH, OracleComp.run_interpret_lift, ← PMF.monad_map_eq_map, Functor.map_map]
  exact id_map _

/-- **Uniform `PseudorandomFunction` security of `naorReingoldSeededPRF`** (paraphrase of
[NaorReingold2004], Section 4.1, Construction 4.2 and Theorem 4.3, combined with PRG key
expansion): if `desc : ℕ → F.Desc` is a deterministic polynomial-time group family satisfying
`F.DDH (fun n => PMF.pure (desc n))` with `2 ^ n / F.order (desc n)` negligible, `expWidth n ≥
(F.order (desc n)).size + n`, and `expand` is a `PseudorandomGenerator` stretching `n`-bit keys to
at least `(n + 1) * expWidth n + n * (2 * bound (desc n) + 1)` bits, then `naorReingoldSeededPRF`
is a uniform `PseudorandomFunction`. -/
theorem DDH.pseudorandomFunction_naorReingoldSeeded {F : PrimeOrderGroupFamily}
    {desc : ℕ → F.Desc} {bound : F.Desc → ℕ} {expWidth targetLen : ℕ → ℕ}
    {expand : List Bool → List Bool}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hbound : ∀ n, ∀ x : F.Carrier (desc n), (F.encode (desc n) x).length ≤ bound (desc n))
    (hexpWidth_poly : ComputableInPolyTime expWidth encUnary encUnary)
    (hexpWidth : ∀ n, (F.order (desc n)).size + n ≤ expWidth n)
    (hexpand : PseudorandomGenerator expand targetLen)
    (htarget : ∀ n, (n + 1) * expWidth n + n * (2 * bound (desc n) + 1) ≤ targetLen n)
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ n / (F.order (desc n) : ℝ≥0)) :
    PseudorandomFunction (F.naorReingoldSeededPRF desc bound expWidth expand) := by
  refine ⟨F.computableInPolyTime_naorReingoldSeededPRF hdesc hbound_poly hexpWidth_poly
    hexpand.polyTime, fun key query _ => F.length_naorReingoldSeededPRF _ _ _ _ key query, ?_⟩
  intro adversary hadversary
  let D_tape := prfTapeDistinguisher F desc bound expWidth adversary
  have hD_tape : IsPPT encBool D_tape :=
    isPPT_prfTapeDistinguisher F hdesc hbound_poly hexpWidth_poly hadversary
  have hprg_neg := hexpand.indistinguishable D_tape hD_tape
  have hadv_aux : IsOraclePPT encBool (fun k (_ : List Bool) => adversary k []) :=
    hadversary.on.preprocess
      ((ComputableTidilyInPolyTime.fst encUnary encBits).prod
        (ComputableTidilyInPolyTime.const []))
  obtain ⟨cD, eD, hdesc_b⟩ := hdesc.tidy.polyBounded_length.exists_le
  have hdesc_poly : PolynomiallyBounded (fun n => cD * (n + 1) ^ eD) := by fun_prop
  have hdesc_supp : ∀ n, ∀ d ∈ (PMF.pure (desc n)).support,
      (F.encDesc d).length ≤ cD * (n + 1) ^ eD := by
    intro n d hd
    rw [PMF.mem_support_pure_iff] at hd; subst hd
    simpa only [encUnary_apply, List.length_replicate] using hdesc_b n
  have hbound_supp : ∀ n, ∀ d ∈ (PMF.pure (desc n)).support, ∀ x : F.Carrier d,
      (F.encode d x).length ≤ bound d := by
    intro n d hd
    rw [PMF.mem_support_pure_iff] at hd; subst hd
    exact hbound n
  have hnr_neg := hDDH.negligible_naorReingoldHashedGame
    (inLen := id) (outLen := id) (qMin := fun n => F.order (desc n))
    ComputableInPolyTime.id' ComputableInPolyTime.id'
    hbound_poly hdesc_poly hdesc_supp hbound_supp
    (fun n => (F.prime_order (desc n)).pos)
    (fun n d hd => by rw [PMF.mem_support_pure_iff] at hd; subst hd; exact le_rfl)
    hneg hadv_aux
  have hexp_neg : Negligible fun n => ((n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    have hp : PolynomiallyBounded (fun n => n + 1) := by fun_prop
    have h1 := (negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)).polynomiallyBounded_mul
      hp
    refine negligible_of_le h1 fun n => ?_
    rw [div_eq_mul_inv, ← inv_pow]
  refine negligible_of_le ((hprg_neg.add hexp_neg).add hnr_neg) fun n => ?_
  let need := expWidth n + (n * expWidth n + n * (2 * bound (desc n) + 1))
  have hneed_le : need ≤ targetLen n := by
    have ht := htarget n
    dsimp only [need]
    linarith
  have hreal_eq :
      ProbComp.eval (prfRealGame (F.naorReingoldSeededPRF desc bound expWidth expand)
        adversary n) =
      distinguishingGame (generatorEnsemble expand n) (D_tape n) := by
    simp only [prfRealGame, distinguishingGame, generatorEnsemble, ProbComp.eval_bind,
      ProbOracleComp.eval_interpret, ProbComp.eval_pure, BitString.eval_sampleList,
      PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, D_tape,
      eval_prfTapeDistinguisher]
    refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
    have hklen : key.length = n := BitString.length_of_mem_support_uniformList hkey
    congr 1; funext q
    cases q with
    | inl r => rfl
    | inr request =>
      dsimp only [ProbOracleComp.handler, prfOracle]
      by_cases hq : request.2.length = n
      · simp only [hq, ↓reduceIte, naorReingoldSeededPRF_eq_evalTape, hklen]
      · simp [hq]
  have hunif_trunc :
      distinguishingGame (BitString.uniformList (targetLen n)) (D_tape n) =
      (BitString.uniformList need).bind fun tape =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle fun request =>
            PMF.pure (if request.2.length = n then
              F.evalNaorReingoldTape id id desc bound expWidth n tape request.2
            else []))
          (adversary n []) := by
    rw [← BitString.uniformList_take hneed_le]
    simp only [distinguishingGame, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def,
      D_tape, eval_prfTapeDistinguisher]
    congr 1; funext x; congr 1; funext q
    cases q with
    | inl r => rfl
    | inr request =>
      dsimp only [ProbOracleComp.handler]
      rw [evalNaorReingoldTape_take F id id desc bound expWidth (limit := need) le_rfl]
  have hideal_eq :
      ProbComp.eval (prfIdealGame adversary n) =
      F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) id id bound
        (fun k _ => adversary k []) n := by
    rw [naorReingoldHashedIdealGame_pure_const]
    simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.eval_interpret, ProbComp.eval_pure, randomFunctionOracle, id_eq]
  dsimp only
  rw [hreal_eq, hideal_eq]
  have h12 := Game.advantage_triangle
    (distinguishingGame (generatorEnsemble expand n) (D_tape n))
    (distinguishingGame (BitString.uniformList (targetLen n)) (D_tape n))
    (F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) id id bound
      (fun k _ => adversary k []) n)
  have h23 := Game.advantage_triangle
    (distinguishingGame (BitString.uniformList (targetLen n)) (D_tape n))
    (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) id id bound
      (fun k _ => adversary k []) n)
    (F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) id id bound
      (fun k _ => adversary k []) n)
  have hexp_le :
      Game.advantage
        (distinguishingGame (BitString.uniformList (targetLen n)) (D_tape n))
        (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) id id bound
          (fun k _ => adversary k []) n) ≤
      ((n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    rw [hunif_trunc]
    exact advantage_evalNaorReingoldTape_uniform_le F id id desc bound expWidth adversary n
      (hexpWidth n)
  calc Game.advantage
        (distinguishingGame (generatorEnsemble expand n) (D_tape n))
        (F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) id id bound
          (fun k _ => adversary k []) n)
      ≤ Game.advantage
          (distinguishingGame (generatorEnsemble expand n) (D_tape n))
          (distinguishingGame (BitString.uniformList (targetLen n)) (D_tape n)) +
        (Game.advantage
          (distinguishingGame (BitString.uniformList (targetLen n)) (D_tape n))
          (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) id id bound
            (fun k _ => adversary k []) n) +
        Game.advantage
          (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) id id bound
            (fun k _ => adversary k []) n)
          (F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) id id bound
            (fun k _ => adversary k []) n)) :=
        h12.trans (add_le_add le_rfl h23)
    _ ≤ Game.advantage
          (distinguishingGame (generatorEnsemble expand n) (D_tape n))
          (distinguishingGame (BitString.uniformList (targetLen n)) (D_tape n)) +
        (((n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n +
        Game.advantage
          (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) id id bound
            (fun k _ => adversary k []) n)
          (F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) id id bound
            (fun k _ => adversary k []) n)) :=
        add_le_add le_rfl (add_le_add hexp_le le_rfl)
    _ = _ := by dsimp only [Pi.add_apply]; rw [add_assoc]

/-! ### Direct Algebraic `PseudorandomGenerator` from DDH Alone -/

private theorem sq_add_six_mul_add_seven_le_two_pow :
    ∀ s : ℕ, s * s + 6 * s + 7 ≤ 2 ^ (s + 4)
  | 0 => by norm_num
  | 1 => by norm_num
  | k + 2 => by
      have ih := sq_add_six_mul_add_seven_le_two_pow (k + 1)
      have hpow : 2 ^ (k + 2 + 4) = 2 * 2 ^ (k + 1 + 4) := by
        rw [show k + 2 + 4 = (k + 1 + 4) + 1 by omega, Nat.pow_succ']
      nlinarith

private theorem seedLen_succ_le_two_pow (e h : ℕ) :
    e + ((e + h + 4) * e + h) + 1 ≤ 2 ^ (e + h + 4) := by
  have h1 := sq_add_six_mul_add_seven_le_two_pow (e + h)
  have h2 : e + ((e + h + 4) * e + h) + 1 ≤ (e + h) * (e + h) + 6 * (e + h) + 7 := by nlinarith
  simpa only [Nat.add_assoc] using h2.trans h1

private def evalLowBitsHom (r M : ℕ) : (BitString r → BitString 1) →+ BitString M where
  toFun f j := f (BitString.ofList r (Cslib.BitString.lowBits r j.val)) ⟨0, Nat.zero_lt_one⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem lowBits_ofList_injective {r M : ℕ} (hM : M ≤ 2 ^ r) :
    Function.Injective (fun j : Fin M =>
      BitString.ofList r (Cslib.BitString.lowBits r j.val)) := by
  intro j j' h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < r
  · have hcongr := congrFun h ⟨i, hi⟩
    simpa only [BitString.ofList, Cslib.BitString.lowBits, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some] using hcongr
  · have hj : j.val < 2 ^ i :=
      lt_of_lt_of_le (lt_of_lt_of_le j.isLt hM)
        (Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi))
    have hj' : j'.val < 2 ^ i :=
      lt_of_lt_of_le (lt_of_lt_of_le j'.isLt hM)
        (Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi))
    rw [Nat.testBit_lt_two_pow hj, Nat.testBit_lt_two_pow hj']

private theorem uniformOfFintype_map_evalLowBitsHom {r M : ℕ} (hM : M ≤ 2 ^ r) :
    ((PMF.uniformOfFintype (BitString r → BitString 1)).map (evalLowBitsHom r M)).map List.ofFn =
      BitString.uniformList M := by
  classical
  have hhom :
      (PMF.uniformOfFintype (BitString r → BitString 1)).map (evalLowBitsHom r M) =
        PMF.uniformOfFintype (BitString M) := by
    refine PMF.uniformOfFintype_map_addHom _ fun φ => ?_
    let emb : Fin M → BitString r := fun j =>
      BitString.ofList r (Cslib.BitString.lowBits r j.val)
    have hemb : Function.Injective emb := lowBits_ofList_injective hM
    refine ⟨fun x _ => if h : ∃ j, emb j = x then φ h.choose else false, funext fun j => ?_⟩
    have hj : ∃ j', emb j' = emb j := ⟨j, rfl⟩
    change (if h : ∃ j', emb j' = emb j then φ h.choose else false) = φ j
    simp only [hj, dite_true]
    rw [hemb hj.choose_spec]
  rw [hhom]
  rfl

private theorem map_lowBits_randomFunction {r M : ℕ} (f : BitString r → BitString 1) :
    ((List.range M).map (Cslib.BitString.lowBits r)).map
      (fun word =>
        (if word.length = r then List.ofFn (f (BitString.ofList r word)) else []).headD false) =
      List.ofFn (evalLowBitsHom r M f) := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  have hi : i < M := by simpa using hi₂
  simp only [List.map_map, Function.comp_apply, List.getElem_map, List.getElem_range,
    Cslib.BitString.length_lowBits, ↓reduceIte, List.ofFn_succ, List.ofFn_zero, List.headD_cons,
    List.getElem_ofFn, evalLowBitsHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rfl

/-- **Existence of a uniform `PseudorandomGenerator` from DDH alone**: for any deterministic
polynomial-time prime-order group family `desc : ℕ → F.Desc` satisfying
`F.DDH (fun n => PMF.pure (desc n))`, evaluating 1-bit universal-hash Naor–Reingold at distinct
binary inputs and reindexing via `GeneratorReindex.pseudorandomGenerator` yields a uniform
`PseudorandomGenerator` with one-bit stretch at every seed length. -/
theorem DDH.exists_pseudorandomGenerator {F : PrimeOrderGroupFamily} {desc : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc) :
    ∃ generator : List Bool → List Bool, PseudorandomGenerator generator (fun n => n + 1) := by
  obtain ⟨cB, eB, hbound⟩ := F.exists_length_encode_le
  let bound : F.Desc → ℕ := fun d => cB * ((F.encDesc d).length + 1) ^ eB
  have hbound_poly : ComputableInPolyTime bound F.encDesc encUnary := by
    dsimp [bound]
    fun_prop
  let expWidth : ℕ → ℕ := fun n => (F.order (desc n)).size + n + 1
  let hashLen : ℕ → ℕ := fun n => 2 * bound (desc n) + 1
  let inBits : ℕ → ℕ := fun n => expWidth n + hashLen n + 4
  let seedLen : ℕ → ℕ := fun n => expWidth n + (inBits n * expWidth n + hashLen n)
  let core : ℕ → List Bool → List Bool := fun n seed =>
    (List.range (seedLen n + 1)).map fun i =>
      (F.evalNaorReingoldTape inBits (fun _ => 1) desc bound expWidth n seed
        (Cslib.BitString.lowBits (inBits n) i)).headD false
  have hexp_poly : ComputableInPolyTime expWidth encUnary encUnary :=
    ((ComputableInPolyTime.binary_size.comp (F.computableInPolyTime_order.comp hdesc)).unary_add'
      ComputableInPolyTime.id').unary_add' (ComputableInPolyTime.const 1)
  have hhash_poly : ComputableInPolyTime hashLen encUnary encUnary :=
    ((ComputableInPolyTime.const 2).unary_mul' (hbound_poly.comp hdesc)).unary_add'
      (ComputableInPolyTime.const 1)
  have hinBits_poly : ComputableInPolyTime inBits encUnary encUnary :=
    (hexp_poly.unary_add' hhash_poly).unary_add' (ComputableInPolyTime.const 4)
  have hseedLen_poly : ComputableInPolyTime seedLen encUnary encUnary :=
    hexp_poly.unary_add' ((hinBits_poly.unary_mul' hexp_poly).unary_add' hhash_poly)
  have hge : ∀ n, n + 1 ≤ seedLen n := by
    intro n
    dsimp only [seedLen, expWidth]
    omega
  have hcnt : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => seedLen p.1 + 1)
      (encPair encUnary encBits) encUnary :=
    ((hseedLen_poly.comp (ComputableInPolyTime.fst encUnary encBits)).unary_add'
      (ComputableInPolyTime.const 1)).tidy
  have hcore_poly : ComputableInPolyTime (fun p : ℕ × List Bool => core p.1 p.2)
      (encPair encUnary encBits) encBits := by
    have hrange : ComputableTidilyInPolyTime
        (fun p : ℕ × List Bool => List.range (seedLen p.1 + 1))
        (encPair encUnary encBits) (encList encUnary) :=
      ComputableTidilyInPolyTime.range.comp hcnt
    let ELoop := encPair (encPair encUnary encBits) encUnary
    have hfstL := ComputableTidilyInPolyTime.fst (encPair encUnary encBits) encUnary
    have hp1 : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ => q.1.1) ELoop encUnary :=
      .of_tidy ((ComputableTidilyInPolyTime.fst encUnary encBits).comp hfstL)
    have hp2 : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ => q.1.2) ELoop encBits :=
      .of_tidy ((ComputableTidilyInPolyTime.snd encUnary encBits).comp hfstL)
    have hq2 : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ => q.2) ELoop encNat :=
      .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp
        (ComputableTidilyInPolyTime.snd (encPair encUnary encBits) encUnary))
    have hstep_word : ComputableInPolyTime
        (fun q : (ℕ × List Bool) × ℕ =>
          F.evalNaorReingoldTape inBits (fun _ => 1) desc bound expWidth q.1.1 q.1.2
            (Cslib.BitString.lowBits (inBits q.1.1) q.2))
        ELoop encBits := by
      have hlow : ComputableInPolyTime
          (fun q : (ℕ × List Bool) × ℕ => Cslib.BitString.lowBits (inBits q.1.1) q.2)
          ELoop encBits :=
        ComputableInPolyTime.bitsLow (hinBits_poly.comp' hp1) hq2
      exact computableInPolyTime_evalNaorReingoldTape_of F
        hinBits_poly (ComputableInPolyTime.const 1) hdesc hbound_poly hexp_poly
        hp1 hp2 hlow
    have hbit : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool) × ℕ =>
          (F.evalNaorReingoldTape inBits (fun _ => 1) desc bound expWidth q.1.1 q.1.2
            (Cslib.BitString.lowBits (inBits q.1.1) q.2)).headD false)
        ELoop encBool :=
      (ComputableTidilyInPolyTime.headD (encA := encBool) (encL := encBits) false).comp
        hstep_word.tidy
    exact .of_tidy (ComputableTidilyInPolyTime.mapToBitsWithInput hrange hbit)
  have hcore_len : ∀ n seed, seed.length = seedLen n → (core n seed).length = seedLen n + 1 := by
    intro n seed _
    simp [core]
  have hsecure : ComputationallyIndistinguishable
      (fun n => (BitString.uniformList (seedLen n)).map (core n))
      (fun n => BitString.uniformList (seedLen n + 1)) := by
    intro D hD
    let queries : ℕ → List (List Bool) := fun n =>
      (List.range (seedLen n + 1)).map (Cslib.BitString.lowBits (inBits n))
    let adv : OracleDistinguisher := fun n _ => do
      let word ← KabanetsCai.queryTable (queries n)
      ProbOracleComp.sample (D n word)
    have hqueries : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => queries p.1)
        (encPair encUnary encBits) (encList encBits) :=
      ComputableTidilyInPolyTime.mapWithInput (ComputableTidilyInPolyTime.range.comp hcnt)
        (ComputableTidilyInPolyTime.bitsLow
          (hinBits_poly.tidy.comp
            ((ComputableTidilyInPolyTime.fst encUnary encBits).comp
              (ComputableTidilyInPolyTime.fst (encPair encUnary encBits) encUnary)))
          (ComputableTidilyInPolyTime.unary_to_binary.comp
            (ComputableTidilyInPolyTime.snd (encPair encUnary encBits) encUnary)))
    have hadv : IsOraclePPT encBool adv := by
      refine IsOraclePPTOn.isOraclePPT ?_
      exact (KabanetsCai.isOraclePPTOn_queryTable.preprocess hqueries).bind_with
        ((hD.preprocess
          ((ComputableTidilyInPolyTime.fst encUnary encBits).comp'
            (ComputableTidilyInPolyTime.fst (encPair encUnary encBits) encBits))
          (ComputableTidilyInPolyTime.snd (encPair encUnary encBits) encBits)).isOraclePPTOn)
    have hadv_aux : IsOraclePPT encBool (fun k (_ : List Bool) => adv k []) :=
      (hadv.on.preprocess
        ((ComputableTidilyInPolyTime.fst encUnary encBits).prod
          (ComputableTidilyInPolyTime.const []))).isOraclePPT
    obtain ⟨cD, eD, hdesc_b⟩ := hdesc.tidy.polyBounded_length.exists_le
    have hdesc_poly : PolynomiallyBounded (fun n => cD * (n + 1) ^ eD) := by fun_prop
    have hdesc_supp : ∀ n, ∀ d ∈ (PMF.pure (desc n)).support,
        (F.encDesc d).length ≤ cD * (n + 1) ^ eD := by
      intro n d hd
      rw [PMF.mem_support_pure_iff] at hd; subst hd
      simpa only [encUnary_apply, List.length_replicate] using hdesc_b n
    have hbound_supp : ∀ n, ∀ d ∈ (PMF.pure (desc n)).support, ∀ x : F.Carrier d,
        (F.encode d x).length ≤ bound d := by
      intro n d hd x
      rw [PMF.mem_support_pure_iff] at hd; subst hd
      exact hbound (desc n) x
    have hnr_neg := hDDH.negligible_naorReingoldHashedGame_const 1
      hinBits_poly hbound_poly hdesc_poly hdesc_supp hbound_supp hadv_aux
    have hinBits_polyB : PolynomiallyBounded inBits := hinBits_poly.tidy.polynomiallyBounded
    have hexp_neg : Negligible fun n => ((inBits n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
      have hp : PolynomiallyBounded (fun n => inBits n + 1) := by fun_prop
      have h1 :=
        (negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)).polynomiallyBounded_mul hp
      refine negligible_of_le h1 fun n => ?_
      rw [div_eq_mul_inv, ← inv_pow]
    refine negligible_of_le (hexp_neg.add hnr_neg) fun n => ?_
    have hinterp (oracle : List Bool → List Bool) :
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle fun request => PMF.pure (oracle request.2))
          (adv n []) =
        ProbComp.eval (D n ((queries n).map fun word => (oracle word).headD false)) := by
      change OracleComp.interpret
        (ProbOracleComp.handler ProbComp.unifOracle fun request => pure (oracle request.2))
        (KabanetsCai.queryTable (queries n) >>= fun word => ProbOracleComp.sample (D n word)) = _
      rw [OracleComp.interpret_bind,
        KabanetsCai.interpret_queryTable ProbComp.unifOracle oracle (queries n),
        pure_bind, ProbOracleComp.interpret_sample]
      rfl
    have hreal_eq :
        distinguishingGame ((BitString.uniformList (seedLen n)).map (core n)) (D n) =
        (BitString.uniformList
          (expWidth n + (inBits n * expWidth n + 1 * (2 * bound (desc n) + 1)))).bind fun tape =>
            OracleComp.interpret
              (ProbOracleComp.handler ProbComp.unifOracle fun request =>
                PMF.pure (if request.2.length = inBits n then
                  F.evalNaorReingoldTape inBits (fun _ => 1) desc bound expWidth n tape request.2
                else []))
              (adv n []) := by
      have hsl : seedLen n =
          expWidth n + (inBits n * expWidth n + 1 * (2 * bound (desc n) + 1)) := by
        simp [seedLen, hashLen]
      rw [hsl]
      simp only [distinguishingGame, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
      congr 1; funext tape
      rw [hinterp (fun q =>
        if q.length = inBits n then
          F.evalNaorReingoldTape inBits (fun _ => 1) desc bound expWidth n tape q
        else [])]
      congr 2
      simp [core, queries, List.map_map, Function.comp_def, Cslib.BitString.length_lowBits]
    have hideal_eq :
        distinguishingGame (BitString.uniformList (seedLen n + 1)) (D n) =
        F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) inBits (fun _ => 1) bound
          (fun k _ => adv k []) n := by
      rw [naorReingoldHashedIdealGame_pure_const]
      have hfit : seedLen n + 1 ≤ 2 ^ (inBits n) := by
        simpa only [seedLen, inBits] using seedLen_succ_le_two_pow (expWidth n) (hashLen n)
      rw [← uniformOfFintype_map_evalLowBitsHom hfit]
      simp only [distinguishingGame, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
      congr 1; funext f
      rw [hinterp (fun q =>
        if q.length = inBits n then List.ofFn (f (BitString.ofList (inBits n) q)) else [])]
      congr 2
      exact (map_lowBits_randomFunction f).symm
    dsimp only
    rw [hreal_eq, hideal_eq]
    refine (Game.advantage_triangle _
      (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) inBits (fun _ => 1) bound
        (fun k _ => adv k []) n) _).trans (add_le_add ?_ le_rfl)
    exact advantage_evalNaorReingoldTape_uniform_le F inBits (fun _ => 1) desc bound expWidth adv n
      (by dsimp only [expWidth]; omega)
  exact ⟨GeneratorReindex.generate seedLen core,
    GeneratorReindex.pseudorandomGenerator hseedLen_poly hge hcore_poly hcore_len hsecure⟩

/-- **Existence of an explicit Naor–Reingold `PseudorandomFunction` from DDH**: for any
deterministic polynomial-time prime-order group family `desc : ℕ → F.Desc` satisfying
`F.DDH (fun n => PMF.pure (desc n))` with `2 ^ n / F.order (desc n)` negligible, there exist
polynomial-time parameters `bound`, `expWidth`, and `expand` such that
`F.naorReingoldSeededPRF desc bound expWidth expand` is a uniform `PseudorandomFunction`. -/
theorem DDH.exists_naorReingoldPseudorandomFunction {F : PrimeOrderGroupFamily}
    {desc : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ n / (F.order (desc n) : ℝ≥0)) :
    ∃ (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ) (expand : List Bool → List Bool),
      PseudorandomFunction (F.naorReingoldSeededPRF desc bound expWidth expand) := by
  obtain ⟨cB, eB, hbound⟩ := F.exists_length_encode_le
  let bound : F.Desc → ℕ := fun d => cB * ((F.encDesc d).length + 1) ^ eB
  have hbound_poly : ComputableInPolyTime bound F.encDesc encUnary := by
    dsimp [bound]
    fun_prop
  obtain ⟨G, hG⟩ := hDDH.exists_pseudorandomGenerator hdesc
  let expWidth : ℕ → ℕ := fun n => (F.order (desc n)).size + n + 1
  let targetLen : ℕ → ℕ := fun n => (n + 1) * expWidth n + n * (2 * bound (desc n) + 1)
  have hexp_poly : ComputableInPolyTime expWidth encUnary encUnary :=
    ((ComputableInPolyTime.binary_size.comp (F.computableInPolyTime_order.comp hdesc)).unary_add'
      ComputableInPolyTime.id').unary_add' (ComputableInPolyTime.const 1)
  have hhash_poly : ComputableInPolyTime (fun n => 2 * bound (desc n) + 1) encUnary encUnary :=
    ((ComputableInPolyTime.const 2).unary_mul' (hbound_poly.comp hdesc)).unary_add'
      (ComputableInPolyTime.const 1)
  have htarget_poly : ComputableInPolyTime targetLen encUnary encUnary :=
    ((ComputableInPolyTime.id'.unary_add' (ComputableInPolyTime.const 1)).unary_mul'
      hexp_poly).unary_add' (ComputableInPolyTime.id'.unary_mul' hhash_poly)
  have hstretch : ∀ n, n < targetLen n := by
    intro n
    dsimp only [targetLen, expWidth]
    nlinarith
  have hexpand := hG.amplify targetLen htarget_poly hstretch
  exact ⟨bound, expWidth, _,
    hDDH.pseudorandomFunction_naorReingoldSeeded hdesc hbound_poly (fun n => hbound (desc n))
      hexp_poly (fun n => by dsimp only [expWidth]; omega) hexpand (fun _ => le_rfl) hneg⟩

/-- **Existence of a uniform `PseudorandomFunction` from DDH alone**: any deterministic
polynomial-time prime-order group family `desc : ℕ → F.Desc` satisfying
`F.DDH (fun n => PMF.pure (desc n))` yields a uniform `PseudorandomFunction` by combining the
1-bit-stretch Naor–Reingold generator `DDH.exists_pseudorandomGenerator` with the
Goldreich–Goldwasser–Micali tree construction `PseudorandomGenerator.exists_pseudorandomFunction`
([GGM1986]). For the direct Naor–Reingold PRF family under `Negligible (2 ^ n / F.order (desc n))`,
see `DDH.exists_naorReingoldPseudorandomFunction`. -/
theorem DDH.exists_pseudorandomFunction {F : PrimeOrderGroupFamily} {desc : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc) :
    ∃ family : List Bool → List Bool → List Bool, PseudorandomFunction family := by
  obtain ⟨G, hG⟩ := hDDH.exists_pseudorandomGenerator hdesc
  exact hG.exists_pseudorandomFunction

end PrimeOrderGroupFamily

end Cslib.Crypto
