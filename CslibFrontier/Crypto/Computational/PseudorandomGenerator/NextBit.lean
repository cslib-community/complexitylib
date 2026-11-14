/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Negligible.Basic
public import CslibFrontier.Probability.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.HiddenBit
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Crypto.Primitives.PRG.Game
import CslibFrontier.Crypto.Primitives.PRG.NextBit
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.Product.Split
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Yao's next-bit theorem for uniform pseudorandom generators

`CslibFrontier/Crypto/Primitives/PRG/NextBit.lean` establishes the finite equivalence between
pseudorandomness and next-bit unpredictability for caller-supplied admissibility predicates and
closure hypotheses. This module lifts that argument to uniform strict-PPT `PseudorandomGenerator`s
over arbitrary bit strings without closure hypotheses or non-uniform advice.

Two standard uniform next-bit formulations are covered and proved equivalent to
`PseudorandomGenerator`:

1. **Random-index prediction (`NextBitUnpredictableRandomIndex`)**: a single-stage `Distinguisher`
   receives the security parameter `1ⁿ` and a prefix `(G s).take i` for a uniformly sampled bit
   index `i < length n`, and attempts to guess `(G s)[i]`. Note that `(G s).take i` has length `i`,
   so the predictor observes the index from the prefix itself.
2. **Adversary-chosen index (`NextBitUnpredictable`, Boneh–Shoup Attack Game 3.2)**: a two-stage
   adversary `TwoStage Unit ℕ (List Bool) Bool σ` first chooses an index `i` (with saved state `σ`)
   and then, given a prefix `(G s).take i` of the generated word, attempts to guess `(G s)[i]`; if
   `length n ≤ i`, the challenger outputs a fair coin so out-of-range guesses yield zero advantage.

Both reductions (`wordNextBitPredictor` / `wordNextBitTwoStage` and `nextBitDistinguisher` /
`twoStageNextBitDistinguisher`) are unconditionally certified in strict polynomial time, reusing
`PRG.polyTime_length`, `ProbComp.sampleDyadicIndex` (`isPPTOn_sampleDyadicIndex`) for padded
uniform index sampling, and the finite hybrid/predictor theorem
`PRG.Generator.toReal_predictionExperiment_nextBitPredictor` from
`CslibFrontier/Crypto/Primitives/PRG/NextBit.lean`.

## Main definitions

* `Cslib.Crypto.nextBitPredictionGame`: random-index next-bit game for a single-stage predictor.
* `Cslib.Crypto.NextBitUnpredictableRandomIndex`: uniform PPT unpredictability at a random bit.
* `Cslib.Crypto.wordNextBitPredictor`: uniform PPT next-bit predictor built from a PRG
  distinguisher, padding suffix bits uniformly.
* `Cslib.Crypto.nextBitDistinguisher`: uniform PPT PRG distinguisher built from a random-index
  predictor via `ProbComp.sampleDyadicIndex`.
* `Cslib.Crypto.nextBitExperiment`: Boneh–Shoup Attack Game 3.2 for two-stage predictors.
* `Cslib.Crypto.NextBitUnpredictable`: uniform PPT unpredictability against two-stage predictors.
* `Cslib.Crypto.wordNextBitTwoStage`, `Cslib.Crypto.twoStageNextBitDistinguisher`: uniform strict
  PPT two-stage reductions in both directions.

## Main results

* `Cslib.Crypto.isPPT_wordNextBitPredictor`, `Cslib.Crypto.isPPT_nextBitDistinguisher`,
  `Cslib.Crypto.isPPT_wordNextBitTwoStage`, `Cslib.Crypto.isPPT_twoStageNextBitDistinguisher`:
  unconditional uniform strict-PPT certificates for all four reductions.
* `Cslib.Crypto.guessingAdvantage_nextBitPredictionGame_wordNextBitPredictor`,
  `Cslib.Crypto.advantage_nextBitDistinguisher_eq`,
  `Cslib.Crypto.guessingAdvantage_nextBitExperiment_wordNextBitTwoStage`,
  `Cslib.Crypto.guessingAdvantage_nextBitExperiment_eq`: exact concrete advantage relations.
* `Cslib.Crypto.pseudorandomGenerator_iff_nextBitUnpredictableRandomIndex`,
  `Cslib.Crypto.pseudorandomGenerator_iff_nextBitUnpredictable`: Yao's next-bit equivalence theorem
  in both the random-index and two-stage Attack Game 3.2 formulations.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 3.5 (Attack Game 3.2, Theorems 3.4 and 3.6).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 8.1.3 (Theorem 8.10).
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.2.3.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Uniformity, binary-splitting, and padded-average helpers -/

private theorem getD_eq_headD_drop (l : List Bool) (i : ℕ) (d : Bool) :
    l.getD i d = (l.drop i).headD d := by
  rw [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

private theorem uniformList_bind_take_getD {α : Type*} (m i : ℕ) (hi : i < m)
    (k : List Bool → Bool → PMF α) :
    (BitString.uniformList m).bind (fun word => k (word.take i) (word.getD i false)) =
      (BitString.uniformList i).bind fun front =>
        (PMF.uniformOfFintype Bool).bind fun bit => k front bit := by
  have hm : m = i + ((m - (i + 1)) + 1) := by omega
  simp_rw [getD_eq_headD_drop]
  rw [hm]
  simpa only using (BitString.uniformList_bind_split i ((m - (i + 1)) + 1)
    (fun front back => k front (back.headD false))).trans (by
      refine congrArg _ (funext fun front => ?_)
      rw [BitString.uniformList_succ, PMF.bind_bind]
      refine congrArg _ (funext fun bit => ?_)
      rw [PMF.bind_map]
      simp only [Function.comp_def, List.headD_cons, PMF.bind_const])

private theorem uniformList_bind_take_getD_eq_uniform_bool {m i : ℕ} (hi : i < m)
    (f : List Bool → PMF Bool) :
    (BitString.uniformList m).bind
        (fun word => (f (word.take i)).map fun guess => decide (guess = word.getD i false)) =
      PMF.uniformOfFintype Bool := by
  rw [uniformList_bind_take_getD m i hi
    (fun front bit => (f front).map fun guess => decide (guess = bit))]
  refine (congrArg _ (funext fun front => ?_)).trans (PMF.bind_const _ _)
  simpa only [show ∀ a b : Bool, decide (a = b) = (a == b) by decide] using
    Game.uniform_bool_bind_map_beq_const (f front)

private theorem uniformList_map_suffix_eq_uniformOfFintype {m : ℕ} (i : Fin m)
    (x : Fin i → Bool) (r : Bool) :
    (BitString.uniformList (m - (i.val + 1))).map (fun suffix => List.ofFn x ++ r :: suffix) =
      (PMF.uniformOfFintype (Fin m → Bool)).map fun z =>
        List.ofFn fun j : Fin m =>
          if h : (j : ℕ) < i then x ⟨j, h⟩ else if j = i then r else z j := by
  let g : Fin (m - (i.val + 1)) → Fin m := fun k => ⟨i.val + 1 + k.val, by omega⟩
  have hg : Function.Injective g := fun a b hab => Fin.ext (by
    have := congrArg Fin.val hab
    dsimp [g] at this
    omega)
  have hmap :
      (PMF.uniformOfFintype (Fin m → Bool)).map (fun z k => z (g k)) =
        PMF.uniformOfFintype (Fin (m - (i.val + 1)) → Bool) := by
    simpa only using PMF.uniformOfFintype_map_comp_dep (R := fun _ => Bool) hg
  have hlist (z : Fin m → Bool) :
      List.ofFn (fun j : Fin m =>
        if h : (j : ℕ) < i then x ⟨j, h⟩ else if j = i then r else z j) =
        List.ofFn x ++ r :: List.ofFn (fun k : Fin (m - (i.val + 1)) => z (g k)) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append, List.length_cons]
      omega
    · intro k hk₁ hk₂
      simp only [List.getElem_ofFn]
      by_cases hlt : k < i.val
      · simp only [hlt, ↓reduceDIte]
        rw [List.getElem_append_left (by simp [hlt]), List.getElem_ofFn]
      · have hge : (List.ofFn x).length ≤ k := by simp; omega
        rw [List.getElem_append_right hge]
        simp only [List.length_ofFn]
        by_cases heq : k = i.val
        · have hj : (⟨k, by simpa using hk₁⟩ : Fin m) = i := Fin.ext heq
          simp only [heq, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte, Nat.sub_self,
            List.getElem_cons_zero]
        · have hjne : (⟨k, by simpa using hk₁⟩ : Fin m) ≠ i := fun h => heq (congrArg Fin.val h)
          have hpos : k - i.val = (k - (i.val + 1)) + 1 := by omega
          simp only [hlt, ↓reduceDIte, hjne, ↓reduceIte, hpos, List.getElem_cons_succ,
            List.getElem_ofFn, g]
          congr 2
          omega
  calc
    (BitString.uniformList (m - (i.val + 1))).map (fun suffix => List.ofFn x ++ r :: suffix)
        = (PMF.uniformOfFintype (Fin (m - (i.val + 1)) → Bool)).map
            (fun suffix => List.ofFn x ++ r :: List.ofFn suffix) := by
          simp only [BitString.uniformList, PMF.map_comp, Function.comp_def]
    _ = ((PMF.uniformOfFintype (Fin m → Bool)).map (fun z k => z (g k))).map
            (fun suffix => List.ofFn x ++ r :: List.ofFn suffix) := by rw [hmap]
    _ = (PMF.uniformOfFintype (Fin m → Bool)).map fun z =>
            List.ofFn x ++ r :: List.ofFn (fun k => z (g k)) := PMF.map_comp _ _ _
    _ = _ := by
          congr 1 with z : 1
          exact (hlist z).symm

private theorem succProbability_uniformOfFintype_bool :
    (Game.succProbability (PMF.uniformOfFintype Bool) : ℝ) = 1 / 2 := by
  simp [Game.succProbability, ENNReal.toNNReal_ofNat]

private theorem guessingAdvantage_uniform_ite_fin {L D : ℕ} (games : Fin L → Game) [NeZero D]
    (hLD : L ≤ D) :
    (Game.guessingAdvantage
      ((PMF.uniformOfFintype (Fin D)).bind fun i =>
        if hi : i.val < L then games ⟨i.val, hi⟩ else PMF.uniformOfFintype Bool) : ℝ) =
      |∑ i : Fin L, ((Game.succProbability (games i) : ℝ) - 1 / 2)| / D := by
  let g : ℕ → ℝ := fun i =>
    if hi : i < L then (Game.succProbability (games ⟨i, hi⟩) : ℝ) - 1 / 2 else 0
  have hsum_eq :
      ∑ i : Fin D,
          (Game.succProbability (if hi : i.val < L then games ⟨i.val, hi⟩ else
            PMF.uniformOfFintype Bool) : ℝ) =
        ∑ i : Fin D, (1 / 2 + g i.val) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < L
    · simp only [hi, ↓reduceDIte, g]
      ring
    · simp only [hi, ↓reduceDIte, succProbability_uniformOfFintype_bool, g]
      ring
  have hsum_range : ∑ i ∈ Finset.range L, g i =
      ∑ i : Fin L, ((Game.succProbability (games i) : ℝ) - 1 / 2) := by
    have hL : ∑ i : Fin L, ((Game.succProbability (games i) : ℝ) - 1 / 2) =
        ∑ i : Fin L, g i.val := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [g, i.isLt]
    rw [hL, Fin.sum_univ_eq_sum_range]
  have hsum_g :
      ∑ i : Fin D, g i.val = ∑ i : Fin L, ((Game.succProbability (games i) : ℝ) - 1 / 2) := by
    rw [Fin.sum_univ_eq_sum_range g D, ← Finset.sum_range_add_sum_Ico _ hLD]
    have hhi : ∑ i ∈ Finset.Ico L D, g i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hge : ¬ i < L := by
        rw [Finset.mem_Ico] at hi
        omega
      simp only [g, hge, ↓reduceDIte]
    rw [hhi, add_zero, hsum_range]
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr (NeZero.pos D)
  rw [Game.coe_guessingAdvantage, Game.succProbability_uniform, NNReal.coe_div, NNReal.coe_sum,
    NNReal.coe_natCast, Fintype.card_fin, hsum_eq, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum_g]
  rw [show (D * (1 / 2 : ℝ) + ∑ i : Fin L, ((Game.succProbability (games i) : ℝ) - 1 / 2)) / D -
      1 / 2 =
      (∑ i : Fin L, ((Game.succProbability (games i) : ℝ) - 1 / 2)) / D by field_simp; ring,
    abs_div, abs_of_pos hDpos]

/-! ### Polynomial-time and PPT helper certificates -/

private theorem computableInPolyTime_length_take_lt {length : ℕ → ℕ}
    (hl : ComputableInPolyTime length encUnary encUnary) :
    ComputableInPolyTime (fun p : ℕ × List Bool => decide (p.2.length < length p.1))
      (encPair encUnary encBits) encBool := by
  have h1 : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.length)
      (encPair encUnary encBits) encUnary :=
    ComputableInPolyTime.length_bits_comp (ComputableInPolyTime.snd encUnary encBits)
  have h2 : ComputableInPolyTime (fun p : ℕ × List Bool => length p.1)
      (encPair encUnary encBits) encUnary :=
    hl.comp (ComputableInPolyTime.fst encUnary encBits)
  exact ComputableInPolyTime.unary_lt.comp (h1.prod h2)

private theorem computableInPolyTime_suffixLen {length : ℕ → ℕ}
    (hl : ComputableInPolyTime length encUnary encUnary) :
    ComputableInPolyTime
      (fun q : (ℕ × List Bool) × Bool => length q.1.1 - (q.1.2.length + 1))
      (encPair (encPair encUnary encBits) encBool) encUnary := by
  have hfst : ComputableInPolyTime (fun q : (ℕ × List Bool) × Bool => q.1)
      (encPair (encPair encUnary encBits) encBool) (encPair encUnary encBits) :=
    ComputableInPolyTime.fst _ _
  have hl1 : ComputableInPolyTime (fun q : (ℕ × List Bool) × Bool => length q.1.1)
      (encPair (encPair encUnary encBits) encBool) encUnary :=
    hl.comp ((ComputableInPolyTime.fst encUnary encBits).comp hfst)
  have hpref : ComputableInPolyTime (fun q : (ℕ × List Bool) × Bool => q.1.2.length)
      (encPair (encPair encUnary encBits) encBool) encUnary :=
    ComputableInPolyTime.length_bits_comp
      ((ComputableInPolyTime.snd encUnary encBits).comp hfst)
  have hplus1 : ComputableInPolyTime (fun q : (ℕ × List Bool) × Bool => q.1.2.length + 1)
      (encPair (encPair encUnary encBits) encBool) encUnary :=
    ComputableInPolyTime.unary_succ.comp hpref
  exact ComputableInPolyTime.unary_sub' hl1 hplus1

private theorem computableInPolyTime_two_mul_length_poly {length : ℕ → ℕ}
    (hl : ComputableInPolyTime length encUnary encUnary) :
    PolynomiallyBounded (fun n => dyadicSize (length n - 1)) := by
  refine polynomiallyBounded_iff_le.mpr ?_
  obtain ⟨c, d, hc⟩ := polynomiallyBounded_iff_le.mp hl.polynomiallyBounded
  refine ⟨2 * c + 2, d, fun n => ?_⟩
  have h1 := Probability.dyadicSize_le (length n - 1)
  have h2 : length n - 1 + 1 ≤ c * (n + 1) ^ d + 1 :=
    Nat.add_le_add_right ((Nat.sub_le _ 1).trans (hc n)) 1
  have h3 : c * (n + 1) ^ d + 1 ≤ (c + 1) * (n + 1) ^ d := by
    have hpow : 1 ≤ (n + 1) ^ d := Nat.one_le_pow d _ (Nat.succ_pos n)
    nlinarith
  nlinarith

private theorem computableInPolyTime_decide_eq_getD {γ : Type} {encγ : γ ↪ List Bool}
    {wordOf : γ → List Bool} {idxOf : γ → ℕ}
    (hword : ComputableInPolyTime wordOf encγ encBits)
    (hidx : ComputableInPolyTime idxOf encγ encUnary) :
    ComputableInPolyTime
      (fun r : γ × Bool => decide (r.2 = (wordOf r.1).getD (idxOf r.1) false))
      (encPair encγ encBool) encBool :=
  .of_tidy ((ComputableTidilyInPolyTime.snd encγ encBool).decide_eq'
    (ComputableInPolyTime.bitsGetDWithInput
      (hword.comp (ComputableInPolyTime.fst encγ encBool))
      (hidx.comp (ComputableInPolyTime.fst encγ encBool)) false).tidy)

/-! ### Section 1: Random-Index Next-Bit Prediction -/

/-- Random-index next-bit prediction game: draw a uniform `n`-bit seed `s`, set `word :=
generator s`, draw a uniform bit position `i < length n`, run `predictor n (word.take i)`, and
accept when the guess matches bit `i` of `word`. If `length n = 0`, output a fair coin. -/
@[expose] noncomputable def nextBitPredictionGame (generator : List Bool → List Bool)
    (length : ℕ → ℕ) (predictor : Distinguisher) (n : ℕ) : Game :=
  if hl : 0 < length n then
    have : Nonempty (Fin (length n)) := ⟨⟨0, hl⟩⟩
    do
      let seed ← BitString.uniformList n
      let word := generator seed
      let i ← PMF.uniformOfFintype (Fin (length n))
      let guess ← ProbComp.eval (predictor n (word.take i.val))
      return decide (guess = word.getD i.val false)
  else
    PMF.uniformOfFintype Bool

/-- Uniform strict-PPT next-bit unpredictability at a random bit position: every uniform strict PPT
predictor `Distinguisher` has negligible guessing advantage in `nextBitPredictionGame`. -/
@[expose] def NextBitUnpredictableRandomIndex (generator : List Bool → List Bool)
    (length : ℕ → ℕ) : Prop :=
  ∀ predictor : Distinguisher, IsPPT encBool predictor →
    Negligible (fun n =>
      Game.guessingAdvantage (nextBitPredictionGame generator length predictor n))

/-- The uniform strict-PPT next-bit predictor constructed from a PRG distinguisher `adversary`:
given `(n, prefixBits)` with `prefixBits.length < length n`, sample a candidate bit `candidate`
and uniform suffix `suffix ← BitString.sampleList (length n - (prefixBits.length + 1))`, run
`adversary n (prefixBits ++ candidate :: suffix)`, and output `candidate` if it accepts or
`!candidate` if it rejects. -/
noncomputable def wordNextBitPredictor (length : ℕ → ℕ)
    (adversary : Distinguisher) : Distinguisher := fun n prefixBits => do
  if prefixBits.length < length n then
    let candidate ← ProbComp.uniform Bool
    let suffix ← BitString.sampleList (length n - (prefixBits.length + 1))
    let accept ← adversary n (prefixBits ++ candidate :: suffix)
    return if accept then candidate else !candidate
  else
    ProbComp.uniform Bool

/-- `wordNextBitPredictor length adversary` is uniformly strict PPT whenever `length` is unary
polynomial-time computable and `adversary` is uniformly strict PPT. -/
@[program_certificate]
theorem isPPT_wordNextBitPredictor {length : ℕ → ℕ} {adversary : Distinguisher}
    (hl : ComputableInPolyTime length encUnary encUnary) (ha : IsPPT encBool adversary) :
    IsPPT encBool (wordNextBitPredictor length adversary) := by
  have hcond := computableInPolyTime_length_take_lt hl
  have hcand : IsPPTOn (encPair encUnary encBits) encBool (fun _ => ProbComp.uniform Bool) :=
    isPPTOn_uniform_bool _
  have hsuf : IsPPTOn (encPair (encPair encUnary encBits) encBool) encBits
      (fun q => BitString.sampleList (length q.1.1 - (q.1.2.length + 1))) :=
    isPPTOn_sampleList.preprocess (computableInPolyTime_suffixLen hl)
  have hword : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × Bool) × List Bool => r.1.1.2 ++ r.1.2 :: r.2)
      (encPair (encPair (encPair encUnary encBits) encBool) encBits) encBits := by
    have hpref : ComputableInPolyTime
        (fun r : ((ℕ × List Bool) × Bool) × List Bool => r.1.1.2)
        (encPair (encPair (encPair encUnary encBits) encBool) encBits) encBits := by fun_prop
    have hc : ComputableInPolyTime
        (fun r : ((ℕ × List Bool) × Bool) × List Bool => r.1.2)
        (encPair (encPair (encPair encUnary encBits) encBool) encBits) encBool := by fun_prop
    have hs : ComputableInPolyTime
        (fun r : ((ℕ × List Bool) × Bool) × List Bool => r.2)
        (encPair (encPair (encPair encUnary encBits) encBool) encBits) encBits := by fun_prop
    have hbitlist : ComputableInPolyTime
        (fun r : ((ℕ × List Bool) × Bool) × List Bool => [r.1.2])
        (encPair (encPair (encPair encUnary encBits) encBool) encBits) encBits :=
      ComputableInPolyTime.bitsCons hc (ComputableInPolyTime.const [])
    exact ComputableInPolyTime.bitsAppend hpref (ComputableInPolyTime.bitsAppend hbitlist hs)
  have hn : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × Bool) × List Bool => r.1.1.1)
      (encPair (encPair (encPair encUnary encBits) encBool) encBits) encUnary := by fun_prop
  have hadv : IsPPTOn (encPair (encPair (encPair encUnary encBits) encBool) encBits) encBool
      (fun r => adversary r.1.1.1 (r.1.1.2 ++ r.1.2 :: r.2)) :=
    ha.on.preprocess (hn.prod hword)
  have hret : ComputableInPolyTime
      (fun s : (((ℕ × List Bool) × Bool) × List Bool) × Bool =>
        if s.2 then s.1.1.2 else !s.1.1.2)
      (encPair (encPair (encPair (encPair encUnary encBits) encBool) encBits) encBool) encBool := by
    fun_prop
  have hthen : IsPPTOn (encPair encUnary encBits) encBool (fun p => do
      let candidate ← ProbComp.uniform Bool
      let suffix ← BitString.sampleList (length p.1 - (p.2.length + 1))
      (fun accept => if accept then candidate else !candidate) <$>
        adversary p.1 (p.2 ++ candidate :: suffix)) :=
    hcand.bind_with (hsuf.bind_with (hadv.map_with hret))
  have helse : IsPPTOn (encPair encUnary encBits) encBool (fun _ => ProbComp.uniform Bool) :=
    isPPTOn_uniform_bool _
  change IsPPTOn (encPair encUnary encBits) encBool
    (fun p => wordNextBitPredictor length adversary p.1 p.2)
  simpa only [wordNextBitPredictor, bind_pure_comp] using IsPPTOn.ite hcond.tidy hthen helse

private theorem eval_wordNextBitPredictor_ofFn {length : ℕ → ℕ}
    (adversary : Distinguisher) {n : ℕ} (i : Fin (length n)) (x : Fin i → Bool) :
    ProbComp.eval (wordNextBitPredictor length adversary n (List.ofFn x)) =
      PRG.nextBitPredictor (fun bits : BitString (length n) =>
        ProbComp.eval (adversary n (List.ofFn bits))) i x := by
  unfold wordNextBitPredictor
  simp only [List.length_ofFn, i.isLt, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_uniform,
    BitString.eval_sampleList, ProbComp.eval_pure, PRG.nextBitPredictor, PRG.guessOfDistinguisher,
    PMF.monad_bind_eq_bind]
  refine congrArg _ (funext fun r => ?_)
  have hmap := uniformList_map_suffix_eq_uniformOfFintype i x r
  have hstep :
      (BitString.uniformList (length n - (i.val + 1))).bind (fun suffix =>
          (ProbComp.eval (adversary n (List.ofFn x ++ r :: suffix))).bind fun a =>
            PMF.pure (if a = true then r else !r)) =
        ((BitString.uniformList (length n - (i.val + 1))).map
            (fun suffix => List.ofFn x ++ r :: suffix)).bind
          (fun w => (ProbComp.eval (adversary n w)).map fun a => if a = true then r else !r) := by
    rw [PMF.bind_map]
    refine congrArg _ (funext fun suffix => ?_)
    exact (PMF.bind_pure_comp _ _).symm
  rw [hstep, hmap, PMF.bind_map]
  simp only [Function.comp_def, PMF.map_bind]

private noncomputable def wordNextBitStepGame (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (adversary : Distinguisher) (n : ℕ) (i : Fin (length n)) : Game :=
  (BitString.uniformList n).bind fun seed =>
    let word := generator seed
    (ProbComp.eval (wordNextBitPredictor length adversary n (word.take i.val))).map
      fun guess => decide (guess = word.getD i.val false)

private theorem eval_wordNextBitStepGame {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ word, (generator word).length = length word.length)
    (adversary : Distinguisher) {n : ℕ} (i : Fin (length n)) :
    wordNextBitStepGame generator length adversary n i =
      (PRG.wordFamily generator length n).predictionExperiment i
        (PRG.nextBitPredictor
          (fun bits : BitString (length n) => ProbComp.eval (adversary n (List.ofFn bits))) i) := by
  have heq :
      wordNextBitStepGame generator length adversary n i =
        (generatorEnsemble generator n).bind fun word =>
          (ProbComp.eval (wordNextBitPredictor length adversary n (word.take i.val))).map
            fun guess => decide (guess = word.getD i.val false) := by
    simp only [wordNextBitStepGame, generatorEnsemble, PMF.bind_map]
    rfl
  rw [heq, generatorEnsemble_eq_outputDist hlen, PRG.Generator.predictionExperiment, PMF.bind_map]
  refine congrArg _ (funext fun y : BitString (length n) => ?_)
  have htake : (List.ofFn y).take i.val = List.ofFn (Fin.take i i.isLt.le y) := by
    apply List.ext_getElem
    · simp
    · intro k hk₁ hk₂
      simp [Fin.take]
  have hget : (List.ofFn y).getD i.val false = y i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [i.isLt]
  dsimp only [Function.comp_apply]
  rw [htake, hget, eval_wordNextBitPredictor_ofFn]
  rfl

private theorem succProbability_wordNextBitStepGame_toReal
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ word, (generator word).length = length word.length)
    (adversary : Distinguisher) {n : ℕ} (i : Fin (length n)) :
    (Game.succProbability (wordNextBitStepGame generator length adversary n i) : ℝ) =
      1 / 2 + (PRG.wordFamily generator length n).hybridGap
        (fun bits : BitString (length n) => ProbComp.eval (adversary n (List.ofFn bits))) i := by
  rw [eval_wordNextBitStepGame hlen adversary i, Game.coe_succProbability]
  exact (PRG.wordFamily generator length n).toReal_predictionExperiment_nextBitPredictor
    (fun bits : BitString (length n) => ProbComp.eval (adversary n (List.ofFn bits))) i

private theorem sum_wordNextBitStepGame_sub_half
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ word, (generator word).length = length word.length)
    (adversary : Distinguisher) (n : ℕ) :
    |∑ i : Fin (length n),
        ((Game.succProbability (wordNextBitStepGame generator length adversary n i) : ℝ) -
          1 / 2)| =
      (Game.advantage (ProbComp.eval (prgRealGame generator adversary n))
        (ProbComp.eval (prgIdealGame length adversary n)) : ℝ) := by
  have hterm (i : Fin (length n)) :
      (Game.succProbability (wordNextBitStepGame generator length adversary n i) : ℝ) - 1 / 2 =
        (PRG.wordFamily generator length n).hybridGap
          (fun bits : BitString (length n) => ProbComp.eval (adversary n (List.ofFn bits))) i := by
    rw [succProbability_wordNextBitStepGame_toReal hlen adversary i, add_sub_cancel_left]
  simp_rw [hterm, PRG.Generator.sum_hybridGap, PRG.wordFamily_realExperiment hlen,
    PRG.wordFamily_idealExperiment, ← eval_prgRealGame, ← eval_prgIdealGame, Game.coe_advantage,
    Game.coe_succProbability]

/-- Exact quantitative advantage of `wordNextBitPredictor`: when `0 < length n`, the random-index
prediction advantage is `1 / length n` times the distinguisher's PRG advantage. -/
theorem guessingAdvantage_nextBitPredictionGame_wordNextBitPredictor
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ word, (generator word).length = length word.length)
    (adversary : Distinguisher) {n : ℕ} (hpos : 0 < length n) :
    Game.guessingAdvantage (nextBitPredictionGame generator length
      (wordNextBitPredictor length adversary) n) =
      Game.advantage (ProbComp.eval (prgRealGame generator adversary n))
        (ProbComp.eval (prgIdealGame length adversary n)) / (length n : ℝ≥0) := by
  have : NeZero (length n) := ⟨Nat.ne_of_gt hpos⟩
  have hgame : nextBitPredictionGame generator length (wordNextBitPredictor length adversary) n =
      (PMF.uniformOfFintype (Fin (length n))).bind fun i =>
        if hi : i.val < length n then
          wordNextBitStepGame generator length adversary n ⟨i.val, hi⟩
        else
          PMF.uniformOfFintype Bool := by
    simp only [nextBitPredictionGame, hpos, ↓reduceDIte, PMF.monad_bind_eq_bind]
    rw [PMF.bind_comm]
    refine congrArg _ (funext fun i => ?_)
    simp only [i.isLt, ↓reduceDIte, wordNextBitStepGame]
    rfl
  apply NNReal.coe_injective
  rw [hgame, guessingAdvantage_uniform_ite_fin _ le_rfl,
    sum_wordNextBitStepGame_sub_half hlen adversary n, NNReal.coe_div, NNReal.coe_natCast]

/-- Uniform strict-PPT random-index next-bit distinguisher built from a single-stage `predictor`:
when `0 < length n`, draw a padded uniform index `i ← ProbComp.sampleDyadicIndex (length n - 1)`;
if `i < length n`, output `decide ((← predictor n (word.take i)) = word.getD i false)`, else output
a fair coin. -/
noncomputable def nextBitDistinguisher (length : ℕ → ℕ)
    (predictor : Distinguisher) : Distinguisher := fun n word => do
  if 0 < length n then
    let i ← ProbComp.sampleDyadicIndex (length n - 1)
    if i < length n then
      let guess ← predictor n (word.take i)
      return decide (guess = word.getD i false)
    else
      ProbComp.uniform Bool
  else
    ProbComp.uniform Bool

private theorem isPPTOn_sampleDyadicIndex_fst {α : Type} {encα : α ↪ List Bool}
    {length : ℕ → ℕ} (hl : ComputableInPolyTime length encUnary encUnary) :
    IsPPTOn (encPair encUnary encα) encUnary
      (fun x : ℕ × α => ProbComp.sampleDyadicIndex (length x.1 - 1)) :=
  isPPTOn_sampleDyadicIndex
    (ComputableInPolyTime.unary_sub' (hl.comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.const 1))

/-- `nextBitDistinguisher length predictor` is uniformly strict PPT whenever `length` is unary
polynomial-time computable and `predictor` is uniformly strict PPT. -/
@[program_certificate]
theorem isPPT_nextBitDistinguisher {length : ℕ → ℕ} {predictor : Distinguisher}
    (hl : ComputableInPolyTime length encUnary encUnary) (hp : IsPPT encBool predictor) :
    IsPPT encBool (nextBitDistinguisher length predictor) := by
  have hpos : ComputableInPolyTime (fun p : ℕ × List Bool => decide (0 < length p.1))
      (encPair encUnary encBits) encBool :=
    ComputableInPolyTime.unary_lt' (ComputableInPolyTime.const 0)
      (hl.comp (ComputableInPolyTime.fst _ _))
  have hidx := isPPTOn_sampleDyadicIndex_fst (encα := encBits) hl
  have hcond : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ => decide (q.2 < length q.1.1))
      (encPair (encPair encUnary encBits) encUnary) encBool :=
    ComputableInPolyTime.unary_lt' (ComputableInPolyTime.snd _ _)
      (hl.comp ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))
  have htake : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ => q.1.2.take q.2)
      (encPair (encPair encUnary encBits) encUnary) encBits :=
    ComputableInPolyTime.bitsTakeWithInput
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _)
  have hn : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ => q.1.1)
      (encPair (encPair encUnary encBits) encUnary) encUnary :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)
  have hpred : IsPPTOn (encPair (encPair encUnary encBits) encUnary) encBool
      (fun q => predictor q.1.1 (q.1.2.take q.2)) :=
    hp.on.preprocess (hn.prod htake)
  have hret : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × ℕ) × Bool => decide (r.2 = r.1.1.2.getD r.1.2 false))
      (encPair (encPair (encPair encUnary encBits) encUnary) encBool) encBool :=
    computableInPolyTime_decide_eq_getD
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _)
  have hguess : IsPPTOn (encPair (encPair encUnary encBits) encUnary) encBool
      (fun q => if q.2 < length q.1.1 then
        (fun guess => decide (guess = q.1.2.getD q.2 false)) <$>
          predictor q.1.1 (q.1.2.take q.2)
      else ProbComp.uniform Bool) :=
    IsPPTOn.ite hcond.tidy (hpred.map_with hret) (isPPTOn_uniform_bool _)
  have hthen : IsPPTOn (encPair encUnary encBits) encBool (fun p => do
      let i ← ProbComp.sampleDyadicIndex (length p.1 - 1)
      if i < length p.1 then
        (fun guess => decide (guess = p.2.getD i false)) <$> predictor p.1 (p.2.take i)
      else ProbComp.uniform Bool) :=
    hidx.bind_with hguess
  change IsPPTOn (encPair encUnary encBits) encBool
    (fun p => nextBitDistinguisher length predictor p.1 p.2)
  simpa only [nextBitDistinguisher, bind_pure_comp] using
    IsPPTOn.ite hpos.tidy hthen (isPPTOn_uniform_bool _)

/-- On uniform ideal inputs, `nextBitDistinguisher length predictor` accepts with probability
exactly `1 / 2`. -/
theorem eval_prgIdealGame_nextBitDistinguisher (length : ℕ → ℕ)
    (predictor : Distinguisher) (n : ℕ) :
    ProbComp.eval (prgIdealGame length (nextBitDistinguisher length predictor) n) =
      PMF.uniformOfFintype Bool := by
  rw [eval_prgIdealGame, distinguishingGame_eq_bind]
  by_cases hl : 0 < length n
  · simp only [nextBitDistinguisher, hl, ↓reduceIte, ProbComp.eval_bind,
      ProbComp.eval_sampleDyadicIndex, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
    rw [PMF.bind_comm]
    refine (congrArg _ (funext fun i => ?_)).trans (PMF.bind_const _ _)
    by_cases hi : i.val < length n
    · simp only [hi, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
      rw [show (fun word : List Bool =>
          (ProbComp.eval (predictor n (word.take i.val))).bind fun guess =>
            PMF.pure (decide (guess = word.getD i.val false))) =
          fun word => (ProbComp.eval (predictor n (word.take i.val))).map
            fun guess => decide (guess = word.getD i.val false) from
        funext fun word => PMF.bind_pure_comp _ _]
      exact uniformList_bind_take_getD_eq_uniform_bool hi
        (fun w => ProbComp.eval (predictor n w))
    · simp only [hi, ↓reduceIte, ProbComp.eval_uniform, PMF.bind_const]
  · simp only [nextBitDistinguisher, hl, ↓reduceIte, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
      PMF.bind_const]

/-- Exact quantitative advantage of `nextBitDistinguisher`: when `0 < length n`, its PRG advantage
equals `(length n / dyadicSize (length n - 1))` times `predictor`'s random-index guessing
advantage. -/
theorem advantage_nextBitDistinguisher_eq (generator : List Bool → List Bool)
    (length : ℕ → ℕ) (predictor : Distinguisher) {n : ℕ} (hpos : 0 < length n) :
    Game.advantage
        (ProbComp.eval (prgRealGame generator (nextBitDistinguisher length predictor) n))
        (ProbComp.eval (prgIdealGame length (nextBitDistinguisher length predictor) n)) =
      ((length n : ℝ≥0) / dyadicSize (length n - 1)) *
        Game.guessingAdvantage (nextBitPredictionGame generator length predictor n) := by
  have : Nonempty (Fin (length n)) := ⟨⟨0, hpos⟩⟩
  let stepGame : Fin (length n) → Game := fun i =>
    (BitString.uniformList n).bind fun seed =>
      (ProbComp.eval (predictor n ((generator seed).take i.val))).map
        fun guess => decide (guess = (generator seed).getD i.val false)
  have hreal :
      ProbComp.eval (prgRealGame generator (nextBitDistinguisher length predictor) n) =
        (PMF.uniformOfFintype (Fin (dyadicSize (length n - 1)))).bind fun i =>
          if hi : i.val < length n then stepGame ⟨i.val, hi⟩ else PMF.uniformOfFintype Bool := by
    rw [eval_prgRealGame, distinguishingGame_eq_bind]
    simp only [nextBitDistinguisher, hpos, ↓reduceIte, ProbComp.eval_bind,
      ProbComp.eval_sampleDyadicIndex, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
    rw [PMF.bind_comm]
    refine congrArg _ (funext fun i => ?_)
    by_cases hi : i.val < length n
    · simp only [hi, ↓reduceIte, ↓reduceDIte, stepGame, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.bind_map, generatorEnsemble]
      rfl
    · simp only [hi, ↓reduceIte, ↓reduceDIte, ProbComp.eval_uniform, PMF.bind_const]
  have hpred :
      nextBitPredictionGame generator length predictor n =
        (PMF.uniformOfFintype (Fin (length n))).bind fun i =>
          if hi : i.val < length n then stepGame ⟨i.val, hi⟩ else PMF.uniformOfFintype Bool := by
    simp only [nextBitPredictionGame, hpos, ↓reduceDIte, PMF.monad_bind_eq_bind]
    rw [PMF.bind_comm]
    refine congrArg _ (funext fun i => ?_)
    simp only [i.isLt, ↓reduceDIte, stepGame, Fin.eta]
    rfl
  have hLD : length n ≤ dyadicSize (length n - 1) := by
    have hlt := Probability.lt_dyadicSize (length n - 1)
    omega
  have : NeZero (length n) := ⟨Nat.ne_of_gt hpos⟩
  have hDpos : (dyadicSize (length n - 1) : ℝ) ≠ 0 :=
    by exact_mod_cast (Probability.dyadicSize_pos (length n - 1)).ne'
  have hLpos : (length n : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  apply NNReal.coe_injective
  rw [eval_prgIdealGame_nextBitDistinguisher, ← Game.guessingAdvantage, hreal,
    guessingAdvantage_uniform_ite_fin stepGame hLD, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_natCast, hpred,
    guessingAdvantage_uniform_ite_fin stepGame le_rfl]
  field_simp
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Consequently `nextBitDistinguisher` loses at most a factor of `2` in advantage relative to
`nextBitPredictionGame`. -/
theorem guessingAdvantage_nextBitPredictionGame_le (generator : List Bool → List Bool)
    (length : ℕ → ℕ) (predictor : Distinguisher) {n : ℕ} (hpos : 0 < length n) :
    Game.guessingAdvantage (nextBitPredictionGame generator length predictor n) ≤
      2 * Game.advantage
        (ProbComp.eval (prgRealGame generator (nextBitDistinguisher length predictor) n))
        (ProbComp.eval (prgIdealGame length (nextBitDistinguisher length predictor) n)) := by
  rw [advantage_nextBitDistinguisher_eq generator length predictor hpos]
  have hDle : dyadicSize (length n - 1) ≤ 2 * length n := by
    have hle := Probability.dyadicSize_le (length n - 1)
    omega
  have hDpos : (0 : ℝ≥0) < dyadicSize (length n - 1) :=
    by exact_mod_cast Probability.dyadicSize_pos _
  have hLpos : (0 : ℝ≥0) < length n := by exact_mod_cast hpos
  calc Game.guessingAdvantage (nextBitPredictionGame generator length predictor n)
      ≤ ((2 * (length n : ℝ≥0)) / dyadicSize (length n - 1)) *
          Game.guessingAdvantage (nextBitPredictionGame generator length predictor n) := by
        refine le_mul_of_one_le_left zero_le ?_
        rw [one_le_div hDpos]
        exact_mod_cast hDle
    _ = 2 * (((length n : ℝ≥0) / dyadicSize (length n - 1)) *
          Game.guessingAdvantage (nextBitPredictionGame generator length predictor n)) := by
        ring

/-- Every `PseudorandomGenerator` is random-index next-bit unpredictable. -/
theorem PseudorandomGenerator.nextBitUnpredictableRandomIndex
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) :
    NextBitUnpredictableRandomIndex generator length := by
  intro predictor hp
  have hD : IsPPT encBool (nextBitDistinguisher length predictor) :=
    isPPT_nextBitDistinguisher hG.polyTime_length hp
  have hadv : Negligible (fun n =>
      Game.advantage
        (ProbComp.eval (prgRealGame generator (nextBitDistinguisher length predictor) n))
        (ProbComp.eval (prgIdealGame length (nextBitDistinguisher length predictor) n))) := by
    simpa only [eval_prgRealGame, eval_prgIdealGame] using hG.indistinguishable _ hD
  refine negligible_of_le (hadv.const_mul 2) fun n => ?_
  exact guessingAdvantage_nextBitPredictionGame_le generator length predictor
    (lt_of_le_of_lt (Nat.zero_le n) (hG.stretch n))

/-- A polynomial-time length-stretching generator that is random-index next-bit unpredictable is a
`PseudorandomGenerator`. -/
theorem PseudorandomGenerator.of_nextBitUnpredictableRandomIndex
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ word, (generator word).length = length word.length)
    (hstretch : ∀ n, n < length n)
    (hunpred : NextBitUnpredictableRandomIndex generator length) :
    PseudorandomGenerator generator length := by
  apply PseudorandomGenerator.of_indistinguishable hg hlen hstretch
  intro adversary ha
  have hl := PRG.polyTime_length hg hlen
  have hP : IsPPT encBool (wordNextBitPredictor length adversary) :=
    isPPT_wordNextBitPredictor hl ha
  have hadv : Negligible (fun n => Game.guessingAdvantage
      (nextBitPredictionGame generator length (wordNextBitPredictor length adversary) n)) :=
    hunpred _ hP
  refine (hadv.polynomiallyBounded_mul hl.polynomiallyBounded).congr fun n => ?_
  have hpos : 0 < length n := lt_of_le_of_lt (Nat.zero_le n) (hstretch n)
  have hLne : (length n : ℝ≥0) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [guessingAdvantage_nextBitPredictionGame_wordNextBitPredictor hlen adversary hpos,
    mul_div_cancel₀ _ hLne, eval_prgRealGame, eval_prgIdealGame]

/-- **Yao's next-bit theorem (random-index formulation)**: a function is a `PseudorandomGenerator`
with expansion schedule `length` if and only if it runs in polynomial time, produces words of length
`length n`, strictly stretches every seed, and is uniformly PPT random-index next-bit
unpredictable. -/
theorem pseudorandomGenerator_iff_nextBitUnpredictableRandomIndex
    (generator : List Bool → List Bool) (length : ℕ → ℕ) :
    PseudorandomGenerator generator length ↔
      ComputableInPolyTime generator encBits encBits ∧
        (∀ word, (generator word).length = length word.length) ∧
        (∀ n, n < length n) ∧
        NextBitUnpredictableRandomIndex generator length :=
  ⟨fun h => ⟨h.polyTime, h.length_eq, h.stretch, h.nextBitUnpredictableRandomIndex⟩,
    fun ⟨hg, hlen, hstretch, hunpred⟩ =>
      PseudorandomGenerator.of_nextBitUnpredictableRandomIndex hg hlen hstretch hunpred⟩

/-! ### Section 2: Two-Stage Next-Bit Prediction (Boneh–Shoup Attack Game 3.2) -/

/-- Boneh–Shoup Attack Game 3.2 next-bit prediction experiment for a two-stage predictor: stage 1
chooses a bit position `i` and state `state`; stage 2 receives `state` and the generated prefix
`word.take i` and guesses bit `i` of `word`. Out-of-range positions (`length n ≤ i`) return a
fair coin so they yield zero advantage. -/
@[expose] noncomputable def nextBitExperiment {σ : Type} (generator : List Bool → List Bool)
    (length : ℕ → ℕ) (adversary : TwoStage Unit ℕ (List Bool) Bool σ) (n : ℕ) : Experiment := do
  let (i, state) ← adversary.choose ()
  let seed ← BitString.sampleList n
  let word := generator seed
  if i < length n then
    let guess ← adversary.guess state (word.take i)
    return decide (guess = word.getD i false)
  else
    ProbComp.uniform Bool

/-- Uniform strict-PPT next-bit unpredictability (Boneh–Shoup Definition 3.3 / Attack Game 3.2):
every uniform strict PPT two-stage predictor choosing a position `i : ℕ` (binary encoded) has
negligible guessing advantage in `nextBitExperiment`. -/
@[expose] def NextBitUnpredictable (generator : List Bool → List Bool) (length : ℕ → ℕ) : Prop :=
  ∀ {σ : Type} (encσ : σ ↪ List Bool) (adversary : ℕ → TwoStage Unit ℕ (List Bool) Bool σ),
    TwoStage.IsPPT encUnit encNat encBits encBool encσ adversary →
      Negligible (fun n =>
        Game.guessingAdvantage (ProbComp.eval (nextBitExperiment generator length (adversary n) n)))

/-- The uniform strict-PPT two-stage next-bit predictor built from a PRG distinguisher `adversary`:
stage 1 draws a padded uniform bit index `i ← ProbComp.sampleDyadicIndex (length n - 1)`; stage 2
forwards prefix queries to `wordNextBitPredictor length adversary`. -/
noncomputable def wordNextBitTwoStage (length : ℕ → ℕ) (adversary : Distinguisher) (n : ℕ) :
    TwoStage Unit ℕ (List Bool) Bool Unit where
  choose _ := do
    let i ← ProbComp.sampleDyadicIndex (length n - 1)
    return (i, ())
  guess _ prefixBits := wordNextBitPredictor length adversary n prefixBits

/-- `wordNextBitTwoStage length adversary` is uniformly strict PPT whenever `length` is unary
polynomial-time computable and `adversary` is uniformly strict PPT. -/
theorem isPPT_wordNextBitTwoStage {length : ℕ → ℕ} {adversary : Distinguisher}
    (hl : ComputableInPolyTime length encUnary encUnary) (ha : IsPPT encBool adversary) :
    TwoStage.IsPPT encUnit encNat encBits encBool encUnit
      (wordNextBitTwoStage length adversary) where
  choose := by
    have hidx := isPPTOn_sampleDyadicIndex_fst (encα := encUnit) hl
    have hret : ComputableInPolyTime (fun i : ℕ => (i, ())) encUnary (encPair encNat encUnit) :=
      ComputableInPolyTime.unary_to_binary.prod (ComputableInPolyTime.const ())
    simpa only [wordNextBitTwoStage, bind_pure_comp] using hidx.map hret
  guess := by
    have hpred := isPPT_wordNextBitPredictor hl ha
    have hproj : ComputableInPolyTime (fun q : ℕ × (Unit × List Bool) => (q.1, q.2.2))
        (encPair encUnary (encPair encUnit encBits)) (encPair encUnary encBits) := by fun_prop
    exact hpred.on.preprocess hproj

/-- Exact quantitative advantage of `wordNextBitTwoStage`: when `0 < length n`, its two-stage
next-bit guessing advantage is `1 / dyadicSize (length n - 1)` times `adversary`'s PRG
advantage. -/
theorem guessingAdvantage_nextBitExperiment_wordNextBitTwoStage
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ word, (generator word).length = length word.length)
    (adversary : Distinguisher) {n : ℕ} (hpos : 0 < length n) :
    Game.guessingAdvantage
        (ProbComp.eval
          (nextBitExperiment generator length (wordNextBitTwoStage length adversary n) n)) =
      Game.advantage (ProbComp.eval (prgRealGame generator adversary n))
        (ProbComp.eval (prgIdealGame length adversary n)) /
        (dyadicSize (length n - 1) : ℝ≥0) := by
  have hexp :
      ProbComp.eval
          (nextBitExperiment generator length (wordNextBitTwoStage length adversary n) n) =
        (PMF.uniformOfFintype (Fin (dyadicSize (length n - 1)))).bind fun i =>
          if hi : i.val < length n then
            wordNextBitStepGame generator length adversary n ⟨i.val, hi⟩
          else
            PMF.uniformOfFintype Bool := by
    simp only [nextBitExperiment, wordNextBitTwoStage, ProbComp.eval_bind,
      ProbComp.eval_sampleDyadicIndex, ProbComp.eval_pure, BitString.eval_sampleList,
      PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def]
    refine congrArg _ (funext fun i => ?_)
    by_cases hi : i.val < length n
    · simp only [hi, ↓reduceIte, ↓reduceDIte, wordNextBitStepGame, ProbComp.eval_bind,
        ProbComp.eval_pure]
      rfl
    · simp only [hi, ↓reduceIte, ↓reduceDIte, ProbComp.eval_uniform, PMF.bind_const]
  have hLD : length n ≤ dyadicSize (length n - 1) := by
    have hlt := Probability.lt_dyadicSize (length n - 1)
    omega
  apply NNReal.coe_injective
  rw [hexp, guessingAdvantage_uniform_ite_fin _ hLD,
    sum_wordNextBitStepGame_sub_half hlen adversary n, NNReal.coe_div, NNReal.coe_natCast]

/-- The uniform strict-PPT PRG distinguisher constructed from a two-stage next-bit predictor
`adversary`: run stage 1 `(i, state) ← (adversary n).choose ()`, cap `idx := min (length n) i` to
a unary bound in polynomial time, and if `idx < length n` run stage 2 on `word.take idx` and
compare with bit `idx`; otherwise flip a fair coin. -/
noncomputable def twoStageNextBitDistinguisher {σ : Type} (length : ℕ → ℕ)
    (adversary : ℕ → TwoStage Unit ℕ (List Bool) Bool σ) : Distinguisher := fun n word => do
  let (i, state) ← (adversary n).choose ()
  let idx := min (length n) i
  if idx < length n then
    let guess ← (adversary n).guess state (word.take idx)
    return decide (guess = word.getD idx false)
  else
    ProbComp.uniform Bool

/-- `twoStageNextBitDistinguisher length adversary` is uniformly strict PPT whenever `length` is
unary polynomial-time computable and `adversary` is uniformly strict PPT. -/
@[program_certificate]
theorem isPPT_twoStageNextBitDistinguisher {σ : Type} {encσ : σ ↪ List Bool}
    {length : ℕ → ℕ} {adversary : ℕ → TwoStage Unit ℕ (List Bool) Bool σ}
    (hl : ComputableInPolyTime length encUnary encUnary)
    (hA : TwoStage.IsPPT encUnit encNat encBits encBool encσ adversary) :
    IsPPT encBool (twoStageNextBitDistinguisher length adversary) := by
  have hchoose : IsPPTOn (encPair encUnary encBits) (encPair encNat encσ)
      (fun p => (adversary p.1).choose ()) :=
    hA.choose.preprocess ((ComputableInPolyTime.fst _ _).prod (ComputableInPolyTime.const ()))
  have hlen : ComputableInPolyTime (fun q : (ℕ × List Bool) × (ℕ × σ) => length q.1.1)
      (encPair (encPair encUnary encBits) (encPair encNat encσ)) encUnary :=
    hl.comp ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))
  have hmin : ComputableInPolyTime (fun q : (ℕ × List Bool) × (ℕ × σ) => min (length q.1.1) q.2.1)
      (encPair (encPair encUnary encBits) (encPair encNat encσ)) encUnary :=
    ComputableInPolyTime.binary_min_unary' hlen
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))
  have hcond : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × (ℕ × σ) => decide (min (length q.1.1) q.2.1 < length q.1.1))
      (encPair (encPair encUnary encBits) (encPair encNat encσ)) encBool :=
    ComputableInPolyTime.unary_lt' hmin hlen
  have htake : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × (ℕ × σ) => q.1.2.take (min (length q.1.1) q.2.1))
      (encPair (encPair encUnary encBits) (encPair encNat encσ)) encBits :=
    ComputableInPolyTime.bitsTakeWithInput
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)) hmin
  have hguess : IsPPTOn (encPair (encPair encUnary encBits) (encPair encNat encσ)) encBool
      (fun q => (adversary q.1.1).guess q.2.2 (q.1.2.take (min (length q.1.1) q.2.1))) :=
    hA.guess.preprocess
      (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
        (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)).prod htake))
  have hret : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × (ℕ × σ)) × Bool =>
        decide (r.2 = r.1.1.2.getD (min (length r.1.1.1) r.1.2.1) false))
      (encPair (encPair (encPair encUnary encBits) (encPair encNat encσ)) encBool) encBool :=
    computableInPolyTime_decide_eq_getD
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)) hmin
  have hbranch : IsPPTOn (encPair (encPair encUnary encBits) (encPair encNat encσ)) encBool
      (fun q => if min (length q.1.1) q.2.1 < length q.1.1 then
        (fun guess => decide (guess = q.1.2.getD (min (length q.1.1) q.2.1) false)) <$>
          (adversary q.1.1).guess q.2.2 (q.1.2.take (min (length q.1.1) q.2.1))
      else ProbComp.uniform Bool) :=
    IsPPTOn.ite hcond.tidy (hguess.map_with hret) (isPPTOn_uniform_bool _)
  change IsPPTOn (encPair encUnary encBits) encBool
    (fun p => twoStageNextBitDistinguisher length adversary p.1 p.2)
  simpa only [twoStageNextBitDistinguisher, bind_pure_comp] using hchoose.bind_with hbranch

private theorem eval_twoStageNextBitDistinguisher_eq {σ : Type} (length : ℕ → ℕ)
    (adversary : ℕ → TwoStage Unit ℕ (List Bool) Bool σ) (n : ℕ) (word : List Bool) :
    ProbComp.eval (twoStageNextBitDistinguisher length adversary n word) =
      (ProbComp.eval ((adversary n).choose ())).bind fun p =>
        if p.1 < length n then
          (ProbComp.eval ((adversary n).guess p.2 (word.take p.1))).map
            fun guess => decide (guess = word.getD p.1 false)
        else
          PMF.uniformOfFintype Bool := by
  simp only [twoStageNextBitDistinguisher, ProbComp.eval_bind]
  refine congrArg _ (funext fun p => ?_)
  by_cases hi : p.1 < length n
  · have hmin : min (length n) p.1 = p.1 := Nat.min_eq_right hi.le
    simp only [hmin, hi, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
    exact (PMF.bind_pure_comp _ _).symm
  · have hmin : min (length n) p.1 = length n := Nat.min_eq_left (Nat.le_of_not_lt hi)
    simp only [hmin, hi, lt_irrefl, ↓reduceIte, ProbComp.eval_uniform]

/-- On uniform ideal inputs, `twoStageNextBitDistinguisher` accepts with probability `1 / 2`. -/
theorem eval_prgIdealGame_twoStageNextBitDistinguisher {σ : Type} (length : ℕ → ℕ)
    (adversary : ℕ → TwoStage Unit ℕ (List Bool) Bool σ) (n : ℕ) :
    ProbComp.eval (prgIdealGame length (twoStageNextBitDistinguisher length adversary) n) =
      PMF.uniformOfFintype Bool := by
  rw [eval_prgIdealGame, distinguishingGame_eq_bind]
  simp only [PMF.monad_bind_eq_bind, eval_twoStageNextBitDistinguisher_eq]
  rw [PMF.bind_comm]
  have hconst : (fun p : ℕ × σ =>
      (BitString.uniformList (length n)).bind fun word =>
        if p.1 < length n then
          (ProbComp.eval ((adversary n).guess p.2 (word.take p.1))).map
            fun guess => decide (guess = word.getD p.1 false)
        else PMF.uniformOfFintype Bool) = fun _ => PMF.uniformOfFintype Bool := by
    funext p
    by_cases hi : p.1 < length n
    · simp only [hi, ↓reduceIte]
      exact uniformList_bind_take_getD_eq_uniform_bool hi
        (fun w => ProbComp.eval ((adversary n).guess p.2 w))
    · simp only [hi, ↓reduceIte, PMF.bind_const]
  rw [hconst, PMF.bind_const]

/-- On generated inputs, `twoStageNextBitDistinguisher` agrees identically with
`nextBitExperiment`. -/
theorem eval_prgRealGame_twoStageNextBitDistinguisher {σ : Type}
    (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (adversary : ℕ → TwoStage Unit ℕ (List Bool) Bool σ) (n : ℕ) :
    ProbComp.eval (prgRealGame generator (twoStageNextBitDistinguisher length adversary) n) =
      ProbComp.eval (nextBitExperiment generator length (adversary n) n) := by
  rw [eval_prgRealGame, distinguishingGame_eq_bind, generatorEnsemble]
  simp only [PMF.monad_bind_eq_bind]
  rw [PMF.bind_map]
  simp only [Function.comp_def, eval_twoStageNextBitDistinguisher_eq]
  rw [PMF.bind_comm]
  simp only [nextBitExperiment, ProbComp.eval_bind, BitString.eval_sampleList]
  refine congrArg _ (funext fun p => congrArg _ (funext fun seed => ?_))
  by_cases hi : p.1 < length n
  · simp only [hi, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
    rfl
  · simp only [hi, ↓reduceIte, ProbComp.eval_uniform]

/-- Exact zero-loss quantitative identity between Attack Game 3.2 and PRG distinguishing for
`twoStageNextBitDistinguisher`. -/
theorem guessingAdvantage_nextBitExperiment_eq {σ : Type}
    (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (adversary : ℕ → TwoStage Unit ℕ (List Bool) Bool σ) (n : ℕ) :
    Game.guessingAdvantage (ProbComp.eval (nextBitExperiment generator length (adversary n) n)) =
      Game.advantage
        (ProbComp.eval
          (prgRealGame generator (twoStageNextBitDistinguisher length adversary) n))
        (ProbComp.eval
          (prgIdealGame length (twoStageNextBitDistinguisher length adversary) n)) := by
  rw [eval_prgRealGame_twoStageNextBitDistinguisher,
    eval_prgIdealGame_twoStageNextBitDistinguisher, Game.guessingAdvantage]

/-- Every `PseudorandomGenerator` is two-stage next-bit unpredictable (`NextBitUnpredictable`,
Boneh–Shoup Attack Game 3.2). -/
theorem PseudorandomGenerator.nextBitUnpredictable
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) :
    NextBitUnpredictable generator length := by
  intro σ encσ adversary hA
  have hD : IsPPT encBool (twoStageNextBitDistinguisher length adversary) :=
    isPPT_twoStageNextBitDistinguisher hG.polyTime_length hA
  have hadv : Negligible (fun n =>
      Game.advantage
        (ProbComp.eval
          (prgRealGame generator (twoStageNextBitDistinguisher length adversary) n))
        (ProbComp.eval
          (prgIdealGame length (twoStageNextBitDistinguisher length adversary) n))) := by
    simpa only [eval_prgRealGame, eval_prgIdealGame] using hG.indistinguishable _ hD
  refine hadv.congr fun n => ?_
  exact (guessingAdvantage_nextBitExperiment_eq generator length adversary n).symm

/-- A polynomial-time length-stretching generator that is two-stage next-bit unpredictable is a
`PseudorandomGenerator`. -/
theorem PseudorandomGenerator.of_nextBitUnpredictable
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ word, (generator word).length = length word.length)
    (hstretch : ∀ n, n < length n)
    (hunpred : NextBitUnpredictable generator length) :
    PseudorandomGenerator generator length := by
  apply PseudorandomGenerator.of_indistinguishable hg hlen hstretch
  intro adversary ha
  have hl := PRG.polyTime_length hg hlen
  have hA : TwoStage.IsPPT encUnit encNat encBits encBool encUnit
      (wordNextBitTwoStage length adversary) :=
    isPPT_wordNextBitTwoStage hl ha
  have hadv : Negligible (fun n => Game.guessingAdvantage
      (ProbComp.eval
        (nextBitExperiment generator length (wordNextBitTwoStage length adversary n) n))) :=
    hunpred encUnit _ hA
  have hpoly := computableInPolyTime_two_mul_length_poly hl
  refine (hadv.polynomiallyBounded_mul hpoly).congr fun n => ?_
  have hpos : 0 < length n := lt_of_le_of_lt (Nat.zero_le n) (hstretch n)
  have hDne : (dyadicSize (length n - 1) : ℝ≥0) ≠ 0 :=
    by exact_mod_cast (Probability.dyadicSize_pos (length n - 1)).ne'
  rw [guessingAdvantage_nextBitExperiment_wordNextBitTwoStage hlen adversary hpos,
    mul_div_cancel₀ _ hDne, eval_prgRealGame, eval_prgIdealGame]

/-- **Yao's next-bit theorem (Boneh–Shoup Attack Game 3.2)**: a function is a
`PseudorandomGenerator` with expansion schedule `length` if and only if it runs in polynomial time,
produces words of length `length n`, strictly stretches every seed, and is uniformly PPT two-stage
next-bit unpredictable. -/
theorem pseudorandomGenerator_iff_nextBitUnpredictable
    (generator : List Bool → List Bool) (length : ℕ → ℕ) :
    PseudorandomGenerator generator length ↔
      ComputableInPolyTime generator encBits encBits ∧
        (∀ word, (generator word).length = length word.length) ∧
        (∀ n, n < length n) ∧
        NextBitUnpredictable generator length :=
  ⟨fun h => ⟨h.polyTime, h.length_eq, h.stretch, h.nextBitUnpredictable⟩,
    fun ⟨hg, hlen, hstretch, hunpred⟩ =>
      PseudorandomGenerator.of_nextBitUnpredictable hg hlen hstretch hunpred⟩

end Cslib.Crypto
