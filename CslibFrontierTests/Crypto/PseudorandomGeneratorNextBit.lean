/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.PseudorandomGenerator.NextBit
import CslibFrontier.Crypto.Computational.OneWayToPRG
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Checked tests for uniform Yao next-bit unpredictability and pseudorandom generators

Exercises `CslibFrontier.Crypto.Computational.PseudorandomGenerator.NextBit` as a client:

1. **PPT certificate composition:** all four reductions (`wordNextBitPredictor`,
   `nextBitDistinguisher`, `wordNextBitTwoStage`, `twoStageNextBitDistinguisher`) inherit
   polynomial-time certificates in a plain client module.
2. **Concrete non-vacuity and full-output position coverage (`appendFalse`):** extending a seed
   by one trailing `false` bit (`seed ↦ seed ++ [false]`) leaves every proper prefix purely
   uniform, yet fails both `NextBitUnpredictable` (guessing index `n` with `false` gives exact
   success probability `1` and guessing advantage `1 / 2`) and
   `NextBitUnpredictableRandomIndex` (always guessing `false` gives exact guessing advantage
   `1 / (2 * (n + 1))`), refuting `PseudorandomGenerator` via both Yao equivalences.
3. **Out-of-range stage-1 index guard:** a two-stage predictor that outputs an index `≥ length n`
   receives guessing advantage `0` in `nextBitExperiment`.
4. **Non-stretching separation:** `generator := id` and `length := id` satisfy both
   `NextBitUnpredictable id id` and `NextBitUnpredictableRandomIndex id id` with zero advantage
   for every adversary (even unbounded), isolating the stretch requirement of
   `pseudorandomGenerator_iff_nextBitUnpredictable`.
5. **Positive client:** any uniform `OneWay` function yields a one-bit-stretching generator
   satisfying both `NextBitUnpredictable` and `NextBitUnpredictableRandomIndex`.
-/

namespace CslibFrontierTests.Crypto.PseudorandomGeneratorNextBit

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Shared uniform-prefix prediction helpers -/

private theorem length_of_mem_support_uniformList :
    ∀ {n : ℕ} {w : List Bool}, w ∈ (BitString.uniformList n).support → w.length = n
  | 0, w, hw => by
    rw [BitString.uniformList_zero, PMF.mem_support_pure_iff] at hw
    subst hw
    rfl
  | n + 1, w, hw => by
    rw [BitString.uniformList_succ] at hw
    simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hw
    rcases hw with ⟨_, _, tail, htail, rfl⟩
    simp [length_of_mem_support_uniformList htail]

private theorem getD_drop_zero (w : List Bool) (i : ℕ) :
    w.getD i false = (w.drop i).getD 0 false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem decide_eq_beq (bit : Bool) :
    (fun guess : Bool => decide (guess = bit)) = (fun guess : Bool => guess == bit) := by
  funext guess
  cases guess <;> cases bit <;> rfl

private theorem eval_uniformList_predictBit {i n : ℕ} (hi : i < n)
    (pred : List Bool → PMF Bool) :
    ((BitString.uniformList n).bind fun w =>
      (pred (w.take i)).map fun guess => decide (guess = w.getD i false)) =
      PMF.uniformOfFintype Bool := by
  let k := n - i - 1
  have hn : n = i + (k + 1) := by omega
  rw [hn]
  have hsplit := BitString.uniformList_bind_split i (k + 1)
    fun front back => (pred front).map fun guess => decide (guess = back.getD 0 false)
  have hfun :
      (fun w : List Bool => (pred (w.take i)).map fun guess => decide (guess = w.getD i false)) =
      (fun w : List Bool =>
        (pred (w.take i)).map fun guess => decide (guess = (w.drop i).getD 0 false)) := by
    funext w
    rw [getD_drop_zero w i]
  rw [hfun, hsplit]
  have htail (front : List Bool) :
      ((BitString.uniformList (k + 1)).bind fun back =>
        (pred front).map fun guess => decide (guess = back.getD 0 false)) =
        PMF.uniformOfFintype Bool := by
    rw [BitString.uniformList_succ, PMF.bind_bind]
    simp only [PMF.bind_map, Function.comp_def, List.getD_cons_zero, PMF.bind_const,
      decide_eq_beq]
    exact Game.uniform_bool_bind_map_beq_const (pred front)
  simp only [htail, PMF.bind_const]

/-! ### 1. Certificate composition in a client module -/

section Certificates

example (length : ℕ → ℕ) (hlength : ComputableInPolyTime length encUnary encUnary)
    (adversary : Distinguisher) (hadversary : IsPPT encBool adversary) :
    IsPPT encBool (wordNextBitPredictor length adversary) := by
  ppt

example (length : ℕ → ℕ) (hlength : ComputableInPolyTime length encUnary encUnary)
    (predictor : Distinguisher) (hpredictor : IsPPT encBool predictor) :
    IsPPT encBool (nextBitDistinguisher length predictor) := by
  ppt

example (length : ℕ → ℕ) (hlength : ComputableInPolyTime length encUnary encUnary)
    (adversary : Distinguisher) (hadversary : IsPPT encBool adversary) :
    TwoStage.IsPPT encUnit encNat encBits encBool encUnit
      (wordNextBitTwoStage length adversary) :=
  isPPT_wordNextBitTwoStage hlength hadversary

example (length : ℕ → ℕ) (hlength : ComputableInPolyTime length encUnary encUnary)
    {σ : Type} (encσ : σ ↪ List Bool)
    (adversary : ℕ → TwoStage Unit ℕ (List Bool) Bool σ)
    (hadversary : TwoStage.IsPPT encUnit encNat encBits encBool encσ adversary) :
    IsPPT encBool (twoStageNextBitDistinguisher length adversary) := by
  ppt

end Certificates

/-! ### 2. Trailing-zero generator fails both next-bit notions and `PseudorandomGenerator` -/

/-- Append a predictable trailing `false` bit to the seed. Every prefix of length `< n` is uniform,
so only predicting index `n` (the stretched bit) breaks next-bit unpredictability. -/
def appendFalse (seed : List Bool) : List Bool := seed ++ [false]

private noncomputable def twoStageLastFalse (n : ℕ) :
    TwoStage Unit ℕ (List Bool) Bool Unit where
  choose _ := pure (n, ())
  guess _ _ := pure false

private theorem isPPT_twoStageLastFalse :
    TwoStage.IsPPT encUnit encNat encBits encBool encUnit twoStageLastFalse where
  choose := by
    change IsPPTOn (encPair encUnary encUnit) (encPair encNat encUnit) fun x => pure (x.1, ())
    ppt
  guess := by
    change IsPPTOn (encPair encUnary (encPair encUnit encBits)) encBool fun _ => pure false
    ppt

private theorem eval_nextBitExperiment_appendFalse_twoStageLastFalse (n : ℕ) :
    ProbComp.eval (nextBitExperiment appendFalse (· + 1) (twoStageLastFalse n) n) =
      PMF.pure true := by
  simp only [nextBitExperiment, twoStageLastFalse, Nat.lt_add_one, ↓reduceIte, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  have hcongr :
      ((BitString.uniformList n).bind fun seed =>
        PMF.pure (decide (false = (appendFalse seed).getD n false))) =
      (BitString.uniformList n).bind fun _ => PMF.pure true := by
    refine Probability.PMF.bind_congr_on_support _ _ _ fun seed hseed => ?_
    have hlen := length_of_mem_support_uniformList hseed
    simp [appendFalse, List.getD_eq_getElem?_getD, hlen]
  rw [hcongr, PMF.bind_const]

/-- **`appendFalse` is not two-stage next-bit unpredictable**, hence not a `PseudorandomGenerator`
by `pseudorandomGenerator_iff_nextBitUnpredictable`. -/
theorem not_nextBitUnpredictable_appendFalse :
    ¬ NextBitUnpredictable appendFalse (· + 1) := by
  intro h
  have hneg := h encUnit twoStageLastFalse isPPT_twoStageLastFalse
  have hadv (n : ℕ) :
      Game.guessingAdvantage
        (ProbComp.eval (nextBitExperiment appendFalse (· + 1) (twoStageLastFalse n) n)) =
        1 / 2 := by
    rw [eval_nextBitExperiment_appendFalse_twoStageLastFalse]
    ext
    rw [Game.coe_guessingAdvantage, Game.coe_succProbability, PMF.pure_apply]
    norm_num
  exact not_negligible_const (by norm_num : (1 / 2 : ℝ≥0) ≠ 0) (hneg.congr hadv)

example : ¬ PseudorandomGenerator appendFalse (· + 1) := by
  intro hPRG
  exact not_nextBitUnpredictable_appendFalse
    ((pseudorandomGenerator_iff_nextBitUnpredictable appendFalse (· + 1)).mp hPRG).2.2.2

/-- Random-index predictor that always outputs `false`. -/
private noncomputable def constFalsePredictor : Distinguisher := fun _ _ => pure false

private theorem isPPT_constFalsePredictor : IsPPT encBool constFalsePredictor := by
  unfold constFalsePredictor
  ppt

private theorem not_negligible_inv_two_mul_add_one :
    ¬ Negligible (fun n : ℕ => 1 / (2 * ((n : ℝ≥0) + 1))) := by
  intro hneg
  have hlim := (hneg 1).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0) < 1 / 4))
  rcases (Filter.eventually_atTop.mp hlim) with ⟨N, hN⟩
  let m := max N 1
  have hm := hN m (le_max_left N 1)
  have hmpos : 1 ≤ m := le_max_right N 1
  have hm_real : ((m : ℝ) ^ 1 * (1 / (2 * ((m : ℝ) + 1)))) < 1 / 4 := by
    simpa using show ((m ^ 1 * (1 / (2 * ((m : ℝ≥0) + 1))) : ℝ≥0) : ℝ) < (1 / 4 : ℝ≥0) from
      hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hden : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
  rw [pow_one, mul_one_div, div_lt_iff₀ hden] at hm_real
  linarith

private theorem succProbability_nextBitPredictionGame_appendFalse_constFalse (n : ℕ) :
    (Game.succProbability
      (nextBitPredictionGame appendFalse (· + 1) constFalsePredictor n) : ℝ) =
      1 / 2 + 1 / (2 * ((n : ℝ) + 1)) := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  simp only [nextBitPredictionGame, hpos, ↓reduceDIte, constFalsePredictor, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.pure_bind]
  rw [PMF.bind_comm (BitString.uniformList n) (PMF.uniformOfFintype (Fin (n + 1)))]
  have hslice (i : Fin (n + 1)) :
      ((BitString.uniformList n).bind fun seed =>
        PMF.pure (decide (false = (appendFalse seed).getD i.1 false))) true =
        if i.1 < n then (2 : ℝ≥0∞)⁻¹ else 1 := by
    split_ifs with hi
    · have hleft :
          ((BitString.uniformList n).bind fun seed =>
            PMF.pure (decide (false = (appendFalse seed).getD i.1 false))) =
          ((BitString.uniformList n).bind fun seed =>
            (PMF.pure false : PMF Bool).map fun guess => decide (guess = seed.getD i.1 false)) := by
        refine Probability.PMF.bind_congr_on_support _ _ _ fun seed hseed => ?_
        have hlen := length_of_mem_support_uniformList hseed
        simp [appendFalse, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (lt_of_lt_of_eq hi hlen.symm)]
      rw [hleft, eval_uniformList_predictBit hi (fun _ => PMF.pure false),
        PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
    · have hin : i.1 = n := by omega
      have hpure :
          ((BitString.uniformList n).bind fun seed =>
            PMF.pure (decide (false = (appendFalse seed).getD i.1 false))) =
          (BitString.uniformList n).bind fun _ => PMF.pure true := by
        refine Probability.PMF.bind_congr_on_support _ _ _ fun seed hseed => ?_
        have hlen := length_of_mem_support_uniformList hseed
        simp [appendFalse, hin, List.getD_eq_getElem?_getD, hlen]
      rw [hpure, PMF.bind_const, PMF.pure_apply_self]
  rw [Game.coe_succProbability, PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum, Finset.sum_congr rfl fun i _ => by convert hslice i, Fin.sum_univ_castSucc]
  have hcast (j : Fin n) : (if (j.castSucc : Fin (n + 1)).1 < n then (2 : ℝ≥0∞)⁻¹ else 1) =
      (2 : ℝ≥0∞)⁻¹ := by
    simp [j.isLt]
  have hlast : (if (Fin.last n : Fin (n + 1)).1 < n then (2 : ℝ≥0∞)⁻¹ else 1) = 1 := by
    simp
  rw [Finset.sum_congr rfl fun j _ => hcast j, hlast, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one]
  norm_num [Nat.cast_add]
  field_simp
  ring

/-- **`appendFalse` is not random-index next-bit unpredictable**, hence not a
`PseudorandomGenerator` by `pseudorandomGenerator_iff_nextBitUnpredictableRandomIndex`. -/
theorem not_nextBitUnpredictableRandomIndex_appendFalse :
    ¬ NextBitUnpredictableRandomIndex appendFalse (· + 1) := by
  intro h
  have hneg := h constFalsePredictor isPPT_constFalsePredictor
  have hadv (n : ℕ) :
      Game.guessingAdvantage (nextBitPredictionGame appendFalse (· + 1) constFalsePredictor n) =
        1 / (2 * ((n : ℝ≥0) + 1)) := by
    ext
    rw [Game.coe_guessingAdvantage, succProbability_nextBitPredictionGame_appendFalse_constFalse]
    simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add,
      NNReal.coe_natCast]
    rw [add_sub_cancel_left, abs_of_pos (by positivity)]
  exact not_negligible_inv_two_mul_add_one (hneg.congr hadv)

example : ¬ PseudorandomGenerator appendFalse (· + 1) := by
  intro hPRG
  exact not_nextBitUnpredictableRandomIndex_appendFalse
    ((pseudorandomGenerator_iff_nextBitUnpredictableRandomIndex appendFalse (· + 1)).mp
      hPRG).2.2.2

/-! ### 3. Out-of-range stage-1 index guard check -/

private noncomputable def outOfRangeTwoStage (length : ℕ → ℕ) (n : ℕ) :
    TwoStage Unit ℕ (List Bool) Bool Unit where
  choose _ := pure (length n, ())
  guess _ _ := pure false

/-- A two-stage adversary returning index `length n` (out of `[0, length n)`) is routed to a
fair coin, so its guessing advantage in `nextBitExperiment` is `0`. -/
example (generator : List Bool → List Bool) (length : ℕ → ℕ) (n : ℕ) :
    Game.guessingAdvantage
      (ProbComp.eval (nextBitExperiment generator length (outOfRangeTwoStage length n) n)) = 0 := by
  have heval :
      ProbComp.eval (nextBitExperiment generator length (outOfRangeTwoStage length n) n) =
        PMF.uniformOfFintype Bool := by
    simp [nextBitExperiment, outOfRangeTwoStage, ProbComp.eval_uniform]
  rw [heval]
  ext
  rw [Game.coe_guessingAdvantage, Game.coe_succProbability]
  norm_num [PMF.uniformOfFintype_apply]

/-! ### 4. Non-stretching separation: `id` is next-bit unpredictable but not a PRG -/

/-- Even an unbounded two-stage adversary gets zero guessing advantage against the non-stretching
identity generator `id`. -/
theorem guessingAdvantage_nextBitExperiment_id {σ : Type}
    (adversary : TwoStage Unit ℕ (List Bool) Bool σ) (n : ℕ) :
    Game.guessingAdvantage (ProbComp.eval (nextBitExperiment id id adversary n)) = 0 := by
  have heval :
      ProbComp.eval (nextBitExperiment id id adversary n) = PMF.uniformOfFintype Bool := by
    simp only [nextBitExperiment, id_eq, ProbComp.eval_bind, BitString.eval_sampleList]
    trans (ProbComp.eval (adversary.choose ())).bind fun _ => PMF.uniformOfFintype Bool
    · refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨i, state⟩ _ => ?_
      split_ifs with hi
      · have hmap :
            ((BitString.uniformList n).bind fun seed =>
              (ProbComp.eval (adversary.guess state (seed.take i))).bind fun guess =>
                PMF.pure (decide (guess = seed.getD i false))) =
            ((BitString.uniformList n).bind fun seed =>
              (ProbComp.eval (adversary.guess state (seed.take i))).map
                fun guess => decide (guess = seed.getD i false)) := by
          refine Probability.PMF.bind_congr_on_support _ _ _ fun seed _ => rfl
        simpa only [ProbComp.eval_bind, ProbComp.eval_pure] using
          hmap.trans (eval_uniformList_predictBit hi fun prefixWord =>
            ProbComp.eval (adversary.guess state prefixWord))
      · simp [ProbComp.eval_uniform]
    · simp
  rw [heval]
  ext
  rw [Game.coe_guessingAdvantage, Game.coe_succProbability]
  norm_num [PMF.uniformOfFintype_apply]

/-- **`id` satisfies `NextBitUnpredictable id id`** (without stretch). -/
theorem nextBitUnpredictable_id : NextBitUnpredictable id id := by
  intro _ _ adversary _
  exact negligible_zero.congr fun n => (guessingAdvantage_nextBitExperiment_id (adversary n) n).symm

/-- **`id` satisfies `NextBitUnpredictableRandomIndex id id`** (without stretch). -/
theorem nextBitUnpredictableRandomIndex_id : NextBitUnpredictableRandomIndex id id := by
  intro predictor _
  refine negligible_zero.congr fun n => ?_
  have heval : nextBitPredictionGame id id predictor n = PMF.uniformOfFintype Bool := by
    simp only [nextBitPredictionGame, id_eq, PMF.monad_bind_eq_bind]
    split_ifs with hpos
    · have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hpos
      rw [PMF.bind_comm (BitString.uniformList n) (PMF.uniformOfFintype (Fin n))]
      have hslice (i : Fin n) :
          ((BitString.uniformList n).bind fun seed =>
            (ProbComp.eval (predictor n (seed.take i.1))).bind fun guess =>
              PMF.pure (decide (guess = seed.getD i.1 false))) =
            PMF.uniformOfFintype Bool := by
        have hmap :
            ((BitString.uniformList n).bind fun seed =>
              (ProbComp.eval (predictor n (seed.take i.1))).bind fun guess =>
                PMF.pure (decide (guess = seed.getD i.1 false))) =
            ((BitString.uniformList n).bind fun seed =>
              (ProbComp.eval (predictor n (seed.take i.1))).map
                fun guess => decide (guess = seed.getD i.1 false)) := rfl
        exact hmap.trans (eval_uniformList_predictBit i.isLt fun prefixWord =>
          ProbComp.eval (predictor n prefixWord))
      trans (PMF.uniformOfFintype (Fin n)).bind fun _ => PMF.uniformOfFintype Bool
      · exact Probability.PMF.bind_congr_on_support _ _ _ fun i _ => hslice i
      · simp
    · rfl
  rw [heval]
  symm
  ext
  rw [Game.coe_guessingAdvantage, Game.coe_succProbability]
  norm_num [PMF.uniformOfFintype_apply]

/-- Yet `id` is not a `PseudorandomGenerator`, isolating the strict-stretch requirement. -/
example : ¬ PseudorandomGenerator id id := fun h => absurd (h.stretch 0) (Nat.lt_irrefl _)

/-! ### 5. Positive client from a one-way function -/

/-- Any uniform one-way function supplies a generator satisfying both asymptotic next-bit
unpredictability notions. -/
example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ generator : List Bool → List Bool,
      NextBitUnpredictable generator (· + 1) ∧
      NextBitUnpredictableRandomIndex generator (· + 1) := by
  obtain ⟨generator, hG⟩ := hf.exists_pseudorandomGenerator
  exact ⟨generator, hG.nextBitUnpredictable, hG.nextBitUnpredictableRandomIndex⟩

end CslibFrontierTests.Crypto.PseudorandomGeneratorNextBit
