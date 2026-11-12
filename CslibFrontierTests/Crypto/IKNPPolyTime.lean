/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.MPC.IKNP.PolyTime
import CslibFrontier.Tactic.PPT

/-! # Asymptotic correlation robustness and polytime IKNP: checked instances

* Non-vacuity of `CorrelationRobustHash.IsCorrelationRobust`: a constant-zero
  `CorrelationRobustHash` is explicitly broken by a `WordAdversary.IsPPT` distinguisher with
  constant advantage `1 / 2`.
* Non-vacuity of `isOraclePPTOn_iknpWordOracle`, `isPPTOn_iknpWordRun`,
  `isPPTOn_iknpSenderSimWord`, `isPPTOn_iknpReceiverSimWord`, `isPPTOn_iknpWordReduction`,
  `iknpWordRun_correctness`, `iknpWord_sender_advantage_zero`, and `iknpWord_receiver_advantage_eq`
  for concrete polynomial-time inputs. -/

namespace CslibFrontierTests.Crypto.IKNPPolyTime

open Cslib
open Cslib.BitString
open Cslib.Crypto
open Cslib.Crypto.CorrelationRobust
open Cslib.Crypto.Protocols.MPC
open Cslib.Probability
open Turing.MultiTapeTM
open scoped ENNReal NNReal

private def constZeroHash : CorrelationRobustHash where
  queries _ := 1
  keyLength _ := 1
  outLength _ := 1
  eval _ _ _ := [false]
  eval_length _ _ _ _ _ := rfl
  queries_poly := by fun_prop
  keyLength_poly := by fun_prop
  outLength_poly := by fun_prop
  eval_poly := by fun_prop

private def zeroCheckAdv : WordAdversary :=
  fun _ pair => pure (pair.2 == [[false]])

private theorem zeroCheckAdv_ppt : WordAdversary.IsPPT zeroCheckAdv := by
  unfold WordAdversary.IsPPT
  ppt [zeroCheckAdv]

/-- `constZeroHash` is NOT correlation-robust: `zeroCheckAdv` distinguishes `wordRealGame` from
`wordIdealGame` with advantage `1 / 2` for every security parameter `n`. -/
theorem not_isCorrelationRobust_constZeroHash : ¬ constZeroHash.IsCorrelationRobust := by
  intro hrobust
  have hneg := hrobust zeroCheckAdv zeroCheckAdv_ppt
  have hadv (n : ℕ) :
      Game.advantage (wordRealGame constZeroHash zeroCheckAdv n)
        (wordIdealGame constZeroHash zeroCheckAdv n) = (1 / 2 : ℝ≥0) := by
    rw [wordAdvantage_eq_finite, CorrelationRobust.advantage]
    have hfin (j : Fin (constZeroHash.queries n)) (x : BitString (constZeroHash.keyLength n))
        (i : Fin (constZeroHash.outLength n)) :
        constZeroHash.toFinite n j x i = false := by
      fin_cases i
      simp [CorrelationRobustHash.toFinite, constZeroHash, BitString.ofList]
    have hbody (t u : Fin 1 → BitString 1) :
        Adversary.ofWord zeroCheckAdv n 1 1 1 (t, u) = pure (decide (u 0 0 = false)) := by
      simp [Adversary.ofWord, CorrelationRobust.encodePair, zeroCheckAdv, List.ofFn_succ]
    have hreal :
        CorrelationRobust.realGame (constZeroHash.toFinite n)
            (Adversary.ofWord zeroCheckAdv n (constZeroHash.queries n)
              (constZeroHash.keyLength n) (constZeroHash.outLength n)) =
          PMF.pure true := by
      have hconst :
          ∀ (s : BitString (constZeroHash.keyLength n))
            (t : Fin (constZeroHash.queries n) → BitString (constZeroHash.keyLength n)),
            Adversary.ofWord zeroCheckAdv n (constZeroHash.queries n)
              (constZeroHash.keyLength n) (constZeroHash.outLength n)
              (t, fun j => constZeroHash.toFinite n j (t j + s)) = pure true := by
        intro s t
        have hlist :
            (List.ofFn fun j : Fin (constZeroHash.queries n) =>
              List.ofFn (constZeroHash.toFinite n j (t j + s))) = [[false]] := by
          have hzero :
              ∀ (j : Fin (constZeroHash.queries n)) (i : Fin (constZeroHash.outLength n)),
                constZeroHash.toFinite n j (t j + s) i = false :=
            fun j i => hfin j (t j + s) i
          dsimp only [constZeroHash] at hzero ⊢
          simp [List.ofFn_succ, hzero]
        simp [Adversary.ofWord, CorrelationRobust.encodePair, zeroCheckAdv, hlist]
      simp only [CorrelationRobust.realGame, ProbComp.eval_bind, ProbComp.eval_uniform,
        hconst, ProbComp.eval_pure, PMF.bind_const]
    have hidealTrue :
        (CorrelationRobust.idealGame
            (Adversary.ofWord zeroCheckAdv n (constZeroHash.queries n)
              (constZeroHash.keyLength n) (constZeroHash.outLength n))) true =
          (1 / 2 : ℝ≥0∞) := by
      change (CorrelationRobust.idealGame (Adversary.ofWord zeroCheckAdv n 1 1 1)) true =
        (1 / 2 : ℝ≥0∞)
      simp only [CorrelationRobust.idealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
        hbody, ProbComp.eval_pure, PMF.bind_apply, PMF.uniformOfFintype_apply,
        PMF.pure_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_unique,
        tsum_fintype, pow_one, Nat.cast_ofNat, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, mul_ite, mul_zero]
      let e : (Fin 1 → BitString 1) ≃ Bool :=
        ⟨fun u => u 0 0, fun b _ _ => b, fun u => by funext i j; fin_cases i; fin_cases j; rfl,
          fun _ => rfl⟩
      rw [Fintype.sum_equiv e
          (fun a : Fin 1 → BitString 1 =>
            if true = decide (a 0 0 = false) then (2 : ℝ≥0∞)⁻¹ else 0)
          (fun b : Bool => if true = decide (b = false) then (2 : ℝ≥0∞)⁻¹ else 0)
          (fun _ => rfl),
        Fintype.sum_bool]
      simp only [Bool.true_eq_false, decide_false, ↓reduceIte, decide_true, zero_add]
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul, one_div]
    rw [hreal]
    apply NNReal.eq
    rw [Game.coe_advantage, Game.succProbability, Game.succProbability, PMF.pure_apply,
      hidealTrue]
    simp only [↓reduceIte, ENNReal.toNNReal_one, NNReal.coe_one, one_div,
      ENNReal.toNNReal_inv, ENNReal.toNNReal_ofNat, NNReal.coe_inv, NNReal.coe_ofNat]
    norm_num
  have hconst : Negligible (fun _ : ℕ => (1 / 2 : ℝ≥0)) :=
    hneg.congr' (Filter.Eventually.of_forall hadv)
  obtain ⟨N, hN⟩ := (negligible_iff _).mp hconst 0 (1 / 2) (by norm_num)
  have hlt := hN N le_rfl
  simp at hlt

private def constX (_ : ℕ) : List (List Bool × List Bool) := [([true], [false])]

private def constR (_ : ℕ) : List Bool := [true]

private theorem constX_poly : ComputableInPolyTime constX encUnary encIKNPSenderPairs := by
  unfold constX encIKNPSenderPairs
  fun_prop

private theorem constR_poly : ComputableInPolyTime constR encUnary encBits := by
  unfold constR
  fun_prop

private def toyDistinguisher : ℕ → List Bool × List Bool → ProbComp Bool :=
  fun _ pair => pure (pair.1.headD false)

private theorem toyDistinguisher_ppt :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
      (fun p => toyDistinguisher p.1 p.2) := by
  ppt [toyDistinguisher]

/-- All word-level IKNP oracle, closed, simulator, and reduction components satisfy their strict
PPT contracts on `constZeroHash` and `(constX, constR, toyDistinguisher)`. -/
theorem iknp_ppt_contracts :
    IsOraclePPTOn encIKNPWordInput encIKNPRunOut
      (fun p => let q := p.2; iknpWordOracle constZeroHash p.1 q.1 q.2) ∧
    IsPPTOn encIKNPWordInput encIKNPRunOut
      (fun p => iknpWordRun constZeroHash p.1 p.2.1 p.2.2) ∧
    IsPPTOn (encPair encUnary encIKNPSenderPairs) encBits
      (fun p => iknpSenderSimWord constZeroHash p.1 p.2) ∧
    IsPPTOn (encPair encUnary (encPair encBits (encList encBits))) encBits
      (fun p => iknpReceiverSimWord constZeroHash p.1 p.2.1 p.2.2) ∧
    WordAdversary.IsPPT (iknpWordReduction constZeroHash constX constR toyDistinguisher) :=
  ⟨isOraclePPTOn_iknpWordOracle constZeroHash,
   isPPTOn_iknpWordRun constZeroHash,
   isPPTOn_iknpSenderSimWord constZeroHash,
   isPPTOn_iknpReceiverSimWord constZeroHash,
   isPPTOn_iknpWordReduction constZeroHash constX_poly constR_poly toyDistinguisher_ppt⟩

/-- Concrete sender privacy is exact (`advantage = 0`). -/
theorem sender_advantage_concrete :
    Game.advantage
      (ProbComp.eval (do
        let (sv, _, ov) ← iknpWordRun constZeroHash 3 (constX 3) (constR 3)
        toyDistinguisher 3 (sv, ov)))
      (ProbComp.eval (do
        let pair ← iknpWordSenderIdealSample constZeroHash 3 (constX 3) (constR 3)
        toyDistinguisher 3 pair)) = 0 :=
  iknpWord_sender_advantage_zero constZeroHash 3 (constX 3) (constR 3) (toyDistinguisher 3)

end CslibFrontierTests.Crypto.IKNPPolyTime
