/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Crypto.Multiparty.Tetrahedral
import Complexity.Crypto.Multiparty.TetrahedralChosen
import Complexity.Crypto.Multiparty.TetrahedralYield
import Complexity.Cryptanalysis.AddXNORRuns
import Complexity.GameTheory.FairDivision.MMSCodes
import Complexity.GameTheory.FairDivision.MMSChores
import Complexity.GameTheory.FairDivision.MMSAsymptotic
import Complexity.Cryptanalysis.AddXNOR
import Complexity.GameTheory.FairDivision.MMSImpossibility
import Mathlib.Tactic.NormNum

/-! # Regression clients for the three selected batch-B endpoints -/

open Cslib.Crypto.Tetrahedral

-- Figure 4: shuffle 1230, message Y, Alice 01, Bob receives the second bit 1.
public theorem shuffled_example : shuffle 9 = ![1, 2, 3, 0] ∧ message 9 = 1 ∧
    senderOutput 9 = (false, true) ∧ receiverOutput 9 = (true, true) := by decide

-- Receiving the first bit does not determine the other bit: Figure 6, X/0.
example : bobView 10 = bobView 14 ∧ senderOutput 10 ≠ senderOutput 14 := by decide

-- Section 5's reverse protocol publishes M=f(Alice's hand). Conditional on
-- Bob's card being 0, hand 13 and message X are dependent: the joint count is
-- 1, card-0 count is 6, hand-13/card-0 count is 1, X/card-0 count is 2.
-- Conditional independence would require 1*6=1*2. This refutes the reverse
-- complete-view privacy assertion, not the forward ROT theorem.
example :
    (Finset.univ.filter fun k => shuffle k 0 = 1 ∧ shuffle k 1 = 3 ∧
      shuffle k 2 = 0 ∧ message k = 0).card *
      (Finset.univ.filter fun k => shuffle k 2 = 0).card ≠
    (Finset.univ.filter fun k => shuffle k 0 = 1 ∧ shuffle k 1 = 3 ∧
      shuffle k 2 = 0).card *
      (Finset.univ.filter fun k => shuffle k 2 = 0 ∧ message k = 0).card :=
  reverse_message_leakage

-- Chosen input 10, choice 1, and the actual Figure 4 shuffle: Bob recovers 0.
example : choiceOffset 9 true = false ∧
    chosenMasks 9 (true, false) false = (true, true) ∧
    chosenOutput 9 (true, false) true = false := by decide

-- Complete-view privacy for two sender inputs agreeing in the selected position.
example (v : (Fin 4 × Fin 3 × (Bool × Bool)) × Bool × (Bool × Bool)) :
    (Finset.univ.filter fun k => chosenBobView k (false, false) true = v).card =
      (Finset.univ.filter fun k => chosenBobView k (true, false) true = v).card :=
  chosen_bob_privacy _ _ _ _ (by decide)

-- Arbitrary full-deck shuffles and hand positions: no more than one output per rank.
example (m : ℕ) (ρ : Equiv.Perm (Fin (4 * m))) (A B : Finset (Fin (4 * m))) :
    yield m ρ A B ≤ m := yield_le m ρ A B

open Cslib.FairDivision.MMSImpossibility

-- This concrete allocation attains minimum utility 20, so the bound is sharp.
example : let a : Cslib.FairDivision.MMSImpossibility.Allocation :=
    ![0, 0, 0, 1, 0, 1, 2, 2, 2, 3, 3]
    (fun i => value (agentType i) (bundle a i)) = ![22, 20, 20, 24] := by decide

-- A threshold above 21 fails for every four-way partition, not just the witnesses.
example : ¬ Guarantees true 22 := by
  rw [guarantees_iff]
  decide

open Cslib.Cryptanalysis.AddXNOR

-- Width 5, five operands and four operations; actual full-word average is 3 / 16.
example : averageCorrelation 3 4 = 3 / 16 := by
  rw [averageCorrelation_eq]
  norm_num

-- At width 2 and one operator the exact correlation is 3 / 4.
example : averageCorrelation 0 1 = 3 / 4 := by
  rw [averageCorrelation_eq]
  norm_num

-- Actual full-width addition carries into bit 1; XNOR has its usual word semantics.
example : step false (1#5) (1#5) = 2#5 ∧ step true (1#5) (1#5) = 31#5 := by decide

-- Fixed operators, arbitrary high bits: a length-two addition run annihilates correlation.
example (h : ℕ) : fixedCorrelation h (runs [2, 7]) = 0 := by
  rw [fixedCorrelation_runs]
  norm_num [runFactor, Function.iterate_succ_apply']

-- Signed factors may be negative, unlike an absolute correlation statistic.
example (h : ℕ) : fixedCorrelation h (runs [3, 1]) = -1 / 8 := by
  rw [fixedCorrelation_runs]
  norm_num [runFactor, Function.iterate_succ_apply']

open Cslib.FairDivision.MMSAsymptotic

-- Source parameter k=8, 110 dummy goods: 128 agents and 168 actual items.
example : Fintype.card (Good 8 110) = 168 := by rw [card_goods]

-- A matched pair and a mismatched pair are genuinely distinguished by the model.
example :
    lowWeight 8 (Sum.inl 3) + lowWeight 8 (Sum.inr (Sum.inl 3)) = 1088 ∧
    lowWeight 8 (Sum.inl 3) + lowWeight 8 (Sum.inr (Sum.inl 4)) ≠ 1088 := by decide

-- The parameterized integer valuations and costs are strictly positive on all items.
example (S : Finset (Fin 16)) (g : Good 8 110) :
    0 < goodsValue 8 110 S g ∧ 0 < choreCost 8 110 S g :=
  ⟨goodsValue_pos _ _ (by decide) S g, choreCost_pos _ _ (by decide) S g⟩

-- Source chores instance: the first source partition attains maximum cost 93.
example : let a : Cslib.FairDivision.MMSImpossibility.Allocation :=
    ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3]
    (fun i => Cslib.FairDivision.MMSChores.cost (agentType i) (bundle a i)) =
      ![90, 90, 93, 81] := by decide

-- A chores MMS cost cap below 90 is impossible for every complete partition.
example : ¬ Cslib.FairDivision.MMSChores.Caps true 89 := by
  rw [Cslib.FairDivision.MMSChores.caps_iff]
  decide

-- An actual source type (four one-bits out of eight) has exact MMS in both senses.
example (t : ℤ) :
    (Cslib.FairDivision.MMSAsymptotic.Guarantees 8 110 {1, 3, 5, 7, 8, 10, 12, 14} t ↔
      t ≤ 104448) ∧
    (Cslib.FairDivision.MMSAsymptotic.Caps 8 110 {1, 3, 5, 7, 8, 10, 12, 14} t ↔
      104448 ≤ t) := by
  constructor
  · exact Cslib.FairDivision.MMSAsymptotic.guarantees_iff 8 110 _ (by decide) (by decide) t
  · exact Cslib.FairDivision.MMSAsymptotic.caps_iff 8 110 _ (by decide) (by decide) t

-- Z has T-H, not 3T/4; the distinction matters for k greater than one.
example : weight 8 110 (Sum.inr (Sum.inl 0)) = 33728 := by decide

-- The codeword-to-label API discharges the weight invariant for an actual balanced word.
example (t : ℤ) :
    Cslib.FairDivision.MMSAsymptotic.Guarantees 8 110
      (labelSet (fun h => decide (h.val < 4))) t ↔ t ≤ 104448 :=
  balanced_guarantees_iff 110 _ (by decide) (by decide) t

-- The balanced encoder really doubles Hamming distance, including opposite words.
example : Cslib.FairDivision.MMSCodes.balance ![false, true, false] =
    ![false, true, false, true, false, true] := by decide

example : hammingDist
    (Cslib.FairDivision.MMSCodes.balance ![false, true, false])
    (Cslib.FairDivision.MMSCodes.balance ![true, false, true]) = 6 := by decide

-- A full population, rather than an assumed codebook, has a quantified item budget.
example : Fintype.card (Good 1088 63358) = 70976 := by rw [card_goods]
