/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import Complexity.Crypto.Multiparty.Tetrahedral
import Complexity.Cryptanalysis.AddXNOR
import Complexity.GameTheory.FairDivision.MMSImpossibility
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/-! # Regression clients for the three selected batch-B endpoints -/

open Cslib.Crypto.Tetrahedral

-- Figure 4: shuffle 1230, message Y, Alice 01, Bob receives the second bit 1.
example : shuffle 9 = ![1, 2, 3, 0] ∧ message 9 = 1 ∧
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
      (Finset.univ.filter fun k => shuffle k 2 = 0 ∧ message k = 0).card := by decide

open Cslib.FairDivision.MMSImpossibility

-- This concrete allocation attains minimum utility 20, so the bound is sharp.
example : let a : Allocation := ![0, 0, 0, 1, 0, 1, 2, 2, 2, 3, 3]
    (fun i => value (agentType i) (bundle a i)) = ![22, 20, 20, 24] := by decide

-- A threshold above 21 fails for every four-way partition, not just the witnesses.
example : ¬ Guarantees true 22 := by
  rw [guarantees_iff]
  decide

open Cslib.Cryptanalysis.AddXNOR

-- Width 5, five operands and four operations; actual full-word average is 3/16.
example : averageCorrelation 3 4 = 3/16 := by
  rw [averageCorrelation_eq]
  norm_num

-- At width 2 and one operator the exact correlation is 3/4.
example : averageCorrelation 0 1 = 3/4 := by
  rw [averageCorrelation_eq]
  norm_num

-- Actual full-width addition carries into bit 1; XNOR has its usual word semantics.
example : step false (1#5) (1#5) = 2#5 ∧ step true (1#5) (1#5) = 31#5 := by decide
