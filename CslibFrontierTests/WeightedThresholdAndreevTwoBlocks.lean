/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevTwoBlocks
import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevTwoBlocksLowerBound

/-!
Clients of the two-address-block bounds for Andreev's function: corner cutting and the ring lemma,
the explicit `4 ⌈m / 2⌉ + m`-gate circuit, and the `m - 1` lower bound for sign-coherent circuits,
applied to that circuit and to the `(5/16 + o(1)) n ^ 2` circuit.
-/

open Cslib Cslib.Circuits Cslib.Combinatorics

namespace WeightedThresholdAndreevTwoBlocksTests

open Boolean Boolean.WeightedThreshold Finset

-- An AND of two literals cuts the corner of the square `(0, 0)`; a literal does not.
example : CutsCorner (fun i j => decide (1 ≤ i ∧ 1 ≤ j)) 0 0 := by decide

example : ¬ CutsCorner (fun i _ => decide (1 ≤ i)) 0 0 := by decide

-- The staircase `[i + j ≥ 3]` turns at every square of the anti-diagonal `i + j = 2` (it cuts the
-- corners of `(0, 2), (1, 1), (2, 0)`) and of `i + j = 1`, but only `4` of the cut squares of the
-- `5 × 5` grid lie on the border.
example : CutsCorner (fun i j => decide (3 ≤ i + j)) 1 1 := by decide

example :
    #((gridBorder 5).filter fun p => CutsCorner (fun i j => decide (3 ≤ i + j)) p.1 p.2) ≤ 4 :=
  card_filter_cutsCorner_gridBorder_le
    (Or.inl fun _ _ _ h => by simp only [Bool.le_iff_imp, decide_eq_true_eq]; omega)
    (Or.inl fun _ _ _ h => by simp only [Bool.le_iff_imp, decide_eq_true_eq]; omega) 5

-- A reflected (antitone in `i`) staircase satisfies the ring lemma as well.
example (m : ℕ) :
    #((gridBorder m).filter fun p => CutsCorner (fun i j => decide (i ≤ j)) p.1 p.2) ≤ 4 :=
  card_filter_cutsCorner_gridBorder_le
    (Or.inr fun _ _ _ h => by simp only [Bool.le_iff_imp, decide_eq_true_eq]; omega)
    (Or.inl fun _ _ _ h => by simp only [Bool.le_iff_imp, decide_eq_true_eq]; omega) m

-- The border of the `7 × 7` grid has `24 = 4 · 6` squares.
example : 24 ≤ #(gridBorder 7) := le_card_gridBorder 7

-- The circuit computes Andreev's function with two address blocks, with `4 ⌈m / 2⌉ + m` bottom
-- gates; for `m = 4` that is `12` bottom gates on `12` inputs.
example (m : ℕ) : (andreevTwoBlocksCircuit m).Computes interpretation (single (andreev 2 m)) :=
  computes_andreevTwoBlocksCircuit m

example : (andreevTwoBlocksCircuit 4).size = 13 := by
  rw [size_andreevTwoBlocksCircuit]

-- It is far smaller than the general `(5/16 + o(1)) n ^ 2` circuit at `b = 2`.
example : (andreevTwoBlocksCircuit 8).size < (andreevSharpCircuit 2 8).size := by
  rw [size_andreevTwoBlocksCircuit, size_andreevSharpCircuit]; decide

-- The top sum is at least `13` exactly at the table bit addressed by the count parities.
example (x : BitString 2 → Bool) :
    13 ≤ andreevTwoBlocksTopSum 3 x ![3, 2] ↔ x (Pi.single 0 true) = true := by
  rw [thirteen_le_andreevTwoBlocksTopSum_iff x _ (by intro i; fin_cases i <;> decide)]
  congr! 2
  funext l; fin_cases l <;> rfl

-- Every bottom gate sees each block only through its count, so it is sign-coherent.
example (m : ℕ) (idx : AndreevTwoBlocksIndex m) (l : Fin 2) (t t' : Fin m) :
    (andreevTwoBlocksBottomOp m idx).weight (andreevBlockVar 2 m l t) =
      (andreevTwoBlocksBottomOp m idx).weight (andreevBlockVar 2 m l t') := by
  rw [weight_andreevTwoBlocksBottomOp_blockVar, weight_andreevTwoBlocksBottomOp_blockVar]

-- The lower bound applies to the circuit: `m - 1 ≤ 4 ⌈m / 2⌉ + m`.
example (m : ℕ) : m - 1 ≤ Fintype.card (AndreevTwoBlocksIndex m) :=
  sub_one_le_of_depthTwoInputs_andreev_two _ _ _ _ _ (computes_andreevTwoBlocksCircuit m)
    fun _ => isSignCoherent_andreevTwoBlocksBottomOp _

-- It applies to the `(5/16 + o(1)) n ^ 2` circuit at `b = 2` too.
example (m : ℕ) : m - 1 ≤ Fintype.card (AndreevSharpIndex 2 m) :=
  sub_one_le_of_depthTwoInputs_andreev_two _ _ _ _ _ (computes_andreevSharpCircuit 2 m)
    fun _ => isSignCoherent_andreevSharpBottomOp _

-- For a general circuit of depth at most two, it counts the bottom gates read by the output.
example (m : ℕ) (c : Circuit WeightedThreshold.signature (2 ^ 2 + 2 * m) 1) (hd : c.depth ≤ 2)
    (hc : c.Computes interpretation (single (andreev 2 m)))
    (hcoh : ∀ k ∈ outputBottomGates c 0,
      IsSignCoherent (andreevBlockVar 2 m) (inputWeight c.program k)) :
    m - 1 ≤ #(outputBottomGates c 0) :=
  sub_one_le_card_outputBottomGates_andreev_two c hd hc hcoh

end WeightedThresholdAndreevTwoBlocksTests
