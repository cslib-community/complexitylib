/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevSharp

/-!
Clients of the `(5/16 + o(1)) n ^ 2` depth-two circuit for Andreev's function: correctness, exact
gate counts at small parameters, the balanced size identity, the floor-balanced bound, and sign
coherence of the bottom gates.
-/

open Cslib Cslib.Circuits

namespace WeightedThresholdAndreevSharpTests

open Boolean Boolean.WeightedThreshold

-- The circuit computes Andreev's function on every input, with depth at most two.
example (b m : ℕ) : (andreevSharpCircuit b m).Computes interpretation (single (andreev b m)) :=
  computes_andreevSharpCircuit b m

example (b m : ℕ) : (andreevSharpCircuit b m).depth ≤ 2 := depth_andreevSharpCircuit_le b m

-- Exact sizes, matching the preprint's count `eq:bestcount` plus one top gate. At `b = m = 2`
-- the circuit has `35` gates, against `49` for the `(3/4) n ^ 2` circuit `andreevCircuit 2 2`.
example : (andreevSharpCircuit 2 2).size = 35 := by
  rw [size_andreevSharpCircuit]; decide

example : (andreevSharpCircuit 3 2).size = 88 := by
  rw [size_andreevSharpCircuit]; decide

example : (andreevSharpCircuit 4 4).size = 375 := by
  rw [size_andreevSharpCircuit]; decide

example : (andreevSharpCircuit 2 2).size < (andreevCircuit 2 2).size := by
  rw [size_andreevSharpCircuit, size_andreevCircuit]; decide

-- At exact balance `2 ^ 4 = 4 * 4` (`n = 32`) the identity reads
-- `16 · 375 = 5 · 32² - 4 · 32 · 4 + 48 · 32 - 32 · 4 - 16`.
example : 16 * ((andreevSharpCircuit 4 4).size : ℤ) =
    5 * ((2 ^ 4 + 4 * 4 : ℕ) : ℤ) ^ 2 - 4 * ((2 ^ 4 + 4 * 4 : ℕ) : ℤ) * (4 : ℕ) +
      48 * ((2 ^ 4 + 4 * 4 : ℕ) : ℤ) - 32 * (4 : ℕ) - 16 :=
  size_andreevSharpCircuit_of_balanced (by norm_num)

example : (16 * 375 : ℤ) = 5 * 32 ^ 2 - 4 * 32 * 4 + 48 * 32 - 32 * 4 - 16 := by norm_num

-- The floor-balanced bound `m = ⌊2 ^ b / b⌋` at `b = 5` (`m = 6`, `n = 62`).
example : 16 * (andreevSharpCircuit 5 6).size ≤ 5 * 67 ^ 2 + 52 * 67 + 24 := by
  simpa using size_andreevSharpCircuit_floor_le (b := 5) (by norm_num)

-- Every bottom gate is sign-coherent for Andreev's blocks, with block weights in `{0, 1}`.
example (b m : ℕ) (idx : AndreevSharpIndex b m) :
    IsSignCoherent (andreevBlockVar b m) (argWeight (andreevSharpBottomOp b m idx) id) :=
  isSignCoherent_andreevSharpBottomOp idx

-- In the form of lower bounds over the gates read by the output gate (#4718's `hcoh`).
example (b m : ℕ) {top : Fin (andreevSharpCircuit b m).size}
    (htop : (andreevSharpCircuit b m).outputs 0 = .gate top)
    {k : Fin (andreevSharpCircuit b m).size}
    (hk : k ∈ gateSupport (andreevSharpCircuit b m).program top) :
    IsSignCoherent (andreevBlockVar b m) (inputWeight (andreevSharpCircuit b m).program k) :=
  isSignCoherent_inputWeight_andreevSharpCircuit htop hk

-- The score has margin `N`: at `b = 1`, with the table `x_c = c_0` and block count `1`
-- (parity `1`), the selected bit is `true` and the score is at most `-2`.
example : andreevSharpScore 1 1 (fun c => c 0) (fun _ => 1) ≤ -(2 : ℝ) ^ 1 := by
  refine (andreevSharpScore_margin (m := 1) _ _ fun _ => le_rfl).2 ?_
  decide

end WeightedThresholdAndreevSharpTests
