/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevSharp

/-!
Clients of the `(5/16 + o(1)) n ^ 2` depth-two circuit for Andreev's function: correctness, exact
gate counts at small parameters, the balanced size identity, the floor-balanced bound, sign
coherence of the bottom gates, and the weight-magnitude bounds.
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

-- Weight magnitudes, with `n = 2 ^ b + b m`: every weight and threshold of every gate satisfies
-- `27 |w| ≤ 2 n ^ 3 + 54 (n + 1) (n + 4)`.
example (b m : ℕ) (k : Fin (andreevSharpCircuit b m).size)
    (a : Fin ((andreevSharpCircuit b m).program.lines k).op.arity) :
    27 * |((andreevSharpCircuit b m).program.lines k).op.weight a| ≤
      2 * (2 ^ b + b * m : ℝ) ^ 3 + 54 * (((2 ^ b + b * m : ℝ) + 1) * ((2 ^ b + b * m : ℝ) + 4)) :=
  abs_weight_andreevSharpCircuit_le k a

-- At `b = m = 4` (`n = 32`) this is `27 |w| ≤ 129688`, so `|w| ≤ 4804`.
example (k : Fin (andreevSharpCircuit 4 4).size) :
    |((andreevSharpCircuit 4 4).program.lines k).op.threshold| ≤ 4804 := by
  have h := abs_threshold_andreevSharpCircuit_le k
  norm_num at h
  linarith

-- The bottom gates read by the output gate have input weights at most `2 n`.
example (b m : ℕ) {top : Fin (andreevSharpCircuit b m).size}
    (htop : (andreevSharpCircuit b m).outputs 0 = .gate top)
    {k : Fin (andreevSharpCircuit b m).size}
    (hk : k ∈ gateSupport (andreevSharpCircuit b m).program top) (i : Fin (2 ^ b + b * m)) :
    |inputWeight (andreevSharpCircuit b m).program k i| ≤ 2 * (2 ^ b + b * m : ℝ) := by
  refine abs_inputWeight_andreevSharpCircuit_le (fun h => ?_) i
  rw [htop] at h
  cases h
  exact (mem_gateSupport _ _ _).mp hk (gateWeight_eq_zero_of_le _ _ _ le_rfl)

-- The bottom bound `2 n` is attained up to a constant: at `b = m = 4` the last load gate has
-- threshold `R = 54`, against `2 n = 64`.
example : andreevSharpThreshold 4 4 (.inr (.inl ⟨53, by decide⟩)) = 54 := by decide

example : andreevSharpRange 4 4 = 54 := by decide

-- The cubic top weights sit on the weight-one table addresses: `2 N (α ^ 2 - 1)`. At `b = 2`,
-- `m = 6` (`α = 2`, `n = 16`) this is `24`.
example : andreevSharpTopTable 2 6 (Pi.single 0 true) = 24 := by
  have h : BitString.IsSingle (Pi.single (0 : Fin 2) true) := ⟨0, rfl⟩
  have h0 : (Pi.single (0 : Fin 2) true : BitString 2) ≠ 0 := by decide
  simp [andreevSharpTopTable, h, h0, andreevSharpAmp]

-- The sharper top-input bound `27 b ^ 2 |v| ≤ 2 n ^ 3 + 54 b ^ 2 n (n + 1)`.
example (b m : ℕ) (i : Fin (2 ^ b + b * m)) :
    27 * b ^ 2 * |andreevSharpTopInput b m i| ≤
      2 * (2 ^ b + b * m : ℤ) ^ 3 +
        54 * b ^ 2 * ((2 ^ b + b * m : ℤ) * ((2 ^ b + b * m : ℤ) + 1)) :=
  sq_mul_abs_andreevSharpTopInput_le i

end WeightedThresholdAndreevSharpTests
