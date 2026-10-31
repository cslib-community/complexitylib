/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BQP.Counting
import ComplexityTests.BQP

/-! `BQP ⊆ AWPP ⊆ PP`: concrete path counts, interference in the counts, and the inclusions
applied to a language in `BQP`. -/

namespace ComplexityTests.BQPCounting

open Cslib Cslib.Quantum Cslib.Complexity Turing.MultiTapeTM ComplexityTests.BQP

/-! ### Path simulation -/

-- The Toffoli code flips its target only when both controls are one.
example : pathRun [(false, 2, [0, 1])] [true, true, false] [] = ([true, true, true], false) := by
  decide
example : pathRun [(false, 2, [0, 1])] [true, false, false] [] = ([true, false, false], false) := by
  decide

-- A Hadamard gate writes the path bit and records the sign `(-1)^{1·1}`.
example : pathRun [(true, 0, [])] [true] [true] = ([true], true) := by decide
example : pathRun [(true, 0, [])] [true] [false] = ([false], false) := by decide

/-! ### Amplitudes and acceptance as counts -/

-- `H|1⟩ = (|0⟩ - |1⟩)/√2`: the amplitude gaps of the two outcomes are `1` and `-1`.
example : pathGap [(true, 0, [])] [true] [false] = 1 := by decide
example : pathGap [(true, 0, [])] [true] [true] = -1 := by decide

-- One Hadamard gate: one of the four pairs of paths accepts, so the probability is `1 / 2^1`.
example : acceptGap [(true, 0, [])] [false] = 1 := by decide

-- Two Hadamard gates interfere. From `|0⟩` the four accepting pairs cancel (probability `0`);
-- from `|1⟩` they add up to `4 = 2^2` (probability `1`).
example : acceptGap [(true, 0, []), (true, 0, [])] [false] = 0 := by decide
example : acceptGap [(true, 0, []), (true, 0, [])] [true] = 4 := by decide

-- The count agrees with the quantum acceptance probability of `hadamardOnce`.
example : acceptProb 1 [(true, 0, [])] [] = 1 / 2 := by
  rw [acceptProb_eq_acceptGap (by norm_num) _ (by decide)]
  have : List.ofFn (inputState 1 []) = [false] := by decide
  rw [this, show acceptGap [(true, 0, [])] [false] = 1 by decide]
  norm_num

/-! ### The inclusions -/

example : FirstBit ∈ AWPP encBits := BQP_subset_AWPP firstBit_mem_BQP
example : FirstBitᶜ ∈ PP encBits := BQP_subset_PP (compl_mem_BQP firstBit_mem_BQP)

end ComplexityTests.BQPCounting
