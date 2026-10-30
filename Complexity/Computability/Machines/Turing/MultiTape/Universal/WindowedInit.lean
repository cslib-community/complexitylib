/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedBound

/-!
# The cost of the initial windows

From the input of the universal function — a description `d`, an input `x` and a number of steps
`t` in binary — the first problem of the windowed simulation is the description, `t` in unary and
the windows of radius `t` of the initial configuration. It is computable in time
`O(N + (D + 1) ^ 3 + (t + 1) * (L + 1))` for the encoded input length `N`, the length `D` of the
description and the length `L` of `t` in binary: `t` is converted to unary by doubling, the input
symbols are recoded by a finite-state rewrite in linear time, and the input window is cut with a
linear-time take.

## Main results

* `Turing.MultiTapeTM.Universal.Windowed.initProb_inO`: the first problem.
-/

public section

namespace Turing.MultiTapeTM.Universal.Windowed

/-- **The first problem of the windowed simulation**, in time linear in the encoded input, cubic in
the length of the description and `O((t + 1) * (L + 1))` for `t` steps written with `L` binary
digits. -/
theorem initProb_inO :
    ComputableInO (fun i : Desc × List ℕ × ℕ => ((i.1, i.2.2, extract i.2.2 (initWin i.1 i.2.1)) :
        Prob)) eIn eProb
      (fun i => (eIn i).length + (descLen i.1 + 1) ^ 3 + (i.2.2 + 1) * ((encNat i.2.2).length + 1))
      (fun i => (eIn i).length + (descLen i.1 + 1) ^ 3 +
        (i.2.2 + 1) * ((encNat i.2.2).length + 1)) :=
  sorry

end Turing.MultiTapeTM.Universal.Windowed
