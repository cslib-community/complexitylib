/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: submitted #1072 @1606f7e2fb50e15a8843c9a26a04a8d94cb424c3

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Probability.StatisticalDistance

/-!
# Statistical distance of Boolean games

Boolean distinguishing advantage equals the upstream finite-PMF metric. This bridge lets
finite-source statistical bounds apply to every randomized Boolean test of an encoded output.

## Main results

* `Cslib.Crypto.Game.advantage_eq_nndist`: Boolean advantage is statistical distance.

## References

Copied from cslib PR #1072 at `1606f7e2fb50e15a8843c9a26a04a8d94cb424c3`.
Only the Boolean equality is included: the remaining arbitrary-type metric API requires #1065.
-/

public section

namespace Cslib.Crypto

open Probability.PMF
open scoped NNReal

/-- The absolute difference of success probabilities is precisely statistical distance
for Boolean experiments. -/
theorem Game.advantage_eq_nndist (game1 game2 : Game) :
    advantage game1 game2 = nndist game1 game2 := by
  have hfalse (p : PMF Bool) : (p false).toReal = 1 - (p true).toReal := by
    rw [← sum_toReal p, Fintype.sum_bool, add_sub_cancel_left]
  apply NNReal.eq
  rw [coe_advantage, coe_nndist, dist_eq, Fintype.sum_bool]
  simp only [succProbability, ENNReal.coe_toNNReal_eq_toReal]
  rw [hfalse, hfalse, sub_sub_sub_cancel_left, abs_sub_comm (game2 true).toReal,
    add_self_div_two]

end Cslib.Crypto
