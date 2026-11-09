/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game

/-!
# Symmetric four-game hops

Many indistinguishability proofs compare two real experiments `G0` and `G1` through intermediate
games `M0` and `M1`: each real game is close to its intermediate game by the same bound `c`, and
the two intermediate games are compared directly. The endpoint advantage is then at most
`c + advantage M0 M1 + c`.

## Main results

* `Cslib.Crypto.Game.advantage_four_hop_le`: the endpoint bound for a symmetric four-game chain.
-/

@[expose] public section

namespace Cslib.Crypto.Game

open scoped NNReal

/-- **Symmetric four-game hop**: if `G0` is within `c` of `M0` and `G1` is within `c` of `M1`,
then `G0` and `G1` differ by at most `c + advantage M0 M1 + c`. -/
theorem advantage_four_hop_le {G0 M0 M1 G1 : Game} {c : ℝ≥0}
    (h0 : G0.advantage M0 ≤ c) (h1 : G1.advantage M1 ≤ c) :
    G0.advantage G1 ≤ c + M0.advantage M1 + c := by
  rw [advantage_comm] at h1
  rw [add_assoc]
  exact (G0.advantage_triangle M0 G1).trans
    (add_le_add h0 ((M0.advantage_triangle M1 G1).trans (add_le_add le_rfl h1)))

end Cslib.Crypto.Game
