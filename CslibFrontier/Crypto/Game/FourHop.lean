/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
import CslibFrontier.Crypto.Game.Hop

/-!
# Symmetric four-game hops

Many indistinguishability proofs compare two real experiments `G0` and `G1` through intermediate
games `M0` and `M1`: each real game is close to its intermediate game by the same bound `c`, and
the two intermediate games are compared directly. The endpoint advantage is then at most
`c + advantage M0 M1 + c`.

## Main results

* `Cslib.Crypto.Game.advantage_four_hop_le`: the endpoint bound for a symmetric four-game chain.
* `Cslib.Crypto.Game.negligible_advantage_four_hop`: its asymptotic form, for negligible `c`.
-/

public section

namespace Cslib.Crypto.Game

open Probability
open scoped NNReal

/-- **Symmetric four-game hop**: if `G0` is within `c` of `M0` and `G1` is within `c` of `M1`,
then `G0` and `G1` differ by at most `c + advantage M0 M1 + c`. -/
theorem advantage_four_hop_le {G0 M0 M1 G1 : Game} {c : ℝ≥0}
    (h0 : G0.advantage M0 ≤ c) (h1 : G1.advantage M1 ≤ c) :
    G0.advantage G1 ≤ c + M0.advantage M1 + c :=
  advantage_le_of_approxEq
    (calc Pr[G0] ≈[c] Pr[M0] := approxEq_of_advantage_le h0
      _ ≈[M0.advantage M1] Pr[M1] := approxEq_advantage M0 M1
      _ ≈[c] Pr[G1] := (approxEq_of_advantage_le h1).symm)

/-- **Asymptotic symmetric four-game hop**: if each real game `G0 n`, `G1 n` is within a
negligible `c n` of its intermediate game, and the intermediate games are indistinguishable, then
so are the real games. -/
theorem negligible_advantage_four_hop {G0 M0 M1 G1 : ℕ → Game} {c : ℕ → ℝ≥0}
    (hc : Negligible c) (hM : Negligible fun n => (M0 n).advantage (M1 n))
    (h0 : ∀ n, (G0 n).advantage (M0 n) ≤ c n) (h1 : ∀ n, (G1 n).advantage (M1 n) ≤ c n) :
    Negligible fun n => (G0 n).advantage (G1 n) :=
  negligible_of_le ((hc.add hM).add hc) fun n => advantage_four_hop_le (h0 n) (h1 n)

end Cslib.Crypto.Game
