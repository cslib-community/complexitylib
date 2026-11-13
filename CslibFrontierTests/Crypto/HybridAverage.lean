/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Game.Hybrid

/-!
# Finite-chain averaging with cancellation and padding

A four-game chain alternates between rejection and acceptance. Its three signed hop gaps
cancel to the endpoint gap. Sampling four indices pads both mixtures with one rejecting case.
-/

namespace Cslib.Tests.HybridAverage

open Probability Cslib.Crypto
open scoped NNReal

private noncomputable def games : Fin 4 → Game :=
  ![PMF.pure false, PMF.pure true, PMF.pure false, PMF.pure true]

private noncomputable def earlier : Game :=
  (PMF.uniformOfFintype (Fin 4)).bind fun i =>
    if hi : i.val < 3 then games (i.castLT hi).castSucc else PMF.pure false

private noncomputable def later : Game :=
  (PMF.uniformOfFintype (Fin 4)).bind fun i =>
    if hi : i.val < 3 then games (i.castLT hi).succ else PMF.pure false

/-- Only the middle active index accepts in the earlier mixture; the padded index rejects. -/
private theorem succProbability_earlier : Game.succProbability earlier = 1 / 4 := by
  rw [earlier, Game.succProbability_uniform]
  norm_num [games, Fin.sum_univ_succ, Game.succProbability, PMF.pure_apply]

/-- Two active indices accept in the later mixture; the padded index still rejects. -/
private theorem succProbability_later : Game.succProbability later = 1 / 2 := by
  rw [later, Game.succProbability_uniform]
  norm_num [games, Fin.sum_univ_succ, Game.succProbability, PMF.pure_apply]

/-- The two mixtures have advantage one quarter, and their exact finite-chain loss is four. -/
example : Game.advantage earlier later = 1 / 4 ∧
    Game.advantage (games 0) (games (Fin.last 3)) = 4 * Game.advantage earlier later := by
  constructor
  · apply NNReal.eq
    rw [Game.coe_advantage, succProbability_earlier, succProbability_later]
    norm_num
  · exact Game.advantage_hybrid_average_fin games 4 (by decide)

end Cslib.Tests.HybridAverage
