/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Probability.MarkovChain.RandomWalk

/-!
# Hitting times of simple random walks: checked clients

* Goldreich's Exercise 6.19 in the source's form: for an edge `{u, v}` of a connected graph,
  `E_u[τ_v] ≤ 2 |E|`.
* On a single edge (`K₂`), the walk from `0` reaches `1` in exactly one step, so
  `E_0[τ_1] = 1` and the bound `E_u[τ_v] + deg v ≤ 2 |E|` holds with equality; the expected
  return time is `2 = 2 |E| / deg v` (here `deg v = 1 > 0`).
* On the triangle `K₃`, the edge bound gives `E_u[τ_v] ≤ 6`.
* On a single vertex the walk stays put (`randomWalk_apply_of_degree_eq_zero`), and the expected
  return time is `1`, so the division form `2 |E| / deg v` needs `deg v > 0`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.RandomWalkHitting

open Cslib.Probability.MarkovChain SimpleGraph Finset
open scoped ENNReal

/-- Goldreich, Exercise 6.19, as stated: for an edge `{u, v}` of a connected graph `G = (V, E)`,
the expected hitting time `E[X_{u,v}]` is at most `2 |E|`. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) {u v : V} (huv : G.Adj u v) :
    hittingTime (randomWalk G) v u ≤ 2 * #G.edgeFinset :=
  hittingTime_randomWalk_le_of_adj hG huv

/-- The single edge `K₂`. -/
private abbrev K₂ : SimpleGraph (Fin 2) := ⊤

private theorem card_edgeFinset_K₂ : #K₂.edgeFinset = 1 := by
  rw [card_edgeFinset_top_eq_card_choose_two]; rfl

private theorem degree_K₂ (v : Fin 2) : K₂.degree v = 1 := by
  rw [← card_neighborFinset_eq_degree]; fin_cases v <;> rfl

/-- On `K₂`, the walk from `0` reaches `1` after exactly one step. -/
private theorem hittingTime_K₂ : hittingTime (randomWalk K₂) 1 0 = 1 := by
  rw [hittingTime_eq_of_ne (by decide), Fin.sum_univ_two, hittingTime_self, mul_zero, add_zero,
    randomWalk_apply (by rw [degree_K₂]; norm_num), ite_eq_right (by simp), zero_mul, add_zero]

/-- On `K₂` the edge bound `E_u[τ_v] + deg v ≤ 2 |E|` is an equality. -/
example : hittingTime (randomWalk K₂) 1 0 + K₂.degree 1 = 2 * #K₂.edgeFinset := by
  rw [hittingTime_K₂, degree_K₂, card_edgeFinset_K₂]; norm_num

/-- The expected return time on `K₂` is `2 |E| / deg v = 2`. -/
example : returnTime (randomWalk K₂) 0 = 2 := by
  have h := degree_mul_returnTime_randomWalk (G := K₂) connected_top 0
  rw [degree_K₂, card_edgeFinset_K₂] at h
  simpa using h

/-- On the triangle, the expected hitting time of an adjacent vertex is at most `6`. -/
example : hittingTime (randomWalk (⊤ : SimpleGraph (Fin 3))) 1 0 ≤ 6 := by
  have h := hittingTime_randomWalk_le_of_adj (G := (⊤ : SimpleGraph (Fin 3))) connected_top
    (u := 0) (v := 1) (by decide)
  rw [card_edgeFinset_top_eq_card_choose_two] at h
  exact h.trans (by norm_num)

/-- On a single vertex the walk stays put. -/
example : randomWalk (⊥ : SimpleGraph Unit) () () = 1 := by
  rw [randomWalk_apply_of_degree_eq_zero (by simp)]; simp

/-- On a single vertex the expected return time is `1`, although `deg v = 0`. -/
example : returnTime (randomWalk (⊥ : SimpleGraph Unit)) () = 1 := by
  rw [returnTime_eq]; simp

end CslibFrontierTests.RandomWalkHitting
