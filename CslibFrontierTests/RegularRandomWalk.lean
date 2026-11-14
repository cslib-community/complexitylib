/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Probability.MarkovChain.RotationMap

/-!
# Random walks on regular multigraphs: checked clients for Arora–Barak Exercise 7.9

The parts (b)(i), (c) and (d) of [Arora and Barak, Exercise 7.9][AroraBarak07] in the source's
form, for a `d`-regular multigraph `G : RotationMap V D` on `n = |V|` vertices, and the
single-edge instance `flip` on `Bool`, where the expected return time is exactly `2`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.RegularRandomWalk

open Cslib Cslib.RotationMap Cslib.Probability Cslib.Probability.MarkovChain Finset
open scoped ENNReal

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [Nonempty D] (G : RotationMap V D)

/-- (b)(i): on a connected regular graph, the uniform distribution is the unique stationary
distribution. -/
example (hG : G.toSimpleGraph.Connected) (π : PMF V) :
    G.randomWalk.IsStationary π ↔ π = @PMF.uniformOfFintype V _ hG.nonempty :=
  isStationary_randomWalk_iff hG π

/-- (c): `E_u ≤ 10 n²`, and in fact `E_u = n` on a connected graph. -/
example (u : V) : returnTime G.randomWalk u ≤ 10 * (Fintype.card V : ℝ≥0∞) ^ 2 :=
  returnTime_randomWalk_le_ten_mul_sq u

example (hG : G.toSimpleGraph.Connected) (u : V) :
    returnTime G.randomWalk u = Fintype.card V :=
  returnTime_randomWalk_eq_card_of_connected hG u

/-- (d): with `d ≤ n`, a path of length at most `k` from `u` to `v` gives
`E_{u,v} ≤ 100 k n²`. -/
example (hD : Fintype.card D ≤ Fintype.card V) {k : ℕ} {u v : V}
    (p : G.toSimpleGraph.Walk u v) (hk : p.length ≤ k) :
    hittingTime G.randomWalk v u ≤ 100 * k * (Fintype.card V : ℝ≥0∞) ^ 2 :=
  hittingTime_randomWalk_le_hundred_mul hD p hk

/-- (d), corollary: for connected `s`, `t`, the `1000 n³`-step walk from `s` misses `t` with
probability at most `1 / 10`, as a fraction of the label sequences. -/
example (hD : Fintype.card D ≤ Fintype.card V) {s t : V} (h : G.toSimpleGraph.Reachable s t) :
    (#{k : Fin (1000 * Fintype.card V ^ 3) → D |
        ∀ i ≤ 1000 * Fintype.card V ^ 3, G.walkAt (s, k) i ≠ t} : ℝ≥0∞) /
      (Fintype.card D : ℝ≥0∞) ^ (1000 * Fintype.card V ^ 3) ≤ 1 / 10 := by
  have h10 := ten_mul_card_filter_walkAt_ne_le (G := G) hD h
  rw [ENNReal.div_le_iff (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero))
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))]
  rw [one_div, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm]
  exact_mod_cast h10

/-- The single edge `{false, true}` as a `1`-regular graph. -/
private def flip : RotationMap Bool Unit := ofInvolutive (!·) fun b => Bool.not_not b

private theorem flip_connected : flip.toSimpleGraph.Connected := by
  have hadj : flip.toSimpleGraph.Adj false true := ⟨by decide, (), rfl⟩
  refine ⟨fun x y => ?_⟩
  have hft : flip.toSimpleGraph.Reachable false true := hadj.reachable
  cases x <;> cases y
  exacts [.refl _, hft, hft.symm, .refl _]

/-- On a single edge, the expected return time is `2`. -/
example : returnTime flip.randomWalk false = 2 := by
  rw [returnTime_randomWalk_eq_card_of_connected flip_connected]; rfl

end CslibFrontierTests.RegularRandomWalk
