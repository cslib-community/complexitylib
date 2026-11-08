/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.SimpleGraph.GreedyColoring
import Complexity.Probability.MarkovChain.Coloring
import Complexity.Probability.StatisticalDistance.ClosedForm

/-!
# Path coupling and Glauber colorings: checked instances

* Uniform distributions on `{0}` and `{0, 1}` are at statistical distance exactly `1 / 2`, the
  bound `k / m` of `dist_uniformOfFinset_le` with `k = 1` and `m = 1` being `1`.
* Greedy coloring is tight: the triangle `K₃` has maximum degree `2` and chromatic number `3`.
* Glauber dynamics for `3`-colorings of the single edge `K₂` (`n = 2`, `Δ = 1`, `q = 3 > 2Δ`):
  `t_mix(ε) ≤ ⌈4 (log 2 - log ε)⌉`.
* The hypothesis that proper colorings exist is not vacuous: `K₂` has no proper `1`-coloring.
* The edge-length condition `ρ ≥ 1` of `IsPathMetric` cannot be dropped: for the identity chain on
  `Bool`, the metric `ρ(x, y) = 1/2` off the diagonal has geodesic steps and contracting
  couplings with `κ = 1`, but the statistical distance `1` between point masses exceeds `ρ`.
-/

namespace ComplexityTests.PathCoupling

open Cslib.Probability Cslib.Probability.PMF Cslib.Probability.MarkovChain
open scoped Cslib.Probability.PMF

/-! ### Uniform distributions on nested sets -/

theorem dist_uniform_zero_zeroOne :
    dist (uniformOfFinset ({0} : Finset (Fin 2)) (Finset.singleton_nonempty _))
      (uniformOfFinset ({0, 1} : Finset (Fin 2)) (Finset.insert_nonempty _ _)) = 1 / 2 := by
  rw [dist_uniformOfFinset_of_card_le _ _ (by decide)]
  rw [show (({0, 1} : Finset (Fin 2)) \ {0}) = {1} by decide]
  simp

/-! ### Greedy coloring is tight -/

theorem maxDegree_top_fin (n : ℕ) :
    (⊤ : SimpleGraph (Fin (n + 1))).maxDegree = n := by
  rw [SimpleGraph.IsRegularOfDegree.top.maxDegree_eq, Fintype.card_fin, Nat.add_sub_cancel]

example : (⊤ : SimpleGraph (Fin 3)).Colorable 3 :=
  SimpleGraph.colorable_of_maxDegree_lt _ (by rw [maxDegree_top_fin]; decide)

example : (⊤ : SimpleGraph (Fin 3)).chromaticNumber = (⊤ : SimpleGraph (Fin 3)).maxDegree + 1 := by
  rw [SimpleGraph.chromaticNumber_top, maxDegree_top_fin, Fintype.card_fin]
  rfl

/-! ### Glauber dynamics on a single edge -/

/-- `K₂` has maximum degree one. -/
theorem maxDegree_edge : (⊤ : SimpleGraph (Fin 2)).maxDegree = 1 := maxDegree_top_fin 1

/-- `K₂` has proper `3`-colorings, by greedy coloring. -/
theorem properColorings_edge_nonempty : (properColorings (⊤ : SimpleGraph (Fin 2)) 3).Nonempty :=
  properColorings_nonempty _ (by rw [maxDegree_edge]; decide)

/-- **Theorem 14.10 on `K₂` with `q = 3`**: `t_mix(ε) ≤ ⌈4 (log 2 - log ε)⌉`. -/
theorem mixingTime_glauberColoring_edge {ε : ℝ} (hε : 0 < ε) :
    (glauberColoring (⊤ : SimpleGraph (Fin 2)) 3).mixingTime
        (uniformOfFinset _ properColorings_edge_nonempty) ε ≤
      (⌈4 * (Real.log 2 - Real.log ε)⌉₊ : ℕ) := by
  have h := mixingTime_glauberColoring_le (⊤ : SimpleGraph (Fin 2)) (q := 3)
    (by rw [maxDegree_edge]; decide) properColorings_edge_nonempty hε
  simp only [maxDegree_edge, Fintype.card_fin] at h
  convert h using 4
  norm_num

/-- Without enough colors, proper colorings need not exist: `K₂` has no proper `1`-coloring. -/
theorem properColorings_edge_one : properColorings (⊤ : SimpleGraph (Fin 2)) 1 = ∅ := by
  ext x
  simp only [mem_properColorings, isProperColoring_iff, Finset.notMem_empty, iff_false]
  intro h
  exact h 0 1 (by decide) (Subsingleton.elim _ _)

/-! ### The edge-length condition is needed -/

/-- The identity chain on `Bool`. -/
noncomputable def idChain : MarkovChain Bool := 1

/-- A metric with edge length `1 / 2`. -/
noncomputable def halfMetric (x y : Bool) : ℝ := if x = y then 0 else 1 / 2

/-- All hypotheses of path coupling except `ρ ≥ 1` off the diagonal hold for `idChain` and
`halfMetric` with `κ = 1`: the diagonal coupling contracts, and every pair is a geodesic. -/
theorem halfMetric_coupling (x y : Bool) :
    ∃ ω : PMF (Bool × Bool), ω.map Prod.fst = idChain x ∧ ω.map Prod.snd = idChain y ∧
      ∑ p, (ω p).toReal * halfMetric p.1 p.2 ≤ 1 * halfMetric x y := by
  refine ⟨PMF.pure (x, y), by simp [idChain], by simp [idChain], ?_⟩
  rw [Finset.sum_eq_single (x, y)]
  · simp
  · intro b _ hb
    rw [PMF.pure_apply_of_ne _ _ hb, ENNReal.toReal_zero, zero_mul]
  · simp

/-- The conclusion of path coupling fails at `t = 0`: point masses are at distance `1`, which
exceeds `halfMetric true false = 1 / 2`. -/
theorem halfMetric_dist :
    dist ((idChain ^ 0) true) ((idChain ^ 0) false) = 1 ∧ halfMetric true false = 1 / 2 := by
  refine ⟨?_, by simp [halfMetric]⟩
  rw [pow_zero, one_apply, one_apply]
  exact dist_eq_one_of_disjoint_support (by simp)

end ComplexityTests.PathCoupling
