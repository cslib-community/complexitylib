/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.SimpleGraph.GreedyColoring
import CslibFrontier.Probability.MarkovChain.Coloring.Ratio
import CslibFrontier.Probability.StatisticalDistance.ClosedForm

/-!
# Path coupling and Glauber colorings: checked instances

* Uniform distributions on `{0}` and `{0, 1}` are at statistical distance exactly `1 / 2`, the
  bound `k / m` of `dist_uniformOfFinset_le` with `k = 1` and `m = 1` being `1`.
* Greedy coloring is tight: the triangle `K₃` has maximum degree `2` and chromatic number `3`.
* Glauber dynamics for `3`-colorings of the single edge `K₂` (`n = 2`, `Δ = 1`, `q = 3 > 2Δ`):
  `t_mix(ε) ≤ ⌈4 (log 2 - log ε)⌉`.
* The hypothesis that proper colorings exist is not vacuous: `K₂` has no proper `1`-coloring.
* The edge-length condition `ρ ≥ 1` of `IsPathMetric` cannot be dropped: for the identity chain on
  `Bool`, the metric `ρ(x, y) = 1/2` off the diagonal vanishes on the diagonal, has geodesic steps
  and has contracting couplings with `κ = 1`, but the statistical distance `1` between point masses
  exceeds `ρ`.
* Frozen boundary on `K₂` with `q = 3`, freezing vertex `1` at color `1`: the colorings agreeing
  with the boundary are the two colorings with vertex `0` colored `0` or `2`; freezing vertex `0`
  too leaves one coloring, a ratio `1 / 2 ≥ 1 / (3e)` (Lemma 14.16); and the frozen dynamics is
  within `δ` of uniform after `⌈-2 log δ⌉` steps.
-/

namespace ComplexityTests.PathCoupling

open Cslib.Probability Cslib.Probability.PMF Cslib.Probability.MarkovChain SimpleGraph
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

/-- `halfMetric` satisfies every field of `IsPathMetric` for the relation `≠` except `ρ ≥ 1`: it
vanishes on the diagonal and every pair `x ≠ y` has the geodesic step `z = y`. -/
theorem halfMetric_self_and_exists_step :
    (∀ x, halfMetric x x = 0) ∧
      (∀ x y, x ≠ y → ∃ z, x ≠ z ∧ x ≠ z ∧ halfMetric x z + halfMetric z y ≤ halfMetric x y) ∧
      ¬ IsPathMetric (fun x y : Bool => x ≠ y) halfMetric := by
  refine ⟨fun x => by simp [halfMetric], fun x y hxy => ⟨y, hxy, hxy, by simp [halfMetric]⟩,
    fun h => ?_⟩
  have := h.one_le true false (by decide)
  norm_num [halfMetric] at this

/-- All hypotheses of path coupling except `ρ ≥ 1` off the diagonal hold for `idChain` and
`halfMetric` with `κ = 1`: the diagonal coupling contracts, and every pair is a geodesic
(`halfMetric_self_and_exists_step`). -/
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

/-! ### A frozen boundary on a single edge -/

/-- The boundary coloring of `K₂`: vertex `0` colored `0`, vertex `1` colored `1`. -/
def edgeBoundary : Fin 2 → Fin 3 := fun i => i.castSucc

theorem isProperColoring_edgeBoundary : (⊤ : SimpleGraph (Fin 2)).IsProperColoring edgeBoundary :=
  (isProperColoring_iff _).2 fun u v huv => by
    simpa [edgeBoundary, Fin.ext_iff] using (top_adj u v).1 huv

/-- With vertex `1` frozen at color `1`, the proper colorings are those coloring vertex `0` with
`0` or `2`. -/
theorem frozenColorings_edge :
    frozenColorings (⊤ : SimpleGraph (Fin 2)) 3 {0} edgeBoundary =
      {![0, 1], ![2, 1]} := by
  decide

/-- Freezing vertex `0` as well leaves only the boundary coloring. -/
theorem frozenColorings_edge_empty :
    frozenColorings (⊤ : SimpleGraph (Fin 2)) 3 ∅ edgeBoundary = {edgeBoundary} := by
  decide

/-- **Lemma 14.16 on `K₂` with `q = 3`**: the ratio `|X_∅| / |X_{0}| = 1 / 2` is at least
`1 / (3e)`, as the lemma guarantees. -/
theorem ratio_frozenColorings_edge :
    (Real.exp 1 * 3)⁻¹ ≤
        ((frozenColorings (⊤ : SimpleGraph (Fin 2)) 3 ∅ edgeBoundary).card : ℝ) /
          (frozenColorings (⊤ : SimpleGraph (Fin 2)) 3 {0} edgeBoundary).card ∧
      ((frozenColorings (⊤ : SimpleGraph (Fin 2)) 3 ∅ edgeBoundary).card : ℝ) /
          (frozenColorings (⊤ : SimpleGraph (Fin 2)) 3 {0} edgeBoundary).card = 1 / 2 := by
  refine ⟨?_, by rw [frozenColorings_edge, frozenColorings_edge_empty]; norm_num⟩
  have h := inv_exp_mul_le_card_frozenColorings_erase_div (q := 3)
    (by rw [maxDegree_edge]; decide) isProperColoring_edgeBoundary (Finset.mem_singleton_self 0)
  simpa using h

/-- **Frozen-boundary sampling on `K₂` with `q = 3`** ((14.23) with `n = 1`): from the boundary
coloring, `t ≥ -2 log δ` steps of the dynamics updating vertex `0` are within `δ` of the uniform
distribution on the two colorings with vertex `1` colored `1`. -/
theorem dist_glauberColoringOn_edge {δ : ℝ} (hδ : 0 < δ) {t : ℕ} (ht : -2 * Real.log δ ≤ t) :
    dist ((glauberColoringOn (⊤ : SimpleGraph (Fin 2)) 3 {0} (Finset.singleton_nonempty 0) ^ t)
        edgeBoundary)
      (uniformOfFinset (frozenColorings (⊤ : SimpleGraph (Fin 2)) 3 {0} edgeBoundary)
        ⟨_, mem_frozenColorings_self isProperColoring_edgeBoundary⟩) ≤ δ := by
  refine dist_glauberColoringOn_frozen_le_of_le (⊤ : SimpleGraph (Fin 2)) (q := 3)
    (by rw [maxDegree_edge]; decide) _ _ (n := 1) (by simp) hδ ?_ fun _ _ => rfl
  simp only [maxDegree_edge, Nat.cast_one, Real.log_one]
  norm_num
  linarith

end ComplexityTests.PathCoupling
