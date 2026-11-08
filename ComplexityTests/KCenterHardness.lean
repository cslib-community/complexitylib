/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.KCenter.Gonzalez
public import Complexity.Computability.PCP.Approximation.KCenter

/-!
# Hardness of approximating metric k-center: examples

These kernel-checked examples (using no `native_decide`) exercise
`Cslib.Complexity.P_eq_NP_of_kCenter_approx`:

1. The `{0, 1, 2}` distance matrix of a path, with repeated and non-contiguous vertex labels and an
   edge to an undeclared vertex, and metric instances that hold and fail.
2. The decider on the path: centers at the middle vertex are accepted, centers at an endpoint are
   not, so a `2`-approximate answer (radius `2` against an optimum of `1`) is not enough. The
   decider handles `k = 0`, `k` above the number of vertices and out-of-range indices.
3. The hypotheses of the theorem: an exact, not necessarily polynomial-time, algorithm satisfies
   them with `ρ = 1`, and Gonzalez's algorithm, whose running time is not certified, satisfies
   them with `ρ = 2`, the threshold. A
   polynomial-time algorithm with `ρ < 2` gives `P = NP`, so no unconditional witness is expected.
-/

public section

namespace ComplexityTests.KCenterHardness

open Cslib.Complexity Cslib.Complexity.KCenter Cslib.Algorithms.Lean.KCenter

/-! ### 1. The distance matrix of a graph -/

/-- The path `10 - 20 - 30`, with `10` declared twice and an edge `30 - 40` to the undeclared
vertex `40`. -/
private def path3 : Graph := ([10, 20, 10, 30], [(10, 20), (30, 20), (30, 40)])

example : path3.distinctVertices = [10, 20, 30] := by decide

example : domMatrix path3 = [[0, 1, 2], [1, 0, 1], [2, 1, 0]] := by decide

example : IsInstance (domMatrix path3) := isInstance_domMatrix path3

/-- A matrix that violates the triangle inequality is not an instance. -/
example : ¬ IsInstance [[0, 1, 5], [1, 0, 1], [5, 1, 0]] := fun h => by
  have := h.isMetric.triangle 0 (by decide) 1 (by decide) 2 (by decide)
  revert this
  decide

/-- A matrix with a nonzero diagonal entry is not an instance. -/
example : ¬ IsInstance [[1, 1], [1, 0]] := fun h => by
  have := h.dist_self 0 (by decide)
  revert this
  decide

/-- A ragged matrix is not an instance. -/
example : ¬ IsInstance [[0, 1], [1]] := fun h => by
  have := h.length_row [1] (by decide)
  revert this
  decide

/-! ### 2. The decider -/

/-- An algorithm that picks the middle point `1`, plus an out-of-range index. -/
private def middle : List (List ℕ) × ℕ → List ℕ := fun _ => [1, 7]

/-- An algorithm that picks the endpoint `0`: radius `2`, twice the optimum. -/
private def endpoint : List (List ℕ) × ℕ → List ℕ := fun _ => [0]

example : centerLabels middle path3 1 = [20] := by decide

example : decideDominatingSet middle (path3, 1) = true := by decide

/-- A `2`-approximate answer does not dominate: the decider needs `ρ < 2`. -/
example : decideDominatingSet endpoint (path3, 1) = false := by decide

private instance : NeZero (domMatrix path3).length := ⟨by decide⟩

/-- The radius of the endpoint is `2`, twice the radius `1` of the middle point. -/
example : radius (fun i j => (TSP.finDist (domMatrix path3) i j : ℕ)) {0} = (2 : ℕ) ∧
    radius (fun i j => (TSP.finDist (domMatrix path3) i j : ℕ)) {1} = (1 : ℕ) := by
  decide

/-- `k` above the number of distinct vertices is rejected, as `DominatingSet` asks for exactly
`k` vertices. -/
example : decideDominatingSet middle (path3, 4) = false := by decide

/-- With `k = 0`, only the graph without vertices is accepted. -/
example : decideDominatingSet middle (path3, 0) = false ∧
    decideDominatingSet middle (([], []), 0) = true := by decide

/-! ### 3. The hypotheses of the hardness theorem -/

open Classical in
/-- An exact k-center algorithm: a set of at most `k` centers of optimal radius, as indices. It is
not claimed to be polynomial-time. -/
noncomputable def exactCenters (x : List (List ℕ) × ℕ) : List ℕ :=
  if h : x.1.length = 0 then []
  else
    haveI : NeZero x.1.length := ⟨h⟩
    ((exists_radius_eq_optRadius (fun i j => (TSP.finDist x.1 i j : ℝ)) x.2).choose.toList.map
      Fin.val)

private theorem centers_map_val (D : List (List ℕ)) (S : Finset (Fin D.length)) :
    centers D (S.toList.map Fin.val) = S := by
  ext i
  simp only [mem_centers, List.mem_map, Finset.mem_toList]
  exact ⟨fun ⟨j, hj, hji⟩ => Fin.val_injective hji ▸ hj, fun hi => ⟨i, hi, rfl⟩⟩

/-- The exact algorithm satisfies the hypotheses of `Cslib.Complexity.P_eq_NP_of_kCenter_approx`
with `ρ = 1`, so they are consistent. -/
example : (∀ D k, IsInstance D → 0 < k → k ≤ D.length →
      (centers D (exactCenters (D, k))).card ≤ k) ∧
    ∀ D k [NeZero D.length], IsInstance D → 0 < k → k ≤ D.length → ∀ r : ℝ,
      optRadius (fun i j => (TSP.finDist D i j : ℝ)) k ≤ r →
        radius (fun i j => (TSP.finDist D i j : ℝ)) (centers D (exactCenters (D, k))) ≤
          ((1 * r : ℝ) : WithTop ℝ) := by
  have hspec : ∀ D k [NeZero D.length], (centers D (exactCenters (D, k))).card ≤ k ∧
      radius (fun i j => (TSP.finDist D i j : ℝ)) (centers D (exactCenters (D, k))) =
        optRadius (fun i j => (TSP.finDist D i j : ℝ)) k := by
    intro D k hD
    have h0 : D.length ≠ 0 := NeZero.ne _
    simp only [exactCenters, h0, ↓reduceDIte, centers_map_val]
    exact (exists_radius_eq_optRadius _ k).choose_spec
  refine ⟨fun D k _ _ _ => ?_, fun D k _ _ _ _ r hr => ?_⟩
  · rcases Nat.eq_zero_or_pos D.length with h0 | h0
    · refine le_of_eq_of_le (Finset.card_eq_zero.2 ?_) (Nat.zero_le k)
      exact Finset.eq_empty_of_forall_notMem fun i _ => absurd i.2 (by omega)
    · have : NeZero D.length := ⟨by omega⟩
      exact (hspec D k).1
  · rw [one_mul, (hspec D k).2]
    exact hr

open Classical in
/-- Gonzalez's farthest-first traversal on the points of `D`, as indices. -/
noncomputable def gonzalezCenters (x : List (List ℕ) × ℕ) : List ℕ :=
  (gonzalez (fun i j => (TSP.finDist x.1 i j : ℝ)) (List.finRange x.1.length) x.2).map Fin.val

private theorem centers_gonzalezCenters (D : List (List ℕ)) (k : ℕ) :
    centers D (gonzalezCenters (D, k)) =
      (gonzalez (fun i j => (TSP.finDist D i j : ℝ)) (List.finRange D.length) k).toFinset := by
  ext i
  simp only [mem_centers, gonzalezCenters, List.mem_map, List.mem_toFinset]
  exact ⟨fun ⟨j, hj, hji⟩ => Fin.val_injective hji ▸ hj, fun hi => ⟨i, hi, rfl⟩⟩

/-- Gonzalez's algorithm satisfies the hypotheses of `Cslib.Complexity.P_eq_NP_of_kCenter_approx`
other than running time with `ρ = 2` ([WilliamsonShmoys2011], Theorem 2.3). So the threshold
`ρ < 2` is sharp, up to certifying Gonzalez's polynomial running time, which is not done here. -/
example : (∀ D k, IsInstance D → 0 < k → k ≤ D.length →
      (centers D (gonzalezCenters (D, k))).card ≤ k) ∧
    ∀ D k [NeZero D.length], IsInstance D → 0 < k → k ≤ D.length → ∀ r : ℝ,
      optRadius (fun i j => (TSP.finDist D i j : ℝ)) k ≤ r →
        radius (fun i j => (TSP.finDist D i j : ℝ)) (centers D (gonzalezCenters (D, k))) ≤
          ((2 * r : ℝ) : WithTop ℝ) := by
  refine ⟨fun D k _ _ _ => ?_, fun D k _ hD _ _ r hr => ?_⟩
  · rw [centers_gonzalezCenters]
    exact card_toFinset_gonzalez_le _ _ k
  · rw [centers_gonzalezCenters]
    refine radius_gonzalez_le_two_mul (fun i j => ?_) (fun i j l => ?_) (List.mem_finRange) hr
    · exact_mod_cast hD.isMetric.symm i i.2 j j.2
    · exact_mod_cast hD.isMetric.triangle i i.2 j j.2 l l.2

end ComplexityTests.KCenterHardness
