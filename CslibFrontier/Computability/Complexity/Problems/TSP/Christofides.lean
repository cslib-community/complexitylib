/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TSP.Christofides
public import CslibFrontier.Computability.Complexity.Problems.TSP.Approximation

/-!
# Christofides' 3/2-approximation for metric `TSP`

Christofides' tour `Cslib.Algorithms.Lean.TSP.christofides`, run on the distance matrix of a `TSP`
instance, visits every city exactly once, and on metric matrices its length is at most `3/2` times
the length of every tour, in particular an optimal one ([Christofides1976];
[WilliamsonShmoys2011], Theorem 2.13).

## Model

The cities, distances, tour lengths and the metric condition are those of
`Cslib.Complexity.TSP` and of the 2-approximation `Cslib.Complexity.TSP.approxTour`: the cities
are the row indices `0, …, D.length - 1`, `TSP.tourLength D p` is the length of the closed tour
`p`, and `TSP.IsMetric D` asks for symmetric distances satisfying the triangle inequality for all
triples of cities. Diagonal entries need not be zero.

## Main definitions

* `Cslib.Complexity.TSP.christofidesTour`: Christofides' tour of the cities.

## Main results

* `christofidesTour_perm`: the tour visits every city exactly once.
* `two_mul_tourLength_christofidesTour_le_three_mul`: on metric matrices, twice the length of the
  tour is at most three times the length of any tour.
* `two_mul_tourLength_christofidesTour_le_three_mul_of_mem`: if `x ∈ TSP` with `x.dist` metric,
  twice the length of the tour is at most `3 * x.bound`.

## Limitations

The matching step of `christofidesTour` is exhaustive search, which takes exponential time; these
results certify the approximation ratio, not a polynomial running time. No machine-level running
time is certified.

## References

* [N. Christofides, *Worst-case analysis of a new heuristic for the travelling salesman
  problem*][Christofides1976]
* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.4.
-/

public section

namespace Cslib.Complexity.TSP

open Cslib.Algorithms.Lean.TSP

/-- **Christofides' tour** of the cities of `D`: shortcut an Euler circuit of Kruskal's minimum
spanning tree together with a minimum-weight perfect matching on its odd-degree cities. -/
@[expose] def christofidesTour (D : List (List ℕ)) : List ℕ :=
  (christofides (finDist D)).map Fin.val

/-- **Feasibility.** Christofides' tour visits every city exactly once. -/
theorem christofidesTour_perm (D : List (List ℕ)) :
    (christofidesTour D).Perm (List.range D.length) := by
  rw [christofidesTour, ← List.map_coe_finRange_eq_range]
  exact (christofides_perm _).map Fin.val

/-- **Christofides' 3/2-approximation for metric TSP** ([Christofides1976];
[WilliamsonShmoys2011], Theorem 2.13): on a metric matrix, twice the length of Christofides' tour
is at most three times the length of any tour, in particular an optimal one. The matching step is
exhaustive search, so this certifies the approximation ratio, not a polynomial running time. -/
theorem two_mul_tourLength_christofidesTour_le_three_mul {D : List (List ℕ)} (hD : IsMetric D)
    {p : List ℕ} (hp : p.Perm (List.range D.length)) :
    2 * tourLength D (christofidesTour D) ≤ 3 * tourLength D p := by
  obtain ⟨q, rfl, hq, hcov⟩ := exists_map_val_eq_of_perm_range hp
  rw [christofidesTour, tourLength_map_val, tourLength_map_val]
  exact two_mul_cycleCost_christofides_le_three_mul (fun x y => hD.symm x x.isLt y y.isLt)
    (fun x y z => hD.triangle x x.isLt y y.isLt z z.isLt) hq hcov

/-- **The 3/2-approximation against the decision problem**: if a metric instance `x` belongs to
`TSP`, twice the length of Christofides' tour is at most `3 * x.bound`. -/
theorem two_mul_tourLength_christofidesTour_le_three_mul_of_mem {x : TSPInstance}
    (hx : IsMetric x.dist) (h : x ∈ TSP) :
    2 * tourLength x.dist (christofidesTour x.dist) ≤ 3 * x.bound := by
  obtain ⟨p, hp, hb⟩ := h
  exact (two_mul_tourLength_christofidesTour_le_three_mul hx hp).trans (Nat.mul_le_mul_left 3 hb)

end Cslib.Complexity.TSP
