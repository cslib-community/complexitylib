/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.TSP.MSTTour
public import Complexity.Computability.Complexity.Problems.TSP

/-!
# A 2-approximation for metric `TSP`

The minimum-spanning-tree tour `Cslib.Algorithms.Lean.TSP.mstTour`, run on the distance matrix of
a `TSP` instance, visits every city exactly once, and on metric matrices its length is at most
twice the length of every tour, in particular an optimal one ([WilliamsonShmoys2011],
Section 2.4).

## Model

The cities, distances and tour lengths are those of `Cslib.Complexity.TSP`: the cities are the
row indices `0, …, D.length - 1`, distances are `TSP.dist D`, and `TSP.tourLength D p` is the
length of the closed tour `p`. A matrix is metric (`TSP.IsMetric`) when the distances between
cities are symmetric and satisfy the triangle inequality. The triangle inequality is required for
all triples of cities, including those with `i = k`, so each diagonal entry is at most twice any
distance from its city. Diagonal entries need not be zero, as [WilliamsonShmoys2011] assumes; the
bound does not need that. Entries outside the city range are irrelevant.

## Main definitions

* `Cslib.Complexity.TSP.IsMetric`: symmetric distances with the triangle inequality.
* `Cslib.Complexity.TSP.approxTour`: the minimum-spanning-tree tour of the cities.

## Main results

* `approxTour_perm`: the tour visits every city exactly once.
* `tourLength_approxTour_le_two_mul`: on metric matrices, the tour has length at most twice the
  length of any tour.
* `tourLength_approxTour_le_two_mul_of_mem`: if `(D, b) ∈ TSP` with `D` metric, the tour has
  length at most `2 * b`.

## Limitations

No machine-level running time is certified for `approxTour`; that requires a polynomial-time
certificate for Kruskal's algorithm on encoded matrices.

## References

* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.4.
-/

public section

namespace Cslib.Complexity.TSP

open Cslib.Algorithms.Lean.TSP

/-- A distance matrix is **metric** when the distances between its cities are symmetric and satisfy
the triangle inequality. The triangle inequality covers all triples, including `i = k`, so each
diagonal entry is at most twice any distance from its city; diagonal entries need not be zero. -/
structure IsMetric (D : List (List ℕ)) : Prop where
  /-- Distances between cities are symmetric. -/
  symm : ∀ i < D.length, ∀ j < D.length, dist D i j = dist D j i
  /-- Distances between cities satisfy the triangle inequality. -/
  triangle : ∀ i < D.length, ∀ j < D.length, ∀ k < D.length, dist D i k ≤ dist D i j + dist D j k

/-- The distances between the cities of `D`, indexed by `Fin D.length`. -/
@[expose] def finDist (D : List (List ℕ)) (i j : Fin D.length) : ℕ :=
  dist D i j

/-- **The MST tour** of the cities of `D`: grow a tour from city `0` along Kruskal's minimum
spanning tree of the complete graph on the cities. -/
@[expose] def approxTour (D : List (List ℕ)) : List ℕ :=
  (mstTour (finDist D)).map Fin.val

/-- Tour lengths of city lists are closed-walk costs. -/
theorem tourLength_map_val (D : List (List ℕ)) (q : List (Fin D.length)) :
    tourLength D (q.map Fin.val) = cycleCost (finDist D) q := by
  simp only [tourLength, cycleCost, ← List.map_rotate, List.zipWith_map]
  rfl

/-- **Feasibility.** The MST tour visits every city exactly once. -/
theorem approxTour_perm (D : List (List ℕ)) : (approxTour D).Perm (List.range D.length) := by
  refine (List.perm_ext_iff_of_nodup
    (((mstTour_perm _).nodup_iff.2 (List.nodup_finRange _)).map Fin.val_injective)
    List.nodup_range).2 fun x => ?_
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.isLt
  · intro hx
    exact ⟨⟨x, hx⟩, (mstTour_perm _).symm.subset (List.mem_finRange _), rfl⟩

/-- **The 2-approximation for metric TSP** ([WilliamsonShmoys2011], Section 2.4): on a metric
matrix, the MST tour has length at most twice the length of any tour, in particular an optimal
one. -/
theorem tourLength_approxTour_le_two_mul {D : List (List ℕ)} (hD : IsMetric D) {p : List ℕ}
    (hp : p.Perm (List.range D.length)) : tourLength D (approxTour D) ≤ 2 * tourLength D p := by
  have hlt : ∀ x ∈ p, x < D.length := fun x hx => List.mem_range.1 (hp.subset hx)
  obtain ⟨q, rfl⟩ : ∃ q : List (Fin D.length), q.map Fin.val = p :=
    ⟨p.pmap Fin.mk hlt, by simp [List.map_pmap]⟩
  have hq : q.Nodup := (hp.nodup_iff.2 List.nodup_range).of_map _
  have hcov : ∀ x, x ∈ q := fun x => by
    obtain ⟨y, hy, hyx⟩ := List.mem_map.1 (hp.symm.subset (List.mem_range.2 x.isLt))
    exact Fin.ext hyx ▸ hy
  rw [approxTour, tourLength_map_val, tourLength_map_val]
  exact cycleCost_mstTour_le_two_mul (fun x y => hD.symm x x.isLt y y.isLt)
    (fun x y z => hD.triangle x x.isLt y y.isLt z z.isLt) hq hcov

/-- **The 2-approximation against the decision problem**: if a metric instance `(D, b)` belongs
to `TSP`, the MST tour has length at most `2 * b`. -/
theorem tourLength_approxTour_le_two_mul_of_mem {D : List (List ℕ)} {b : ℕ} (hD : IsMetric D)
    (h : (D, b) ∈ TSP) : tourLength D (approxTour D) ≤ 2 * b := by
  obtain ⟨p, hp, hb⟩ := h
  exact (tourLength_approxTour_le_two_mul hD hp).trans (Nat.mul_le_mul_left 2 hb)

end Cslib.Complexity.TSP
