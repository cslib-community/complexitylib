/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Card

/-!
# Superquadratic sensitivity separation: tournament

Defines tournaments on `Fin k`, regular tournaments on `2 * M ^ 2 + 1` vertices with outdegree
`M ^ 2`, and good labelings: edge labelings `label : Fin k → Fin k → Fin r` such that no sixteen
vertices admit a target assignment `m` with `label i j = m j` on every internal edge `i → j`. Basic
facts about edge orientations and sinks are recorded.

## Main definitions

* `Tournament`: a loopless digraph on `Fin k` with exactly one edge between distinct vertices.
* `RegularTournament`: a tournament on `2 * M ^ 2 + 1` vertices of outdegree `M ^ 2`.
* `GoodLabeling`: an edge labeling admitting no target-constant set of sixteen vertices.

## Main results

* `Tournament.adj_or_reverse`: distinct vertices are joined in one of the two directions.
* `Tournament.internal_sink_unique`: a vertex set has at most one internal sink.
* `GoodLabeling.good_implies_card_lt_sixteen`: a set on which the labeling is target-constant has
  fewer than `16` vertices.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Tournament.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- A loopless directed graph with exactly one edge between distinct vertices. -/
structure Tournament (k : ℕ) extends Digraph (Fin k) where
  /-- No vertex has an edge to itself. -/
  loopless : ∀ i, ¬ Adj i i
  /-- Exactly one orientation occurs between distinct vertices. -/
  edge_compl : ∀ {i j}, i ≠ j → (Adj i j ↔ ¬ Adj j i)

open scoped Classical in
/-- A tournament on `2 * M ^ 2 + 1` vertices with uniform outdegree `M ^ 2`. -/
structure RegularTournament (M : ℕ) extends Tournament (2 * M ^ 2 + 1) where
  /-- Every vertex has the prescribed number of outgoing neighbors. -/
  outdegree : ∀ i, (Finset.univ.filter (Adj i)).card = M ^ 2

/-- An edge labeling obstructing every target-constant labeling on sixteen vertices. -/
structure GoodLabeling {k : ℕ} (T : Tournament k) (r : ℕ) where
  /-- Label assigned to each ordered pair of vertices. -/
  label : Fin k → Fin k → Fin r
  /-- Every sixteen-vertex target assignment disagrees on a directed edge. -/
  good : ∀ I : Finset (Fin k), I.card = 16 → ∀ m : Fin k → Fin r,
    ∃ i ∈ I, ∃ j ∈ I, T.Adj i j ∧ label i j ≠ m j

namespace Tournament
variable {k : ℕ} (T : Tournament k)

/-- Adjacent vertices are distinct. -/
theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h

/-- An edge `i → j` excludes the reverse edge `j → i`. -/
theorem not_adj_reverse {i j : Fin k} (h : T.Adj i j) : ¬ T.Adj j i :=
  (T.edge_compl (T.ne_of_adj h)).mp h

/-- Distinct vertices are joined by an edge in at least one of the two directions. -/
theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)

/-- Two vertices of a set `I`, neither having an outgoing edge into `I`, are equal. -/
theorem internal_sink_unique {I : Finset (Fin k)} {i j : Fin k}
    (hi : i ∈ I) (hj : j ∈ I)
    (hsi : ∀ v ∈ I, ¬ T.Adj i v) (hsj : ∀ v ∈ I, ¬ T.Adj j v) : i = j := by
  by_contra h
  rcases T.adj_or_reverse h with hh | hh
  · exact hsi j hj hh
  · exact hsj i hi hh

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

/-- If `A.label i j = m j` for every edge `i → j` inside `I`, for some target assignment `m`, then
`I` has fewer than `16` vertices. -/
theorem good_implies_card_lt_sixteen (I : Finset (Fin k)) (m : Fin k → Fin r)
    (h : ∀ i ∈ I, ∀ j ∈ I, T.Adj i j → A.label i j = m j) : I.card < 16 := by
  by_contra hn
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (show 16 ≤ I.card by omega)
  obtain ⟨i, hi, j, hj, hij, hne⟩ := A.good J hJ m
  exact hne (h i (hJI hi) j (hJI hj) hij)

end GoodLabeling
end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
