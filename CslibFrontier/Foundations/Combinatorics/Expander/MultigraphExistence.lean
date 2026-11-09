/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Multigraph
import CslibFrontier.Foundations.Combinatorics.Expander.Existence

/-!
# Constant-degree expander multigraphs exist

For every `n ≥ 2` there is a connected multigraph on `Fin n` with at most `120 n` edges, each vertex
on at most `120` edges other than self-loops, and expansion `e(G) ≥ n / 18000`
(`Cslib.Multigraph.exists_expander`). It is the multigraph of edges
(`Cslib.RotationMap.edgeEnds`) of the `120`-regular expander `Cslib.RotationMap.expander (Fin n)`,
whose edge expansion is at least `1 / 6000` (`Cslib.RotationMap.le_edgeExpansion_expander`), so
`h(G) |V| / 3 ≤ e(G)` (`Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_minBalancedCut`) gives
the expansion bound. The expanders are obtained non-constructively.

This is the graph family behind the Tseitin lower bounds for resolution and sum-of-squares
(`CslibFrontier.Logics.Propositional.Resolution.TseitinExpander`,
`CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.TseitinExpander`).

## Main results

* `Cslib.Multigraph.exists_expander`: connected multigraphs on `n` vertices with `O(n)` edges,
  constant degree and expansion `Ω(n)`.

## References

* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

public section

namespace Cslib.Multigraph

open Finset

/-- **Constant-degree expander multigraphs exist**: for every `n ≥ 2` there is a connected
multigraph on `n` vertices with at most `120 n` edges, each vertex on at most `120` edges other than
self-loops, and expansion `e(G) ≥ n / 18000`. It is the multigraph of the `120`-regular expander
`Cslib.RotationMap.expander (Fin n)`, with edge expansion at least `1 / 6000`, whose existence is
proved non-constructively. -/
theorem exists_expander (n : ℕ) (hn : 2 ≤ n) :
    ∃ m ≤ 120 * n, ∃ ends : Fin m → Sym2 (Fin n),
      (∀ v, #(incidence ends v) ≤ 120) ∧ (toSimpleGraph ends).Connected ∧
      (n : ℝ) / 18000 ≤ minBalancedCut ends := by
  have : NeZero n := ⟨by omega⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  set G := RotationMap.expander (Fin n)
  let f : Fin (Fintype.card G.edges) ≃ G.edges := (Fintype.equivFin G.edges).symm
  -- the edge expansion is at least `1 / 6000`, so `G` is connected and `e(G) ≥ n / 18000`
  have hh := RotationMap.le_edgeExpansion_expander (Fin n)
  refine ⟨_, ?_, G.edgeEnds ∘ f, fun v => ?_, ?_, ?_⟩
  · rw [Fintype.card_coe, mul_comm]
    simpa using G.card_edges_le
  · rw [card_incidence_comp]
    simpa using G.card_incidence_edgeEnds_le v
  · rw [toSimpleGraph_comp, G.toSimpleGraph_edgeEnds]
    exact G.connected_toSimpleGraph_of_edgeExpansion_pos (by linarith)
  · rw [minBalancedCut_comp]
    have := G.edgeExpansion_mul_card_div_three_le_minBalancedCut
    simp only [Fintype.card_fin] at this
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

end Cslib.Multigraph
