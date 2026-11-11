/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Generalized Geography

**Generalized Geography**, in the version of [Sipser, Section 8.3][Sipser2013], is played on a
directed graph (`Cslib.Complexity.Graph`: declared vertices and arcs) with a token on a start
vertex. Two players alternately move the token along an arc to a declared vertex that the token has
not visited yet, the start vertex counting as visited; the player who cannot move loses. This is
the vertex version of the game, whose `PSPACE`-completeness is due to Lichtenstein and Sipser
[LichtensteinSipser1980]; in Schaefer's original Generalized Geography the players may not reuse an
arc instead [Schaefer1978].

Every move visits a new declared vertex, so the game is finite, and the winner is determined by
backward induction: with the token at `v` and the vertices `vis` visited, the player to move wins
(`Cslib.Complexity.Graph.GeographyWins`) exactly when some arc from `v` leads to an unvisited
declared vertex `w` from which the other player, now to move, does not win. This is the existence
of a winning strategy for the player to move. `GeneralizedGeography` is the set of graphs with a
start vertex on which the first player wins.

Boundary cases: arcs to undeclared vertices are never used; the start vertex need not be declared,
and it is never revisited; a start vertex without usable arcs is a loss for the first player.

## Main definitions

* `Cslib.Complexity.Graph.GeographyWins`: the player to move wins.
* `Cslib.Complexity.GeneralizedGeographyInstance`: instance `(graph, start)` of Generalized
  Geography.
* `Cslib.Complexity.encGeneralizedGeography`: polynomial-time encoding of
  `GeneralizedGeographyInstance`.
* `Cslib.Complexity.GeneralizedGeography`: the first player wins.

## Main results

* `Cslib.Complexity.Graph.geographyWins_iff`: the backward induction.
* `Cslib.Complexity.Graph.geographyWins_congr`: only the set of visited vertices matters.
* `Cslib.Complexity.Graph.card_sdiff_cons_lt`: every move visits a new declared vertex.
* `Cslib.Complexity.Graph.not_geographyWins_iff`: the player to move loses when every move leads to
  a position won by the other player.
* `Cslib.Complexity.notMem_GeneralizedGeography_of_nil`: on a graph without arcs the first player
  loses.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.3][Sipser2013]
* [D. Lichtenstein, M. Sipser, *GO is polynomial-space hard*][LichtensteinSipser1980]
* [T. J. Schaefer, *On the complexity of some two-person perfect-information games*][Schaefer1978]
-/

public section

namespace Cslib.Complexity

namespace Graph

/-- A move to an unvisited declared vertex leaves fewer unvisited declared vertices. -/
theorem card_sdiff_cons_lt {G : Graph} {vis : List ℕ} {w : ℕ} (hw : w ∈ G.1) (hvis : w ∉ vis) :
    (G.1.toFinset \ (w :: vis).toFinset).card < (G.1.toFinset \ vis.toFinset).card := by
  rw [List.toFinset_cons, Finset.sdiff_insert]
  exact Finset.card_erase_lt_of_mem
    (Finset.mem_sdiff.2 ⟨List.mem_toFinset.2 hw, fun h => hvis (List.mem_toFinset.1 h)⟩)

/-- **Generalized Geography**: with the token at `v` and the vertices `vis` visited, the player
to move wins when some arc from `v` leads to an unvisited declared vertex `w` from which the other
player, to move with `w` visited, does not win. -/
@[expose]
def GeographyWins (G : Graph) (vis : List ℕ) (v : ℕ) : Prop :=
  ∃ w, ∃ _ : (v, w) ∈ G.2 ∧ w ∈ G.1 ∧ w ∉ vis, ¬G.GeographyWins (w :: vis) w
termination_by (G.1.toFinset \ vis.toFinset).card
decreasing_by rename_i h; exact card_sdiff_cons_lt h.2.1 h.2.2

/-- **The backward induction of Generalized Geography.** -/
theorem geographyWins_iff {G : Graph} {vis : List ℕ} {v : ℕ} :
    G.GeographyWins vis v ↔
      ∃ w, (v, w) ∈ G.2 ∧ w ∈ G.1 ∧ w ∉ vis ∧ ¬G.GeographyWins (w :: vis) w := by
  rw [GeographyWins]
  simp only [exists_prop, and_assoc]

/-- The player to move loses exactly when every move leads to a position won by the other
player. -/
theorem not_geographyWins_iff {G : Graph} {vis : List ℕ} {v : ℕ} :
    ¬G.GeographyWins vis v ↔
      ∀ w, (v, w) ∈ G.2 → w ∈ G.1 → w ∉ vis → G.GeographyWins (w :: vis) w := by
  rw [geographyWins_iff]
  simp only [not_exists, not_and, not_not]

/-- **Only the set of visited vertices matters.** -/
theorem geographyWins_congr {G : Graph} {vis vis' : List ℕ} (h : ∀ u, u ∈ vis ↔ u ∈ vis')
    (v : ℕ) : G.GeographyWins vis v ↔ G.GeographyWins vis' v := by
  suffices ∀ n (vis vis' : List ℕ), (G.1.toFinset \ vis.toFinset).card < n →
      (∀ u, u ∈ vis ↔ u ∈ vis') → ∀ v, G.GeographyWins vis v → G.GeographyWins vis' v from
    ⟨this _ vis vis' (Nat.lt_succ_self _) h v,
      this _ vis' vis (Nat.lt_succ_self _) (fun u => (h u).symm) v⟩
  intro n
  induction n with
  | zero => intro _ _ hn; exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro vis vis' hn h v hwin
    obtain ⟨w, hvw, hw, hwvis, hlose⟩ := geographyWins_iff.1 hwin
    refine geographyWins_iff.2 ⟨w, hvw, hw, fun h' => hwvis ((h w).2 h'), fun hwin' => hlose ?_⟩
    have hlt := card_sdiff_cons_lt hw hwvis
    refine ih (w :: vis') (w :: vis) ?_ (fun u => ?_) w hwin'
    · have hcard :
          (G.1.toFinset \ (w :: vis').toFinset) = (G.1.toFinset \ (w :: vis).toFinset) := by
        ext u
        simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, h]
      rw [hcard]
      omega
    · simp only [List.mem_cons, h]

end Graph

/-- An instance `(graph, start)` of **Generalized Geography**. -/
@[ext]
structure GeneralizedGeographyInstance where
  /-- The directed graph on which the game is played. -/
  graph : Graph
  /-- The starting vertex of the token. -/
  start : ℕ
  deriving DecidableEq, Repr

/-- Encoding of `GeneralizedGeographyInstance` as a pair `(graph, start)`. -/
enc_structure encGeneralizedGeography : GeneralizedGeographyInstance where
  graph : encGraph,
  start : Turing.MultiTapeTM.encNat

attribute [fun_prop] encGeneralizedGeography_graph_polyTime
  encGeneralizedGeography_start_polyTime encGeneralizedGeography_mk_polyTime

/-- **Generalized Geography**, vertex version [Sipser, Section 8.3][Sipser2013]
[LichtensteinSipser1980]: the graphs with a start vertex on which the first player wins, moving
first with the token on the start vertex, when no vertex may be visited twice. -/
@[expose]
def GeneralizedGeography : Set GeneralizedGeographyInstance :=
  {x | x.graph.GeographyWins [x.start] x.start}

theorem mem_GeneralizedGeography {x : GeneralizedGeographyInstance} :
    x ∈ GeneralizedGeography ↔ x.graph.GeographyWins [x.start] x.start :=
  Iff.rfl

/-- On a graph without arcs the first player cannot move and loses. -/
theorem notMem_GeneralizedGeography_of_nil {V : List ℕ} {s : ℕ} :
    (⟨(V, []), s⟩ : GeneralizedGeographyInstance) ∉ GeneralizedGeography := by
  rw [mem_GeneralizedGeography, Graph.geographyWins_iff]
  simp

end Cslib.Complexity
