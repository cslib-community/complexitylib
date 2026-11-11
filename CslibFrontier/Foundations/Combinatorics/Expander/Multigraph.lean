/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Cheeger
public import CslibFrontier.Foundations.Combinatorics.Expander.SimpleGraph
public import CslibFrontier.Foundations.Combinatorics.Multigraph

/-!
# The edges of a rotation map

A `D`-regular multigraph presented by a rotation map `G` (`Cslib.RotationMap`) has an edge for
each unordered pair `{p, G.rot p}` of a dart and its reversal (`Cslib.RotationMap.edges`), joining
the vertices of the two darts (`Cslib.RotationMap.edgeEnds`); a dart fixed by `G.rot` is a
self-loop. This presents `G` as a multigraph given by its ends (`Cslib.Multigraph`), with the
same underlying simple graph (`Cslib.RotationMap.toSimpleGraph_edgeEnds`). The edges between a set
`S` of vertices and its complement are the darts from `S` to its complement
(`Cslib.RotationMap.card_edgeCut_edgeEnds`), so the edge expansion `h(G)` bounds the expansion
`e(G)` of Ben-Sasson and Wigderson: `h(G) |V| / 3 ≤ e(G)`
(`Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_minBalancedCut`), and a rotation map of
positive edge expansion is connected
(`Cslib.RotationMap.connected_toSimpleGraph_of_edgeExpansion_pos`).

## Main definitions

* `Cslib.RotationMap.edges`, `Cslib.RotationMap.edgeEnds`: the edges of a rotation map and their
  ends.

## Main results

* `Cslib.RotationMap.toSimpleGraph_edgeEnds`: the multigraph of the edges has the simple graph of
  the rotation map.
* `Cslib.RotationMap.card_edgeCut_edgeEnds`: the edges leaving a set are the darts leaving it.
* `Cslib.RotationMap.card_incidence_edgeEnds_le`: a vertex has at most `|D|` edges other than
  self-loops.
* `Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_minBalancedCut`: `h(G) |V| / 3 ≤ e(G)`.
* `Cslib.RotationMap.connected_toSimpleGraph_of_edgeExpansion_pos`: positive edge expansion makes
  a rotation map connected.

## References

* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
  (G : RotationMap V D)

/-- The edges of `G`: the unordered pairs `{p, G.rot p}` of a dart and its reversal. A dart fixed
by `G.rot` is a self-loop. -/
def edges : Finset (Sym2 (V × D)) :=
  univ.image fun p => s(p, G.rot p)

/-- The ends of an edge of `G`: the vertices of its two darts. -/
def edgeEnds (e : G.edges) : Sym2 V :=
  e.1.map Prod.fst

/-- Every dart `p` gives the edge `{p, G.rot p}` of `G`. -/
theorem mk_mem_edges (p : V × D) : s(p, G.rot p) ∈ G.edges :=
  mem_image_of_mem _ (mem_univ p)

variable {G} in
/-- Every edge of `G` is `{p, G.rot p}` for some dart `p`. -/
theorem exists_eq_of_mem_edges {e : Sym2 (V × D)} (he : e ∈ G.edges) :
    ∃ p, s(p, G.rot p) = e := by
  simpa [edges] using he

/-- `G` has at most `|V| |D|` edges. -/
theorem card_edges_le : #G.edges ≤ Fintype.card V * Fintype.card D :=
  card_image_le.trans (by rw [card_univ, Fintype.card_prod])

/-- The multigraph of the edges of `G` has the simple graph of `G`. -/
theorem toSimpleGraph_edgeEnds : Multigraph.toSimpleGraph G.edgeEnds = G.toSimpleGraph := by
  ext u v
  rw [Multigraph.toSimpleGraph_adj, toSimpleGraph_adj]
  refine and_congr_right fun _ => ⟨fun ⟨⟨e, he⟩, h⟩ => ?_, fun ⟨i, hi⟩ => ?_⟩
  · obtain ⟨p, rfl⟩ := exists_eq_of_mem_edges he
    change s(p.1, (G.rot p).1) = s(u, v) at h
    rcases Sym2.eq_iff.1 h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine ⟨p.2, ?_⟩
      rw [neighbor, ← h₁, ← h₂]
    · refine ⟨(G.rot p).2, ?_⟩
      rw [neighbor, ← h₂, Prod.mk.eta, rot_rot, h₁]
  · refine ⟨⟨_, G.mk_mem_edges (u, i)⟩, ?_⟩
    change s(u, G.neighbor u i) = s(u, v)
    rw [hi]

/-- The edges between `S` and its complement are the darts from `S` to its complement. -/
theorem card_edgeCut_edgeEnds (S : Finset V) :
    #(Multigraph.edgeCut G.edgeEnds S) = #(G.interedges S Sᶜ) := by
  symm
  refine card_bij (fun p _ => ⟨s(p, G.rot p), G.mk_mem_edges p⟩) (fun p hp => ?_)
    (fun p hp q hq h => ?_) (fun e he => ?_)
  · rw [mem_interedges] at hp
    exact Multigraph.mem_edgeCut.2 ⟨p.1, hp.1, (G.rot p).1, hp.2, rfl⟩
  · rw [mem_interedges] at hp hq
    simp only [Subtype.mk.injEq, Sym2.eq_iff] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · -- `p = G.rot q` leads from `S` to its complement and back
      refine absurd hq.1 (mem_compl.1 ?_)
      have : G.rot p = q := by rw [h, rot_rot]
      rw [← this]
      exact hp.2
  · rcases e with ⟨e, he'⟩
    obtain ⟨v, hv, w, hw, hvw⟩ := Multigraph.mem_edgeCut.1 he
    obtain ⟨p, rfl⟩ := exists_eq_of_mem_edges he'
    change s(p.1, (G.rot p).1) = s(v, w) at hvw
    rcases Sym2.eq_iff.1 hvw with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine ⟨p, mem_interedges.2 ⟨h₁ ▸ hv, ?_⟩, rfl⟩
      change (G.rot p).1 ∈ Sᶜ
      rw [h₂]
      exact hw
    · refine ⟨G.rot p, mem_interedges.2 ⟨h₂ ▸ hv, ?_⟩, Subtype.ext ?_⟩
      · change (G.rot (G.rot p)).1 ∈ Sᶜ
        rw [rot_rot, h₁]
        exact hw
      · change s(G.rot p, G.rot (G.rot p)) = s(p, G.rot p)
        rw [rot_rot, Sym2.eq_swap]

/-- A vertex of `G` has at most `|D|` edges other than self-loops. -/
theorem card_incidence_edgeEnds_le (v : V) :
    #(Multigraph.incidence G.edgeEnds v) ≤ Fintype.card D := by
  have hsub : Multigraph.incidence G.edgeEnds v ⊆
      univ.image fun i : D => (⟨s((v, i), G.rot (v, i)), G.mk_mem_edges _⟩ : G.edges) := by
    intro e he
    rcases e with ⟨e, he'⟩
    obtain ⟨p, rfl⟩ := exists_eq_of_mem_edges he'
    have hv : v ∈ s(p.1, (G.rot p).1) := (Multigraph.mem_incidence.1 he).1
    rcases Sym2.mem_iff.1 hv with h | h
    · refine mem_image.2 ⟨p.2, mem_univ _, Subtype.ext ?_⟩
      simp only [h]
    · refine mem_image.2 ⟨(G.rot p).2, mem_univ _, Subtype.ext ?_⟩
      simp only [h, Prod.mk.eta, rot_rot, Sym2.eq_swap]
  exact (card_le_card hsub).trans (card_image_le.trans card_univ.le)

/-- **Edge expansion bounds the expansion of Ben-Sasson and Wigderson**: `h(G) |V| / 3 ≤ e(G)`. -/
theorem edgeExpansion_mul_card_div_three_le_minBalancedCut :
    G.edgeExpansion * Fintype.card V / 3 ≤ Multigraph.minBalancedCut G.edgeEnds := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [G.edgeExpansion_eq_zero_of_subsingleton]
    simp
  obtain ⟨S, h₁, h₂, hS⟩ := Multigraph.exists_card_edgeCut_eq_minBalancedCut G.edgeEnds
    Fintype.one_lt_card
  rw [← hS, card_edgeCut_edgeEnds]
  exact G.edgeExpansion_mul_card_div_three_le_card_interedges h₁ h₂

omit [DecidableEq D] in
/-- A rotation map of positive edge expansion is connected. -/
theorem connected_toSimpleGraph_of_edgeExpansion_pos (hG : 0 < G.edgeExpansion) :
    G.toSimpleGraph.Connected := by
  classical
  have : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hG.ne' G.edgeExpansion_eq_zero_of_subsingleton
  rw [← toSimpleGraph_edgeEnds]
  refine (Multigraph.connected_toSimpleGraph_iff _).2 ⟨inferInstance, fun S hS hSu => ?_⟩
  rw [← card_pos, card_edgeCut_edgeEnds, ← Nat.cast_pos (α := ℝ)]
  rcases le_or_gt (2 * #S) (Fintype.card V) with h | h
  · have hpos : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
    exact (mul_pos hG hpos).trans_le (G.edgeExpansion_mul_card_le h)
  · have hc := card_add_card_compl S
    have hle : 2 * #Sᶜ ≤ Fintype.card V := by omega
    have hpos : (0 : ℝ) < #Sᶜ := by
      exact_mod_cast (compl_ne_univ_iff_nonempty Sᶜ |>.1 (by rwa [compl_compl])).card_pos
    have := G.edgeExpansion_mul_card_le hle
    rw [compl_compl, card_interedges_comm] at this
    exact (mul_pos hG hpos).trans_le this

end Cslib.RotationMap
