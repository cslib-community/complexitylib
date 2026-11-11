/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Local
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic.Ring

/-!
# Counting the edges of multigraphs

Parallel edges are distinct elements of the edge type throughout. The *underlying simple graph*
(`Cslib.Circuits.Frontier.Multigraph.toSimpleGraph`), with loops and multiplicities discarded,
is the graph in which the Gaussian layouts measure distances, and its degrees are at most those
of the multigraph (`Cslib.Circuits.Frontier.Multigraph.MaxDegreeLE.degree_toSimpleGraph_le`). The
multigraph itself supplies degrees, cuts, and the density of cores.

**Core density** (`Cslib.Circuits.Frontier.Multigraph.core_density`). Let a loopless multigraph
of maximum degree `d` have every vertex of degree at least three, and the ends of every edge of
degrees summing to at least `d + 3`. Give each vertex the weight `d + 3 - deg v`. The weights at
the ends of an edge sum to at most `d + 3`, and a vertex of degree `j + 3 ≤ d` has
`deg v · weight v = (j + 3)(d - j) ≥ 3 d`. So the weighted handshake lemma
(`Cslib.Circuits.Frontier.Multigraph.sum_ncard_incidenceSet_mul`) gives
`3 d |V| ≤ (d + 3) |E|`.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.MaxDegreeLE.degree_toSimpleGraph_le`: the underlying simple
  graph has no larger degrees.
* `Cslib.Circuits.Frontier.Multigraph.ncard_touching_le`: at most `d |S|` edges touch `S`.
* `Cslib.Circuits.Frontier.Multigraph.card_le_mul_card`: at most `d |V|` edges.
* `Cslib.Circuits.Frontier.Multigraph.sum_ncard_incidenceSet_mul`: the weighted handshake lemma.
* `Cslib.Circuits.Frontier.Multigraph.core_density`: the density of cores.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Multigraph

open Set

variable {V E : Type*} {G : Multigraph V E}

/-- **The underlying simple graph has no larger degrees.** Every neighbour of `v` in the
underlying simple graph is the other end of an edge at `v`. -/
theorem MaxDegreeLE.degree_toSimpleGraph_le [Fintype V] [DecidableRel G.toSimpleGraph.Adj]
    [Finite E] {d : ℕ} (h : G.MaxDegreeLE d) (v : V) : G.toSimpleGraph.degree v ≤ d := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset,
    ← ncard_eq_toFinset_card']
  refine (ncard_le_ncard (t := G.otherEnd v '' G.incidenceSet v) fun w hw => ?_).trans
    ((ncard_image_le (toFinite _)).trans (h v))
  obtain ⟨hne, e, he⟩ := toSimpleGraph_adj.mp hw
  refine ⟨e, ?_, ?_⟩ <;> rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact Or.inl hs
  · exact Or.inr ht
  · simp [otherEnd, hs, ht]
  · simp [otherEnd, hs, Ne.symm hne]

/-- In maximum degree `d`, at most `d |S|` edges touch a set of vertices `S`. -/
theorem ncard_touching_le [Finite E] [Finite V] {d : ℕ} (hd : G.MaxDegreeLE d) (S : Set V) :
    (G.touching S).ncard ≤ d * S.ncard := by
  classical
  have := Fintype.ofFinite V
  have heq : G.touching S = ⋃ v ∈ S.toFinset, G.incidenceSet v := by
    ext e
    simp only [mem_touching, mem_toFinset, mem_iUnion, mem_incidenceSet, exists_prop]
    constructor
    · rintro (h | h)
      exacts [⟨_, h, Or.inl rfl⟩, ⟨_, h, Or.inr rfl⟩]
    · rintro ⟨v, hv, rfl | rfl⟩
      exacts [Or.inl hv, Or.inr hv]
  rw [heq, ncard_eq_toFinset_card' S]
  calc _ ≤ ∑ v ∈ S.toFinset, (G.incidenceSet v).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ _v ∈ S.toFinset, d := Finset.sum_le_sum fun v _ => hd v
    _ = d * S.toFinset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- In maximum degree `d`, a multigraph has at most `d |V|` edges. -/
theorem card_le_mul_card [Finite E] [Finite V] {d : ℕ} (hd : G.MaxDegreeLE d) :
    Nat.card E ≤ d * Nat.card V := by
  have h := ncard_touching_le hd (univ : Set V)
  rwa [show G.touching univ = univ by ext; simp [mem_touching], ncard_univ, ncard_univ] at h

/-- **The weighted handshake lemma.** In a finite loopless multigraph, the numbers of edges at
the vertices, weighted by `w`, add up to the sum over the edges of the weights of their ends. -/
theorem sum_ncard_incidenceSet_mul [Fintype V] [Fintype E] (hl : G.Loopless) (w : V → ℕ) :
    ∑ v, (G.incidenceSet v).ncard * w v = ∑ e, (w (G.src e) + w (G.tgt e)) := by
  classical
  have hf (v : V) : (G.incidenceSet v).ncard * w v =
      ∑ e, if G.src e = v ∨ G.tgt e = v then w v else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, ← ncard_coe_finset]
    congr 2
    ext e
    simp [mem_incidenceSet]
  simp_rw [hf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hi (v : V) : (if G.src e = v ∨ G.tgt e = v then w v else 0) =
      (if v = G.src e then w v else 0) + (if v = G.tgt e then w v else 0) := by
    have := hl e
    split_ifs <;> grind
  simp_rw [hi]
  simp [Finset.sum_add_distrib]

/-- **The density of cores.** In a loopless multigraph of maximum degree `d` in which every
vertex has at least three edges and the ends of every edge have at least `d + 3` edges between
them, counted with multiplicity, `3 d |V| ≤ (d + 3) |E|`. -/
theorem core_density [Fintype V] [Fintype E] (hl : G.Loopless) {d : ℕ}
    (hlo : ∀ v, 3 ≤ (G.incidenceSet v).ncard) (hhi : G.MaxDegreeLE d)
    (hadj : ∀ e, d + 3 ≤ (G.incidenceSet (G.src e)).ncard + (G.incidenceSet (G.tgt e)).ncard) :
    3 * d * Fintype.card V ≤ (d + 3) * Fintype.card E := by
  let w (v : V) := d + 3 - (G.incidenceSet v).ncard
  -- With `j + 3` edges at `v` and `d = j + i`, the weight is `i ≥ 3` and
  -- `3 (j + i) ≤ (j + 3) i`.
  have hv (v : V) : 3 * d ≤ (G.incidenceSet v).ncard * w v := by
    obtain ⟨j, hj⟩ : ∃ j, (G.incidenceSet v).ncard = j + 3 :=
      ⟨_, (Nat.sub_add_cancel (hlo v)).symm⟩
    obtain ⟨i, hi⟩ : ∃ i, d = j + i := ⟨d - j, by have := hhi v; omega⟩
    have h3 : 3 ≤ i := by
      have := hhi v
      omega
    dsimp only [w]
    rw [hj, hi, show j + i + 3 - (j + 3) = i by omega]
    calc 3 * (j + i) = j * 3 + 3 * i := by ring
      _ ≤ j * i + 3 * i := Nat.add_le_add_right (Nat.mul_le_mul_left j h3) _
      _ = (j + 3) * i := by ring
  have he (e : E) : w (G.src e) + w (G.tgt e) ≤ d + 3 := by
    have := hadj e
    have := hhi (G.src e)
    have := hhi (G.tgt e)
    dsimp only [w]
    omega
  calc 3 * d * Fintype.card V = ∑ _v : V, 3 * d := by simp [mul_comm]
    _ ≤ ∑ v, (G.incidenceSet v).ncard * w v := Finset.sum_le_sum fun v _ => hv v
    _ = ∑ e, (w (G.src e) + w (G.tgt e)) := sum_ncard_incidenceSet_mul hl w
    _ ≤ ∑ _e : E, (d + 3) := Finset.sum_le_sum fun e _ => he e
    _ = (d + 3) * Fintype.card E := by simp [mul_comm]

end Cslib.Circuits.Frontier.Multigraph
