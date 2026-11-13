/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.FeedbackVertexSet
public import CslibFrontier.Computability.Complexity.Problems.Graph.VertexColors
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Feedback arc sets

`FeedbackArcSet` is Karp's problem FEEDBACK ARC SET [Karp1972], problem GT8 of
[Garey and Johnson][GareyJohnson1979]: given a directed graph `G` and a number `k`, removing some
set of at most `k` arcs of `G` leaves no directed cycle (`Cslib.Complexity.Graph.IsDirAcyclic`).
Graphs are read as directed graphs on their declared vertices, so a self-loop is a cycle of length
one, and instances are encoded with the graph (`encGraph`) and `k` in binary (`encNat`)
(`Cslib.Complexity.FeedbackArcSetInstance`, encoded by `Cslib.Complexity.encFeedbackArcSet`).

`NP` membership uses a list of numbers as the witness, read along the vertex list
(`Cslib.Complexity.colorOf`): the arcs between declared vertices that do not increase the number
(`FeedbackArcSet.backArcs`) are removed, and there must be at most `k` distinct ones. Removing them
leaves an acyclic graph, numbered by the witness; conversely, a topological numbering of the graph
left by a feedback arc set (`Cslib.Complexity.Graph.isDirAcyclic_iff_exists_rank`) has all its
back arcs in that set, and it can be taken below the number of declared vertices.

Hardness is a vertex-splitting reduction from `FeedbackVertexSet`
(`FeedbackVertexSet.toFeedbackArcSet`): every vertex `v` becomes an arc `2v → 2v + 1`, and every
arc `u → v` becomes an arc `2u + 1 → 2v` (`FeedbackVertexSet.splitVertices`), with the same `k`.
Every walk passes through the arcs of the vertices it visits, so removing the arcs of a feedback
vertex set leaves an acyclic graph; conversely, removing an arc `2v → 2v + 1` or `2v + 1 → 2w`
can be replaced by removing the vertex `v`.

Attribution: in Karp's reduction tree [Karp1972], FEEDBACK NODE SET and FEEDBACK ARC SET are both
reduced from NODE COVER. His FEEDBACK ARC SET reduction splits the vertices of the node-cover
instance: `⟨u, 0⟩ → ⟨u, 1⟩` for every vertex `u`, and `⟨u, 1⟩ → ⟨v, 0⟩` and `⟨v, 1⟩ → ⟨u, 0⟩` for
every edge `{u, v}`. Here the splitting is generalized to arbitrary directed graphs and factored
through `FeedbackVertexSet`. For a loopless graph `G`, `splitVertices (VertexCover.bidirect G)`
(the graph of `VertexCover.toFeedbackVertexSet`) is Karp's graph with `⟨u, i⟩` numbered `2u + i`.
This account of Karp's construction follows secondary descriptions; it has not been checked
against the printed paper.

## Main definitions

* `Cslib.Complexity.FeedbackArcSetInstance`, `Cslib.Complexity.encFeedbackArcSet`.
* `Cslib.Complexity.FeedbackArcSet`.
* `Cslib.Complexity.FeedbackVertexSet.splitVertices`,
  `Cslib.Complexity.FeedbackVertexSet.toFeedbackArcSet`.

## Main results

* `Cslib.Complexity.FeedbackArcSet.mem_NP`: `FeedbackArcSet ∈ NP encFeedbackArcSet`.
* `Cslib.Complexity.FeedbackVertexSet.toFeedbackArcSet_mem_iff`,
  `Cslib.Complexity.FeedbackVertexSet.computableInPolyTime_toFeedbackArcSet`,
  `Cslib.Complexity.polyTimeReducible_FeedbackVertexSet_FeedbackArcSet`: the reduction.
* `Cslib.Complexity.FeedbackArcSet_npHard`, `Cslib.Complexity.FeedbackArcSet_npComplete`:
  `FeedbackArcSet` is `NP`-complete.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Graph

/-- An instance `(graph, bound)` of **Feedback Arc Set**. -/
@[ext]
structure FeedbackArcSetInstance where
  /-- The directed graph whose directed cycles must be hit. -/
  graph : Graph
  /-- The maximum number of arcs to remove. -/
  bound : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `FeedbackArcSetInstance` as a pair `(graph, bound)`. -/
enc_structure encFeedbackArcSet : FeedbackArcSetInstance where
  graph : encGraph,
  bound : encNat

attribute [fun_prop] encFeedbackArcSet_graph_polyTime encFeedbackArcSet_bound_polyTime
  encFeedbackArcSet_mk_polyTime

/-- **Feedback arc set** [Karp1972] [Garey and Johnson, Problem GT8][GareyJohnson1979]: the
directed graphs with a number `k` such that removing some set of at most `k` arcs leaves no
directed cycle. -/
@[expose]
def FeedbackArcSet : Set FeedbackArcSetInstance :=
  {x | ∃ S : Finset (ℕ × ℕ), (∀ e ∈ S, e ∈ x.graph.edges) ∧ S.card ≤ x.bound ∧
    (x.graph.deleteArcs S).IsDirAcyclic}

theorem mem_FeedbackArcSet_iff {G : Graph} {k : ℕ} :
    (⟨G, k⟩ : FeedbackArcSetInstance) ∈ FeedbackArcSet ↔
      ∃ S : Finset (ℕ × ℕ), (∀ e ∈ S, e ∈ G.edges) ∧ S.card ≤ k ∧ (G.deleteArcs S).IsDirAcyclic :=
  Iff.rfl

namespace FeedbackArcSet

/-! ### Membership in `NP` -/

/-- The arcs between declared vertices that the listed numbering `ρ` does not increase. -/
@[expose]
def backArcs (G : Graph) (ρ : List ℕ) : List (ℕ × ℕ) :=
  G.edges.filter fun e =>
    decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices) &&
      decide (colorOf G ρ e.2 ≤ colorOf G ρ e.1)

theorem mem_backArcs {G : Graph} {ρ : List ℕ} {e : ℕ × ℕ} :
    e ∈ backArcs G ρ ↔ e ∈ G.edges ∧ e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices ∧
      colorOf G ρ e.2 ≤ colorOf G ρ e.1 := by
  simp only [backArcs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- The check of a listed numbering: at most `k` distinct arcs are back arcs. -/
private def check (x : FeedbackArcSetInstance × List ℕ) : Bool :=
  decide ((selectDistinct (backArcs x.1.graph x.2)
    (List.replicate (backArcs x.1.graph x.2).length true)).length ≤ x.1.bound)

private theorem computableInPolyTime_backArcs :
    ComputableInPolyTime (fun x : FeedbackArcSetInstance × List ℕ => backArcs x.1.graph x.2)
      (encPair encFeedbackArcSet (encList encNat)) (encList (encPair encNat encNat)) := by
  unfold backArcs
  exact filterWithInput (encGraph_edges_polyTime (by fun_prop))
    (by fun_prop [encGraph_vertices_polyTime])

private theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair encFeedbackArcSet (encList encNat)) encBool := by
  have hb := computableInPolyTime_backArcs
  have hl : ComputableInPolyTime (fun x : FeedbackArcSetInstance × List ℕ =>
      (selectDistinct (backArcs x.1.graph x.2)
        (List.replicate (backArcs x.1.graph x.2).length true)).length)
      (encPair encFeedbackArcSet (encList encNat)) encUnary :=
    (length_list _).comp ((computableInPolyTime_selectDistinct _).comp
      (hb.prod ((bitsReplicate true).comp ((length_list _).comp hb))))
  have hk : ComputableInPolyTime (fun x : FeedbackArcSetInstance × List ℕ => x.1.bound)
      (encPair encFeedbackArcSet (encList encNat)) encNat := by
    fun_prop
  exact binary_le' (unary_to_binary.comp hl) hk

private theorem check_iff (x : FeedbackArcSetInstance × List ℕ) :
    check x = true ↔ (backArcs x.1.graph x.2).toFinset.card ≤ x.1.bound := by
  rw [check, decide_eq_true_eq, length_selectDistinct_replicate]

/-- The witness relation: at most `k` distinct arcs are back arcs. -/
private def Certifies (x : FeedbackArcSetInstance) (ρ : List ℕ) : Prop :=
  (backArcs x.graph ρ).toFinset.card ≤ x.bound

/-- Removing the back arcs of a numbering leaves an acyclic graph, so a numbering with at most `k`
distinct back arcs shows membership. -/
private theorem mem_of_certifies {G : Graph} {k : ℕ} {ρ : List ℕ} (h : Certifies ⟨G, k⟩ ρ) :
    (⟨G, k⟩ : FeedbackArcSetInstance) ∈ FeedbackArcSet := by
  classical
  refine ⟨(backArcs G ρ).toFinset, fun e he => (mem_backArcs.1 (List.mem_toFinset.1 he)).1, h,
    isDirAcyclic_of_rank (f := colorOf G ρ) fun u v huv => ?_⟩
  rw [dirAdj_deleteArcs, List.mem_toFinset, mem_backArcs] at huv
  obtain ⟨⟨hu, hv, huv⟩, hback⟩ := huv
  by_contra hlt
  exact hback ⟨huv, hu, hv, Nat.le_of_not_lt hlt⟩

/-- A member has a numbering, at most the number of distinct declared vertices, listed along the
vertex list, whose back arcs lie in a feedback arc set. -/
private theorem exists_certifies {G : Graph} {k : ℕ}
    (h : (⟨G, k⟩ : FeedbackArcSetInstance) ∈ FeedbackArcSet) :
    ∃ g : ℕ → ℕ, (∀ v ∈ G.vertices, g v ≤ G.vertices.toFinset.card) ∧
      Certifies ⟨G, k⟩ (G.vertices.map g) := by
  classical
  obtain ⟨S, -, hcard, hacyc⟩ := h
  obtain ⟨f, hflt, hf⟩ := exists_rank_of_isDirAcyclic hacyc
  refine ⟨f, fun v hv => (hflt v hv).le, (Finset.card_le_card fun e he => ?_).trans hcard⟩
  rw [List.mem_toFinset, mem_backArcs] at he
  obtain ⟨he, h1, h2, hle⟩ := he
  rw [colorOf_map h1, colorOf_map h2] at hle
  by_contra hS
  have := hf e.1 e.2 (dirAdj_deleteArcs.2 ⟨⟨h1, h2, he⟩, hS⟩)
  omega

/-- `FeedbackArcSet` belongs to `NP`, with a listed numbering as the witness. -/
theorem mem_NP : FeedbackArcSet ∈ NP encFeedbackArcSet := by
  refine mem_NP_of_colorOf FeedbackArcSetInstance.graph computableInPolyTime_check
    (fun ⟨G, k⟩ => by
      rw [encFeedbackArcSet_apply]
      exact G.length_vertices_le_encGraph.trans (length_le_encPair_left _ _ (G, k)))
    (fun ⟨G, k⟩ ρ h => mem_of_certifies ((check_iff (⟨G, k⟩, ρ)).1 h)) fun ⟨G, k⟩ h => ?_
  obtain ⟨g, hgle, hg⟩ := exists_certifies h
  exact ⟨g, fun v hv => (hgle v hv).trans G.vertices.toFinset_card_le,
    (check_iff (⟨G, k⟩, _)).2 hg⟩

end FeedbackArcSet

/-! ### Reduction from feedback vertex sets -/

namespace FeedbackVertexSet

/-- **Vertex splitting**: every vertex `v` becomes the arc `2v → 2v + 1`, and every arc `u → v`
becomes the arc `2u + 1 → 2v`. -/
@[expose]
def splitVertices (G : Graph) : Graph :=
  ⟨G.vertices.map (2 * ·) ++ G.vertices.map (2 * · + 1),
    G.vertices.map (fun v => (2 * v, 2 * v + 1)) ++ G.edges.map fun e => (2 * e.1 + 1, 2 * e.2)⟩

/-- The arcs of the split graph: the arc `2v → 2v + 1` of a declared vertex `v`, and the arc
`2u + 1 → 2v` of an arc `u → v` between declared vertices. -/
theorem dirAdj_splitVertices {G : Graph} {a b : ℕ} :
    (splitVertices G).DirAdj a b ↔
      (∃ v ∈ G.vertices, a = 2 * v ∧ b = 2 * v + 1) ∨
        ∃ u v, G.DirAdj u v ∧ a = 2 * u + 1 ∧ b = 2 * v := by
  simp only [DirAdj, splitVertices, List.mem_append, List.mem_map, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨ha, hb, ⟨v, hv, rfl, rfl⟩ | ⟨u, v, he, rfl, rfl⟩⟩
    · exact Or.inl ⟨v, hv, rfl, rfl⟩
    · refine Or.inr ⟨u, v, ⟨?_, ?_, he⟩, rfl, rfl⟩
      · obtain ⟨w, hw, h⟩ | ⟨w, hw, h⟩ := ha
        · omega
        · obtain rfl : w = u := by omega
          exact hw
      · obtain ⟨w, hw, h⟩ | ⟨w, hw, h⟩ := hb
        · obtain rfl : w = v := by omega
          exact hw
        · omega
  · rintro (⟨v, hv, rfl, rfl⟩ | ⟨u, v, ⟨hu, hv, he⟩, rfl, rfl⟩)
    · exact ⟨Or.inl ⟨v, hv, rfl⟩, Or.inr ⟨v, hv, rfl⟩, Or.inl ⟨v, hv, rfl, rfl⟩⟩
    · exact ⟨Or.inr ⟨u, hu, rfl⟩, Or.inl ⟨v, hv, rfl⟩, Or.inr ⟨u, v, he, rfl, rfl⟩⟩

/-- A numbering of the split graph after removing the arcs of the vertices of `R`, from a
numbering `f` of the graph after removing `R` bounded by `M`: the arc `2v → 2v + 1` of a remaining
vertex gets `2 f(v) + 1 → 2 f(v) + 2`, and a removed vertex `v` gets `2M + 1` at `2v` and `0` at
`2v + 1`. -/
private def splitRank (R : Finset ℕ) (f : ℕ → ℕ) (M w : ℕ) : ℕ :=
  if w / 2 ∈ R then (if w % 2 = 0 then 2 * M + 1 else 0)
  else (if w % 2 = 0 then 2 * f (w / 2) + 1 else 2 * f (w / 2) + 2)

private theorem splitRank_even (R : Finset ℕ) (f : ℕ → ℕ) (M v : ℕ) :
    splitRank R f M (2 * v) = if v ∈ R then 2 * M + 1 else 2 * f v + 1 := by
  have h1 : 2 * v / 2 = v := by omega
  have h2 : 2 * v % 2 = 0 := by omega
  simp only [splitRank, h1, h2, ↓reduceIte]

private theorem splitRank_odd (R : Finset ℕ) (f : ℕ → ℕ) (M v : ℕ) :
    splitRank R f M (2 * v + 1) = if v ∈ R then 0 else 2 * f v + 2 := by
  have h1 : (2 * v + 1) / 2 = v := by omega
  have h2 : ¬(2 * v + 1) % 2 = 0 := by omega
  simp only [splitRank, h1, h2, ↓reduceIte]

/-- The vertex-splitting reduction: the split graph with the same `k`. -/
@[expose]
def toFeedbackArcSet (x : FeedbackVertexSetInstance) : FeedbackArcSetInstance :=
  ⟨splitVertices x.graph, x.bound⟩

/-- **Feedback vertex sets are feedback arc sets of the split graph.** -/
theorem toFeedbackArcSet_mem_iff (x : FeedbackVertexSetInstance) :
    toFeedbackArcSet x ∈ FeedbackArcSet ↔ x ∈ FeedbackVertexSet := by
  classical
  obtain ⟨G, k⟩ := x
  rw [toFeedbackArcSet, mem_FeedbackArcSet_iff, mem_FeedbackVertexSet_iff]
  constructor
  · rintro ⟨S, -, hcard, hacyc⟩
    obtain ⟨g, -, hg⟩ := exists_rank_of_isDirAcyclic hacyc
    -- Remove the vertices whose arcs `2v → 2v + 1` or `2v + 1 → 2w` were removed.
    refine ⟨(S.image fun e => e.1 / 2).filter (· ∈ G.vertices),
      fun v hv => (Finset.mem_filter.1 hv).2,
      (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans hcard),
      isDirAcyclic_of_rank (f := fun v => g (2 * v + 1)) fun u v huv => ?_⟩
    rw [dirAdj_deleteVerts] at huv
    obtain ⟨⟨hu, hv, he⟩, huR, hvR⟩ := huv
    simp only [Finset.mem_filter, Finset.mem_image, not_and] at huR hvR
    have h1 : (2 * u + 1, 2 * v) ∉ S := fun h => huR ⟨_, h, by simp only; omega⟩ hu
    have h2 : (2 * v, 2 * v + 1) ∉ S := fun h => hvR ⟨_, h, by simp only; omega⟩ hv
    have := hg _ _ (dirAdj_deleteArcs.2 ⟨dirAdj_splitVertices.2 (Or.inr ⟨u, v, ⟨hu, hv, he⟩,
      rfl, rfl⟩), h1⟩)
    have := hg _ _ (dirAdj_deleteArcs.2 ⟨dirAdj_splitVertices.2 (Or.inl ⟨v, hv, rfl, rfl⟩), h2⟩)
    omega
  · rintro ⟨R, hRV, hcard, hacyc⟩
    obtain ⟨f, hflt, hf⟩ := exists_rank_of_isDirAcyclic hacyc
    -- Remove the arcs `2v → 2v + 1` of the removed vertices.
    refine ⟨R.image fun v => (2 * v, 2 * v + 1), fun e he => ?_,
      Finset.card_image_le.trans hcard, isDirAcyclic_of_rank
        (f := splitRank R f (G.deleteVerts R).vertices.toFinset.card) fun a b hab => ?_⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
      exact List.mem_append_left _ (List.mem_map.2 ⟨v, hRV v hv, rfl⟩)
    · rw [dirAdj_deleteArcs, dirAdj_splitVertices] at hab
      obtain ⟨⟨v, hv, rfl, rfl⟩ | ⟨u, v, huv, rfl, rfl⟩, hS⟩ := hab
      · have hvR : v ∉ R := fun h => hS (Finset.mem_image.2 ⟨v, h, rfl⟩)
        simp only [splitRank_even, splitRank_odd, hvR, ↓reduceIte]
        omega
      · rw [splitRank_even, splitRank_odd]
        by_cases huR : u ∈ R
        · simp only [huR, ↓reduceIte]
          split <;> omega
        · have hu := hflt u (mem_deleteVerts_vertices.2 ⟨huv.1, huR⟩)
          by_cases hvR : v ∈ R
          · simp only [huR, hvR, ↓reduceIte]
            omega
          · have := hf u v (dirAdj_deleteVerts.2 ⟨huv, huR, hvR⟩)
            simp only [huR, hvR, ↓reduceIte]
            omega

/-- The vertex-splitting reduction is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toFeedbackArcSet :
    ComputableInPolyTime toFeedbackArcSet encFeedbackVertexSet encFeedbackArcSet := by
  have hs : ComputableInPolyTime (fun x : FeedbackVertexSetInstance => splitVertices x.graph)
      encFeedbackVertexSet encGraph := by
    unfold splitVertices
    fun_prop
  unfold toFeedbackArcSet
  fun_prop

end FeedbackVertexSet

/-- `FeedbackVertexSet` reduces to `FeedbackArcSet` in polynomial time, by vertex splitting.
Karp [Karp1972] instead reduces NODE COVER to FEEDBACK ARC SET by splitting the vertices of the
node-cover instance. This reduction generalizes his splitting to arbitrary directed graphs, and
composing it with `polyTimeReducible_VertexCover_FeedbackVertexSet` recovers his graph. -/
theorem polyTimeReducible_FeedbackVertexSet_FeedbackArcSet :
    PolyTimeReducible encFeedbackVertexSet encFeedbackArcSet FeedbackVertexSet FeedbackArcSet :=
  ⟨FeedbackVertexSet.toFeedbackArcSet, FeedbackVertexSet.computableInPolyTime_toFeedbackArcSet,
    fun x => (FeedbackVertexSet.toFeedbackArcSet_mem_iff x).symm⟩

/-- `FeedbackArcSet` is `NP`-hard. -/
theorem FeedbackArcSet_npHard : NPHard encFeedbackArcSet FeedbackArcSet :=
  FeedbackVertexSet_npHard.trans polyTimeReducible_FeedbackVertexSet_FeedbackArcSet

/-- **Feedback arc set is NP-complete**, for directed graphs with the target in binary
[Karp1972]. -/
theorem FeedbackArcSet_npComplete : NPComplete encFeedbackArcSet FeedbackArcSet :=
  ⟨FeedbackArcSet.mem_NP, FeedbackArcSet_npHard⟩

end Cslib.Complexity
