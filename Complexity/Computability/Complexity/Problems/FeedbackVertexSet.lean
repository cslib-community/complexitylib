/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.DirectedCycle
public import Complexity.Computability.Complexity.Problems.VertexCover
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.Problems.Graph.VertexColors
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Feedback vertex sets

`FeedbackVertexSet` is Karp's problem FEEDBACK NODE SET [Karp1972], problem GT7 of
[Garey and Johnson][GareyJohnson1979] for directed graphs: given a directed graph `G` and a number
`k`, some set of at most `k` declared vertices meets every directed cycle; that is, removing it
leaves an acyclic graph (`Cslib.Complexity.mem_FeedbackVertexSet_iff_forall_isDirCycle`). Graphs
are read as directed graphs on their declared vertices (`Cslib.Complexity.Graph.IsDirCycle`), so a
self-loop is a cycle of length one, and instances are encoded with the graph (`encGraph`) and `k`
in binary (`encNat`).

`NP` membership uses a list of numbers as the witness, read along the vertex list
(`Cslib.Complexity.colorOf`): the vertices numbered `0` are removed, at most `k` of them, and
every arc between remaining vertices must increase the number. Such a numbering exists exactly
when removing the vertices numbered `0` leaves an acyclic graph, by topological numbering
(`Cslib.Complexity.Graph.isDirAcyclic_iff_exists_rank`), and it can be taken at most the number of
declared vertices.

Hardness is Karp's reduction from `VertexCover` (`VertexCover.toFeedbackVertexSet`): every edge
between distinct vertices becomes two opposite arcs (`VertexCover.bidirect`), so the directed
cycles of length two are the edges, every directed cycle contains an edge, and the feedback vertex
sets are the vertex covers. Since `VertexCover` rejects targets above the number of distinct
declared vertices, such targets are mapped to a fixed graph without feedback vertex set of size
`0`.

## Main definitions

* `Cslib.Complexity.FeedbackVertexSet`.
* `Cslib.Complexity.VertexCover.bidirect`, `Cslib.Complexity.VertexCover.toFeedbackVertexSet`.

## Main results

* `Cslib.Complexity.mem_FeedbackVertexSet_iff_forall_isDirCycle`: the removed vertices meet every
  directed cycle.
* `Cslib.Complexity.FeedbackVertexSet.mem_NP`:
  `FeedbackVertexSet ∈ NP (encPair encGraph encNat)`.
* `Cslib.Complexity.VertexCover.toFeedbackVertexSet_mem_iff`,
  `Cslib.Complexity.VertexCover.computableInPolyTime_toFeedbackVertexSet`,
  `Cslib.Complexity.polyTimeReducible_VertexCover_FeedbackVertexSet`: Karp's reduction.
* `Cslib.Complexity.FeedbackVertexSet_npHard`, `Cslib.Complexity.FeedbackVertexSet_npComplete`:
  `FeedbackVertexSet` is `NP`-complete.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Graph

/-- **Feedback vertex set** [Karp1972] [Garey and Johnson, Problem GT7][GareyJohnson1979]: the
directed graphs with a number `k` such that removing some set of at most `k` declared vertices
leaves no directed cycle. -/
def FeedbackVertexSet : Set (Graph × ℕ) :=
  {x | ∃ R : Finset ℕ, (∀ v ∈ R, v ∈ x.1.1) ∧ R.card ≤ x.2 ∧ (x.1.deleteVerts R).IsDirAcyclic}

theorem mem_FeedbackVertexSet_iff {G : Graph} {k : ℕ} :
    (G, k) ∈ FeedbackVertexSet ↔
      ∃ R : Finset ℕ, (∀ v ∈ R, v ∈ G.1) ∧ R.card ≤ k ∧ (G.deleteVerts R).IsDirAcyclic :=
  Iff.rfl

/-- Membership in `FeedbackVertexSet` through cycles: at most `k` declared vertices meet every
directed cycle. -/
theorem mem_FeedbackVertexSet_iff_forall_isDirCycle {G : Graph} {k : ℕ} :
    (G, k) ∈ FeedbackVertexSet ↔ ∃ R : Finset ℕ, (∀ v ∈ R, v ∈ G.1) ∧ R.card ≤ k ∧
      ∀ c, G.IsDirCycle c → ∃ v ∈ c, v ∈ R := by
  simp only [mem_FeedbackVertexSet_iff, isDirAcyclic_deleteVerts_iff]

namespace FeedbackVertexSet

/-! ### Membership in `NP` -/

/-- The number of distinct declared vertices numbered `0`. -/
private def zeroCount (x : (Graph × ℕ) × List ℕ) : ℕ :=
  x.1.1.distinctVertices.countP fun v => decide (colorOf x.1.1 x.2 v = 0)

/-- The check of one arc under a listed numbering: unless both ends are declared vertices with
nonzero numbers, the arc increases the number. -/
private def arcOK (x : (Graph × ℕ) × List ℕ) (e : ℕ × ℕ) : Bool :=
  !(decide (e.1 ∈ x.1.1.1) && decide (e.2 ∈ x.1.1.1) &&
      decide (colorOf x.1.1 x.2 e.1 ≠ 0) && decide (colorOf x.1.1 x.2 e.2 ≠ 0)) ||
    decide (colorOf x.1.1 x.2 e.1 < colorOf x.1.1 x.2 e.2)

/-- The check of a listed numbering: at most `k` distinct declared vertices are numbered `0`, and
every arc between declared vertices with nonzero numbers increases the number. -/
private def check (x : (Graph × ℕ) × List ℕ) : Bool :=
  decide (zeroCount x ≤ x.1.2) && x.1.1.2.all (arcOK x)

private theorem computableInPolyTime_arcOK :
    ComputableInPolyTime (fun p : ((Graph × ℕ) × List ℕ) × (ℕ × ℕ) => arcOK p.1 p.2)
      (encPair (encPair (encPair encGraph encNat) (encList encNat)) (encPair encNat encNat))
      encBool := by
  have hV : ComputableInPolyTime (fun p : ((Graph × ℕ) × List ℕ) × (ℕ × ℕ) => p.1.1.1.1)
      (encPair (encPair (encPair encGraph encNat) (encList encNat)) (encPair encNat encNat))
      (encList encNat) := by
    unfold encGraph
    fun_prop
  have hG : ComputableInPolyTime (fun p : ((Graph × ℕ) × List ℕ) × (ℕ × ℕ) => p.1.1.1)
      (encPair (encPair (encPair encGraph encNat) (encList encNat)) (encPair encNat encNat))
      encGraph := by
    fun_prop
  have hc : ComputableInPolyTime (fun p : ((Graph × ℕ) × List ℕ) × (ℕ × ℕ) => p.1.2)
      (encPair (encPair (encPair encGraph encNat) (encList encNat)) (encPair encNat encNat))
      (encList encNat) := by
    fun_prop
  have h1 : ComputableInPolyTime (fun p : ((Graph × ℕ) × List ℕ) × (ℕ × ℕ) => p.2.1)
      (encPair (encPair (encPair encGraph encNat) (encList encNat)) (encPair encNat encNat))
      encNat := by
    fun_prop
  have h2 : ComputableInPolyTime (fun p : ((Graph × ℕ) × List ℕ) × (ℕ × ℕ) => p.2.2)
      (encPair (encPair (encPair encGraph encNat) (encList encNat)) (encPair encNat encNat))
      encNat := by
    fun_prop
  have hc1 := computableInPolyTime_colorOf_comp hG hc h1
  have hc2 := computableInPolyTime_colorOf_comp hG hc h2
  have hm1 := decide_mem hV h1
  have hm2 := decide_mem hV h2
  unfold arcOK
  fun_prop

private theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair (encPair encGraph encNat) (encList encNat)) encBool := by
  have hE : ComputableInPolyTime (fun x : (Graph × ℕ) × List ℕ => x.1.1.2)
      (encPair (encPair encGraph encNat) (encList encNat)) (encList (encPair encNat encNat)) := by
    unfold encGraph
    fun_prop
  have hG : ComputableInPolyTime (fun x : (Graph × ℕ) × List ℕ => x.1.1)
      (encPair (encPair encGraph encNat) (encList encNat)) encGraph := by
    fun_prop
  have hz : ComputableInPolyTime zeroCount
      (encPair (encPair encGraph encNat) (encList encNat)) encUnary := by
    unfold zeroCount
    exact countPWithInput (computableInPolyTime_distinctVertices.comp hG) (by fun_prop)
  have hk : ComputableInPolyTime (fun x : (Graph × ℕ) × List ℕ => x.1.2)
      (encPair (encPair encGraph encNat) (encList encNat)) encNat := by
    fun_prop
  exact bool_and.comp ((binary_le' (unary_to_binary.comp hz) hk).prod
    (allWithInput hE computableInPolyTime_arcOK))

/-- The distinct declared vertices numbered `0` are counted by `zeroCount`. -/
private theorem zeroCount_eq (x : (Graph × ℕ) × List ℕ) :
    zeroCount x = (x.1.1.1.toFinset.filter fun v => colorOf x.1.1 x.2 v = 0).card := by
  have hset : x.1.1.distinctVertices.toFinset = x.1.1.1.toFinset := by
    ext v
    simp only [List.mem_toFinset, mem_distinctVertices]
  rw [zeroCount, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((nodup_distinctVertices _).filter _), List.toFinset_filter, hset]
  simp only [decide_eq_true_eq]

private theorem check_iff (x : (Graph × ℕ) × List ℕ) :
    check x = true ↔
      (x.1.1.1.toFinset.filter fun v => colorOf x.1.1 x.2 v = 0).card ≤ x.1.2 ∧
        ∀ e ∈ x.1.1.2, e.1 ∈ x.1.1.1 → e.2 ∈ x.1.1.1 → colorOf x.1.1 x.2 e.1 ≠ 0 →
          colorOf x.1.1 x.2 e.2 ≠ 0 → colorOf x.1.1 x.2 e.1 < colorOf x.1.1 x.2 e.2 := by
  simp only [check, arcOK, zeroCount_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_not]
  refine and_congr_right fun _ => forall₂_congr fun e _ => ?_
  by_cases h1 : e.1 ∈ x.1.1.1 <;> by_cases h2 : e.2 ∈ x.1.1.1 <;>
    by_cases h3 : colorOf x.1.1 x.2 e.1 = 0 <;> by_cases h4 : colorOf x.1.1 x.2 e.2 = 0 <;>
    simp only [h1, h2, h3, h4, not_true, not_false_eq_true, true_or, or_true, false_or, or_false,
      false_implies, forall_const, implies_true, ne_eq]

/-- The witness relation: the number of distinct declared vertices numbered `0` is at most `k`,
and every arc between declared vertices with nonzero numbers increases the number. -/
private def Certifies (x : Graph × ℕ) (ρ : List ℕ) : Prop :=
  (x.1.1.toFinset.filter fun v => colorOf x.1 ρ v = 0).card ≤ x.2 ∧
    ∀ e ∈ x.1.2, e.1 ∈ x.1.1 → e.2 ∈ x.1.1 → colorOf x.1 ρ e.1 ≠ 0 → colorOf x.1 ρ e.2 ≠ 0 →
      colorOf x.1 ρ e.1 < colorOf x.1 ρ e.2

/-- A numbering removing the vertices numbered `0` shows membership. -/
private theorem mem_of_certifies {G : Graph} {k : ℕ} {ρ : List ℕ} (h : Certifies (G, k) ρ) :
    (G, k) ∈ FeedbackVertexSet := by
  obtain ⟨hcard, hρ⟩ := h
  refine ⟨G.1.toFinset.filter fun v => colorOf G ρ v = 0, fun v hv => ?_, hcard,
    isDirAcyclic_of_rank (f := colorOf G ρ) fun u v huv => ?_⟩
  · exact List.mem_toFinset.1 (Finset.mem_filter.1 hv).1
  · rw [dirAdj_deleteVerts] at huv
    obtain ⟨⟨hu, hv, huv⟩, huR, hvR⟩ := huv
    simp only [Finset.mem_filter, List.mem_toFinset, not_and] at huR hvR
    exact hρ (u, v) huv hu hv (huR hu) (hvR hv)

/-- A member has a numbering, at most the number of distinct declared vertices, listed along the
vertex list. -/
private theorem exists_certifies {G : Graph} {k : ℕ} (h : (G, k) ∈ FeedbackVertexSet) :
    ∃ g : ℕ → ℕ, (∀ v ∈ G.1, g v ≤ G.1.toFinset.card) ∧ Certifies (G, k) (G.1.map g) := by
  classical
  obtain ⟨R, hRV, hcard, hacyc⟩ := h
  obtain ⟨f, hflt, hf⟩ := exists_rank_of_isDirAcyclic hacyc
  have hsub : (G.deleteVerts R).1.toFinset.card ≤ G.1.toFinset.card :=
    Finset.card_le_card fun v hv => List.mem_toFinset.2
      (mem_deleteVerts_fst.1 (List.mem_toFinset.1 hv)).1
  refine ⟨fun v => if v ∈ R then 0 else f v + 1, fun v hv => ?_, ?_, fun e he h1 h2 h3 h4 => ?_⟩
  · dsimp only
    split
    · exact Nat.zero_le _
    · exact (hflt v (mem_deleteVerts_fst.2 ⟨hv, ‹_›⟩)).trans_le hsub
  · have hfilter : (G.1.toFinset.filter fun v => colorOf G (G.1.map fun v =>
        if v ∈ R then 0 else f v + 1) v = 0) = R := by
      ext v
      simp only [Finset.mem_filter, List.mem_toFinset]
      constructor
      · rintro ⟨hv, h0⟩
        rw [colorOf_map hv] at h0
        split at h0
        · assumption
        · omega
      · intro hv
        refine ⟨hRV v hv, ?_⟩
        rw [colorOf_map (hRV v hv)]
        simp only [hv, ite_true]
    rw [hfilter]
    exact hcard
  · rw [colorOf_map h1] at h3 ⊢
    rw [colorOf_map h2] at h4 ⊢
    split at h3
    · exact (h3 rfl).elim
    split at h4
    · exact (h4 rfl).elim
    simp only [*, ite_false, Nat.add_lt_add_iff_right]
    have := hf e.1 e.2 (dirAdj_deleteVerts.2 ⟨⟨h1, h2, he⟩, ‹_›, ‹_›⟩)
    omega

/-- `FeedbackVertexSet` belongs to `NP`, with a listed numbering as the witness. -/
theorem mem_NP : FeedbackVertexSet ∈ NP (encPair encGraph encNat) := by
  have hset : FeedbackVertexSet = {x | ∃ ρ : List ℕ, Certifies x ρ} := by
    ext ⟨G, k⟩
    constructor
    · intro h
      obtain ⟨g, -, hg⟩ := exists_certifies h
      exact ⟨_, hg⟩
    · rintro ⟨ρ, hρ⟩
      exact mem_of_certifies hρ
  rw [hset]
  refine mem_NP_of_witness (p := 2 * Polynomial.X ^ 2 + Polynomial.X) (.list .nat)
    computableInPolyTime_check (fun x ρ => check_iff (x, ρ)) ?_
  rintro ⟨G, k⟩ ρ hρ
  obtain ⟨g, hgle, hg⟩ := exists_certifies (mem_of_certifies hρ)
  refine ⟨_, hg, ?_⟩
  have hN : G.1.length ≤ (encPair encGraph encNat (G, k)).length :=
    G.length_vertices_le_encGraph.trans (length_le_encPair_left _ _ (G, k))
  have h := length_encList_map_le hN fun v hv =>
    (hgle v hv).trans (G.1.toFinset_card_le.trans hN)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat]
  exact h

end FeedbackVertexSet

/-! ### Reduction from vertex covers -/

namespace VertexCover

/-- Both arcs of every edge between distinct vertices: the directed graph whose cycles of length
two are the edges. -/
def bidirect (G : Graph) : Graph :=
  (G.1, G.2.filter (fun e => decide (e.1 ≠ e.2)) ++
    (G.2.filter fun e => decide (e.1 ≠ e.2)).map fun e => (e.2, e.1))

/-- The arcs of `bidirect G` join the adjacent declared vertices of `G`. -/
theorem dirAdj_bidirect {G : Graph} {u v : ℕ} :
    (bidirect G).DirAdj u v ↔ u ∈ G.1 ∧ v ∈ G.1 ∧ G.toSimpleGraph.Adj u v := by
  simp only [DirAdj, bidirect, List.mem_append, List.mem_filter, List.mem_map, decide_eq_true_eq,
    Prod.exists, Prod.mk.injEq, toSimpleGraph_adj]
  constructor
  · rintro ⟨hu, hv, ⟨he, hne⟩ | ⟨a, b, ⟨he, hne⟩, rfl, rfl⟩⟩
    · exact ⟨hu, hv, hne, Or.inl he⟩
    · exact ⟨hu, hv, Ne.symm hne, Or.inr he⟩
  · rintro ⟨hu, hv, hne, he | he⟩
    · exact ⟨hu, hv, Or.inl ⟨he, hne⟩⟩
    · exact ⟨hu, hv, Or.inr ⟨v, u, ⟨he, Ne.symm hne⟩, rfl, rfl⟩⟩

/-- **Karp's reduction from `VertexCover`**: keep the target and make every edge two opposite
arcs, or produce a self-loop with target `0` when the target exceeds the number of distinct
declared vertices. -/
def toFeedbackVertexSet (x : Graph × ℕ) : Graph × ℕ :=
  if x.2 ≤ x.1.1.toFinset.card then (bidirect x.1, x.2) else (([0], [(0, 0)]), 0)

/-- **Vertex covers are feedback vertex sets of the bidirected graph.** -/
theorem toFeedbackVertexSet_mem_iff (x : Graph × ℕ) :
    toFeedbackVertexSet x ∈ FeedbackVertexSet ↔ x ∈ VertexCover := by
  obtain ⟨G, k⟩ := x
  rw [mem_VertexCover_iff_exists_card_le, toFeedbackVertexSet]
  split_ifs with hk
  · rw [mem_FeedbackVertexSet_iff]
    constructor
    · rintro ⟨R, hRV, hcard, hacyc⟩
      refine ⟨hk, R, hRV, fun u hu v hv huv => ?_, hcard⟩
      by_contra h
      push Not at h
      refine hacyc [u, v] (isDirCycle_iff.2 ⟨List.cons_ne_nil _ _, ?_, ?_⟩)
      · simpa using huv.ne
      · rw [Cycle.chain_coe_cons]
        simp only [List.cons_append, List.nil_append, List.isChain_cons_cons,
          List.isChain_singleton, and_true]
        exact ⟨dirAdj_deleteVerts.2 ⟨dirAdj_bidirect.2 ⟨hu, hv, huv⟩, h.1, h.2⟩,
          dirAdj_deleteVerts.2 ⟨dirAdj_bidirect.2 ⟨hv, hu, huv.symm⟩, h.2, h.1⟩⟩
    · rintro ⟨-, S, hSV, hS, hcard⟩
      refine ⟨S, hSV, hcard, isDirAcyclic_of_rank (f := fun _ => 0) fun u v huv => ?_⟩
      rw [dirAdj_deleteVerts, dirAdj_bidirect] at huv
      obtain ⟨⟨hu, hv, hadj⟩, huS, hvS⟩ := huv
      exact ((hS u hu v hv hadj).elim huS hvS).elim
  · constructor
    · rintro ⟨R, -, hcard, hacyc⟩
      rw [Nat.le_zero, Finset.card_eq_zero] at hcard
      subst hcard
      refine (hacyc [0] (isDirCycle_iff.2 ⟨List.cons_ne_nil _ _, List.nodup_singleton _, ?_⟩)).elim
      rw [Cycle.chain_singleton]
      exact dirAdj_deleteVerts.2 ⟨⟨List.mem_singleton_self _, List.mem_singleton_self _,
        List.mem_singleton_self _⟩, Finset.notMem_empty _, Finset.notMem_empty _⟩
    · rintro ⟨hk', -⟩
      exact (hk hk').elim

/-- Karp's reduction is polynomial-time: the number of distinct declared vertices is computed in
unary and compared with the binary target. -/
@[fun_prop]
theorem computableInPolyTime_toFeedbackVertexSet :
    ComputableInPolyTime toFeedbackVertexSet (encPair encGraph encNat)
      (encPair encGraph encNat) := by
  have hn : ComputableInPolyTime (fun x : Graph × ℕ => x.1.1.toFinset.card)
      (encPair encGraph encNat) encUnary := by
    simp_rw [← Graph.length_distinctVertices]
    exact (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp (fst _ _))
  have hb : ComputableInPolyTime (fun x : Graph × ℕ => bidirect x.1)
      (encPair encGraph encNat) encGraph := by
    unfold bidirect encGraph
    fun_prop
  have heq : toFeedbackVertexSet = fun x : Graph × ℕ =>
      if decide (x.2 ≤ x.1.1.toFinset.card) then (bidirect x.1, x.2)
      else (([0], [(0, 0)]), 0) := by
    funext x
    simp only [toFeedbackVertexSet, decide_eq_true_eq]
  rw [heq]
  exact ite' (binary_le' (snd _ _) (unary_to_binary.comp hn)) (hb.prod (snd _ _)) (const _)

end VertexCover

/-- `VertexCover` reduces to `FeedbackVertexSet` in polynomial time [Karp1972]. -/
theorem polyTimeReducible_VertexCover_FeedbackVertexSet :
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) VertexCover
      FeedbackVertexSet :=
  ⟨VertexCover.toFeedbackVertexSet, VertexCover.computableInPolyTime_toFeedbackVertexSet,
    fun x => (VertexCover.toFeedbackVertexSet_mem_iff x).symm⟩

/-- `FeedbackVertexSet` is `NP`-hard. -/
theorem FeedbackVertexSet_npHard : NPHard (encPair encGraph encNat) FeedbackVertexSet :=
  VertexCover_npHard.trans polyTimeReducible_VertexCover_FeedbackVertexSet

/-- **Feedback vertex set is NP-complete**, for directed graphs with the target in binary
[Karp1972]. -/
theorem FeedbackVertexSet_npComplete : NPComplete (encPair encGraph encNat) FeedbackVertexSet :=
  ⟨FeedbackVertexSet.mem_NP, FeedbackVertexSet_npHard⟩

end Cslib.Complexity
