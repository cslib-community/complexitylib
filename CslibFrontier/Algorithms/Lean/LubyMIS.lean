/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Iteration
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.UniformOrder
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Luby's randomized maximal independent set algorithm

Luby's algorithm [Luby1986] finds a maximal independent set of a graph in phases; Alon, Babai and
Itai [AlonBabaiItai1986] gave a closely related randomized parallel algorithm at the same time.
This module formalizes the random-priority variant of Métivier, Robson, Saheb-Djahromi and Zemmari
[MetivierRobsonSahebDjahromiZemmari2011], in the form of Algorithm 7.12 ("Fast MIS 2") of
[Wattenhofer2016]. In each phase:

1. every live vertex draws a random priority;
2. every live vertex whose priority is below those of all its live neighbours joins the set;
3. the joined vertices and their neighbours stop being live.

The algorithm is a `ProbComp` program. `phase` draws a uniform ranking of the vertices (a uniform
random permutation, `ProbComp.uniform (Ranking V)`) and takes the deterministic `step`. `run k`
iterates `phase` `k` times from `init`, where nothing is chosen and every vertex is live
(`OracleComp.iterate`), and `lubyMIS k` answers the chosen set. All probability statements are
about the law `ProbComp.eval`.

## Source conventions

* **Priorities.** The source draws an independent real `r(v) ∈ [0, 1]` for every vertex. Here
  every phase draws one uniform ranking `σ : V ≃ Fin (card V)` and compares ranks. Restricted to
  the live vertices, a uniform ranking orders them uniformly at random, which is the law of the
  order of independent continuous priorities (ties have probability zero there). This
  equivalence is not formalized; the analysis below is carried out for the ranking directly.
* **Model.** This is a centralized simulation of the synchronous phases. It formalizes the
  state transition of a phase, not a LOCAL message-passing algorithm: messages, the rounds inside
  a phase and per-vertex views are not modelled.
* **Running time.** The source proves that one phase removes at least half the live edges in
  expectation ([Wattenhofer2016], Lemma 7.14), derives an expected bound of
  `3 log_{4/3} m + 1` phases (Theorem 7.15) and an `O(log n)` bound with high probability by a
  Chernoff argument (Corollary 7.18). Here the edge-removal lemma is formalized, and the high
  probability bound is proved instead by iterating it and applying Markov's inequality to the
  number of live edges: `O(log n)` phases with explicit constants, failure at most `n ^ (-c)` after
  `(c + 2) ⌈log₂ n⌉ + 1` phases. The expected number of phases (Theorem 7.15) is not formalized.
* **Luby's original algorithm**, in the form of Algorithm 7.6 ("Fast MIS") of [Wattenhofer2016]
  (each vertex marks itself with probability `1 / (2 d(v))` and joins unless a marked neighbour
  has higher degree), its pairwise-independent analysis and its derandomization are not
  formalized.

## Main definitions

* `Cslib.Algorithms.Lean.LubyMIS.State`: the chosen vertices and the live vertices.
* `Cslib.Algorithms.Lean.LubyMIS.liveGraph`, `liveEdges`: the graph on the live vertices and its
  number of edges.
* `Cslib.Algorithms.Lean.LubyMIS.Ranking`: rankings of the vertices.
* `Cslib.Algorithms.Lean.LubyMIS.joiners`, `step`: the vertices that join under a ranking, and the
  resulting state.
* `Cslib.Algorithms.Lean.LubyMIS.phase`, `run`, `lubyMIS`: one phase, `k` phases, and the chosen
  set after `k` phases.
* `Cslib.Algorithms.Lean.LubyMIS.Invariant`: the invariant of the chosen and live sets.

## Main results

* `isIndepSet_of_mem_support_lubyMIS`: after any number of phases, every possible output is an
  independent set.
* `Invariant.maximal_iff`, `maximal_of_mem_support_lubyMIS`: the chosen set is maximal exactly
  when no vertex is live, which holds for every outcome after `k ≥ card V` phases.
* `two_mul_expect_liveEdges_phase_le`: one phase keeps at most half the live edges in expectation
  ([Wattenhofer2016], Lemma 7.14), from the counting form `two_mul_sum_liveEdges_step_le`.
* `two_pow_mul_expect_liveEdges_run_le`: after `k` phases, at most `|E| / 2 ^ k` live edges
  remain in expectation.
* `two_pow_mul_toOuterMeasure_live_nonempty_le`: after `k + 1` phases, the algorithm is still
  running with probability at most `|E| / 2 ^ k`.
* `toOuterMeasure_not_maximal_lubyMIS_le`, `one_sub_le_toOuterMeasure_maximal_lubyMIS`: if
  `|E| ≤ 2 ^ m`, then after `m + t + 1` phases the output is a maximal independent set with
  probability at least `1 - 2 ^ (-t)`; `_clog` and `_card` instantiate `m` with `⌈log₂ |E|⌉` and
  `2 ⌈log₂ n⌉`.
* `toOuterMeasure_not_maximal_lubyMIS_le_inv_pow`: after `(c + 2) ⌈log₂ n⌉ + 1` phases, the
  output fails to be maximal with probability at most `n ^ (-c)`.

## References

* [Luby1986]
* [AlonBabaiItai1986]
* [MetivierRobsonSahebDjahromiZemmari2011]
* [Wattenhofer2016], Chapter 7, Section 7.3
-/

public section

namespace Cslib.Algorithms.Lean.LubyMIS

open Finset
open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The state of Luby's algorithm: the vertices chosen so far and the live vertices. -/
structure State (V : Type) where
  /-- The vertices chosen so far. -/
  chosen : Finset V
  /-- The live vertices: neither chosen nor adjacent to a chosen vertex. -/
  live : Finset V

/-- The live graph: the edges of `G` between live vertices, on the whole vertex type. It is
`(G.induce L).spanningCoe` (`liveGraph_eq_spanningCoe_induce`), stated directly so that its
adjacency is decidable and unfolds by `Iff.rfl`. -/
@[expose] def liveGraph (L : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ L ∧ v ∈ L
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem liveGraph_adj {L : Finset V} {u v : V} :
    (liveGraph G L).Adj u v ↔ G.Adj u v ∧ u ∈ L ∧ v ∈ L := Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The live graph is the induced subgraph on the live vertices, viewed on all of `V`. -/
theorem liveGraph_eq_spanningCoe_induce (L : Finset V) :
    liveGraph G L = (G.induce (L : Set V)).spanningCoe := by
  ext u v
  simp only [liveGraph_adj, SimpleGraph.map_adj, SimpleGraph.comap_adj,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨h, hu, hv⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, h, rfl, rfl⟩
  · rintro ⟨⟨u', hu⟩, ⟨v', hv⟩, h, rfl, rfl⟩
    exact ⟨h, hu, hv⟩

instance (L : Finset V) : DecidableRel (liveGraph G L).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u ∈ L ∧ v ∈ L))

/-- The number of live edges: edges of `G` with both endpoints live. -/
@[expose] def liveEdges (s : State V) : ℕ := (liveGraph G s.live).edgeFinset.card

/-- A ranking: a bijection of the vertices with `{0, …, n - 1}`. A uniform ranking is a uniform
random permutation of the vertices. -/
abbrev Ranking (V : Type) [Fintype V] := V ≃ Fin (Fintype.card V)

instance : Nonempty (Ranking V) := ⟨Fintype.equivFin V⟩

/-- The live vertices that rank below all their live neighbours. -/
@[expose] def joiners (s : State V) (σ : Ranking V) : Finset V :=
  {v ∈ s.live | ∀ w ∈ s.live, G.Adj v w → σ v < σ w}

/-- One phase with ranking `σ`: the joiners are chosen, and they and their neighbours stop being
live. -/
@[expose] def step (s : State V) (σ : Ranking V) : State V where
  chosen := s.chosen ∪ joiners G s σ
  live := {v ∈ s.live | v ∉ joiners G s σ ∧ ∀ u ∈ joiners G s σ, ¬ G.Adj u v}

/-- One phase of Luby's algorithm: draw a uniform ranking and take the step. -/
noncomputable def phase (s : State V) : ProbComp (State V) := do
  let σ ← ProbComp.uniform (Ranking V)
  return step G s σ

/-- The initial state: nothing chosen, every vertex live. -/
@[expose] def init : State V := ⟨∅, univ⟩

/-- `k` phases of Luby's algorithm from the initial state. -/
noncomputable def run (k : ℕ) : ProbComp (State V) :=
  OracleComp.iterate k (phase G) init

/-- The set chosen by `k` phases of Luby's algorithm. -/
noncomputable def lubyMIS (k : ℕ) : ProbComp (Finset V) :=
  State.chosen <$> run G k

theorem run_zero : run G 0 = pure (init : State V) := by
  simp only [run, OracleComp.iterate_zero]

theorem run_succ (k : ℕ) : run G (k + 1) = run G k >>= phase G := by
  simp only [run, OracleComp.iterate_succ]

theorem mem_joiners {s : State V} {σ : Ranking V} {v : V} :
    v ∈ joiners G s σ ↔ v ∈ s.live ∧ ∀ w ∈ s.live, G.Adj v w → σ v < σ w := by
  simp only [joiners, mem_filter]

theorem step_chosen (s : State V) (σ : Ranking V) :
    (step G s σ).chosen = s.chosen ∪ joiners G s σ := rfl

theorem mem_step_live {s : State V} {σ : Ranking V} {v : V} :
    v ∈ (step G s σ).live ↔
      v ∈ s.live ∧ v ∉ joiners G s σ ∧ ∀ u ∈ joiners G s σ, ¬ G.Adj u v := by
  simp only [step, mem_filter]

theorem step_live_subset (s : State V) (σ : Ranking V) : (step G s σ).live ⊆ s.live :=
  fun _ hv => ((mem_step_live G).1 hv).1

/-- The law of one phase: the step under a uniform ranking. -/
theorem eval_phase (s : State V) :
    ProbComp.eval (phase G s) =
      (Probability.PMF.uniformOfFintype (Ranking V)).map (step G s) := by
  rw [phase, ProbComp.eval_bind, ProbComp.eval_uniform]
  rfl

/-! ### Correctness -/

/-- The invariant of Luby's algorithm. -/
structure Invariant (s : State V) : Prop where
  /-- The chosen vertices are independent. -/
  isIndepSet : G.IsIndepSet (s.chosen : Set V)
  /-- A live vertex is neither chosen nor adjacent to a chosen vertex. -/
  disjoint : ∀ v ∈ s.live, ∀ u ∈ s.chosen, ¬ G.Adj u v ∧ u ≠ v
  /-- A vertex that is not live is chosen or adjacent to a chosen vertex. -/
  dominated : ∀ v, v ∉ s.live → v ∈ s.chosen ∨ ∃ u ∈ s.chosen, G.Adj u v

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem invariant_init : Invariant G (init : State V) where
  isIndepSet := by simp [init]
  disjoint := by simp [init]
  dominated := by simp [init]

/-- A phase preserves the invariant, whatever the ranking. -/
theorem Invariant.step {s : State V} (h : Invariant G s) (σ : Ranking V) :
    Invariant G (LubyMIS.step G s σ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu v hv huv hadj
    rw [mem_coe, step_chosen, mem_union] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact h.isIndepSet hu hv huv hadj
    · exact (h.disjoint v ((mem_joiners G).1 hv).1 u hu).1 hadj
    · exact (h.disjoint u ((mem_joiners G).1 hu).1 v hv).1 hadj.symm
    · have h1 := ((mem_joiners G).1 hu).2 v ((mem_joiners G).1 hv).1 hadj
      have h2 := ((mem_joiners G).1 hv).2 u ((mem_joiners G).1 hu).1 hadj.symm
      exact lt_asymm h1 h2
  · intro v hv u hu
    rw [mem_step_live] at hv
    rw [step_chosen, mem_union] at hu
    rcases hu with hu | hu
    · exact h.disjoint v hv.1 u hu
    · exact ⟨hv.2.2 u hu, fun huv => hv.2.1 (huv ▸ hu)⟩
  · intro v hv
    rw [mem_step_live] at hv
    simp only [not_and, not_forall, not_not] at hv
    rw [step_chosen, mem_union]
    by_cases hL : v ∈ s.live
    · by_cases hJ : v ∈ joiners G s σ
      · exact Or.inl (Or.inr hJ)
      · obtain ⟨u, hu, hadj⟩ := hv hL hJ
        exact Or.inr ⟨u, mem_union_right _ hu, hadj⟩
    · rcases h.dominated v hL with hv | ⟨u, hu, hadj⟩
      · exact Or.inl (Or.inl hv)
      · exact Or.inr ⟨u, mem_union_left _ hu, hadj⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A chosen set satisfying the invariant is maximal exactly when no vertex is live. -/
theorem Invariant.maximal_iff {s : State V} (h : Invariant G s) :
    Maximal G.IsIndepSet (s.chosen : Set V) ↔ s.live = ∅ := by
  constructor
  · intro hmax
    by_contra hne
    obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.2 hne
    have hind : G.IsIndepSet (insert v (s.chosen : Set V)) := by
      refine Set.pairwise_insert.2 ⟨h.isIndepSet, fun u hu _ => ⟨fun hvu => ?_, fun huv => ?_⟩⟩
      · exact (h.disjoint v hv u hu).1 hvu.symm
      · exact (h.disjoint v hv u hu).1 huv
    have := hmax.2 hind (Set.subset_insert _ _) (Set.mem_insert v _)
    exact (h.disjoint v hv v this).2 rfl
  · intro hlive
    refine ⟨h.isIndepSet, fun t ht hst w hw => ?_⟩
    rcases h.dominated w (by simp [hlive]) with hw' | ⟨u, hu, hadj⟩
    · exact hw'
    · exact absurd hadj (ht (hst hu) hw (fun huw => G.loopless.irrefl u (huw ▸ hadj)))

/-- Every possible state after any number of phases satisfies the invariant. -/
theorem invariant_of_mem_support_run {k : ℕ} {s : State V}
    (hs : s ∈ (ProbComp.eval (run G k)).support) : Invariant G s :=
  ProbComp.iterate_invariant k (phase G) init (fun _ s => Invariant G s) (invariant_init G)
    (fun _ _ s hs next hnext => by
      rw [eval_phase, PMF.support_map] at hnext
      obtain ⟨σ, -, rfl⟩ := hnext
      exact hs.step G σ) s hs

/-- Each phase with a live vertex removes at least one live vertex: the live vertex of least rank
joins. -/
theorem card_step_live_lt {s : State V} (hs : s.live.Nonempty) (σ : Ranking V) :
    (step G s σ).live.card < s.live.card := by
  obtain ⟨v, hv, hmin⟩ := s.live.exists_min_image σ hs
  have hJ : v ∈ joiners G s σ := (mem_joiners G).2 ⟨hv, fun w hw hadj =>
    lt_of_le_of_ne (hmin w hw) (fun h => G.loopless.irrefl v (σ.injective h ▸ hadj))⟩
  refine card_lt_card ⟨step_live_subset G s σ, fun hsub => ?_⟩
  exact ((mem_step_live G).1 (hsub hv)).2.1 hJ

/-- **Las Vegas correctness.** After `k ≥ card V` phases, every possible output is a maximal
independent set. -/
theorem maximal_of_mem_support_lubyMIS {k : ℕ} (hk : Fintype.card V ≤ k) {S : Finset V}
    (hS : S ∈ (ProbComp.eval (lubyMIS G k)).support) :
    Maximal G.IsIndepSet (S : Set V) := by
  rw [lubyMIS, ProbComp.eval_map, PMF.support_map] at hS
  obtain ⟨s, hs, rfl⟩ := hS
  refine (invariant_of_mem_support_run G hs).maximal_iff.2 ?_
  -- Until the live set empties, each phase removes a live vertex.
  have hcard := ProbComp.iterate_invariant k (phase G) init
    (fun i s => s.live = ∅ ∨ s.live.card + i ≤ Fintype.card V) (Or.inr (by simp [init]))
    (fun i _ s hs next hnext => by
      rw [eval_phase, PMF.support_map] at hnext
      obtain ⟨σ, -, rfl⟩ := hnext
      rcases s.live.eq_empty_or_nonempty with he | hne
      · exact Or.inl (subset_empty.1 (he ▸ step_live_subset G s σ))
      · rcases hs with he | hs
        · exact absurd he hne.ne_empty
        · have := card_step_live_lt G hne σ
          exact Or.inr (by omega)) s hs
  rcases hcard with he | hcard
  · exact he
  · exact card_eq_zero.1 (by omega)

/-- **Independence.** After any number of phases, every possible output is an independent set. -/
theorem isIndepSet_of_mem_support_lubyMIS {k : ℕ} {S : Finset V}
    (hS : S ∈ (ProbComp.eval (lubyMIS G k)).support) : G.IsIndepSet (S : Set V) := by
  rw [lubyMIS, ProbComp.eval_map, PMF.support_map] at hS
  obtain ⟨s, hs, rfl⟩ := hS
  exact (invariant_of_mem_support_run G hs).isIndepSet

/-! ### Random rankings -/

/-- In a uniform ranking, each vertex of a nonempty set `S` is the least of `S` with probability
`1 / |S|`: exactly `(card V)! / |S|` rankings put `u` first among `S`. -/
theorem card_filter_least_mul_card {S : Finset V} {u : V} (hu : u ∈ S) :
    (univ.filter fun σ : Ranking V => ∀ w ∈ S, w ≠ u → σ u < σ w).card * S.card =
      Fintype.card (Ranking V) :=
  Cslib.Probability.card_filter_least_mul_card hu

/-! ### Progress -/

section Progress

variable (s : State V)

/-- The per-vertex accounting of [Wattenhofer2016], Lemma 7.14: if some live neighbour `u` of a
live vertex `v` ranks least on `N(u) ∪ N(v)`, then `u` joins and `v` loses all its live edges, and
at most one neighbour can rank least there. -/
private theorem degree_step_add_le (σ : Ranking V) (v : V) :
    (liveGraph G (step G s σ).live).degree v +
        ∑ u ∈ (liveGraph G s.live).neighborFinset v,
          (if ∀ w ∈ (liveGraph G s.live).neighborFinset u ∪ (liveGraph G s.live).neighborFinset v,
              w ≠ u → σ u < σ w then (liveGraph G s.live).degree v else 0) ≤
      (liveGraph G s.live).degree v := by
  set H := liveGraph G s.live
  set H' := liveGraph G (step G s σ).live
  set W : V → Prop := fun u => ∀ w ∈ H.neighborFinset u ∪ H.neighborFinset v, w ≠ u → σ u < σ w
  have hsub : H'.neighborFinset v ⊆ H.neighborFinset v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact ⟨hw.1, step_live_subset G s σ hw.2.1, step_live_subset G s σ hw.2.2⟩
  have hdeg : H'.degree v ≤ H.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    exact card_le_card hsub
  by_cases hex : ∃ u ∈ H.neighborFinset v, W u
  · obtain ⟨u, hu, hW⟩ := hex
    rw [SimpleGraph.mem_neighborFinset] at hu
    -- `u` joins,
    have hJ : u ∈ joiners G s σ := by
      refine (mem_joiners G).2 ⟨hu.2.2, fun w hw hadj => hW w ?_ ?_⟩
      · exact mem_union_left _ ((SimpleGraph.mem_neighborFinset _ _ _).2 ⟨hadj, hu.2.2, hw⟩)
      · rintro rfl; exact G.loopless.irrefl _ hadj
    -- so `v` is not live afterwards.
    have hv' : v ∉ (step G s σ).live := fun hv =>
      ((mem_step_live G).1 hv).2.2 u hJ hu.1.symm
    have hdeg0 : H'.degree v = 0 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_zero, eq_empty_iff_forall_notMem]
      intro w hw
      exact hv' ((SimpleGraph.mem_neighborFinset _ _ _).1 hw).2.1
    have hu' : u ∈ H.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).2 hu
    rw [hdeg0, zero_add, sum_eq_single_of_mem u hu']
    · rw [ite_eq_left hW]
    · intro u' hu'' hne
      rw [ite_eq_right]
      intro hW'
      have h1 : σ u < σ u' := hW u' (mem_union_right _ hu'') hne
      have h2 : σ u' < σ u := hW' u (mem_union_right _ hu') (Ne.symm hne)
      exact lt_asymm h1 h2
  · push Not at hex
    rw [sum_eq_zero fun u hu => ite_eq_right (hex u hu), add_zero]
    exact hdeg

/-- **Edge removal** ([Wattenhofer2016], Lemma 7.14), counting form: summed over all rankings, a
phase keeps at most half of the live edges. -/
theorem two_mul_sum_liveEdges_step_le :
    2 * ∑ σ : Ranking V, liveEdges G (step G s σ) ≤
      Fintype.card (Ranking V) * liveEdges G s := by
  set H := liveGraph G s.live
  set N := Fintype.card (Ranking V)
  set W : Ranking V → V → V → Prop :=
    fun σ u v => ∀ w ∈ H.neighborFinset u ∪ H.neighborFinset v, w ≠ u → σ u < σ w
  -- For each ranking, the kept edges and the counted removals fit in the live edges.
  have hper : ∀ σ : Ranking V, 2 * liveEdges G (step G s σ) +
      ∑ v, ∑ u ∈ H.neighborFinset v, (if W σ u v then H.degree v else 0) ≤ 2 * liveEdges G s := by
    intro σ
    rw [liveEdges, liveEdges, ← SimpleGraph.sum_degrees_eq_twice_card_edges,
      ← SimpleGraph.sum_degrees_eq_twice_card_edges, ← sum_add_distrib]
    exact sum_le_sum fun v _ => degree_step_add_le G s σ v
  -- The counted removals, summed over rankings: `a u v` rankings put `u` first on `N(u) ∪ N(v)`.
  set a : V → V → ℕ := fun u v => (univ.filter fun σ : Ranking V => W σ u v).card
  have hT : ∑ σ : Ranking V, ∑ v, ∑ u ∈ H.neighborFinset v, (if W σ u v then H.degree v else 0) =
      ∑ v, ∑ u ∈ H.neighborFinset v, a u v * H.degree v := by
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [← sum_filter, sum_const, smul_eq_mul]
  have haS : ∀ u v, H.Adj u v → a u v * (H.degree u + H.degree v) ≥ N := by
    intro u v huv
    have hu : u ∈ H.neighborFinset u ∪ H.neighborFinset v :=
      mem_union_right _ ((SimpleGraph.mem_neighborFinset _ _ _).2 huv.symm)
    calc N = a u v * (H.neighborFinset u ∪ H.neighborFinset v).card :=
          (card_filter_least_mul_card hu).symm
      _ ≤ a u v * (H.degree u + H.degree v) := by
          refine Nat.mul_le_mul_left _ ?_
          rw [← SimpleGraph.card_neighborFinset_eq_degree,
            ← SimpleGraph.card_neighborFinset_eq_degree]
          exact card_union_le _ _
  have hsym : ∀ u v, H.Adj u v → a u v = a v u := by
    intro u v huv
    have hu : u ∈ H.neighborFinset u ∪ H.neighborFinset v :=
      mem_union_right _ ((SimpleGraph.mem_neighborFinset _ _ _).2 huv.symm)
    have hv : v ∈ H.neighborFinset v ∪ H.neighborFinset u :=
      mem_union_right _ ((SimpleGraph.mem_neighborFinset _ _ _).2 huv)
    have h1 := card_filter_least_mul_card hu
    have h2 : a v u * (H.neighborFinset u ∪ H.neighborFinset v).card =
        Fintype.card (Ranking V) := by
      rw [union_comm]
      exact card_filter_least_mul_card hv
    have hpos : 0 < (H.neighborFinset u ∪ H.neighborFinset v).card := card_pos.2 ⟨u, hu⟩
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  -- The counted removals total at least `N` times the live edges.
  have hTlow : N * liveEdges G s ≤ ∑ v, ∑ u ∈ H.neighborFinset v, a u v * H.degree v := by
    have hswap : ∑ v, ∑ u ∈ H.neighborFinset v, a u v * H.degree v =
        ∑ v, ∑ u ∈ H.neighborFinset v, a u v * H.degree u := by
      simp only [SimpleGraph.neighborFinset_eq_filter, sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun v _ => sum_congr rfl fun u _ => ?_
      by_cases huv : H.Adj v u
      · rw [ite_eq_left huv, ite_eq_left huv.symm, hsym u v huv.symm]
      · rw [ite_eq_right huv, ite_eq_right fun h => huv h.symm]
    have h2 : 2 * (N * liveEdges G s) ≤
        2 * ∑ v, ∑ u ∈ H.neighborFinset v, a u v * H.degree v := by
      calc 2 * (N * liveEdges G s) = ∑ v, ∑ _u ∈ H.neighborFinset v, N := by
            rw [liveEdges, mul_left_comm, ← SimpleGraph.sum_degrees_eq_twice_card_edges, mul_sum]
            refine sum_congr rfl fun v _ => ?_
            rw [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, mul_comm]
        _ ≤ ∑ v, ∑ u ∈ H.neighborFinset v, a u v * (H.degree u + H.degree v) :=
            sum_le_sum fun v _ => sum_le_sum fun u hu =>
              haS u v ((SimpleGraph.mem_neighborFinset _ _ _).1 hu).symm
        _ = 2 * ∑ v, ∑ u ∈ H.neighborFinset v, a u v * H.degree v := by
            rw [two_mul]
            nth_rewrite 2 [hswap]
            rw [← sum_add_distrib]
            refine sum_congr rfl fun v _ => ?_
            rw [← sum_add_distrib]
            refine sum_congr rfl fun u _ => ?_
            ring
    omega
  have hsum := sum_le_sum fun σ (_ : σ ∈ univ) => hper σ
  rw [sum_add_distrib, hT, ← mul_sum, sum_const, card_univ, smul_eq_mul] at hsum
  linarith

/-- **Edge removal** ([Wattenhofer2016], Lemma 7.14): one phase of Luby's algorithm keeps at most
half of the live edges in expectation. -/
theorem two_mul_expect_liveEdges_phase_le :
    2 * ∑' t, ProbComp.eval (phase G s) t * (liveEdges G t : ℝ≥0∞) ≤ liveEdges G s := by
  rw [eval_phase, Probability.PMF.tsum_map_mul, tsum_fintype]
  simp only [Probability.PMF.uniformOfFintype_apply]
  rw [← mul_sum, ← mul_assoc, mul_comm 2, mul_assoc]
  have h := two_mul_sum_liveEdges_step_le G s
  have hN : (Fintype.card (Ranking V) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc (Fintype.card (Ranking V) : ℝ≥0∞)⁻¹ *
        (2 * ∑ σ : Ranking V, (liveEdges G (step G s σ) : ℝ≥0∞))
      ≤ (Fintype.card (Ranking V) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (Ranking V) : ℝ≥0∞) * liveEdges G s) := by
        exact mul_le_mul_right (by exact_mod_cast h) _
    _ = liveEdges G s := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hN (ENNReal.natCast_ne_top _), one_mul]

end Progress

/-! ### Round bounds -/

theorem liveEdges_init : liveEdges G (init : State V) = G.edgeFinset.card := by
  rw [liveEdges]
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  induction e using Sym2.ind with
  | _ u v => simp [init]

/-- After `k` phases the expected number of live edges is at most `|E| / 2 ^ k`. -/
theorem two_pow_mul_expect_liveEdges_run_le (k : ℕ) :
    2 ^ k * ∑' t, ProbComp.eval (run G k) t * (liveEdges G t : ℝ≥0∞) ≤ G.edgeFinset.card := by
  induction k with
  | zero =>
    rw [pow_zero, one_mul, run_zero, ProbComp.eval_pure,
      tsum_eq_single init (fun t ht => by rw [PMF.pure_apply, ite_eq_right ht, zero_mul]),
      PMF.pure_apply, ite_eq_left rfl, one_mul, liveEdges_init]
  | succ k ih =>
    rw [run_succ, ProbComp.eval_bind, Probability.PMF.tsum_bind_mul]
    calc 2 ^ (k + 1) * ∑' a, ProbComp.eval (run G k) a *
          ∑' t, ProbComp.eval (phase G a) t * (liveEdges G t : ℝ≥0∞)
        = 2 ^ k * ∑' a, ProbComp.eval (run G k) a *
          (2 * ∑' t, ProbComp.eval (phase G a) t * (liveEdges G t : ℝ≥0∞)) := by
          rw [pow_succ, mul_assoc, ← ENNReal.tsum_mul_left]
          congr 1
          refine tsum_congr fun a => ?_
          ring
      _ ≤ 2 ^ k * ∑' a, ProbComp.eval (run G k) a * (liveEdges G a : ℝ≥0∞) := by
          gcongr with a
          exact two_mul_expect_liveEdges_phase_le G a
      _ ≤ G.edgeFinset.card := ih

/-- With no live edge left, the next phase makes every live vertex join, and none stays live. -/
theorem live_step_eq_empty {s : State V} (h : liveEdges G s = 0) (σ : Ranking V) :
    (step G s σ).live = ∅ := by
  rw [liveEdges, card_eq_zero, SimpleGraph.edgeFinset_eq_empty] at h
  have hno : ∀ u ∈ s.live, ∀ w ∈ s.live, ¬ G.Adj u w := fun u hu w hw hadj => by
    have : (liveGraph G s.live).Adj u w := ⟨hadj, hu, hw⟩
    rw [h] at this
    exact this
  refine eq_empty_iff_forall_notMem.2 fun v hv => ?_
  obtain ⟨hL, hJ, -⟩ := (mem_step_live G).1 hv
  exact hJ ((mem_joiners G).2 ⟨hL, fun w hw hadj => absurd hadj (hno v hL w hw)⟩)

/-- **Round bound.** After `k + 1` phases, some vertex is still live with probability at most
`|E| / 2 ^ k` (Markov's inequality for the live edges after `k` phases). -/
theorem two_pow_mul_toOuterMeasure_live_nonempty_le (k : ℕ) :
    2 ^ k * (ProbComp.eval (run G (k + 1))).toOuterMeasure {s | s.live.Nonempty} ≤
      G.edgeFinset.card := by
  refine le_trans ?_ (two_pow_mul_expect_liveEdges_run_le G k)
  rw [run_succ, ProbComp.eval_bind, PMF.toOuterMeasure_bind_apply]
  gcongr with a
  rcases Nat.eq_zero_or_pos (liveEdges G a) with h0 | hpos
  · rw [h0, Nat.cast_zero, eval_phase, PMF.toOuterMeasure_map_apply]
    refine le_of_eq (PMF.toOuterMeasure_apply_eq_zero_iff _ _ |>.2 ?_)
    refine Set.disjoint_left.2 fun σ _ hσ => ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, live_step_eq_empty G h0 σ,
      Finset.not_nonempty_empty] at hσ
  · exact (Probability.PMF.toOuterMeasure_le_one _ _).trans (Nat.one_le_cast.2 hpos)

/-- **High-probability round bound.** If `|E| ≤ 2 ^ m`, then after `m + t + 1` phases the chosen
set fails to be a maximal independent set with probability at most `2 ^ (-t)`. -/
theorem toOuterMeasure_not_maximal_lubyMIS_le {m : ℕ} (hm : G.edgeFinset.card ≤ 2 ^ m) (t : ℕ) :
    (ProbComp.eval (lubyMIS G (m + t + 1))).toOuterMeasure
        {S | ¬ Maximal G.IsIndepSet (S : Set V)} ≤ (2 ^ t)⁻¹ := by
  rw [lubyMIS, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  have hsub : (State.chosen ⁻¹' {S : Finset V | ¬ Maximal G.IsIndepSet (S : Set V)}) ∩
      (ProbComp.eval (run G (m + t + 1))).support ⊆ {s | s.live.Nonempty} := by
    rintro s ⟨hs, hsupp⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq,
      (invariant_of_mem_support_run G hsupp).maximal_iff] at hs ⊢
    exact nonempty_iff_ne_empty.2 hs
  refine (PMF.toOuterMeasure_mono _ hsub).trans ?_
  have h := two_pow_mul_toOuterMeasure_live_nonempty_le G (m + t)
  have h2 : (2 : ℝ≥0∞) ^ (m + t) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ (m + t) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl h2) (Or.inl h2')] at h
  refine h.trans ?_
  rw [pow_add, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
    (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), mul_comm _ (2 ^ t)⁻¹, mul_assoc]
  calc (2 ^ t)⁻¹ * (((2 : ℝ≥0∞) ^ m)⁻¹ * G.edgeFinset.card)
      ≤ (2 ^ t)⁻¹ * (((2 : ℝ≥0∞) ^ m)⁻¹ * 2 ^ m) := by
        gcongr
        exact_mod_cast hm
    _ = (2 ^ t)⁻¹ := by
        rw [ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero)
          (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), mul_one]

/-- The success form: if `|E| ≤ 2 ^ m`, then after `m + t + 1` phases the output is a maximal
independent set with probability at least `1 - 2 ^ (-t)`. -/
theorem one_sub_le_toOuterMeasure_maximal_lubyMIS {m : ℕ} (hm : G.edgeFinset.card ≤ 2 ^ m)
    (t : ℕ) :
    1 - (2 ^ t)⁻¹ ≤ (ProbComp.eval (lubyMIS G (m + t + 1))).toOuterMeasure
        {S | Maximal G.IsIndepSet (S : Set V)} := by
  have hsum := Probability.PMF.toOuterMeasure_add_compl_ennreal
    (ProbComp.eval (lubyMIS G (m + t + 1))) {S | Maximal G.IsIndepSet (S : Set V)}
  have hfail := toOuterMeasure_not_maximal_lubyMIS_le G hm t
  rw [tsub_le_iff_right, ← hsum]
  gcongr
  exact hfail

/-- The success form with `m = ⌈log₂ |E|⌉`: `⌈log₂ |E|⌉ + t + 1` phases suffice. -/
theorem one_sub_le_toOuterMeasure_maximal_lubyMIS_clog (t : ℕ) :
    1 - (2 ^ t)⁻¹ ≤ (ProbComp.eval
        (lubyMIS G (Nat.clog 2 G.edgeFinset.card + t + 1))).toOuterMeasure
        {S | Maximal G.IsIndepSet (S : Set V)} :=
  one_sub_le_toOuterMeasure_maximal_lubyMIS G (Nat.le_pow_clog one_lt_two _) t

omit [DecidableEq V] in
/-- A graph on `n` vertices has at most `2 ^ (2 ⌈log₂ n⌉)` edges. -/
private theorem card_edgeFinset_le_two_pow_two_mul_clog :
    G.edgeFinset.card ≤ 2 ^ (2 * Nat.clog 2 (Fintype.card V)) :=
  calc G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
    _ ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _
    _ ≤ (2 ^ Nat.clog 2 (Fintype.card V)) ^ 2 :=
        Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two _) 2
    _ = 2 ^ (2 * Nat.clog 2 (Fintype.card V)) := by rw [← pow_mul, mul_comm]

/-- The success form in terms of the number `n` of vertices: `2 ⌈log₂ n⌉ + t + 1` phases
suffice. -/
theorem one_sub_le_toOuterMeasure_maximal_lubyMIS_card (t : ℕ) :
    1 - (2 ^ t)⁻¹ ≤ (ProbComp.eval
        (lubyMIS G (2 * Nat.clog 2 (Fintype.card V) + t + 1))).toOuterMeasure
        {S | Maximal G.IsIndepSet (S : Set V)} :=
  one_sub_le_toOuterMeasure_maximal_lubyMIS G (card_edgeFinset_le_two_pow_two_mul_clog G) t

/-- **With high probability.** After `(c + 2) ⌈log₂ n⌉ + 1` phases, the output fails to be a
maximal independent set with probability at most `n ^ (-c)`. -/
theorem toOuterMeasure_not_maximal_lubyMIS_le_inv_pow (c : ℕ) :
    (ProbComp.eval (lubyMIS G ((c + 2) * Nat.clog 2 (Fintype.card V) + 1))).toOuterMeasure
        {S | ¬ Maximal G.IsIndepSet (S : Set V)} ≤ ((Fintype.card V : ℝ≥0∞) ^ c)⁻¹ := by
  have hk : (c + 2) * Nat.clog 2 (Fintype.card V) + 1 =
      2 * Nat.clog 2 (Fintype.card V) + c * Nat.clog 2 (Fintype.card V) + 1 := by ring
  rw [hk]
  refine (toOuterMeasure_not_maximal_lubyMIS_le G (card_edgeFinset_le_two_pow_two_mul_clog G)
    _).trans (ENNReal.inv_le_inv.2 ?_)
  rw [mul_comm, pow_mul]
  gcongr
  exact_mod_cast Nat.le_pow_clog one_lt_two _

end Cslib.Algorithms.Lean.LubyMIS
