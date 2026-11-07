/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Languages.Probabilistic.Oracle.QueryCount
public import Complexity.Languages.Probabilistic.Semantics
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Order.SymmDiff
import Complexity.Foundations.Combinatorics.SimpleGraph.SymmDiff
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Property testing in the dense graph model

In the dense graph model of [Goldreich, Goldwasser and Ron][GoldreichGoldwasserRon1998] a tester
for graphs on the vertex set `Fin n` accesses the graph only through its adjacency matrix: it asks
whether two vertices are adjacent and receives one bit [Goldreich, Chapter 8][Goldreich2017].
Here a tester is a probabilistic oracle program (`Tester n`, a `ProbOracleComp`) that tosses
private coins and asks vertex-pair queries adaptively; it runs against the deterministic adjacency
oracle of the graph (`adjOracle`), and `acceptProb T G` is the probability that it outputs
`true`.

The distance between two graphs on the same vertex set is the number of vertex pairs on which
they differ (`editDist`, the number of edges of their symmetric difference). A graph is `ε`-far
from a property `P` when every graph with property `P` differs from it in more than `ε n²` pairs
(`IsFar`). Goldreich normalizes by the `n²` ordered entries of the adjacency matrix, each changed
pair accounting for two entries, so his distance `ε` corresponds to `IsFar G P (ε / 2)` here. A
*one-sided tester* (`IsOneSidedTester`) makes at most `q` queries on every run, accepts every graph
with the property with probability one and accepts every `ε`-far graph with probability at most
`1 / 3`; a family of properties is `OneSidedTestable` with query bound `q` if every proximity
`ε > 0` and every number of vertices admits a one-sided tester with `q ε` queries, independent
of `n`.

The far notion is related to Mathlib's deletion distance: an `ε`-far graph is
`ε n²`-delete-far (`IsFar.deleteFar`), in particular `ε`-far from triangle-free in the sense of
`SimpleGraph.FarFromTriangleFree` (`IsFar.farFromTriangleFree`); conversely, for a property that is
closed under taking subgraphs, deletion distance more than `ε n²` implies `ε`-far
(`isFar_of_deleteFar`, `isFar_of_farFromTriangleFree`).

Repetition (`repeatAll`) runs independent copies of a tester and accepts when all of them accept;
its acceptance probability is the power of the single-run acceptance probability
(`acceptProb_repeatAll`). This turns a perfectly complete `q`-query test that rejects far graphs
with probability at least `δ` into a one-sided tester after `k` runs with `2 ≤ δ k`
(`IsOneSidedTester.of_repeatAll`).

This file bounds queries only; it makes no claim about running time.

## Main definitions

* `Cslib.DenseGraphTesting.Tester`: probabilistic oracle programs asking vertex-pair queries.
* `Cslib.DenseGraphTesting.acceptProb`: the acceptance probability of a tester on a graph.
* `Cslib.DenseGraphTesting.editDist`: the number of vertex pairs on which two graphs differ.
* `Cslib.DenseGraphTesting.IsFar`: `ε`-far from a property, relative to `n²`.
* `Cslib.DenseGraphTesting.IsOneSidedTester`: one-sided testers with a worst-case query bound.
* `Cslib.DenseGraphTesting.OneSidedTestable`: testability with a query bound depending only on
  the proximity parameter.
* `Cslib.DenseGraphTesting.repeatAll`: independent repetition, accepting when every run accepts.

## Main results

* `Cslib.DenseGraphTesting.IsFar.deleteFar`, `IsFar.farFromTriangleFree`,
  `isFar_of_deleteFar`, `isFar_of_farFromTriangleFree`: comparison with Mathlib's deletion
  distance.
* `Cslib.DenseGraphTesting.acceptProb_repeatAll`, `isQueryBounded_repeatAll`: repetition
  multiplies acceptance probabilities and query bounds.
* `Cslib.DenseGraphTesting.IsOneSidedTester.of_repeatAll`: amplification of a perfectly complete
  test.

## References

* [O. Goldreich, S. Goldwasser, D. Ron, *Property testing and its connection to learning and
  approximation*][GoldreichGoldwasserRon1998]
* [O. Goldreich, *Introduction to Property Testing*][Goldreich2017]
-/

public section

namespace Cslib.DenseGraphTesting

open SimpleGraph Finset

/-- Vertex-pair queries: the query `(u, v)` is answered by one bit, whether `u` and `v` are
adjacent. -/
abbrev pairSpec (V : Type) : V × V → Type := fun _ => Bool

/-- A tester for graphs on `Fin n`: a probabilistic oracle program that asks vertex-pair queries
and outputs `true` (accept) or `false` (reject). -/
abbrev Tester (n : ℕ) : Type := ProbOracleComp (pairSpec (Fin n)) Bool

open Classical in
/-- The adjacency oracle of a graph: it answers the query `(u, v)` deterministically with whether
`u` and `v` are adjacent. -/
noncomputable def adjOracle {V : Type} (G : SimpleGraph V) : (q : V × V) → PMF (pairSpec V q) :=
  fun (u, v) => PMF.pure (decide (G.Adj u v))

/-- The probability that the tester `T` accepts the graph `G`, with its coins uniform and its
queries answered by the adjacency oracle of `G`. -/
noncomputable def acceptProb {n : ℕ} (T : Tester n) (G : SimpleGraph (Fin n)) : ℝ :=
  (OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle G)) T true).toReal

/-- Unfolding lemma for `acceptProb`. -/
theorem acceptProb_eq {n : ℕ} (T : Tester n) (G : SimpleGraph (Fin n)) :
    acceptProb T G =
      (OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle G)) T
        true).toReal := by
  rw [acceptProb]

/-- The edit distance of two graphs on the same vertex set: the number of vertex pairs that are
an edge of exactly one of them. -/
noncomputable def editDist {V : Type*} (G H : SimpleGraph V) : ℕ :=
  Nat.card (symmDiff G H).edgeSet

/-- `G` is `ε`-far from the property `P`: every graph with property `P` differs from `G` in more
than `ε n²` vertex pairs, where `n` is the number of vertices. -/
def IsFar {V : Type*} [Fintype V] (G : SimpleGraph V) (P : SimpleGraph V → Prop) (ε : ℝ) :
    Prop :=
  ∀ H, P H → ε * (Fintype.card V ^ 2 : ℕ) < editDist G H

/-- `T` is a one-sided tester for the property `P` of graphs on `Fin n` with proximity `ε` and
query bound `q`: every run asks at most `q` vertex-pair queries, every graph with property `P` is
accepted with probability one, and every graph `ε`-far from `P` is accepted with probability at
most `1 / 3`. -/
structure IsOneSidedTester {n : ℕ} (T : Tester n) (P : SimpleGraph (Fin n) → Prop) (ε : ℝ)
    (q : ℕ) : Prop where
  /-- Every run of the tester asks at most `q` vertex-pair queries. -/
  queryBounded : ProbOracleComp.IsQueryBounded T q
  /-- Perfect completeness: graphs with the property are always accepted. -/
  accept : ∀ G, P G → acceptProb T G = 1
  /-- Soundness: graphs `ε`-far from the property are accepted with probability at most
  `1 / 3`. -/
  reject : ∀ G, IsFar G P ε → acceptProb T G ≤ 1 / 3

/-- The family of graph properties `P n` (one for each number `n` of vertices) is one-sided
testable with query bound `q`: for every proximity `ε > 0` and every `n` there is a one-sided
tester for `P n` with proximity `ε` asking at most `q ε` queries, a bound independent of `n`. -/
def OneSidedTestable (P : ∀ n, SimpleGraph (Fin n) → Prop) (q : ℝ → ℕ) : Prop :=
  ∀ ε, 0 < ε → ∀ n, ∃ T : Tester n, IsOneSidedTester T (P n) ε (q ε)

theorem isFar_iff {V : Type*} [Fintype V] {G : SimpleGraph V} {P : SimpleGraph V → Prop}
    {ε : ℝ} : IsFar G P ε ↔ ∀ H, P H → ε * (Fintype.card V ^ 2 : ℕ) < editDist G H :=
  Iff.rfl

theorem oneSidedTestable_iff {P : ∀ n, SimpleGraph (Fin n) → Prop} {q : ℝ → ℕ} :
    OneSidedTestable P q ↔ ∀ ε, 0 < ε → ∀ n, ∃ T : Tester n, IsOneSidedTester T (P n) ε (q ε) :=
  Iff.rfl

/-! ### Edit distance -/

section EditDist

variable {V : Type*}

@[simp]
theorem editDist_self (G : SimpleGraph V) : editDist G G = 0 := by
  rw [editDist, symmDiff_self, SimpleGraph.edgeSet_bot, Nat.card_eq_zero]
  exact Or.inl (Set.isEmpty_coe_sort.mpr rfl)

theorem editDist_comm (G H : SimpleGraph V) : editDist G H = editDist H G := by
  rw [editDist, editDist, symmDiff_comm]

/-- On a finite vertex set the edit distance is the size of the symmetric difference of the edge
sets. -/
theorem editDist_eq_card [Fintype V] [DecidableEq V] (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] : editDist G H = #(symmDiff G.edgeFinset H.edgeFinset) := by
  have he : (symmDiff G H).edgeSet = ↑(symmDiff G.edgeFinset H.edgeFinset) := by
    rw [Finset.coe_symmDiff, SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset,
      SimpleGraph.edgeSet_symmDiff]
  rw [editDist, Nat.card_coe_set_eq, he, Set.ncard_coe_finset]

/-- Deleting a set `s` of edges of `G` changes exactly the pairs in `s`. -/
theorem editDist_deleteEdges [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : Finset (Sym2 V)} (hs : s ⊆ G.edgeFinset) : editDist G (G.deleteEdges s) = #s := by
  have he : (symmDiff G (G.deleteEdges s)).edgeSet = s := by
    rw [SimpleGraph.edgeSet_symmDiff, SimpleGraph.edgeSet_deleteEdges]
    ext e
    have := @hs e
    simp only [Set.mem_symmDiff, Set.mem_sdiff, Finset.mem_coe, SimpleGraph.mem_edgeFinset]
      at this ⊢
    tauto
  rw [editDist, he, Nat.card_coe_set_eq, Set.ncard_coe_finset]

end EditDist

/-! ### Far graphs and deletion distance -/

section Far

variable {V : Type*} [Fintype V]

/-- A graph with property `P` is not `ε`-far from `P` for any `ε ≥ 0`. -/
theorem not_isFar_of {G : SimpleGraph V} {P : SimpleGraph V → Prop} (hG : P G) {ε : ℝ}
    (hε : 0 ≤ ε) : ¬ IsFar G P ε := fun h => by
  have h₁ := h G hG
  rw [editDist_self, Nat.cast_zero] at h₁
  have h₂ : (0 : ℝ) ≤ ε * (Fintype.card V ^ 2 : ℕ) := by positivity
  linarith

variable {G : SimpleGraph V} [DecidableRel G.Adj] {P : SimpleGraph V → Prop}

/-- An `ε`-far graph is `ε n²`-delete-far: at least `ε n²` edges must be deleted to reach the
property. -/
theorem IsFar.deleteFar {ε : ℝ} (h : IsFar G P ε) :
    G.DeleteFar P (ε * (Fintype.card V ^ 2 : ℕ)) := fun s hs hP => by
  have h₁ := h _ hP
  rw [editDist_deleteEdges G hs] at h₁
  exact h₁.le

/-- A graph `ε`-far from triangle-free is `ε`-far from triangle-free in the sense of Mathlib's
triangle removal lemma. -/
theorem IsFar.farFromTriangleFree {ε : ℝ} (h : IsFar G (fun H => H.CliqueFree 3) ε) :
    G.FarFromTriangleFree ε :=
  h.deleteFar

/-- For a property closed under taking subgraphs, more than `ε n²` deletion distance implies
`ε`-far: the edges of `G` that a graph `H` with the property lacks can be deleted from `G`, and
the result is a subgraph of `H`. -/
theorem isFar_of_deleteFar (hP : ∀ ⦃H H' : SimpleGraph V⦄, H ≤ H' → P H' → P H) {ε r : ℝ}
    (h : G.DeleteFar P r) (hr : ε * (Fintype.card V ^ 2 : ℕ) < r) : IsFar G P ε := by
  intro H hH
  classical
  have hdel : P (G.deleteEdges (G.edgeFinset \ H.edgeFinset : Finset (Sym2 V))) := by
    refine hP (fun u v huv => ?_) hH
    rw [SimpleGraph.deleteEdges_adj] at huv
    obtain ⟨hG, hn⟩ := huv
    by_contra hH'
    exact hn (by simp [hG, hH'])
  have h₁ := h Finset.sdiff_subset hdel
  have h₂ : #(G.edgeFinset \ H.edgeFinset) ≤ editDist G H := by
    rw [editDist_eq_card]
    exact Finset.card_le_card fun e he => Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp he))
  have h₃ : (#(G.edgeFinset \ H.edgeFinset) : ℝ) ≤ editDist G H := by exact_mod_cast h₂
  linarith

/-- On a nonempty vertex set, being `ε'`-far from triangle-free in the sense of Mathlib implies
being `ε`-far from triangle-free for every `ε < ε'`. -/
theorem isFar_of_farFromTriangleFree [Nonempty V] {ε ε' : ℝ} (h : G.FarFromTriangleFree ε')
    (hεε' : ε < ε') : IsFar G (fun H => H.CliqueFree 3) ε := by
  refine isFar_of_deleteFar (fun H H' hle hH' => hH'.anti hle) h ?_
  have hn : (0 : ℝ) < (Fintype.card V ^ 2 : ℕ) := by
    have := Fintype.card_pos (α := V)
    positivity
  push_cast at hn ⊢
  nlinarith

end Far

/-! ### Queries and repetition -/

/-- Ask whether the vertices `u` and `v` are adjacent. -/
def queryAdj {n : ℕ} (u v : Fin n) : ProbOracleComp (pairSpec (Fin n)) Bool :=
  ProbOracleComp.query (u, v)

/-- Run `k` independent copies of the tester `T` in sequence, rejecting as soon as one of them
rejects and accepting when all of them accept. -/
def repeatAll {n : ℕ} (T : Tester n) : ℕ → Tester n
  | 0 => pure true
  | k + 1 => do
    if ← T then repeatAll T k else pure false

/-- A uniform coin toss of a tester is distributed as the corresponding `ProbComp`. -/
theorem evalWith_sample {n : ℕ} (G : SimpleGraph (Fin n)) {α : Type} (p : ProbComp α) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle G))
      (ProbOracleComp.sample (spec := pairSpec (Fin n)) p) = ProbComp.eval p := by
  rw [ProbOracleComp.sample_eq_liftLeft, OracleComp.evalWith_sumHandler_liftLeft]
  rfl

/-- The adjacency oracle answers a pair query with the adjacency bit. -/
theorem evalWith_queryAdj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle G))
      (queryAdj u v) = PMF.pure (decide (G.Adj u v)) := by
  rw [queryAdj, ProbOracleComp.query, OracleComp.evalWith_query]
  simp only [OracleComp.sumHandler, adjOracle]
  congr

theorem isQueryBounded_queryAdj {n : ℕ} (u v : Fin n) :
    ProbOracleComp.IsQueryBounded (queryAdj u v) 1 :=
  ProbOracleComp.IsQueryBounded.query _

theorem acceptProb_nonneg {n : ℕ} (T : Tester n) (G : SimpleGraph (Fin n)) :
    0 ≤ acceptProb T G :=
  ENNReal.toReal_nonneg

@[simp]
theorem acceptProb_pure {n : ℕ} (b : Bool) (G : SimpleGraph (Fin n)) :
    acceptProb (pure b : Tester n) G = if b then 1 else 0 := by
  cases b <;> simp [acceptProb]

/-- Independent repetition multiplies acceptance probabilities. -/
theorem acceptProb_repeatAll {n : ℕ} (T : Tester n) (G : SimpleGraph (Fin n)) (k : ℕ) :
    acceptProb (repeatAll T k) G = acceptProb T G ^ k := by
  induction k with
  | zero => simp only [repeatAll, acceptProb_pure, ite_true, pow_zero]
  | succ k ih =>
    rw [pow_succ', ← ih]
    simp only [acceptProb, repeatAll, OracleComp.evalWith_bind]
    rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    simp only [ite_true, Bool.false_eq_true, ite_false, OracleComp.evalWith_pure, PMF.pure_apply,
      Bool.true_eq_false, mul_zero, add_zero, ENNReal.toReal_mul]

/-- `k` repetitions of a `q`-query tester ask at most `q k` queries. -/
theorem isQueryBounded_repeatAll {n : ℕ} {T : Tester n} {q : ℕ}
    (hT : ProbOracleComp.IsQueryBounded T q) (k : ℕ) :
    ProbOracleComp.IsQueryBounded (repeatAll T k) (q * k) := by
  induction k with
  | zero => exact .pure _ _
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (q * k)]
    refine hT.bind fun b => ?_
    cases b
    · exact OracleComp.IsCostBounded.pure _ _
    · exact ih

private theorem pow_le_one_third {p δ : ℝ} (hp : 0 ≤ p) (hpδ : p ≤ 1 - δ) {k : ℕ}
    (hk : 2 ≤ δ * k) : p ^ k ≤ 1 / 3 := by
  have h₁ : p ^ k ≤ Real.exp (-δ) ^ k :=
    pow_le_pow_left₀ hp (hpδ.trans (Real.one_sub_le_exp_neg δ)) k
  rw [← Real.exp_nat_mul] at h₁
  have h₂ : Real.exp (k * -δ) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by nlinarith)
  have h₃ : Real.exp (-2) ≤ 1 / 3 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 2) (by norm_num)]
    linarith [Real.add_one_le_exp 2]
  linarith

/-- Amplification: if the `q`-query tester `T` accepts every graph with property `P` with
probability one and accepts every `ε`-far graph with probability at most `1 - δ`, then `k`
independent repetitions with `2 ≤ δ k` form a one-sided tester with `q k` queries. -/
theorem IsOneSidedTester.of_repeatAll {n : ℕ} {T : Tester n} {P : SimpleGraph (Fin n) → Prop}
    {ε δ : ℝ} {q k : ℕ} (hq : ProbOracleComp.IsQueryBounded T q)
    (hacc : ∀ G, P G → acceptProb T G = 1)
    (hrej : ∀ G, IsFar G P ε → acceptProb T G ≤ 1 - δ) (hk : 2 ≤ δ * k) :
    IsOneSidedTester (repeatAll T k) P ε (q * k) where
  queryBounded := isQueryBounded_repeatAll hq k
  accept G hG := by rw [acceptProb_repeatAll, hacc G hG, one_pow]
  reject G hG := by
    rw [acceptProb_repeatAll]
    exact pow_le_one_third (acceptProb_nonneg T G) (hrej G hG) hk

end Cslib.DenseGraphTesting
