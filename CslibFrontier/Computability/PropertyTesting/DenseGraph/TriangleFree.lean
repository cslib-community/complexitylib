/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PropertyTesting.DenseGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF

/-!
# Testing triangle-freeness with a constant number of queries

The triangle tester samples a uniformly random ordered vertex triple `(u, v, w)`, queries the
three pairs `(u, v)`, `(v, w)` and `(u, w)`, and rejects exactly when all three are edges
(`triangleTrial`); `triangleTester n k` repeats this `k` times independently and accepts when no
sampled triple is a triangle. Its acceptance probability is exact
(`acceptProb_triangleTester`): a trial on a graph on `n` vertices with `t` triangles accepts with
probability `1 - 6 t / n³`, since each triangle is hit by `6` ordered triples
(`card_orderedTriangles`).

A triangle-free graph is therefore always accepted. A graph `ε`-far from triangle-free (`IsFar`)
is in particular `ε`-far in the sense of Mathlib's `SimpleGraph.FarFromTriangleFree`, so by the
triangle removal lemma `SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset` it has at least
`triangleRemovalBound ε * n³` triangles. A trial thus rejects it with probability at least
`6 · triangleRemovalBound ε`, and `k` trials with `1 ≤ 3 · triangleRemovalBound ε · k` form a
one-sided tester with `3 k` queries (`isOneSidedTester_triangleTester`). The number of trials
depends only on `ε`, so triangle-freeness is one-sided testable with a query bound independent of
the number of vertices (`oneSidedTestable_cliqueFree_three`). This removal-lemma argument for
testing triangle-freeness goes back to
[Alon, Duke, Lefmann, Rödl and Yuster][AlonDukeLefmannRodlYuster1994]; see also
[Alon, Fischer, Krivelevich and Szegedy][AlonFischerKrivelevichSzegedy2000] and
[Goldreich, Section 8.4.2][Goldreich2017] for subgraph-freeness testers in the dense graph model.

The query bound inherits the constant of Mathlib's removal lemma, which comes from Szemerédi's
regularity lemma and is of tower type in `1 / ε`. The results bound queries only, not running
time.

## Main definitions

* `Cslib.DenseGraphTesting.triangleTrial`: one trial, three random vertices and three queries.
* `Cslib.DenseGraphTesting.triangleTester`: `k` independent trials.

## Main results

* `Cslib.DenseGraphTesting.card_orderedTriangles`: ordered triangles number six times the
  triangles.
* `Cslib.DenseGraphTesting.acceptProb_triangleTrial`, `acceptProb_triangleTester`: exact
  acceptance probabilities.
* `Cslib.DenseGraphTesting.isOneSidedTester_triangleTester`: the tester is a one-sided tester
  for triangle-freeness.
* `Cslib.DenseGraphTesting.oneSidedTestable_cliqueFree_three`: triangle-freeness is one-sided
  testable with `3 ⌈(3 · triangleRemovalBound ε)⁻¹⌉` queries.

## References

* [N. Alon, R. A. Duke, H. Lefmann, V. Rödl, R. Yuster, *The algorithmic aspects of the regularity
  lemma*][AlonDukeLefmannRodlYuster1994]
* [N. Alon, E. Fischer, M. Krivelevich, M. Szegedy, *Efficient testing of large
  graphs*][AlonFischerKrivelevichSzegedy2000]
* [O. Goldreich, *Introduction to Property Testing*][Goldreich2017]
-/

public section

namespace Cslib.DenseGraphTesting

open SimpleGraph Finset

/-! ### Counting ordered triangles -/

/-- Each triangle of `G` is hit by exactly six ordered vertex triples `(u, v, w)` with `u v`,
`v w` and `u w` edges. -/
theorem card_orderedTriangles (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (∑ u, ∑ v, ∑ w, if G.Adj u v ∧ G.Adj v w ∧ G.Adj u w then 1 else 0 : ℕ) =
      6 * #(G.cliqueFinset 3) := by
  set T : Finset (V × V × V) :=
    univ.filter fun x => G.Adj x.1 x.2.1 ∧ G.Adj x.2.1 x.2.2 ∧ G.Adj x.1 x.2.2 with hT
  have hsum : (∑ u, ∑ v, ∑ w, if G.Adj u v ∧ G.Adj v w ∧ G.Adj u w then 1 else 0 : ℕ) = #T := by
    rw [hT, Finset.card_filter, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
  rw [hsum]
  have hmaps : ∀ x ∈ T, ({x.1, x.2.1, x.2.2} : Finset V) ∈ G.cliqueFinset 3 := by
    rintro ⟨u, v, w⟩ hx
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
    exact ⟨hx.1, hx.2.2, hx.2.1⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  have hfib : T.filter (fun x => ({x.1, x.2.1, x.2.2} : Finset V) = {a, b, c}) =
      {(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)} := by
    ext ⟨u, v, w⟩
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, heq⟩
      have hu : u ∈ ({a, b, c} : Finset V) := heq ▸ by simp
      have hv : v ∈ ({a, b, c} : Finset V) := heq ▸ by simp
      have hw : w ∈ ({a, b, c} : Finset V) := heq ▸ by simp
      clear heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        rcases hw with rfl | rfl | rfl <;> simp_all
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
        first
        | assumption
        | exact (‹_› : G.Adj _ _).symm
        | (ext; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm])
  rw [hfib]
  have hab' := hab.ne
  have hac' := hac.ne
  have hbc' := hbc.ne
  simp [Finset.card_insert_of_notMem, hab', hac', hbc', hab'.symm, hac'.symm, hbc'.symm]

/-! ### The triangle tester -/

/-- One trial of the triangle tester on `Fin (m + 1)`: sample three uniform vertices `u`, `v`,
`w`, query the pairs `(u, v)`, `(v, w)` and `(u, w)`, and reject exactly when all three are
edges. -/
def triangleTrial (m : ℕ) : Tester (m + 1) := do
  let u ← ProbOracleComp.sample (ProbComp.unifFin m)
  let v ← ProbOracleComp.sample (ProbComp.unifFin m)
  let w ← ProbOracleComp.sample (ProbComp.unifFin m)
  let a ← queryAdj u v
  let b ← queryAdj v w
  let c ← queryAdj u w
  return !(a && b && c)

/-- The triangle tester with `k` independent trials. The graph on no vertices is accepted
without queries. -/
def triangleTester : (n : ℕ) → ℕ → Tester n
  | 0, _ => pure true
  | m + 1, k => OracleComp.repeatAll (triangleTrial m) k

/-- A trial asks three queries. -/
theorem isQueryBounded_triangleTrial (m : ℕ) :
    ProbOracleComp.IsQueryBounded (triangleTrial m) 3 :=
  (ProbOracleComp.IsQueryBounded.sample _).bind fun _ =>
    (ProbOracleComp.IsQueryBounded.sample _).bind fun _ =>
    (ProbOracleComp.IsQueryBounded.sample _).bind fun _ =>
    (isQueryBounded_queryAdj _ _).bind fun _ =>
    (isQueryBounded_queryAdj _ _).bind fun _ =>
    (isQueryBounded_queryAdj _ _).bind fun _ => OracleComp.IsCostBounded.pure _ 0

/-- The tester with `k` trials asks at most `3 k` queries. -/
theorem isQueryBounded_triangleTester (n k : ℕ) :
    ProbOracleComp.IsQueryBounded (triangleTester n k) (3 * k) := by
  cases n with
  | zero => exact .pure _ _
  | succ m => exact isQueryBounded_repeatAll (isQueryBounded_triangleTrial m) k

private theorem evalWith_triangleTrial (m : ℕ) (G : SimpleGraph (Fin (m + 1)))
    [DecidableRel G.Adj] :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle G))
      (triangleTrial m) =
      (Probability.PMF.uniformOfFintype (Fin (m + 1))).bind fun u =>
        (Probability.PMF.uniformOfFintype (Fin (m + 1))).bind fun v =>
          (Probability.PMF.uniformOfFintype (Fin (m + 1))).bind fun w =>
            PMF.pure (!(decide (G.Adj u v) && decide (G.Adj v w) && decide (G.Adj u w))) := by
  simp only [triangleTrial, OracleComp.evalWith_bind,
    ProbOracleComp.evalWith_sumHandler_unifOracle_sample, ProbComp.eval_unifFin, evalWith_queryAdj,
    PMF.pure_bind, OracleComp.evalWith_pure]

private theorem toReal_pure_not_and (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    (PMF.pure (!(decide A && decide B && decide C)) true).toReal =
      1 - if A ∧ B ∧ C then (1 : ℝ) else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC, PMF.pure_apply]

/-- A trial accepts a graph on `m + 1` vertices with `t` triangles with probability
`1 - 6 t / (m + 1)³`. -/
theorem acceptProb_triangleTrial (m : ℕ) (G : SimpleGraph (Fin (m + 1))) [DecidableRel G.Adj] :
    acceptProb (triangleTrial m) G = 1 - 6 * #(G.cliqueFinset 3) / (m + 1 : ℝ) ^ 3 := by
  have hcount : (∑ u, ∑ v, ∑ w, if G.Adj u v ∧ G.Adj v w ∧ G.Adj u w then (1 : ℝ) else 0) =
      6 * #(G.cliqueFinset 3) := by
    exact_mod_cast card_orderedTriangles (Fin (m + 1)) G
  rw [acceptProb_eq, evalWith_triangleTrial]
  simp only [Probability.PMF.bind_apply_toReal, Probability.PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.card_fin, toReal_pure_not_and,
    Finset.mul_sum, mul_sub, mul_one]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, hcount]
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The tester with `k` trials accepts a graph on `n` vertices with `t` triangles with
probability `(1 - 6 t / n³) ^ k`. -/
theorem acceptProb_triangleTester (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    acceptProb (triangleTester n k) G = (1 - 6 * #(G.cliqueFinset 3) / (n : ℝ) ^ 3) ^ k := by
  cases n with
  | zero => simp [triangleTester]
  | succ m =>
    rw [triangleTester, acceptProb_repeatAll, acceptProb_triangleTrial]
    push_cast
    rfl

/-! ### Soundness via the removal lemma -/

/-- **Triangle-freeness is testable.** For `ε > 0`, the triangle tester with `k` trials, where
`1 ≤ 3 · triangleRemovalBound ε · k`, is a one-sided tester for triangle-freeness with proximity
`ε` and `3 k` queries. -/
theorem isOneSidedTester_triangleTester {n : ℕ} {ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (hk : 1 ≤ 3 * triangleRemovalBound ε * k) :
    IsOneSidedTester (triangleTester n k) (fun G => G.CliqueFree 3) ε (3 * k) := by
  cases n with
  | zero =>
    refine ⟨isQueryBounded_triangleTester 0 k, fun G _ => by simp [triangleTester],
      fun G hG => ?_⟩
    exact absurd hG (not_isFar_of_property (SimpleGraph.cliqueFree_of_card_lt (by simp)) hε.le)
  | succ m =>
    classical
    refine isOneSidedTester_repeatAll (δ := 6 * triangleRemovalBound ε)
      (isQueryBounded_triangleTrial m) (fun G hG => ?_) (fun G hG => ?_) (by linarith)
    · rw [acceptProb_triangleTrial, SimpleGraph.cliqueFinset_eq_empty_iff.mpr hG,
        Finset.card_empty, Nat.cast_zero, mul_zero, zero_div, sub_zero]
    · rw [acceptProb_triangleTrial]
      have hrem := hG.farFromTriangleFree.le_card_cliqueFinset
      rw [Fintype.card_fin] at hrem
      have hpos : (0 : ℝ) < (m + 1 : ℝ) ^ 3 := by positivity
      rw [sub_le_sub_iff_left, le_div_iff₀ hpos]
      push_cast at hrem ⊢
      linarith

/-- **Triangle-freeness is one-sided testable with a constant number of queries**: with
`3 ⌈(3 · triangleRemovalBound ε)⁻¹⌉` queries, a bound that depends on the proximity `ε` but not on
the number of vertices. -/
theorem oneSidedTestable_cliqueFree_three :
    OneSidedTestable (fun _ G => G.CliqueFree 3)
      (fun ε => 3 * ⌈(3 * triangleRemovalBound ε)⁻¹⌉₊) := by
  refine oneSidedTestable_iff.mpr fun ε hε n => ?_
  refine ⟨triangleTester n _, isOneSidedTester_triangleTester hε ?_⟩
  have hpos : 0 < 3 * triangleRemovalBound ε := by
    have := triangleRemovalBound_pos hε
    positivity
  calc (1 : ℝ) = 3 * triangleRemovalBound ε * (3 * triangleRemovalBound ε)⁻¹ :=
        (mul_inv_cancel₀ hpos.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) hpos.le

end Cslib.DenseGraphTesting
