/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Combinatorics/BinomialRandomGraph/`)

public import Complexity.Foundations.Probability.Combinatorics.BinomialRandomGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Complexity.Foundations.Probability.SecondMoment
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Sym.Card
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Cliques and the triangle threshold in binomial random graphs

A fixed set of `k` vertices spans a clique of the binomial random graph `G(V, p)` with probability
`p ^ C(k, 2)` (`SimpleGraph.binomialRandom_real_isClique`), so `G(V, p)` has `C(|V|, k) p ^ C(k, 2)`
`k`-cliques in expectation (`SimpleGraph.integral_card_cliqueFinset`) and contains one with at
most this probability (`SimpleGraph.binomialRandom_real_not_cliqueFree_le`).

For triangles these first-moment bounds are matched by the second moment method, giving the
**triangle threshold** `p = 1 / n` [Alon and Spencer, Section 4.4][AlonSpencer2016]
[Janson, Łuczak and Ruciński, Chapter 3][JansonLuczakRucinski2000]. Let `X` count the triangles of
`G(n, p)`. Two distinct triangles sharing an edge span `5` edges, and two triangles sharing at most
one vertex are independent; there are at most `3 (n - 3)` triangles sharing an edge with a fixed
one. The second moment method then bounds `P(X = 0) ≤ Var X / (E X) ^ 2` by
`1 / (C(n, 3) p ^ 3) + 3 (n - 3) / (C(n, 3) p)`
(`SimpleGraph.binomialRandom_real_cliqueFree_three_le_of_choose`), hence by
`16 / (n p) ^ 3 + 48 / (n p)` for `n ≥ 4`
(`SimpleGraph.binomialRandom_real_cliqueFree_three_le`). With the first-moment bound
`P(X > 0) ≤ (n p) ^ 3 / 6` (`SimpleGraph.binomialRandom_real_not_cliqueFree_three_le`):

* if `n p(n) → 0`, then `G(n, p(n))` is triangle-free with probability tending to `1`
  (`SimpleGraph.tendsto_binomialRandom_real_not_cliqueFree_three`);
* if `n p(n) → ∞`, then `G(n, p(n))` contains a triangle with probability tending to `1`
  (`SimpleGraph.tendsto_binomialRandom_real_cliqueFree_three`,
  `SimpleGraph.tendsto_binomialRandom_real_not_cliqueFree_three_nhds_one`).

The triangle is the case `v = e = 3` of the threshold `n ^ (-v / e)` for strictly balanced graphs;
the general case is not formalized here.

## Main results

* `SimpleGraph.measurableSet_isClique`, `SimpleGraph.measurableSet_cliqueFree`: measurability of
  clique events.
* `SimpleGraph.binomialRandom_real_isClique`: a fixed `k`-set is a clique with probability
  `p ^ C(k, 2)`.
* `SimpleGraph.integral_card_cliqueFinset`: the expected number of `k`-cliques.
* `SimpleGraph.binomialRandom_real_not_cliqueFree_le`: the first-moment bound for `k`-cliques.
* `SimpleGraph.binomialRandom_real_cliqueFree_three_le_of_choose`,
  `SimpleGraph.binomialRandom_real_cliqueFree_three_le`: the second-moment bounds for triangles.
* `SimpleGraph.binomialRandom_real_not_cliqueFree_three_le`: the first-moment bound for triangles.
* `SimpleGraph.tendsto_binomialRandom_real_not_cliqueFree_three`,
  `SimpleGraph.tendsto_binomialRandom_real_cliqueFree_three`,
  `SimpleGraph.tendsto_binomialRandom_real_not_cliqueFree_three_nhds_one`: the two sides of the
  threshold.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 4.4][AlonSpencer2016]
* [S. Janson, T. Łuczak, A. Ruciński, *Random Graphs*, Chapter 3][JansonLuczakRucinski2000]
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Finset Topology

namespace SimpleGraph

variable {V : Type*}

/-! ### The edges spanned by a set of vertices -/

section EdgesOn

variable [DecidableEq V]

/-- The edges of the complete graph on `t`. -/
private def edgesOn (t : Finset V) : Finset (Sym2 V) := t.offDiag.image Sym2.mk.uncurry

private theorem mk_mem_edgesOn {t : Finset V} {a b : V} :
    s(a, b) ∈ edgesOn t ↔ a ∈ t ∧ b ∈ t ∧ a ≠ b := by
  simp only [edgesOn, mem_image, mem_offDiag, Prod.exists, Function.uncurry_apply_pair]
  constructor
  · rintro ⟨x, y, ⟨hx, hy, hxy⟩, h⟩
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hx, hy, hxy⟩
    · exact ⟨hy, hx, Ne.symm hxy⟩
  · rintro ⟨ha, hb, hab⟩
    exact ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩

private theorem card_edgesOn (t : Finset V) : #(edgesOn t) = (#t).choose 2 :=
  Sym2.card_image_offDiag t

private theorem not_isDiag_of_mem_edgesOn {t : Finset V} {e : Sym2 V} (he : e ∈ edgesOn t) :
    ¬e.IsDiag := by
  induction e using Sym2.ind with
  | _ a b => exact fun h => (mk_mem_edgesOn.1 he).2.2 (Sym2.mk_isDiag_iff.1 h)

private theorem edgesOn_inter (s t : Finset V) : edgesOn (s ∩ t) = edgesOn s ∩ edgesOn t := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_inter, mk_mem_edgesOn]
    tauto

private theorem isClique_iff_edgesOn_subset {G : SimpleGraph V} {t : Finset V} :
    G.IsClique (t : Set V) ↔ (edgesOn t : Set (Sym2 V)) ⊆ G.edgeSet := by
  constructor
  · intro h e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mk_mem_edgesOn.1 he
      exact h ha hb hab
  · intro h a ha b hb hab
    exact h (mk_mem_edgesOn.2 ⟨ha, hb, hab⟩)

end EdgesOn

/-! ### Cliques -/

/-- The graphs in which a fixed finite set of vertices is a clique form a measurable set. -/
theorem measurableSet_isClique [Countable V] (t : Finset V) :
    MeasurableSet {G : SimpleGraph V | G.IsClique (t : Set V)} := by
  classical
  simp_rw [isClique_iff_edgesOn_subset]
  exact measurableSet_subset_edgeSet _

/-- A fixed set of `k` vertices spans a clique of `G(V, p)` with probability `p ^ C(k, 2)`. -/
theorem binomialRandom_real_isClique [Countable V] (p : I) (t : Finset V) :
    G(V, p).real {G | G.IsClique (t : Set V)} = (p : ℝ) ^ (#t).choose 2 := by
  classical
  simp_rw [isClique_iff_edgesOn_subset]
  rw [binomialRandom_real_subset_edgeSet p _ fun e he => not_isDiag_of_mem_edgesOn he,
    card_edgesOn]

variable [Fintype V]

private theorem setOf_not_cliqueFree (k : ℕ) :
    {G : SimpleGraph V | ¬G.CliqueFree k} =
      ⋃ t ∈ powersetCard k (univ : Finset V), {G | G.IsClique (t : Set V)} := by
  ext G
  simp only [CliqueFree, not_forall, not_not, Set.mem_ofPred_eq, Set.mem_iUnion, mem_powersetCard,
    subset_univ, true_and, exists_prop, isNClique_iff]
  exact ⟨fun ⟨t, ht, hk⟩ => ⟨t, hk, ht⟩, fun ⟨t, hk, ht⟩ => ⟨t, ht, hk⟩⟩

omit [Fintype V] in
/-- The `K_k`-free graphs on a finite vertex type form a measurable set. -/
theorem measurableSet_cliqueFree [Finite V] (k : ℕ) :
    MeasurableSet {G : SimpleGraph V | G.CliqueFree k} := by
  have := Fintype.ofFinite V
  have h : MeasurableSet {G : SimpleGraph V | ¬G.CliqueFree k} := by
    rw [setOf_not_cliqueFree]
    exact Finset.measurableSet_biUnion _ fun t _ => measurableSet_isClique t
  simpa only [Set.compl_ofPred, not_not] using h.compl

/-- **First moment bound for cliques** [Alon and Spencer, Section 4.4][AlonSpencer2016]:
`G(V, p)` contains a `k`-clique with probability at most the expected number
`C(|V|, k) p ^ C(k, 2)` of `k`-cliques. -/
theorem binomialRandom_real_not_cliqueFree_le (p : I) (k : ℕ) :
    G(V, p).real {G | ¬G.CliqueFree k} ≤ (Fintype.card V).choose k * (p : ℝ) ^ k.choose 2 := by
  rw [setOf_not_cliqueFree]
  refine (measureReal_biUnion_finset_le _ _).trans_eq ?_
  rw [sum_congr rfl fun t ht => by
    rw [binomialRandom_real_isClique, (mem_powersetCard.1 ht).2], sum_const, card_powersetCard,
    card_univ, nsmul_eq_mul]

open Classical in
/-- The expected number of `k`-cliques of `G(V, p)` is `C(|V|, k) p ^ C(k, 2)`. The adjacency
relation of the integrated graph is decided classically. -/
theorem integral_card_cliqueFinset [DecidableEq V] (p : I) (k : ℕ) :
    ∫ G, (#(G.cliqueFinset k) : ℝ) ∂G(V, p) =
      (Fintype.card V).choose k * (p : ℝ) ^ k.choose 2 := by
  have hcount (G : SimpleGraph V) : (#(G.cliqueFinset k) : ℝ) =
      ∑ t ∈ powersetCard k (univ : Finset V),
        {G : SimpleGraph V | G.IsClique (t : Set V)}.indicator (fun _ => 1) G := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, sum_boole]
    congr 2
    ext t
    simp [mem_cliqueFinset_iff, isNClique_iff, mem_powersetCard, and_comm]
  simp_rw [hcount]
  rw [integral_finsetSum _ fun t _ => (integrable_const 1).indicator (measurableSet_isClique t)]
  simp_rw [integral_indicator_const _ (measurableSet_isClique _), smul_eq_mul, mul_one]
  rw [sum_congr rfl fun t ht => by
    rw [binomialRandom_real_isClique, (mem_powersetCard.1 ht).2], sum_const, card_powersetCard,
    card_univ, nsmul_eq_mul]

/-! ### Triangles -/

section Triangle

variable [DecidableEq V]

/-- For a fixed `3`-set `s`, at most `3 (|V| - 3)` `3`-sets share exactly two vertices with it:
such a set is determined by the pair it shares and its remaining vertex. -/
private theorem card_filter_card_inter_eq_two_le {s : Finset V} (hs : #s = 3) :
    #{t ∈ powersetCard 3 (univ : Finset V) | #(s ∩ t) = 2} ≤ 3 * (Fintype.card V - 3) := by
  set T : Finset (Finset V) := {t ∈ powersetCard 3 (univ : Finset V) | #(s ∩ t) = 2}
  have hinj : Set.InjOn (fun t => (s ∩ t, t \ s)) (T : Set (Finset V)) := by
    intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    rw [← sdiff_union_inter a s, ← sdiff_union_inter b s, inter_comm a, inter_comm b, h.1, h.2]
  have hmaps : Set.MapsTo (fun t => (s ∩ t, t \ s)) (T : Set (Finset V))
      (powersetCard 2 s ×ˢ powersetCard 1 (univ \ s) : Finset _) := by
    intro t ht
    rw [mem_coe, mem_filter, mem_powersetCard] at ht
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powersetCard]
    refine ⟨⟨inter_subset_left, ht.2⟩, sdiff_subset_sdiff (subset_univ t) le_rfl, ?_⟩
    have := card_sdiff_add_card_inter t s
    rw [inter_comm] at this
    omega
  calc #T ≤ #(powersetCard 2 s ×ˢ powersetCard 1 (univ \ s)) := card_le_card_of_injOn _ hmaps hinj
    _ = 3 * (Fintype.card V - 3) := by
      rw [card_product, card_powersetCard, card_powersetCard, hs, card_univ_sdiff, hs,
        Nat.choose_one_right]
      rfl

omit [Fintype V] in
/-- The pair probabilities of the triangle events. Two `3`-sets span `6`, `5` or `3` edges
according as they share at most one, exactly two or all three vertices. -/
private theorem binomialRandom_real_isClique_inter_le [Countable V] (p : I) {s t : Finset V}
    (hs : #s = 3) (ht : #t = 3) :
    G(V, p).real ({G | G.IsClique (s : Set V)} ∩ {G | G.IsClique (t : Set V)}) ≤
      (p : ℝ) ^ 6 + (if s = t then (p : ℝ) ^ 3 else 0) +
        (if #(s ∩ t) = 2 then (p : ℝ) ^ 5 else 0) := by
  have hset : {G : SimpleGraph V | G.IsClique (s : Set V)} ∩ {G | G.IsClique (t : Set V)} =
      {G | ((edgesOn s ∪ edgesOn t : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ G.edgeSet} := by
    ext G
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, isClique_iff_edgesOn_subset, coe_union,
      Set.union_subset_iff]
  rw [hset, binomialRandom_real_subset_edgeSet p _ fun e he => by
    rcases mem_union.1 he with he | he <;> exact not_isDiag_of_mem_edgesOn he]
  have hcard : #(edgesOn s ∪ edgesOn t) + (#(s ∩ t)).choose 2 = 6 := by
    rw [← card_edgesOn, edgesOn_inter, card_union_add_card_inter, card_edgesOn, card_edgesOn,
      hs, ht]
    rfl
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hj : #(s ∩ t) ≤ 3 := hs ▸ card_le_card inter_subset_left
  by_cases hst : s = t
  · subst hst
    rw [inter_self, hs] at hcard
    have h3 : #(edgesOn s ∪ edgesOn s) = 3 := by simpa using hcard
    simp only [↓reduceIte, inter_self, hs, h3]
    norm_num
    positivity
  · simp only [hst, ↓reduceIte, add_zero]
    have hne : #(s ∩ t) ≠ 3 := fun h =>
      hst (eq_of_subset_of_card_le (inter_eq_left.1 (eq_of_subset_of_card_le inter_subset_left
        (by omega))) (by omega))
    interval_cases h : #(s ∩ t)
    · have h6 : #(edgesOn s ∪ edgesOn t) = 6 := by simpa using hcard
      rw [h6]; norm_num
    · have h6 : #(edgesOn s ∪ edgesOn t) = 6 := by simpa using hcard
      rw [h6]; norm_num
    · have h5 : #(edgesOn s ∪ edgesOn t) = 5 := by simpa using hcard
      rw [h5]; norm_num; positivity
    · exact absurd rfl hne

omit [DecidableEq V] in
private theorem setOf_cliqueFree_three :
    {G : SimpleGraph V | G.CliqueFree 3} =
      {G | ∀ t ∈ powersetCard 3 (univ : Finset V), G ∉ {G | G.IsClique (t : Set V)}} := by
  ext G
  have h := congrArg (G ∈ ·) (setOf_not_cliqueFree (V := V) 3)
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, eq_iff_iff] at h
  simp only [Set.mem_ofPred_eq]
  rw [← not_iff_not, h]
  simp only [not_forall, not_not, exists_prop]

end Triangle

/-- **The triangle threshold, second moment** [Alon and Spencer, Section 4.4][AlonSpencer2016]:
for `n ≥ 3` and `p > 0`, `G(n, p)` is triangle-free with probability at most
`1 / (C(n, 3) p ^ 3) + 3 (n - 3) / (C(n, 3) p)`. This is the bound `Var X / (E X) ^ 2` for the
number `X` of triangles, with the covariances of pairs of triangles sharing an edge bounded by
`p ^ 5` and those of pairs sharing at most one vertex equal to zero. -/
theorem binomialRandom_real_cliqueFree_three_le_of_choose {n : ℕ} (hn : 3 ≤ n) (p : I)
    (hp : 0 < (p : ℝ)) :
    G(Fin n, p).real {G | G.CliqueFree 3} ≤
      1 / (n.choose 3 * (p : ℝ) ^ 3) + 3 * (n - 3 : ℝ) / (n.choose 3 * p) := by
  set C : ℝ := ((n.choose 3 : ℕ) : ℝ) with hC
  have hC0 : 0 < C := by rw [hC]; exact_mod_cast Nat.choose_pos hn
  have hT : #(powersetCard 3 (univ : Finset (Fin n))) = n.choose 3 := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  have hA : ∀ t ∈ powersetCard 3 (univ : Finset (Fin n)),
      G(Fin n, p).real {G | G.IsClique (t : Set (Fin n))} = (p : ℝ) ^ 3 := fun t ht => by
    rw [binomialRandom_real_isClique, (mem_powersetCard.1 ht).2]; rfl
  have hS : ∑ t ∈ powersetCard 3 (univ : Finset (Fin n)),
      G(Fin n, p).real {G | G.IsClique (t : Set (Fin n))} = C * (p : ℝ) ^ 3 := by
    rw [sum_congr rfl hA, sum_const, hT, nsmul_eq_mul]
  have hpair : ∑ s ∈ powersetCard 3 (univ : Finset (Fin n)),
      ∑ t ∈ powersetCard 3 (univ : Finset (Fin n)),
        G(Fin n, p).real ({G | G.IsClique (s : Set (Fin n))} ∩ {G | G.IsClique (t : Set (Fin n))})
      ≤ C * (C * (p : ℝ) ^ 6 + (p : ℝ) ^ 3 + 3 * (n - 3 : ℝ) * (p : ℝ) ^ 5) := by
    rw [hC, ← hT, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun s hs => ?_
    have hs3 := (mem_powersetCard.1 hs).2
    refine (sum_le_sum fun t ht =>
      binomialRandom_real_isClique_inter_le p hs3 (mem_powersetCard.1 ht).2).trans ?_
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_ite_eq, ite_eq_left hs, sum_ite,
      sum_const_zero, add_zero, sum_const, nsmul_eq_mul, nsmul_eq_mul, hT]
    gcongr
    have := card_filter_card_inter_eq_two_le (V := Fin n) hs3
    rw [Fintype.card_fin] at this
    have h3 : ((n - 3 : ℕ) : ℝ) = n - 3 := by rw [Nat.cast_sub hn]; norm_num
    rw [← h3]
    exact_mod_cast this
  rw [setOf_cliqueFree_three]
  refine (measureReal_forall_notMem_le _ (fun t _ => measurableSet_isClique t)
    (hS ▸ by positivity)).trans ?_
  rw [hS, div_le_iff₀ (by positivity)]
  have hp3 : 0 < (p : ℝ) ^ 3 := by positivity
  calc _ ≤ C * (C * (p : ℝ) ^ 6 + (p : ℝ) ^ 3 + 3 * (n - 3 : ℝ) * (p : ℝ) ^ 5) -
        (C * (p : ℝ) ^ 3) ^ 2 := by linarith
    _ = _ := by field_simp; ring

/-- A lower bound for `C(n, 3)` used in the asymptotic corollaries. -/
private theorem pow_three_le_sixteen_mul_choose {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) ^ 3 ≤ 16 * n.choose 3 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h : ((4 + m).choose 3 : ℝ) * 6 = (4 + m) * (3 + m) * (2 + m) := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 4 + m) (k := 3) (by omega)
    rw [show 4 + m - 3 = m + 1 by omega] at this
    have hf : (m + 1 + 3).factorial = (4 + m) * (3 + m) * (2 + m) * (m + 1).factorial := by
      rw [show m + 1 + 3 = (m + 1 + 2) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ]
      ring
    rw [show 4 + m = m + 1 + 3 by ring, hf] at this
    have h6 : (3 : ℕ).factorial = 6 := rfl
    rw [h6] at this
    have hpos := Nat.factorial_pos (m + 1)
    have : (m + 1 + 3).choose 3 * 6 = (m + 1 + 3) * (m + 1 + 2) * (m + 1 + 1) := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      nlinarith [this]
    rw [show 4 + m = m + 1 + 3 by ring]
    exact_mod_cast (by rw [this]; ring)
  push_cast
  nlinarith [sq_nonneg (m : ℝ), (m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- **The triangle threshold, second moment, in terms of `n p`**: for `n ≥ 4` and `p > 0`,
`G(n, p)` is triangle-free with probability at most `16 / (n p) ^ 3 + 48 / (n p)`. -/
theorem binomialRandom_real_cliqueFree_three_le {n : ℕ} (hn : 4 ≤ n) (p : I)
    (hp : 0 < (p : ℝ)) :
    G(Fin n, p).real {G | G.CliqueFree 3} ≤ 16 / (n * p) ^ 3 + 48 / (n * p) := by
  have hC := pow_three_le_sixteen_mul_choose hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hC0 : (0 : ℝ) < n.choose 3 := by exact_mod_cast Nat.choose_pos (by omega)
  refine (binomialRandom_real_cliqueFree_three_le_of_choose (by omega) p hp).trans
    (add_le_add ?_ ?_)
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hp 3]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hn0 hp, sq_nonneg (n : ℝ)]

/-- **The triangle threshold, first moment** [Alon and Spencer, Section 4.4][AlonSpencer2016]:
`G(n, p)` contains a triangle with probability at most `C(n, 3) p ^ 3 ≤ (n p) ^ 3 / 6`. -/
theorem binomialRandom_real_not_cliqueFree_three_le (n : ℕ) (p : I) :
    G(Fin n, p).real {G | ¬G.CliqueFree 3} ≤ (n * p) ^ 3 / 6 := by
  refine (binomialRandom_real_not_cliqueFree_le p 3).trans ?_
  rw [Fintype.card_fin]
  have h := Nat.choose_le_pow_div (α := ℝ) 3 n
  have h6 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  have hp3 : (0 : ℝ) ≤ (p : ℝ) ^ (3 : ℕ).choose 2 := pow_nonneg p.2.1 _
  calc (n.choose 3 : ℝ) * (p : ℝ) ^ (3 : ℕ).choose 2 ≤ (n : ℝ) ^ 3 / 6 * (p : ℝ) ^ 3 :=
        mul_le_mul h (le_of_eq rfl) hp3 (by positivity)
    _ = _ := by ring

/-- **Below the triangle threshold** [Alon and Spencer, Section 4.4][AlonSpencer2016]: if
`n p(n) → 0`, then `G(n, p(n))` contains a triangle with probability tending to `0`. -/
theorem tendsto_binomialRandom_real_not_cliqueFree_three {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 0)) :
    Tendsto (fun n => G(Fin n, p n).real {G | ¬G.CliqueFree 3}) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) * p n) ^ 3 / 6) atTop (𝓝 0) := by
    simpa using (hp.pow 3).div_const 6
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => binomialRandom_real_not_cliqueFree_three_le n (p n)) hlim

/-- **Above the triangle threshold** [Alon and Spencer, Section 4.4][AlonSpencer2016]: if
`n p(n) → ∞`, then `G(n, p(n))` is triangle-free with probability tending to `0`, that is, it
contains a triangle with probability tending to `1`. -/
theorem tendsto_binomialRandom_real_cliqueFree_three {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop atTop) :
    Tendsto (fun n => G(Fin n, p n).real {G | G.CliqueFree 3}) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 16 / ((n : ℝ) * p n) ^ 3 + 48 / ((n : ℝ) * p n)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 16 / ((n : ℝ) * p n) ^ 3) atTop (𝓝 0) :=
      (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0) |>.comp hp).const_div_atTop 16
    have h2 : Tendsto (fun n : ℕ => 48 / ((n : ℝ) * p n)) atTop (𝓝 0) := hp.const_div_atTop 48
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop 4, hp.eventually_gt_atTop 0] with n hn hnp
  exact binomialRandom_real_cliqueFree_three_le hn (p n) (pos_of_mul_pos_right hnp n.cast_nonneg)

/-- **Above the triangle threshold**, in the usual form [Alon and Spencer, Section 4.4]
[AlonSpencer2016]: if `n p(n) → ∞`, then `G(n, p(n))` contains a triangle with probability tending
to `1`. -/
theorem tendsto_binomialRandom_real_not_cliqueFree_three_nhds_one {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop atTop) :
    Tendsto (fun n => G(Fin n, p n).real {G | ¬G.CliqueFree 3}) atTop (𝓝 1) := by
  have h := (tendsto_binomialRandom_real_cliqueFree_three hp).const_sub 1
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  rw [← Set.compl_ofPred, probReal_compl_eq_one_sub (measurableSet_cliqueFree 3)]

end SimpleGraph
