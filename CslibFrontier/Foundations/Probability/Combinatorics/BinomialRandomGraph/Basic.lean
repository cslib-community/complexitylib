/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Combinatorics/BinomialRandomGraph/`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.EdgePattern
import CslibFrontier.Foundations.Probability.SecondMoment
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Subgraph probabilities in binomial random graphs

Mathlib's `SimpleGraph.binomialRandom V p`, written `G(V, p)`, is the law of the random simple
graph on `V` in which each pair of distinct vertices is an edge independently with probability
`p`. This file computes the basic probabilities of `G(V, p)` for countable `V`:

* `G(V, p)` contains a fixed finite set `s` of non-diagonal edges with probability `p ^ |s|`
  (`SimpleGraph.binomialRandom_real_subset_edgeSet`) and avoids a fixed finite set `t` of
  non-diagonal edges with probability `(1 - p) ^ |t|`
  (`SimpleGraph.binomialRandom_real_disjoint_edgeSet`), so it contains a fixed subgraph `H` on its
  own vertex set with probability `p ^ e(H)` (`SimpleGraph.binomialRandom_real_setOf_le`);
* for finite `V` the expected number of labelled copies of a finite graph `H` is the falling
  factorial `|V| (|V| - 1) ⋯ (|V| - v(H) + 1)` times `p ^ e(H)`
  (`SimpleGraph.integral_labelledCopyCount`), and by the union
  bound `G(V, p)` contains a copy of `H` with at most this probability
  (`SimpleGraph.binomialRandom_real_isContained_le`);
* consequently, if `n ^ v(H) p(n) ^ e(H) → 0`, then `G(n, p(n))` contains no copy of `H` with
  probability tending to `1` (`SimpleGraph.tendsto_binomialRandom_real_isContained`). This is the
  first-moment half of the small-subgraph threshold theorem
  [Janson, Łuczak and Ruciński, Chapter 3][JansonLuczakRucinski2000]; applied to the densest
  subgraph of `H`, it gives the `0`-statement below `n ^ (-1 / m(H))`. The second-moment half is
  proved for triangles in the sibling module `BinomialRandomGraph.Clique`.

## Main results

* `SimpleGraph.measurableSet_subset_edgeSet`, `SimpleGraph.measurableSet_setOf_le`: events
  defined by required edges are measurable.
* `SimpleGraph.binomialRandom_real_subset_edgeSet`,
  `SimpleGraph.binomialRandom_real_disjoint_edgeSet`,
  `SimpleGraph.binomialRandom_real_setOf_le`:
  the probability of containing or avoiding a fixed set of edges or containing a fixed subgraph.
* `SimpleGraph.integral_labelledCopyCount`: the expected number of labelled copies of `H`.
* `SimpleGraph.binomialRandom_real_isContained_le`: the first-moment bound for containing `H`.
* `SimpleGraph.tendsto_binomialRandom_real_isContained`: its asymptotic form.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 4.4][AlonSpencer2016]
* [S. Janson, T. Łuczak, A. Ruciński, *Random Graphs*, Chapter 3][JansonLuczakRucinski2000]
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Finset Topology

namespace SimpleGraph

variable {V W : Type*}

/-! ### Fixed edges and fixed subgraphs -/

/-- The graphs containing a given set of edges form a measurable set. -/
theorem measurableSet_subset_edgeSet [Countable V] (s : Set (Sym2 V)) :
    MeasurableSet {G : SimpleGraph V | s ⊆ G.edgeSet} := by
  simpa [Set.subset_def] using measurableSet_edgePattern s fun _ => true

/-- The supergraphs of a given graph form a measurable set. -/
theorem measurableSet_setOf_le [Countable V] (H : SimpleGraph V) :
    MeasurableSet {G : SimpleGraph V | H ≤ G} := by
  simpa only [← edgeSet_subset_edgeSet] using measurableSet_subset_edgeSet H.edgeSet

/-- `G(V, p)` contains a fixed finite set `s` of non-diagonal edges with probability `p ^ |s|`:
the constant pattern `true` in `SimpleGraph.binomialRandom_edgePattern`. -/
theorem binomialRandom_subset_edgeSet [Countable V] (p : I) (s : Finset (Sym2 V))
    (hs : ∀ e ∈ s, ¬e.IsDiag) :
    G(V, p) {G | (s : Set (Sym2 V)) ⊆ G.edgeSet} = toNNReal p ^ #s := by
  have h := binomialRandom_edgePattern p s hs fun _ => true
  simp only [iff_true, ↓reduceIte, Finset.prod_const] at h
  exact h

/-- `G(V, p)` contains a fixed finite set `s` of non-diagonal edges with probability `p ^ |s|`. -/
theorem binomialRandom_real_subset_edgeSet [Countable V] (p : I) (s : Finset (Sym2 V))
    (hs : ∀ e ∈ s, ¬e.IsDiag) :
    G(V, p).real {G | (s : Set (Sym2 V)) ⊆ G.edgeSet} = (p : ℝ) ^ #s := by
  rw [measureReal_def, binomialRandom_subset_edgeSet p s hs]
  simp

/-- `G(V, p)` has no edge in a fixed finite set `t` of non-diagonal edges with probability
`(1 - p) ^ |t|`: the constant pattern `false` in `SimpleGraph.binomialRandom_edgePattern`. -/
theorem binomialRandom_disjoint_edgeSet [Countable V] (p : I) (t : Finset (Sym2 V))
    (ht : ∀ e ∈ t, ¬e.IsDiag) :
    G(V, p) {G | Disjoint (t : Set (Sym2 V)) G.edgeSet} = toNNReal (σ p) ^ #t := by
  have h := binomialRandom_edgePattern p t ht fun _ => false
  simp only [Bool.false_eq_true, iff_false, ↓reduceIte, Finset.prod_const] at h
  rw [← h]
  congr 1
  ext G
  simp [Set.disjoint_left]

/-- `G(V, p)` has no edge in a fixed finite set `t` of non-diagonal edges with probability
`(1 - p) ^ |t|`. -/
theorem binomialRandom_real_disjoint_edgeSet [Countable V] (p : I) (t : Finset (Sym2 V))
    (ht : ∀ e ∈ t, ¬e.IsDiag) :
    G(V, p).real {G | Disjoint (t : Set (Sym2 V)) G.edgeSet} = (1 - p : ℝ) ^ #t := by
  rw [measureReal_def, binomialRandom_disjoint_edgeSet p t ht]
  simp

/-- `G(V, p)` contains a fixed subgraph `H` with finitely many edges with probability
`p ^ e(H)`. -/
theorem binomialRandom_real_setOf_le [Countable V] (p : I) (H : SimpleGraph V) [Fintype H.edgeSet] :
    G(V, p).real {G | H ≤ G} = (p : ℝ) ^ #H.edgeFinset := by
  have : {G : SimpleGraph V | H ≤ G} =
      {G | ((H.edgeFinset : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ G.edgeSet} := by
    ext G; simp
  rw [this, binomialRandom_real_subset_edgeSet p _ fun e he => not_isDiag_of_mem_edgeFinset he]

/-! ### Labelled copies -/

/-- Copies of `H` in `G` are the vertex embeddings under which the image of `H` is a subgraph of
`G`. -/
private def copyEquiv (H : SimpleGraph W) (G : SimpleGraph V) :
    Copy H G ≃ {f : W ↪ V // H.map f ≤ G} where
  toFun c := ⟨c.toEmbedding, map_le_iff_le_comap.2 fun _ _ h => c.toHom.map_adj h⟩
  invFun f := ⟨⟨f.1, fun h => (map_le_iff_le_comap.1 f.2) h⟩, f.1.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The image of `H` under a fixed vertex embedding is present in `G(V, p)` with probability
`p ^ e(H)`. -/
private theorem binomialRandom_real_setOf_map_le [Finite V] [Finite W] (p : I) (H : SimpleGraph W)
    [Fintype H.edgeSet] (f : W ↪ V) :
    G(V, p).real {G | H.map f ≤ G} = (p : ℝ) ^ #H.edgeFinset := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite W
  rw [binomialRandom_real_setOf_le]
  congr 1
  convert card_edgeFinset_map f H

/-- **The expected number of labelled copies** of a graph `H` in `G(V, p)` is the falling
factorial `|V| (|V| - 1) ⋯ (|V| - v(H) + 1)` times `p ^ e(H)`
[Alon and Spencer, Section 4.4][AlonSpencer2016]. -/
theorem integral_labelledCopyCount [Fintype V] [Fintype W] (p : I) (H : SimpleGraph W)
    [Fintype H.edgeSet] :
    ∫ G, (G.labelledCopyCount H : ℝ) ∂G(V, p) =
      (Fintype.card V).descFactorial (Fintype.card W) * (p : ℝ) ^ #H.edgeFinset := by
  classical
  have hcount (G : SimpleGraph V) : (G.labelledCopyCount H : ℝ) =
      ∑ f : W ↪ V, {G : SimpleGraph V | H.map f ≤ G}.indicator (1 : SimpleGraph V → ℝ) G := by
    rw [labelledCopyCount, Fintype.card_eq_nat_card, Nat.card_congr (copyEquiv H G),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [Set.indicator_apply, Finset.sum_boole]
  simp_rw [hcount]
  rw [integral_sum_indicator_one _ fun f _ => measurableSet_setOf_le _]
  simp_rw [binomialRandom_real_setOf_map_le]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, nsmul_eq_mul]

/-- **First moment bound for containment** [Alon and Spencer, Section 4.4][AlonSpencer2016]:
`G(V, p)` contains a copy of `H` with probability at most the expected number
`|V| (|V| - 1) ⋯ (|V| - v(H) + 1) · p ^ e(H)` of labelled copies. -/
theorem binomialRandom_real_isContained_le [Fintype V] [Fintype W] (p : I) (H : SimpleGraph W)
    [Fintype H.edgeSet] :
    G(V, p).real {G | H ⊑ G} ≤
      (Fintype.card V).descFactorial (Fintype.card W) * (p : ℝ) ^ #H.edgeFinset := by
  classical
  have hset : {G : SimpleGraph V | H ⊑ G} = ⋃ f ∈ (univ : Finset (W ↪ V)), {G | H.map f ≤ G} := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_univ, exists_const,
      isContained_iff_exists_le_comap, map_le_iff_le_comap]
  rw [hset]
  refine (measureReal_biUnion_finset_le _ _).trans_eq ?_
  simp_rw [binomialRandom_real_setOf_map_le]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, nsmul_eq_mul]

/-- **Below the first-moment threshold** [Janson, Łuczak and Ruciński, Chapter 3]
[JansonLuczakRucinski2000]: if `n ^ v(H) p(n) ^ e(H) → 0`, then `G(n, p(n))` contains a copy of
`H` with probability tending to `0`. -/
theorem tendsto_binomialRandom_real_isContained [Fintype W] (H : SimpleGraph W)
    [Fintype H.edgeSet] {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) ^ Fintype.card W * (p n : ℝ) ^ #H.edgeFinset) atTop
      (𝓝 0)) :
    Tendsto (fun n => G(Fin n, p n).real {G | H ⊑ G}) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hp
  refine (binomialRandom_real_isContained_le (p n) H).trans ?_
  rw [Fintype.card_fin]
  gcongr
  · exact pow_nonneg (p n).2.1 _
  · exact_mod_cast Nat.descFactorial_le_pow n _

end SimpleGraph
