/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Combinatorics/BinomialRandomGraph/`)

public import CslibFrontier.Foundations.MeasureTheory.Constructions.SimpleGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

/-!
# Edge patterns in binomial random graphs

In Mathlib's binomial random graph `G(V, p)` (`SimpleGraph.binomialRandom V p`), the pairs of
distinct vertices are edges independently with probability `p`. This file states that
independence for finitely many pairs: `G(V, p)` gives a finite set `t` of non-diagonal pairs a
prescribed pattern `b : Sym2 V → Bool` of edges (`e` is an edge exactly when `b e = true`) with
probability `∏ e ∈ t, (if b e then p else 1 - p)`. A fixed set of pairs being all edges
(probability `p ^ |t|`, `SimpleGraph.binomialRandom_subset_edgeSet`) or all non-edges (probability
`(1 - p) ^ |t|`, `SimpleGraph.binomialRandom_disjoint_edgeSet`) is the special case of a constant
pattern. Measurability of these events is `SimpleGraph.measurableSet_edgePattern`.

## Main results

* `SimpleGraph.binomialRandom_edgePattern`, `SimpleGraph.binomialRandom_real_edgePattern`: the
  probability of a prescribed edge pattern on a finite set of pairs.
* `SimpleGraph.binomialRandom_real_edgePattern_of_injective`: the same, for pairs indexed by an
  injective family.
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset

namespace SimpleGraph

variable {V : Type*}

/-- **Edge independence in `G(V, p)`.** `G(V, p)` gives a finite set `t` of non-diagonal pairs the
pattern `b` (each `e ∈ t` is an edge exactly when `b e = true`) with probability
`∏ e ∈ t, (if b e then p else 1 - p)`. This is a statement about `setBernoulli` transported along
`fromEdgeSet`; upstream it belongs next to the `setBernoulli` API. -/
theorem binomialRandom_edgePattern [Countable V] (p : I) (t : Finset (Sym2 V))
    (ht : ∀ e ∈ t, ¬e.IsDiag) (b : Sym2 V → Bool) :
    G(V, p) {G | ∀ e ∈ t, (e ∈ G.edgeSet ↔ b e = true)} =
      ∏ e ∈ t, ((if b e then toNNReal p else toNNReal (σ p) : NNReal) : ENNReal) := by
  have hm : MeasurableSet {G : SimpleGraph V | ∀ e ∈ t, (e ∈ G.edgeSet ↔ b e = true)} := by
    simpa only [Finset.mem_coe] using measurableSet_edgePattern (t : Set (Sym2 V)) b
  rw [binomialRandom_eq_map, Measure.map_apply measurable_fromEdgeSet hm, setBernoulli_apply']
  have : (fun q : Sym2 V → Prop => {i | q i}) ⁻¹'
      (fromEdgeSet ⁻¹' {G | ∀ e ∈ t, (e ∈ G.edgeSet ↔ b e = true)}) =
      Set.pi (t : Set (Sym2 V)) (fun e => {(b e = true : Prop)}) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, edgeSet_fromEdgeSet, Set.mem_sdiff,
      Set.mem_pi, Finset.mem_coe, Set.mem_singleton_iff, eq_iff_iff]
    exact forall₂_congr fun e he => by
      rw [and_iff_left (show e ∉ Sym2.diagSet from ht e he)]
  rw [this, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  refine Finset.prod_congr rfl fun e he => ?_
  have hd : ¬e.IsDiag := ht e he
  cases b e
  · rw [bernoulliMeasure_apply_of_notMem_of_mem p (measurableSet_singleton _)]
    · simp
    · simpa using hd
    · simp
  · rw [bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _)]
    · simp
    · simpa using hd
    · simp

/-- **Edge independence in `G(V, p)`.** `G(V, p)` gives a finite set `t` of non-diagonal pairs the
pattern `b` with probability `∏ e ∈ t, (if b e then p else 1 - p)`. -/
theorem binomialRandom_real_edgePattern [Countable V] (p : I) (t : Finset (Sym2 V))
    (ht : ∀ e ∈ t, ¬e.IsDiag) (b : Sym2 V → Bool) :
    G(V, p).real {G | ∀ e ∈ t, (e ∈ G.edgeSet ↔ b e = true)} =
      ∏ e ∈ t, (if b e then (p : ℝ) else 1 - p) := by
  rw [measureReal_def, binomialRandom_edgePattern p t ht b, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  cases b e <;> simp

/-- **Edge independence in `G(V, p)`, indexed form.** For an injective family `f : ι → Sym2 V` of
non-diagonal pairs indexed by a finite type and a pattern `c : ι → Bool`, `G(V, p)` makes each
`f i` an edge exactly when `c i = true` with probability `∏ i, (if c i then p else 1 - p)`. -/
theorem binomialRandom_real_edgePattern_of_injective [Countable V] {ι : Type*} [Fintype ι]
    (p : I) {f : ι → Sym2 V} (hf : Function.Injective f) (hd : ∀ i, ¬(f i).IsDiag)
    (c : ι → Bool) :
    G(V, p).real {G | ∀ i, (f i ∈ G.edgeSet ↔ c i = true)} =
      ∏ i, (if c i then (p : ℝ) else 1 - p) := by
  classical
  have ht : ∀ e ∈ univ.map ⟨f, hf⟩, ¬e.IsDiag := by
    simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk, forall_exists_index,
      forall_apply_eq_imp_iff]
    exact hd
  have h := binomialRandom_real_edgePattern p (univ.map ⟨f, hf⟩) ht
    (Function.extend f c fun _ => false)
  simp only [forall_mem_map, mem_univ, forall_const, Function.Embedding.coeFn_mk,
    hf.extend_apply, prod_map] at h
  exact h

end SimpleGraph
