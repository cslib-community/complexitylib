/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Combinatorics/BinomialRandomGraph/`)

public import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.EdgePattern
public import Mathlib.Logic.Embedding.Basic

/-!
# Extension witnesses in binomial random graphs

Fix distinct vertices `x 0, …, x (k - 1)` of a finite vertex type `V` and a pattern
`s : Fin k → Bool`. A vertex `z` outside the tuple *witnesses* `s` in a graph `G` when `z` is
adjacent to `x i` exactly when `s i = true`. In the binomial random graph `G(V, p)` each outside
vertex witnesses `s` with probability `w = ∏ i, (if s i then p else 1 - p)`, independently of the
other outside vertices, because the pairs `{z, x i}` for different `z` are disjoint. Hence no vertex
witnesses `s` with probability exactly `(1 - w) ^ (|V| - k)`
(`SimpleGraph.binomialRandom_real_forall_not_witness`).

This is the probabilistic step of the extension axioms of the random graph: summing over the
injective tuples gives the failure bound for one extension axiom, and so its almost-sure validity in
`G(n, p)` for constant `0 < p < 1` [AlonSpencer2016, Section 10.4], as in Fagin's proof of the
`p = 1/2` law [Fagin1976]. The exact product formula and its derivation from
`SimpleGraph.binomialRandom_real_edgePattern_of_injective`, by summing over the adjacency patterns
of the outside vertices that avoid `s`, are this formalization's route; the 0-1 law only needs the
upper bound `(1 - min (p, 1 - p) ^ k) ^ (|V| - k)` that follows from it.

## Main results

* `SimpleGraph.binomialRandom_real_forall_not_witness`: no vertex outside `x` witnesses `s` with
  probability `(1 - ∏ i, (if s i then p else 1 - p)) ^ (|V| - k)`.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 10.4][AlonSpencer2016] (locator from
  secondary sources, unverified)
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset

namespace SimpleGraph

variable {V : Type*}

/-- **Extension witnesses in `G(V, p)`.** For distinct vertices `x 0, …, x (k - 1)` and a pattern
`s : Fin k → Bool`, the probability that no vertex `z` outside `x` is adjacent to exactly those
`x i` with `s i = true` is `(1 - ∏ i, (if s i then p else 1 - p)) ^ (|V| - k)`. -/
theorem binomialRandom_real_forall_not_witness [Fintype V] (p : I) {k : ℕ} (x : Fin k ↪ V)
    (s : Fin k → Bool) :
    G(V, p).real {G | ∀ z, ¬((∀ i, z ≠ x i) ∧ ∀ i, (G.Adj z (x i) ↔ s i = true))} =
      (1 - ∏ i, (if s i then (p : ℝ) else 1 - p)) ^ (Fintype.card V - k) := by
  classical
  -- The vertices outside `x`, and the pairs joining them to `x`.
  let O := {z : V // z ∉ Set.range x}
  let f : O × Fin k → Sym2 V := fun q => s(q.1.1, x q.2)
  have hf : Function.Injective f := by
    rintro ⟨z, i⟩ ⟨z', i'⟩ h
    rcases Sym2.eq_iff.1 h with ⟨hz, hi⟩ | ⟨hz, -⟩
    · exact Prod.ext (Subtype.ext hz) (x.injective hi)
    · exact absurd ⟨i', hz.symm⟩ z.2
  have hd : ∀ q, ¬(f q).IsDiag := fun q h => q.1.2 ⟨q.2, (Sym2.mk_isDiag_iff.1 h).symm⟩
  -- The event that the adjacency pattern of the outside vertices towards `x` is `t`.
  let E : (O → Fin k → Bool) → Set (SimpleGraph V) :=
    fun t => {G | ∀ q : O × Fin k, (f q ∈ G.edgeSet ↔ t q.1 q.2 = true)}
  let w : Bool → ℝ := fun b => if b then (p : ℝ) else 1 - p
  have hE : ∀ t, G(V, p).real (E t) = ∏ z, ∏ i, w (t z i) := fun t => by
    rw [binomialRandom_real_edgePattern_of_injective p hf hd, Fintype.prod_prod_type]
  -- No vertex witnesses `s` exactly when the pattern of every outside vertex differs from `s`.
  let A : Finset (O → Fin k → Bool) := Fintype.piFinset fun _ => univ.erase s
  have hset : {G : SimpleGraph V | ∀ z, ¬((∀ i, z ≠ x i) ∧ ∀ i, (G.Adj z (x i) ↔ s i = true))} =
      ⋃ t ∈ A, E t := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, A, E, f, mem_edgeSet,
      Fintype.mem_piFinset, mem_erase, mem_univ, and_true, Prod.forall]
    constructor
    · intro h
      refine ⟨fun z i => decide (G.Adj z (x i)), fun z hz => h z ?_, fun z i => ?_⟩
      · refine ⟨fun i he => z.2 ⟨i, he.symm⟩, fun i => ?_⟩
        rw [← congrFun hz i, decide_eq_true_iff]
      · rw [decide_eq_true_iff]
    · rintro ⟨t, ht, hG⟩ z ⟨hne, hadj⟩
      have hz : z ∉ Set.range x := fun ⟨i, hi⟩ => hne i hi.symm
      refine ht ⟨z, hz⟩ (funext fun i => ?_)
      rw [Bool.eq_iff_iff, ← hG ⟨z, hz⟩ i, ← hadj i]
  have hdisj : (A : Set (O → Fin k → Bool)).PairwiseDisjoint E := by
    intro t _ t' _ htt'
    refine Set.disjoint_left.2 fun G hG hG' => htt' (funext fun z => funext fun i => ?_)
    rw [Bool.eq_iff_iff, ← hG (z, i), hG' (z, i)]
  rw [hset, measureReal_biUnion_finset hdisj fun t _ => (E t).toFinite.measurableSet]
  simp only [hE]
  -- Sum over the patterns avoiding `s`, one outside vertex at a time.
  have h1 : ∑ b : Fin k → Bool, ∏ i, w (b i) = 1 := by
    rw [← Fintype.prod_sum]
    simp [w]
  rw [Finset.sum_prod_piFinset (univ.erase s) fun _ b => ∏ i, w (b i),
    Finset.sum_erase_eq_sub (mem_univ s), h1, prod_const, card_univ]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin]

end SimpleGraph
