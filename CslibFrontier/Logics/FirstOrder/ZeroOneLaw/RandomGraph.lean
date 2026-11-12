/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.EvenEdges
public import CslibFrontier.Probability.PMF
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.SymmDiff
import CslibFrontier.Foundations.MeasureTheory.Constructions.SimpleGraph
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Probability.PMF.Uniform

/-!
# The uniform random graph `G(n, 1/2)`

`Cslib.Logic.FO.graph.randomGraph n` is the uniform distribution on the labelled simple graphs
with vertex set `Fin n`, the random graph `G(n, 1/2)` of the 0-1 law for first-order logic
[Fagin1976] [Libkin2004, Section 12.1]. `Cslib.Logic.FO.graph.randomGraphProb n P` is the
probability that it has the property `P`, that is, the fraction of the labelled graphs on `Fin n`
with `P`.

Besides the basic API (complement, monotonicity, union bound), this file records a counting
principle: a property exchanged with its negation by an involution of the graphs on `Fin n` has
probability exactly `1/2`. Toggling one potential edge is such an involution, so every potential
edge is present with probability `1/2`, and for `n ≥ 2` the number of edges is even with
probability exactly `1/2`.

`randomGraph n` is Mathlib's binomial random graph `G(Fin n, p)` (`SimpleGraph.binomialRandom`) at
`p = 1/2`: under both, every labelled graph on `Fin n` has the same probability
(`Cslib.Logic.FO.graph.binomialRandom_real_eq_randomGraphProb`).

## Main definitions

* `Cslib.Logic.FO.graph.randomGraph`: the uniform distribution on `SimpleGraph (Fin n)`.
* `Cslib.Logic.FO.graph.randomGraphProb`: the probability of a graph property under it.

## Main results

* `Cslib.Logic.FO.graph.randomGraphProb_eq`: the probability is a ratio of graph counts.
* `Cslib.Logic.FO.graph.randomGraphProb_not`, `Cslib.Logic.FO.graph.randomGraphProb_mono`,
  `Cslib.Logic.FO.graph.randomGraphProb_exists_le`: complement, monotonicity, union bound.
* `Cslib.Logic.FO.graph.randomGraphProb_eq_half_of_involutive`: probability `1/2` from an
  involution exchanging a property and its negation.
* `Cslib.Logic.FO.graph.randomGraphProb_adj`: each potential edge has probability `1/2`.
* `Cslib.Logic.FO.graph.randomGraphProb_evenEdges`: an even number of edges has probability `1/2`.
* `Cslib.Logic.FO.graph.binomialRandom_real_eq_randomGraphProb`: `G(Fin n, 1/2)` is the uniform
  random graph.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Section 12.1.
-/

public section

open Cslib.Probability

namespace Cslib.Logic.FO.graph

/-- The **uniform random graph** `G(n, 1/2)`: the uniform distribution on the labelled simple
graphs with vertex set `Fin n` [Libkin2004, Section 12.1]. -/
noncomputable def randomGraph (n : ℕ) : PMF (SimpleGraph (Fin n)) :=
  PMF.uniformOfFintype (SimpleGraph (Fin n))

/-- The probability that `G(n, 1/2)` has the property `P`. -/
noncomputable def randomGraphProb (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((randomGraph n).toOuterMeasure {G | P G}).toReal

theorem randomGraphProb_def (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    randomGraphProb n P = ((randomGraph n).toOuterMeasure {G | P G}).toReal := by
  rw [randomGraphProb]

/-- The probability of `P` is the fraction of labelled graphs on `Fin n` with property `P`. -/
theorem randomGraphProb_eq (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    randomGraphProb n P = Nat.card {G // P G} / Nat.card (SimpleGraph (Fin n)) := by
  classical
  rw [randomGraphProb, randomGraph, PMF.toOuterMeasure_uniformOfFintype_toReal,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem randomGraphProb_nonneg (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    0 ≤ randomGraphProb n P :=
  ENNReal.toReal_nonneg

/-- The probability of `¬ P` is one minus the probability of `P`. -/
theorem randomGraphProb_not (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    randomGraphProb n (fun G => ¬P G) = 1 - randomGraphProb n P := by
  rw [randomGraphProb, randomGraphProb,
    ← PMF.toOuterMeasure_toReal_add_compl (randomGraph n) {G | P G}, add_sub_cancel_left]
  rfl

theorem randomGraphProb_le_one (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    randomGraphProb n P ≤ 1 := by
  have h := randomGraphProb_not n P
  have h0 := randomGraphProb_nonneg n fun G => ¬P G
  linarith

theorem randomGraphProb_mono {n : ℕ} {P Q : SimpleGraph (Fin n) → Prop} (h : ∀ G, P G → Q G) :
    randomGraphProb n P ≤ randomGraphProb n Q :=
  PMF.toOuterMeasure_toReal_mono _ fun G hG => h G hG

@[simp]
theorem randomGraphProb_false (n : ℕ) : randomGraphProb n (fun _ => False) = 0 := by
  rw [randomGraphProb, Set.ofPred_false, MeasureTheory.measure_empty, ENNReal.toReal_zero]

@[simp]
theorem randomGraphProb_true (n : ℕ) : randomGraphProb n (fun _ => True) = 1 := by
  have h := randomGraphProb_not n fun _ => True
  simp only [not_true_eq_false, randomGraphProb_false] at h
  linarith

/-- A property of positive probability holds for some graph. -/
theorem exists_of_randomGraphProb_pos {n : ℕ} {P : SimpleGraph (Fin n) → Prop}
    (h : 0 < randomGraphProb n P) : ∃ G, P G := by
  by_contra hne
  push Not at hne
  have := randomGraphProb_mono (Q := fun _ => False) fun G hG => hne G hG
  rw [randomGraphProb_false] at this
  linarith

/-- **Union bound.** -/
theorem randomGraphProb_exists_le {ι : Type*} (n : ℕ) (I : Finset ι)
    (P : ι → SimpleGraph (Fin n) → Prop) :
    randomGraphProb n (fun G => ∃ i ∈ I, P i G) ≤ ∑ i ∈ I, randomGraphProb n (P i) := by
  have hset : {G | ∃ i ∈ I, P i G} = ⋃ i ∈ I, {G | P i G} := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [randomGraphProb, hset]
  exact Cslib.Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le _ I fun i => {G | P i G}

/-- If an involution of the graphs on `Fin n` exchanges `P` and `¬ P`, then `P` has probability
exactly `1/2`. -/
theorem randomGraphProb_eq_half_of_involutive {n : ℕ} {P : SimpleGraph (Fin n) → Prop}
    (τ : SimpleGraph (Fin n) → SimpleGraph (Fin n)) (hτ : Function.Involutive τ)
    (hP : ∀ G, P (τ G) ↔ ¬P G) : randomGraphProb n P = 1 / 2 := by
  have hcard : Nat.card {G // P G} = Nat.card {G // ¬P G} :=
    Nat.card_congr ((hτ.toPerm τ).subtypeEquiv fun G => by
      rw [Function.Involutive.coe_toPerm, hP, not_not])
  have h : randomGraphProb n P = randomGraphProb n fun G => ¬P G := by
    rw [randomGraphProb_eq, randomGraphProb_eq, hcard]
  rw [randomGraphProb_not] at h
  linarith

/-- Toggle the potential edge `uv`. -/
private def toggleEdge {n : ℕ} (u v : Fin n) (G : SimpleGraph (Fin n)) : SimpleGraph (Fin n) :=
  symmDiff G (SimpleGraph.edge u v)

private theorem toggleEdge_involutive {n : ℕ} (u v : Fin n) :
    Function.Involutive (toggleEdge u v) :=
  fun G => symmDiff_symmDiff_cancel_right (SimpleGraph.edge u v) G

/-- In `G(n, 1/2)`, each potential edge is present with probability `1/2`. -/
theorem randomGraphProb_adj {n : ℕ} {u v : Fin n} (huv : u ≠ v) :
    randomGraphProb n (fun G => G.Adj u v) = 1 / 2 := by
  refine randomGraphProb_eq_half_of_involutive (toggleEdge u v) (toggleEdge_involutive u v)
    fun G => ?_
  rw [toggleEdge, SimpleGraph.symmDiff_adj, SimpleGraph.edge_adj]
  simp only [and_self, true_or, ne_eq, huv, not_false_eq_true, not_true_eq_false, and_false,
    false_or, true_and]

/-- For `n ≥ 2`, `G(n, 1/2)` has an even number of edges with probability exactly `1/2`. -/
theorem randomGraphProb_evenEdges {n : ℕ} (hn : 2 ≤ n) :
    randomGraphProb n SimpleGraph.EvenEdges = 1 / 2 := by
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := Fin.ne_of_val_ne zero_ne_one
  exact randomGraphProb_eq_half_of_involutive (toggleEdge u v) (toggleEdge_involutive u v)
    (SimpleGraph.evenEdges_symmDiff_edge_iff huv)

/-! ### `G(n, 1/2)` is the uniform random graph -/

section Binomial

open MeasureTheory unitInterval
open scoped SimpleGraph

/-- **`G(n, 1/2)` is the uniform random graph.** At `p = 1/2` every labelled graph on `Fin n` has
the same probability `2 ^ (-n (n - 1) / 2)`, so the probability of a graph property in
`G(Fin n, p)` is its probability `randomGraphProb n P` in `Cslib.Logic.FO.graph.randomGraph`. -/
theorem binomialRandom_real_eq_randomGraphProb {p : I} (hp : (p : ℝ) = 1 / 2) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) :
    G(Fin n, p).real {G | P G} = randomGraphProb n P := by
  classical
  have hσ : toNNReal (σ p) = toNNReal p := NNReal.eq (by
    rw [coe_toNNReal, coe_toNNReal, coe_symm_eq, hp]
    norm_num)
  -- Every graph has the same probability `c`.
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, ((toNNReal p : ENNReal) ^ (Nat.card (Fin n)).choose 2) = c :=
    ⟨_, rfl⟩
  have hsingle : ∀ G : SimpleGraph (Fin n), G(Fin n, p) {G} = c := fun G => by
    have hle : G.edgeSet.ncard ≤ (Nat.card (Fin n)).choose 2 := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, Nat.card_eq_fintype_card]
      exact G.card_edgeFinset_le_card_choose_two
    rw [SimpleGraph.binomialRandom_singleton, hσ, ← pow_add, Nat.add_sub_cancel' hle, hc]
  have hset : ∀ S : Set (SimpleGraph (Fin n)), G(Fin n, p) S = S.ncard * c := fun S => by
    rw [← Set.coe_toFinset S, ← sum_measure_singleton, Finset.sum_congr rfl fun G _ => hsingle G,
      Finset.sum_const, nsmul_eq_mul, Set.ncard_coe_finset]
  -- Total mass one forces `c = 1 / #(SimpleGraph (Fin n))`.
  have hc' : c = (Nat.card (SimpleGraph (Fin n)) : ENNReal)⁻¹ := by
    refine ENNReal.eq_inv_of_mul_eq_one_left ?_
    rw [mul_comm, ← Set.ncard_univ, ← hset, measure_univ]
  rw [randomGraphProb_eq, measureReal_def, hset, hc', ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv,
    ← Nat.card_coe_set_eq {G | P G}]
  rfl

end Binomial

end Cslib.Logic.FO.graph
