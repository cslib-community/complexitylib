/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PropertyTesting.DenseGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.SymmDiff
import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.Product
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Testing bipartiteness in the dense graph model

Bipartiteness is one-sided testable in the dense graph model with a number of queries polynomial in
`1 / ε` and independent of the number of vertices [Goldreich, Goldwasser and
Ron][GoldreichGoldwasserRon1998]; see also [Goldreich, Chapter 8][Goldreich2017].

The tester `bipartiteRun n' s m` on `Fin (n' + 1)` samples `s` uniform vertices `u` and `m`
uniform pairs of vertices `(x k, y k)`, all independent. It queries the `m (2 s + 1)` pairs
`(x k, u i)`, `(y k, u i)` and `(x k, y k)` and accepts when there is a proper 2-colouring of the
sample *positions* (`bipAccept`): a colour for each index `i` of `u` and for each index `k` of `x`
and of `y`, with different colours at the two ends of every observed edge. A vertex that occurs at
several positions may receive different colours, so this is laxer than asking that the observed
subgraph be bipartite: with `s = 0` and `m = 3` on the triangle, the tester can observe all three
edges and still accept. A bipartite graph is always accepted, since a proper 2-colouring of the
graph induces one of the positions.

## Source mapping

The query pattern, with a vertex sample `U` and pairs each checked against `U` and against each
other, is that of [Goldreich, Goldwasser and Ron, §6.1.1, p. 683][GoldreichGoldwasserRon1998]. The
soundness argument follows their §6.1 (Theorem 6.1.2, Claims 6.1.4 and 6.1.6, pp. 679–683): a
2-partition of `U` forces a partition of the vertices with a neighbour in `U`, and a far graph
leaves many violating pairs under every such forced partition. Their factor-two distance
convention is §5.1, pp. 675–676. The open book draft of April 26, 2017 (§8.3.1, Algorithm 8.7 and
Lemma 8.8, pp. 174–177; the published book is [Goldreich][Goldreich2017], Chapter 8) presents the
same high-degree coverage argument.

*Adaptation in the coverage step.* GGR take `|U| = O(log (1 / (ε δ)) / ε)` so that, with high
probability, `U` dominates all but few high-degree vertices. The result is
`O(log² (1 / (ε δ)) / ε³)` queries. Here the coverage step is replaced by an expectation bound. The
expected degree mass of the vertices with no neighbour in `U` is at most `n² / (s + 1)`
(`sum_uncoveredDegree_le`, from `d (n - d) ^ s ≤ n ^ (s + 1) / (s + 1)`). Markov's inequality then
suffices at constant confidence, so `s = ⌈12 / ε⌉` works and the logarithmic factors disappear.
This refinement of the analysis is ours; we do not know of an exact source for it and claim no
novelty for it. It gives no asymptotic improvement over the `Õ(ε⁻²)` bound of
[Alon and Krivelevich][AlonKrivelevich2002].

## Proof outline

A colouring `χ` of the sampled vertices forces a colour on every vertex with a sampled neighbour,
the colour opposite to that neighbour's.
If the tester accepts, some `χ` leaves every sampled pair `(x k, y k)` outside the set of *bad*
pairs: edges between two vertices with sampled neighbours that receive the same forced colour.
Extending the forced colouring arbitrarily, an `ε`-far graph has more than `2 ε n²` ordered
monochromatic adjacent pairs, and those not bad have an endpoint without a sampled neighbour. The
expected degree mass of the vertices without a sampled neighbour is at most `n² / (s + 1)`, so by
Markov's inequality it exceeds `ε n² / 2` with probability at most `2 / (ε (s + 1))`. Otherwise
every colouring of the sample has more than `ε n²` ordered bad pairs, and the `m` independent pairs
all avoid them with probability at most `(1 - ε) ^ m`. A union bound over the `2 ^ s` colourings
gives

`acceptProb ≤ 2 / (ε (s + 1)) + 2 ^ s (1 - ε) ^ m ≤ 1 / 6 + 1 / 8 < 1 / 3`

when `12 ≤ ε s` and `s + 3 ≤ ε m`. With `s = ⌈12 / ε⌉` and `m = ⌈(s + 3) / ε⌉` the tester asks
`m (2 s + 1) ≤ 459 / ε³` queries for `ε ≤ 1`. Distances are those of `IsFar`, relative to `n²`
vertex pairs; Goldreich's distance `ε` is `IsFar G P (ε / 2)` here.

This file bounds queries only; it makes no claim about running time. The `O(ε⁻³)` bound is not
optimal: a uniform sample of `Õ(1 / ε)` vertices already induces a non-bipartite subgraph of an
`ε`-far graph with high probability, which gives `Õ(ε⁻²)` queries
[Alon and Krivelevich][AlonKrivelevich2002].

## Main definitions

* `Cslib.DenseGraphTesting.bipAccept`: accept when the sample positions admit a proper
  2-colouring.
* `Cslib.DenseGraphTesting.bipartiteRun`, `bipartiteTester`: the bipartiteness tester.

## Main results

* `Cslib.DenseGraphTesting.IsFar.two_mul_lt_sum_monochromatic`: a graph `ε`-far from bipartite has
  more than `2 ε n²` ordered monochromatic adjacent pairs under every 2-colouring.
* `Cslib.DenseGraphTesting.acceptProb_bipartiteTester_eq_one`: perfect completeness.
* `Cslib.DenseGraphTesting.acceptProb_bipartiteTester_le_one_third`: soundness.
* `Cslib.DenseGraphTesting.isOneSidedTester_bipartiteTester`: the tester is a one-sided tester
  with `m (2 s + 1)` queries.
* `Cslib.DenseGraphTesting.oneSidedTestable_isBipartite`,
  `bipartiteQueryBound_le`: bipartiteness is one-sided testable with `O(ε⁻³)` queries.

## References

* [N. Alon, M. Krivelevich, *Testing k-colorability*][AlonKrivelevich2002]
* [O. Goldreich, S. Goldwasser, D. Ron, *Property testing and its connection to learning and
  approximation*][GoldreichGoldwasserRon1998]
* [O. Goldreich, *Introduction to Property Testing*][Goldreich2017]
-/

public section

namespace Cslib.DenseGraphTesting

open SimpleGraph Finset

/-! ### The decision rule -/

/-- The decision rule of the bipartiteness tester. The bits `a k i`, `b k i` and `c k` report
whether `x k ~ u i`, `y k ~ u i` and `x k ~ y k`; accept when the sample positions admit a proper
2-colouring: `χ` of the positions `i`, `ξ` and `ζ` of the positions `k` of `x` and of `y`. Colours
are attached to positions, not vertices, so a repeated vertex may receive two colours. -/
def bipAccept {s m : ℕ} (a b : Fin m → Fin s → Bool) (c : Fin m → Bool) : Bool :=
  decide (∃ (χ : Fin s → Bool) (ξ ζ : Fin m → Bool), (∀ k i, a k i = true → ξ k ≠ χ i) ∧
    (∀ k i, b k i = true → ζ k ≠ χ i) ∧ ∀ k, c k = true → ξ k ≠ ζ k)

theorem bipAccept_eq_true_iff {s m : ℕ} (a b : Fin m → Fin s → Bool) (c : Fin m → Bool) :
    bipAccept a b c = true ↔
      ∃ (χ : Fin s → Bool) (ξ ζ : Fin m → Bool), (∀ k i, a k i = true → ξ k ≠ χ i) ∧
        (∀ k i, b k i = true → ζ k ≠ χ i) ∧ ∀ k, c k = true → ξ k ≠ ζ k := by
  rw [bipAccept, decide_eq_true_iff]

/-! ### Monochromatic pairs -/

section Combinatorics

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edges of `G` whose endpoints receive the same colour under `f`. -/
private def monoGraph (f : V → Bool) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ f v = f w
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl v h := G.loopless.irrefl v h.1

private instance (f : V → Bool) : DecidableRel (monoGraph G f).Adj := fun v w =>
  inferInstanceAs (Decidable (G.Adj v w ∧ f v = f w))

omit [DecidableEq V] in
/-- Counting the neighbours of `v`. -/
private theorem sum_ite_adj (v : V) : (∑ w, if G.Adj v w then (1 : ℝ) else 0) = G.degree v := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]
  push_cast
  rfl

omit [DecidableEq V] in
/-- The handshake lemma for indicator sums. -/
private theorem sum_sum_ite_adj :
    (∑ v, ∑ w, if G.Adj v w then (1 : ℝ) else 0) = 2 * #G.edgeFinset := by
  rw [Finset.sum_congr rfl fun v _ => sum_ite_adj G v]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

variable {G}

omit [DecidableEq V] in
/-- A graph `ε`-far from bipartite has more than `2 ε n²` ordered adjacent pairs of the same colour
under every 2-colouring `f`: deleting them leaves a bipartite graph. -/
theorem IsFar.two_mul_lt_sum_monochromatic {ε : ℝ} (h : IsFar G (fun H => H.IsBipartite) ε)
    (f : V → Bool) :
    2 * (ε * (Fintype.card V ^ 2 : ℕ)) <
      ∑ v, ∑ w, if G.Adj v w ∧ f v = f w then (1 : ℝ) else 0 := by
  classical
  have hcol : (G \ monoGraph G f).Colorable 2 := by
    refine ⟨Coloring.mk (fun v => if f v then 0 else 1) fun {v w} hvw => ?_⟩
    simp only [sdiff_adj, monoGraph] at hvw
    have hne : f v ≠ f w := fun he => hvw.2 ⟨hvw.1, he⟩
    revert hne
    cases f v <;> cases f w <;> simp
  have hsymm : symmDiff G (G \ monoGraph G f) = monoGraph G f := by
    ext v w
    simp only [symmDiff_adj, sdiff_adj, monoGraph]
    tauto
  have he :
      symmDiff G.edgeFinset (G \ monoGraph G f).edgeFinset = (monoGraph G f).edgeFinset := by
    apply Finset.coe_injective
    rw [Finset.coe_symmDiff, coe_edgeFinset, coe_edgeFinset, coe_edgeFinset, ← edgeSet_symmDiff,
      hsymm]
  have hd : ε * (Fintype.card V ^ 2 : ℕ) < #(monoGraph G f).edgeFinset := by
    convert isFar_iff.mp h _ hcol using 2
    rw [editDist_eq_card]
    convert (congrArg Finset.card he).symm
  have hsum : (∑ v, ∑ w, if G.Adj v w ∧ f v = f w then (1 : ℝ) else 0) =
      2 * #(monoGraph G f).edgeFinset := by
    rw [← sum_sum_ite_adj (monoGraph G f)]
    rfl
  rw [hsum]
  linarith

/-! ### Forced colourings -/

variable {s : ℕ}

/-- `v` has a neighbour among the sampled vertices `u`. -/
private abbrev Covered (G : SimpleGraph V) (u : Fin s → V) (v : V) : Prop := ∃ i, G.Adj v (u i)

/-- The colour forced on `v` by a colouring `χ` of the sampled vertices `u`: opposite to the colour
of a sampled neighbour (`false` exactly when every sampled neighbour is coloured `true`). -/
private def forcedColor (G : SimpleGraph V) [DecidableRel G.Adj] (u : Fin s → V)
    (χ : Fin s → Bool) (v : V) : Bool :=
  decide (∃ i, G.Adj v (u i) ∧ χ i = false)

/-- An edge between two vertices with sampled neighbours that receive the same forced colour. -/
private abbrev IsBadPair (G : SimpleGraph V) [DecidableRel G.Adj] (u : Fin s → V)
    (χ : Fin s → Bool) (x y : V) : Prop :=
  G.Adj x y ∧ Covered G u x ∧ Covered G u y ∧ forcedColor G u χ x = forcedColor G u χ y

/-- The degree mass of the vertices without a sampled neighbour. -/
private def uncoveredDegree (G : SimpleGraph V) [DecidableRel G.Adj] (u : Fin s → V) : ℝ :=
  ∑ v, if Covered G u v then 0 else (G.degree v : ℝ)

omit [DecidableEq V] in
/-- The uncovered degree mass is nonnegative. -/
private theorem uncoveredDegree_nonneg (u : Fin s → V) : 0 ≤ uncoveredDegree G u :=
  sum_nonneg fun v _ => by split_ifs <;> positivity

omit [Fintype V] [DecidableEq V] in
/-- A colour different from that of every sampled neighbour is the forced colour. -/
private theorem eq_forcedColor {u : Fin s → V} {χ : Fin s → Bool} {w : V} {θ : Bool}
    (hθ : ∀ i, G.Adj w (u i) → θ ≠ χ i) (hw : Covered G u w) : θ = forcedColor G u χ w := by
  obtain ⟨i, hi⟩ := hw
  unfold forcedColor
  by_cases hex : ∃ j, G.Adj w (u j) ∧ χ j = false
  · obtain ⟨j, hj, hχ⟩ := hex
    have h₁ := hθ j hj
    rw [hχ] at h₁
    rw [decide_eq_true ⟨j, hj, hχ⟩]
    cases θ <;> simp_all
  · have hχi : χ i = true := by
      cases h : χ i
      · exact absurd ⟨i, hi, h⟩ hex
      · rfl
    have h₁ := hθ i hi
    rw [hχi] at h₁
    rw [decide_eq_false hex]
    cases θ <;> simp_all

omit [Fintype V] [DecidableEq V] in
/-- If the tester accepts, some colouring of the sample makes no sampled pair bad. -/
private theorem exists_forall_not_isBadPair {m : ℕ} {u : Fin s → V} {x y : Fin m → V}
    (h : bipAccept (fun k i => decide (G.Adj (x k) (u i))) (fun k i => decide (G.Adj (y k) (u i)))
      (fun k => decide (G.Adj (x k) (y k))) = true) :
    ∃ χ : Fin s → Bool, ∀ k, ¬ IsBadPair G u χ (x k) (y k) := by
  obtain ⟨χ, ξ, ζ, ha, hb, hc⟩ := of_decide_eq_true h
  refine ⟨χ, fun k ⟨hxy, hcx, hcy, heq⟩ => ?_⟩
  have h₁ := eq_forcedColor (fun i hi => ha k i (decide_eq_true hi)) hcx
  have h₂ := eq_forcedColor (fun i hi => hb k i (decide_eq_true hi)) hcy
  exact hc k (decide_eq_true hxy) (h₁.trans (heq.trans h₂.symm))

omit [Fintype V] [DecidableEq V] in
/-- A bipartite graph passes every sample. -/
private theorem bipAccept_of_colorable (hG : G.Colorable 2) {m : ℕ} (u : Fin s → V)
    (x y : Fin m → V) :
    bipAccept (fun k i => decide (G.Adj (x k) (u i))) (fun k i => decide (G.Adj (y k) (u i)))
      (fun k => decide (G.Adj (x k) (y k))) = true := by
  obtain ⟨C⟩ := hG
  let f : V → Bool := fun v => decide (C v = 0)
  have hf : ∀ v w, G.Adj v w → f v ≠ f w := by
    intro v w hvw
    have hne := C.valid hvw
    simp only [f]
    revert hne
    generalize C v = a
    generalize C w = b
    fin_cases a <;> fin_cases b <;> decide
  refine decide_eq_true ⟨fun i => f (u i), fun k => f (x k), fun k => f (y k), ?_, ?_, ?_⟩
  · exact fun k i h => hf _ _ (of_decide_eq_true h)
  · exact fun k i h => hf _ _ (of_decide_eq_true h)
  · exact fun k h => hf _ _ (of_decide_eq_true h)

omit [DecidableEq V] in
/-- Monochromatic pairs of the forced colouring are bad or have an uncovered endpoint. -/
private theorem sum_mono_le (u : Fin s → V) (χ : Fin s → Bool) :
    (∑ v, ∑ w, if G.Adj v w ∧ forcedColor G u χ v = forcedColor G u χ w then (1 : ℝ) else 0) ≤
      (∑ v, ∑ w, if IsBadPair G u χ v w then (1 : ℝ) else 0) + 2 * uncoveredDegree G u := by
  have h₁ : (∑ v, ∑ w, if ¬ Covered G u v ∧ G.Adj v w then (1 : ℝ) else 0) =
      uncoveredDegree G u := by
    unfold uncoveredDegree
    refine sum_congr rfl fun v _ => ?_
    by_cases hv : Covered G u v
    · simp only [hv, not_true_eq_false, false_and, ite_false, sum_const_zero, ite_true]
    · simp only [hv, not_false_eq_true, true_and, ite_false]
      exact sum_ite_adj G v
  have h₂ : (∑ v, ∑ w, if ¬ Covered G u w ∧ G.Adj v w then (1 : ℝ) else 0) =
      uncoveredDegree G u := by
    rw [Finset.sum_comm, ← h₁]
    refine sum_congr rfl fun v _ => sum_congr rfl fun w _ => ?_
    exact if_congr (and_congr_right' (G.adj_comm w v)) rfl rfl
  calc _ ≤ ∑ v, ∑ w, ((if IsBadPair G u χ v w then (1 : ℝ) else 0) +
          (if ¬ Covered G u v ∧ G.Adj v w then (1 : ℝ) else 0) +
          (if ¬ Covered G u w ∧ G.Adj v w then (1 : ℝ) else 0)) := by
        gcongr with v _ w _
        by_cases ha : G.Adj v w ∧ forcedColor G u χ v = forcedColor G u χ w
        · rw [ite_eq_left ha]
          by_cases hv : Covered G u v
          · by_cases hw : Covered G u w
            · rw [ite_eq_left (show IsBadPair G u χ v w from ⟨ha.1, hv, hw, ha.2⟩)]
              split_ifs <;> norm_num
            · rw [ite_eq_left (show ¬Covered G u w ∧ G.Adj v w from ⟨hw, ha.1⟩)]
              split_ifs <;> norm_num
          · rw [ite_eq_left (show ¬Covered G u v ∧ G.Adj v w from ⟨hv, ha.1⟩)]
            split_ifs <;> norm_num
        · rw [ite_eq_right ha]
          split_ifs <;> norm_num
    _ = _ := by
        simp only [sum_add_distrib, h₁, h₂]
        ring

/-! ### Coverage -/

omit [DecidableEq V] in
/-- The samples missing the neighbourhood of `v`. -/
private theorem card_filter_not_covered (s : ℕ) (v : V) :
    #(univ.filter fun u : Fin s → V => ¬ Covered G u v) = (Fintype.card V - G.degree v) ^ s := by
  classical
  have h : (univ.filter fun u : Fin s → V => ¬ Covered G u v) =
      Fintype.piFinset fun _ => (G.neighborFinset v)ᶜ := by
    ext u
    simp [Fintype.mem_piFinset, mem_neighborFinset]
  rw [h, Fintype.card_piFinset, prod_const, card_compl, card_neighborFinset_eq_degree, card_univ,
    Fintype.card_fin]

omit [Fintype V] [DecidableEq V] in
/-- Bernoulli-type inequality `(N - d) ^ k (N + k d) ≤ N ^ (k + 1)`. -/
private theorem pow_mul_le {N d : ℝ} (hd : 0 ≤ d) (hdN : d ≤ N) (k : ℕ) :
    (N - d) ^ k * (N + k * d) ≤ N ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h0 : 0 ≤ (N - d) ^ k := pow_nonneg (by linarith) k
    have hN : 0 ≤ N := hd.trans hdN
    calc (N - d) ^ (k + 1) * (N + ((k + 1 : ℕ) : ℝ) * d) =
          (N - d) ^ k * ((N - d) * (N + k * d + d)) := by push_cast; ring
      _ ≤ (N - d) ^ k * (N * (N + k * d)) := by
          apply mul_le_mul_of_nonneg_left _ h0
          nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sq_nonneg d), sq_nonneg d]
      _ = N * ((N - d) ^ k * (N + k * d)) := by ring
      _ ≤ N * N ^ (k + 1) := mul_le_mul_of_nonneg_left ih hN
      _ = N ^ (k + 1 + 1) := by ring

omit [Fintype V] [DecidableEq V] in
/-- `d (N - d) ^ s ≤ N ^ (s + 1) / (s + 1)` for `0 ≤ d ≤ N`. -/
private theorem mul_pow_le {N d : ℝ} (hd : 0 ≤ d) (hdN : d ≤ N) (s : ℕ) :
    d * (N - d) ^ s ≤ N ^ (s + 1) / (s + 1) := by
  rw [le_div_iff₀ (by positivity)]
  have h₁ := pow_mul_le hd hdN s
  have h₂ : 0 ≤ (N - d) ^ s := pow_nonneg (by linarith) s
  nlinarith [mul_le_mul_of_nonneg_left hdN h₂]

omit [DecidableEq V] in
/-- The expected uncovered degree mass is at most `n² / (s + 1)`. -/
private theorem sum_uncoveredDegree_le (s : ℕ) :
    ∑ u : Fin s → V, uncoveredDegree G u ≤ (Fintype.card V : ℝ) ^ (s + 2) / (s + 1) := by
  unfold uncoveredDegree
  rw [Finset.sum_comm]
  have hv : ∀ v, (∑ u : Fin s → V, if Covered G u v then 0 else (G.degree v : ℝ)) =
      G.degree v * ((Fintype.card V : ℝ) - G.degree v) ^ s := by
    intro v
    rw [Finset.sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul,
      card_filter_not_covered, Nat.cast_pow,
      Nat.cast_sub (card_neighborFinset_eq_degree G v ▸ card_le_univ _)]
    ring
  rw [Finset.sum_congr rfl fun v _ => hv v]
  calc _ ≤ ∑ _v : V, (Fintype.card V : ℝ) ^ (s + 1) / (s + 1) :=
        sum_le_sum fun v _ => mul_pow_le (Nat.cast_nonneg _)
          (by exact_mod_cast card_neighborFinset_eq_degree G v ▸ card_le_univ _) s
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

omit [DecidableEq V] in
/-- Markov's inequality for the uncovered degree mass. -/
private theorem card_filter_lt_uncoveredDegree_le {ε : ℝ} (hε : 0 < ε) (hV : 0 < Fintype.card V)
    (s : ℕ) :
    (#(univ.filter fun u : Fin s → V => ε * (Fintype.card V : ℝ) ^ 2 / 2 < uncoveredDegree G u)
      : ℝ) ≤ 2 * (Fintype.card V : ℝ) ^ s / (ε * (s + 1)) := by
  set N : ℝ := (Fintype.card V : ℝ)
  set B := univ.filter fun u : Fin s → V => ε * N ^ 2 / 2 < uncoveredDegree G u
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr hV
  have h₁ : (#B : ℝ) * (ε * N ^ 2 / 2) ≤ ∑ u ∈ B, uncoveredDegree G u := by
    rw [← nsmul_eq_mul]
    exact card_nsmul_le_sum _ _ _ fun u hu => (mem_filter.mp hu).2.le
  have h₂ : ∑ u ∈ B, uncoveredDegree G u ≤ ∑ u, uncoveredDegree G u :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun u _ _ => uncoveredDegree_nonneg u
  have h₃ := sum_uncoveredDegree_le (G := G) s
  rw [le_div_iff₀ (by positivity)]
  have h₄ : (#B : ℝ) * (ε * N ^ 2 / 2) ≤ N ^ (s + 2) / (s + 1) := h₁.trans (h₂.trans h₃)
  rw [le_div_iff₀ (by positivity)] at h₄
  have h₅ : N ^ (s + 2) = N ^ s * N ^ 2 := by ring
  rw [h₅] at h₄
  have hN2 : 0 < N ^ 2 := by positivity
  nlinarith

/-! ### Counting accepted samples -/

omit [DecidableEq V] in
/-- Summing a product over pairs of tuples. -/
private theorem sum_sum_prod_eq_pow {m : ℕ} (g : V → V → ℝ) :
    (∑ x : Fin m → V, ∑ y : Fin m → V, ∏ k, g (x k) (y k)) = (∑ a, ∑ b, g a b) ^ m := by
  have h₁ : (∑ a, ∑ b, g a b) = ∑ p : V × V, g p.1 p.2 := (Fintype.sum_prod_type' _).symm
  rw [h₁, ← Fin.prod_const, Fintype.prod_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun _ => rfl

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- No graph is `1 / 2`-far from bipartite. -/
private theorem lt_half_of_isFar {ε : ℝ} (h : IsFar G (fun H => H.IsBipartite) ε) : ε < 1 / 2 := by
  classical
  have h₁ := h.two_mul_lt_sum_monochromatic (fun _ => true)
  have h₃ : 2 * (ε * ((Fintype.card V ^ 2 : ℕ) : ℝ)) < ((Fintype.card V ^ 2 : ℕ) : ℝ) := by
    refine h₁.trans_le ?_
    calc _ ≤ ∑ _v : V, ∑ _w : V, (1 : ℝ) := by
          gcongr with v _ w _
          split_ifs <;> norm_num
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]; push_cast; ring
  by_contra hε
  have := not_lt.mp hε
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card V ^ 2)]

omit [DecidableEq V] in
/-- Accepted samples are counted by the colourings of the sample. -/
private theorem sum_accept_le_sum_pow (u : Fin s → V) {m : ℕ} :
    (∑ x : Fin m → V, ∑ y : Fin m → V,
      if bipAccept (fun k i => decide (G.Adj (x k) (u i))) (fun k i => decide (G.Adj (y k) (u i)))
        (fun k => decide (G.Adj (x k) (y k))) = true then (1 : ℝ) else 0) ≤
      ∑ χ : Fin s → Bool, (∑ a, ∑ b, if IsBadPair G u χ a b then (0 : ℝ) else 1) ^ m := by
  calc _ ≤ ∑ x : Fin m → V, ∑ y : Fin m → V, ∑ χ : Fin s → Bool,
        ∏ k, (if IsBadPair G u χ (x k) (y k) then (0 : ℝ) else 1) := by
        gcongr with x _ y _
        split_ifs with hacc
        · obtain ⟨χ, hχ⟩ := exists_forall_not_isBadPair hacc
          calc (1 : ℝ) = ∏ k, (if IsBadPair G u χ (x k) (y k) then (0 : ℝ) else 1) := by
                rw [prod_eq_one]
                intro k _
                rw [ite_eq_right (hχ k)]
            _ ≤ _ := single_le_sum (f := fun χ => ∏ k,
                (if IsBadPair G u χ (x k) (y k) then (0 : ℝ) else 1))
                (fun χ _ => prod_nonneg fun k _ => by split_ifs <;> norm_num) (mem_univ χ)
        · exact sum_nonneg fun χ _ => prod_nonneg fun k _ => by split_ifs <;> norm_num
    _ = ∑ χ : Fin s → Bool, ∑ x : Fin m → V, ∑ y : Fin m → V,
        ∏ k, (if IsBadPair G u χ (x k) (y k) then (0 : ℝ) else 1) := by
        rw [sum_congr rfl fun x _ => sum_comm]
        exact sum_comm
    _ = _ := by
        refine sum_congr rfl fun χ _ => ?_
        exact sum_sum_prod_eq_pow (fun a b => if IsBadPair G u χ a b then (0 : ℝ) else 1)

omit [DecidableEq V] in
/-- With small uncovered mass, every colouring has more than `ε n²` bad pairs. -/
private theorem sum_not_isBadPair_le {ε : ℝ} (h : IsFar G (fun H => H.IsBipartite) ε)
    {u : Fin s → V}
    (hu : uncoveredDegree G u ≤ ε * (Fintype.card V : ℝ) ^ 2 / 2) (χ : Fin s → Bool) :
    (∑ a, ∑ b, if IsBadPair G u χ a b then (0 : ℝ) else 1) ≤
      (Fintype.card V : ℝ) ^ 2 * (1 - ε) := by
  have h₁ := h.two_mul_lt_sum_monochromatic (forcedColor G u χ)
  have h₂ := sum_mono_le (G := G) u χ
  have h₃ : (∑ a, ∑ b, if IsBadPair G u χ a b then (0 : ℝ) else 1) =
      (Fintype.card V : ℝ) ^ 2 - ∑ a, ∑ b, if IsBadPair G u χ a b then (1 : ℝ) else 0 := by
    have h₄ : ∀ a b, (if IsBadPair G u χ a b then (0 : ℝ) else 1) =
        1 - if IsBadPair G u χ a b then (1 : ℝ) else 0 := fun a b => by split_ifs <;> norm_num
    simp only [h₄, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
    ring
  rw [h₃]
  push_cast at h₁
  nlinarith

omit [DecidableEq V] in
/-- Accepted pair samples for a sample `u` with small uncovered mass. -/
private theorem sum_accept_le_of_good {ε : ℝ} (h : IsFar G (fun H => H.IsBipartite) ε)
    {u : Fin s → V}
    (hu : uncoveredDegree G u ≤ ε * (Fintype.card V : ℝ) ^ 2 / 2) {m : ℕ} :
    (∑ x : Fin m → V, ∑ y : Fin m → V,
      if bipAccept (fun k i => decide (G.Adj (x k) (u i))) (fun k i => decide (G.Adj (y k) (u i)))
        (fun k => decide (G.Adj (x k) (y k))) = true then (1 : ℝ) else 0) ≤
      2 ^ s * ((Fintype.card V : ℝ) ^ 2 * (1 - ε)) ^ m := by
  refine (sum_accept_le_sum_pow u).trans ?_
  calc _ ≤ ∑ _χ : Fin s → Bool, ((Fintype.card V : ℝ) ^ 2 * (1 - ε)) ^ m :=
        sum_le_sum fun χ _ => pow_le_pow_left₀
          (sum_nonneg fun a _ => sum_nonneg fun b _ => by split_ifs <;> norm_num)
          (sum_not_isBadPair_le h hu χ) m
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
        push_cast
        ring

omit [DecidableEq V] in
/-- The trivial bound on accepted pair samples. -/
private theorem sum_accept_le_trivial (u : Fin s → V) {m : ℕ} :
    (∑ x : Fin m → V, ∑ y : Fin m → V,
      if bipAccept (fun k i => decide (G.Adj (x k) (u i))) (fun k i => decide (G.Adj (y k) (u i)))
        (fun k => decide (G.Adj (x k) (y k))) = true then (1 : ℝ) else 0) ≤
      (Fintype.card V : ℝ) ^ m * (Fintype.card V : ℝ) ^ m := by
  calc _ ≤ ∑ _x : Fin m → V, ∑ _y : Fin m → V, (1 : ℝ) := by
        gcongr with x _ y _
        split_ifs <;> norm_num
    _ = _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
          Fintype.card_fin]
        push_cast
        ring

omit [Fintype V] [DecidableEq V] in
/-- `2 ^ s (1 - ε) ^ m ≤ 1 / 8` when `s + 3 ≤ ε m`. -/
private theorem two_pow_mul_one_sub_pow_le {ε : ℝ} (hε : ε ≤ 1) {s m : ℕ} (hm : s + 3 ≤ ε * m) :
    (2 : ℝ) ^ s * (1 - ε) ^ m ≤ 1 / 8 := by
  have h₁ : (1 - ε) ^ m ≤ Real.exp (-ε) ^ m :=
    pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg ε) m
  have h₂ : Real.exp (-ε) ^ m ≤ Real.exp (-1) ^ (s + 3) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    linarith
  have h₃ : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have h₄ : Real.exp (-1) ^ (s + 3) ≤ (1 / 2) ^ (s + 3) :=
    pow_le_pow_left₀ (Real.exp_pos _).le h₃ _
  have h₅ : (2 : ℝ) ^ s * (1 / 2) ^ (s + 3) = 1 / 8 := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  calc (2 : ℝ) ^ s * (1 - ε) ^ m ≤ 2 ^ s * (1 / 2) ^ (s + 3) :=
        mul_le_mul_of_nonneg_left (h₁.trans (h₂.trans h₄)) (by positivity)
    _ = 1 / 8 := h₅

omit [Fintype V] [DecidableEq V] in
/-- Positivity of the proximity parameter from the sample-size condition. -/
private theorem pos_of_twelve_le {ε : ℝ} {s : ℕ} (hs : 12 ≤ ε * s) : 0 < ε := by
  by_contra hε
  have := not_lt.mp hε
  nlinarith [Nat.cast_nonneg (α := ℝ) s]

omit [DecidableEq V] in
/-- The counting form of soundness. -/
private theorem sum_accept_le {ε : ℝ} (h : IsFar G (fun H => H.IsBipartite) ε) {s m : ℕ}
    (hs : 12 ≤ ε * s) (hm : s + 3 ≤ ε * m) :
    (∑ u : Fin s → V, ∑ x : Fin m → V, ∑ y : Fin m → V,
      if bipAccept (fun k i => decide (G.Adj (x k) (u i))) (fun k i => decide (G.Adj (y k) (u i)))
        (fun k => decide (G.Adj (x k) (y k))) = true then (1 : ℝ) else 0) ≤
      (Fintype.card V : ℝ) ^ s * (Fintype.card V : ℝ) ^ m * (Fintype.card V : ℝ) ^ m / 3 := by
  classical
  have hhalf := lt_half_of_isFar h
  have hε : 0 < ε := pos_of_twelve_le hs
  have hV : 0 < Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with hV | hV
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      exact absurd h (not_isFar_of_property (Colorable.of_isEmpty 2) hε.le)
    · exact hV
  have hB := card_filter_lt_uncoveredDegree_le (G := G) hε hV s
  have h8 := two_pow_mul_one_sub_pow_le (by linarith) hm
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr hV
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  set B := univ.filter fun u : Fin s → V => ε * N ^ 2 / 2 < uncoveredDegree G u with hBdef
  have hB' : (#B : ℝ) ≤ N ^ s / 6 := by
    refine hB.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ N ^ s := by positivity
    nlinarith
  rw [← sum_filter_add_sum_filter_not univ
    (fun u : Fin s → V => ε * N ^ 2 / 2 < uncoveredDegree G u)]
  have hX : (∑ u ∈ B, ∑ x : Fin m → V, ∑ y : Fin m → V,
      if bipAccept (fun k i => decide (G.Adj (x k) (u i))) (fun k i => decide (G.Adj (y k) (u i)))
        (fun k => decide (G.Adj (x k) (y k))) = true then (1 : ℝ) else 0) ≤
      (#B : ℝ) * (N ^ m * N ^ m) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun u _ => sum_accept_le_trivial u
  have hY : (∑ u ∈ univ.filter (fun u : Fin s → V => ¬ ε * N ^ 2 / 2 < uncoveredDegree G u),
      ∑ x : Fin m → V, ∑ y : Fin m → V,
      if bipAccept (fun k i => decide (G.Adj (x k) (u i))) (fun k i => decide (G.Adj (y k) (u i)))
        (fun k => decide (G.Adj (x k) (y k))) = true then (1 : ℝ) else 0) ≤
      N ^ s * (2 ^ s * (N ^ 2 * (1 - ε)) ^ m) := by
    have hc : 0 ≤ (2 : ℝ) ^ s * (N ^ 2 * (1 - ε)) ^ m :=
      mul_nonneg (by positivity) (pow_nonneg (mul_nonneg (by positivity) (by linarith)) m)
    calc _ ≤ ∑ u ∈ univ.filter (fun u : Fin s → V => ¬ ε * N ^ 2 / 2 < uncoveredDegree G u),
          (2 : ℝ) ^ s * (N ^ 2 * (1 - ε)) ^ m :=
          sum_le_sum fun u hu => sum_accept_le_of_good h (not_lt.mp (mem_filter.mp hu).2)
      _ ≤ ∑ _u : Fin s → V, (2 : ℝ) ^ s * (N ^ 2 * (1 - ε)) ^ m :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => hc
      _ = _ := by
          rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
  have hY' : N ^ s * (2 ^ s * (N ^ 2 * (1 - ε)) ^ m) =
      (N ^ s * N ^ m * N ^ m) * (2 ^ s * (1 - ε) ^ m) := by rw [mul_pow, ← pow_mul]; ring
  have hP : 0 ≤ N ^ s * N ^ m * N ^ m := by positivity
  have hm2 : 0 ≤ N ^ m * N ^ m := by positivity
  nlinarith

end Combinatorics

/-! ### The tester -/

/-- Budgets add along `OracleComp.pi`. -/
private theorem isCostBounded_pi {ι : Type} {spec : ι → Type} {cost : ι → ℕ} {m : ℕ}
    {β : Fin m → Type} {programs : (i : Fin m) → OracleComp spec (β i)} {c : ℕ}
    (h : ∀ i, OracleComp.IsCostBounded cost (programs i) c) :
    OracleComp.IsCostBounded cost (OracleComp.pi programs) (m * c) := by
  induction m with
  | zero => exact .pure _ _
  | succ m ih =>
    rw [OracleComp.pi_succ]
    exact ((h 0).bind fun _ => (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (ih fun i => h i.succ)).mono (by rw [Nat.succ_mul, Nat.add_comm])

/-- Deterministic coordinates evaluate to a point mass. -/
private theorem evalWith_pi_pure {ι : Type} {spec : ι → Type} (oracle : (q : ι) → PMF (spec q))
    {m : ℕ} {β : Fin m → Type} {programs : (i : Fin m) → OracleComp spec (β i)}
    (x : (i : Fin m) → β i)
    (h : ∀ i, OracleComp.evalWith oracle (programs i) = PMF.pure (x i)) :
    OracleComp.evalWith oracle (OracleComp.pi programs) = PMF.pure x := by
  induction m with
  | zero =>
    rw [OracleComp.pi_zero, OracleComp.evalWith_pure]
    exact congrArg PMF.pure (funext fun i => i.elim0)
  | succ m ih =>
    rw [OracleComp.pi_succ, OracleComp.evalWith_bind, h 0, PMF.pure_bind, OracleComp.evalWith_map,
      ih (fun i => x i.succ) (fun i => h i.succ), PMF.pure_map]
    exact congrArg PMF.pure (funext fun i => Fin.cases rfl (fun _ => rfl) i)

/-- One run of the bipartiteness tester on `Fin (n' + 1)`: sample `s` uniform vertices `u` and `m`
uniform pairs `(x k, y k)`, query `(x k, u i)`, `(y k, u i)` and `(x k, y k)`, and accept when the
sample positions admit a proper 2-colouring (`bipAccept`). -/
def bipartiteRun (n' s m : ℕ) : Tester (n' + 1) := do
  let u ← ProbOracleComp.sample (OracleComp.replicateFin s (ProbComp.unifFin n'))
  let x ← ProbOracleComp.sample (OracleComp.replicateFin m (ProbComp.unifFin n'))
  let y ← ProbOracleComp.sample (OracleComp.replicateFin m (ProbComp.unifFin n'))
  let a ← OracleComp.pi fun k : Fin m => OracleComp.pi fun i : Fin s => queryAdj (x k) (u i)
  let b ← OracleComp.pi fun k : Fin m => OracleComp.pi fun i : Fin s => queryAdj (y k) (u i)
  let c ← OracleComp.pi fun k : Fin m => queryAdj (x k) (y k)
  return bipAccept a b c

/-- The bipartiteness tester with `s` sampled vertices and `m` sampled pairs. The graph on no
vertices is accepted without queries. -/
def bipartiteTester : (n : ℕ) → ℕ → ℕ → Tester n
  | 0, _, _ => pure true
  | n' + 1, s, m => bipartiteRun n' s m

theorem bipartiteTester_succ (n' s m : ℕ) :
    bipartiteTester (n' + 1) s m = bipartiteRun n' s m := by
  rw [bipartiteTester]

/-- A run asks `m (2 s + 1)` queries. -/
theorem isQueryBounded_bipartiteRun (n' s m : ℕ) :
    ProbOracleComp.IsQueryBounded (bipartiteRun n' s m) (m * (2 * s + 1)) := by
  have h := (ProbOracleComp.IsQueryBounded.sample
      (spec := pairSpec (Fin (n' + 1))) (OracleComp.replicateFin s (ProbComp.unifFin n'))).bind
    fun u => (ProbOracleComp.IsQueryBounded.sample
      (spec := pairSpec (Fin (n' + 1))) (OracleComp.replicateFin m (ProbComp.unifFin n'))).bind
    fun x => (ProbOracleComp.IsQueryBounded.sample
      (spec := pairSpec (Fin (n' + 1))) (OracleComp.replicateFin m (ProbComp.unifFin n'))).bind
    fun y => (isCostBounded_pi fun k => isCostBounded_pi fun i =>
      isQueryBounded_queryAdj (x k) (u i)).bind
    fun a => (isCostBounded_pi fun k => isCostBounded_pi fun i =>
      isQueryBounded_queryAdj (y k) (u i)).bind
    fun b => (isCostBounded_pi fun k => isQueryBounded_queryAdj (x k) (y k)).bind
    fun c => OracleComp.IsCostBounded.pure (bipAccept a b c) 0
  refine OracleComp.IsCostBounded.mono h ?_
  ring_nf
  omega

/-- The tester asks at most `m (2 s + 1)` queries. -/
theorem isQueryBounded_bipartiteTester (n s m : ℕ) :
    ProbOracleComp.IsQueryBounded (bipartiteTester n s m) (m * (2 * s + 1)) := by
  cases n with
  | zero => exact .pure _ _
  | succ n' => exact isQueryBounded_bipartiteRun n' s m

/-- Independent uniform vertices form a uniform tuple. -/
private theorem evalWith_sample_replicateFin {n : ℕ} (G : SimpleGraph (Fin n)) (n' k : ℕ) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle G))
      (ProbOracleComp.sample (spec := pairSpec (Fin n))
        (OracleComp.replicateFin k (ProbComp.unifFin n'))) =
      Probability.PMF.uniformOfFintype (Fin k → Fin (n' + 1)) := by
  rw [evalWith_sample, ProbComp.eval_replicateFin, ProbComp.eval_unifFin,
    Probability.PMF.pi_uniformOfFintype]

/-- The acceptance probability of a run is the fraction of accepted samples. -/
theorem acceptProb_bipartiteRun (n' s m : ℕ) (G : SimpleGraph (Fin (n' + 1)))
    [DecidableRel G.Adj] :
    acceptProb (bipartiteRun n' s m) G =
      (∑ u : Fin s → Fin (n' + 1), ∑ x : Fin m → Fin (n' + 1), ∑ y : Fin m → Fin (n' + 1),
        if bipAccept (fun k i => decide (G.Adj (x k) (u i))) (fun k i => decide (G.Adj (y k) (u i)))
          (fun k => decide (G.Adj (x k) (y k))) then (1 : ℝ) else 0) /
        ((n' + 1 : ℝ) ^ s * (n' + 1 : ℝ) ^ m * (n' + 1 : ℝ) ^ m) := by
  rw [acceptProb_eq, bipartiteRun]
  simp only [OracleComp.evalWith_bind, evalWith_sample_replicateFin]
  simp only [evalWith_pi_pure _ _ fun k => evalWith_pi_pure _ _ fun i => evalWith_queryAdj G _ _,
    evalWith_pi_pure _ _ fun k => evalWith_queryAdj G _ _, PMF.pure_bind,
    OracleComp.evalWith_pure]
  simp only [Probability.PMF.bind_apply_toReal, Probability.PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.card_pi, Fintype.card_fin, prod_const,
    card_univ]
  have hpure : ∀ b : Bool, (PMF.pure b true).toReal = if b = true then (1 : ℝ) else 0 := by
    intro b; cases b <;> simp [PMF.pure_apply]
  simp only [hpure, ← mul_sum]
  push_cast
  field_simp

/-- **Completeness.** A bipartite graph is accepted with probability one. -/
theorem acceptProb_bipartiteTester_eq_one {n : ℕ} (s m : ℕ) {G : SimpleGraph (Fin n)}
    (hG : G.IsBipartite) : acceptProb (bipartiteTester n s m) G = 1 := by
  cases n with
  | zero => simp [bipartiteTester]
  | succ n' =>
    classical
    rw [bipartiteTester, acceptProb_bipartiteRun]
    simp only [bipAccept_of_colorable hG, ite_true, sum_const, card_univ, nsmul_eq_mul,
      mul_one, Fintype.card_fun, Fintype.card_fin]
    push_cast
    field_simp

/-- **Soundness.** If `12 ≤ ε s` and `s + 3 ≤ ε m`, a graph `ε`-far from bipartite is accepted with
probability at most `1 / 3`. -/
theorem acceptProb_bipartiteTester_le_one_third {n s m : ℕ} {ε : ℝ} (hs : 12 ≤ ε * s)
    (hm : s + 3 ≤ ε * m) {G : SimpleGraph (Fin n)} (hG : IsFar G (fun H => H.IsBipartite) ε) :
    acceptProb (bipartiteTester n s m) G ≤ 1 / 3 := by
  cases n with
  | zero =>
    exact absurd hG (not_isFar_of_property (Colorable.of_isEmpty 2) (pos_of_twelve_le hs).le)
  | succ n' =>
    classical
    rw [bipartiteTester, acceptProb_bipartiteRun, div_le_iff₀ (by positivity)]
    have h := sum_accept_le hG hs hm
    simp only [Fintype.card_fin] at h
    push_cast at h
    linarith

/-- **Bipartiteness is testable.** If `12 ≤ ε s` and `s + 3 ≤ ε m`, the tester with `s` sampled
vertices and `m` sampled pairs is a one-sided tester for bipartiteness with proximity `ε` and
`m (2 s + 1)` queries. -/
theorem isOneSidedTester_bipartiteTester {n s m : ℕ} {ε : ℝ} (hs : 12 ≤ ε * s)
    (hm : s + 3 ≤ ε * m) :
    IsOneSidedTester (bipartiteTester n s m) (fun G => G.IsBipartite) ε (m * (2 * s + 1)) where
  queryBounded := isQueryBounded_bipartiteTester n s m
  accept _ hG := acceptProb_bipartiteTester_eq_one s m hG
  reject _ hG := acceptProb_bipartiteTester_le_one_third hs hm hG

/-- **Bipartiteness is one-sided testable with a number of queries depending only on the
proximity**: `⌈(⌈12 / ε⌉ + 3) / ε⌉ (2 ⌈12 / ε⌉ + 1)` queries, which is at most `459 / ε³` for
`ε ≤ 1` (`bipartiteQueryBound_le`). -/
theorem oneSidedTestable_isBipartite :
    OneSidedTestable (fun _ G => G.IsBipartite)
      (fun ε => ⌈(⌈12 / ε⌉₊ + 3 : ℝ) / ε⌉₊ * (2 * ⌈12 / ε⌉₊ + 1)) := by
  refine oneSidedTestable_iff.mpr fun ε hε n => ⟨bipartiteTester n _ _,
    isOneSidedTester_bipartiteTester ?_ ?_⟩
  · calc (12 : ℝ) = ε * (12 / ε) := by field_simp
      _ ≤ ε * ⌈12 / ε⌉₊ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) hε.le
  · calc ((⌈12 / ε⌉₊ : ℕ) : ℝ) + 3 = ε * ((⌈12 / ε⌉₊ + 3 : ℝ) / ε) := by field_simp
      _ ≤ ε * ⌈(⌈12 / ε⌉₊ + 3 : ℝ) / ε⌉₊ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) hε.le

/-- The query bound of `oneSidedTestable_isBipartite` is `O(ε⁻³)`: at most `459 / ε³` for
`0 < ε ≤ 1`. -/
theorem bipartiteQueryBound_le {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ((⌈(⌈12 / ε⌉₊ + 3 : ℝ) / ε⌉₊ * (2 * ⌈12 / ε⌉₊ + 1) : ℕ) : ℝ) ≤ 459 / ε ^ 3 := by
  set t : ℝ := 1 / ε with ht_def
  have ht : 1 ≤ t := by rw [ht_def, le_div_iff₀ hε]; linarith
  have h12 : 12 / ε = 12 * t := by rw [ht_def]; ring
  have hS : ((⌈12 / ε⌉₊ : ℕ) : ℝ) ≤ 13 * t := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 12 / ε by positivity)
    linarith
  have hM : ((⌈(⌈12 / ε⌉₊ + 3 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ 17 * t ^ 2 := by
    have h₁ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (⌈12 / ε⌉₊ + 3 : ℝ) / ε by positivity)
    have h₂ : (⌈12 / ε⌉₊ + 3 : ℝ) / ε = (⌈12 / ε⌉₊ + 3 : ℝ) * t := by rw [ht_def]; ring
    have h₃ : (⌈12 / ε⌉₊ + 3 : ℝ) * t ≤ 16 * t * t :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have ht2 : 1 ≤ t ^ 2 := by nlinarith
    linarith
  have h459 : 459 / ε ^ 3 = 17 * t ^ 2 * (27 * t) := by rw [ht_def]; field_simp; ring
  rw [h459]
  push_cast
  exact mul_le_mul hM (by linarith) (by positivity) (by positivity)

end Cslib.DenseGraphTesting
