/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.MarkovChain.Coloring.Count
import ComplexityTests.PathCoupling

/-!
# Approximate counting of colorings: checked instances

* An empirical frequency: three of the four samples `true, false, true, true` are `true`.
* The single edge `K₂` has `6` proper `3`-colorings, and the first vertex of the identity
  enumeration of `Fin 2` is `0`.
* Theorem 14.14 on `K₂` with `q = 3` (`n = 2`, `Δ = 1`): `4 (log 2 + log (36 e / ε))` steps per
  sample and `162 / (η ε²)` samples per stage estimate `1 / 6` within relative error `ε` with
  probability at least `1 - η`.
* The hypotheses on `t` and `a` can always be met: for every graph with `2Δ < q`, every proper
  coloring, `0 < ε ≤ 1` and `0 < η`, some `t` and `a` give the guarantee.
* The sample-size hypothesis cannot be dropped: with one sample per stage the estimator only takes
  the values `0` and `1`, so on `K₂` it never lies within relative error `1 / 2` of `1 / 6`.
-/

namespace ComplexityTests.ColoringCount

open Cslib.Probability Cslib.Probability.PMF Cslib.Probability.MarkovChain SimpleGraph
open ComplexityTests.PathCoupling

/-! ### Empirical frequencies -/

theorem empiricalFrequency_example :
    empiricalFrequency {b : Bool | b = true} ![true, false, true, true] = 3 / 4 := by
  rw [empiricalFrequency_eq, Fin.sum_univ_four]
  norm_num

/-! ### The single edge -/

theorem card_properColorings_edge : (properColorings (⊤ : SimpleGraph (Fin 2)) 3).card = 6 := by
  decide

theorem firstVertices_edge : firstVertices (Equiv.refl (Fin 2)) 1 = {0} := by
  decide

/-- **Theorem 14.14 on `K₂` with `q = 3`**: `n = 2`, `Δ = 1`, `(q - Δ) / (q - 2Δ) = 2` and
`|X| = 6`. -/
theorem le_toOuterMeasure_coloringCountEstimator_edge {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) {t a : ℕ} (ht : 4 * (Real.log 2 + Real.log (36 * Real.exp 1 / ε)) ≤ t)
    (ha : 162 / (η * ε ^ 2) ≤ a) :
    1 - η ≤ ((coloringCountEstimator (⊤ : SimpleGraph (Fin 2)) (Equiv.refl _) 3 t a
      edgeBoundary).toOuterMeasure {W | (1 - ε) / 6 ≤ W ∧ W ≤ (1 + ε) / 6}).toReal := by
  have h := le_toOuterMeasure_coloringCountEstimator (G := ⊤) (q := 3)
    (by rw [maxDegree_edge]; decide) (Equiv.refl (Fin 2)) isProperColoring_edgeBoundary hε hε1 hη
    (t := t) ?_ (a := a) ?_
  · rwa [card_properColorings_edge, Nat.cast_ofNat] at h
  · rw [maxDegree_edge]
    convert ht using 3 <;> norm_num
    ring_nf
  · convert ha using 2
    norm_num

/-! ### The hypotheses can be met -/

/-- For every graph with `2Δ < q` and every proper coloring, suitable `t` and `a` exist. -/
theorem exists_le_toOuterMeasure_coloringCountEstimator {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {q : ℕ} (hq : 2 * G.maxDegree < q)
    {x₀ : V → Fin q} (hx₀ : G.IsProperColoring x₀) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) :
    ∃ t a : ℕ, 1 - η ≤ ((coloringCountEstimator G (Fintype.equivFin V) q t a x₀).toOuterMeasure
      {W | (1 - ε) / (G.properColorings q).card ≤ W ∧
        W ≤ (1 + ε) / (G.properColorings q).card}).toReal := by
  obtain ⟨t, ht⟩ := exists_nat_ge (((q - G.maxDegree : ℕ) : ℝ) / ((q - 2 * G.maxDegree : ℕ) : ℝ) *
    Fintype.card V * (Real.log (Fintype.card V) +
      Real.log (6 * Real.exp 1 * q * Fintype.card V / ε)))
  obtain ⟨a, ha⟩ := exists_nat_ge (27 * q * Fintype.card V / (η * ε ^ 2))
  exact ⟨t, a, le_toOuterMeasure_coloringCountEstimator hq _ hx₀ hε hε1 hη ht ha⟩

/-! ### One sample per stage is not enough -/

/-- With one sample per stage, the product estimator is `0` or `1`. -/
theorem productEstimate_one_sample {κ S : Type*} [Fintype κ] (A : κ → Set S)
    [∀ k, DecidablePred (· ∈ A k)] (x : κ → Fin 1 → S) :
    productEstimate A x = 0 ∨ productEstimate A x = 1 := by
  rw [productEstimate_eq]
  by_cases h : ∀ k, x k 0 ∈ A k
  · right
    refine Finset.prod_eq_one fun k _ => ?_
    rw [empiricalFrequency_eq, Fin.sum_univ_one, Nat.cast_one, div_one, ite_eq_left (h k)]
  · left
    obtain ⟨k, hk⟩ := not_forall.1 h
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    rw [empiricalFrequency_eq, Fin.sum_univ_one, Nat.cast_one, div_one, ite_eq_right hk]

/-- With one sample per stage, the estimator on `K₂` with `q = 3` never lies within relative
error `1 / 2` of `1 / |X| = 1 / 6`, however long the chain runs. -/
theorem toOuterMeasure_coloringCountEstimator_edge_one_sample (t : ℕ) :
    (coloringCountEstimator (⊤ : SimpleGraph (Fin 2)) (Equiv.refl _) 3 t 1
      edgeBoundary).toOuterMeasure
      {W | (1 - 1 / 2) / (properColorings (⊤ : SimpleGraph (Fin 2)) 3).card ≤ W ∧
        W ≤ (1 + 1 / 2) / (properColorings (⊤ : SimpleGraph (Fin 2)) 3).card} = 0 := by
  rw [coloringCountEstimator, _root_.PMF.toOuterMeasure_map_apply,
    _root_.PMF.toOuterMeasure_apply_eq_zero_iff, card_properColorings_edge]
  refine Set.disjoint_left.2 fun x _ hx => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Nat.cast_ofNat] at hx
  have key : ∀ W : ℝ, W = 0 ∨ W = 1 → ¬((1 - 1 / 2) / 6 ≤ W ∧ W ≤ (1 + 1 / 2) / 6) := by
    rintro W (rfl | rfl) <;> norm_num
  exact key _ (productEstimate_one_sample _ x) hx

end ComplexityTests.ColoringCount
