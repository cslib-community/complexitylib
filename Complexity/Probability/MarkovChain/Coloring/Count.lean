/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.MarkovChain.Coloring
public import Complexity.Probability.Product.Estimator
import Complexity.Probability.MarkovChain.Coloring.Ratio
import Complexity.Probability.PMF.Event
import Complexity.Probability.StatisticalDistance.Event
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Approximate counting of proper colorings

Let `G` be a graph with `n` vertices and maximum degree `Δ`, and let `q > 2Δ`. The number `|X|` of
proper `q`-colorings of `G` can be approximated from samples of the Glauber dynamics
([LevinPeres2017], Section 14.4.2, following Jerrum and Sinclair). Enumerate the vertices as
`v_0, …, v_{n-1}` by `e : V ≃ Fin n` (`v_k = e.symm k`), fix a proper coloring `x₀` and let `X_k`
be the proper colorings agreeing with `x₀` off the first `k` vertices
(`Cslib.Probability.MarkovChain.firstVertices`). Then `X_0 = {x₀}`, `X_n = X` and
`1 / |X| = ∏_{k < n} |X_k| / |X_{k+1}|`.

At stage `k` (`Cslib.Probability.MarkovChain.coloringCountStage`), the Glauber dynamics that only
updates the first `k + 1` vertices, run for `t` steps from `x₀`, nearly samples the uniform
distribution on `X_{k+1}` ([LevinPeres2017], (14.23); here
`Cslib.Probability.MarkovChain.dist_glauberColoringOn_frozen_le_of_le`). Under that distribution
the vertex `v_k` keeps its color `x₀ v_k` with probability `|X_k| / |X_{k+1}|`, which is at least
`1 / (e q)` by [LevinPeres2017], Lemma 14.16
(`Cslib.Probability.MarkovChain.inv_exp_mul_le_card_frozenColorings_erase_div`). The estimator
(`Cslib.Probability.MarkovChain.coloringCountEstimator`) takes `a` independent runs at each stage
and multiplies the fractions `W_k` of runs in which `v_k` keeps its color. It uses `n t a` Glauber
updates in total. The concentration bound for the product estimator
(`Cslib.Probability.PMF.le_toOuterMeasure_productEstimate`) gives [LevinPeres2017],
Theorem 14.14 (`Cslib.Probability.MarkovChain.le_toOuterMeasure_coloringCountEstimator`).

The proof of [LevinPeres2017] bounds `E(W_k) ≥ 1 / (e q) - ε / (6 e q n) ≥ 1 / (3 q)`. The second
inequality fails for `n = 1` and `ε` close to `1`, as `(1 - 1 / 6) / e < 1 / 3`. The formalization
uses `E(W_k) ≥ (1 - ε / (6 n)) / (e q) ≥ 5 / (6 e q)` instead, which still gives (14.22) with the
sample sizes of (14.21).

## Main definitions

* `Cslib.Probability.MarkovChain.firstVertices`: the first `k` vertices of an enumeration.
* `Cslib.Probability.MarkovChain.coloringCountStage`: the distribution of one sample at stage `k`.
* `Cslib.Probability.MarkovChain.coloringCountEstimator`: the distribution of the estimator `W`.

## Main results

* `Cslib.Probability.MarkovChain.le_toOuterMeasure_coloringCountEstimator`: [LevinPeres2017],
  Theorem 14.14: if `2Δ < q`, `t ≥ ((q - Δ) / (q - 2Δ)) n (log n + log (6 e q n / ε))` and
  `a ≥ 27 q n / (η ε²)`, then `(1 - ε) / |X| ≤ W ≤ (1 + ε) / |X|` with probability at least
  `1 - η`.

## References

* [LevinPeres2017], Section 14.4.2.
-/

public section

open scoped ENNReal

namespace Cslib.Probability.MarkovChain

open Cslib.Probability.PMF SimpleGraph

variable {V : Type*} {q : ℕ} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The first `k` vertices `e.symm 0, …, e.symm (k - 1)` of the enumeration `e`. -/
def firstVertices {n : ℕ} (e : V ≃ Fin n) (k : ℕ) : Finset V :=
  Finset.univ.filter fun v => (e v : ℕ) < k

omit [DecidableEq V] in
theorem mem_firstVertices {n : ℕ} (e : V ≃ Fin n) {k : ℕ} {v : V} :
    v ∈ firstVertices e k ↔ (e v : ℕ) < k := by
  simp [firstVertices]

omit [DecidableEq V] in
@[simp] theorem firstVertices_zero {n : ℕ} (e : V ≃ Fin n) : firstVertices e 0 = ∅ := by
  ext v
  simp [mem_firstVertices]

omit [DecidableEq V] in
@[simp] theorem firstVertices_self {n : ℕ} (e : V ≃ Fin n) : firstVertices e n = Finset.univ := by
  ext v
  simp [mem_firstVertices]

/-- Removing the vertex `e.symm k` from the first `k + 1` vertices leaves the first `k`. -/
theorem firstVertices_succ_erase {n : ℕ} (e : V ≃ Fin n) (k : Fin n) :
    (firstVertices e ((k : ℕ) + 1)).erase (e.symm k) = firstVertices e k := by
  ext v
  simp only [Finset.mem_erase, mem_firstVertices]
  constructor
  · rintro ⟨hv, hk⟩
    have : e v ≠ k := fun h => hv (by rw [← h, Equiv.symm_apply_apply])
    have : (e v : ℕ) ≠ k := fun h => this (Fin.ext h)
    omega
  · intro hv
    refine ⟨fun h => ?_, by omega⟩
    rw [h, Equiv.apply_symm_apply] at hv
    exact lt_irrefl _ hv

omit [DecidableEq V] in
theorem firstVertices_succ_nonempty {n : ℕ} (e : V ≃ Fin n) (k : Fin n) :
    (firstVertices e ((k : ℕ) + 1)).Nonempty :=
  ⟨e.symm k, by simp [mem_firstVertices]⟩

omit [DecidableEq V] in
theorem card_firstVertices_le {n : ℕ} (e : V ≃ Fin n) (k : ℕ) :
    (firstVertices e k).card ≤ n := by
  calc (firstVertices e k).card ≤ Finset.univ.card := Finset.card_le_univ _
    _ = n := by rw [Finset.card_univ, Fintype.card_congr e, Fintype.card_fin]

/-- One sample at stage `k` of the counting algorithm: `t` steps from `x₀` of the Glauber dynamics
that only updates the first `k + 1` vertices. -/
noncomputable def coloringCountStage {n : ℕ} (e : V ≃ Fin n) (q t : ℕ) (x₀ : V → Fin q)
    (k : Fin n) : PMF (V → Fin q) :=
  (glauberColoringOn G q (firstVertices e ((k : ℕ) + 1)) (firstVertices_succ_nonempty e k) ^ t) x₀

/-- **The coloring counting estimator** of [LevinPeres2017], Section 14.4.2: for each stage
`k < n`, draw `a` independent samples of `coloringCountStage G e q t x₀ k` and let `W_k` be the
fraction of them in which the vertex `e.symm k` keeps its color `x₀ (e.symm k)`. The estimator is
`W = ∏ k, W_k`, computed from `n t a` Glauber updates. -/
noncomputable def coloringCountEstimator {n : ℕ} (e : V ≃ Fin n) (q t a : ℕ) (x₀ : V → Fin q) :
    PMF ℝ :=
  (pi fun k : Fin n => pi fun _ : Fin a => coloringCountStage G e q t x₀ k).map
    (productEstimate fun k : Fin n => {x : V → Fin q | x (e.symm k) = x₀ (e.symm k)})

/-- A telescoping product of ratios. -/
private theorem prod_fin_div_succ {n : ℕ} (f : ℕ → ℝ) (hf : ∀ k, f k ≠ 0) :
    ∏ k : Fin n, f k / f (k + 1) = f 0 / f n := by
  induction n with
  | zero => simp [div_self (hf 0)]
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    field_simp [hf n, hf (n + 1)]

variable {G}

/-- **Approximate counting of colorings** ([LevinPeres2017], Theorem 14.14). Let `G` have `n`
vertices and maximum degree `Δ < q / 2`, let `x₀` be a proper coloring, `0 < ε ≤ 1` and `0 < η`.
If each stage runs `t ≥ ((q - Δ) / (q - 2Δ)) n (log n + log (6 e q n / ε))` Glauber steps and
draws `a ≥ 27 q n / (η ε²)` samples, then the estimator `W` satisfies
`(1 - ε) / |X| ≤ W ≤ (1 + ε) / |X|` with probability at least `1 - η`, where `X` is the set of
proper `q`-colorings. -/
theorem le_toOuterMeasure_coloringCountEstimator (hq : 2 * G.maxDegree < q) {n : ℕ}
    (e : V ≃ Fin n) {x₀ : V → Fin q} (hx₀ : G.IsProperColoring x₀) {ε η : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hη : 0 < η) {t : ℕ}
    (ht : ((q - G.maxDegree : ℕ) : ℝ) / ((q - 2 * G.maxDegree : ℕ) : ℝ) * n *
      (Real.log n + Real.log (6 * Real.exp 1 * q * n / ε)) ≤ t)
    {a : ℕ} (ha : 27 * q * n / (η * ε ^ 2) ≤ a) :
    1 - η ≤ ((coloringCountEstimator G e q t a x₀).toOuterMeasure
      {W | (1 - ε) / (G.properColorings q).card ≤ W ∧
        W ≤ (1 + ε) / (G.properColorings q).card}).toReal := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.2 (by omega)
  have hb : (0 : ℝ) < (Real.exp 1 * q)⁻¹ := inv_pos.2 (mul_pos (Real.exp_pos 1) hq0)
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℝ,
      X = fun k => ((frozenColorings G q (firstVertices e k) x₀).card : ℝ) := ⟨_, rfl⟩
  have hX0 (k : ℕ) : X k ≠ 0 := by
    rw [hX]
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨x₀, mem_frozenColorings_self hx₀⟩)
  -- `1 / |X| = ∏_{k < n} |X_k| / |X_{k+1}|`.
  have hR : ∏ k : Fin n, X k / X (k + 1) = 1 / (G.properColorings q).card := by
    rw [prod_fin_div_succ X hX0, hX]
    simp only [firstVertices_zero, firstVertices_self, frozenColorings_empty hx₀,
      frozenColorings_univ, Finset.card_singleton, Nat.cast_one]
  -- Lemma 14.16.
  have hratio (k : Fin n) : (Real.exp 1 * q)⁻¹ ≤ X k / X (k + 1) := by
    have h := inv_exp_mul_le_card_frozenColorings_erase_div hq hx₀
      (show e.symm k ∈ firstVertices e ((k : ℕ) + 1) by simp [mem_firstVertices])
    rw [firstVertices_succ_erase] at h
    simpa only [hX, Nat.cast_add, Nat.cast_one] using h
  -- (14.23) and (14.24): each stage probability is within `ε / (6 e q n)` of its ratio.
  have hp (k : Fin n) : |((coloringCountStage G e q t x₀ k).toOuterMeasure
      {x : V → Fin q | x (e.symm k) = x₀ (e.symm k)}).toReal - X k / X (k + 1)| ≤
      ε / (6 * Fintype.card (Fin n)) * (X k / X (k + 1)) := by
    rw [Fintype.card_fin]
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos k)
    have hU := firstVertices_succ_nonempty e k
    have hne : (frozenColorings G q (firstVertices e ((k : ℕ) + 1)) x₀).Nonempty :=
      ⟨x₀, mem_frozenColorings_self hx₀⟩
    have hπ : ((uniformOfFinset _ hne).toOuterMeasure
        {x : V → Fin q | x (e.symm k) = x₀ (e.symm k)}).toReal = X k / X (k + 1) := by
      rw [toOuterMeasure_toReal_eq_sum_ite]
      have h := sum_uniformOfFinset_frozenColorings_ite hne (e.symm k)
      rw [firstVertices_succ_erase] at h
      simpa only [hX, Set.mem_ofPred_eq] using h
    have hδ : 0 < ε / (6 * Real.exp 1 * q * n) :=
      div_pos hε (mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) hq0) hn)
    have hdist := dist_glauberColoringOn_frozen_le_of_le G hq hU hne (card_firstVertices_le e _)
      hδ (t := t) ?_ (x := x₀) fun _ _ => rfl
    · have hev := abs_toOuterMeasure_toReal_sub_le_dist
        ((glauberColoringOn G q _ hU ^ t) x₀) (uniformOfFinset _ hne)
        {x : V → Fin q | x (e.symm k) = x₀ (e.symm k)}
      rw [hπ] at hev
      calc _ ≤ ε / (6 * Real.exp 1 * q * n) := hev.trans hdist
        _ = ε / (6 * n) * (Real.exp 1 * q)⁻¹ := by field_simp
        _ ≤ ε / (6 * n) * (X k / X (k + 1)) :=
            mul_le_mul_of_nonneg_left (hratio k) (by positivity)
    · have hlog : Real.log (ε / (6 * Real.exp 1 * q * n)) =
          -Real.log (6 * Real.exp 1 * q * n / ε) := by
        rw [← Real.log_inv, inv_div]
      rw [hlog, sub_neg_eq_add]
      exact ht
  -- The sample size: `48 n ≤ 5 η ε² a / (e q)` since `e < 2.72`.
  have hcard : 48 * (Fintype.card (Fin n) : ℝ) ≤ 5 * η * ε ^ 2 * a * (Real.exp 1 * q)⁻¹ := by
    rw [Fintype.card_fin]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hηε : 0 < η * ε ^ 2 := by positivity
    rw [div_le_iff₀ hηε] at ha
    rw [← div_eq_mul_inv, le_div_iff₀ (mul_pos (Real.exp_pos 1) hq0)]
    have hqn : 0 ≤ (q : ℝ) * n := by positivity
    have := mul_le_mul_of_nonneg_right he.le hqn
    linarith
  have hgen := le_toOuterMeasure_productEstimate (fun k : Fin n => coloringCountStage G e q t x₀ k)
    (fun k : Fin n => {x : V → Fin q | x (e.symm k) = x₀ (e.symm k)})
    (fun k : Fin n => X k / X (k + 1)) hb hratio hε hε1 hη hp hcard
  simp only [hR] at hgen
  rw [coloringCountEstimator, _root_.PMF.toOuterMeasure_map_apply]
  convert hgen using 3
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mul_one_div]

end Cslib.Probability.MarkovChain
